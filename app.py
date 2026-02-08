import os
import secrets
from datetime import datetime, timedelta
from decimal import Decimal
from functools import wraps

import requests
from dotenv import load_dotenv
from flask import (
    Flask,
    render_template,
    request,
    redirect,
    url_for,
    session,
    abort,
    flash,
    send_file,
    jsonify,
)
from flask_migrate import Migrate
from sqlalchemy import func, or_, and_

from models import (
    db,
    Customer, Vehicle, RepairOrder, ROEvent,
    Document, Job, LineItem, Appointment,
    LaborMatrixTier, PartsMatrixTier, Technician
)

from pdf import build_document_pdf, build_invoice_pdf

load_dotenv()

TAX_RATE = Decimal(os.getenv("TAX_RATE", "0.00"))
APP_USERNAME = os.getenv("APP_USERNAME", "admin")
APP_PASSWORD = os.getenv("APP_PASSWORD", "password")

ENGINE_PRESETS = [
    "2.0L", "2.3L", "2.4L", "2.5L", "2.7L",
    "3.0L", "3.5L", "3.6L",
    "4.0L", "4.6L", "5.0L", "5.2L", "5.3L", "5.7L",
    "6.0L", "6.2L", "6.4L", "6.6L", "6.7L", "7.3L",
]

def D(x) -> Decimal:
    if x is None:
        return Decimal("0.00")
    if isinstance(x, Decimal):
        return x
    return Decimal(str(x))

def parse_decimal(v):
    v = (v or "").strip()
    if not v:
        return None
    # allow $ and commas
    v = v.replace("$", "").replace(",", "")
    try:
        return Decimal(v)
    except Exception:
        return None


def create_app():
    app = Flask(__name__)
    app.secret_key = os.getenv("SECRET_KEY", "dev-secret-change-me")

    db_url = os.getenv("DATABASE_URL")
    if not db_url:
        raise RuntimeError("DATABASE_URL missing in .env")
    app.config["SQLALCHEMY_DATABASE_URI"] = db_url
    app.config["SQLALCHEMY_TRACK_MODIFICATIONS"] = False

    db.init_app(app)
    Migrate(app, db)

    # ---------- Auth ----------
    def login_required(fn):
        @wraps(fn)
        def wrapper(*args, **kwargs):
            if not session.get("logged_in"):
                return redirect(url_for("login"))
            return fn(*args, **kwargs)
        return wrapper



    @app.get("/login")
    def login():
        return render_template("login.html")

    @app.post("/login")
    def login_post():
        username = (request.form.get("username") or "").strip()
        password = (request.form.get("password") or "").strip()
        if username == APP_USERNAME and password == APP_PASSWORD:
            session["logged_in"] = True
            return redirect(url_for("dashboard"))
        flash("Invalid login.")
        return redirect(url_for("login"))

    @app.get("/logout")
    def logout():
        session.clear()
        return redirect(url_for("login"))

    # ---------- Helpers ----------
    def log_event(ro_id: str, event_type: str, old=None, new=None):
        db.session.add(ROEvent(
            ro_id=ro_id,
            event_type=event_type,
            old_value=str(old) if old is not None else None,
            new_value=str(new) if new is not None else None,
        ))

    def line_amount(li: LineItem) -> Decimal:
        amt = D((li.qty or 0) * (li.unit_price or 0))
        if li.item_type == "discount":
            return -abs(amt)
        return amt

    def active_items_for_totals(items):
        job_ids = list({i.job_id for i in items if i.job_id})
        job_status = {}
        if job_ids:
            job_status = {
                j.id: j.status
                for j in Job.query.filter(Job.id.in_(job_ids)).all()
            }
        return [
            i for i in items
            if (not i.job_id) or job_status.get(i.job_id) != "declined"
        ]

    def recalc_document_totals(doc: Document):
        if doc.status in ("locked", "paid") or doc.locked_at is not None:
            return

        items = LineItem.query.filter_by(document_id=doc.id).all()
        active_items = active_items_for_totals(items)
        subtotal = sum((line_amount(i) for i in active_items), start=Decimal("0.00"))

        taxable = sum(
            (line_amount(i) for i in active_items if i.taxable and i.item_type != "discount"),
            start=Decimal("0.00"),
        )
        tax = (taxable * TAX_RATE).quantize(Decimal("0.01"))
        total = (subtotal + tax).quantize(Decimal("0.01"))

        doc.subtotal = subtotal.quantize(Decimal("0.01"))
        doc.tax = tax
        doc.total = total
        db.session.add(doc)

    def get_or_create_doc(ro_id: str, doc_type: str) -> Document:
        doc = Document.query.filter_by(ro_id=ro_id, doc_type=doc_type, version=1).first()
        if not doc:
            doc = Document(ro_id=ro_id, doc_type=doc_type, version=1, status="draft")
            db.session.add(doc)
            db.session.commit()
        return doc

    def ensure_share_token(doc: Document) -> None:
        if getattr(doc, "share_token", None):
            return
        while True:
            token = secrets.token_urlsafe(24)
            if not Document.query.filter_by(share_token=token).first():
                doc.share_token = token
                db.session.add(doc)
                return

    def calc_profit_for_doc(doc_id: str):
        items = LineItem.query.filter_by(document_id=doc_id).all()
        revenue = Decimal("0.00")
        cost = Decimal("0.00")
        for i in items:
            revenue += line_amount(i)
            if i.item_type != "discount" and i.cost is not None:
                cost += D((i.qty or 0) * (i.cost or 0))
        gp = revenue - cost
        margin = (gp / revenue * 100) if revenue != 0 else Decimal("0.00")
        return {
            "revenue": revenue.quantize(Decimal("0.01")),
            "cost": cost.quantize(Decimal("0.01")),
            "gross_profit": gp.quantize(Decimal("0.01")),
            "margin_pct": margin.quantize(Decimal("0.01")),
        }

    def job_totals(doc_id: str):
        items = LineItem.query.filter_by(document_id=doc_id).all()
        totals = {}
        for i in items:
            jid = i.job_id or "__none__"
            totals[jid] = totals.get(jid, Decimal("0.00")) + line_amount(i)
        return {k: v.quantize(Decimal("0.01")) for k, v in totals.items()}

    def ensure_default_job(ro_id: str):
        if Job.query.filter_by(ro_id=ro_id).count() == 0:
            ro = RepairOrder.query.get(ro_id)
            title = (ro.concern or "Job 1").strip()
            db.session.add(Job(ro_id=ro_id, title=title or "Job 1", status="pending", sort_order=1))
            db.session.commit()

    def labor_hours_for_job(doc_id: str, job_id: str) -> Decimal:
        items = LineItem.query.filter_by(document_id=doc_id, job_id=job_id, item_type="labor").all()
        total = Decimal("0.00")
        for item in items:
            if item.labor_hours is not None:
                total += D(item.labor_hours)
            else:
                total += D(item.qty or 0)
        return total.quantize(Decimal("0.01"))

    # -------- Matrix logic --------
    def get_labor_rate_for_hours(hours: Decimal) -> Decimal:
        """
        Finds the first tier where min_hours <= hours <= max_hours (or max is NULL).
        If no tiers exist, fallback to 115/hr.
        """
        tiers = LaborMatrixTier.query.order_by(LaborMatrixTier.min_hours.asc()).all()
        if not tiers:
            return Decimal("115.00")

        for t in tiers:
            min_h = D(t.min_hours)
            max_h = D(t.max_hours) if t.max_hours is not None else None
            if hours >= min_h and (max_h is None or hours <= max_h):
                return D(t.rate_per_hour).quantize(Decimal("0.01"))

        return D(tiers[-1].rate_per_hour).quantize(Decimal("0.01"))

    def get_parts_multiplier_for_cost(cost: Decimal) -> Decimal:
        """
        Finds tier where min_cost <= cost <= max_cost (or max is NULL).
        If no tiers exist, fallback to 1.30x
        """
        tiers = PartsMatrixTier.query.order_by(PartsMatrixTier.min_cost.asc()).all()
        if not tiers:
            return Decimal("1.3000")

        for t in tiers:
            min_c = D(t.min_cost)
            max_c = D(t.max_cost) if t.max_cost is not None else None
            if cost >= min_c and (max_c is None or cost <= max_c):
                return D(t.multiplier)

        return D(tiers[-1].multiplier)

    # ---------- Root ----------
    @app.get("/")
    def root():
        return redirect(url_for("dashboard"))

    # ---------- Dashboard ----------
    @app.get("/dashboard")
    @login_required
    def dashboard():
        status_filter = (request.args.get("status") or "open").strip().lower()
        status_map = {
            "open": "open",
            "estimate_sent": "estimate_sent",
            "work_in_progress": "work_in_progress",
            "completed": "closed",
        }
        ro_status = status_map.get(status_filter, "open")
        first_day = datetime.utcnow().replace(day=1, hour=0, minute=0, second=0, microsecond=0)
        paid = Document.query.join(RepairOrder, Document.ro_id == RepairOrder.id).filter(
            Document.doc_type == "invoice",
            Document.status == "paid",
            Document.created_at >= first_day,
            RepairOrder.deleted_at.is_(None),
        ).all()
        mtd_revenue = sum((D(d.total) for d in paid), start=Decimal("0.00")).quantize(Decimal("0.01"))
        paid_count = len(paid)
        aro = (mtd_revenue / paid_count).quantize(Decimal("0.01")) if paid_count else Decimal("0.00")

        ros = RepairOrder.query.filter(
            RepairOrder.status == ro_status,
            RepairOrder.deleted_at.is_(None),
        ).order_by(RepairOrder.opened_at.desc()).limit(24).all()
        cust_ids = list({r.customer_id for r in ros})
        veh_ids = list({r.vehicle_id for r in ros})
        customers = Customer.query.filter(Customer.id.in_(cust_ids)).all() if cust_ids else []
        vehicles = Vehicle.query.filter(Vehicle.id.in_(veh_ids)).all() if veh_ids else []
        cust_map = {str(c.id): c for c in customers}
        veh_map = {str(v.id): v for v in vehicles}

        ro_ids = [r.id for r in ros]
        docs = Document.query.filter(Document.ro_id.in_(ro_ids)).all() if ro_ids else []
        est_map = {d.ro_id: d for d in docs if d.doc_type == "estimate"}
        inv_map = {d.ro_id: d for d in docs if d.doc_type == "invoice"}

        sent_count = ROEvent.query.join(RepairOrder, ROEvent.ro_id == RepairOrder.id).filter(
            ROEvent.event_type == "estimate_sent",
            RepairOrder.deleted_at.is_(None),
        ).count()
        approved_count = ROEvent.query.join(RepairOrder, ROEvent.ro_id == RepairOrder.id).filter(
            ROEvent.event_type == "approved",
            RepairOrder.deleted_at.is_(None),
        ).count()
        close_ratio = round((approved_count / sent_count * 100), 1) if sent_count else 0.0

        return render_template(
            "dashboard.html",
            mtd_revenue=mtd_revenue,
            aro=aro,
            ros=ros,
            open_ros=ros,
            close_ratio=close_ratio,
            cust_map=cust_map,
            veh_map=veh_map,
            est_map=est_map,
            inv_map=inv_map,
            status_filter=status_filter,
        )


    # ---------- Job Board ----------
    @app.get("/job-board")
    @login_required
    def job_board():
        # Pull jobs that are approved or work in progress by default
        status = (request.args.get("status") or "active").strip().lower()
        q = Job.query.join(RepairOrder, Job.ro_id == RepairOrder.id).filter(RepairOrder.deleted_at.is_(None))

        if status == "approved":
            q = q.filter(Job.status == "approved")
        elif status == "wip":
            q = q.filter(Job.status == "work_in_progress")
        elif status == "completed":
            q = q.filter(Job.status == "completed")
        elif status == "all":
            q = q
        else:
            q = q.filter(Job.status.in_(["approved", "work_in_progress"]))

        jobs = q.order_by(Job.created_at.desc()).limit(500).all()

        # Enrich with RO + customer + vehicle for the template without needing relationships
        ro_ids = list({j.ro_id for j in jobs})
        ros = RepairOrder.query.filter(RepairOrder.id.in_(ro_ids)).all() if ro_ids else []
        ro_map = {r.id: r for r in ros}

        cust_ids = list({r.customer_id for r in ros})
        veh_ids = list({r.vehicle_id for r in ros})
        custs = Customer.query.filter(Customer.id.in_(cust_ids)).all() if cust_ids else []
        vehs = Vehicle.query.filter(Vehicle.id.in_(veh_ids)).all() if veh_ids else []
        cust_map = {c.id: c for c in custs}
        veh_map = {v.id: v for v in vehs}

        enriched = []
        for j in jobs:
            r = ro_map.get(j.ro_id)
            c = cust_map.get(r.customer_id) if r else None
            v = veh_map.get(r.vehicle_id) if r else None
            enriched.append({"job": j, "ro": r, "customer": c, "vehicle": v})

        return render_template("job_board.html", rows=enriched, status=status)

    # ---------- Settings: Matrices ----------
    @app.get("/settings/matrices")
    @login_required
    def matrices_settings():
        labor = LaborMatrixTier.query.order_by(LaborMatrixTier.min_hours.asc()).all()
        parts = PartsMatrixTier.query.order_by(PartsMatrixTier.min_cost.asc()).all()
        return render_template("settings_matrices.html", labor=labor, parts=parts)

    @app.post("/settings/matrices/labor/add")
    @login_required
    def matrices_labor_add():
        min_hours = parse_decimal(request.form.get("min_hours")) or Decimal("0.00")
        max_hours = parse_decimal(request.form.get("max_hours"))  # may be None
        rate = parse_decimal(request.form.get("rate_per_hour")) or Decimal("115.00")
        db.session.add(LaborMatrixTier(min_hours=min_hours, max_hours=max_hours, rate_per_hour=rate))
        db.session.commit()
        return redirect(url_for("matrices_settings"))

    @app.post("/settings/matrices/parts/add")
    @login_required
    def matrices_parts_add():
        min_cost = parse_decimal(request.form.get("min_cost")) or Decimal("0.00")
        max_cost = parse_decimal(request.form.get("max_cost"))  # may be None
        mult = parse_decimal(request.form.get("multiplier")) or Decimal("1.3000")
        db.session.add(PartsMatrixTier(min_cost=min_cost, max_cost=max_cost, multiplier=mult))
        db.session.commit()
        return redirect(url_for("matrices_settings"))

    @app.post("/settings/matrices/tier/<string:tier_id>/delete")
    @login_required
    def matrices_delete_tier(tier_id):
        # could be either table
        t = LaborMatrixTier.query.get(tier_id)
        if t:
            db.session.delete(t)
            db.session.commit()
            return redirect(url_for("matrices_settings"))
        t2 = PartsMatrixTier.query.get_or_404(tier_id)
        db.session.delete(t2)
        db.session.commit()
        return redirect(url_for("matrices_settings"))

    # ---------- Customers ----------
    @app.get("/customers")
    @login_required
    def customers():
        q = (request.args.get("q") or "").strip()
        query = Customer.query.filter(Customer.deleted_at.is_(None))
        if q:
            like = f"%{q}%"
            query = query.filter(or_(Customer.name.like(like), Customer.phone.like(like), Customer.email.like(like)))
        rows = query.order_by(Customer.created_at.desc()).limit(300).all()
        return render_template("customers.html", customers=rows, q=q)

    @app.get("/customers/<string:customer_id>")
    @login_required
    def customer_detail(customer_id):
        cust = Customer.query.get_or_404(customer_id)
        vehicles = Vehicle.query.filter_by(customer_id=cust.id).all()
        ros = RepairOrder.query.filter(
            RepairOrder.customer_id == cust.id,
            RepairOrder.deleted_at.is_(None),
        ).order_by(RepairOrder.opened_at.desc()).all()

        ro_ids = [r.id for r in ros]
        invs = Document.query.filter(Document.doc_type == "invoice", Document.ro_id.in_(ro_ids)).all() if ro_ids else []
        paid = [d for d in invs if d.status == "paid"]
        total_revenue = sum((D(d.total) for d in paid), start=Decimal("0.00")).quantize(Decimal("0.01"))

        return render_template("customer_detail.html", cust=cust, vehicles=vehicles, ros=ros, total_revenue=total_revenue)

    # ---------- API: Customer search + vehicles ----------
    @app.get("/api/customers/search")
    @login_required
    def api_customers_search():
        q = (request.args.get("q") or "").strip()
        if not q or len(q) < 2:
            return {"results": []}
        like = f"%{q}%"
        rows = Customer.query.filter(
            Customer.deleted_at.is_(None),
            or_(Customer.name.like(like), Customer.phone.like(like), Customer.email.like(like)),
        ).order_by(Customer.created_at.desc()).limit(10).all()

        return {"results": [{
            "id": c.id,
            "name": c.name,
            "phone": c.phone,
            "email": c.email,
            "address1": c.address1,
            "address2": c.address2,
            "city": c.city,
            "state": c.state,
            "postal_code": c.postal_code,
        } for c in rows]}

    @app.get("/api/customers/<string:customer_id>/vehicles")
    @login_required
    def api_customer_vehicles(customer_id):
        rows = Vehicle.query.filter_by(customer_id=customer_id).order_by(Vehicle.created_at.desc()).all()
        return {"results": [{
            "id": v.id,
            "label": f"{v.year or ''} {v.make or ''} {v.model or ''} {v.engine or ''}".strip(),
            "year": v.year, "make": v.make, "model": v.model, "engine": v.engine,
            "vin": v.vin, "odometer_last": v.odometer_last
        } for v in rows]}

    # ---------- API: NHTSA make/model ----------
    @app.get("/api/vehicle/makes")
    @login_required
    def api_vehicle_makes():
        year = (request.args.get("year") or "").strip()
        if not year.isdigit():
            return {"results": []}
        url = f"https://api.nhtsa.gov/products/vehicle/makes?modelYear={year}&issueType=r"
        r = requests.get(url, timeout=10)
        data = r.json()
        results = data.get("results") or data.get("Results") or []
        makes = sorted({(x.get("make") or x.get("Make") or "").strip() for x in results if (x.get("make") or x.get("Make"))})
        return {"results": makes}

    @app.get("/api/vehicle/models")
    @login_required
    def api_vehicle_models():
        year = (request.args.get("year") or "").strip()
        make = (request.args.get("make") or "").strip()
        if not year.isdigit() or not make:
            return {"results": []}
        url = f"https://api.nhtsa.gov/products/vehicle/models?modelYear={year}&make={make}&issueType=r"
        r = requests.get(url, timeout=10)
        data = r.json()
        results = data.get("results") or data.get("Results") or []
        models = sorted({(x.get("model") or x.get("Model") or "").strip() for x in results if (x.get("model") or x.get("Model"))})
        return {"results": models}



    # ---------- Calendar ----------
    @app.get("/calendar")
    @login_required
    def calendar_view():
        ros = RepairOrder.query.filter(RepairOrder.deleted_at.is_(None)).order_by(RepairOrder.opened_at.desc()).limit(200).all()
        cust_ids = list({r.customer_id for r in ros})
        veh_ids = list({r.vehicle_id for r in ros})
        customers = Customer.query.filter(Customer.id.in_(cust_ids)).all() if cust_ids else []
        vehicles = Vehicle.query.filter(Vehicle.id.in_(veh_ids)).all() if veh_ids else []
        cust_map = {c.id: c for c in customers}
        veh_map = {v.id: v for v in vehicles}
        ro_pick = []
        for ro in ros:
            cust = cust_map.get(ro.customer_id)
            veh = veh_map.get(ro.vehicle_id)
            vehicle_text = ""
            if veh:
                parts = [veh.year, veh.make, veh.model, veh.engine]
                vehicle_text = " ".join([str(p) for p in parts if p])
            ro_pick.append({
                "id": ro.id,
                "ro_number": ro.ro_number,
                "customer_name": cust.name if cust else "",
                "vehicle_text": vehicle_text,
            })
        return render_template("calendar.html", ro_pick=ro_pick)

    def calendar_events(start=None, end=None):
        q = Appointment.query
        if start:
            try:
                dt = datetime.fromisoformat(start.replace("Z",""))
                q = q.filter(Appointment.start_at >= dt)
            except Exception:
                pass
        if end:
            try:
                dt = datetime.fromisoformat(end.replace("Z",""))
                q = q.filter(Appointment.end_at <= dt)
            except Exception:
                pass
        appts = q.order_by(Appointment.start_at.asc()).limit(2000).all()
        events = []
        for a in appts:
            ro = RepairOrder.query.get(a.ro_id)
            title = a.title
            if ro:
                cust = Customer.query.get(ro.customer_id)
                veh = Vehicle.query.get(ro.vehicle_id)
                parts = [f"RO #{ro.ro_number}"]
                if cust and cust.name:
                    parts.append(cust.name)
                if veh and (veh.year or veh.make or veh.model):
                    y = veh.year or ""
                    m1 = veh.make or ""
                    m2 = veh.model or ""
                    parts.append(f"{y} {m1} {m2}".strip())
                title = " • ".join([p for p in parts if p])
            events.append({
                "id": a.id,
                "title": title,
                "start": a.start_at.isoformat(),
                "end": a.end_at.isoformat(),
                "extendedProps": {
                    "ro_id": a.ro_id,
                    "status": a.status,
                    "notes": a.notes,
                }
            })
        return events

    @app.get("/api/appointments")
    @login_required
    def api_appointments():
        start = request.args.get("start")
        end = request.args.get("end")
        return jsonify(calendar_events(start, end))

    @app.get("/api/calendar/events")
    @login_required
    def api_calendar_events():
        start = request.args.get("start")
        end = request.args.get("end")
        return jsonify(calendar_events(start, end))

    @app.get("/api/calendar/event/<string:appt_id>")
    @login_required
    def api_calendar_event(appt_id):
        appt = Appointment.query.get_or_404(appt_id)
        return jsonify({
            "id": appt.id,
            "title": appt.title,
            "ro_id": appt.ro_id,
            "start_at": appt.start_at.isoformat(),
            "end_at": appt.end_at.isoformat(),
            "status": appt.status,
            "notes": appt.notes,
        })

    def create_appointment_from_form():
        ro_id = (request.form.get("ro_id") or "").strip()
        title = (request.form.get("title") or "").strip() or "Appointment"
        start_at = (request.form.get("start_at") or "").strip()
        end_at = (request.form.get("end_at") or "").strip()
        status = (request.form.get("status") or "").strip() or "scheduled"
        notes = (request.form.get("notes") or "").strip() or None

        if not ro_id:
            abort(400)
        RepairOrder.query.get_or_404(ro_id)

        try:
            sdt = datetime.fromisoformat(start_at.replace("Z",""))
            edt = datetime.fromisoformat(end_at.replace("Z",""))
        except Exception:
            abort(400)

        appt = Appointment(
            id=gen_uuid(),
            ro_id=ro_id,
            title=title,
            start_at=sdt,
            end_at=edt,
            status=status,
            notes=notes,
            created_at=datetime.utcnow(),
        )
        db.session.add(appt)
        db.session.commit()
        return appt

    @app.post("/api/appointments")
    @login_required
    def api_appointments_create():
        appt = create_appointment_from_form()
        return {"ok": True, "id": appt.id}

    @app.post("/api/calendar/appointments")
    @login_required
    def api_calendar_appointments_create():
        appt = create_appointment_from_form()
        return {"ok": True, "id": appt.id}

    def update_appointment_from_form(appt_id):
        appt = Appointment.query.get_or_404(appt_id)
        title = (request.form.get("title") or "").strip()
        start_at = (request.form.get("start_at") or "").strip()
        end_at = (request.form.get("end_at") or "").strip()
        status = (request.form.get("status") or "").strip() or appt.status
        notes = (request.form.get("notes") or "").strip() or None

        if title:
            appt.title = title
        if start_at:
            appt.start_at = datetime.fromisoformat(start_at.replace("Z",""))
        if end_at:
            appt.end_at = datetime.fromisoformat(end_at.replace("Z",""))
        appt.status = status
        appt.notes = notes
        db.session.add(appt)
        db.session.commit()
        return appt

    @app.post("/api/appointments/<string:appt_id>/update")
    @login_required
    def api_appointments_update(appt_id):
        update_appointment_from_form(appt_id)
        return {"ok": True}

    @app.post("/api/calendar/appointments/<string:appt_id>/update")
    @login_required
    def api_calendar_appointments_update(appt_id):
        update_appointment_from_form(appt_id)
        return {"ok": True}

    def delete_appointment(appt_id):
        appt = Appointment.query.get_or_404(appt_id)
        db.session.delete(appt)
        db.session.commit()
        return {"ok": True}

    @app.post("/api/appointments/<string:appt_id>/delete")
    @login_required
    def api_appointments_delete(appt_id):
        return delete_appointment(appt_id)

    @app.post("/api/calendar/appointments/<string:appt_id>/delete")
    @login_required
    def api_calendar_appointments_delete(appt_id):
        return delete_appointment(appt_id)

    # ---------- RO list ----------
    @app.get("/ros")
    @login_required
    def ro_list():
        status = (request.args.get("status") or "all").strip()
        q = RepairOrder.query.filter(RepairOrder.deleted_at.is_(None))
        if status != "all":
            q = q.filter(RepairOrder.status == status)
        ros = q.order_by(RepairOrder.opened_at.desc()).limit(400).all()

        cust_ids = list({r.customer_id for r in ros})
        veh_ids = list({r.vehicle_id for r in ros})
        customers = Customer.query.filter(Customer.id.in_(cust_ids)).all() if cust_ids else []
        vehicles = Vehicle.query.filter(Vehicle.id.in_(veh_ids)).all() if veh_ids else []
        cust_map = {c.id: c for c in customers}
        veh_map = {v.id: v for v in vehicles}

        return render_template("ro_list.html", ros=ros, status=status, cust_map=cust_map, veh_map=veh_map)

    # ---------- RO create ----------
    @app.get("/ros/new", endpoint="ro_new")
    @login_required
    def ro_new_form():
        return render_template("ro_new.html", engine_presets=ENGINE_PRESETS)

    @app.post("/ros/new")
    @login_required
    def ro_new_create():
        existing_customer_id = (request.form.get("existing_customer_id") or "").strip() or None
        existing_vehicle_id = (request.form.get("existing_vehicle_id") or "").strip() or None

        if existing_customer_id:
            cust = Customer.query.get_or_404(existing_customer_id)
            cust.name = (request.form.get("customer_name") or cust.name).strip()
            cust.phone = (request.form.get("customer_phone") or cust.phone or "").strip() or None
            cust.email = (request.form.get("customer_email") or cust.email or "").strip() or None
            cust.address1 = (request.form.get("address1") or cust.address1 or "").strip() or None
            cust.address2 = (request.form.get("address2") or cust.address2 or "").strip() or None
            cust.city = (request.form.get("city") or cust.city or "").strip() or None
            cust.state = (request.form.get("state") or cust.state or "").strip() or None
            cust.postal_code = (request.form.get("postal_code") or cust.postal_code or "").strip() or None
            cust.source = (request.form.get("source") or cust.source or "").strip() or None
            db.session.add(cust)
        else:
            cust = Customer(
                name=(request.form.get("customer_name") or "").strip(),
                phone=(request.form.get("customer_phone") or "").strip() or None,
                email=(request.form.get("customer_email") or "").strip() or None,
                address1=(request.form.get("address1") or "").strip() or None,
                address2=(request.form.get("address2") or "").strip() or None,
                city=(request.form.get("city") or "").strip() or None,
                state=(request.form.get("state") or "").strip() or None,
                postal_code=(request.form.get("postal_code") or "").strip() or None,
                source=(request.form.get("source") or "").strip() or None,
            )
            db.session.add(cust)
            db.session.flush()

        def to_int(v):
            v = (v or "").strip()
            return int(v) if v.isdigit() else None

        if existing_vehicle_id:
            veh = Vehicle.query.get_or_404(existing_vehicle_id)
        else:
            veh = Vehicle(
                customer_id=cust.id,
                year=to_int(request.form.get("year")),
                make=(request.form.get("make") or "").strip() or None,
                model=(request.form.get("model") or "").strip() or None,
                engine=(request.form.get("engine") or "").strip() or None,
                vin=(request.form.get("vin") or "").strip() or None,
                odometer_last=to_int(request.form.get("odometer_last")),
            )
            db.session.add(veh)
            db.session.flush()

        last_num = db.session.query(func.max(RepairOrder.ro_number)).scalar() or 1000
        ro = RepairOrder(
            ro_number=last_num + 1,
            customer_id=cust.id,
            vehicle_id=veh.id,
            status="open",
            concern=(request.form.get("concern") or "").strip() or None,
        )
        db.session.add(ro)
        db.session.flush()
        log_event(ro.id, "created", None, "open")

        est = Document(ro_id=ro.id, doc_type="estimate", version=1, status="draft")
        inv = Document(ro_id=ro.id, doc_type="invoice", version=1, status="draft")
        db.session.add(est)
        db.session.add(inv)
        db.session.commit()

        ensure_default_job(ro.id)
        return redirect(url_for("ro_detail", ro_id=ro.id, tab="estimate"))

    # ---------- RO detail ----------
    @app.get("/ros/<string:ro_id>")
    @login_required
    def ro_detail(ro_id):
        tab = (request.args.get("tab") or "estimate").strip().lower()
        if tab not in ("estimate", "invoice", "activity", "wip"):
            tab = "estimate"

        ro = RepairOrder.query.get_or_404(ro_id)
        customer = Customer.query.get_or_404(ro.customer_id)
        vehicle = Vehicle.query.get_or_404(ro.vehicle_id)

        estimate = get_or_create_doc(ro.id, "estimate")
        invoice = get_or_create_doc(ro.id, "invoice")
        ensure_share_token(estimate)
        ensure_share_token(invoice)

        ensure_default_job(ro.id)

        jobs = Job.query.filter_by(ro_id=ro.id).order_by(Job.sort_order.asc(), Job.created_at.asc()).all()
        technicians = Technician.query.order_by(Technician.name.asc()).all()



        recalc_document_totals(estimate)
        recalc_document_totals(invoice)
        db.session.commit()

        est_items = LineItem.query.filter_by(document_id=estimate.id).order_by(LineItem.created_at.asc()).all()
        inv_items = LineItem.query.filter_by(document_id=invoice.id).order_by(LineItem.created_at.asc()).all()

        def group_items(items):
            grouped = {}
            unassigned = []
            for li in items:
                if li.job_id:
                    grouped.setdefault(li.job_id, []).append(li)
                else:
                    unassigned.append(li)
            return grouped, unassigned

        est_items_by_job, est_unassigned_items = group_items(est_items)
        inv_items_by_job, inv_unassigned_items = group_items(inv_items)

        est_job_totals = job_totals(estimate.id)
        inv_job_totals = job_totals(invoice.id)
        job_labor_hours = {j.id: labor_hours_for_job(estimate.id, j.id) for j in jobs}

        est_profit = calc_profit_for_doc(estimate.id)
        inv_profit = calc_profit_for_doc(invoice.id)

        events = ROEvent.query.filter_by(ro_id=ro.id).order_by(ROEvent.created_at.desc()).limit(80).all()

        est_share_url = url_for("share_view", token=estimate.share_token, _external=True)
        inv_share_url = url_for("share_view", token=invoice.share_token, _external=True)

        return render_template(
            "ro_detail.html",
            ro=ro, customer=customer, vehicle=vehicle,
            estimate=estimate, invoice=invoice,
            jobs=jobs,
            est_items=est_items, inv_items=inv_items,
            est_items_by_job=est_items_by_job,
            inv_items_by_job=inv_items_by_job,
            est_unassigned_items=est_unassigned_items,
            inv_unassigned_items=inv_unassigned_items,
            est_job_totals=est_job_totals, inv_job_totals=inv_job_totals,
            est_profit=est_profit, inv_profit=inv_profit,
            events=events,
            est_share_url=est_share_url,
            inv_share_url=inv_share_url,
            technicians=technicians,
            job_labor_hours=job_labor_hours,
            active_tab=tab,
        )

    @app.post("/ros/<string:ro_id>/status")
    @login_required
    def ro_change_status(ro_id):
        ro = RepairOrder.query.get_or_404(ro_id)
        new_status = (request.form.get("status") or "").strip()
        if new_status not in ("open", "estimate_sent", "work_in_progress", "closed", "canceled"):
            flash("Invalid status.")
            return redirect(url_for("ro_detail", ro_id=ro.id, tab=request.form.get("return_tab") or "estimate"))

        old = ro.status
        ro.status = new_status
        if new_status == "closed" and ro.closed_at is None:
            ro.closed_at = datetime.utcnow()
        if new_status != "closed":
            ro.closed_at = None

        db.session.add(ro)
        log_event(ro.id, "ro_status", old, new_status)
        db.session.commit()

        return redirect(url_for("ro_detail", ro_id=ro.id, tab=request.form.get("return_tab") or "estimate"))

    @app.post("/ros/<string:ro_id>/delete")
    @login_required
    def ro_delete(ro_id):
        ro = RepairOrder.query.get_or_404(ro_id)
        if ro.deleted_at is None:
            ro.deleted_at = datetime.utcnow()
            db.session.add(ro)
            log_event(ro.id, "ro_deleted", None, ro.deleted_at.isoformat())
            db.session.commit()
        flash("Repair order archived.")
        return redirect(url_for("ro_list"))

    @app.post("/customers/<string:customer_id>/delete")
    @login_required
    def customer_delete(customer_id):
        cust = Customer.query.get_or_404(customer_id)
        if cust.deleted_at is None:
            cust.deleted_at = datetime.utcnow()
            db.session.add(cust)
            db.session.commit()
        flash("Customer archived.")
        return redirect(url_for("customers"))

    @app.post("/jobs/<string:job_id>/status")
    @login_required
    def job_set_status(job_id):
        job = Job.query.get_or_404(job_id)
        ro = RepairOrder.query.get_or_404(job.ro_id)

        new_status = (request.form.get("status") or "").strip()
        if new_status not in ("pending", "approved", "work_in_progress", "completed", "declined"):
            flash("Invalid job status.")
            return redirect(url_for("ro_detail", ro_id=ro.id, tab=request.form.get("return_tab") or "estimate"))

        old = job.status
        job.status = new_status
        if new_status == "completed" and job.completed_at is None:
            job.completed_at = datetime.utcnow()
        db.session.add(job)
        log_event(ro.id, "job_status", f"{job.title}:{old}", f"{job.title}:{new_status}")

        # Optional convenience: if ANY job is approved/WIP, set RO to WIP
        if new_status in ("approved", "work_in_progress") and ro.status in ("open", "estimate_sent"):
            ro.status = "work_in_progress"
            db.session.add(ro)

        if new_status == "completed":
            remaining = Job.query.filter_by(ro_id=ro.id).filter(Job.status != "completed").count()
            if remaining == 0:
                ro.status = "closed"
                ro.closed_at = datetime.utcnow()
                db.session.add(ro)
                log_event(ro.id, "ro_completed", None, ro.closed_at.isoformat())

        db.session.commit()
        return redirect(url_for("ro_detail", ro_id=ro.id, tab=request.form.get("return_tab") or "estimate"))

    # ---------- Jobs ----------
    @app.post("/ros/<string:ro_id>/jobs/add")
    @login_required
    def job_add(ro_id):
        title = (request.form.get("title") or "").strip() or "New Job"
        max_sort = db.session.query(func.max(Job.sort_order)).filter(Job.ro_id == ro_id).scalar() or 0
        db.session.add(Job(ro_id=ro_id, title=title, status="pending", sort_order=max_sort + 1))
        log_event(ro_id, "job_added", None, title)
        db.session.commit()
        return redirect(url_for("ro_detail", ro_id=ro_id, tab=request.form.get("return_tab") or "estimate"))



    @app.post("/jobs/<string:job_id>/edit")
    @login_required
    def job_edit(job_id):
        job = Job.query.get_or_404(job_id)
        ro = RepairOrder.query.get_or_404(job.ro_id)
        title = (request.form.get("title") or "").strip()
        if not title:
            flash("Job name is required.")
            return redirect(url_for("ro_detail", ro_id=ro.id, tab=request.form.get("return_tab") or "estimate"))
        old = job.title
        job.title = title
        db.session.add(job)
        log_event(ro.id, "job_renamed", old, title)
        db.session.commit()
        return redirect(url_for("ro_detail", ro_id=ro.id, tab=request.form.get("return_tab") or "estimate"))

    @app.post("/jobs/<string:job_id>/delete")
    @login_required
    def job_delete(job_id):
        job = Job.query.get_or_404(job_id)
        ro_id = job.ro_id

        # Prevent deleting if it would orphan existing line items: move them to None-job bucket
        items = LineItem.query.filter_by(job_id=job.id).all()
        for li in items:
            li.job_id = None
            db.session.add(li)

        db.session.delete(job)
        log_event(ro_id, "job_deleted", job_id, None)
        db.session.commit()
        return redirect(url_for("ro_detail", ro_id=ro_id, tab=request.form.get("return_tab") or "estimate"))

    @app.post("/jobs/<string:job_id>/complete")
    @login_required
    def job_complete(job_id):
        job = Job.query.get_or_404(job_id)
        ro = RepairOrder.query.get_or_404(job.ro_id)
        tech_id = (request.form.get("tech_id") or "").strip() or None

        if tech_id:
            job.tech_id = tech_id

        if job.status != "completed":
            job.status = "completed"
            job.completed_at = datetime.utcnow()
            log_event(ro.id, "job_completed", None, job.title)

        estimate = get_or_create_doc(ro.id, "estimate")
        hours = labor_hours_for_job(estimate.id, job.id)

        if tech_id and hours > 0:
            tech = Technician.query.get(tech_id)
            if tech:
                tech.total_hours = D(tech.total_hours) + hours
                db.session.add(tech)

        db.session.add(job)

        remaining = Job.query.filter_by(ro_id=ro.id).filter(Job.status != "completed").count()
        if remaining == 0:
            ro.status = "closed"
            ro.closed_at = datetime.utcnow()
            db.session.add(ro)
            log_event(ro.id, "ro_completed", None, ro.closed_at.isoformat())

        db.session.commit()
        return redirect(url_for("ro_detail", ro_id=ro.id, tab="wip"))

    @app.post("/techs/add")
    @login_required
    def tech_add():
        name = (request.form.get("name") or "").strip()
        ro_id = (request.form.get("ro_id") or "").strip()
        if not name:
            flash("Technician name is required.")
            return redirect(url_for("ro_detail", ro_id=ro_id, tab="wip"))
        db.session.add(Technician(name=name))
        db.session.commit()
        return redirect(url_for("ro_detail", ro_id=ro_id, tab="wip"))
    # ---------- Line items (MATRIX MAGIC HERE) ----------
    @app.post("/docs/<string:doc_id>/items/add")
    @login_required
    def add_line_item(doc_id):
        doc = Document.query.get_or_404(doc_id)

        if doc.status in ("locked", "paid") or doc.locked_at is not None:
            flash("Document is locked.")
            return redirect(url_for(
                "ro_detail",
                ro_id=doc.ro_id,
                tab=request.form.get("return_tab") or "estimate"
            ))

        # Always normalize once
        item_type = (request.form.get("item_type") or "").strip().lower()
        description = (request.form.get("description") or "").strip()
        job_id = (request.form.get("job_id") or "").strip() or None

        qty_in = parse_decimal(request.form.get("qty"))
        qty = qty_in if qty_in is not None else Decimal("1.00")

        taxable = "taxable" in request.form

        # Initialize everything so nothing is "left over"
        cost_in = None
        hours_in = None
        unit_price_in = None
        unit_price = Decimal("0.00")

        # ---------------- LABOR ----------------
        if item_type == "labor":
            hours_in = parse_decimal(request.form.get("labor_hours"))
            # optional override rate for labor, if you ever add it
            unit_price_in = parse_decimal(request.form.get("labor_rate"))

            if hours_in is None:
                flash("Labor requires hours.")
                return redirect(url_for("ro_detail", ro_id=doc.ro_id, tab=request.form.get("return_tab") or "estimate"))

            qty = Decimal(hours_in)  # qty = hours
            rate = get_labor_rate_for_hours(qty)  # qty already hours

            unit_price = unit_price_in if unit_price_in is not None else rate
            taxable = False

        # ---------------- PART ----------------
        elif item_type == "part":
            cost_in = parse_decimal(request.form.get("part_cost"))
            unit_price_in = parse_decimal(request.form.get("part_price"))  # OPTIONAL override

            if cost_in is None:
                flash("Parts require cost.")
                return redirect(url_for("ro_detail", ro_id=doc.ro_id, tab=request.form.get("return_tab") or "estimate"))

            multiplier = get_parts_multiplier_for_cost(Decimal(cost_in))

            # Matrix if no override price
            if unit_price_in is None:
                unit_price = (Decimal(cost_in) * Decimal(multiplier)).quantize(Decimal("0.01"))
            else:
                unit_price = unit_price_in

            taxable = True

        # ---------------- FEE ----------------
        elif item_type == "fee":
            unit_price_in = parse_decimal(request.form.get("fee_price"))
            cost_in = parse_decimal(request.form.get("fee_cost"))  # optional, if you keep it

            if unit_price_in is None:
                flash("Fee requires a unit price.")
                return redirect(url_for("ro_detail", ro_id=doc.ro_id, tab=request.form.get("return_tab") or "estimate"))

            unit_price = unit_price_in
            # taxable checkbox decides

        # ---------------- DISCOUNT ----------------
        elif item_type == "discount":
            unit_price_in = parse_decimal(request.form.get("discount_amount"))
            cost_in = parse_decimal(request.form.get("discount_cost"))  # optional, if you keep it

            if unit_price_in is None:
                flash("Discount requires an amount.")
                return redirect(url_for("ro_detail", ro_id=doc.ro_id, tab=request.form.get("return_tab") or "estimate"))

            unit_price = abs(unit_price_in) * Decimal("-1.00")
            taxable = False

        else:
            flash("Invalid line item type.")
            return redirect(url_for(
                "ro_detail",
                ro_id=doc.ro_id,
                tab=request.form.get("return_tab") or "estimate"
            ))

        li = LineItem(
            document_id=doc.id,
            job_id=job_id,
            item_type=item_type,
            description=description,
            qty=qty,
            unit_price=unit_price,
            taxable=taxable,
            labor_hours=hours_in,
            cost=cost_in,
        )

        db.session.add(li)
        db.session.commit()

        recalc_document_totals(doc)
        db.session.commit()

        return redirect(url_for(
            "ro_detail",
            ro_id=doc.ro_id,
            tab=request.form.get("return_tab") or "estimate"
        ))



    @app.post("/items/<string:item_id>/delete")
    @login_required
    def delete_item(item_id):
        li = LineItem.query.get_or_404(item_id)
        doc = Document.query.get_or_404(li.document_id)

        if doc.status in ("locked", "paid") or doc.locked_at is not None:
            flash("Document is locked.")
            return redirect(url_for("ro_detail", ro_id=doc.ro_id, tab="invoice" if doc.doc_type == "invoice" else "estimate"))

        db.session.delete(li)
        db.session.commit()

        recalc_document_totals(doc)
        db.session.commit()

        tab = (request.form.get("return_tab") or ("invoice" if doc.doc_type == "invoice" else "estimate")).strip().lower()
        return redirect(url_for("ro_detail", ro_id=doc.ro_id, tab=tab))



    @app.post("/items/<string:item_id>/edit")
    @login_required
    def edit_item(item_id):
        li = LineItem.query.get_or_404(item_id)
        doc = Document.query.get_or_404(li.document_id)

        if doc.status in ("locked", "paid") or doc.locked_at is not None:
            flash("Document is locked.")
            return redirect(url_for("ro_detail", ro_id=doc.ro_id, tab="invoice" if doc.doc_type == "invoice" else "estimate"))

        # Allow editing basic fields; keep matrix logic optional
        description = (request.form.get("description") or li.description).strip()
        qty_in = parse_decimal(request.form.get("qty"))
        unit_price_in = parse_decimal(request.form.get("unit_price"))
        taxable = "taxable" in request.form

        # Per-type optional fields
        cost_in = parse_decimal(request.form.get("cost"))
        hours_in = parse_decimal(request.form.get("labor_hours"))
        job_id = (request.form.get("job_id") or "").strip() or None

        li.description = description
        if qty_in is not None:
            li.qty = qty_in
        if unit_price_in is not None:
            li.unit_price = unit_price_in
        li.taxable = taxable
        li.job_id = job_id

        # Only update if provided
        if cost_in is not None or request.form.get("cost") == "0":
            li.cost = cost_in
        if hours_in is not None or request.form.get("labor_hours") == "0":
            li.labor_hours = hours_in

        db.session.add(li)
        db.session.commit()

        recalc_document_totals(doc)
        db.session.commit()

        tab = (request.form.get("return_tab") or ("invoice" if doc.doc_type == "invoice" else "estimate")).strip().lower()
        flash("Line item updated.")
        return redirect(url_for("ro_detail", ro_id=doc.ro_id, tab=tab))

    # ---------- Document actions ----------
    @app.post("/docs/<string:doc_id>/lock")
    @login_required
    def lock_document(doc_id):
        doc = Document.query.get_or_404(doc_id)
        recalc_document_totals(doc)

        if doc.doc_type == "estimate":
            doc.sent_at = datetime.utcnow()
            doc.status = "sent"
            log_event(doc.ro_id, "estimate_sent", None, doc.id)
            ro = RepairOrder.query.get_or_404(doc.ro_id)
            if ro.status == "open":
                ro.status = "estimate_sent"
                db.session.add(ro)
        else:
            doc.status = "locked"

        doc.locked_at = datetime.utcnow()
        db.session.add(doc)
        db.session.commit()

        return redirect(url_for("ro_detail", ro_id=doc.ro_id, tab="invoice" if doc.doc_type == "invoice" else "estimate"))

    @app.post("/docs/<string:doc_id>/share")
    @login_required
    def share_document(doc_id):
        doc = Document.query.get_or_404(doc_id)
        ensure_share_token(doc)
        recalc_document_totals(doc)

        if doc.doc_type == "estimate":
            if doc.sent_at is None:
                doc.sent_at = datetime.utcnow()
            doc.status = "sent"
            log_event(doc.ro_id, "estimate_sent", None, doc.id)
            ro = RepairOrder.query.get_or_404(doc.ro_id)
            if ro.status == "open":
                ro.status = "estimate_sent"
                db.session.add(ro)

        db.session.add(doc)
        db.session.commit()

        return jsonify({"url": url_for("share_view", token=doc.share_token, _external=True)})

    @app.post("/docs/<string:doc_id>/approve")
    @login_required
    def approve_estimate(doc_id):
        est = Document.query.get_or_404(doc_id)
        if est.doc_type != "estimate":
            abort(400)

        est.status = "approved"
        db.session.add(est)
        log_event(est.ro_id, "approved", None, est.id)

        ro = RepairOrder.query.get_or_404(est.ro_id)
        ro.status = "work_in_progress"
        db.session.add(ro)

        invoice = Document.query.filter_by(ro_id=ro.id, doc_type="invoice", version=1).first()
        if not invoice:
            invoice = Document(ro_id=ro.id, doc_type="invoice", version=1, status="draft")
            db.session.add(invoice)
            db.session.flush()

        if invoice.status in ("locked", "paid") or invoice.locked_at is not None:
            db.session.commit()
            return redirect(url_for("ro_detail", ro_id=ro.id, tab="invoice"))

        LineItem.query.filter_by(document_id=invoice.id).delete()
        for i in LineItem.query.filter_by(document_id=est.id).all():
            db.session.add(LineItem(
                document_id=invoice.id,
                job_id=i.job_id,
                item_type=i.item_type,
                description=i.description,
                qty=i.qty,
                unit_price=i.unit_price,
                taxable=i.taxable,
                labor_hours=i.labor_hours,
                cost=i.cost,
            ))

        db.session.commit()
        recalc_document_totals(invoice)
        db.session.commit()

        return redirect(url_for("ro_detail", ro_id=ro.id, tab="invoice"))

    @app.post("/docs/<string:doc_id>/decline")
    @login_required
    def decline_estimate(doc_id):
        doc = Document.query.get_or_404(doc_id)
        if doc.doc_type != "estimate":
            abort(400)
        doc.status = "declined"
        db.session.add(doc)
        log_event(doc.ro_id, "declined", None, doc.id)
        db.session.commit()
        return redirect(url_for("ro_detail", ro_id=doc.ro_id, tab="estimate"))

    @app.post("/docs/<string:doc_id>/mark_paid")
    @login_required
    def mark_invoice_paid(doc_id):
        doc = Document.query.get_or_404(doc_id)
        if doc.doc_type != "invoice":
            abort(400)
        doc.status = "paid"
        db.session.add(doc)
        log_event(doc.ro_id, "paid", None, doc.id)
        db.session.commit()
        return redirect(url_for("ro_detail", ro_id=doc.ro_id, tab="invoice"))

    # ---------- Share ----------
    @app.get("/share/<string:token>")
    def share_view(token):
        doc = Document.query.filter_by(share_token=token).first_or_404()
        ro = RepairOrder.query.get_or_404(doc.ro_id)
        cust = Customer.query.get_or_404(ro.customer_id)
        veh = Vehicle.query.get_or_404(ro.vehicle_id)

        items = LineItem.query.filter_by(document_id=doc.id).order_by(LineItem.created_at.asc()).all()
        recalc_document_totals(doc)
        db.session.commit()

        def group_items(items):
            grouped = {}
            unassigned = []
            for li in items:
                if li.job_id:
                    grouped.setdefault(li.job_id, []).append(li)
                else:
                    unassigned.append(li)
            return grouped, unassigned

        items_by_job, unassigned_items = group_items(items)
        job_ids = list(items_by_job.keys())
        jobs = []
        if job_ids:
            jobs = Job.query.filter(Job.id.in_(job_ids)).order_by(Job.sort_order.asc(), Job.created_at.asc()).all()
        job_totals_map = job_totals(doc.id)

        pdf_url = url_for("share_doc_pdf", token=token)
        return render_template(
            "share_doc.html",
            doc=doc,
            ro=ro,
            customer=cust,
            vehicle=veh,
            items=items,
            items_by_job=items_by_job,
            unassigned_items=unassigned_items,
            jobs=jobs,
            job_totals=job_totals_map,
            pdf_url=pdf_url,
        )

    @app.post("/share/<string:token>/jobs/<string:job_id>/status")
    def share_job_status(token, job_id):
        doc = Document.query.filter_by(share_token=token).first_or_404()
        if doc.doc_type != "estimate":
            abort(400)

        job = Job.query.get_or_404(job_id)
        if job.ro_id != doc.ro_id:
            abort(404)

        new_status = (request.form.get("status") or "").strip()
        if new_status not in ("approved", "declined"):
            abort(400)

        old = job.status
        job.status = new_status
        db.session.add(job)
        log_event(doc.ro_id, "job_status", f"{job.title}:{old}", f"{job.title}:{new_status}")

        if new_status == "approved":
            ro = RepairOrder.query.get_or_404(job.ro_id)
            if ro.status in ("open", "estimate_sent"):
                ro.status = "work_in_progress"
                db.session.add(ro)

        db.session.commit()
        return redirect(url_for("share_view", token=token))

    @app.get("/share/<string:token>/document.pdf")
    def share_doc_pdf(token):
        doc = Document.query.filter_by(share_token=token).first_or_404()
        ro = RepairOrder.query.get_or_404(doc.ro_id)
        cust = Customer.query.get_or_404(ro.customer_id)
        veh = Vehicle.query.get_or_404(ro.vehicle_id)

        items = LineItem.query.filter_by(document_id=doc.id).order_by(LineItem.created_at.asc()).all()
        recalc_document_totals(doc)
        db.session.commit()

        pdf_buf = build_document_pdf(ro, cust, veh, doc, items, title=doc.doc_type.capitalize())
        filename = f"{doc.doc_type.capitalize()}_RO_{ro.ro_number}.pdf"
        return send_file(pdf_buf, mimetype="application/pdf", as_attachment=False, download_name=filename)

    # ---------- PDF ----------
    @app.get("/ros/<string:ro_id>/invoice.pdf")
    @login_required
    def invoice_pdf(ro_id):
        ro = RepairOrder.query.get_or_404(ro_id)
        cust = Customer.query.get_or_404(ro.customer_id)
        veh = Vehicle.query.get_or_404(ro.vehicle_id)

        invoice = get_or_create_doc(ro.id, "invoice")
        items = LineItem.query.filter_by(document_id=invoice.id).order_by(LineItem.created_at.asc()).all()
        recalc_document_totals(invoice)
        db.session.commit()

        pdf_buf = build_invoice_pdf(ro, cust, veh, invoice, items)
        return send_file(pdf_buf, mimetype="application/pdf", as_attachment=False,
                         download_name=f"Invoice_RO_{ro.ro_number}.pdf")

    @app.get("/ros/<string:ro_id>/estimate.pdf")
    @login_required
    def estimate_pdf(ro_id):
        ro = RepairOrder.query.get_or_404(ro_id)
        cust = Customer.query.get_or_404(ro.customer_id)
        veh = Vehicle.query.get_or_404(ro.vehicle_id)

        estimate = get_or_create_doc(ro.id, "estimate")
        items = LineItem.query.filter_by(document_id=estimate.id).order_by(LineItem.created_at.asc()).all()
        recalc_document_totals(estimate)
        db.session.commit()

        pdf_buf = build_document_pdf(ro, cust, veh, estimate, items, title="Estimate")
        return send_file(pdf_buf, mimetype="application/pdf", as_attachment=False,
                         download_name=f"Estimate_RO_{ro.ro_number}.pdf")

    return app

app = create_app()

if __name__ == "__main__":
    app.run(debug=True)
