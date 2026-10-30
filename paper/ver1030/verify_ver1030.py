"""Exact identities and source checks; not a certificate of the global proof."""
from pathlib import Path
import hashlib
import json
import re
import sympy as s

checks = {}


def check(name, expression):
    reduced = s.simplify(s.expand_trig(expression))
    if reduced != 0:
        raise AssertionError((name, reduced))
    checks[name] = "PASS"


# The positively oriented Darboux frame and the scaled ruling.
k, tau, tp, f, g, xi, xip, u = s.symbols(
    "k tau tp f g xi xip u", real=True
)


def derivative(vector):
    ordinary = (vector.diff(f)*(-k*g)
                + vector.diff(g)*(xi+k*f)
                + vector.diff(xi)*xip + vector.diff(tau)*tp)
    connection = s.Matrix([-k*vector[1],
                           k*vector[0]-tau*vector[2], tau*vector[1]])
    return ordinary + connection


T = s.Matrix([1, 0, 0])
V = s.Matrix([g, f, 0])
Vs = derivative(V)
Vss = derivative(Vs)
Rs = T + u*Vs
area_vector = Rs.cross(V)
A = (xip-tp*xi/tau+g*tau**2)/2
check("scaled ruling determinant", s.det(s.Matrix.hstack(T, V, Vs))-f*f*tau)
check("scaled ruling derivative E component", Vs[1])
check("scaled ruling mixed second coefficient", Vs.dot(area_vector)-f*f*tau)
check("scaled ruling ss second coefficient",
      (k*s.Matrix([0, 1, 0])+u*Vss).dot(area_vector)
      -f*f*tp*u+2*f*f*tau*A*u*u)
rho, rp, rpp = s.symbols("rho rp rpp", positive=True)
Arho = (xip+2*rp*xi/rho+g/rho**4)/2
total_derivative = rho*xip+2*rp*xi+rpp*g+rp*k*f
check("linear period exact derivative",
      2*rho*Arho-(g*(rho**-3-rpp)-f*k*rp)-total_derivative)

# Spherical normal curve with the manuscript's sign convention.
n = s.Matrix([0, 0, 1])
ns = derivative(n)
nss = derivative(ns)
check("spherical normal speed squared", ns.dot(ns)-tau*tau)
check("spherical geodesic curvature numerator", nss.dot(n.cross(ns))-k*tau*tau)
check("asymptotic curve curvature squared", derivative(T).dot(derivative(T))-k*k)

# Integration by parts for the signed normal flux.
S, Su, uc, p, pc, Delta = s.symbols("S Su uc p pc Delta")
flux = (S*pc-uc*Su*p)/(2*Delta)
total_derivative = (uc*Su*p+S*pc)/(2*Delta)
check("flux integration by parts",
      flux-total_derivative+uc*Su*p/Delta)

# Normalization changes the geometric curvature scale using actual arclength.
r, rs, rss, speed, sp, spp = s.symbols("r rs rss speed sp spp", positive=True)
new_rho = s.sqrt(speed)*r


def derivative_in_old_parameter(value):
    return (value.diff(r)*rs+value.diff(rs)*rss
            +value.diff(speed)*sp+value.diff(sp)*spp)


new_second = derivative_in_old_parameter(
    derivative_in_old_parameter(new_rho)/speed)/speed
check("normalization curvature-scale derivative",
      new_second.subs({speed:1, sp:0})-rss-r*spp/2)
check("normalization preparation condition",
      (new_rho**-3-new_second).subs({speed:1, sp:0})-(r**-3-rss-r*spp/2))
kp = s.symbols("kp", real=True)
Ts = derivative(T)
Tss = derivative(Ts)+Ts.diff(k)*kp
check("closure moments from tangent span",
      s.det(s.Matrix.hstack(T, Ts, Tss))-k*k*tau)

root = Path(__file__).resolve().parent
source = root / "main.tex"
body = source.read_text(encoding="utf-8")
labels = re.findall(r"\\label\{([^}]+)\}", body)
references = re.findall(r"\\(?:eqref|ref)\{([^}]+)\}", body)
assert len(labels) == len(set(labels)), "Duplicate labels"
assert not (set(references)-set(labels)), "Missing reference target"
assert not re.search(r"ver61[0123]|TODO|FIXME|PLACEHOLDER", body, flags=re.I)
assert len(re.findall(r"\\bibitem\{", body)) == 9
assert "eq:height-curvature" not in body
assert "eq:body" not in body
assert "def:planar-jets" not in body
assert "eq:bgqr-poly" not in body
assert "eq:own-inflection" not in body
assert "sec:independent" not in body
assert "Lelieuvre" not in body
assert all(label in labels for label in ("thm:seed","thm:one-curve","prop:pair","prop:ruled","thm:band-bending","prop:insert","lem:globalize"))
checks["source references and replacement scope"] = "PASS"
# The revised seed proof is the only mathematical source replacement.
seed_start = body.index(r"\section{The BGQR annulus")
seed_end = body.index(r"\section{The Darboux", seed_start)
assert hashlib.sha256(body[:seed_start].encode()).hexdigest() == "308d19a07fb9c37b055aaf90957a7d05e41b86bb1cb2d5a328ef7457bf8984ec"
assert hashlib.sha256(body[seed_end:].encode()).hexdigest() == "4231add5cd8840db63962b844aee166fb8d2cce11befa480e3430f12e89ed3f9"
checks["unchanged mathematical source outside seed section"] = "PASS"
report = {
    "source": source.name,
    "sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
    "checks": checks,
    "scope": "Exact algebra and source consistency only. Analytic, topological, and existence arguments are in the manuscript. No Lean certificate is asserted.",
}
(root / "verification.json").write_text(json.dumps(report, indent=2)+"\n", encoding="utf-8")
print(f"PASS: {len(checks)} exact algebra and source checks")
