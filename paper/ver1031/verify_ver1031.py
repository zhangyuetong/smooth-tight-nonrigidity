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


# Scaled-normal acceleration, including the torsion sign convention.
def full_derivative(vector):
    return derivative(vector)+vector.diff(rho)*rp+vector.diff(rp)*rpp

scaled_second=full_derivative(full_derivative(rho*n))
expected=(rpp-rho*tau*tau)*n+rho*tau*k*T-(2*rp*tau+rho*tp)*s.Matrix([0,1,0])
for i,component in enumerate(scaled_second-expected):
    check("scaled normal acceleration component "+str(i),component)
check("scaled normal transverse cancellation",scaled_second[1].subs(tp,-2*rp*tau/rho))
check("scaled normal curvature weight",(scaled_second[2]-(rpp-rho**-3)).subs(tau*tau,rho**-4))

# The two Codazzi identities and their flux functional.
sigma,W=s.symbols("sigma W",nonzero=True)
aa,bb,cc,dd=s.symbols("aa bb cc dd",real=True)
sig_s,Ws=(aa-bb)*sigma,(aa+bb)*W
sig_c,Wc=(dd-cc)*sigma,(cc+dd)*W
check("Codazzi periodic positive factor",(sig_s/sigma+Ws/W)/2-aa)
ratio_c=(Wc*sigma-W*sig_c)/sigma**2
check("second Codazzi flux ratio",ratio_c-2*cc*W/sigma)
p,pc,ratio,rc=s.symbols("p pc ratio rc")
h=(pc-2*cc*p)/(2*sigma)
check("mixed strain normal displacement",pc-2*cc*p-2*h*sigma)
check("geometric flux density",h*W-(W*pc/sigma-ratio_c*p)/2)
check("geometric flux integration by parts",
      (ratio*pc-rc*p)/2-(rc*p+ratio*pc)/2+rc*p)

# Generic affine ruling area and mixed second coefficient.
us,ucs=s.symbols("us ucs",real=True)
uc=s.symbols("uc",positive=True)
core_tangent=s.Matrix(s.symbols("t0:3",real=True))
ruling=s.Matrix(s.symbols("v0:3",real=True))
ruling_s=s.Matrix(s.symbols("w0:3",real=True))
triple=s.det(s.Matrix.hstack(core_tangent,ruling,ruling_s))
Bs=core_tangent+us*ruling+u*ruling_s
Bc=uc*ruling
Bsc=ucs*ruling+uc*ruling_s
check("affine mixed coefficient numerator",
      s.det(s.Matrix.hstack(Bsc,Bs,Bc))-uc*uc*triple)
area=(core_tangent+u*ruling_s).cross(ruling)
area_squared=area.dot(area)
linear=s.diff(area_squared,u).subs(u,0)
quadratic=ruling_s.cross(ruling).dot(ruling_s.cross(ruling))
check("squared ruling area derivative",
      s.diff(area_squared,u)-linear-2*quadratic*u)

# The positive geometric factor has the SAME sign as Delta in direct coordinates.
dpos=s.symbols("dpos",positive=True)
Su=s.symbols("Su",real=True)
Q=s.sqrt(dpos)*uc
check("direct positive determinant flux sign",
      Q*uc*Su/dpos-uc*uc*Su/s.sqrt(dpos))
check("direct negative determinant flux sign",
      Q*uc*Su/(-dpos)+uc*uc*Su/s.sqrt(dpos))

# Quotient normalization and the all-order vanishing-integral induction.
quad=s.symbols("quad",real=True)
check("ruling quotient independent of s",
      (2*quad*u*uc)/u**2-2*uc*(quad*u*u)/u**3)
positive_u=s.symbols("positive_u",positive=True)
S1,S2=s.symbols("S1 S2",real=True)
order=s.symbols("order",integer=True,nonnegative=True)
moment=positive_u**(order+4)*(S1+(order+4)*S2*positive_u/2)
next_moment=positive_u**(order+5)*(S1+(order+5)*S2*positive_u/2)
check("general differentiated moment recurrence",
      positive_u**2*s.diff(moment,positive_u)-(order+4)*next_moment)
check("initial zero moment",
      moment.subs(order,0)-positive_u**4*(S1+2*S2*positive_u))
check("weighted normal-displacement cancellation",
      h*sigma**2/W-(pc/(W/sigma)-p*ratio_c/(W/sigma)**2)/2)

# The reciprocal substitution remains only in the later core return-map calculation.
u0,rho0,period=s.symbols("u0 rho0 period",nonzero=True)
return_map=u0/(1-period*u0/rho0)
check("return map reciprocal period",1/return_map-1/u0+period/rho0)
check("return map unit multiplier",s.diff(return_map,u0).subs(u0,0)-1)
check("return map quadratic obstruction",s.diff(return_map,u0,2).subs(u0,0)-2*period/rho0)
# Explicit shell Hessian.
x,y,height,first,second=s.symbols("x y height first second",positive=True)
shell=s.Matrix([[2*first+4*second*x*x,4*second*x*y,0],
                [4*second*x*y,2*first+4*second*y*y,0],[0,0,2/height**2]])
check("convex shell Hessian determinant",
      shell.det()-(8*first**2+16*first*second*(x*x+y*y))/height**2)

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


root=Path(__file__).resolve().parent
source=root/"main.tex"
body=source.read_text(encoding="utf-8")
labels=re.findall(r"\\label\{([^}]+)\}",body)
references=re.findall(r"\\(?:eqref|ref)\{([^}]+)\}",body)
assert len(labels)==len(set(labels)),"Duplicate labels"
assert set(references)<=set(labels),"Missing reference target"
cited={key.strip() for group in re.findall(r"\\cite(?:\[[^\]]*\])?\{([^}]+)\}",body) for key in group.split(",")}
bibliography=set(re.findall(r"\\bibitem\{([^}]+)\}",body))
assert cited==bibliography and len(bibliography)==11
assert not re.search(r"ver61[0-6]|TODO|FIXME|PLACEHOLDER",body,flags=re.I)
assert all(key in labels for key in ("thm:seed","thm:one-curve","prop:pair","thm:band-bending",
    "prop:codazzi-family","eq:ruling-normalization","eq:direct-flux","eq:vanishing-moments","eq:return-map",
    "prop:ruled","prop:insert","lem:globalize"))
assert "eq:pairings" not in body and "Y\\cdot V_s" not in body
assert "Codazzi interpretation of the factor" not in body
assert "sec:independent" not in body and "eq:own-inflection" not in body
assert body.index(r"\label{sec:bending}")<body.index(r"\label{sec:frame}")
band=body[body.index(r"\label{sec:bending}"):body.index(r"\section{The Darboux")]
assert all(token not in band for token in (
    "lem:reciprocal-form","lem:reciprocal-flux","eq:normal-form","eq:H",
    r"\omega",r"\rho",r"\widehat B",r"\mathcal L",r"\kappa",
    "analytic","pole"))
checks["source references and replacement scope"]="PASS"

# Preserve every numbered equation from ver616, allowing only the local
# preparation-arclength rename. This is a source check, not a proof certificate.
expected_equations = {'eq:gauss-curvature': 'f516d8a5aaaa7789e72be0d8ae0ed02a116779b3cec50b8dae90271068105133', 'eq:strain': '2ec79b8ae9e46553942421c8a92e5b60f48fbf9cf2e66bf2a91a8d0ddd0317ae', 'eq:main-pair': '4368f69ffc2cb0df5e1cdec2208f28aa307f1a5ab2831bf29bc55a7d4dafb5f1', 'eq:one-curve-output': '9488baab34d3308457c49975a25a92170a8f8c01b0af11b670da63da92a68420', 'eq:exact-metric': '2df9825b21b6eceee52c90778e53430b7631dcaa74bf073d00b5ab100dca9044', 'eq:tightness': '2b1b16a5f807877cc797dcea88779bb208f0d3017a51374379652e00e74d9e9d', 'eq:volume-variation': '3ad5514c41efccf398b2df05d8ebcb6a44f9176bd39f09295d6b9bcf39a675d9', 'eq:odd-volume': '5461dc83a49ae96d1e8b100d243c4f25c1b7af8b042e41f6a254b7d0d7bc6cb3', 'eq:band-geometry': 'ae3b260cae617c28db576dfd8a0ea4a0d2cfb0d36d163f9bdf54d64bc7173b05', 'eq:linearized-metric': 'b822d927615eb07d09c2274275ab399722790719207e3ec1add768b4b82317c3', 'eq:reduced-strain': '437b8b02b4caf22f3c2ac2da4bff79c532f4e1877e7b79f047b13b7cebcfd9bc', 'eq:geometric-factor': 'b8804a68ee43df5ea7fb672be0865d681140ccf04d0b5e6e1b6de81ee382abc6', 'eq:geometric-field': 'cf97d32cefaf18576b490811cd8012989a77560f05552e9347504ad77d1614c3', 'eq:geometric-flux': 'cc012c6df4396f425504bf82196c431e14b277f96fcfa9fbecf1e0ae47ee2768', 'eq:ruling-normalization': 'd873a83105815b1ee49ddadb7b28bef065700c74c8692af2886fc9ef2689745c', 'eq:direct-flux': '43b6acb102d8926fa0045ee502c7bb4e745f60b35db915a16420f78f93c12941', 'eq:vanishing-moments': '2354bdf46edfdbd729ba29b38b55bdd7ae011f6c8e0fda460bc05897f7ea0622', 'eq:darboux': '3a5fabd6ac9ff1dae651184455aafd4f47647d70df66ec9359985f6a34697657', 'eq:rho': '3fb56ccd30f12072a608facf7f2d953a4c8406b2e6ecefa88a077a2478c95a6d', 'eq:prepared': '9c0be435f5da955b45ff4a493d5998359c380082e2d89a8abe67a72f77b22d9c', 'eq:closure-moment': '39e3c4775979c1f094ef2a0ffeafc6ceabaa6d5c575ad591168c79e818a051b6', 'eq:speed-jets': '7f13ef18f8beafa57ab5565f458704b414cff2540f4fddc92ea419d1fabffbab', 'eq:ruling-constraint': 'c43c2c6f31b4664952bdefefc407c1481d1755ab0fffed16497b249a2547baee', 'eq:delta': 'a8bc70aa3ce15cfe51ed3c748e9eb830f3cba66e9225f2e7fe14e3ba4d85976d', 'eq:ruled-curvature': 'a825f747dab89d943f5e56068cbdb5e2708772285197d7e167c8c512877ec392', 'eq:riccati': '7f6378917bb0a2d636ea44a9a7476c547027e2e2d698ef7b8d2e7356249e737e', 'eq:reciprocal': '7dffbda40fd6cfc4cd5fb96bc0eb7ed5b571e1dacc9d062f7c1797d62f187f54', 'eq:return-map': 'c600f4f7856ed8288b1844375e297d299d4d961d0001decb7fcc71a354212a97', 'eq:leaves': 'deecea6eb8728cc5b4032804499498eb5a926814ee5f3fd15e8edb0c329d1aa5', 'eq:period-identity': '22cdce59e7219bc91f78b3922a82cb3d4f99dec25cc3f7f7580589873e2fbedb', 'eq:linear-periods': 'c31d4b821fb0aa47b9098d5a9d0f5238ee9969848599e745b1819f805f0218e7', 'eq:balance': '5eaf6c734351e2c62b51f194e0cac08f404f7db960d0a384e5427936f7adf809'}
actual_equations = {}
normalized_body = body.replace(r"\widetilde s", r"\sigma")
for match in re.finditer(r"\\begin\{equation\}(.*?)\\end\{equation\}", normalized_body, re.S):
    label = re.search(r"\\label\{([^}]+)\}", match[1])[1]
    content = re.sub(r"\s+", "", match[1])
    actual_equations[label] = hashlib.sha256(content.encode()).hexdigest()
assert actual_equations == expected_equations, "Numbered equation changed"
checks["all numbered equations preserved from ver616"] = "PASS"
intro = body[body.index(r"\section{Introduction}"):body.index(r"\section{Preliminaries}")]
prelim = body[body.index(r"\section{Preliminaries}"):body.index(r"\section{Classical reductions")]
assert len(re.findall(r"\\begin\{theorem\}", intro)) == 7
assert r"\begin{definition}" not in intro
assert r"\subsection*{Proof sketch}" not in body
assert intro.count(r"\emph{Method.}") == 6
assert all(label in intro for label in (
    "thm:main", "thm:seed", "thm:prepared-core", "thm:ruled-interface",
    "prop:insert", "thm:band-bending", "prop:pair"))
checks["seven theorem roadmap with brief methods"] = "PASS"
assert len(prelim.split()) < 300
assert all(token in prelim for token in (r"g_X=\langle dX,dX\rangle",r"\mathrm{II}_{ij}", "Christoffel"))
checks["short separate preliminaries"] = "PASS"
assert r"set $B=X\circ\iota$" in body
assert "converge uniformly" in body
for label in ("prop:prepare", "prop:ruled", "prop:insert"):
    start = body.index(r"\label{" + label + "}")
    stop = re.search(r"\\end\{(?:proposition|theorem)\}", body[start:]).start() + start
    assert r"\ell>0" in body[start:stop]
checks["definition and theorem precision edits"] = "PASS"
assert "actual" not in body.lower()
assert r"\begin{tabular}" not in body
assert "tfrac12 g^{km}" not in body
checks["editorial simplification"] = "PASS"

report={"source":source.name,"sha256":hashlib.sha256(source.read_bytes()).hexdigest(),
    "checks":checks,"scope":"Exact algebra and source consistency only. Differential, geometric, topological and existence arguments are in the manuscript. No formal proof certificate is asserted."}
(root/"verification.json").write_text(json.dumps(report,indent=2)+"\n",encoding="utf-8")
print(f"PASS: {len(checks)} exact algebra and source checks")
