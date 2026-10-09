"""Attach mathematical statements, proof arguments and audited Lean interfaces.

The annotated manuscript is the mathematical blueprint. The overview is a
navigation aid; readiness is tracked at smaller lemma interfaces.
"""
from pathlib import Path
import hashlib
import json
import re

DEFINITIONS = [
    ("D.coordinates", "Actual coordinate calculus", [
        "OAI.SmoothLocal.Geometry.Coord", "OAI.SmoothLocal.Geometry.Ambient",
        "OAI.SmoothLocal.Geometry.MetricField"], [],
        r"The coordinate plane is $\mathbb R^{\{0,1\}}$ and the ambient space is Euclidean three-space. All partial derivatives are evaluations of the actual Frechet derivative; metric matrices act on these coordinate vectors."),
    ("D.sphere", "Actual sphere and its coordinate maps", [
        "TightVer401.RoundSphere", "TightVer401.sphereHemispherePoint",
        "TightVer401.hemisphereDomain"], ["D.coordinates"],
        r"The sphere is the unit sphere in Euclidean three-space. For a unit vector $w$, construct an orthonormal isometry $e_w:\mathbb R^2\to w^\perp$ and let $Q_w(z)=(w+e_wz)/\lVert w+e_wz\rVert$. For an open sphere set $\Omega$, let $V_w=Q_w^{-1}(\Omega)$, using the actual sphere-valued chart map."),
    ("D.support", "Actual spherical support map", [
        "TightVer401.sphereGradient", "TightVer401.sphereSupportTensor",
        "TightVer401.sphereSupportEndomorphism", "TightVer401.globalSphereSupport"],
        ["D.sphere"],
        r"In a regular sphere chart with induced round metric $g$, define $\nabla H=\sum_i(g^{-1}dH)^i\partial_iQ$, $B_{ij}=\nabla_i\nabla_jH+Hg_{ij}$, and the endomorphism $g^{-1}B$. The support map is $\nabla H+HQ$. The global candidate evaluates this expression at zero in the hemisphere chart centered at each sphere point."),
    ("D.gauss-inverse", "Inverse restricted to the actual Gauss image", [
        "TightVer401.gaussImageInverse"], ["D.sphere"],
        r"For $q\in N(U)$ choose a preimage in $U$. Injectivity on $U$ later proves this choice unique. Outside $N(U)$ the inverse has an arbitrary value, used only to represent a partially defined map as a total Lean function. All inverse identities and smoothness statements are restricted to $N(U)$; no property outside this image is assumed."),
    ("D.planar", "Actual planar potential and gnomonic normal", [
        "TightVer401.planarSupportMap", "TightVer401.planarHessian",
        "TightVer401.planarWeight", "TightVer401.planarUnitNormal"], ["D.coordinates"],
        r"Define $X_G=(\partial_0G,\partial_1G,G-z_0\partial_0G-z_1\partial_1G)$ in actual Euclidean three-space using the coordinate-to-Euclidean linear equivalence. Define $A_{ij}=\partial_i\partial_jG$, $w=\sqrt{1+z_0^2+z_1^2}$, and $q=(z_0,z_1,1)/w$. These definitions use actual Frechet coordinate derivatives."),
]

DEFINITIONS += [
    ("D.normal-loop", "Actual normal-loop geometry and integral curve", [
        "TightVer401.normalLoopTangent", "TightVer401.normalLoopCurvature",
        "TightVer401.normalLoopCurve", "TightVer401.normalLoopMoment",
        "TightVer401.normalLoopPhysicalK", "TightVer401.normalLoopPhysicalTau"], ["D.coordinates"],
        r"For an actual smooth spherical curve define $P=-\zeta\times\zeta'$, $\kappa=-\langle\zeta'',P\rangle$, the actual integral curve $c(r)=\int_0^r aP$, and the vector moment $\int_0^L aP$. After the derived inverse arclength map $\psi$, define $k=(\kappa/a)\circ\psi$ and $\tau=-(1/a)\circ\psi$."),
    ("D.moment-path", "Actual finite-control moment correction path", [
        "TightVer401.normalizedMomentControl", "TightVer401.realControlMoment",
        "TightVer401.momentPathCorrection", "TightVer401.momentPath",
        "TightVer401.momentPathMoment", "TightVer401.momentNonlinearPeriod"], [],
        r"Real control bumps are normalized actual smooth bumps of integral one. For $n$ controls set $C(r)=\sum_{j\in\mathrm{Fin}(n)}c_j\psi_j(r)$ and $a_t=b-t\chi b+tC$. The moment is the actual Euclidean vector integral $\int_0^L a_tf$ and the nonlinear period is the actual scalar integral $\int_0^L g/\sqrt{a_t}$. Circle descent and construction of a basis remain separate requirements."),
]


DEFINITIONS += [
    ("D.band-bending", "Actual native band bending and induced form", [
        "TightVer401.IsBandBending", "TightVer401.bandDifferential", "TightVer401.bandInducedForm"], ["D.coordinates"],
        r"On the native circle times open height interval, the differential is the actual manifold derivative. The induced form is its ambient inner product. A bending is an actual smooth vector field whose symmetric mixed derivative pairing with the surface differential vanishes for all tangent vectors."),
]

REFINEMENTS = [
    {
        "id": "BP.support.chart-on", "parent": "prop:support",
        "title": "Support-map agreement on an arbitrary open sphere domain",
        "depends_on": ["D.sphere", "D.support", "L.support.domain-agreement", "L.support.domain-height"],
        "lean_target": "TightVer401.globalSphereSupport_chartOn",
        "lean_file": "TightVer401/SphereSupportOpen.lean",
        "statement_tex": r"Let $\Omega\subset S^2$ be open and let $H:S^2\to\mathbb R$ be smooth on $\Omega$. For every unit $w$ and every $z\in V_w$, the centered global candidate satisfies $a_H(Q_w(z))=\nabla_{g_w}(H\circ Q_w)(z)+H(Q_w(z))Q_w(z)$. No smoothness or extension property of $H$ outside $\Omega$ is required.",
        "proof_sketch_tex": r"Set $q=Q_w(z)$. Its centered chart has $Q_q(0)=q$, and its inverse takes $q$ to zero. The transition from the $w$-chart to the $q$-chart is smooth near $z$. Apply the already proved domain agreement to $V_q$, which is open and contains zero. The height function is smooth on $V_q$ by composition. This proves equality without imposing global smoothness of $H$.",
        "target_signature": "theorem globalSphereSupport_chartOn {H : RoundSphere → ℝ} {Ω : Set RoundSphere}\n  (hH : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H Ω) (hΩ : IsOpen Ω)\n  (w : Ambient) (hw : w ≠ 0) (hu : ‖w‖ = 1) {p : Coord}\n  (hp : p ∈ hemisphereDomain w hw hu Ω) :\n  globalSphereSupport H (sphereHemispherePoint w hw hu p) = hemisphereSupport w hw hu H p",
    },
    {
        "id": "BP.support.smooth-on", "parent": "prop:support",
        "title": "Smoothness of the global support candidate on an open domain",
        "depends_on": ["BP.support.chart-on", "L.support.domain-smooth", "L.sphere.inverse-smooth"],
        "lean_target": "TightVer401.globalSphereSupport_contMDiffOn",
        "lean_file": "TightVer401/SphereSupportOpen.lean",
        "statement_tex": r"For open $\Omega\subset S^2$ and $H$ smooth on $\Omega$, the actual centered support map $a_H$ is smooth on $\Omega$.",
        "proof_sketch_tex": r"At $q\in\Omega$, compose the smooth local support map in the $q$-hemisphere with the smooth hemisphere inverse. The inverse takes $q$ to zero, which is in $V_q$. On the neighborhood $\Omega\cap\{u:\langle q,u\rangle>0\}$ this composition equals $a_H$ by chart agreement. Smoothness is local, so the candidate is smooth at $q$, hence smooth on $\Omega$.",
        "target_signature": "theorem globalSphereSupport_contMDiffOn {H : RoundSphere → ℝ} {Ω : Set RoundSphere}\n  (hH : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H Ω) (hΩ : IsOpen Ω) :\n  ContMDiffOn (𝓡 2) 𝓘(ℝ, Ambient) ∞ (globalSphereSupport H) Ω",
    },
    {
        "id": "BP.support.gauss-image", "parent": "prop:support",
        "title": "Global inverse on the image of an injective regular Gauss map",
        "depends_on": ["L.manifold.gauss-local", "L.manifold.gauss-open", "D.gauss-inverse"],
        "lean_target": "TightVer401.gaussImage_inverse", "lean_file": "TightVer401/GaussImageInverse.lean",
        "statement_tex": r"Let $M$ be a boundaryless smooth surface and $N:M\to S^2$ a smooth map with invertible actual tangent differential at every point. If $N$ is injective, its image $\Omega=N(M)$ is open and $N:M\to\Omega$ is a smooth diffeomorphism.",
        "proof_sketch_tex": r"Apply the existing actual coordinate inverse construction in each source chart. It gives a local smooth inverse and an open image around every image point. Their union proves that $\Omega$ is open. Injectivity makes all local inverses agree pointwise; glue them to the inverse on $\Omega$ and use locality to prove smoothness. The global conclusion is not an extra hypothesis in reconstruction.",
    },
    {
        "id": "BP.support.global-converse", "parent": "prop:support",
        "title": "Support reconstruction of a surface on its Gauss image",
        "depends_on": ["BP.support.smooth-on", "BP.support.gauss-image", "L.support.open-converse"],
        "lean_target": "TightVer401.gaussImage_support_exists", "lean_file": "TightVer401/GaussImageInverse.lean",
        "statement_tex": r"Let $X:M\to\mathbb R^3$ be a smooth immersion with smooth injective regular Gauss map $N$. On $\Omega=N(M)$ define $\widetilde X=X\circ N^{-1}$ and $H(q)=\langle\widetilde X(q),q\rangle$. Then $\widetilde X=a_H$ on $\Omega$.",
        "proof_sketch_tex": r"The derived inverse makes $\widetilde X$ smooth. Its differential remains orthogonal to $q$ by the actual chain rule. Differentiate the height: $dH(v)=\langle\widetilde X,v\rangle$. The tangential component is therefore the round gradient, and the normal component is $Hq$. Use the checked local converse on each sphere chart and glue the pointwise identities.",
    },
    {
        "id": "BP.support.open-geometry", "parent": "prop:support",
        "title": "Actual differential and fundamental forms on every open-domain chart",
        "depends_on": ["BP.support.chart-on", "L.support.local-forms", "L.support.curvature-at"],
        "lean_target": "TightVer401.globalSphereSupport_chart_geometryOn",
        "lean_file": "TightVer401/SphereSupportOpenGeometry.lean",
        "statement_tex": r"Let $A_w=a_H\circ Q_w$ on $V_w$. Its actual differential is the tangent lift of $B$, its normal is $Q_w$, its induced metric is $Bg^{-1}B^T$, and its second form is $-B$. At each point where $\det B\ne0$, its differential is injective and its intrinsic curvature is $1/\det(g^{-1}B)$. These are the chart expressions for $da_H=B_H$, metric $B_H^2$, and $K=R_H^{-1}$.",
        "proof_sketch_tex": r"Chart agreement on the open domain yields equality of the actual Frechet derivatives and all second derivatives, hence of the induced metric and second form. Transfer the checked local formulas. For curvature at one invertible point, shrink to the open neighborhood where the continuous determinant remains nonzero; do not assume invertibility everywhere on the original domain. Use locality of actual intrinsic curvature to transfer the result back to $A_w$.",
    },
    {
        "id": "BP.support.manifold-regularity", "parent": "prop:support",
        "title": "Immersion and normal equation for the actual manifold differential",
        "depends_on": ["BP.support.open-geometry", "BP.support.smooth-on", "L.sphere.chart-differentiable"],
        "lean_target": "TightVer401.globalSphereSupport_manifold_geometryOn",
        "lean_file": "TightVer401/SphereSupportManifoldGeometry.lean",
        "statement_tex": r"At a sphere point with invertible support tensor, the actual manifold tangent differential of $a_H:S^2\to\mathbb R^3$ is injective and every vector in its image is orthogonal to the sphere point.",
        "proof_sketch_tex": r"The hemisphere chart and its explicit inverse are differentiable, so the chart differential is surjective onto the actual sphere tangent space. The actual manifold chain rule identifies the checked coordinate differential with $da_H\circ dQ_w$. Lift arbitrary sphere tangent vectors through $dQ_w$ to transfer injectivity and the normal equation. No identification of a chart derivative with the manifold derivative is assumed.",
    },
    {
        "id": "BP.planar.differential", "parent": "G.planar",
        "title": "Actual differential of the planar potential immersion",
        "depends_on": ["D.coordinates"],
        "lean_target": "TightVer401.planarSupportMap_coordPartial",
        "lean_file": "TightVer401/PlanarSupport.lean",
        "statement_tex": r"For smooth $G:U\subset\mathbb R^2\to\mathbb R$ on open $U$, define $X_G(z)=(\partial_0G,\partial_1G,G-z_0\partial_0G-z_1\partial_1G)$. Then $\partial_iX_G=(\partial_i\partial_0G,\partial_i\partial_1G,-z_0\partial_i\partial_0G-z_1\partial_i\partial_1G)$, and consequently $dX_G(\xi)=(D^2G\xi,-z\cdot D^2G\xi)$ using Hessian symmetry.",
        "proof_sketch_tex": r"Use the actual coordinate projections and the Frechet product rule. The derivative of $G$ cancels the derivatives of the two coordinate factors. The coordinate-to-Euclidean continuous linear equivalence supplies the actual three-space derivative. Expand an arbitrary coordinate vector in the two standard basis vectors; interchange mixed partials using smoothness before identifying the Hessian matrix action.",
        "target_signature": "def planarSupportMap (G : Coord → ℝ) (p : Coord) : Ambient :=\n  WithLp.toLp 2 ![coordPartial 0 G p, coordPartial 1 G p,\n    G p - p 0 * coordPartial 0 G p - p 1 * coordPartial 1 G p]\n\ntheorem planarSupportMap_coordPartial {G : Coord → ℝ} {U : Set Coord}\n  (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U) (i : Fin 2) :\n  coordPartial i (planarSupportMap G) p = WithLp.toLp 2\n    ![coordPartial i (coordPartial 0 G) p, coordPartial i (coordPartial 1 G) p,\n      -p 0 * coordPartial i (coordPartial 0 G) p - p 1 * coordPartial i (coordPartial 1 G) p]",
    },
    {
        "id": "BP.planar.unit-normal", "parent": "G.planar",
        "title": "Actual unit normal of the planar potential immersion",
        "depends_on": ["D.planar", "BP.planar.differential"],
        "lean_target": "TightVer401.planarSupportMap_isUnitNormal",
        "lean_file": "TightVer401/PlanarSupportNormal.lean",
        "statement_tex": r"With $w(z)=\sqrt{1+z_0^2+z_1^2}$, the vector $q(z)=(z_0,z_1,1)/w(z)$ has unit length and is orthogonal to every actual derivative vector of $X_G$. This assertion does not require the Hessian determinant to be nonzero; immersion regularity is a separate lemma.",
        "proof_sketch_tex": r"The weight is strictly positive, so its square is $1+z_0^2+z_1^2$. Compute the actual Euclidean inner product to obtain unit length. Pair each of the two derivative vectors from the preceding lemma with $(z_0,z_1,1)/w(z)$; the third component cancels the first two. Expand every direction in the two coordinate basis vectors to prove the full normal equation.",
        "target_signature": "def planarWeight (p : Coord) : ℝ := Real.sqrt (1 + p 0 ^ 2 + p 1 ^ 2)\n\ndef planarUnitNormal (p : Coord) : Ambient :=\n  WithLp.toLp 2 ![p 0 / planarWeight p, p 1 / planarWeight p, 1 / planarWeight p]\n\ntheorem planarSupportMap_isUnitNormal {G : Coord → ℝ} {U : Set Coord}\n  (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U) :\n  IsUnitNormalAt (planarSupportMap G) (planarUnitNormal p) p",
    },
    {
        "id": "BP.planar.metric", "parent": "G.planar",
        "title": "Induced metric of the planar potential immersion",
        "depends_on": ["D.planar", "BP.planar.differential"],
        "lean_target": "TightVer401.planarSupportMap_inducedMetric",
        "lean_file": "TightVer401/PlanarSupportForms.lean",
        "statement_tex": r"Let $A_{ij}=\partial_i\partial_jG$. In the coordinate basis the actual induced metric of $X_G$ is $A(I+zz^T)A^T$, which equals $A^T(I+zz^T)A$ by Hessian symmetry.",
        "proof_sketch_tex": r"Take the actual Euclidean inner products of the two derivative vectors. Their first two entries contribute the row dot product; the third entries contribute $(z\cdot A_i)(z\cdot A_j)$. Expand matrix multiplication to identify this with $A(I+zz^T)A^T$. Prove mixed-partial symmetry when translating to the manuscript's Hessian convention.",
        "target_signature": "def planarHessian (G : Coord → ℝ) (p : Coord) : Matrix (Fin 2) (Fin 2) ℝ :=\n  fun i j => coordPartial i (coordPartial j G) p\n\ntheorem planarSupportMap_inducedMetric {G : Coord → ℝ} {U : Set Coord}\n  (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U) :\n  inducedMetric (planarSupportMap G) p = planarHessian G p *\n    (1 + Matrix.of (fun i j => p i * p j)) * (planarHessian G p).transpose",
    },
    {
        "id": "BP.planar.second-form", "parent": "G.planar",
        "title": "Second fundamental form of the planar potential immersion",
        "depends_on": ["D.planar", "BP.planar.differential", "BP.planar.unit-normal"],
        "lean_target": "TightVer401.planarSupportMap_secondFundamental",
        "lean_file": "TightVer401/PlanarSupportSecondForm.lean",
        "statement_tex": r"The actual second fundamental form of $X_G$ with normal $(z,1)/w(z)$ is $-D^2G/w(z)$.",
        "proof_sketch_tex": r"Differentiate the identically zero pairing of $\partial_jX_G$ with the unnormalized normal $(z,1)$ on the open domain. Its actual derivative contributes the Hessian entry. Scale the resulting second-derivative pairing by $w^{-1}$ and use smooth mixed-partial symmetry. The computation uses the defined second Frechet derivative, rather than an assumed shape operator.",
        "target_signature": "theorem planarSupportMap_secondFundamental {G : Coord → ℝ} {U : Set Coord}\n  (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U) :\n  secondFundamental (planarSupportMap G) (planarUnitNormal p) p =\n    -(planarWeight p)⁻¹ • planarHessian G p",
    },
    {
        "id": "BP.balance.bump-basis", "parent": "lem:finite-moment-balance",
        "title": "Independent localized moment controls",
        "depends_on": ["BP.balance.normalized-control"],
        "lean_target": "TightVer401.exists_short_circle_moment_controls",
        "lean_file": "TightVer401/MomentControlCircle.lean",
        "statement_tex": r"For smooth $f:S^1\to\mathbb R^m$, put $V=\operatorname{span}f(S^1)$ and $d=\dim V$. There exist $d$ disjoint arbitrarily short control arcs and smooth bumps $\psi_j$ supported there whose moment vectors $v_j=\oint\psi_j f$ form a basis of $V$. The arcs can be disjoint from a chosen sufficiently small slowdown arc. For $d=0$, the control family is empty.",
        "proof_sketch_tex": r"Choose independent sample values of $f$. Normalize nonnegative bumps to mass one and shrink their supports; their moment vectors approach those samples. Nonzero determinant is an open condition in the finite-dimensional span, so sufficiently short bumps retain independence. Fix these controls before shrinking the slowdown support. Prove continuity of the vector integrals and include the zero-dimensional case.",
    },
    {
        "id": "BP.balance.positive-path", "parent": "lem:finite-moment-balance",
        "title": "Exact moments along a small positive slowdown path",
        "depends_on": ["BP.balance.bump-basis", "BP.balance.coordinates-small", "BP.balance.path-basic"],
        "lean_target": "TightVer401.exists_momentSlowdown_data",
        "lean_file": "TightVer401/MomentSlowdownConstruction.lean",
        "statement_tex": r"For positive smooth $b$, a slowdown bump $0\le\chi\le1$ with a nonempty plateau, and fixed control bumps, solve $\sum_jc_jv_j=\oint\chi bf$ and define $a_t=b-t\chi b+t\sum_jc_j\psi_j$, $0\le t<1$. By shrinking the slowdown arc, all $a_t$ are positive, $\oint a_tf=\oint bf$, and $\lVert a_t-b\rVert_{L^1}<\eta$ uniformly in $t$.",
        "proof_sketch_tex": r"The inverse of the fixed moment-coordinate map bounds $\lVert c\rVert$ by a constant times $\lVert\oint\chi bf\rVert$, which tends to zero with the slowdown arc length. On the slowdown support, positivity follows from $(1-t)b>0$; on the disjoint control supports, use a positive lower bound for $b$ and the coefficient bound. Integral linearity gives exact moments. The triangle inequality gives the uniform $L^1$ estimate.",
        "interface_gap": "The target constructs quantitative slowdown data from raw normalized independent controls and their actual coordinate inverse. The final circle theorem must instantiate these inputs from the checked localized basis construction.",
    },
    {
        "id": "BP.balance.period-attainment", "parent": "lem:finite-moment-balance",
        "title": "Nonlinear period divergence and target attainment",
        "depends_on": ["BP.balance.path-basic", "BP.balance.period-continuity"],
        "lean_target": "TightVer401.momentPrescription_from_controls",
        "lean_file": "TightVer401/MomentPrescriptionPath.lean",
        "statement_tex": r"Choose the slowdown support where $g$ has the sign of $B_*-\oint g/\sqrt b$. Then $t\mapsto\oint g/\sqrt{a_t}$ is continuous for $t<1$ and tends to the corresponding signed infinity as $t\uparrow1$. Consequently some $t_*<1$ attains $B_*$ while retaining the exact moments, positivity, smallness and support bounds.",
        "proof_sketch_tex": r"On the plateau, $a_t=(1-t)b$, so its integral contribution is a nonzero constant times $(1-t)^{-1/2}$. All remaining terms on the slowdown support have the same sign. On the complementary control supports the denominator is uniformly bounded away from zero, so their contributions remain bounded. Prove continuity locally in t by a positive denominator bound and use the intermediate-value theorem. If the initial period already equals the target, take $a=b$.",
        "interface_gap": "This target proves signed divergence and attainment for supplied controls with quantitative bounds. Construction of those bounds and the complete arbitrary-short-arc support/count conclusion are separate positive-path and final circle assembly obligations.",
    },
]

REFINEMENTS += [
    {
        "id": "BP.criterion.balance-closing-speed", "parent": "thm:normal-loop-criterion",
        "title": "Arbitrarily close actual balanced closing speeds",
        "depends_on": ["BP.criterion.derivative-signs", "BP.balance.final-circle"],
        "lean_target": "TightVer401.normalLoop_balance_closing_speed",
        "lean_file": "TightVer401/NormalLoopPrescription.lean",
        "statement_tex": r"For every actual positive smooth closing speed $b$ and every $\eta>0$, there is an actual positive smooth periodic speed $a$ with $\int aP=0$, $\int\kappa_r/\sqrt a=0$ and $\int|a-b|<\eta$.",
        "proof_sketch_tex": r"Positive closure gives actual nonconstant periodic curvature and hence both signs of its derivative. Apply the full actual finite-moment theorem with $f=P$, $g=\kappa_r$, and target zero. This derives exact closure, balance and arbitrary L1 closeness simultaneously.",
    },
    {
        "id": "BP.criterion.full-band", "parent": "thm:normal-loop-criterion",
        "title": "Three speed conditions and actual immersed-band existence",
        "depends_on": ["BP.criterion.interior", "BP.criterion.positive-speed", "BP.criterion.balance-closing-speed", "BP.structural.assembly"],
        "lean_target": "TightVer401.normalLoop_prescribed_identity_band_criterion",
        "lean_file": "TightVer401/NormalLoopCriterionBand.lean",
        "statement_tex": r"Ordinary ambient convex interior, existence of a smooth positive closing speed, existence of a smooth positive closed balanced speed, and existence of the actual prescribed immersed principal-normal circle-band with negative curvature and identity return are equivalent.",
        "proof_sketch_tex": r"Combine the two convex directions and exact balance construction. The actual global arclength inverse builds the prescribed frame and ruled map. Actual coordinate derivatives give injectivity and negative intrinsic curvature; the manifold chain rule transfers injectivity to the native circle-band differential. The actual Riccati trajectory supplies the asymptotic and identity-return equations. In the converse, actual curve periodicity and the arclength shift derive vector moment closure; closure and period cancellation are not fields of the band descriptor.",
    },
    {
        "id": "BP.criterion.flow-inside-band", "parent": "thm:normal-loop-criterion",
        "title": "Actual positive identity-return trajectories remain in each band",
        "depends_on": ["BP.criterion.full-band"],
        "lean_target": "TightVer401.periodicRuledFrame_identity_flow_inside_band",
        "lean_file": "TightVer401/NormalLoopCriterionBandFlow.lean",
        "statement_tex": r"For every base point and every width $w>0$, there exists $0<\delta<w$ such that all actual trajectories beginning at $0<v<\delta$ stay in $(0,w)$ for the full period, satisfy the actual asymptotic equation, and return exactly to $v$.",
        "proof_sketch_tex": r"Derive a global positive minimum of the actual periodic $\rho$ and a compact-interval lower bound $1/2$ for the projective denominator. Shrink the initial value using these bounds and the requested width. Intersect this tolerance with the checked identity-return tolerance. Positivity, upper containment, actual ODE and endpoint then follow for every such trajectory.",
    },
    {
        "id": "BP.cap.relative-join", "parent": "lem:cap",
        "title": "Relative smoothing of concave matching first jets",
        "depends_on": ["BP.cap.actual-derivatives", "BP.cap.double-primitive", "BP.cap.local-acceleration", "BP.cap.small-moment-error", "BP.cap.positive-correction"],
        "lean_target": "TightVer401.exists_concave_first_jet_join",
        "lean_file": "TightVer401/ConcaveJetJoinRelative.lean",
        "statement_tex": r"Let $u<c<v$, with $q_L,q_R$ smooth on $(u,v)$, equal in value and first derivative at $c$, and with actual second derivatives strictly negative. Inside any prescribed open neighborhood $V$ of $c$, construct a smooth strictly concave join $q$ equal to the original left branch on $((u,v)\cap(-\infty,c])\setminus V$ and right branch on $((u,v)\cap[c,\infty))\setminus V$, retaining their full outer germs.",
        "proof_sketch_tex": r"Extend only the local positive accelerations $-q_L''$ and $-q_R''$ by actual compact cutoffs. Blend in a shrinking central interval and correct the actual total mass and first moment with fixed normalized controls away from that interval. Moment errors tend to zero with its width, so derived coordinate bounds preserve acceleration positivity. Integrate twice with the incoming first jet. The two exact moment equalities reconstruct both outer value and slope germs; paste back to the original local representatives. No global smoothness of either original representative is assumed.",
        "interface_gap": "Construct the actual positive acceleration correction and both full outer-germ identities. This is a proposed target, not an assumed smoothing package.",
    },
    {
        "id": "BP.complete.profile", "parent": "lem:complete-profile",
        "title": "Full-germ positive radial profile continuation",
        "depends_on": [],
        "lean_target": "TightVer401.exists_completeProfile",
        "lean_file": "TightVer401/CompleteProfile.lean",
        "statement_tex": r"If $q_0$ is smooth near $H$, with $q_0(H)>0$, $q_0'(H)>0$ and $q_0''>0$ nearby, then every $\beta>0$ admits an actual smooth $q$ agreeing with $q_0$ on a whole neighborhood of $H$, satisfying $q,q',q''>0$ for $z\ge H$, $q''=\beta$ eventually and $q'\to\infty$.",
        "proof_sketch_tex": r"An actual smooth cutoff with support inside the original smooth domain blends $q_0''$ with $\beta$ into a globally smooth positive acceleration. Integrate twice using the pinned OpenAI actual primitive and the incoming value and first derivative. Actual FTC on all sufficiently short intervals proves full-germ agreement. Positive integrals give half-line positivity; the constant acceleration tail gives an affine positive-slope derivative tending to infinity.",
    },
    {
        "id": "BP.cap.actual-derivatives", "parent": "lem:cap",
        "title": "Actual derivatives and first-jet matching of the finite radial cap",
        "depends_on": [],
        "lean_target": "TightVer401.radialCap_matches_first_jet",
        "lean_file": "TightVer401/RadialCapConstants.lean",
        "statement_tex": r"For $d,s>0$, $R=j+d$, $a=d\sqrt{1+s^{-2}}$ and $C=v-d/s$, the actual smooth square-root cap $k(r)=C+\sqrt{a^2-(R-r)^2}$ satisfies $k(j)=v$, $k'(j)=s$, $k'>0$ before $R$, $k''<0$, $k'(R)=0$ and $k''(R)=-1/a$. For fixed $j,s>0$, all sufficiently small $d$ satisfy $R>a$.",
        "proof_sketch_tex": r"Differentiate the actual square-root function on its positive-radicand open domain. Differentiate the resulting first derivative using germ equality on this domain. The cap constants make the incoming radicand $(d/s)^2$; strict positivity, endpoint derivatives and the width bound follow by exact real algebra. Relative smoothing at the incoming seam remains a separate obligation.",
    },
    {
        "id": "BP.cap.inverse-germ", "parent": "prop:dual-inversion",
        "title": "Actual radial inverse and polar Legendre germ",
        "depends_on": ["BP.cap.actual-derivatives"],
        "lean_target": "TightVer401.radialCap_inverse_legendre",
        "lean_file": "TightVer401/RadialCapInverse.lean",
        "statement_tex": r"For $a>0$ and $\rho>0$, set $r=R-a\rho/\sqrt{1+\rho^2}$. Then $R-a<r<R$, the actual cap derivative is $k'(r)=\rho$, and its actual radial Legendre expression is $\rho r-k(r)=R\rho-a\sqrt{1+\rho^2}-C$.",
        "proof_sketch_tex": r"The actual cap radicand at the displayed radius equals $(a/\sqrt{1+\rho^2})^2$. Substitute into the checked actual derivative and the Legendre expression, then use the exact square-root identity. The global capped gradient bijection and the puncture compactification remain separate degree and geometric obligations.",
    },
    {
        "id": "BP.balance.final-circle", "parent": "lem:finite-moment-balance",
        "title": "Full finite-moment prescription on the actual smooth circle",
        "depends_on": ["BP.balance.positive-path", "BP.balance.period-attainment"],
        "lean_target": "TightVer401.finite_moment_period_prescription_smooth_circle",
        "lean_file": "TightVer401/MomentPrescriptionSmoothCircle.lean",
        "statement_tex": r"For actual smooth circle maps $f:S_L^1\to\mathbb R^m$, $g:S_L^1\to\mathbb R$ taking both signs, and $b>0$, every $B\in\mathbb R$ and $\eta,\varepsilon>0$ admit a smooth positive $a$ with exact original vector moments, $\int|a-b|<\eta$ and $\int g/\sqrt a=B$. Its correction support lies in at most $d+1$ projected intervals whose summed lengths are below $\varepsilon$, where $d=\dim\operatorname{span}f(S_L^1)$.",
        "proof_sketch_tex": r"Choose the required sign center in an interior representative of the actual circle. Fix independent normalized disjoint controls away from that center. Their actual coordinate inverse constructs the small compensating coefficients after shrinking the slowdown bump. Apply signed period divergence and continuity to attain the target, descend the actual periodic speed to the smooth circle, and retain all integral identities and the finite short-arc cover. The native wrapper derives smooth pullbacks from the actual smooth period projection.",
    },
    {
        "id": "BP.criterion.positive-speed", "parent": "thm:normal-loop-criterion",
        "title": "Convex interior constructs an actual smooth positive closing speed",
        "depends_on": ["BP.balance.bump-basis", "BP.structural.frame"],
        "lean_target": "TightVer401.normalLoop_origin_interior_positive_closing_speed",
        "lean_file": "TightVer401/NormalLoopPositiveClosure.lean",
        "statement_tex": r"For a smooth periodic loop, ordinary ambient convex interior $0\in\operatorname{int}\operatorname{conv}P(S^1)$ yields an actual smooth positive periodic $b$ with $\int bP=0$.",
        "proof_sketch_tex": r"Form the actual convex cone of vector moments of nonnegative smooth periodic speeds. Normalized localized bumps put each $P$ sample in its closure. Independent actual control moments give the cone nonempty ordinary interior, while the input convex interior makes the actual moment span all of Euclidean three-space. The convex interior--closure identity puts zero in the cone interior. Realize a sufficiently small negative multiple of the constant-speed moment inside that cone and add a strictly positive constant speed. This yields exact zero moment and actual strict positivity without assuming a minimizer or speed.",
        "target_signature": "theorem normalLoop_origin_interior_positive_closing_speed {ζ : ℝ → Ambient} {L : ℝ}\n  (hζ : ContDiff ℝ ∞ ζ) (hζL : Function.Periodic ζ L) (hL : 0 < L)\n  (h0 : (0 : Ambient) ∈ interior (convexHull ℝ (range (normalLoopTangent ζ)))) :\n  ∃ b : ℝ → ℝ, ContDiff ℝ ∞ b ∧ Function.Periodic b L ∧\n    (∀ r, 0 < b r) ∧ normalLoopMoment b ζ (deriv ζ) L = 0",
    },
    {
        "id": "BP.balance.coordinates-small", "parent": "lem:finite-moment-balance",
        "title": "Actual slowdown moments and coordinate smallness",
        "depends_on": ["BP.balance.bump-basis"],
        "lean_target": "TightVer401.slowdown_coefficients_l1_le",
        "lean_file": "TightVer401/MomentControlSmallness.lean",
        "statement_tex": r"For a fixed actual moment-coordinate inverse $T$ with $\sum_j|(Tu)_j|\le C\|u\|$, the slowdown vector $u=\int\chi_\rho bf$ satisfies $\|u\|\le2M\rho$ and hence $\sum_j|(Tu)_j|\le2CM\rho$. The controls and inverse are fixed before $\rho$ shrinks.",
        "proof_sketch_tex": r"The actual integrand vanishes off the radius-$\rho$ interval and has norm bounded by $M$. Bound its Bochner integral by interval length times $M$, prove membership in the actual sample span, and apply the derived continuous linear coordinate inverse bound.",
    },
    {
        "id": "BP.criterion.nonconstant", "parent": "thm:normal-loop-criterion",
        "title": "Positive vector closure forces curvature nonconstancy",
        "depends_on": ["BP.structural.frame", "BP.structural.closure"],
        "lean_target": "TightVer401.normalLoop_closure_forces_nonconstant_curvature",
        "lean_file": "TightVer401/NormalLoopNonconstant.lean",
        "statement_tex": r"For a smooth unit-speed spherical loop and continuous positive closing speed $a$, the actual geodesic curvature $\kappa$ is nonconstant.",
        "proof_sketch_tex": r"If $\kappa=c$, actual differentiation gives $(P-c\zeta)'=0$. The constant axis $C=P-c\zeta$ satisfies $C\cdot P=1$. Pair the actual closing moment with $C$ to obtain $\int a=0$, contradicting positivity on a positive-length period.",
    },
    {
        "id": "BP.criterion.derivative-signs", "parent": "thm:normal-loop-criterion",
        "title": "Actual curvature derivative takes both signs",
        "depends_on": ["BP.criterion.nonconstant"],
        "lean_target": "TightVer401.normalLoop_closed_curvature_derivative_signs",
        "lean_file": "TightVer401/PeriodicDerivativeSigns.lean",
        "statement_tex": r"For every such positive closing speed, the actual derivative $\kappa_r$ has a strictly positive value and a strictly negative value.",
        "proof_sketch_tex": r"A periodic monotone real function is constant: integer period shifts compare arbitrary arguments. If its derivative had only one sign, the actual mean-value monotonicity theorem would contradict the already derived nonconstancy. Smoothness and periodicity of $\kappa$ come from the actual loop derivatives.",
    },
    {
        "id": "BP.criterion.affine-span", "parent": "thm:normal-loop-criterion",
        "title": "Positive closure forces full affine span",
        "depends_on": ["BP.criterion.nonconstant", "BP.structural.frame"],
        "lean_target": "TightVer401.normalLoop_closure_affineSpan_eq_top",
        "lean_file": "TightVer401/NormalLoopAffineSpan.lean",
        "statement_tex": r"The actual family $P(r)$ of a positively closing unit-speed spherical loop has affine span equal to Euclidean three-space.",
        "proof_sketch_tex": r"A vector annihilating all $P(r)-P(0)$ has constant pairing with $P$. Closure and $\int a>0$ force that constant to vanish. On a neighborhood with $\kappa\ne0$, differentiate the zero pairings with $P$ and $\zeta_r$; the actual frame equations then annihilate all three orthonormal frame vectors, forcing the vector to be zero. Finite-dimensional orthogonal-complement duality gives full affine span.",
    },
    {
        "id": "BP.criterion.interior", "parent": "thm:normal-loop-criterion",
        "title": "Positive closure implies ordinary convex interior",
        "depends_on": ["BP.criterion.affine-span"],
        "lean_target": "TightVer401.normalLoop_closure_convex_interior",
        "lean_file": "TightVer401/NormalLoopInterior.lean",
        "statement_tex": r"A positive closing speed implies $0\in\operatorname{int}_{\mathbb R^3}\operatorname{conv}P(S^1)$, with the ordinary ambient interior.",
        "proof_sketch_tex": r"Full affine span makes the convex hull's ordinary interior nonempty. If zero were outside it, actual Hahn--Banach separation gives a nonzero linear functional with one-signed pairing on $P$. Positive weighted closure and continuity make that pairing identically zero. The checked annihilator theorem contradicts the functional being nonzero.",
        "target_signature": "theorem normalLoop_closure_convex_interior {ζ : ℝ → Ambient} {a : ℝ → ℝ}\n  (hζ : ContDiff ℝ ∞ ζ) (ha : Continuous a)\n  (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)\n  (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1)\n  (hpos : ∀ r, 0 < a r) {L : ℝ} (hL : 0 < L)\n  (hζL : Function.Periodic ζ L)\n  (hmoment : normalLoopMoment a ζ (deriv ζ) L = 0) :\n  (0 : Ambient) ∈ interior (convexHull ℝ (range (normalLoopTangent ζ)))",
    },
]


REFINEMENTS += [
    {
        "id": "BP.planar.regularity", "parent": "G.planar",
        "title": "Actual planar immersion regularity and metric determinant",
        "depends_on": ["BP.planar.metric"],
        "lean_target": "TightVer401.planarSupportMap_differential_injective",
        "lean_file": "TightVer401/PlanarSupportRegularity.lean",
        "statement_tex": r"On an open smooth domain, $\det D^2G(z)\ne0$ implies that the actual derivative of $X_G$ is injective. Its induced metric has determinant $w(z)^2(\det D^2G(z))^2$.",
        "proof_sketch_tex": r"The first two components of $dX_G(v)$ equal the transposed Hessian applied to $v$. Invert the Hessian to prove injectivity. Take determinants in the proved metric formula and compute $\det(I+zz^T)=1+|z|^2=w^2$.",
    },
    {
        "id": "BP.planar.curvature", "parent": "G.planar",
        "title": "Actual planar Gaussian curvature and saddle sign",
        "depends_on": ["BP.planar.regularity", "BP.planar.second-form"],
        "lean_target": "TightVer401.planarSupportMap_gaussianCurvature_at",
        "lean_file": "TightVer401/PlanarSupportCurvature.lean",
        "statement_tex": r"For smooth $G$ on open $U$ and $z\in U$ with nonzero Hessian determinant, $K_{X_G}(z)=1/(w(z)^4\det D^2G(z))$. Thus $K_{X_G}(z)<0$ if and only if $\det D^2G(z)<0$.",
        "proof_sketch_tex": r"Shrink to the open nonzero-Hessian set around $z$. The induced metric is smooth positive there. Apply the audited OpenAI Gauss equation to the actual normal and second form; divide its determinant by the actual metric determinant and cancel nonzero factors. Positivity of $w$ proves the sign equivalence.",
    },
    {
        "id": "BP.planar.chart", "parent": "G.planar",
        "title": "Actual smooth gnomonic chart and inverse",
        "depends_on": ["D.planar", "D.sphere"],
        "lean_target": "TightVer401.gnomonicChart",
        "lean_file": "TightVer401/GnomonicCoordinates.lean",
        "statement_tex": r"The map $q(z)=(z,1)/w(z)$ is a smooth open partial homeomorphism from the whole plane onto the northern hemisphere. Its inverse is $q\mapsto(q_0/q_2,q_1/q_2)$; both maps are smooth on their stated domains and the actual derivative of $q$ is injective.",
        "proof_sketch_tex": r"Prove the weight positive and smooth. Compute both inverse identities using the actual unit-sphere equation and $q_2>0$. Quotient smoothness gives the inverse; differentiate the exact left-inverse identity to obtain derivative injectivity.",
    },
    {
        "id": "BP.planar.reconstruction", "parent": "G.planar",
        "title": "Gnomonic potential equals the spherical support reconstruction",
        "depends_on": ["BP.planar.chart", "BP.planar.unit-normal", "BP.support.global-converse"],
        "lean_target": "TightVer401.gnomonicSupport_reconstruction",
        "lean_file": "TightVer401/GnomonicSupport.lean",
        "statement_tex": r"Let $\Omega$ be an open subset of the northern hemisphere and $H$ smooth on $\Omega$. Set $G(z)=w(z)H(q(z))$. Then $X_G(z)=a_H(q(z))$ for every $q(z)\in\Omega$, without assuming a global extension of $H$ is smooth.",
        "proof_sketch_tex": r"Transport $X_G$ to $\Omega$ by the proved gnomonic inverse. The actual chain rule and the proved normal equation make its differential orthogonal to $q$. Its height is $G/w=H$ on $\Omega$. Apply the audited open-sphere converse and support-map locality to identify it with $a_H$.",
    },
    {
        "id": "BP.planar.converse", "parent": "G.planar",
        "title": "Planar potential reconstructed from an actual normal-parametrized surface",
        "depends_on": ["BP.planar.unit-normal"],
        "lean_target": "TightVer401.planarSupportMap_converse_local",
        "lean_file": "TightVer401/PlanarSupportConverse.lean",
        "statement_tex": r"For a smooth $X$ on open $U$ with actual tangent vectors orthogonal to $(z,1)/w(z)$, define $G=X_0z_0+X_1z_1+X_2$. Then $\partial_iG=X_i$, $X=X_G$ on $U$, and $G=w\langle X,q\rangle$.",
        "proof_sketch_tex": r"Differentiate $\langle X,(z,1)\rangle$. The term containing $dX$ vanishes by the actual normal equation; the other term is the corresponding component of $X$. Substitute both derivatives into the definition of $X_G$ and use the height identity for its third component.",
    },
    {
        "id": "BP.planar.gradient-inverse", "parent": "G.planar",
        "title": "Actual gradient local inverse from Hessian nonsingularity",
        "depends_on": ["D.planar", "BP.planar.second-form"],
        "lean_target": "TightVer401.planarGradient_exists_smooth_local_inverse_at",
        "lean_file": "TightVer401/PlanarGradientInverse.lean",
        "statement_tex": r"At any point of an open smooth domain with $\det D^2G\ne0$, the actual planar gradient has a smooth local inverse on an open target neighborhood, with its source retained in the original domain.",
        "proof_sketch_tex": r"Differentiate the actual coordinate partials and use Hessian symmetry to identify $d(\nabla G)v=D^2Gv$. Matrix nonsingularity gives derivative injectivity, and the checked finite-dimensional smooth inverse theorem produces the actual local homeomorphism and smooth inverse. Shrink first to the nonzero-determinant set if only pointwise regularity is supplied.",
    },
    {
        "id": "BP.planar.duality", "parent": "G.planar",
        "title": "Differential Legendre duality on an actual gradient diffeomorphism",
        "depends_on": ["BP.planar.gradient-inverse"],
        "lean_target": "TightVer401.planarLegendre_hessian", "lean_file": "TightVer401/PlanarLegendre.lean",
        "statement_tex": r"If $\nabla G$ is an actual smooth diffeomorphism with smooth inverse $z(y)$, define $G^*(y)=z(y)\cdot y-G(z(y))$. Then $\nabla G^*=z$, $D^2G^*=(D^2G)^{-1}$, and negative determinant is preserved.",
        "proof_sketch_tex": r"Differentiate the defining expression. The terms containing $dz$ cancel because $y=\nabla G(z)$. Differentiate the exact inverse identity to obtain the inverse Hessian and take determinants. This conditional duality does not prove the global annular gradient diffeomorphism.",
        "interface_gap": "Bind the checked declarations after the actual inverse-identity derivative proof compiles; do not assume Hessian inversion as an input.",
    },
    {
        "id": "BP.planar.trace", "parent": "G.planar",
        "title": "Actual value and gradient traces and the zero action identity",
        "depends_on": ["D.planar", "BP.planar.gradient-inverse"],
        "lean_target": "TightVer401.planarTrace_periodic_action_zero", "lean_file": "TightVer401/PlanarTrace.lean",
        "statement_tex": r"For smooth $G$ and a smooth source curve $p$, let $g=G\circ p$ and $\gamma=\nabla G\circ p$. Then $g'=\gamma\cdot p'$ and $\gamma'=D^2G(p)p'$. If $p$ closes after period $L$, the actual integral $\int_0^L\gamma\cdot p'$ is zero.",
        "proof_sketch_tex": r"Apply the actual chain rule to $G$ and its gradient. Expand directions in the coordinate basis. The fundamental theorem of calculus identifies the action integral with the endpoint value difference, which vanishes for a closed curve.",
        "interface_gap": "Bind actual derivative and interval-integral declarations after compilation.",
    },
    {
        "id": "BP.structural.frame", "parent": "G.structural",
        "title": "Cross-product frame from actual spherical curve derivatives",
        "depends_on": ["D.coordinates"],
        "lean_target": "TightVer401.normalLoop_derivative_P",
        "lean_file": "TightVer401/NormalLoopFrame.lean",
        "statement_tex": r"Let $\zeta$ be an actual unit-speed spherical curve, $E=\zeta'$ and $P=-\zeta\times E$. Define $\kappa=-\langle\zeta'',P\rangle$. Then $(P,E,\zeta)$ is an orthonormal frame, $\zeta''=-\zeta-\kappa P$ and $P'=\kappa E$.",
        "proof_sketch_tex": r"Differentiate the unit-length and unit-speed equations to obtain orthogonality. Decompose the actual second derivative in the orthonormal frame. Differentiate the actual cross product and use the vector triple-product identity to obtain $P'=\kappa E$.",
    },
    {
        "id": "BP.structural.closure", "parent": "G.structural",
        "title": "Closure of the actual OpenAI integral primitive",
        "depends_on": ["BP.structural.frame"],
        "lean_target": "TightVer401.normalLoopCurve_periodic_iff",
        "lean_file": "TightVer401/NormalLoopSpeed.lean",
        "statement_tex": r"For periodic smooth $a,\zeta,E$ of any period $L$, set $c(r)=\int_0^r a(t)P(t)\,dt$. The actual curve $c$ is periodic if and only if the full vector moment $\int_0^L aP$ vanishes.",
        "proof_sketch_tex": r"Use the pinned OpenAI actual integral primitive and its fundamental theorem. A periodic integrand changes the primitive by the integral over one period. Evaluate periodicity at zero for necessity and use the interval-integral addition identity for sufficiency.",
    },
    {
        "id": "BP.structural.physical-frame", "parent": "G.structural",
        "title": "Frame derivatives after an actual inverse arclength map",
        "depends_on": ["BP.structural.frame", "BP.structural.closure"],
        "lean_target": "TightVer401.normalLoop_physical_frame",
        "lean_file": "TightVer401/NormalLoopSpeed.lean",
        "statement_tex": r"Under an actual scalar parameter change $\psi'(s)=1/a(\psi(s))$, the frame satisfies $P_s=(\kappa/a)E$, $E_s=-(\kappa/a)P-(1/a)\zeta$ and $\zeta_s=(1/a)E$.",
        "proof_sketch_tex": r"Apply the ordinary actual derivative chain rule to the already derived frame equations and collect scalar factors. Existence of the inverse arclength map and the nonlinear period integral are distinct obligations.",
    },
]

REFINEMENTS += [
    {
        "id": "BP.planar.round-metric", "parent": "G.planar",
        "title": "Actual gnomonic round metric determinant",
        "depends_on": ["BP.planar.chart"],
        "lean_target": "TightVer401.gnomonic_inducedMetric_det",
        "lean_file": "TightVer401/GnomonicMetric.lean",
        "statement_tex": r"The actual gnomonic round metric is $g_{ij}=\delta_{ij}/w^2-z_iz_j/w^4$ and $\det g=w^{-6}$.",
        "proof_sketch_tex": r"Differentiate the actual square root weight to obtain $\partial_iw=z_i/w$. Differentiate the actual normalized numerator, take Euclidean inner products, and compute the two-by-two determinant using $w^2=1+|z|^2$.",
    },
    {
        "id": "BP.planar.tensor", "parent": "G.planar",
        "title": "Actual spherical support tensor in gnomonic coordinates",
        "depends_on": ["BP.planar.reconstruction", "BP.planar.second-form"],
        "lean_target": "TightVer401.gnomonicSupport_tensor",
        "lean_file": "TightVer401/GnomonicTensor.lean",
        "statement_tex": r"For $G=wH(q)$ on an open Gauss domain, the actual covariant spherical support tensor pulled back to gnomonic coordinates is $B=D^2G/w$.",
        "proof_sketch_tex": r"Use the actual local support converse to identify $X_G$ with the chart support map. Equality on an open domain identifies their actual second derivative germs. Equate the two checked second fundamental forms, $-D^2G/w$ and $-B$, and cancel the sign.",
    },
    {
        "id": "BP.planar.support-determinant", "parent": "G.planar",
        "title": "Support endomorphism determinant and saddle equivalence",
        "depends_on": ["BP.planar.round-metric", "BP.planar.tensor"],
        "lean_target": "TightVer401.gnomonicSupport_endomorphism_det",
        "lean_file": "TightVer401/GnomonicDeterminant.lean",
        "statement_tex": r"The determinant of the actual raised support tensor satisfies $\det(g^{-1}B)=w^4\det D^2G$. Its negativity is equivalent to the planar saddle condition.",
        "proof_sketch_tex": r"Take determinants of $B=D^2G/w$ and use $\det g=w^{-6}$. The weight is positive, so cancel the nonzero powers and preserve the determinant sign.",
    },
    {
        "id": "BP.planar.tangent-sign", "parent": "G.planar",
        "title": "Actual support tangent pairing along a source curve",
        "depends_on": ["BP.planar.tensor", "BP.planar.trace"],
        "lean_target": "TightVer401.gnomonicSupport_trace_tangent",
        "lean_file": "TightVer401/GnomonicDeterminant.lean",
        "statement_tex": r"For a differentiable planar source curve $p$ and $\gamma=\nabla G\circ p$, the actual pulled-back support tensor satisfies $B(p',p')=p'\cdot\gamma'/w(p)$.",
        "proof_sketch_tex": r"Apply the actual gradient-trace chain rule and substitute $B=D^2G/w$. Expand the matrix quadratic pairing and collect the scalar weight.",
    },
    {
        "id": "BP.structural.global-arclength", "parent": "G.structural",
        "title": "Constructed global smooth arclength inverse",
        "depends_on": ["D.normal-loop"],
        "lean_target": "TightVer401.normalLoop_exists_global_arclength_inverse",
        "lean_file": "TightVer401/NormalLoopGlobalArclength.lean",
        "statement_tex": r"For smooth positive $L$-periodic $a$ with $L>0$, $S(r)=\int_0^r a$ is a global homeomorphism with smooth inverse $\psi$, $\psi'=1/a(\psi)$, and $\psi(s+S(L))=\psi(s)+L$.",
        "proof_sketch_tex": r"Actual positive derivative proves strict monotonicity. Periodic integration gives $S(r+L)=S(r)+S(L)$ with $S(L)>0$. Integer translates and the intermediate value theorem prove surjectivity. Join actual inverse function theorem neighborhoods and differentiate the inverse identity to obtain smoothness and the reciprocal derivative.",
    },
    {
        "id": "BP.structural.period", "parent": "G.structural",
        "title": "Whole-period characteristic integral from the nonlinear balance",
        "depends_on": ["BP.structural.global-arclength", "BP.structural.physical-frame"],
        "lean_target": "TightVer401.normalLoop_whole_period_balance",
        "lean_file": "TightVer401/NormalLoopPeriod.lean",
        "statement_tex": r"For the constructed global arclength inverse, $\rho=1/\sqrt a$, $D=\kappa_r/a^2$, and the actual whole-period characteristic integral equals $I_0=\tfrac12\int_0^L\kappa_r/\sqrt a\,dr$.",
        "proof_sketch_tex": r"Differentiate the actual physical $k$ and $\tau$. Their quotient terms cancel in $D$. Compute $\rho$ from $\tau=-1/a$, multiply the characteristic coefficient by the actual Jacobian $ds/dr=a$, and apply actual interval-integral substitution through the derived global inverse.",
    },
    {
        "id": "BP.structural.assembly", "parent": "G.structural",
        "title": "Constructed periodic ruled frame retains the prescribed normal loop",
        "depends_on": ["BP.structural.period", "BP.structural.closure", "BP.structural.frame"],
        "lean_target": "TightVer401.normalLoop_construct_periodic_ruled_frame",
        "lean_file": "TightVer401/NormalLoopRuledFrame.lean",
        "statement_tex": r"A positive closing periodic speed for the prescribed actual unit-speed spherical loop supplies the actual periodic frame required by the ruled theorem. Its curve and all frame maps are explicitly the integral primitive and spherical maps composed with the constructed inverse, and its characteristic period is one half of the nonlinear balance.",
        "proof_sketch_tex": r"Use exact vector closure to prove the actual integral curve periodic. The inverse period shift transfers all original periods to the physical period. Assemble smoothness, actual derivative equations, orthonormality and nonzero torsion into the periodic frame; retain each map identity and the whole-period integral as explicit outputs.",
    },
    {
        "id": "BP.stability.position", "parent": "G.stability",
        "title": "Uniform positional control from actual L1 speed smallness",
        "depends_on": ["D.normal-loop", "BP.structural.frame"],
        "lean_target": "TightVer401.normalLoopCurve_uniform_norm_sub_le",
        "lean_file": "TightVer401/NormalLoopStability.lean",
        "statement_tex": r"For every $r\in[0,L]$, the actual primitive curves satisfy $\lVert c_a(r)-c_b(r)\rVert\le\int_0^L|a-b|$. This does not by itself establish embedding stability.",
        "proof_sketch_tex": r"The derived unit frame gives $\lVert P\rVert=1$. Integral linearity writes the curve difference as the actual integral of $(a-b)P$. Bound its norm by the integral of $|a-b|$ and enlarge the prefix interval using nonnegativity.",
    },
    {
        "id": "BP.balance.normalized-control", "parent": "lem:finite-moment-balance",
        "title": "Actual normalized local control moments converge to samples",
        "depends_on": ["D.moment-path"],
        "lean_target": "TightVer401.normedBump_moment_tendsto",
        "lean_file": "TightVer401/MomentControlBump.lean",
        "statement_tex": r"Normalized smooth bumps centered at $c$ with radii tending to zero have mass one, short support, and actual vector moments tending to $f(c)$. Supports inside $(0,L)$ identify whole-real and period-interval moments.",
        "proof_sketch_tex": r"Use actual normalized smooth bumps and Bochner integration. Subtract the sample times the mass-one identity. The moment error is bounded by the oscillation of $f$ on the support, which tends to zero by continuity at $c$. Zero off the short support identifies the two integration domains.",
    },
    {
        "id": "BP.balance.path-basic", "parent": "lem:finite-moment-balance",
        "title": "Actual correction path positivity, exact moments and L1 estimate",
        "depends_on": ["D.moment-path"],
        "lean_target": "TightVer401.momentPathMoment_eq",
        "lean_file": "TightVer401/MomentPath.lean",
        "statement_tex": r"The displayed actual path $a_t=b-t\chi b+t\sum c_j\psi_j$ preserves the vector moment when the actual control moments solve the correction equation. For $0\le t<1$, disjointness and $\sum|c_j||\psi_j|<b$ on the controls prove positivity. Its actual L1 change is bounded uniformly by $\int|\chi b|+\sum|c_j|\int|\psi_j|$, including no controls.",
        "proof_sketch_tex": r"Differentiate or compose the explicit finite expression to prove smoothness and periodicity. Apply actual interval-integral linearity to cancel the correction moment. Split positivity according to whether $\chi$ vanishes, and use the strict control bound there. Apply the triangle inequality pointwise and integrate its finite sum.",
    },
    {
        "id": "BP.balance.period-continuity", "parent": "lem:finite-moment-balance",
        "title": "Actual nonlinear period continuity and slowdown scaling",
        "depends_on": ["D.moment-path"],
        "lean_target": "TightVer401.momentNonlinearPeriod_continuous",
        "lean_file": "TightVer401/MomentPeriod.lean",
        "statement_tex": r"A jointly continuous positive speed family on a locally compact parameter space has a continuous actual nonlinear period over a compact interval. For an exact slowdown $(1-t)b$, its actual period scales by $1/\sqrt{1-t}$ for $t<1$.",
        "proof_sketch_tex": r"Square-root positivity keeps the quotient continuous. The actual compact parametric integral theorem proves parameter continuity; equality of closed and half-open interval integrals gives the period form. Square-root multiplication and integral scalar linearity give the exact slowdown factor.",
    },
]

REFINEMENTS += [
    {
        "id": "BP.seed.variance", "parent": "G.seed-bounds",
        "title": "Strict variance monotonicity of the actual seed expectation",
        "depends_on": [],
        "lean_target": "TightVer401.corrugatedCosExpectation_strictAnti",
        "lean_file": "TightVer401/CorrugatedRootVariance.lean",
        "statement_tex": r"For $|\varepsilon|<1$, the actual normalized cosine expectation with weight $e^{-k\cos x}(1+\varepsilon\sin x)^2$ is strictly decreasing in $k$.",
        "proof_sketch_tex": r"Differentiate the actual compact interval moments. The derivative is minus the actual variance. Its centered-square integral is strictly positive because cosine is nonconstant and the weight is everywhere positive.",
    },
    {
        "id": "BP.seed.concentration", "parent": "G.seed-bounds",
        "title": "Actual exponential concentration at a compact minimum",
        "depends_on": [],
        "lean_target": "TightVer401.corrugatedCosExpectation_tendsto_atTop",
        "lean_file": "TightVer401/CorrugatedRootLimits.lean",
        "statement_tex": r"The actual normalized cosine expectation tends to $-1$ as $k\to+\infty$ and to $1$ as $k\to-\infty$.",
        "proof_sketch_tex": r"Bound the partition integral below on a positive-length neighborhood of a minimum and bound the moment outside a smaller sublevel set by an exponentially vanishing ratio. This also handles minima at an endpoint. Apply to $1+\cos x$ and $1-\cos x$.",
    },
    {
        "id": "BP.seed.scalar-root", "parent": "G.seed-bounds",
        "title": "Existence and uniqueness of the manuscript scalar root",
        "depends_on": ["BP.seed.variance", "BP.seed.concentration"],
        "lean_target": "TightVer401.corrugatedRoot_exists_unique_nat",
        "lean_file": "TightVer401/CorrugatedRootExistence.lean",
        "statement_tex": r"For every integer $N\ge10000$ there is a unique actual real $k_N$ such that $\int_0^{2\pi}e^{-k_N\cos x}(1+N^{-1}\sin x)^2(1+2\cos x)\,dx=0$.",
        "proof_sketch_tex": r"Rewrite the equation as normalized cosine expectation equal to $-1/2$. The two actual limits bracket this value, continuity gives a root by the intermediate value theorem, and strict decrease gives uniqueness. No numerical root is assumed.",
    },
    {
        "id": "BP.seed.joint-smoothness", "parent": "G.seed-bounds",
        "title": "Joint smoothness of the actual seed root integral",
        "depends_on": [],
        "lean_target": "TightVer401.corrugatedRootIntegral_joint_contDiff",
        "lean_file": "TightVer401/CorrugatedRootJoint.lean",
        "statement_tex": r"The actual seed integral is jointly smooth in $(\varepsilon,k)$.",
        "proof_sketch_tex": r"Use actual moment differentiation for all orders in $k$ and exact quadratic interpolation in $\varepsilon$ at $0,1,-1$. Smoothness follows from these actual expressions; it is not assumed for a selected solution.",
    },
    {
        "id": "BP.complete.end-forms", "parent": "G.complete",
        "title": "Actual fundamental forms and curvature of the cylinder end",
        "depends_on": ["D.coordinates", "BP.complete.profile"],
        "lean_target": "TightVer401.revolutionEnd_gaussianCurvature",
        "lean_file": "TightVer401/RevolutionEndCurvature.lean",
        "statement_tex": r"For the actual end $X(\theta,z)=q(z)e_\theta+ze_3$, derive metric $\operatorname{diag}(q^2,1+q'^2)$, normal $(-e_\theta+q'e_3)/\sqrt{1+q'^2}$, second form $\operatorname{diag}(q/w,-q''/w)$ and intrinsic curvature $-q''/[q(1+q'^2)^2]$ where $q>0$.",
        "proof_sketch_tex": r"Differentiate the actual Euclidean map twice. Its orthogonal tangent vectors prove immersion for $q\ne0$. Derive the normal and fundamental forms, then apply the audited OpenAI Gauss-equation bridge to the actual induced metric.",
    },
    {
        "id": "BP.complete.normal-height", "parent": "G.complete",
        "title": "Strictly increasing end normal height and its limit",
        "depends_on": ["BP.complete.end-forms", "BP.complete.profile"],
        "lean_target": "TightVer401.revolutionNormalHeight_strictMonoOn",
        "lean_file": "TightVer401/RevolutionEndNormalHeight.lean",
        "statement_tex": r"On the constructed convex half-line profile, the actual north normal height $q'/\sqrt{1+q'^2}$ has derivative $q''/(1+q'^2)^{3/2}>0$ and tends to $1$. This is a local end statement; global Gauss bijectivity and completeness remain separate.",
        "proof_sketch_tex": r"Differentiate the actual ratio and apply the mean value theorem. The profile's proved slope divergence and the elementary ratio limit give the height limit.",
    },
    {
        "id": "BP.cap.polar-support", "parent": "prop:dual-inversion",
        "title": "Actual support map and saddle curvature of the polar germ",
        "depends_on": ["BP.cap.inverse-germ", "BP.planar.second-form"],
        "lean_target": "TightVer401.polarSupportPotential_gaussianCurvature_neg",
        "lean_file": "TightVer401/PolarSupportCurvature.lean",
        "statement_tex": r"For $R>a>0$, the actual potential $G(p)=R|p|-a\sqrt{1+|p|^2}-C$ is smooth and saddle on the punctured plane. Its support map is $(Rp/|p|-ap/w,-a/w-C)$ and its intrinsic curvature is $-|p|/[a(Rw-a|p|)]<0$.",
        "proof_sketch_tex": r"Differentiate the actual radius and weight. Factor the Hessian as $A I+Bpp^T$, giving determinant $A(A+B|p|^2)=-a(Rw-a|p|)/(|p|w^4)$. Positivity of $Rw-a|p|$ proves the saddle sign, and the actual planar curvature bridge supplies intrinsic curvature.",
    },
    {
        "id": "BP.cap.double-primitive", "parent": "lem:cap",
        "title": "Actual double-primitive reconstruction and full germ uniqueness",
        "depends_on": [],
        "lean_target": "TightVer401.concaveJetReconstruction_eqOn_of_second_deriv",
        "lean_file": "TightVer401/ConcaveJetJoinReconstruction.lean",
        "statement_tex": r"An actual smooth acceleration $h$ reconstructs $q''=-h$ with prescribed value and slope. On an open connected interval where a local smooth representative has the same actual second derivative and first jet, the reconstruction equals that representative throughout the interval.",
        "proof_sketch_tex": r"Use the pinned OpenAI primitive twice and its actual derivative theorem. Derivative uniqueness on a connected open interval first identifies the first derivatives and then the values. Matching total mass and first moment also preserves the outgoing first jet.",
    },
]

REFINEMENTS += [
    {
        "id": "BP.seed.smooth-root", "parent": "G.seed-bounds",
        "title": "Smooth dependence of the actual selected seed root",
        "depends_on": ["BP.seed.scalar-root", "BP.seed.joint-smoothness", "BP.seed.variance"],
        "lean_target": "TightVer401.corrugatedRootValue_contDiffOn",
        "lean_file": "TightVer401/CorrugatedRootParameter.lean",
        "statement_tex": r"The unique actual seed root $k(\varepsilon)$ is smooth on $|\varepsilon|<1$.",
        "proof_sketch_tex": r"At the actual root, the $k$ derivative of the integral is strictly negative by the variance identity. Apply the smooth implicit function theorem to the jointly smooth actual integral. Actual global uniqueness makes the local implicit functions equal the selected root and therefore glues their smooth germs.",
    },
    {
        "id": "BP.cap.local-acceleration", "parent": "lem:cap",
        "title": "Smooth compact extension of only the local acceleration",
        "depends_on": [],
        "lean_target": "TightVer401.jetLocalExtension_contDiff",
        "lean_file": "TightVer401/ConcaveJetJoinLocalExtension.lean",
        "statement_tex": r"If $f$ is smooth only on an open interval $U$ and a smooth compact bump has closed support in $U$, its product with $f$ is globally smooth and agrees with $f$ where the bump is one.",
        "proof_sketch_tex": r"Inside the closed support use local smoothness and the product rule. Outside that support the product vanishes on a neighborhood. These actual germs establish global smoothness without extending the original representative itself.",
    },
    {
        "id": "BP.cap.small-moment-error", "parent": "lem:cap",
        "title": "Constructed shrinking blend has arbitrarily small actual moment error",
        "depends_on": ["BP.cap.local-acceleration"],
        "lean_target": "TightVer401.exists_concaveJetJoinBlend_small_radius",
        "lean_file": "TightVer401/ConcaveJetJoinBlendSmallness.lean",
        "statement_tex": r"Smoothly blend the two positive accelerations only in $(c-r,c+r)$. For any continuous finite-dimensional moment map and any positive error threshold, an arbitrarily small positive radius makes the actual vector moment error smaller than that threshold.",
        "proof_sketch_tex": r"The explicit smooth step lies between zero and one and has exact exterior values. The actual difference is supported in the shrinking interval. Compact continuity derives a uniform integrand bound $M$; interval integration gives error norm at most $2Mr$. Choose the radius against the requested threshold.",
    },
    {
        "id": "BP.cap.positive-correction", "parent": "lem:cap",
        "title": "Fixed control inverse corrects the actual two moments while preserving positivity",
        "depends_on": ["BP.balance.bump-basis", "BP.balance.coordinates-small"],
        "lean_target": "TightVer401.exists_jetAccelerationControl_threshold",
        "lean_file": "TightVer401/ConcaveJetJoinControl.lean",
        "statement_tex": r"Independent actual normalized control moments and their actual continuous coordinate inverse yield a positive error threshold. Correcting any smaller actual moment error preserves positive acceleration and changes it only on the fixed control supports.",
        "proof_sketch_tex": r"Bound the coordinate inverse and compact control amplitudes. Choose the threshold below the acceleration lower bound divided by these actual bounds. Integral linearity proves exact correction, and the coefficient bound preserves positivity. The seam assembly still has to construct the controls and choose its blend radius.",
    },
    {
        "id": "BP.cap.circular-boundary", "parent": "prop:saddle",
        "title": "Actual smooth circular resolution of the polar end",
        "depends_on": ["BP.cap.polar-support"],
        "lean_target": "TightVer401.polarCompactification_differential_injective",
        "lean_file": "TightVer401/PolarCompactificationGeometry.lean",
        "statement_tex": r"For $R>a>0$, the actual map $X(\theta,t)=(a\sin t-R)e_\theta+(C+a\cos t)e_3$ is smooth across $t=0$ and has injective actual differential. At the boundary its induced metric is $\operatorname{diag}(R^2,a^2)$.",
        "proof_sketch_tex": r"Differentiate the actual map. Its metric is $\operatorname{diag}((a\sin t-R)^2,a^2)$, and $a\sin t-R<0$ because $R>a$. The positive metric makes the actual differential injective even at the boundary. Equality with the support map on the interior is a separate actual reparametrization identity.",
    },
    {
        "id": "BP.cap.circular-support-agreement", "parent": "prop:saddle",
        "title": "Circular collar agrees with the actual negated polar support",
        "depends_on": ["BP.cap.circular-boundary", "BP.cap.polar-support"],
        "lean_target": "TightVer401.polarCompactification_eq_support",
        "lean_file": "TightVer401/PolarCompactificationSupport.lean",
        "statement_tex": r"Where $\sin t,\cos t>0$, the actual circular map equals the support map of $-G$ evaluated at $p=(\sin t/\cos t)e_\theta$.",
        "proof_sketch_tex": r"Compute the actual planar radius as $\sin t/\cos t$ and weight as $1/\cos t$ using the trigonometric identity. The actual support map is linear under negation. Substitute the proved polar support formula and simplify each Euclidean coordinate.",
    },
]

REFINEMENTS += [
    {
        "id": "BP.cap.full-finite", "parent": "lem:cap",
        "title": "Full finite radial cap with both retained germs",
        "depends_on": ["BP.cap.actual-derivatives", "BP.cap.relative-join"],
        "lean_target": "TightVer401.exists_finite_radial_cap",
        "lean_file": "TightVer401/RadialCapSmoothingFinite.lean",
        "statement_tex": r"For each positive incoming radius and slope, all sufficiently small positive widths admit a smooth strictly concave radial cap preserving an open incoming collar and the exact terminal square-root germ, with positive first derivative before the endpoint and the stated endpoint jets.",
        "proof_sketch_tex": r"Choose the actual width threshold giving $R>a$. Apply the relative first-jet join to the incoming local representative and the exact square-root cap. Recover the full outer germs and use the mean value theorem with strict concavity and terminal slope zero to derive positivity of the first derivative throughout the capped interior.",
    },
    {
        "id": "BP.cap.radial-hessian", "parent": "lem:cap",
        "title": "Actual radial Hessian on only the local profile domain",
        "depends_on": ["D.planar"],
        "lean_target": "TightVer401.radialPlanarPotential_hessian",
        "lean_file": "TightVer401/RadialPlanarPotential.lean",
        "statement_tex": r"On the punctured preimage of an open radial interval, the actual Hessian of $F(|p|)$ is $(F'/r)I+(F''/r^2-F'/r^3)pp^T$. Only local smoothness of $F$ on the interval is required.",
        "proof_sketch_tex": r"Differentiate the actual radius and the actual composition twice. The determinant is $F'F''/r$, so the checked planar curvature formula derives the saddle sign from the actual opposite signs of the radial derivatives.",
    },
    {
        "id": "BP.cap.circular-curvature", "parent": "prop:saddle",
        "title": "Actual curvature of the smooth circular boundary resolution",
        "depends_on": ["BP.cap.circular-boundary", "BP.cap.circular-support-agreement"],
        "lean_target": "TightVer401.polarCompactification_gaussianCurvature_neg",
        "lean_file": "TightVer401/PolarCompactificationCurvature.lean",
        "statement_tex": r"For $R>a>0$ and $\sin t>0$, the actual circular resolution has intrinsic curvature $\sin t/[a(a\sin t-R)]<0$, with its actual unit normal and second form derived from the map.",
        "proof_sketch_tex": r"Differentiate the actual map twice. Pair its second derivatives with the explicit unit normal to obtain the second form. Apply the audited Gauss equation to the actual metric and simplify the determinant ratio.",
    },
    {
        "id": "BP.seed.covariance", "parent": "G.seed-bounds",
        "title": "Actual positive-speed seed primitive and rotational covariance",
        "depends_on": ["BP.seed.scalar-root"],
        "lean_target": "TightVer401.corrugatedSeedPartner_cell",
        "lean_file": "TightVer401/CorrugatedSeedPrimitive.lean",
        "statement_tex": r"The constructed partner has actual derivative $\delta'=m_N\beta'$ with positive multiplier and satisfies the exact one-cell rotational covariance, hence the full period.",
        "proof_sketch_tex": r"Use the pinned OpenAI integral primitive and its actual derivative. The constant $I_N/(\xi_N-1)$ makes the cell shift equal multiplication by $\xi_N$; repeated shifts close the full period.",
    },
    {
        "id": "BP.seed.action", "parent": "G.seed-bounds",
        "title": "Exact zero mixed action of the constructed seed",
        "depends_on": ["BP.seed.covariance", "BP.seed.scalar-root"],
        "lean_target": "TightVer401.corrugatedSeedPartner_action",
        "lean_file": "TightVer401/CorrugatedSeedAction.lean",
        "statement_tex": r"The actual mixed determinant integral $\int_0^{2\pi}\det(\beta,\delta')$ vanishes for the constructed seed.",
        "proof_sketch_tex": r"Compute the determinant from the actual complex curves and their proved derivative. Substitution identifies the cell integral with the actual scalar root equation; covariance then gives the full-period identity.",
    },
    {
        "id": "BP.seed.analytic", "parent": "G.seed-bounds",
        "title": "Real analyticity of the actual integral partner",
        "depends_on": ["BP.seed.covariance"],
        "lean_target": "TightVer401.corrugatedSeedPartner_contDiff_analytic",
        "lean_file": "TightVer401/CorrugatedSeedAnalytic.lean",
        "statement_tex": r"Both explicit seed curves, including the partner defined by the actual real integral, are real analytic.",
        "proof_sketch_tex": r"Extend the explicit partner velocity holomorphically and construct a genuine holomorphic primitive. Its real restriction and the actual integral primitive have the same derivative; derivative uniqueness identifies them up to a constant, yielding real analyticity.",
    },
    {
        "id": "BP.seed.unit-tangent", "parent": "G.seed-bounds",
        "title": "Certified normalized tangent comparison",
        "depends_on": ["BP.seed.covariance"],
        "lean_target": "TightVer401.corrugatedSeedUnitTangent_error",
        "lean_file": "TightVer401/CorrugatedSeedNormalize.lean",
        "statement_tex": r"For $N>1$, the actual unit tangent differs from its explicit limiting tangent by less than $50/N$ uniformly in the parameter.",
        "proof_sketch_tex": r"Prove the limiting velocity has a uniform positive norm, bound the actual unnormalized error, and apply a proved normalization inequality. Every constant is obtained from actual real inequalities.",
    },
    {
        "id": "BP.seed.appendix-sixty", "parent": "G.seed-bounds",
        "title": "Exact appendix partner estimate still required",
        "depends_on": ["BP.seed.covariance", "BP.seed.unit-tangent"],
        "lean_target": "TightVer401.corrugatedSeedPartner_error_sixty",
        "lean_file": "TightVer401/CorrugatedSeedExactBounds.lean",
        "statement_tex": r"The appendix asserts $|\delta_N(t)-(i/2)e^{it}|<60/N$ for $N\ge10$. A weaker estimate sufficient for the numbered visibility lemma does not discharge this exact auxiliary assertion.",
        "proof_sketch_tex": r"Sharpen the actual normalized cell-average, quotient and within-cell motion bounds to the stated constant. Retain this obligation until an actual proof of the exact bound is audited.",
    },
    {
        "id": "BP.stability.fixed-tangent", "parent": "G.stability",
        "title": "Uniform positive tangent projection radius",
        "depends_on": [],
        "lean_target": "TightVer401.exists_speedCurve_tangent_radius",
        "lean_file": "TightVer401/CurveL1StabilityTangent.lean",
        "statement_tex": r"For a smooth periodic nowhere-zero tangent field $P$, compactness derives one positive radius on which nearby tangents have strictly positive scalar product.",
        "proof_sketch_tex": r"Take the attained positive minimum tangent norm and a uniform-continuity radius on a slightly enlarged period interval. Use the actual norm error to bound the scalar product below by a positive quantity.",
    },
    {
        "id": "BP.stability.distant-separation", "parent": "G.stability",
        "title": "Derived separation of distant baseline curve parameters",
        "depends_on": ["BP.stability.fixed-tangent"],
        "lean_target": "TightVer401.exists_speedCurve_distant_separation",
        "lean_file": "TightVer401/CurveL1StabilitySeparation.lean",
        "statement_tex": r"A continuous closed baseline curve injective on one half-open period interval has a positive distance between pairs of parameters separated from both the diagonal and the identified period endpoints.",
        "proof_sketch_tex": r"The relevant pair set is compact. Its actual distance function has no zero because baseline injectivity and endpoint closure exclude coincidences. Its attained minimum is therefore positive.",
    },
    {
        "id": "BP.stability.l1-embedding", "parent": "G.stability",
        "title": "Actual native circle embedding preserved by positive L1 speed perturbations",
        "depends_on": ["BP.stability.fixed-tangent", "BP.stability.distant-separation"],
        "lean_target": "TightVer401.exists_speedCurve_L1_embedding_threshold",
        "lean_file": "TightVer401/CurveL1StabilityCircle.lean",
        "statement_tex": r"Given a periodic nowhere-zero smooth tangent field and a positive smooth closing baseline speed whose primitive embeds the circle, derive a positive threshold such that every positive smooth closing speed within this actual $L^1$ threshold has a smooth embedded native circle primitive.",
        "proof_sketch_tex": r"Positive speeds preserve the strict local tangent projection monotonicity regardless of their pointwise size. The actual $L^1$ integral bounds the global positional change. The derived distant baseline separation excludes the remaining pairs; compactness upgrades native injectivity to embedding.",
    },
    {
        "id": "BP.complete.native-embedding", "parent": "G.complete",
        "title": "Actual proper native revolution-end embedding",
        "depends_on": ["BP.complete.end-forms"],
        "lean_target": "TightVer401.revolutionEndCircle_isClosedEmbedding",
        "lean_file": "TightVer401/RevolutionEndTopology.lean",
        "statement_tex": r"For a continuous positive profile on $[H,\infty)$, the actual revolution map from the native circle times the closed half-line is a proper closed embedding.",
        "proof_sketch_tex": r"The actual height recovers the half-line coordinate; positivity recovers the native angle from sine and cosine. Height bounds preimages of compact ambient sets, and compactness of the circle proves properness and the closed embedding.",
    },
    {
        "id": "BP.complete.native-immersion", "parent": "G.complete",
        "title": "Native actual manifold differential injectivity of the end extension",
        "depends_on": ["BP.complete.end-forms"],
        "lean_target": "TightVer401.revolutionEndCircleFull_mfderiv_injective",
        "lean_file": "TightVer401/RevolutionEndImmersion.lean",
        "statement_tex": r"The smooth full-cylinder extension of the actual revolution end has injective native manifold differential wherever the actual profile is nonzero.",
        "proof_sketch_tex": r"The quotient projection has surjective actual manifold differential. The actual chart chain rule transports the proved raw differential injectivity to the native cylinder.",
    },
    {
        "id": "BP.complete.gauss-smooth", "parent": "G.complete",
        "title": "Actual sphere-valued smooth native end Gauss map",
        "depends_on": ["BP.complete.native-immersion", "BP.complete.normal-height"],
        "lean_target": "TightVer401.revolutionEndCircleGauss_contMDiff",
        "lean_file": "TightVer401/RevolutionEndGaussSmooth.lean",
        "statement_tex": r"The actual end normal descends to a smooth sphere-valued native cylinder map. Positive actual profile second derivative makes its restriction to the closed end injective, and its height tends to one.",
        "proof_sketch_tex": r"Descend the explicit normal using the actual periodic quotient calculus. Prove unit length and orthogonality against the native manifold differential. Strict normal-height monotonicity recovers height and angular cancellation recovers the circle coordinate.",
    },
    {
        "id": "BP.complete.end-area", "parent": "G.complete",
        "title": "Actual product-measure absolute curvature of the end",
        "depends_on": ["BP.complete.end-forms", "BP.complete.normal-height"],
        "lean_target": "TightVer401.revolutionEnd_absoluteCurvature_product_integral",
        "lean_file": "TightVer401/RevolutionEndAreaProduct.lean",
        "statement_tex": r"The actual end absolute-curvature density is integrable and its product-measure integral is $2\pi(1-q'(H)/\sqrt{1+q'(H)^2})$.",
        "proof_sketch_tex": r"The actual metric and curvature identify the density with the derivative of the actual normal height. Apply improper interval integration, the proved limit one, and product integration. The whole attached cylinder integral remains separate.",
    },
    {
        "id": "BP.complete.height-length", "parent": "G.complete",
        "title": "Actual end curve-length escape bound",
        "depends_on": ["BP.complete.native-immersion"],
        "lean_target": "TightVer401.revolutionEndCircleCurve_length_lower_height",
        "lean_file": "TightVer401/RevolutionEndLength.lean",
        "statement_tex": r"The actual ambient length of every smooth native end curve bounds the absolute difference of its height coordinates.",
        "proof_sketch_tex": r"Use the actual composition chain rule and vector fundamental theorem of calculus. Coordinate projection is norm decreasing, so the actual integrated speed controls the height difference. Induced-metric completeness and attached-surface escape still require further arguments.",
    },
]

REFINEMENTS += [
    {
        "id": "BP.seed.uniform-position", "parent": "G.seed-bounds",
        "title": "Derived partner position bound sufficient for visibility",
        "depends_on": ["BP.seed.scalar-root", "BP.seed.covariance"],
        "lean_target": "TightVer401.corrugatedSeedPartner_uniform_error",
        "lean_file": "TightVer401/CorrugatedSeedUniformBounds.lean",
        "statement_tex": r"For $N\ge10000$, the actual selected-root partner satisfies $|\delta_N(t)-(i/2)e^{it}|\le100/N$ uniformly, and its radius lies between $49/100$ and $51/100$.",
        "proof_sketch_tex": r"Normalize the actual cell density, cancel odd sine terms and apply the actual root equation to bound its cosine average. Bound the actual cell quotient and primitive motion. The actual cell covariance makes the error periodic, so a fundamental-cell estimate holds globally. This does not discharge the appendix's sharper $60/N$ assertion.",
    },
    {
        "id": "BP.stability.native-immersion", "parent": "G.stability",
        "title": "L1 threshold also preserves actual native differential injectivity",
        "depends_on": ["BP.stability.l1-embedding"],
        "lean_target": "TightVer401.exists_speedCurve_L1_smooth_embedding_threshold",
        "lean_file": "TightVer401/CurveL1Stability.lean",
        "statement_tex": r"The same actual $L^1$ threshold yields a native smooth embedded primitive with injective actual manifold differential everywhere.",
        "proof_sketch_tex": r"The actual primitive derivative is $aP$, which is nonzero by positive speed and nonzero tangent. Use the native quotient projection's actual surjective differential and the chain rule to derive native differential injectivity; combine this with the constructed native embedding.",
    },
    {
        "id": "BP.jordan.native-range", "parent": "G.jordan",
        "title": "Native circle embedding has an actual Jordan range",
        "depends_on": [],
        "lean_target": "TightVer401.addCircle_complex_embedding_range_isJordanCurve",
        "lean_file": "TightVer401/NativeCircleJordan.lean",
        "statement_tex": r"Every actual continuous injective native period-circle map into the complex plane has a Jordan range after the exact physical-plane coordinate conversion.",
        "proof_sketch_tex": r"Use OpenAI's actual standard interval traversal, its endpoint closure, fundamental-interval injectivity and full-circle image. Transport the native quotient circle by the actual circle homeomorphism and apply the physical-plane continuous linear coordinates. Jordan separation still requires the separately compiled theorem.",
    },
    {
        "id": "BP.complete.c1-height-length", "parent": "G.complete",
        "title": "Actual C1 interval escape inequality in Mathlib path length",
        "depends_on": ["BP.complete.height-length"],
        "lean_target": "TightVer401.revolutionEndCircleCurve_height_edist_le_pathELength",
        "lean_file": "TightVer401/RevolutionEndPathELength.lean",
        "statement_tex": r"Every actual $C^1$ native curve on a compact parameter interval satisfies the height-distance bound by Mathlib's actual ambient-image path length.",
        "proof_sketch_tex": r"Apply the actual interval chain rule and the proved ambient Riemannian distance versus path-length inequality. Height projection is norm decreasing. No intrinsic metric comparison or completeness is assumed.",
    },
    {
        "id": "BP.complete.positive-extension", "parent": "G.complete",
        "title": "Constructed globally positive extension retains a full end neighborhood",
        "depends_on": ["BP.complete.profile"],
        "lean_target": "TightVer401.exists_revolutionEnd_positive_extension",
        "lean_file": "TightVer401/RevolutionEndPositiveExtension.lean",
        "statement_tex": r"A smooth profile positive on $[H,\infty)$ admits an actual smooth globally positive extension agreeing with it on $(b,\infty)$ for some $b<H$.",
        "proof_sketch_tex": r"Local positivity near $H$ and an actual smooth cutoff join the given positive end profile to a positive constant below it, preserving an entire neighborhood of the closed end. Check the actual exported type before using it in boundary metric assembly.",
    },
    {
        "id": "BP.complete.induced-riemannian", "parent": "G.complete",
        "title": "Actual native induced Riemannian metric",
        "depends_on": ["BP.complete.native-immersion", "BP.complete.positive-extension"],
        "lean_target": "TightVer401.revolutionEndRiemannianMetric",
        "lean_file": "TightVer401/RevolutionEndRiemannian.lean",
        "statement_tex": r"Construct the native cylinder's genuine Riemannian metric from its actual immersion differential and ambient Euclidean inner product.",
        "proof_sketch_tex": r"Pull back the actual inner product by the actual manifold differential twice. Differential injectivity gives positivity, and finite-dimensional inverse bounds give bounded unit sublevels. Prove the tangent-coordinate metric section smooth separately, then establish induced-distance comparison and completeness.",
    },
]

REFINEMENTS += [
    {
        "id": "BP.slowdown.scalar", "parent": "prop:one-slowdown",
        "title": "Actual scalar one-slowdown correction with arbitrary small support",
        "depends_on": [],
        "lean_target": "TightVer401.one_slowdown_holonomy_correction",
        "lean_file": "TightVer401/OneSlowdown.lean",
        "statement_tex": r"For the actual smooth periodic scalar data, a positive baseline of zero moment and nonconstant curvature admit positive smooth corrections with exact zero moment and nonlinear holonomy, arbitrarily small $L^1$ change, and at most two arbitrarily short projected support arcs.",
        "proof_sketch_tex": r"Derive both signs of the actual periodic curvature derivative and the scalar span bound. Apply the checked finite-moment prescription on the actual native circle; derive each support and period conclusion from its constructed correction.",
    },
    {
        "id": "BP.seed.visible-pairs", "parent": "lem:seed",
        "title": "Both actual strict seed visibility pairs",
        "depends_on": ["BP.seed.uniform-position"],
        "lean_target": "TightVer401.corrugatedSeed_visible_closed_pairs",
        "lean_file": "TightVer401/CorrugatedSeedVisiblePairs.lean",
        "statement_tex": r"For every integer $N\ge10000$, the actual closed smooth seed pair is strictly visible at radius $1/4$, and its reflected reversed pair is strictly visible at radius $4/5$.",
        "proof_sketch_tex": r"Use actual position and tangent estimates and the exact normalized visibility direction. Bound its change by the proved outer and inner Lipschitz estimates, then subtract the errors from the strict reference margins.",
    },
    {
        "id": "BP.seed.visible-angle", "parent": "lem:seed",
        "title": "Actual positive degree-one visibility angle",
        "depends_on": ["BP.seed.visible-pairs"],
        "lean_target": "TightVer401.corrugatedSeedVisibleAngle_deriv_pos",
        "lean_file": "TightVer401/CorrugatedSeedVisibilityAngleDerivative.lean",
        "statement_tex": r"The explicit actual angle $t+\pi/2+\arg(\delta_N(t)/((i/2)e^{it}))+\arccos((1/4)/|\delta_N(t)|)$ has strictly positive derivative. Its exponential is the actual visibility direction, and its lift shifts by exactly $2\pi$.",
        "proof_sketch_tex": r"The actual ratio estimate puts the logarithm in the right half-plane. Differentiate its argument and the actual arccos term. Their sum equals the positive visibility inner product divided by the positive square-root denominator. Periodic covariance gives the exact lift shift; the exponential identity follows from actual complex polar decomposition.",
    },
    {
        "id": "BP.seed.partner-jordan", "parent": "lem:seed",
        "title": "Actual partner injectivity, native embedding and Jordan separation",
        "depends_on": ["BP.seed.visible-angle", "BP.jordan.native-range"],
        "lean_target": "TightVer401.corrugatedSeedPartner_native_embedding",
        "lean_file": "TightVer401/CorrugatedSeedPartnerJordan.lean",
        "statement_tex": r"The actual seed partner induces a smooth embedding of the native $2\pi$ circle; its actual plane range is a Jordan curve and separates the plane.",
        "proof_sketch_tex": r"Strict monotonicity of the actual angle and its exact one-turn shift imply injectivity of its exponential on the fundamental interval. Since that exponential is a function of the partner point, the partner is injective there. Apply actual native quotient descent and the pinned Jordan theorem. Disk enclosure is still a separate obligation.",
    },
    {
        "id": "BP.jordan.actual-separation", "parent": "G.jordan",
        "title": "Actual periodic Jordan curves separate the plane",
        "depends_on": ["BP.jordan.native-range"],
        "lean_target": "TightVer401.periodicComplexCurve_separates",
        "lean_file": "TightVer401/PeriodicJordanSeparation.lean",
        "statement_tex": r"The actual range of a smooth periodic planar curve injective on a fundamental interval separates into the genuine Jordan inside and outside with the exact curve as frontier.",
        "proof_sketch_tex": r"Construct its native circle embedding and actual Jordan range, then apply the unconditional Jordan theorem from the exact dependency pinned by OpenAI. No membership of a specified point or disk is assumed or concluded here.",
    },
    {
        "id": "BP.normal-loop.embedded-frame", "parent": "G.stability",
        "title": "Balanced frame retains an actual embedded central curve",
        "depends_on": ["BP.stability.native-immersion"],
        "lean_target": "TightVer401.normalLoop_construct_embedded_balanced_frame",
        "lean_file": "TightVer401/NormalLoopEmbeddedFrame.lean",
        "statement_tex": r"A sufficiently small constructed balancing correction preserves the native smooth embedding and injective differential of the spatial central curve after actual arclength reparametrization.",
        "proof_sketch_tex": r"Use the checked positive-speed $L^1$ embedding threshold in the moment prescription, then transport representative injectivity through the constructed strictly monotone arclength inverse. Assemble the actual prescribed normal-loop ruled frame. Whole-band embedding remains separate.",
    },
    {
        "id": "BP.stability.covariant-embedding", "parent": "G.stability",
        "title": "Rotational covariance preserves native horizontal embedding",
        "depends_on": ["BP.stability.native-immersion"],
        "lean_target": "TightVer401.exists_covariantSpeedCurve_L1_smooth_embedding_threshold",
        "lean_file": "TightVer401/CovariantSpeedEmbedding.lean",
        "statement_tex": r"Actual rotational cell covariance with $\xi^N=1$ and $NT=L$ derives full-period closure and preserves smooth native embedding under positive sufficiently small $L^1$ speed changes.",
        "proof_sketch_tex": r"Construct the moving initial point from the cell primitive divided by $\xi-1$. Derive full closure from covariance. Translation does not change representative injectivity; apply the checked positive-speed primitive embedding theorem and native differential calculation.",
    },
    {
        "id": "BP.stability.covariant-visibility", "parent": "G.stability",
        "title": "Actual moving-start L1 perturbations preserve visibility margins",
        "depends_on": ["BP.seed.visible-pairs"],
        "lean_target": "TightVer401.exists_covariantSpeedCurve_L1_visibility_threshold",
        "lean_file": "TightVer401/CovariantSpeedVisibility.lean",
        "statement_tex": r"For an actual compact native baseline with strict radius and fixed-direction visibility margins, sufficiently small full-period $L^1$ perturbations of the covariant speed preserve all margins, including the movement of the initial point.",
        "proof_sketch_tex": r"Actual continuity of the normalized visibility direction gives a uniform neighborhood of the compact graph. Bound both the primitive change and its moving initial point by the actual speed $L^1$ change. Positive scalar velocity factors later recover the actual derivative visibility predicate.",
    },
    {
        "id": "BP.complete.native-length", "parent": "G.complete",
        "title": "Actual induced path length equals ambient image length",
        "depends_on": ["BP.complete.induced-riemannian", "BP.complete.c1-height-length"],
        "lean_target": "TightVer401.revolutionEnd_native_pathELength_eq_image",
        "lean_file": "TightVer401/RevolutionEndNativeLength.lean",
        "statement_tex": r"Every actual $C^1$ native cylinder path has induced Riemannian path length equal to the actual Euclidean length of its end-immersion image.",
        "proof_sketch_tex": r"Identify the exact installed induced norm with the norm of the actual manifold differential. Apply its actual composition chain rule pointwise, then integrate the identical speeds.",
    },
    {
        "id": "BP.complete.height-distance", "parent": "G.complete",
        "title": "Actual height is bounded by induced Riemannian distance",
        "depends_on": ["BP.complete.native-length"],
        "lean_target": "TightVer401.revolutionEnd_height_edist_le_riemannianEDist",
        "lean_file": "TightVer401/RevolutionEndDistance.lean",
        "statement_tex": r"The extended distance of the two height coordinates is bounded by the actual induced Riemannian distance between native cylinder points.",
        "proof_sketch_tex": r"Prove the height bound for every actual admissible $C^1$ path using image-length equality, then pass to the infimum defining the actual Riemannian distance. No completeness or distance comparison is granted.",
    },
    {
        "id": "BP.complete.ambient-distance", "parent": "G.complete",
        "title": "Actual ambient distance is bounded by induced distance",
        "depends_on": ["BP.complete.native-length"],
        "lean_target": "TightVer401.revolutionEnd_ambient_edist_le_riemannianEDist",
        "lean_file": "TightVer401/RevolutionEndAmbientDistance.lean",
        "statement_tex": r"The actual Euclidean distance between end-immersion images is bounded by the actual native induced Riemannian distance.",
        "proof_sketch_tex": r"Use the Euclidean distance versus actual image-path-length theorem for every admissible native path, substitute the actual induced-length equality and take the defining infimum.",
    },
]

REFINEMENTS += [
    {
        "id": "BP.seed.origin-enclosure", "parent": "lem:seed",
        "title": "Origin belongs to each actual bounded Jordan region",
        "depends_on": ["BP.seed.partner-jordan", "BP.jordan.actual-separation"],
        "lean_target": "TightVer401.corrugatedSeed_origin_inside",
        "lean_file": "TightVer401/CorrugatedSeedEnclosure.lean",
        "statement_tex": r"For every integer $N\ge10000$, the origin lies in the actual bounded Jordan component of each of the two constructed seed curves.",
        "proof_sketch_tex": r"Construct actual Schoenflies extensions of the native embeddings. Each explicit normalized position argument advances by exactly one turn. If zero were outside, the actual direction map would admit a continuous real lift on a simply connected enlarged Schoenflies disk avoiding zero. Uniqueness of the actual circle covering lift would then force zero argument increment, a contradiction. The radius bounds exclude zero from the actual frontier. Identify the homeomorphic disk with the bounded complementary component.",
        "target_signature": "theorem corrugatedSeed_origin_inside {N : ℕ} (hN : 10000 ≤ N) :\n  (0 : Schoenflies.Plane) ∈ Schoenflies.inside (Set.range (jordanComplexCoordinates.symm ∘ corrugatedSeedBeta (N : ℝ))) ∧\n  (0 : Schoenflies.Plane) ∈ Schoenflies.inside (Set.range (jordanComplexCoordinates.symm ∘ corrugatedSeedPartner (N : ℝ)))",
    },
    {
        "id": "BP.stability.thin-topology", "parent": "G.stability",
        "title": "Local injectivity yields a uniform embedded thin band",
        "depends_on": ["BP.normal-loop.embedded-frame"],
        "lean_target": "TightVer401.exists_thinBand_embedding",
        "lean_file": "TightVer401/ThinBandTopology.lean",
        "statement_tex": r"An actual continuous map on a compact parameter circle times the real line, injective on the central curve and locally injective there, is injective on a uniform closed strip and embeds its open strip.",
        "proof_sketch_tex": r"Use the actual compact injective-neighborhood theorem and compact thickening to obtain uniform width. The restriction to a larger compact closed strip is a closed embedding, hence its open-strip restriction is an actual embedding. Derive the local-injectivity inputs by actual strict derivative calculus rather than assuming a global neighborhood.",
    },
    {
        "id": "BP.stability.local-rank", "parent": "G.stability",
        "title": "Actual full-rank strict derivative excludes nearby collisions",
        "depends_on": [],
        "lean_target": "TightVer401.exists_local_injOn_of_injective_strictFDeriv",
        "lean_file": "TightVer401/ThinBandLocalCalculus.lean",
        "statement_tex": r"A map on a finite-dimensional real coordinate space with an actual injective strict derivative has an actual injective neighborhood.",
        "proof_sketch_tex": r"The actual injective linear derivative is anti-Lipschitz. Bound its actual strict derivative remainder by less than half the reciprocal constant; a collision then forces the coordinate difference to have zero norm. Transport through actual native circle charts for the ruled surface.",
    },
    {
        "id": "BP.complete.smooth-metric", "parent": "G.complete",
        "title": "Actual induced metric is a smooth native metric section",
        "depends_on": ["BP.complete.induced-riemannian"],
        "lean_target": "TightVer401.revolutionEndContMDiffRiemannianMetric",
        "lean_file": "TightVer401/RevolutionEndMetricCoordinates.lean",
        "statement_tex": r"The installed genuine native pullback metric has an actual smooth tangent-bundle metric section.",
        "proof_sketch_tex": r"Identify its actual tangent trivialization germ with the immersion differential in native coordinates. The actual smooth manifold differential and fixed ambient inner product give a smooth bilinear coordinate field. Derive the exact smooth Riemannian metric class used by Mathlib's distance construction.",
    },
    {
        "id": "BP.complete.model-completeness", "parent": "G.complete",
        "title": "Actual induced metric on the positive model cylinder is complete",
        "depends_on": ["BP.complete.smooth-metric", "BP.complete.height-distance"],
        "lean_target": "TightVer401.revolutionEnd_fullCylinder_complete",
        "lean_file": "TightVer401/RevolutionEndCompleteness.lean",
        "statement_tex": r"For a globally positive actual smooth profile, the native full cylinder is complete for its actual induced Riemannian distance.",
        "proof_sketch_tex": r"The actual height-distance inequality makes the heights of an intrinsic Cauchy sequence Cauchy. Compactness of the native angular factor supplies a convergent subsequence. Actual smooth metric topology agreement gives convergence in the induced distance and therefore convergence of the full Cauchy sequence. Use the exact induced metric structure, avoiding the preexisting product metric instance. The restricted end with boundary and globally assembled surface remain separate.",
    },
]

REFINEMENTS += [
    {
        "id": "BP.seed.spherical-embedding", "parent": "lem:seed",
        "title": "Actual northern spherical seed is natively embedded",
        "depends_on": [],
        "lean_target": "TightVer401.corrugatedSeedSphere_native_embedding",
        "lean_file": "TightVer401/CorrugatedSeedSphereNative.lean",
        "statement_tex": r"The explicit gnomonic seed lift induces an actual smooth embedded native circle in the unit sphere and lies in the northern hemisphere.",
        "proof_sketch_tex": r"Use the actual gnomonic chart, its smooth inverse and seed representative injectivity. Descend its genuine smooth sphere-valued map through the actual period quotient; compactness upgrades continuous injectivity to the native embedding.",
    },
    {
        "id": "BP.seed.arclength-curvature", "parent": "lem:seed",
        "title": "Constructed unit-speed spherical seed has both curvature signs",
        "depends_on": ["BP.seed.spherical-embedding"],
        "lean_target": "TightVer401.corrugatedSeedSphere_exists_arclength",
        "lean_file": "TightVer401/CorrugatedSeedSphereArclength.lean",
        "statement_tex": r"An actual global inverse arclength homeomorphism reparametrizes the explicit seed to a smooth unit-speed periodic embedded northern spherical curve whose actual normal-loop curvature takes both signs.",
        "proof_sketch_tex": r"Integrate the actual positive spherical speed, construct and differentiate the actual global inverse, and derive its period shift. Compute the actual normalized homogeneous lift triple determinant and its composition transformation. The planar determinants at zero and half a cell give the required actual signed curvatures.",
    },
    {
        "id": "BP.stability.ruled-band", "parent": "G.stability",
        "title": "Actual periodic ruled frame has an embedded thin native band",
        "depends_on": ["BP.stability.thin-topology", "BP.stability.local-rank"],
        "lean_target": "TightVer401.periodicRuledFrame_exists_thin_band_embedding",
        "lean_file": "TightVer401/ThinBandRuledEmbedding.lean",
        "statement_tex": r"An actual periodic ruled frame with embedded central curve admits a genuine embedded native thin band.",
        "proof_sketch_tex": r"Its actual frame equations give an injective rank-two derivative. Use the strict derivative collision bound and actual translated quotient charts to derive local injectivity. Apply the compact thin-strip theorem to the actual globally continuous ruled map.",
    },
    {
        "id": "BP.stability.ruled-gauss", "parent": "G.stability",
        "title": "Actual embedded normal loop gives thin Gauss injectivity",
        "depends_on": ["BP.stability.thin-topology", "BP.stability.local-rank"],
        "lean_target": "TightVer401.periodicRuledFrame_exists_thin_Gauss_injective",
        "lean_file": "TightVer401/ThinBandRuledGauss.lean",
        "statement_tex": r"For an actual periodic ruled frame with embedded central normal curve, the actual Gauss map is injective on a uniform thin neighborhood.",
        "proof_sketch_tex": r"Derive smoothness and full-rank Gauss differential from the actual second fundamental determinant, then transport local injectivity through actual native quotient charts and apply compact central-curve separation.",
    },
    {
        "id": "BP.relative.full-upgrade", "parent": "cor:relative-holonomy-upgrade",
        "title": "Complete relative holonomy upgrade with coherent embedded path",
        "depends_on": ["BP.normal-loop.embedded-frame", "BP.stability.ruled-band", "BP.stability.ruled-gauss"],
        "lean_target": "TightVer401.normalLoop_relative_holonomy_upgrade",
        "lean_file": "TightVer401/NormalLoopRelativeUpgrade.lean",
        "statement_tex": r"Every actual embedded closing seed admits arbitrarily small balanced corrections, a jointly smooth path through closed embedded curves with fixed oriented tangent and normal, preservation of every specified regular embedded linear projection, and a thin Gauss-injective resulting band when its prescribed normal loop is embedded.",
        "proof_sketch_tex": r"Choose one moment correction smaller than the spatial, projected and positional thresholds. Construct its actual positive convex speed interpolation and coherent native circle family. Assemble the same corrected speed's actual global arclength inverse and periodic physical frame, then apply the actual thin-band and Gauss theorems.",
    },
    {
        "id": "BP.jordan.schoenflies-extension", "parent": "G.jordan",
        "title": "Actual continuous circle embedding extends to the plane",
        "depends_on": ["BP.jordan.native-range"],
        "lean_target": "TightVer401.exists_complex_schoenflies",
        "lean_file": "TightVer401/NativePlanarSchoenflies.lean",
        "statement_tex": r"Every actual continuous injective complex circle map extends to a genuine plane homeomorphism with the prescribed exact boundary map.",
        "proof_sketch_tex": r"Apply the actual relative Jordan-Schoenflies theorem selected by OpenAI to the standard circle and constructed image range, and conjugate by the exact physical-plane coordinates. This is the argument of the pinned OpenAI proof using its already checked adapter.",
    },
]

REFINEMENTS += [
    {
        "id": "BP.seed.positive-turn", "parent": "lem:seed",
        "title": "Both actual seed arguments make one positive turn",
        "depends_on": ["BP.seed.origin-enclosure"],
        "lean_target": "TightVer401.corrugatedSeed_positive_argument_turns",
        "lean_file": "TightVer401/CorrugatedSeedEnclosure.lean",
        "statement_tex": r"Each actual normalized seed position admits a continuous real argument lift whose increment over the full period is exactly $+2\pi$. Together with actual Jordan enclosure this gives positive orientation about an interior point.",
        "proof_sketch_tex": r"Use the explicit phase for beta and the actual ratio argument for the partner; actual cell covariance makes the ratio periodic and hence its argument increment zero.",
    },
    {
        "id": "BP.seed.whole-package", "parent": "lem:seed",
        "title": "Assemble the complete actual analytic seed",
        "depends_on": ["BP.seed.positive-turn", "BP.seed.partner-jordan"],
        "lean_target": "TightVer401.corrugated_analytic_seed",
        "lean_file": "TightVer401/CorrugatedAnalyticSeed.lean",
        "statement_tex": r"For every $N\ge10000$ the exact constructed seed has analyticity, actual native embeddings and Jordan ranges enclosing zero with positive argument turns, covariance, positive tangent multiplier, zero mixed action, both strict visibility pairs, and an embedded northern spherical lift whose actual geodesic curvature has both signs.",
        "proof_sketch_tex": r"Combine the checked properties of the same explicit beta, constructed partner and spherical lift. No existence or geometric conclusion is passed in as a hypothesis.",
    },
    {
        "id": "BP.complete.boundary-completeness", "parent": "G.complete",
        "title": "The actual closed end is intrinsically complete",
        "depends_on": ["BP.complete.smooth-metric"],
        "lean_target": "TightVer401.revolutionEnd_closedEnd_complete",
        "lean_file": "TightVer401/RevolutionEndBoundaryCompleteness.lean",
        "statement_tex": r"The native closed end, including its actual manifold boundary, is complete for its own induced Riemannian distance, defined using paths constrained to that end.",
        "proof_sketch_tex": r"Height is bounded by actual intrinsic distance, so heights of a Cauchy sequence converge within the closed height half-line. Compactness of the angular circle yields a convergent subsequence in the original topology; the actual induced metric has exactly that topology, and Cauchy convergence follows.",
    },
    {
        "id": "BP.complete.constructed-end", "parent": "G.complete",
        "title": "Construct a complete end retaining the actual attachment collar",
        "depends_on": ["BP.complete.boundary-completeness", "BP.complete.end-area"],
        "lean_target": "TightVer401.exists_revolutionEnd_complete_continuation",
        "lean_file": "TightVer401/RevolutionEndConstruction.lean",
        "statement_tex": r"From a positive strictly convex radial germ construct the actual complete rotational continuation, agreeing on a uniform surface collar, with positive radial derivatives, smooth immersed closed embedding, its own induced-metric completeness, smooth injective Gauss map, and absolute curvature integral below $2\pi$.",
        "proof_sketch_tex": r"Construct the actual radial profile, transport germ agreement uniformly to the surface collar, and apply actual boundary calculus, proper embedding, induced completeness and area identities to that same profile.",
    },
    {
        "id": "BP.complete.gauss-image", "parent": "G.complete",
        "title": "Exact spherical image of the actual rotational end",
        "depends_on": ["BP.complete.constructed-end"],
        "lean_target": "TightVer401.revolutionEndGauss_range",
        "lean_file": "TightVer401/RevolutionEndGaussImage.lean",
        "statement_tex": r"The actual end Gauss image is precisely the punctured spherical cap whose normal height runs from the actual boundary height, included, up to the north height one, excluded.",
        "proof_sketch_tex": r"Prove the actual scalar height image by strict monotonicity, the north limit and the intermediate value theorem. Reconstruct the circle angle from the negative horizontal complex argument of an actual target sphere point.",
    },
    {
        "id": "BP.complete.gauss-inverse", "parent": "G.complete",
        "title": "Actual inverse between the closed end and its exact cap",
        "depends_on": ["BP.complete.gauss-image"],
        "lean_target": "TightVer401.revolutionEndGaussEquiv",
        "lean_file": "TightVer401/RevolutionEndGaussInverse.lean",
        "statement_tex": r"The actual Gauss map is a bijection from the closed end to its actual punctured cap; its inverse is the actual angle reconstruction and the uniquely determined inverse normal height.",
        "proof_sketch_tex": r"Use the proved height range and strict monotonicity to choose the unique height; verify both inverse identities by actual sphere coordinates. Topological and smooth inverse regularity remain separate refinements.",
    },
]

REFINEMENTS += [
    {
        "id": "BP.spike.actual-speed", "parent": "thm:spike",
        "title": "Construct the balanced embedded speed of the exact seed",
        "depends_on": ["BP.seed.whole-package", "BP.slowdown.scalar", "BP.stability.covariant-visibility"],
        "lean_target": "TightVer401.corrugatedSeed_exists_balanced_embedded_speed",
        "lean_file": "TightVer401/CorrugatedSpike.lean",
        "statement_tex": r"For each actual seed and every positive cell $L^1$ tolerance, construct its spherical arclength inverse and positive cell-periodic speed with actual scalar and full spatial closure, actual nonlinear return balance, embedded native spatial curve and exact horizontal projection, and both strict visibility pairs.",
        "proof_sketch_tex": r"Discharge the scalar slowdown inputs from the exact seed frame and actual curvature sign change. Choose one correction within the actual covariant positional and embedding thresholds. Preserve the same corrected speed in the full native primitives and both visible pairs; retain its short native support arcs.",
    },
    {
        "id": "BP.complete.inverse-boundary-smooth", "parent": "G.complete",
        "title": "Actual height inverse is smooth through the end boundary",
        "depends_on": ["BP.complete.gauss-inverse"],
        "lean_target": "TightVer401.revolutionHeightInverse_contDiffOn_closed",
        "lean_file": "TightVer401/RevolutionEndHeightInverseBoundary.lean",
        "statement_tex": r"The actual inverse normal height is smooth on the half-open height interval of the complete end, including its lower boundary in the relative smooth sense.",
        "proof_sketch_tex": r"Use the actual nonzero normal-height derivative and OpenAI's local smooth inverse theorem. At the boundary, continuity of the radial second derivative gives a strictly monotone extension below the boundary height; identify its actual local inverse with the globally chosen unique height inverse on their shared half-interval.",
    },
    {
        "id": "BP.smoothing.tangent-jet", "parent": "lem:smoothing",
        "title": "Matching actual gradient trace fixes the Hessian tangent column",
        "depends_on": ["BP.planar.gradient-inverse"],
        "lean_target": "TightVer401.seam_hessian_tangent_action",
        "lean_file": "TightVer401/SeamHessian.lean",
        "statement_tex": r"If two smooth actual planar potentials have the same gradient trace near a parameter on a differentiable seam, their actual Hessians have the same action on that seam tangent.",
        "proof_sketch_tex": r"Differentiate the actual common gradient trace by the chain rule and identify both gradient derivatives with the actual Hessian matrices. Derivative uniqueness gives equality of the tangent columns; this supplies common tangential and mixed entries in a tangent-normal frame.",
    },
]

REFINEMENTS += [
    {
        "id": "BP.band.identity-period", "parent": "G.flow",
        "title": "Actual identity return forces the characteristic period to vanish",
        "depends_on": ["BP.stability.ruled-band"],
        "lean_target": "TightVer401.periodicRuledFrame_identity_band_period_zero",
        "lean_file": "TightVer401/IdentityBandPeriodKernel.lean",
        "statement_tex": r"For the actual periodic ruled frame, identity return of the actual nonruling asymptotic trajectories is equivalent to vanishing of the actual characteristic period integral.",
        "proof_sketch_tex": r"Choose a nonzero transverse value within both the actual return and projective formula neighborhoods. The actual fixed-point identity forces the projective coefficient to vanish; the strictly positive rho factor gives actual integral cancellation.",
    },
    {
        "id": "BP.band.global-leaves", "parent": "G.flow",
        "title": "Complete smooth periodic asymptotic leaves remain in the selected band",
        "depends_on": ["BP.band.identity-period"],
        "lean_target": "TightVer401.periodicRuledFrame_closed_asymptotic_leaves",
        "lean_file": "TightVer401/IdentityBandGlobalFlow.lean",
        "statement_tex": r"For any cross-section and positive band width, construct a common positive initial interval whose actual trajectories are smooth, periodic, pole-free, and contained in the selected band for all real time, with the actual asymptotic ODE and vanishing actual normal second form on their tangents.",
        "proof_sketch_tex": r"Actual period cancellation makes Omega periodic. Compactness of the actual circle controls the denominator on the whole line. The positive minimum of rho bounds trajectory heights; the exact rational flow formula proves periodicity, smoothness, the ODE and the actual asymptotic tangent identity.",
    },
    {
        "id": "BP.band.supported-kernel", "parent": "thm:ruled",
        "title": "A genuine localized kernel on the same identity band",
        "depends_on": ["BP.band.identity-period"],
        "lean_target": "TightVer401.periodicRuledFrame_identity_band_supported_kernel",
        "lean_file": "TightVer401/IdentityBandPeriodKernel.lean",
        "statement_tex": r"On the same actual identity band construct a nonzero compact supported infinitesimal bending and the attained canonical profile cutoff; every compact supported bending has a unique smooth compact supported profile above that cutoff.",
        "proof_sketch_tex": r"Derive the actual vanishing period from identity return, use the actual primitive Omega and attained circle maximum, and apply the checked ruled-band sufficiency and classification to the same frame and width.",
    },
    {
        "id": "BP.band.seed-existence", "parent": "thm:spike",
        "title": "Construct the actual embedded seed band with identity holonomy",
        "depends_on": ["BP.spike.actual-speed", "BP.band.global-leaves", "BP.band.supported-kernel"],
        "lean_target": "TightVer401.corrugatedSeed_exists_identity_holonomy_band",
        "lean_file": "TightVer401/CorrugatedIdentityBand.lean",
        "statement_tex": r"From only an actual seed index $N\ge10000$ and positive L1 tolerance, construct the same corrected speed, seed arclength inverse, physical arclength frame and translated central primitive, with a positive common width giving native smooth immersion, spatial and horizontal embeddings, injective northern Gauss map, negative intrinsic curvature, actual identity return, complete closed asymptotic leaves and a nonzero localized bending.",
        "proof_sketch_tex": r"Choose the scalar correction directly from the actual seed. Retain that speed through both visibility pairs and the physical frame. Translate the central primitive to its prescribed covariant start without changing the normal, frame coefficients or holonomy. Intersect actual embedding, projection, Gauss and northern widths and apply actual period, flow and kernel theorems on this same band.",
    },
    {
        "id": "BP.band.native-gauss", "parent": "G.surface",
        "title": "Actual smooth sphere-valued Gauss map of the native band",
        "depends_on": ["BP.stability.ruled-gauss"],
        "lean_target": "TightVer401.periodicRuledFrame_bandSphereGauss_contMDiff",
        "lean_file": "TightVer401/PeriodicRuledNativeGauss.lean",
        "statement_tex": r"The exact ruled normal descends to a native smooth unit-sphere-valued Gauss map, is orthogonal to the actual band differential, and has an injective actual Gauss differential.",
        "proof_sketch_tex": r"Use the actual periodic frame components in the quotient atlas, differentiate the actual ruled normal, and transport through the surjective native coordinate differential. Derive the sphere constraint and injectivity from the actual ambient differential rather than assuming sphere regularity.",
    },
]

REFINEMENTS += [
    {
        "id": "BP.band.flow-annulus", "parent": "G.flow",
        "title": "A native embedded annulus parametrized by complete closed leaves",
        "depends_on": ["BP.band.global-leaves", "BP.band.identity-period"],
        "lean_target": "TightVer401.periodicRuledFrame_exists_embedded_flow_annulus",
        "lean_file": "TightVer401/IdentityBandSaturatedAnnulus.lean",
        "statement_tex": r"Inside the selected embedded band construct a native annulus parametrized by circle phase and a positive initial-value interval. Each constant-initial-value circle is a complete closed actual asymptotic leaf. The parametrized image is the protected leaf-filled region; saturation is not asserted of the full original rectangular strip.",
        "proof_sketch_tex": r"Descend the actual periodic rational trajectory to quotient coordinates. An explicit continuous inverse recovers the initial value and proves actual coordinate embedding. Compose with the same geometric band and derive native smoothness and immersion from the actual differential.",
    },
]

REFINEMENTS += [
    {
        "id": "BP.band.native-projection", "parent": "G.stability",
        "title": "Horizontal projection is regular throughout the selected northern band",
        "depends_on": ["BP.band.native-gauss"],
        "lean_target": "TightVer401.periodicRuledFrame_northern_band_projection_regular",
        "lean_file": "TightVer401/PeriodicRuledNativeProjection.lean",
        "statement_tex": r"The exact native horizontal projection is smooth and has injective actual manifold differential at every point of the selected northern band.",
        "proof_sketch_tex": r"A tangent vector with zero horizontal projection is vertical. Actual orthogonality to a normal with nonzero vertical component forces that ambient tangent to vanish; actual immersion then forces the original tangent to vanish. Transport the actual linear projection derivative by the manifold chain rule.",
    },
    {
        "id": "BP.band.flow-immersion", "parent": "G.flow",
        "title": "The actual flow annulus has nonsingular native differential",
        "depends_on": ["BP.band.global-leaves"],
        "lean_target": "TightVer401.identityFlowSurface_immersion",
        "lean_file": "TightVer401/IdentityBandFlowImmersion.lean",
        "statement_tex": r"The native complete-flow surface has injective actual manifold differential, as a consequence of its explicit smooth coordinate inverse and the actual ruled-band immersion.",
        "proof_sketch_tex": r"Recover the initial value by the exact rational inverse on an open neighborhood of each image point. Its actual derivative composes with the flow-coordinate derivative to the identity, proving injectivity. Compose with the actual band immersion.",
    },
    {
        "id": "BP.band.seed-protected-annulus", "parent": "thm:spike",
        "title": "The same exact seed constructs the identity band and its protected flow annulus",
        "depends_on": ["BP.band.seed-existence", "BP.band.flow-annulus", "BP.band.flow-immersion", "BP.band.native-projection"],
        "lean_target": "TightVer401.corrugatedSeed_exists_protected_identity_holonomy_band",
        "lean_file": "TightVer401/CorrugatedIdentityFlowBand.lean",
        "statement_tex": r"From only the seed index and positive L1 tolerance, retain the same balanced speed, physical frame and common width to construct the embedded identity band together with a smooth immersed embedded flow annulus of complete closed asymptotic leaves inside it. Both visibility pairs and regular northern Gauss and horizontal projection are retained. The separate localized bending is supported in the original band; the separate protected-bending refinement places full support inside the chosen flow-annulus image.",
        "proof_sketch_tex": r"Apply the concrete same-speed identity-band construction, derive the actual characteristic period from its actual identity return, and use the native complete-flow annulus on this exact frame and width.",
    },
]

REFINEMENTS += [
    {
        "id": "BP.band.protected-bending",
        "parent": "thm:ruled",
        "title": "Place the full bending support inside the protected flow annulus",
        "depends_on": [
            "BP.band.supported-kernel",
            "BP.band.flow-annulus"
        ],
        "lean_target": "TightVer401.periodicRuledFrame_exists_protected_bending",
        "lean_file": "TightVer401/IdentityBandProtectedBending.lean",
        "statement_tex": "For the same identity frame, any positive original band width and any positive flow parameter, construct a nonzero compactly supported infinitesimal bending whose full topological support has coordinate image inside the actual flow-coordinate image and actual surface image inside the actual flow-surface image.",
        "proof_sketch_tex": "Choose a smooth profile bump above both the attained band cutoff and the section invariant cutoff. Control the full vector-profile support, including its derivative term, by the actual invariant coordinate. Solve the exact rational inverse to locate every support point in the protected annulus."
    },
    {
        "id": "BP.band.flow-bending-pullback",
        "parent": "thm:ruled",
        "title": "Actual nonzero compact bending on the native flow annulus",
        "depends_on": [
            "BP.band.protected-bending",
            "BP.band.flow-immersion"
        ],
        "lean_target": "TightVer401.identityFlowSurface_compact_nonzero_bending",
        "lean_file": "TightVer401/IdentityBandBendingPullback.lean",
        "statement_tex": "The protected bending pulled back through the actual smooth flow inclusion is an actual infinitesimal bending of the native flow surface, has compact support in that annulus and has a nonzero value.",
        "proof_sketch_tex": "Apply the actual manifold derivative chain rule to both maps and the zero-strain identity to their actual coordinate derivatives. A compact support contained in an embedding image has compact inverse image. A nonzero support point supplies a nonzero pullback point."
    },
    {
        "id": "BP.band.branch-metric",
        "parent": "prop:metric",
        "title": "Opposite band perturbations have exactly equal induced metrics",
        "depends_on": [
            "D.band-bending"
        ],
        "lean_target": "TightVer401.bandBending_opposite_branches_metric",
        "lean_file": "TightVer401/BandBendingBranches.lean",
        "statement_tex": "For an actual smooth native band map and actual bending, the maps $\\phi+\\varepsilon Y$ and $\\phi-\\varepsilon Y$ have the same actual induced form for every amplitude: $g_\\phi+\\varepsilon^2g_Y$. They are smooth and agree with the original map as germs outside the full support.",
        "proof_sketch_tex": "Differentiate the actual sum and expand the ambient inner product. Actual zero strain cancels the linear term, opposite amplitudes have equal squares, and the open support complement gives germ agreement."
    },
    {
        "id": "BP.band.branch-immersion",
        "parent": "G.stability",
        "title": "Actual band immersion survives every bending amplitude",
        "depends_on": [
            "BP.band.branch-metric"
        ],
        "lean_target": "TightVer401.bandBending_branch_immersion",
        "lean_file": "TightVer401/BandBendingBranches.lean",
        "statement_tex": "If the original actual band differential is injective at every point, every bending branch has injective differential at every amplitude. Global embedding is a separate question.",
        "proof_sketch_tex": "A tangent annihilated by the branch differential has zero branch norm. The common metric expresses this as the original squared norm plus a nonnegative squared bending norm. Original differential injectivity forces the tangent to vanish."
    },
    {
        "id": "BP.band.branch-distinction",
        "parent": "prop:metric",
        "title": "Nonzero amplitudes give distinct parametrized band maps",
        "depends_on": [
            "BP.band.branch-metric"
        ],
        "lean_target": "TightVer401.bandBending_opposite_branches_ne",
        "lean_file": "TightVer401/BandBendingBranches.lean",
        "statement_tex": "A nonzero bending and nonzero amplitude give distinct parametrized opposite branches. This does not assert noncongruence of their unparametrized images.",
        "proof_sketch_tex": "At an actual point where the bending is nonzero, equality of the two maps would force twice the nonzero amplitude times that vector to vanish."
    },
    {
        "id": "BP.band.seed-protected-bending",
        "parent": "thm:spike",
        "title": "The exact seed constructs the identity band and protected localized bending",
        "depends_on": [
            "BP.band.seed-protected-annulus",
            "BP.band.protected-bending",
            "BP.band.flow-bending-pullback",
            "BP.band.branch-metric"
        ],
        "lean_target": "TightVer401.corrugatedSeed_exists_protected_identity_band_bending",
        "lean_file": "TightVer401/CorrugatedIdentityBendingBand.lean",
        "statement_tex": "From only the seed index and positive L1 tolerance, retain the same balanced speed, physical frame and embedded identity band. Construct a protected smooth immersed embedded annulus of complete closed asymptotic leaves and a genuine nonzero compact bending whose full support is inside that exact annulus. Its native pullback has compact support and is nonzero. Every opposite perturbation pair is smooth and immersive, has exact common metric, and has distinct parametrized maps when the amplitude is nonzero.",
        "proof_sketch_tex": "Keep the concrete same-speed band witnesses, derive the actual characteristic period from actual identity return, choose the protected annulus and the profile above both support cutoffs. Pull back through the actual inclusion and apply native metric branching, positivity-based immersion preservation and nonzero map distinction on this same annulus."
    }
]

LOCAL_LEMMAS = [
    ("L.support.domain-agreement", "TightVer401.hemisphereSupport_agrees_domain"),
    ("L.support.domain-height", "TightVer401.hemisphereHeight_contDiffOn"),
    ("L.support.domain-smooth", "TightVer401.hemisphereSupport_contDiffOn"),
    ("L.sphere.inverse-smooth", "TightVer401.sphereHemisphereInverse_contDiffAt"),
    ("L.gauss.local-inverse", "TightVer401.gaussMap_exists_smooth_inverse_coordinates"),
    ("L.gauss.local-reconstruction", "TightVer401.gaussSupport_reconstruction_local"),
    ("L.manifold.gauss-local", "TightVer401.gaussManifold_exists_smooth_local_inverse"),
    ("L.manifold.gauss-open", "TightVer401.gaussManifold_image_isOpen"),
    ("L.support.open-converse", "TightVer401.globalSphereSupport_converseOn"),
    ("L.support.local-forms", "TightVer401.sphereSupportMap_secondFundamental"),
    ("L.support.curvature-at", "TightVer401.sphereSupportMap_curvature_at"),
    ("L.sphere.chart-differentiable", "TightVer401.sphereHemisphereChart_mdifferentiable"),
]

def text_escape(s):
    table = {"\\": r"\textbackslash{}", "&": r"\&", "%": r"\%", "$": r"\$", "#": r"\#",
             "_": r"\_", "{": r"\{", "}": r"\}", "~": r"\textasciitilde{}", "^": r"\textasciicircum{}"}
    return "".join(table.get(c, c) for c in s)

def build(root):
    # The retained legacy plan is only a historical reference.
    target = json.loads((root / "target-lock.json").read_text(encoding="utf-8"))["target"]
    if target == "ver503":
        from ver503_blueprint import main as active_main
        active_main()
        return
    raise ValueError("Only the active ver503 target may be regenerated in this publication checkout")


def _historical_ver401_build(root):
    out = root / "blueprint"
    overview = json.loads((out / "blueprint.json").read_text(encoding="utf-8"))
    audit_path = root / "kernel-report.json"
    audit = json.loads(audit_path.read_text(encoding="utf-8"))
    assert overview["certificate"]["audit_sha256"] == hashlib.sha256(audit_path.read_bytes()).hexdigest()
    declarations = {d["name"]: d for d in audit["declarations"]}
    source = root.parents[1] / "counterexample_long/ver401/saddle_reconstruction_ver401.tex"
    manuscript = source.read_text(encoding="utf-8-sig")
    claims = [n for n in overview["nodes"] if n["kind"] == "manuscript_claim"]
    bindings = set()
    nodes = [dict(n) for n in overview["nodes"] if n["kind"] == "supporting_obligation"]
    for label, title, exports, deps, statement in DEFINITIONS:
        assert set(exports) <= set(declarations)
        bindings.update(exports)
        nodes.append({"id": label, "kind": "definition", "title": title,
                      "statement_tex": statement, "depends_on": deps,
                      "lean_declarations": exports, "status": "audited"})
    for label, name in LOCAL_LEMMAS:
        assert name in declarations
        bindings.add(name)
        nodes.append({"id": label, "kind": "supporting_lemma", "depends_on": [],
                      "lean_declarations": [name], "status": "audited"})
    for entry in REFINEMENTS:
        n = dict(entry)
        n["kind"] = "refinement_lemma"
        n["lean_declarations"] = [n["lean_target"]] if n.get("lean_target") in declarations else []
        n["status"] = "audited" if n["lean_declarations"] else "pending"
        if n["lean_declarations"]:
            n["target_signature"] = declarations[n["lean_target"]]["type"]
        if n.get("target_signature"):
            n["signature_origin"] = "kernel_audit" if n["lean_declarations"] else "proposed_interface"
        elif n.get("lean_file") and n.get("lean_target"):
            proposal = root / n["lean_file"]
            if proposal.exists():
                short_name = n["lean_target"].rsplit(".", 1)[-1]
                signature = re.search(r"(?m)^theorem " + re.escape(short_name) +
                                      r"\b(.*?)\s*:=\s*by", proposal.read_text(encoding="utf-8"), re.S)
                if signature:
                    n["target_signature"] = "theorem " + short_name + signature[1]
                    n["signature_origin"] = "proposed_interface"
        bindings.update(n["lean_declarations"])
        nodes.append(n)
    mapping = {n["id"]: n for n in nodes}
    for n in nodes:
        if n["kind"] == "supporting_obligation":
            n["depends_on"] += [m["id"] for m in nodes if m.get("parent") == n["id"]]
    for n in nodes:
        # Whole-claim prerequisites of foundation gates are resolved after claims are added.
        if n["kind"] == "supporting_obligation":
            continue
        assert all(d in mapping for d in n["depends_on"])
        n["ready_to_formalize"] = n["status"] == "pending" and all(
            mapping[d]["status"] == "audited" for d in n["depends_on"])
        # A missing concrete interface remains a gap even if its mathematical prerequisites are ready.
        n["interface_specified"] = bool(n.get("target_signature") or n["status"] == "audited")
    for claim in claims:
        exports = claim["proved_declarations"]
        bindings.update(exports)
        statement = claim["statement_tex"].replace("\r\n", "\n")
        begin = manuscript.index(statement)
        tail = manuscript[begin + len(statement):]
        immediate = re.match(r"\s*(\\begin\{proof\}(?:\[[^\]]*\])?.*?\\end\{proof\})", tail, re.S)
        named = re.search(r"\\begin\{proof\}\[Proof of Theorem~\\ref\{" + re.escape(claim["id"]) +
                          r"\}\](.*?)\\end\{proof\}", manuscript, re.S)
        paper_proof = immediate[1] if immediate else (named[0] if named else None)
        nodes.append({"id": claim["id"], "kind": "manuscript_claim", "title": claim["title"],
                      "statement_tex": statement, "paper_proof_tex": paper_proof,
                      "paper_proof_is_kernel_verified": False,
                      "depends_on": claim["depends_on"] + [n["id"] for n in nodes if n.get("parent") == claim["id"]], "status": claim["status"],
                      "lean_declarations": exports, "scope_notes": claim["scope_notes"],
                      "refinement_nodes": [n["id"] for n in nodes if n.get("parent") == claim["id"]]})
    # Validate the entire mathematical dependency graph, including refinements.
    mapping = {n["id"]: n for n in nodes}
    assert len(mapping) == len(nodes), "Duplicate mathematical blueprint node"
    visiting, visited = set(), set()
    def visit(label):
        assert label in mapping, f"Unknown mathematical prerequisite: {label}"
        assert label not in visiting, f"Cyclic mathematical prerequisite: {label}"
        if label in visited:
            return
        visiting.add(label)
        for dep in mapping[label]["depends_on"]:
            visit(dep)
        visiting.remove(label)
        visited.add(label)
    for label in mapping:
        visit(label)
    selected = {name: declarations[name] for name in sorted(bindings)}
    for name, row in selected.items():
        candidates = []
        local_name = name.rsplit(".", 1)[-1]
        for module in audit["modules"]:
            path = root / module["source"]
            source_text = path.read_text(encoding="utf-8-sig")
            found = re.search(r"\b(?:theorem|lemma|def|abbrev|structure|class)\s+" + re.escape(local_name) + r"\b", source_text)
            if found:
                candidates.append({"module": module["module"], "file": module["source"],
                                   "line": source_text[:found.start()].count("\n") + 1})
        row["source_candidates"] = candidates
    result = {"purpose": "Translate the mathematical proof into a dependency graph of precise definition and lemma interfaces, expose missing arguments, and connect each established result to its actual audited Lean type.",
              "certificate": overview["certificate"], "nodes": nodes, "lean_bindings": selected,
              "active_focus": {"title": "Identity band and localized bending",
                  "construction_order": ["BP.spike.actual-speed", "BP.band.identity-period",
                      "BP.band.seed-existence", "BP.band.seed-protected-annulus", "BP.band.protected-bending",
                      "BP.band.flow-bending-pullback", "BP.band.seed-protected-bending"],
                  "scope": "Develop the band and its genuine supported bending as a self-contained part of the argument. Defer torus completion and attachment."},
              "current_ready_frontier": [n["id"] for n in nodes if n.get("ready_to_formalize") and n.get("interface_specified")],
              "readiness_rule": "A refinement is ready only if each stated smaller dependency is audited and its concrete Lean target signature is specified. This does not assert the informal proof has been checked or the theorem implemented."}
    (out / "lean-map.json").write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    macros = r"""
% Formalization annotations; these do not change the manuscript statements.
\newcommand{\uses}[1]{\par\smallskip\noindent\textbf{Dependencies:} \texttt{\detokenize{#1}}\par}
\newcommand{\lean}[1]{\par\noindent\textbf{Audited Lean declarations:} \texttt{\detokenize{#1}}\par}
\newcommand{\leanok}{\par\noindent\textbf{Complete numbered claim verified in the current audit.}\par}
\newcommand{\bpstatus}[1]{\par\noindent\textbf{Formalization status: #1.}\par}
\newcommand{\bpgap}[1]{\par\noindent\textbf{Remaining interface or argument:} #1\par\smallskip}
\newcommand{\bpstatement}[1]{\par\noindent\textbf{Mathematical interface.} #1\par}
\newcommand{\bpproof}[1]{\par\noindent\textbf{Proof sketch for formalization.} #1\par}
"""
    annotated = manuscript.replace(r"\begin{document}", macros + "\n" + r"\begin{document}", 1)
    annotated = annotated.replace(r"\maketitle", r"\maketitle" + "\n" +
        r"\section*{Formalization blueprint: how to read this document}" + "\n" +
        "This is the exact ver401 mathematical text with formalization annotations. Its informal proofs are arguments to translate, not certified Lean proofs. A complete numbered claim receives the Lean-verified marker only when the coverage and full audit certify its full scope. Partial exports keep their explicit limitations. Definitions and smaller target lemmas follow below; their statements and proof sketches guide implementation.\n", 1)
    band_focus_tex = (
        r"\section*{Current focus: the identity band and its localized bending}" + "\n" +
        "The band and bending form a self-contained construction block. First choose the actual corrected speed while retaining spatial closure and both visibility pairs. Construct its physical arclength frame and derive identity return from the same actual period balance. Next select a common embedded band with regular northern Gauss map and horizontal projection, and build a protected annulus parametrized by complete closed asymptotic leaves. Finally construct and classify genuine compactly supported infinitesimal bendings on this same band. The support statement must identify the precise band or protected subannulus in which the bending lives. Torus formation and global attachment are deferred.\n" +
        r"\uses{BP.spike.actual-speed, BP.band.identity-period, BP.band.seed-existence, BP.band.seed-protected-annulus, BP.band.protected-bending, BP.band.flow-bending-pullback, BP.band.seed-protected-bending}" + "\n" +
        r"The organizing coordinate is $J(t,u)=1/(\rho(t)u)-\Omega(t)$, with $\rho=\sqrt{|\tau|}$ and $\Omega'= (k'-k\tau'/\tau)/(2\rho)$. The exact trajectory is $U_{s,v}(t)=\rho(s)v/[\rho(t)(1+\rho(s)v(\Omega(t)-\Omega(s)))]$ and keeps $J$ constant. Choose the compact profile above both the band cutoff and $1/(\rho(s)\delta)-\Omega(s)$ to place the full bending support in the protected flow annulus. Its actual pullback gives the common opposite-branch metric $g_{\phi\pm\varepsilon Y}=g_\phi+\varepsilon^2g_Y$. Smooth immersion and distinct parametrized maps are checked; small-amplitude embedding, curvature preservation and image noncongruence are separate band-level steps." + "\n")
    annotated = annotated.replace(r"\section{Introduction}", band_focus_tex + r"\section{Introduction}", 1) if r"\section{Introduction}" in annotated else annotated.replace(r"\maketitle", r"\maketitle" + "\n" + band_focus_tex, 1)
    for claim in claims:
        statement = claim["statement_tex"].replace("\r\n", "\n")
        labels = [n["id"] for n in nodes if n.get("parent") == claim["id"]]
        metadata = r"\bpstatus{" + claim["status"] + "}\n"
        metadata += r"\uses{" + ", ".join(claim["depends_on"] + labels) + "}\n"
        if claim["proved_declarations"]:
            metadata += r"\lean{" + ", ".join(claim["proved_declarations"]) + "}\n"
        if claim["status"] == "proved":
            metadata += "\\leanok\n"
        else:
            metadata += r"\bpgap{" + text_escape(claim["remaining_work"]) + "}\n"
        annotated = annotated.replace(statement, metadata + statement, 1)
    specification = [r"\section{Definition interfaces and current refinement frontier}"]
    for n in nodes:
        if n["kind"] not in {"definition", "refinement_lemma"}:
            continue
        specification += [r"\subsection{" + text_escape(n["title"]) + "}",
                          r"\label{" + n["id"] + "}", r"\bpstatus{" + n["status"] + "}",
                          r"\uses{" + ", ".join(n["depends_on"]) + "}",
                          r"\bpstatement{" + n["statement_tex"] + "}"]
        if n.get("proof_sketch_tex"):
            specification += [r"\bpproof{" + n["proof_sketch_tex"] + "}"]
        if n["lean_declarations"]:
            specification += [r"\lean{" + ", ".join(n["lean_declarations"]) + "}"]
        if n.get("interface_gap"):
            specification += [r"\bpgap{" + text_escape(n["interface_gap"]) + "}"]
    annotated = annotated.replace(r"\end{document}", "\n\n".join(specification) + "\n" + r"\end{document}")
    assert all(annotated.count(claim["statement_tex"].replace("\r\n", "\n")) == 1 for claim in claims)
    assert annotated.count("\\leanok\n") == sum(c["status"] == "proved" for c in claims)
    (out / "mathematics.tex").write_text(annotated, encoding="utf-8")
    md = ["# Mathematical blueprint and Lean interfaces", "",
          "[mathematics.tex](mathematics.tex) contains the exact paper, its mathematical proofs and formalization annotations. [lean-map.json](lean-map.json) records exact audited Lean types and source candidates. [README.md](README.md) remains the high-level navigation guide.", "",
          "The blueprint decomposes the argument into precise, reusable statements. It exposes missing hypotheses and interfaces before implementation, and identifies the next lemmas whose prerequisites are checked. Informal proofs remain unverified until translated and audited.", "",
          "## Current focus: identity band and bending", "",
          "Treat the band and its bending as a self-contained construction block; torus formation and global attachment are deferred.", "",
          "1. Choose one corrected speed retaining actual spatial closure, holonomy balance and both visibility pairs.",
          "2. Construct that speed's physical arclength frame and the embedded identity band with regular northern Gauss map and horizontal projection.",
          "3. Construct a protected immersed embedded annulus of complete closed asymptotic leaves inside the same band.",
          "4. Construct a genuine nonzero compactly supported bending whose full support lies inside that protected annulus, and pull it back through the actual flow inclusion.",
          "5. Form the opposite perturbations: both are smooth immersions with exactly equal induced metrics, and nonzero amplitudes give distinct parametrized maps.", "",
          "The organizing coordinate is the actual characteristic invariant $J(t,u)=1/(\\rho(t)u)-\\Omega(t)$, where $\\rho=\\sqrt{|\\tau|}$ and $\\Omega$ is the actual primitive of $(k'-k\\tau'/\\tau)/(2\\rho)$.", "",
          "The exact trajectory is $U_{s,v}(t)=\\rho(s)v/[\\rho(t)(1+\\rho(s)v(\\Omega(t)-\\Omega(s)))]$. Vanishing period makes this flow periodic, and its invariant is $J(t,U_{s,v}(t))=1/(\\rho(s)v)-\\Omega(s)$.", "",
          "To protect the bending, choose its compact profile above both the original-band cutoff and the chosen initial-interval cutoff $1/(\\rho(s)\\delta)-\\Omega(s)$. The inverse trajectory places its full support inside the chosen flow annulus.", "",
          "The common branch metric is $g_{\\phi\\pm\\varepsilon Y}=g_\\phi+\\varepsilon^2g_Y$. The current band packet proves immersion and distinct parametrized maps; small-amplitude embedding, preservation of negative curvature, and image noncongruence remain separate band-level steps.", "",
          "## Ready frontier", ""]
    for label in result["current_ready_frontier"]:
        n = next(n for n in nodes if n["id"] == label)
        md += [f"- `{label}`: {n['title']}; intended file `{n['lean_file']}`."]
    md += ["", "## Definition and refinement interfaces", ""]
    for n in nodes:
        if n["kind"] not in {"definition", "refinement_lemma"}:
            continue
        md += [f"### {n['id']}: {n['title']} ({n['status']})", "",
               n["statement_tex"], "", "Dependencies: " + (", ".join(f"`{d}`" for d in n["depends_on"]) or "none") + ".", ""]
        if n.get("proof_sketch_tex"):
            md += ["**Proof sketch.** " + n["proof_sketch_tex"], ""]
        if n.get("target_signature"):
            if n.get("signature_origin") == "proposed_interface":
                md += ["**Proposed interface:** this source signature has not entered the recorded kernel audit.", ""]
            md += ["**Specified Lean interface** (its implementation status is shown above):", "",
                   "```lean", n["target_signature"], "```", ""]
        if n.get("interface_gap"):
            md += ["**Open interface.** " + n["interface_gap"], ""]
        for name in n["lean_declarations"]:
            md += [f"**Checked declaration:** `{name}`", "", "```lean", selected[name]["type"], "```", ""]
            candidates = selected[name]["source_candidates"]
            if candidates:
                md += ["Source: " + ", ".join(
                    f"[{c['module']}:{c['line']}]({(root / c['file']).as_posix()}:{c['line']})"
                    for c in candidates) + ".", ""]
    md += ["## Numbered claim registry", "", "The full statements and mathematical proof arguments are in mathematics.tex. These statuses refer to the exact ver401 claims, not to individual supporting lemmas.", "",
           "| Claim | Status | Audited source declarations |", "|---|---|---|"]
    for n in nodes:
        if n["kind"] != "manuscript_claim":
            continue
        links = []
        for name in n["lean_declarations"]:
            sources = selected[name]["source_candidates"]
            if sources:
                c = sources[0]
                links.append(f"[{name}]({(root / c['file']).as_posix()}:{c['line']})")
            else:
                links.append(f"`{name}` (exact type in lean-map.json)")
        md += [f"| `{n['id']}`: {n['title'].replace('|', '/')} | {n['status']} | {'; '.join(links) or 'Pending'} |"]
    md += [""]
    md += ["## Updating the blueprint after a proof", "",
           "Run the full audit first, then regenerate the blueprint. The audited type and source binding are recorded; a refinement leaves the ready frontier only when its target appears in that audited closure. A whole-paper claim is marked proved only through the separately reviewed coverage register."]
    (out / "interfaces.md").write_text("\n".join(md) + "\n", encoding="utf-8")
    readme = out / "README.md"
    previous = readme.read_text(encoding="utf-8")
    readme.write_text(previous.replace("# ver401 formalization blueprint", "# ver401 formalization blueprint\n\nStart with the [mathematical blueprint and precise Lean interfaces](interfaces.md). The [annotated mathematical source](mathematics.tex) retains all paper statements and proof arguments; the overview below is only navigation.", 1), encoding="utf-8")
    print(f"Mathematical blueprint: 40 exact claims; {len(REFINEMENTS)} refinement nodes; {len(selected)} audited Lean bindings.")

