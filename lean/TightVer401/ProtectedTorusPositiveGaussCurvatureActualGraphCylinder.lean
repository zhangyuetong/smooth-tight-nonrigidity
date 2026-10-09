import TightVer401.ProtectedTorusPositiveGaussCurvatureActualGraph
import TightVer401.ProtectedTorusPositiveGaussCurvatureSeams
import TightVer401.CompletedSaddleAnnulusCylinderCurvature

/-! Consume the actual completed graph cylinder, without reconstructing
sphere-support germs or a global normal. The ordinary data below exposes
the same G, actual gradient inverse e, scalar radial parameter beta and
literal equality to S.saddle. All derivative signs and germs concern these
functions. Actual surface curvature is derived by the committed completed
cylinder proofs and transported through the explicit preferred charts.

The final classification uses precisely D.meridian. Neither a surface
curvature/sign premise nor a positive-region conclusion is an input. The
actual completed-saddle assembly owns production of these ordinary data.
-/
open scoped Manifold ContDiff Topology Matrix
namespace TightVer401
noncomputable section
open Set Filter _root_.Manifold OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false
local instance actualGraphCylinderPeriod : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- Ordinary analytic data and literal map agreement for the completed
saddle cylinder. This record contains no surface curvature conclusions. -/
structure ProtectedTorusActualGraphCylinderData {RN mu h : ℝ}
    (S : ProtectedSaddleCylinderInput RN mu h) where
  G : Coord → ℝ
  e : OpenPartialHomeomorph Coord Coord
  beta : ℝ → ℝ
  A : ℝ
  B : ℝ
  L : ℝ
  d0 : ℝ
  dInfinity : ℝ
  A_positive : 0 < A
  A_lt_RN : A < RN
  B_positive : 0 < B
  L_positive : 0 < L
  source_eq : e.source = {p : Coord | 0 < planarRadius p}
  target_eq : e.target = quadraticRadialFillingOpenAnnulus A RN
  potential_smooth : ContDiffOn ℝ ∞ G e.source
  inverse_smooth : ContDiffOn ℝ ∞ e.symm e.target
  gradient_eq : ∀ p ∈ e.source, e p = planarGradient G p
  hessian_negative : ∀ p ∈ e.source, (planarHessian G p).det < 0
  infinity_germ : ∀ p : Coord, L < planarRadius p →
    G p = A * planarRadius p - B / planarRadius p + dInfinity
  beta_smooth : ContDiff ℝ ∞ beta
  beta_strictMono : StrictMonoOn beta (Icc (Real.pi / 2) Real.pi)
  beta_neck_value : beta (Real.pi / 2) = A
  beta_boundary_value : beta Real.pi = RN
  beta_derivative_positive : ∀ u ∈ Ioo (Real.pi / 2) Real.pi, 0 < deriv beta u
  beta_neck_germ : beta =ᶠ[𝓝 (Real.pi / 2)]
    (fun u => A + B * (u - Real.pi / 2)^2)
  saddle_eq : S.saddle = completedSaddleAnnulusCylinderMap G e A RN d0 dInfinity beta

/-- Direct consumer interface for the actual completed-saddle producer.
Every premise is an ordinary scalar, potential, gradient-inverse, or literal
map field of its output tuple. Hessian negativity concerns the potential;
no surface curvature, sphere-support germ, normal or positive-region
conclusion is supplied. In particular the literal saddle is the same S.
-/
def protectedTorusActualGraphCylinderData_of_ordinary
    {RN mu h : ℝ} (S : ProtectedSaddleCylinderInput RN mu h)
    (G : Coord → ℝ) (e : OpenPartialHomeomorph Coord Coord) (beta : ℝ → ℝ)
    (A B L d0 dInfinity : ℝ)
    (hA : 0 < A) (hARN : A < RN) (hB : 0 < B) (hL : 0 < L)
    (hsource : e.source = {p : Coord | 0 < planarRadius p})
    (htarget : e.target = quadraticRadialFillingOpenAnnulus A RN)
    (hG : ContDiffOn ℝ ∞ G e.source)
    (he : ContDiffOn ℝ ∞ e.symm e.target)
    (hgradient : ∀ p ∈ e.source, e p = planarGradient G p)
    (hhessian : ∀ p ∈ e.source, (planarHessian G p).det < 0)
    (hinfinity : ∀ p : Coord, L < planarRadius p →
      G p = A * planarRadius p - B / planarRadius p + dInfinity)
    (hbeta : ContDiff ℝ ∞ beta)
    (hmono : StrictMonoOn beta (Icc (Real.pi / 2) Real.pi))
    (hneck : beta (Real.pi / 2) = A) (hboundary : beta Real.pi = RN)
    (hderiv : ∀ u ∈ Ioo (Real.pi / 2) Real.pi, 0 < deriv beta u)
    (hgerm : beta =ᶠ[𝓝 (Real.pi / 2)] (fun u => A + B * (u - Real.pi / 2)^2))
    (hsaddle : S.saddle = completedSaddleAnnulusCylinderMap G e A RN d0 dInfinity beta) :
    ProtectedTorusActualGraphCylinderData S where
  G := G
  e := e
  beta := beta
  A := A
  B := B
  L := L
  d0 := d0
  dInfinity := dInfinity
  A_positive := hA
  A_lt_RN := hARN
  B_positive := hB
  L_positive := hL
  source_eq := hsource
  target_eq := htarget
  potential_smooth := hG
  inverse_smooth := he
  gradient_eq := hgradient
  hessian_negative := hhessian
  infinity_germ := hinfinity
  beta_smooth := hbeta
  beta_strictMono := hmono
  beta_neck_value := hneck
  beta_boundary_value := hboundary
  beta_derivative_positive := hderiv
  beta_neck_germ := hgerm
  saddle_eq := hsaddle

/-- The actual preferred torus chart has negative curvature in the saddle
phase, consuming only the ordinary actual completed-cylinder data. -/
theorem protectedTorusPositiveGauss_actualCylinder_saddle_curvature_neg
    {RN mu h : ℝ} (S : ProtectedSaddleCylinderInput RN mu h)
    (d : ProtectedTorusActualGraphCylinderData S) (r : ℝ → ℝ)
    (p : NonrigidTorusSource)
    (hphase : (AddCircle.equivIco (2 * Real.pi) 0 p.2).val ∈ Ioo (0 : ℝ) Real.pi) :
    nativeTorusChartCurvature (protectedTorusMap S.saddle r h) p < 0 := by
  rw [protectedTorusPositiveGauss_saddle_chart_curvature_transport S.saddle r h p hphase,
    d.saddle_eq, ← nativeProductPlane_coordinate_curvature]
  exact completedSaddleAnnulusCylinderMap_gaussianCurvature_neg d.e
    d.A_positive d.A_lt_RN d.B_positive d.L_positive d.source_eq d.target_eq
    d.potential_smooth d.inverse_smooth d.gradient_eq d.hessian_negative d.infinity_germ
    d.beta_smooth d.beta_strictMono d.beta_neck_value d.beta_boundary_value
    d.beta_derivative_positive d.beta_neck_germ p.1 hphase

/-- For the actual completed saddle and the same constructed meridian,
positive preferred-chart curvature is exactly the genuine convex phase. -/
theorem protectedTorusPositiveGauss_actualCylinder_curvature_pos_iff
    {RN mu h : ℝ} (S : ProtectedSaddleCylinderInput RN mu h)
    (D : ParabolicConvexClosureData RN mu h)
    (d : ProtectedTorusActualGraphCylinderData S) (p : NonrigidTorusSource) :
    0 < nativeTorusChartCurvature (protectedTorusMap S.saddle D.meridian h) p ↔
      (AddCircle.equivIco (2 * Real.pi) 0 p.2).val ∈ Ioo Real.pi (2 * Real.pi) := by
  constructor
  · intro hpos
    let u := (AddCircle.equivIco (2 * Real.pi) 0 p.2).val
    have hu : u ∈ Ico (0 : ℝ) (2 * Real.pi) := by
      simpa [u] using (AddCircle.equivIco (2 * Real.pi) 0 p.2).property
    have hp : periodProjection (2 * Real.pi) u = p.2 := AddCircle.coe_equivIco
    by_cases hu0 : u = 0
    · have hp0 : p.2 = 0 := by rw [← hp, hu0]; rfl
      rw [protectedTorusPositiveGauss_south_curvature_zero S D p hp0] at hpos
      exact False.elim (lt_irrefl 0 hpos)
    by_cases huPi : u = Real.pi
    · have hpPi : p.2 = periodProjection (2 * Real.pi) Real.pi := by rw [← hp, huPi]
      rw [protectedTorusPositiveGauss_north_curvature_zero S D p hpPi] at hpos
      exact False.elim (lt_irrefl 0 hpos)
    by_cases hup : u < Real.pi
    · have hneg := protectedTorusPositiveGauss_actualCylinder_saddle_curvature_neg
        S d D.meridian p
        (show u ∈ Ioo (0 : ℝ) Real.pi from ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0), hup⟩)
      exact False.elim (not_lt_of_ge hneg.le hpos)
    · exact ⟨lt_of_le_of_ne (le_of_not_gt hup) (Ne.symm huPi), hu.2⟩
  · exact protectedTorusPositiveGauss_convex_curvature_pos S D p

/-- The actual positive-curvature region, without a sphere-support germ
producer assumption. The consumer still needs the actual ordinary saddle
data, whose completed construction belongs to smoothing. -/
theorem protectedTorusPositiveGauss_actualCylinder_region_eq
    {RN mu h : ℝ} (S : ProtectedSaddleCylinderInput RN mu h)
    (D : ParabolicConvexClosureData RN mu h)
    (d : ProtectedTorusActualGraphCylinderData S) :
    nativeTorusPositiveRegion (protectedTorusMap S.saddle D.meridian h) =
      {p | (AddCircle.equivIco (2 * Real.pi) 0 p.2).val ∈ Ioo Real.pi (2 * Real.pi)} := by
  ext p
  exact protectedTorusPositiveGauss_actualCylinder_curvature_pos_iff S D d p

end
end TightVer401
