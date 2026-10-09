import TightVer401.CompletedSaddleAnnulusLegendreHeight
import TightVer401.DualRadialNeckGeometry
import TightVer401.QuadraticRadialFillingBoundaryGerms
import TightVer401.QuadraticRadialFillingExteriorCollar

/-! Actual outer neck height from the same scalar potential and actual
gradient partial homeomorphism. No boundary inverse extension or radial
completion existence is assumed or concluded. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

def completedSaddleAnnulusNeckInverseCandidate (A B : ℝ) (y : Coord) : Coord :=
  (Real.sqrt (B / (planarRadius y - A)) / planarRadius y) • y

/-- Ordinary scalar equality on the open infinity region supplies actual
ambient scalar germs; matching derivatives are not extra premises. -/
theorem completedSaddleAnnulusNeck_scalar_germ
    {G : Coord → ℝ} {A B L dInfinity : ℝ}
    (hInfinity : ∀ p : Coord, L < planarRadius p →
      G p = A * planarRadius p - B / planarRadius p + dInfinity)
    {p : Coord} (hp : L < planarRadius p) :
    G =ᶠ[𝓝 p] radialPlanarPotential (dualRadialNeckLegendreGerm A B (-dInfinity)) := by
  filter_upwards [(isOpen_lt continuous_const
    quadraticRadialFilling_radius_continuous).mem_nhds hp] with q hq
  simpa [radialPlanarPotential, dualRadialNeckLegendreGerm] using hInfinity q hq

theorem completedSaddleAnnulusNeck_gradient
    {G : Coord → ℝ} {A B L dInfinity : ℝ} (hL : 0 < L)
    (hInfinity : ∀ p : Coord, L < planarRadius p →
      G p = A * planarRadius p - B / planarRadius p + dInfinity)
    {p : Coord} (hp : L < planarRadius p) :
    planarGradient G p = ((A + B / planarRadius p ^ 2) / planarRadius p) • p := by
  have hr : 0 < planarRadius p := hL.trans hp
  have hpSq : 0 < p 0 ^ 2 + p 1 ^ 2 := by
    rw [← planarRadius_sq p]
    exact sq_pos_of_pos hr
  rw [quadraticRadialFilling_gradient_eq_of_germ
    (completedSaddleAnnulusNeck_scalar_germ hInfinity hp)]
  ext i
  change coordPartial i (radialPlanarPotential
    (dualRadialNeckLegendreGerm A B (-dInfinity))) p =
      ((A + B / planarRadius p ^ 2) / planarRadius p) * p i
  rw [radialPlanarPotential_coordPartial
    (dualRadialNeckLegendreGerm_contDiffOn A B (-dInfinity)) isOpen_Ioi
    (show p ∈ radialPlanarDomain (Ioi 0) from ⟨hpSq, hr⟩),
    dualRadialNeckLegendreGerm_deriv A B (-dInfinity) hr]
  ring

/-- The physical support height is obtained from actual scalar equality
and the derived actual gradient, including the full Cartesian dot product. -/
theorem completedSaddleAnnulusNeck_support_height
    {G : Coord → ℝ} {A B L dInfinity : ℝ} (hL : 0 < L)
    (hInfinity : ∀ p : Coord, L < planarRadius p →
      G p = A * planarRadius p - B / planarRadius p + dInfinity)
    {p : Coord} (hp : L < planarRadius p) :
    planarSupportMap G p 2 = dInfinity - 2 * B / planarRadius p := by
  have hr := hL.trans hp
  have hg := completedSaddleAnnulusNeck_gradient hL hInfinity hp
  have h0 : coordPartial 0 G p =
      ((A + B / planarRadius p ^ 2) / planarRadius p) * p 0 := congrFun hg 0
  have h1 : coordPartial 1 G p =
      ((A + B / planarRadius p ^ 2) / planarRadius p) * p 1 := congrFun hg 1
  change G p - p 0 * coordPartial 0 G p - p 1 * coordPartial 1 G p = _
  rw [hInfinity p hp, h0, h1]
  calc
    A * planarRadius p - B / planarRadius p + dInfinity -
        p 0 * (((A + B / planarRadius p ^ 2) / planarRadius p) * p 0) -
        p 1 * (((A + B / planarRadius p ^ 2) / planarRadius p) * p 1) =
        A * planarRadius p - B / planarRadius p + dInfinity -
          ((A + B / planarRadius p ^ 2) / planarRadius p) * (p 0 ^ 2 + p 1 ^ 2) := by ring
    _ = dInfinity - 2 * B / planarRadius p := by
      rw [← planarRadius_sq p]
      field_simp [hr.ne']
      <;> ring

theorem completedSaddleAnnulusNeck_inverseCandidate_radius
    {A B : ℝ} (hB : 0 < B) {y : Coord}
    (hy : 0 < planarRadius y) (hOffset : 0 < planarRadius y - A) :
    planarRadius (completedSaddleAnnulusNeckInverseCandidate A B y) =
      Real.sqrt (B / (planarRadius y - A)) := by
  have hr : 0 < Real.sqrt (B / (planarRadius y - A)) :=
    Real.sqrt_pos.mpr (div_pos hB hOffset)
  unfold completedSaddleAnnulusNeckInverseCandidate
  rw [quadraticRadialFilling_radius_smul, abs_of_pos (div_pos hr hy)]
  exact div_mul_cancel₀ _ hy.ne'

/-- The explicit small radial offset ensures the candidate lies inside
the actual infinity region, not merely inside the punctured source. -/
theorem completedSaddleAnnulusNeck_inverseCandidate_outer
    {A B L : ℝ} (hB : 0 < B) (hL : 0 < L) {y : Coord}
    (hy : 0 < planarRadius y) (hOffset : 0 < planarRadius y - A)
    (hNear : planarRadius y - A < B / L ^ 2) :
    L < planarRadius (completedSaddleAnnulusNeckInverseCandidate A B y) := by
  rw [completedSaddleAnnulusNeck_inverseCandidate_radius hB hy hOffset]
  apply (Real.lt_sqrt hL.le).mpr
  apply (lt_div_iff₀ hOffset).mpr
  have hBound := (lt_div_iff₀ (sq_pos_of_pos hL)).mp hNear
  simpa only [mul_comm] using hBound

theorem completedSaddleAnnulusNeck_sqrt_identity
    {B z : ℝ} (hB : 0 < B) (hz : 0 < z) :
    B / Real.sqrt (B / z) = Real.sqrt (B * z) := by
  have hr : 0 < Real.sqrt (B / z) := Real.sqrt_pos.mpr (div_pos hB hz)
  symm
  apply (Real.sqrt_eq_iff_eq_sq (mul_pos hB hz).le (div_pos hB hr).le).mpr
  rw [div_pow, Real.sq_sqrt (div_pos hB hz).le]
  field_simp [hB.ne', hz.ne']
  <;> ring

/-- Explicit actual inverse formula, proved from the scalar infinity
germ and the actual partial-homeomorphism inverse identities. -/
theorem completedSaddleAnnulusNeck_inverse
    {G : Coord → ℝ} (e : OpenPartialHomeomorph Coord Coord)
    {A B L dInfinity : ℝ} (hB : 0 < B) (hL : 0 < L)
    (hSource : e.source = {p : Coord | 0 < planarRadius p})
    (heG : ∀ p ∈ e.source, e p = planarGradient G p)
    (hInfinity : ∀ p : Coord, L < planarRadius p →
      G p = A * planarRadius p - B / planarRadius p + dInfinity)
    {y : Coord} (hyTarget : y ∈ e.target) (hy : 0 < planarRadius y)
    (hOffset : 0 < planarRadius y - A)
    (hNear : planarRadius y - A < B / L ^ 2) :
    e.symm y = completedSaddleAnnulusNeckInverseCandidate A B y := by
  let p := completedSaddleAnnulusNeckInverseCandidate A B y
  have hp : L < planarRadius p :=
    completedSaddleAnnulusNeck_inverseCandidate_outer hB hL hy hOffset hNear
  have hpSource : p ∈ e.source := by
    rw [hSource]
    exact hL.trans hp
  have hr : planarRadius p = Real.sqrt (B / (planarRadius y - A)) :=
    completedSaddleAnnulusNeck_inverseCandidate_radius hB hy hOffset
  have hrpos : 0 < planarRadius p := hL.trans hp
  have hrSq : planarRadius p ^ 2 = B / (planarRadius y - A) := by
    rw [hr, Real.sq_sqrt (div_pos hB hOffset).le]
  have hMagnitude : A + B / planarRadius p ^ 2 = planarRadius y := by
    rw [hrSq]
    field_simp [hB.ne', hOffset.ne']
    <;> ring
  have hg : planarGradient G p = y := by
    rw [completedSaddleAnnulusNeck_gradient hL hInfinity hp, hMagnitude]
    ext i
    change (planarRadius y / planarRadius p) *
      ((Real.sqrt (B / (planarRadius y - A)) / planarRadius y) * y i) = y i
    rw [← hr]
    field_simp [hrpos.ne', hy.ne']
  have he : e p = y := (heG p hpSource).trans hg
  calc
    e.symm y = e.symm (e p) := congrArg e.symm he.symm
    _ = p := e.left_inv hpSource

theorem completedSaddleAnnulusNeck_graph_height
    {G : Coord → ℝ} (e : OpenPartialHomeomorph Coord Coord)
    {A B L dInfinity : ℝ} (hB : 0 < B) (hL : 0 < L)
    (hSource : e.source = {p : Coord | 0 < planarRadius p})
    (heG : ∀ p ∈ e.source, e p = planarGradient G p)
    (hInfinity : ∀ p : Coord, L < planarRadius p →
      G p = A * planarRadius p - B / planarRadius p + dInfinity)
    {y : Coord} (hyTarget : y ∈ e.target) (hy : 0 < planarRadius y)
    (hOffset : 0 < planarRadius y - A)
    (hNear : planarRadius y - A < B / L ^ 2) :
    completedSaddleAnnulusGraphHeight G e y =
      dInfinity - 2 * Real.sqrt (B * (planarRadius y - A)) := by
  rw [completedSaddleAnnulusGraphHeight_support e heG hyTarget,
    completedSaddleAnnulusNeck_inverse e hB hL hSource heG hInfinity
      hyTarget hy hOffset hNear,
    completedSaddleAnnulusNeck_support_height hL hInfinity
      (completedSaddleAnnulusNeck_inverseCandidate_outer hB hL hy hOffset hNear),
    completedSaddleAnnulusNeck_inverseCandidate_radius hB hy hOffset]
  rw [show 2 * B / Real.sqrt (B / (planarRadius y - A)) =
    2 * (B / Real.sqrt (B / (planarRadius y - A))) by ring,
    completedSaddleAnnulusNeck_sqrt_identity hB hOffset]

/-- Ordinary algebraic resolved parameter identity; no inverse extension
at the boundary is asserted. -/
theorem completedSaddleAnnulusNeck_resolved_sqrt
    {B z : ℝ} (hB : 0 < B) (hz : 0 ≤ z) :
    Real.sqrt (B * z) = B * Real.sqrt (z / B) := by
  apply (Real.sqrt_eq_iff_eq_sq (mul_nonneg hB.le hz)
    (mul_nonneg hB.le (Real.sqrt_nonneg _))).mpr
  rw [mul_pow, Real.sq_sqrt (div_nonneg hz hB.le)]
  field_simp [hB.ne']
  <;> ring

theorem completedSaddleAnnulusNeck_graph_height_resolved
    {G : Coord → ℝ} (e : OpenPartialHomeomorph Coord Coord)
    {A B L dInfinity : ℝ} (hB : 0 < B) (hL : 0 < L)
    (hSource : e.source = {p : Coord | 0 < planarRadius p})
    (heG : ∀ p ∈ e.source, e p = planarGradient G p)
    (hInfinity : ∀ p : Coord, L < planarRadius p →
      G p = A * planarRadius p - B / planarRadius p + dInfinity)
    {y : Coord} (hyTarget : y ∈ e.target) (hy : 0 < planarRadius y)
    (hOffset : 0 < planarRadius y - A)
    (hNear : planarRadius y - A < B / L ^ 2) :
    completedSaddleAnnulusGraphHeight G e y =
      dInfinity - 2 * B * Real.sqrt ((planarRadius y - A) / B) := by
  rw [completedSaddleAnnulusNeck_graph_height e hB hL hSource heG hInfinity
    hyTarget hy hOffset hNear, completedSaddleAnnulusNeck_resolved_sqrt hB hOffset.le]
  ring

end
end TightVer401
