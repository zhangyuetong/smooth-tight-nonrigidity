import TightVer401.ConcaveJetJoinLocalExtension
import TightVer401.RevolutionEndCurvature
import TightVer401.CurvatureLocality
import TightVer401.SphereCharts

/-! Local revolution geometry for the actual parabolic convex closure.

The radius profile is required to be smooth only on an open height domain U.
At each interior height, jetLocalExtension supplies a globally smooth radius
with the same genuine germ. Retained revolution immersion and curvature
theorems apply to this extension, and derivative/metric locality transfers
their conclusions back to the actual profile. No smoothness at a square-root
endpoint, normal differential regularity, Gauss injectivity, inverse, or
convex-body conclusion is an input.

The outward normal is explicitly the negative of the retained inward normal.
For U = Ioo (-h) h the resulting curvature is strictly positive whenever
the actual radius is positive and its actual second derivative is negative.
The closed annulus still requires smooth parabolic boundary parameters.
-/

namespace TightVer401
noncomputable section
open Set Filter Metric OAI.SmoothLocal.Geometry
open scoped ContDiff Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false

/-- A genuine smooth extension of the radius germ at any interior height. -/
theorem parabolicConvexClosure_profile_extension {U : Set ℝ} (hU : IsOpen U)
    {r : ℝ → ℝ} (hr : ContDiffOn ℝ ∞ r U) {z : ℝ} (hz : z ∈ U) :
    ∃ q : ℝ → ℝ, ContDiff ℝ ∞ q ∧ q =ᶠ[𝓝 z] r := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz)
  let β := momentControlBump z (δ / 2) (half_pos hδ)
  have hβ : tsupport (β : ℝ → ℝ) ⊆ U := by
    rw [β.tsupport_eq]
    intro x hx
    apply hball
    change dist x z < δ
    change dist x z ≤ δ / 2 at hx
    exact lt_of_le_of_lt hx (half_lt_self hδ)
  refine ⟨jetLocalExtension β r, jetLocalExtension_contDiff hU hr β hβ, ?_⟩
  have hzβ : z ∈ ball z β.rIn := by simp [β.rIn_pos]
  filter_upwards [isOpen_ball.mem_nhds hzβ] with x hx
  exact jetLocalExtension_eqOn β r (ball_subset_closedBall hx)

/-- Radius germ agreement gives agreement of the actual revolution maps. -/
theorem parabolicConvexClosure_revolution_germ {q r : ℝ → ℝ} {p : Coord}
    (h : q =ᶠ[𝓝 (p 1)] r) : revolutionEnd q =ᶠ[𝓝 p] revolutionEnd r := by
  filter_upwards [h.comp_tendsto (continuous_apply 1).continuousAt] with x hx
  change q (x 1) = r (x 1) at hx
  simp only [revolutionEnd, hx]

/-- Actual coordinate-map smoothness on the open height strip. -/
theorem parabolicConvexClosure_revolution_contDiffOn {U : Set ℝ} (hU : IsOpen U)
    {r : ℝ → ℝ} (hr : ContDiffOn ℝ ∞ r U) :
    ContDiffOn ℝ ∞ (revolutionEnd r) {p : Coord | p 1 ∈ U} := by
  intro p hp
  obtain ⟨q, hq, hg⟩ := parabolicConvexClosure_profile_extension hU hr hp
  exact ((revolutionEnd_contDiff hq).contDiffAt.congr_of_eventuallyEq
    (parabolicConvexClosure_revolution_germ hg).symm).contDiffWithinAt

/-- The actual revolution differential is injective wherever the radius is nonzero. -/
theorem parabolicConvexClosure_revolution_differential_injective {U : Set ℝ}
    (hU : IsOpen U) {r : ℝ → ℝ} (hr : ContDiffOn ℝ ∞ r U)
    {p : Coord} (hp : p 1 ∈ U) (hrp : r (p 1) ≠ 0) :
    Function.Injective (fderiv ℝ (revolutionEnd r) p) := by
  obtain ⟨q, hq, hg⟩ := parabolicConvexClosure_profile_extension hU hr hp
  have hmap := parabolicConvexClosure_revolution_germ hg
  rw [← hmap.fderiv_eq]
  exact revolutionEnd_differential_injective hq (by rwa [hg.self_of_nhds])

/-- The retained intrinsic curvature formula applies to the actual local profile. -/
theorem parabolicConvexClosure_revolution_gaussianCurvature {U : Set ℝ}
    (hU : IsOpen U) {r : ℝ → ℝ} (hr : ContDiffOn ℝ ∞ r U)
    {p : Coord} (hp : p 1 ∈ U) (hrp : 0 < r (p 1)) :
    gaussianCurvature (inducedMetric (revolutionEnd r)) p =
      -deriv (deriv r) (p 1) / (r (p 1) * (1 + deriv r (p 1)^2)^2) := by
  obtain ⟨q, hq, hg⟩ := parabolicConvexClosure_profile_extension hU hr hp
  have hqp : 0 < q (p 1) := by rwa [hg.self_of_nhds]
  calc
    gaussianCurvature (inducedMetric (revolutionEnd r)) p =
        gaussianCurvature (inducedMetric (revolutionEnd q)) p :=
      gaussianCurvature_eq_of_eventuallyEq
        (inducedMetric_eventuallyEq (parabolicConvexClosure_revolution_germ hg).symm)
    _ = -deriv (deriv q) (p 1) / (q (p 1) * (1 + deriv q (p 1)^2)^2) :=
      revolutionEnd_gaussianCurvature hq hqp
    _ = _ := by rw [hg.self_of_nhds, hg.deriv_eq, hg.deriv.deriv_eq]

/-- Positive curvature is derived from the actual positive radius and negative acceleration. -/
theorem parabolicConvexClosure_revolution_gaussianCurvature_pos {U : Set ℝ}
    (hU : IsOpen U) {r : ℝ → ℝ} (hr : ContDiffOn ℝ ∞ r U)
    {p : Coord} (hp : p 1 ∈ U) (hrp : 0 < r (p 1))
    (hneg : deriv (deriv r) (p 1) < 0) :
    0 < gaussianCurvature (inducedMetric (revolutionEnd r)) p := by
  rw [parabolicConvexClosure_revolution_gaussianCurvature hU hr hp hrp]
  exact div_pos (neg_pos.mpr hneg) (mul_pos hrp (sq_pos_of_pos (by positivity)))

/-- Explicit outward orientation, opposite the retained inward revolution normal. -/
def parabolicConvexClosureOutwardNormal (r : ℝ → ℝ) (p : Coord) : Ambient :=
  -revolutionEndNormal r p

theorem parabolicConvexClosureOutwardNormal_unit (r : ℝ → ℝ) (p : Coord) :
    inner ℝ (parabolicConvexClosureOutwardNormal r p)
      (parabolicConvexClosureOutwardNormal r p) = 1 := by
  simpa only [parabolicConvexClosureOutwardNormal, inner_neg_neg] using
    revolutionEndNormal_unit r p

theorem parabolicConvexClosureOutwardNormal_norm (r : ℝ → ℝ) (p : Coord) :
    ‖parabolicConvexClosureOutwardNormal r p‖ = 1 := by
  have h := parabolicConvexClosureOutwardNormal_unit r p
  rw [real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (parabolicConvexClosureOutwardNormal r p)]

/-- Actual unit-sphere value; no regularity or inverse is assumed here. -/
def parabolicConvexClosureOutwardGauss (r : ℝ → ℝ) (p : Coord) : RoundSphere :=
  ⟨parabolicConvexClosureOutwardNormal r p, by
    simpa using parabolicConvexClosureOutwardNormal_norm r p⟩

/-- Orthogonality to the actual revolution differential follows by genuine germ transport. -/
theorem parabolicConvexClosureOutwardNormal_isUnitNormal {U : Set ℝ}
    (hU : IsOpen U) {r : ℝ → ℝ} (hr : ContDiffOn ℝ ∞ r U)
    {p : Coord} (hp : p 1 ∈ U) :
    IsUnitNormalAt (revolutionEnd r) (parabolicConvexClosureOutwardNormal r p) p := by
  obtain ⟨q, hq, hg⟩ := parabolicConvexClosure_profile_extension hU hr hp
  have hmap := parabolicConvexClosure_revolution_germ hg
  have hnormal : revolutionEndNormal q p = revolutionEndNormal r p := by
    simp only [revolutionEndNormal, hg.deriv_eq]
  have hn := revolutionEnd_isUnitNormal hq p
  refine ⟨parabolicConvexClosureOutwardNormal_unit r p, ?_⟩
  intro v
  change inner ℝ (fderiv ℝ (revolutionEnd r) p v) (-revolutionEndNormal r p) = 0
  rw [← hmap.fderiv_eq, ← hnormal, inner_neg_right, hn.2 v, neg_zero]

end
end TightVer401
