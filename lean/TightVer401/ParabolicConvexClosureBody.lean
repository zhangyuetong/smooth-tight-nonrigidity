import TightVer401.MetricBranching
import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Actual convex carrier of the ver500 radius profile, in the pinned Ambient.
The horizontal size is the genuine Complex norm of a continuous linear
projection, hence the Euclidean horizontal radius rather than a product norm.
All carrier and topological properties are proved from ordinary profile data. -/
namespace TightVer401
noncomputable section
open Set Filter Metric OAI.SmoothLocal.Geometry
open scoped Topology Pointwise
set_option backward.isDefEq.respectTransparency false

/-- Actual horizontal projection of the pinned three-dimensional Ambient. -/
def parabolicConvexClosureHorizontalCLM : Ambient →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (EuclideanSpace.proj 0) +
    Complex.I • (Complex.ofRealCLM.comp (EuclideanSpace.proj 1))

 theorem parabolicConvexClosureHorizontalCLM_apply (p : Ambient) :
    parabolicConvexClosureHorizontalCLM p = (⟨p 0, p 1⟩ : ℂ) := by
  apply Complex.ext <;> simp [parabolicConvexClosureHorizontalCLM]

 theorem parabolicConvexClosureHorizontal_norm (p : Ambient) :
    ‖parabolicConvexClosureHorizontalCLM p‖ = Real.sqrt ((p 0)^2 + (p 1)^2) := by
  rw [parabolicConvexClosureHorizontalCLM_apply, Complex.norm_def, Complex.normSq_apply]
  congr 1 <;> ring

 theorem parabolicConvexClosureHorizontal_norm_sq (p : Ambient) :
    ‖parabolicConvexClosureHorizontalCLM p‖^2 = (p 0)^2 + (p 1)^2 := by
  rw [parabolicConvexClosureHorizontalCLM_apply, Complex.sq_norm, Complex.normSq_apply]
  ring

/-- Literal closed body carrier with horizontal Euclidean radius. -/
def parabolicConvexClosureBodyCarrier (r : ℝ → ℝ) (h : ℝ) : Set Ambient :=
  {p | p 2 ∈ Icc (-h) h ∧ ‖parabolicConvexClosureHorizontalCLM p‖ ≤ r (p 2)}

/-- Actual axial/radial point, used for interior and asymmetry witnesses. -/
def parabolicConvexClosureRadialPoint (s z : ℝ) : Ambient := WithLp.toLp 2 ![s, 0, z]

@[simp] theorem parabolicConvexClosureRadialPoint_height (s z : ℝ) :
    parabolicConvexClosureRadialPoint s z 2 = z := rfl

@[simp] theorem parabolicConvexClosureRadialPoint_horizontal (s z : ℝ) :
    parabolicConvexClosureHorizontalCLM (parabolicConvexClosureRadialPoint s z) = (s : ℂ) := by
  rw [parabolicConvexClosureHorizontalCLM_apply]
  apply Complex.ext <;> rfl

/-- Convexity follows from the actual norm triangle inequality and radius concavity. -/
theorem parabolicConvexClosureBody_convex {r : ℝ → ℝ} {h : ℝ}
    (hr : ConcaveOn ℝ (Icc (-h) h) r) : Convex ℝ (parabolicConvexClosureBodyCarrier r h) := by
  intro x hx y hy a b ha hb hab
  change (a • x + b • y) 2 ∈ Icc (-h) h ∧ _
  constructor
  · exact (convex_Icc (-h) h) hx.1 hy.1 ha hb hab
  · calc
      ‖parabolicConvexClosureHorizontalCLM (a • x + b • y)‖ =
          ‖a • parabolicConvexClosureHorizontalCLM x + b • parabolicConvexClosureHorizontalCLM y‖ := by
        rw [map_add, map_smul, map_smul]
      _ ≤ ‖a • parabolicConvexClosureHorizontalCLM x‖ + ‖b • parabolicConvexClosureHorizontalCLM y‖ := norm_add_le _ _
      _ = a * ‖parabolicConvexClosureHorizontalCLM x‖ + b * ‖parabolicConvexClosureHorizontalCLM y‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      _ ≤ a * r (x 2) + b * r (y 2) :=
        add_le_add (mul_le_mul_of_nonneg_left hx.2 ha) (mul_le_mul_of_nonneg_left hy.2 hb)
      _ ≤ r ((a • x + b • y) 2) := hr.2 hx.1 hy.1 ha hb hab

/-- Closedness needs only continuity on the actual closed height interval. -/
theorem parabolicConvexClosureBody_isClosed {r : ℝ → ℝ} {h : ℝ}
    (hr : ContinuousOn r (Icc (-h) h)) : IsClosed (parabolicConvexClosureBodyCarrier r h) := by
  let Z : Ambient →L[ℝ] ℝ := EuclideanSpace.proj 2
  exact (isClosed_Icc.preimage Z.continuous).isClosed_le
    parabolicConvexClosureHorizontalCLM.continuous.norm.continuousOn
    (hr.comp Z.continuous.continuousOn (fun p hp => hp))

/-- The actual carrier is bounded in the Ambient Euclidean norm. -/
theorem parabolicConvexClosureBody_isBounded {r : ℝ → ℝ} {h : ℝ} (hh : 0 < h)
    (hr : ContinuousOn r (Icc (-h) h)) : Bornology.IsBounded (parabolicConvexClosureBodyCarrier r h) := by
  obtain ⟨C0, hC0⟩ := isCompact_Icc.exists_bound_of_continuousOn hr
  let C := max C0 0
  have hC : 0 ≤ C := le_max_right _ _
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨C + h, fun p hp => ?_⟩
  have hbound : |r (p 2)| ≤ C0 := by
    simpa only [Real.norm_eq_abs] using hC0 (p 2) hp.1
  have hH : ‖parabolicConvexClosureHorizontalCLM p‖ ≤ C :=
    hp.2.trans ((le_abs_self _).trans (hbound.trans (le_max_left _ _)))
  have hHs := (sq_le_sq₀ (norm_nonneg _) hC).mpr hH
  have hzs : (p 2)^2 ≤ h^2 := sq_le_sq' hp.1.1 hp.1.2
  have hnorm := EuclideanSpace.real_norm_sq_eq p
  simp only [Fin.sum_univ_three] at hnorm
  rw [parabolicConvexClosureHorizontal_norm_sq] at hHs
  apply (sq_le_sq₀ (norm_nonneg p) (add_nonneg hC hh.le)).mp
  nlinarith [mul_nonneg hC hh.le]

 theorem parabolicConvexClosureBody_isCompact {r : ℝ → ℝ} {h : ℝ} (hh : 0 < h)
    (hr : ContinuousOn r (Icc (-h) h)) : IsCompact (parabolicConvexClosureBodyCarrier r h) :=
  isCompact_iff_isClosed_bounded.mpr
    ⟨parabolicConvexClosureBody_isClosed hr, parabolicConvexClosureBody_isBounded hh hr⟩

/-- Every point of strictly interior height and strictly smaller horizontal
radius belongs to the actual topological interior. -/
theorem parabolicConvexClosureBody_mem_interior_of_lt {r : ℝ → ℝ} {h : ℝ}
    (hr : ContinuousOn r (Icc (-h) h)) {p : Ambient}
    (hz : p 2 ∈ Ioo (-h) h) (hp : ‖parabolicConvexClosureHorizontalCLM p‖ < r (p 2)) :
    p ∈ interior (parabolicConvexClosureBodyCarrier r h) := by
  let Z : Ambient →L[ℝ] ℝ := EuclideanSpace.proj 2
  have hrAt : ContinuousAt r (p 2) := (hr (p 2) (Ioo_subset_Icc_self hz)).continuousAt
    (Icc_mem_nhds hz.1 hz.2)
  have hrad : ∀ᶠ q : Ambient in 𝓝 p, ‖parabolicConvexClosureHorizontalCLM q‖ < r (q 2) :=
    parabolicConvexClosureHorizontalCLM.continuous.norm.continuousAt.eventually_lt
      (hrAt.comp (f := fun q : Ambient => q 2)
        (show ContinuousAt (fun q : Ambient => q 2) p from Z.continuous.continuousAt)) hp
  have hheight : ∀ᶠ q : Ambient in 𝓝 p, q 2 ∈ Ioo (-h) h :=
    Z.continuous.continuousAt.eventually (Ioo_mem_nhds hz.1 hz.2)
  apply mem_interior_iff_mem_nhds.mpr
  filter_upwards [hrad, hheight] with q hq hqz
  exact ⟨Ioo_subset_Icc_self hqz, hq.le⟩

 theorem parabolicConvexClosureBody_zero_mem_interior {r : ℝ → ℝ} {h RN : ℝ}
    (hh : 0 < h) (hRN : 0 < RN) (hr : ContinuousOn r (Icc (-h) h))
    (hp : ∀ z ∈ Ioo (-h) h, RN < r z) :
    (0 : Ambient) ∈ interior (parabolicConvexClosureBodyCarrier r h) := by
  apply parabolicConvexClosureBody_mem_interior_of_lt hr
  · simp only [PiLp.zero_apply]
    exact ⟨neg_neg_of_pos hh, hh⟩
  · simpa only [map_zero, norm_zero, PiLp.zero_apply] using
      hRN.trans (hp 0 ⟨neg_neg_of_pos hh, hh⟩)

 theorem parabolicConvexClosureBody_interior_nonempty {r : ℝ → ℝ} {h RN : ℝ}
    (hh : 0 < h) (hRN : 0 < RN) (hr : ContinuousOn r (Icc (-h) h))
    (hp : ∀ z ∈ Ioo (-h) h, RN < r z) :
    (interior (parabolicConvexClosureBodyCarrier r h)).Nonempty :=
  ⟨0, parabolicConvexClosureBody_zero_mem_interior hh hRN hr hp⟩

/-- A genuine Mathlib convex body with the literal carrier and proved nonempty interior. -/
def parabolicConvexClosureConvexBody {r : ℝ → ℝ} {h RN : ℝ}
    (hh : 0 < h) (hRN : 0 < RN) (hr : ContinuousOn r (Icc (-h) h))
    (hc : ConcaveOn ℝ (Icc (-h) h) r)
    (hp : ∀ z ∈ Ioo (-h) h, RN < r z) : ConvexBody Ambient where
  carrier := parabolicConvexClosureBodyCarrier r h
  convex' := parabolicConvexClosureBody_convex hc
  isCompact' := parabolicConvexClosureBody_isCompact hh hr
  nonempty' := (parabolicConvexClosureBody_interior_nonempty hh hRN hr hp).mono interior_subset

end
end TightVer401


