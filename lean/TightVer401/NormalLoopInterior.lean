import TightVer401.NormalLoopAffineSpan
import TightVer401.NormalLoopSeparation
import Mathlib.Analysis.LocallyConvex.Separation

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry Set
open scoped ContDiff

theorem normalLoop_closure_convex_interior {ζ : ℝ → Ambient} {a : ℝ → ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (ha : Continuous a)
    (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1)
    (hpos : ∀ r, 0 < a r) {L : ℝ} (hL : 0 < L)
    (hζL : Function.Periodic ζ L)
    (hmoment : normalLoopMoment a ζ (deriv ζ) L = 0) :
    (0 : Ambient) ∈ interior (convexHull ℝ (range (normalLoopTangent ζ))) := by
  have hspan := normalLoop_closure_affineSpan_eq_top hζ ha hunit hspeed hpos hL hmoment
  have hnonempty := interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr hspan
  by_contra hout
  obtain ⟨f, hf, hsep⟩ := geometric_hahn_banach_of_nonempty_interior_point
    (convex_convexHull ℝ (range (normalLoopTangent ζ))) hout hnonempty
  let v := (InnerProductSpace.toDual ℝ Ambient).symm f
  have hpair (r : ℝ) : inner ℝ v (normalLoopTangent ζ r) = f (normalLoopTangent ζ r) :=
    InnerProductSpace.toDual_symm_apply
  have hnonpos (r : ℝ) : inner ℝ v (normalLoopTangent ζ r) ≤ 0 := by
    rw [hpair]
    simpa only [map_zero] using hsep _ (subset_convexHull ℝ _ (mem_range_self r))
  have hnonneg (r : ℝ) : 0 ≤ inner ℝ (-v) (normalLoopTangent ζ r) := by
    rw [inner_neg_left]
    exact neg_nonneg.mpr (hnonpos r)
  have hvzero := normalLoop_closure_annihilator_eq_zero hζ ha hunit hspeed hpos hL hmoment
    (normalLoop_closure_halfspace_eq_zero hζ ha hpos hL hζL hmoment hnonneg)
  have hv : v = 0 := neg_eq_zero.mp hvzero
  apply hf
  have he := (InnerProductSpace.toDual ℝ Ambient).apply_symm_apply f
  change (InnerProductSpace.toDual ℝ Ambient) v = f at he
  rw [hv, map_zero] at he
  exact he.symm

end
end TightVer401
