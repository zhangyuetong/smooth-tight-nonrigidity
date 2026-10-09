import TightVer401.NormalLoopCriterionGeometry
import TightVer401.OpenCoordinateDifferential

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry Set
open scoped ContDiff Manifold
set_option backward.isDefEq.respectTransparency false

theorem periodicRuledFrame_bandMap_immersion {T w : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T) (p : AddCircle T × Ioo (0 : ℝ) w) :
    Function.Injective (bandDifferential (d.bandMap (b := w)) p) := by
  obtain ⟨s, hs⟩ := QuotientAddGroup.mk_surjective p.1
  let q : coordinateBandOpen w := ⟨![s, (p.2 : ℝ)], p.2.property⟩
  have hq : bandFromCoordinates T w q = p := by
    apply Prod.ext hs
    exact Subtype.ext rfl
  have hX : ContDiff ℝ ∞ (ruledMap d.γ d.E) :=
    (d.smooth_γ.comp (contDiff_apply ℝ ℝ 0)).add
      ((contDiff_apply ℝ ℝ 1).smul (d.smooth_E.comp (contDiff_apply ℝ ℝ 0)))
  have hraw : openCoordinateDifferential (d.bandMap ∘ bandFromCoordinates T w) q =
      fderiv ℝ (ruledMap d.γ d.E) q.val :=
    openCoordinate_restriction_derivative q (hX.differentiable (by simp) q.val)
  have hchain : fderiv ℝ (ruledMap d.γ d.E) q.val =
      (bandDifferential d.bandMap (bandFromCoordinates T w q)).comp
        (bandFromCoordinatesDifferential T w q) := by
    rw [← hraw]
    exact mfderiv_comp q ((d.bandMap_contMDiff _).mdifferentiableAt (by simp))
      ((bandFromCoordinates_contMDiff T w q).mdifferentiableAt (by simp))
  have hinj := ruled_differential_injective (d.deriv_γ (q.val 0))
    (d.deriv_E (q.val 0)) (d.orthonormal (q.val 0)) (d.torsion_ne_zero (q.val 0))
  have hcoord : Function.Injective (bandFromCoordinatesDifferential T w q) := by
    intro v z hvz
    apply hinj
    rw [hchain]
    exact congrArg (bandDifferential d.bandMap (bandFromCoordinates T w q)) hvz
  have hsurj : Function.Surjective (bandFromCoordinatesDifferential T w q) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by simp [Coord]) (f := (bandFromCoordinatesDifferential T w q).toLinearMap)).mp hcoord
  intro v z hvz
  obtain ⟨v₀, hv₀⟩ := hsurj v
  obtain ⟨z₀, hz₀⟩ := hsurj z
  have heq : v₀ = z₀ := hinj (by
    rw [hchain]
    simp only [ContinuousLinearMap.comp_apply, hv₀, hz₀, hq]
    exact hvz)
  rw [← hv₀, ← hz₀, heq]

end
end TightVer401
