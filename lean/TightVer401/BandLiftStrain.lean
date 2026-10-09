import TightVer401.OpenCoordinateDifferential
import TightVer401.BandLiftSupport

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Manifold
set_option backward.isDefEq.respectTransparency false

theorem bandCoordinateLift_strain_in_band {L b : ℝ} [Fact (0 < L)]
    (d : PeriodicRuledFrame L) {Y : AddCircle L × Ioo (0 : ℝ) b → Ambient}
    (hY : IsBandBending (d.bandMap (b := b)) Y) {p : Coord} (hp : p 1 ∈ Ioo 0 b)
    (i j : Fin 2) : strain (ruledMap d.γ d.E) (bandCoordinateLift Y) p i j = 0 := by
  let q : coordinateBandOpen b := ⟨p, hp⟩
  let r := bandFromCoordinates L b q
  have hσ := (bandFromCoordinates_contMDiff L b q).mdifferentiableAt (by simp)
  have hxchain : openCoordinateDifferential (d.bandMap ∘ bandFromCoordinates L b) q =
      (bandDifferential d.bandMap r).comp (bandFromCoordinatesDifferential L b q) :=
    mfderiv_comp q ((d.bandMap_contMDiff r).mdifferentiableAt (by simp)) hσ
  have hychain : openCoordinateDifferential (Y ∘ bandFromCoordinates L b) q =
      (bandDifferential Y r).comp (bandFromCoordinatesDifferential L b q) :=
    mfderiv_comp q ((hY.1 r).mdifferentiableAt (by simp)) hσ
  have hxraw : ContDiff ℝ ∞ (ruledMap d.γ d.E) :=
    (d.smooth_γ.comp (contDiff_apply ℝ ℝ 0)).add
      ((contDiff_apply ℝ ℝ 1).smul (d.smooth_E.comp (contDiff_apply ℝ ℝ 0)))
  have hyraw : DifferentiableAt ℝ (bandCoordinateLift Y) p :=
    ((bandCoordinateLift_contDiffOn hY.1 p hp).contDiffAt
      ((isOpen_Ioo.preimage (continuous_apply 1)).mem_nhds hp)).differentiableAt (by simp)
  have hxrestrict : openCoordinateDifferential (d.bandMap ∘ bandFromCoordinates L b) q =
      fderiv ℝ (ruledMap d.γ d.E) p :=
    openCoordinate_restriction_derivative q (hxraw.differentiable (by simp) p)
  have he : Y ∘ bandFromCoordinates L b =
      (fun q : coordinateBandOpen b => bandCoordinateLift Y q.val) := by
    funext q
    have hq : q.val 1 ∈ Ioo 0 b := q.property
    rw [bandCoordinateLift, dif_pos hq]
    rfl
  have hyrestrict : openCoordinateDifferential (Y ∘ bandFromCoordinates L b) q =
      fderiv ℝ (bandCoordinateLift Y) p := by
    rw [he]
    exact openCoordinate_restriction_derivative q hyraw
  have hx := hxrestrict.symm.trans hxchain
  have hy := hyrestrict.symm.trans hychain
  simp only [strain, coordPartial, hx, hy, ContinuousLinearMap.comp_apply]
  exact hY.2 r ((bandFromCoordinatesDifferential L b q) (Pi.single i 1))
    ((bandFromCoordinatesDifferential L b q) (Pi.single j 1))

theorem bandCoordinateLift_zero_strain {L b lower upper : ℝ} [Fact (0 < L)]
    (d : PeriodicRuledFrame L) {Y : AddCircle L × Ioo (0 : ℝ) b → Ambient}
    (hY : IsBandBending (d.bandMap (b := b)) Y) (hlower : 0 < lower) (hupper : upper < b)
    (hsupport : ∀ p ∈ tsupport Y, lower ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ upper)
    (p : Coord) (i j : Fin 2) : strain (ruledMap d.γ d.E) (bandCoordinateLift Y) p i j = 0 := by
  by_cases hp : p 1 ∈ Ioo 0 b
  · exact bandCoordinateLift_strain_in_band d hY hp i j
  · have hz := coordinateBandExtension_eventually_zero hlower hupper
      (fun q _ hq => bandCoordinateLift_zero_outside_bounds hsupport q hq) hp
    have he : coordinateBandExtension b (bandCoordinateLift Y) = bandCoordinateLift Y := by
      funext q
      by_cases hq : q 1 ∈ Ioo 0 b <;>
        simp only [coordinateBandExtension, bandCoordinateLift, hq, if_true, if_false, dite_true, dite_false]
    rw [he] at hz
    have hd : fderiv ℝ (bandCoordinateLift Y) p = fderiv ℝ (fun _ : Coord => (0 : Ambient)) p := hz.fderiv_eq
    have hc : fderiv ℝ (fun _ : Coord => (0 : Ambient)) p = 0 :=
      (hasFDerivAt_const (c := (0 : Ambient)) p).fderiv
    simp only [strain, coordPartial, hd, hc, zero_apply, inner_zero_left, inner_zero_right, add_zero]

end
end TightVer401
