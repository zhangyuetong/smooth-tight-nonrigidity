import TightVer401.FermiSupportRegularity
import TightVer401.FermiSeamMultiplier
import TightVer401.FermiPeriodicity
import TightVer401.FermiAsymptoticSlope

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Matrix
set_option backward.isDefEq.respectTransparency false

def fermiSeamMixed (κ : ℝ → ℝ) (H : Coord → ℝ) (r : ℝ) := fermiSupportM κ H ![r,0]
def fermiSeamNormal (H : Coord → ℝ) (r : ℝ) := fermiSupportN H ![r,0]

theorem fermiScalar_derivative_periodic {a : ℝ → ℝ} {L : ℝ}
    (ha : ContDiff ℝ ∞ a) (haL : Function.Periodic a L) : Function.Periodic (deriv a) L := by
  have he : (a ∘ (fun r => r + L)) = a := funext haL
  intro r
  have hd := (ha.differentiable (by simp) (r + L)).hasDerivAt.scomp r
    ((hasDerivAt_id r).add_const L)
  change HasDerivAt (a ∘ (fun r => r + L)) (1 • deriv a (r + L)) r at hd
  rw [he] at hd
  simpa using hd.unique (ha.differentiable (by simp) r).hasDerivAt

theorem fermiSeamSlopeCoefficient_periodic {a κ c : ℝ → ℝ} {L : ℝ}
    (ha : ContDiff ℝ ∞ a) (haL : Function.Periodic a L)
    (hκL : Function.Periodic κ L) (hcL : Function.Periodic c L) :
    Function.Periodic (fermiSeamSlopeCoefficient a κ c) L := by
  have hd := fermiScalar_derivative_periodic ha haL
  intro r
  simp only [fermiSeamSlopeCoefficient, hd r, haL r, hκL r, hcL r]

theorem fermiSeam_coefficients_smooth {κ : ℝ → ℝ} {H : Coord → ℝ} {U : Set Coord}
    (hκ : ContDiff ℝ ∞ κ) (hU : IsOpen U) (hH : ContDiffOn ℝ ∞ H U)
    (hscale : ∀ p ∈ U, fermiNormalScale κ p ≠ 0)
    (hseam : ∀ r : ℝ, (![r,0] : Coord) ∈ U) :
    ContDiff ℝ ∞ (fermiSeamMixed κ H) ∧ ContDiff ℝ ∞ (fermiSeamNormal H) := by
  have hc := fermiSupport_contDiffOn hκ hU hH hscale
  exact ⟨fermiSupport_seam_contDiff hU hc.2.1 hseam,
    fermiSupport_seam_contDiff hU hc.2.2 hseam⟩

theorem fermiSeam_coefficients_periodic {κ : ℝ → ℝ} {H : Coord → ℝ} {L : ℝ}
    (hκ : Function.Periodic κ L) (hH : FermiPeriodic L H) :
    Function.Periodic (fermiSeamMixed κ H) L ∧ Function.Periodic (fermiSeamNormal H) L := by
  have hc := fermiSupport_periodic hκ hH
  exact ⟨(fermiPeriodic_iff_slices L _).mp hc.2.1 0,
    (fermiPeriodic_iff_slices L _).mp hc.2.2 0⟩

theorem fermiSupport_local_seam_slope_coefficient {κ : ℝ → ℝ} {H : Coord → ℝ}
    {U : Set Coord} (hκ : ContDiff ℝ ∞ κ) (hU : IsOpen U)
    (hH : ContDiffOn ℝ ∞ H U) (hscale : ∀ p ∈ U, fermiNormalScale κ p ≠ 0)
    {r : ℝ} (hr : (![r,0] : Coord) ∈ U) (hzero : fermiSupportL κ H ![r,0] = 0)
    (hpos : 0 < fermiSeamMixed κ H r) :
    coordPartial 1 (fermiSupportL κ H) ![r,0] =
      -2 * fermiSeamMixed κ H r *
        fermiSeamSlopeCoefficient (fermiSeamMixed κ H) κ (fermiSeamNormal H) r ∧
    coordPartial 1 (fermiAsymptoticSlope (fermiSupportL κ H)
      (fermiSupportM κ H) (fermiSupportN H)) ![r,0] =
        fermiSeamSlopeCoefficient (fermiSeamMixed κ H) κ (fermiSeamNormal H) r := by
  have hc := fermiSupport_contDiffOn hκ hU hH hscale
  have hd := fermiSupport_seam_hasDerivAt hU hc.2.1 hr
  have hda : deriv (fermiSeamMixed κ H) r = coordPartial 0 (fermiSupportM κ H) ![r,0] := hd.deriv
  have hlt := fermiSupport_local_seam_codazzi hκ hU hH hr
  rw [hzero, mul_zero, add_zero, ← hda] at hlt
  have hs : coordPartial 1 (fermiSupportL κ H) ![r,0] =
      -2 * fermiSeamMixed κ H r *
        fermiSeamSlopeCoefficient (fermiSeamMixed κ H) κ (fermiSeamNormal H) r := by
    rw [hlt]
    change deriv (fermiSeamMixed κ H) r + κ r * fermiSeamNormal H r = _
    unfold fermiSeamSlopeCoefficient
    field_simp [hpos.ne']
    <;> ring
  refine ⟨hs, ?_⟩
  have dh (F : Coord → ℝ) (hF : ContDiffOn ℝ ∞ F U) :=
    ((hF _ hr).contDiffAt (hU.mem_nhds hr)).differentiableAt (by simp)
  rw [(fermiAsymptoticSlope_seam (dh _ hc.1) (dh _ hc.2.1) (dh _ hc.2.2)
    hzero hpos 1).2, hs]
  change -(-2 * fermiSeamMixed κ H r *
    fermiSeamSlopeCoefficient (fermiSeamMixed κ H) κ (fermiSeamNormal H) r) /
      (2 * fermiSeamMixed κ H r) = _
  field_simp [hpos.ne']
  <;> ring

end
end TightVer401
