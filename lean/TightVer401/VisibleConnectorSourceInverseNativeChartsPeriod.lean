import TightVer401.PeriodCircleInstances
import Mathlib.Topology.Instances.AddCircle.Defs

/-! Smooth actual change of period for the existing additive quotient atlas.
The pinned arbitrary-target quotient descent supplies both directions. -/
open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
open Function OAI.RawQuotientLie
set_option backward.isDefEq.respectTransparency false
local instance : Fact (0 < 2*Real.pi) := ⟨Real.two_pi_pos⟩

/-- The literal positive period rescaling homeomorphism. -/
def visibleConnectorSourceInverseNativePeriodRescale (L : ℝ) [hL : Fact (0 < L)] :
    AddCircle L ≃ₜ AddCircle (2*Real.pi) :=
  AddCircle.homeomorphAddCircle L (2*Real.pi) hL.out.ne' Real.two_pi_pos.ne'

theorem visibleConnectorSourceInverseNativePeriodRescale_representative
    (L s : ℝ) [hL : Fact (0 < L)] :
    visibleConnectorSourceInverseNativePeriodRescale L (periodProjection L s) =
      periodProjection (2*Real.pi) (2*Real.pi*s/L) := by
  change ((s*(L⁻¹*(2*Real.pi)) : ℝ) : AddCircle (2*Real.pi)) = _
  congr 1
  simp only [div_eq_mul_inv]
  ring

private theorem nativePeriod_homeomorph_smooth (P Q : ℝ)
    [hP : Fact (0 < P)] [hQ : Fact (0 < Q)] :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
      (AddCircle.homeomorphAddCircle P Q hP.out.ne' hQ.out.ne') := by
  have hc : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
      ((AddCircle.homeomorphAddCircle P Q hP.out.ne' hQ.out.ne') ∘ periodProjection P) := by
    have heq : (AddCircle.homeomorphAddCircle P Q hP.out.ne' hQ.out.ne') ∘ periodProjection P =
        periodProjection Q ∘ (fun s : ℝ => s*(P⁻¹*Q)) := by
      funext s
      rfl
    rw [heq]
    exact (periodProjection_contMDiff Q).comp (contDiff_id.mul contDiff_const).contMDiff
  exact addQuotient_descend_smooth (periodChart P) (periodChart_zero_target P)
    (periodProjection P) QuotientAddGroup.mk_surjective (fun x : ℝ => x) contMDiff_id rfl
    (AddCircle.homeomorphAddCircle P Q hP.out.ne' hQ.out.ne') hc

theorem visibleConnectorSourceInverseNativePeriodRescale_contMDiff
    (L : ℝ) [Fact (0 < L)] :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (visibleConnectorSourceInverseNativePeriodRescale L) :=
  nativePeriod_homeomorph_smooth L (2*Real.pi)

theorem visibleConnectorSourceInverseNativePeriodRescale_symm_contMDiff
    (L : ℝ) [hL : Fact (0 < L)] :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (visibleConnectorSourceInverseNativePeriodRescale L).symm := by
  have heq : ((visibleConnectorSourceInverseNativePeriodRescale L).symm :
      AddCircle (2*Real.pi) → AddCircle L) =
      AddCircle.homeomorphAddCircle (2*Real.pi) L Real.two_pi_pos.ne' hL.out.ne' := by
    funext q
    obtain ⟨s,rfl⟩ := QuotientAddGroup.mk_surjective q
    rfl
  rw [heq]
  exact nativePeriod_homeomorph_smooth (2*Real.pi) L

end
end TightVer401
