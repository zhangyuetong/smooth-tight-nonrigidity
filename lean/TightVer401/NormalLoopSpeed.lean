import TightVer401.NormalLoopFrame
import OAI.Geometry.SurfaceImmersion.Primitive.PeriodicPrimitive

/-! The spatial curve is the actual OpenAI integral primitive. Its closure is
equivalent to the vector moment equation, and the physical frame equations
follow from the ordinary one-variable chain rule. -/
namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

def normalLoopMoment (a : ℝ → ℝ) (ζ E : ℝ → Ambient) (L : ℝ) : Ambient :=
  ∫ r in 0..L, a r • normalLoopP ζ E r

def normalLoopCurve (a : ℝ → ℝ) (ζ E : ℝ → Ambient) : ℝ → Ambient :=
  rawPrimitive (fun r => a r • normalLoopP ζ E r)

theorem normalLoopCurve_contDiff {a : ℝ → ℝ} {ζ E : ℝ → Ambient}
    (ha : ContDiff ℝ ∞ a) (hζ : ContDiff ℝ ∞ ζ) (hE : ContDiff ℝ ∞ E) :
    ContDiff ℝ ∞ (normalLoopCurve a ζ E) :=
  rawPrimitive_contDiff (ha.smul (normalLoopP_contDiff hζ hE))

theorem normalLoopCurve_hasDerivAt {a : ℝ → ℝ} {ζ E : ℝ → Ambient}
    (ha : Continuous a) (hζ : ContDiff ℝ ∞ ζ) (hE : ContDiff ℝ ∞ E) (r : ℝ) :
    HasDerivAt (normalLoopCurve a ζ E) (a r • normalLoopP ζ E r) r :=
  rawPrimitive_hasDerivAt (ha.smul (normalLoopP_contDiff hζ hE).continuous) r

theorem normalLoopP_periodic {ζ E : ℝ → Ambient} {L : ℝ}
    (hζ : Function.Periodic ζ L) (hE : Function.Periodic E L) :
    Function.Periodic (normalLoopP ζ E) L := by
  intro r
  simp only [normalLoopP, hζ r, hE r]

theorem normalLoopCurve_periodic_iff {a : ℝ → ℝ} {ζ E : ℝ → Ambient} {L : ℝ}
    (ha : Continuous a) (hζ : ContDiff ℝ ∞ ζ) (hE : ContDiff ℝ ∞ E)
    (haL : Function.Periodic a L) (hζL : Function.Periodic ζ L)
    (hEL : Function.Periodic E L) :
    Function.Periodic (normalLoopCurve a ζ E) L ↔ normalLoopMoment a ζ E L = 0 := by
  let f : ℝ → Ambient := fun r => a r • normalLoopP ζ E r
  have hf : Continuous f := ha.smul (normalLoopP_contDiff hζ hE).continuous
  have hfL : Function.Periodic f L := by
    intro r
    dsimp [f]
    rw [haL r, normalLoopP_periodic hζL hEL r]
  constructor
  · intro hp
    have he := hp 0
    simpa [normalLoopCurve, normalLoopMoment, rawPrimitive] using he
  · intro hmoment r
    change (∫ t in 0..r + L, f t) = ∫ t in 0..r, f t
    rw [hfL.intervalIntegral_add_eq_add 0 r (fun c d => hf.intervalIntegrable c d)]
    rw [zero_add]
    change (∫ t in 0..r, f t) + normalLoopMoment a ζ E L = _
    rw [hmoment, add_zero]

theorem normalLoop_physical_frame {ζ E A : ℝ → Ambient} {a ψ : ℝ → ℝ} {s : ℝ}
    (hζ : ∀ r, HasDerivAt ζ (E r) r) (hE : ∀ r, HasDerivAt E (A r) r)
    (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (E r) (E r) = 1)
    (hψ : HasDerivAt ψ (a (ψ s))⁻¹ s) :
    HasDerivAt (normalLoopP ζ E ∘ ψ)
      ((normalLoopKappa ζ E A (ψ s) / a (ψ s)) • E (ψ s)) s ∧
    HasDerivAt (E ∘ ψ)
      (-(normalLoopKappa ζ E A (ψ s) / a (ψ s)) • normalLoopP ζ E (ψ s) +
        (-(a (ψ s))⁻¹) • ζ (ψ s)) s ∧
    HasDerivAt (ζ ∘ ψ) ((a (ψ s))⁻¹ • E (ψ s)) s := by
  refine ⟨?_, ?_, (hζ (ψ s)).scomp s hψ⟩
  · simpa only [smul_smul, div_eq_mul_inv, mul_comm] using
      (normalLoop_derivative_P hζ hE hunit hspeed (ψ s)).scomp s hψ
  · have hd := (hE (ψ s)).scomp s hψ
    rw [normalLoop_second_derivative hζ hE hunit hspeed (ψ s)] at hd
    have heq : (a (ψ s))⁻¹ • (-ζ (ψ s) -
        normalLoopKappa ζ E A (ψ s) • normalLoopP ζ E (ψ s)) =
        -(normalLoopKappa ζ E A (ψ s) / a (ψ s)) • normalLoopP ζ E (ψ s) +
        (-(a (ψ s))⁻¹) • ζ (ψ s) := by
      simp only [div_eq_mul_inv]
      module
    rw [heq] at hd
    exact hd

end
end TightVer401
