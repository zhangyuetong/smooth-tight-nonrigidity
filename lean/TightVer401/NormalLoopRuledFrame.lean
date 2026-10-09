import TightVer401.NormalLoopPeriod

/-! A closed normal-loop spatial primitive supplies the actual periodic
ruled frame required by the already checked ruled-band theorem. -/
namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

theorem normalLoop_reparam_periodic {V : Type*} {F : ℝ → V} {ψ : ℝ → ℝ} {L T : ℝ}
    (hF : Function.Periodic F L) (hψ : ∀ s, ψ (s + T) = ψ s + L) :
    Function.Periodic (F ∘ ψ) T := by
  intro s
  change F (ψ (s + T)) = F (ψ s)
  rw [hψ s, hF (ψ s)]

theorem normalLoop_construct_periodic_ruled_frame {ζ : ℝ → Ambient} {a : ℝ → ℝ} {L : ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (ha : ContDiff ℝ ∞ a)
    (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1)
    (hpos : ∀ r, 0 < a r) (hζL : Function.Periodic ζ L) (haL : Function.Periodic a L)
    (hL : 0 < L) (hmoment : normalLoopMoment a ζ (deriv ζ) L = 0) :
    ∃ e : ℝ ≃ₜ ℝ, (e : ℝ → ℝ) = rawPrimitive a ∧ ContDiff ℝ ∞ e.symm ∧
      ∃ d : PeriodicRuledFrame (rawPrimitive a L),
        d.γ = normalLoopCurve a ζ (deriv ζ) ∘ e.symm ∧
        d.T = normalLoopTangent ζ ∘ e.symm ∧ d.E = deriv ζ ∘ e.symm ∧
        d.n = ζ ∘ e.symm ∧ d.k = normalLoopPhysicalK a (normalLoopCurvature ζ) e.symm ∧
        d.τ = normalLoopPhysicalTau a e.symm ∧
        (∫ s in 0..rawPrimitive a L, ruledPeriodCoefficient d.k d.τ s) =
          (1 / 2 : ℝ) * (∫ r in 0..L, deriv (normalLoopCurvature ζ) r / Real.sqrt (a r)) := by
  have hE := (contDiff_infty_iff_deriv.mp hζ).2
  have hA := (contDiff_infty_iff_deriv.mp hE).2
  have hz := (contDiff_infty_iff_deriv.mp hζ).1
  have hEd := (contDiff_infty_iff_deriv.mp hE).1
  have hEL := normalLoop_derivative_periodic hζL (fun r => (hz r).hasDerivAt)
  obtain ⟨hP, hκ⟩ := normalLoop_actual_smooth hζ
  obtain ⟨hPL, hκL⟩ := normalLoop_actual_periodic hζ hζL
  obtain ⟨e, hefun, he, hederiv, heshift, hbalance⟩ :=
    normalLoop_whole_period_balance ha hκ hpos haL hL
  have haψ := ha.comp he
  have hκψ := hκ.comp he
  have hγ := normalLoopCurve_contDiff ha hζ hE
  have hγL := (normalLoopCurve_periodic_iff ha.continuous hζ hE haL hζL hEL).mpr hmoment
  let d : PeriodicRuledFrame (rawPrimitive a L) := {
    γ := normalLoopCurve a ζ (deriv ζ) ∘ e.symm
    T := normalLoopTangent ζ ∘ e.symm
    E := deriv ζ ∘ e.symm
    n := ζ ∘ e.symm
    k := normalLoopPhysicalK a (normalLoopCurvature ζ) e.symm
    τ := normalLoopPhysicalTau a e.symm
    smooth_γ := hγ.comp he
    smooth_T := hP.comp he
    smooth_E := hE.comp he
    smooth_n := hζ.comp he
    smooth_k := hκψ.div haψ (fun s => ne_of_gt (hpos _))
    smooth_τ := (haψ.inv (fun s => ne_of_gt (hpos _))).neg
    period_γ := normalLoop_reparam_periodic hγL heshift
    period_T := normalLoop_reparam_periodic hPL heshift
    period_E := normalLoop_reparam_periodic hEL heshift
    period_n := normalLoop_reparam_periodic hζL heshift
    period_k := by
      intro s
      simp only [normalLoopPhysicalK, heshift s, hκL (e.symm s), haL (e.symm s)]
    period_τ := by
      intro s
      simp only [normalLoopPhysicalTau, heshift s, haL (e.symm s)]
    deriv_γ := fun s => normalLoop_physical_curve_hasDerivAt hζ ha.continuous
      (hpos _) (hederiv s)
    deriv_T := by
      intro s
      exact (normalLoop_physical_frame (fun r => (hz r).hasDerivAt)
        (fun r => (hEd r).hasDerivAt) hunit hspeed (hederiv s)).1
    deriv_E := by
      intro s
      exact (normalLoop_physical_frame (fun r => (hz r).hasDerivAt)
        (fun r => (hEd r).hasDerivAt) hunit hspeed (hederiv s)).2.1
    deriv_n := by
      intro s
      simpa only [normalLoopPhysicalTau, neg_neg, Function.comp_apply] using
        (normalLoop_physical_frame (fun r => (hz r).hasDerivAt)
          (fun r => (hEd r).hasDerivAt) hunit hspeed (hederiv s)).2.2
    orthonormal := fun s => (normalLoop_actual_frame hζ hunit hspeed (e.symm s)).1
    torsion_ne_zero := fun s => neg_ne_zero.mpr (inv_ne_zero (ne_of_gt (hpos _))) }
  exact ⟨e, hefun, he, d, rfl, rfl, rfl, rfl, rfl, rfl, hbalance⟩

end
end TightVer401
