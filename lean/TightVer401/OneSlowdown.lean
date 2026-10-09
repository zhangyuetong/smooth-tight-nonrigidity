import TightVer401.MomentPrescriptionPeriodic
import TightVer401.PeriodicDerivativeSigns

namespace TightVer401
noncomputable section
open Set MeasureTheory
open scoped ContDiff Manifold
set_option backward.isDefEq.respectTransparency false

def oneSlowdownScalarVector (x : ℝ) : EuclideanSpace ℝ (Fin 1) := WithLp.toLp 2 (fun _ => x)

theorem oneSlowdownScalarVector_contDiff : ContDiff ℝ ∞ oneSlowdownScalarVector :=
  (contDiff_piLp 2).mpr (fun _ => contDiff_id)

theorem oneSlowdown_scalar_moment {a p : ℝ → ℝ} (ha : Continuous a) (hp : Continuous p) (L : ℝ) :
    (∫ r in 0..L, a r • oneSlowdownScalarVector (p r)) 0 = ∫ r in 0..L, a r * p r := by
  have hi := (ha.smul (oneSlowdownScalarVector_contDiff.continuous.comp hp)).intervalIntegrable (μ := volume) 0 L
  have he := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 1 => ℝ) 0).intervalIntegral_comp_comm hi
  change (∫ r in 0..L, a r * oneSlowdownScalarVector (p r) 0) =
    (∫ r in 0..L, a r • oneSlowdownScalarVector (p r)) 0 at he
  simpa [oneSlowdownScalarVector] using he.symm

/-- The scalar closing moment admits one slowdown and one compensating arc.
All integral constraints and the total arc length are actual quantities. -/
theorem one_slowdown_holonomy_correction {L η ε : ℝ} [hL : Fact (0 < L)]
    {P₃ κ b : ℝ → ℝ} (hP : ContDiff ℝ ∞ P₃) (hκ : ContDiff ℝ ∞ κ)
    (hb : ContDiff ℝ ∞ b) (hPL : Function.Periodic P₃ L) (hκL : Function.Periodic κ L)
    (hbL : Function.Periodic b L) (hbpos : ∀ r, 0 < b r)
    (_hPnonzero : ∃ r, P₃ r ≠ 0) (hκnonconstant : ∃ r, κ r ≠ κ 0)
    (hclose : (∫ r in 0..L, b r * P₃ r) = 0) (hη : 0 < η) (hε : 0 < ε) :
    ∃ a : ℝ → ℝ, ContDiff ℝ ∞ a ∧ Function.Periodic a L ∧ (∀ r, 0 < a r) ∧
      (∫ r in 0..L, ‖a r - b r‖) < η ∧ (∫ r in 0..L, a r * P₃ r) = 0 ∧
      (∫ r in 0..L, deriv κ r / Real.sqrt (a r)) = 0 ∧
      ∃ A : AddCircle L → ℝ, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ A ∧
        (∀ r, A (periodProjection L r) = a r) ∧
        ∃ n : ℕ, n ≤ 2 ∧ ∃ centers radii : Fin n → ℝ,
          (∀ j, 0 ≤ radii j) ∧ (∑ j, 2 * radii j) < ε ∧
          Function.support (fun q => A q - hbL.lift q) ⊆
            ⋃ j, periodProjection L '' Icc (centers j - radii j) (centers j + radii j) := by
  let f := oneSlowdownScalarVector ∘ P₃
  have hf : ContDiff ℝ ∞ f := oneSlowdownScalarVector_contDiff.comp hP
  have hfL : Function.Periodic f L := fun r => congrArg oneSlowdownScalarVector (hPL r)
  have hg : ContDiff ℝ ∞ (deriv κ) := (contDiff_infty_iff_deriv.mp hκ).2
  have hgL : Function.Periodic (deriv κ) L := deriv_periodic hκL
  obtain ⟨hgpos, hgneg⟩ := periodic_nonconstant_derivative_signs
    (hκ.differentiable (by simp)) hκL hL.out hκnonconstant
  let fCircle := hfL.lift
  let gCircle := hgL.lift
  let bCircle := hbL.lift
  have hfRep : fCircle ∘ periodProjection L = f := funext hfL.lift_coe
  have hgRep : gCircle ∘ periodProjection L = deriv κ := funext hgL.lift_coe
  have hbRep : bCircle ∘ periodProjection L = b := funext hbL.lift_coe
  have hfEq (r) : fCircle (periodProjection L r) = f r := congrFun hfRep r
  have hgEq (r) : gCircle (periodProjection L r) = deriv κ r := congrFun hgRep r
  have hbEq (r) : bCircle (periodProjection L r) = b r := congrFun hbRep r
  have hbCircle : ∀ q, 0 < bCircle q := by
    intro q
    obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact hbpos r
  have hgCirclePos : ∃ q, 0 < gCircle q := by
    obtain ⟨r, hr⟩ := hgpos
    exact ⟨periodProjection L r, by simpa only [hgEq] using hr⟩
  have hgCircleNeg : ∃ q, gCircle q < 0 := by
    obtain ⟨r, hr⟩ := hgneg
    exact ⟨periodProjection L r, by simpa only [hgEq] using hr⟩
  obtain ⟨A, hA, hApos, hsmall, hmoment, htarget, centers, radii, hrad, hlen, hsupp⟩ :=
    finite_moment_period_prescription L fCircle gCircle bCircle
      (periodicLift_contMDiff hf hfL).continuous (hfRep.symm ▸ hf)
      (periodicLift_contMDiff hg hgL).continuous (hbRep.symm ▸ hb)
      hbCircle hgCirclePos hgCircleNeg 0 hη hε
  let a := A ∘ periodProjection L
  have ha : ContDiff ℝ ∞ a := (hA.comp (periodProjection_contMDiff L)).contDiff
  have hM : (∫ r in 0..L, a r • f r) = ∫ r in 0..L, b r • f r := by
    simpa only [a, Function.comp_apply, hfEq, hbEq] using hmoment
  have hM0 := congrArg (fun v : EuclideanSpace ℝ (Fin 1) => v 0) hM
  change (∫ r in 0..L, a r • oneSlowdownScalarVector (P₃ r)) 0 =
    (∫ r in 0..L, b r • oneSlowdownScalarVector (P₃ r)) 0 at hM0
  rw [oneSlowdown_scalar_moment ha.continuous hP.continuous,
    oneSlowdown_scalar_moment hb.continuous hP.continuous] at hM0
  have hd : Module.finrank ℝ (circleMomentSpan L fCircle) ≤ 1 := by
    calc
      _ ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin 1)) := Submodule.finrank_le _
      _ = 1 := by simp
  refine ⟨a, ha, ?_, (fun r => hApos _), ?_, hM0.trans hclose, ?_,
    A, hA, (fun _ => rfl), Module.finrank ℝ (circleMomentSpan L fCircle) + 1,
    by omega, centers, radii, hrad, hlen, hsupp⟩
  · intro r
    change A ((r + L : ℝ) : AddCircle L) = A (r : AddCircle L)
    rw [AddCircle.coe_add_period]
  · simpa only [a, Function.comp_apply, hbEq] using hsmall
  · simpa only [a, Function.comp_apply, hgEq] using htarget

end
end TightVer401
