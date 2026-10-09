import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! A smooth increasing periodic phase lift has an actual smooth periodic inverse. -/
namespace TightVer401
noncomputable section
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

/-- Positive phase drift makes the continuous increasing lift surjective;
this does not assume an inverse or its range. -/
theorem dualRadialCompletion_phase_surjective {theta : ℝ → ℝ} {L : ℝ}
    (hTheta : Continuous theta) (hMono : StrictMono theta) (hL : 0 < L)
    (hShift : ∀ s, theta (s + L) = theta s + 2 * Real.pi) :
    Function.Surjective theta := by
  have hT : 0 < 2 * Real.pi := by
    have h := hMono hL
    rw [show L = 0 + L by simp, hShift 0] at h
    linarith
  have hnat : ∀ n : ℕ, ∀ s : ℝ,
      theta (s + (n : ℝ) * L) = theta s + (n : ℝ) * (2 * Real.pi) := by
    intro n
    induction n with
    | zero => intro s; simp
    | succ n ih =>
      intro s
      rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, ← add_assoc, hShift, ih]
      ring
  intro y
  obtain ⟨n, hn⟩ := exists_nat_gt (|y - theta 0| / (2 * Real.pi))
  have habs : |y - theta 0| < (n : ℝ) * (2 * Real.pi) :=
    (div_lt_iff₀ hT).mp hn
  have hupper : theta ((n : ℝ) * L) = theta 0 + (n : ℝ) * (2 * Real.pi) := by
    simpa only [zero_add] using hnat n 0
  have hnegative := hnat n (-((n : ℝ) * L))
  rw [neg_add_cancel] at hnegative
  have hlower : theta (-((n : ℝ) * L)) = theta 0 - (n : ℝ) * (2 * Real.pi) := by
    linarith
  apply intermediate_value_univ (-((n : ℝ) * L)) ((n : ℝ) * L) hTheta
  rw [hlower, hupper]
  exact ⟨by linarith [neg_abs_le (y - theta 0)],
    by linarith [le_abs_self (y - theta 0)]⟩

/-- Construct the actual inverse of the smooth positive phase lift. Its
smoothness, derivative and periodic shift are consequences, not inputs. -/
theorem exists_dualRadialCompletion_phase_inverse {theta : ℝ → ℝ} {L : ℝ}
    (hTheta : ContDiff ℝ ∞ theta) (hDeriv : ∀ s, 0 < deriv theta s) (hL : 0 < L)
    (hShift : ∀ s, theta (s + L) = theta s + 2 * Real.pi) :
    ∃ e : ℝ ≃ₜ ℝ, (e : ℝ → ℝ) = theta ∧ ContDiff ℝ ∞ e.symm ∧
      (∀ t, HasDerivAt e.symm (deriv theta (e.symm t))⁻¹ t) ∧
      (∀ t, theta (e.symm t) = t) ∧ (∀ s, e.symm (theta s) = s) ∧
      ∀ t, e.symm (t + 2 * Real.pi) = e.symm t + L := by
  have hMono : StrictMono theta := strictMono_of_deriv_pos hDeriv
  let e := (StrictMono.orderIsoOfSurjective theta hMono
    (dualRadialCompletion_phase_surjective hTheta.continuous hMono hL hShift)).toHomeomorph
  have hefun : (e : ℝ → ℝ) = theta := rfl
  have htheta (s : ℝ) : HasDerivAt theta (deriv theta s) s :=
    (hTheta.differentiable (by simp) s).hasDerivAt
  refine ⟨e, hefun, ?_, ?_, ?_, ?_, ?_⟩
  · apply contDiff_iff_contDiffAt.mpr
    intro t
    let F := e.toOpenPartialHomeomorph
    have hd := (htheta (e.symm t)).hasFDerivAt_equiv (ne_of_gt (hDeriv (e.symm t)))
    exact F.contDiffAt_symm (by simp [F])
      (f₀' := ContinuousLinearEquiv.unitsEquivAut ℝ
        (Units.mk0 (deriv theta (e.symm t)) (ne_of_gt (hDeriv (e.symm t)))))
      (by change HasFDerivAt e _ _; rw [hefun]; exact hd)
      (by change ContDiffAt ℝ ∞ e _; rw [hefun]; exact hTheta.contDiffAt)
  · intro t
    exact (htheta (e.symm t)).of_local_left_inverse e.symm.continuous.continuousAt
      (ne_of_gt (hDeriv (e.symm t)))
      (Filter.Eventually.of_forall (fun y => by rw [← hefun]; exact e.apply_symm_apply y))
  · intro t
    rw [← hefun]
    exact e.apply_symm_apply t
  · intro s
    rw [← hefun]
    exact e.symm_apply_apply s
  · intro t
    apply e.injective
    rw [e.apply_symm_apply, hefun, hShift, ← hefun, e.apply_symm_apply]

end
end TightVer401
