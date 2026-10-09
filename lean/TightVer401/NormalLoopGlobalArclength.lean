import TightVer401.NormalLoopBalanceIntegral
import Mathlib.Topology.Order.MonotoneContinuity

/-! A positive periodic speed determines a global smooth arclength
coordinate, with a derived periodic inverse. -/
namespace TightVer401
noncomputable section
open OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

theorem normalLoop_arclength_shift {a : ℝ → ℝ} {L : ℝ}
    (ha : Continuous a) (hperiod : Function.Periodic a L) (r : ℝ) :
    rawPrimitive a (r + L) = rawPrimitive a r + rawPrimitive a L := by
  unfold rawPrimitive
  rw [hperiod.intervalIntegral_add_eq_add 0 r (fun c d => ha.intervalIntegrable c d)]
  rw [zero_add]

theorem normalLoop_arclength_strictMono {a : ℝ → ℝ}
    (ha : Continuous a) (hpos : ∀ r, 0 < a r) : StrictMono (rawPrimitive a) := by
  apply strictMono_of_deriv_pos
  intro r
  rw [(rawPrimitive_hasDerivAt ha r).deriv]
  exact hpos r

theorem normalLoop_arclength_period_pos {a : ℝ → ℝ} {L : ℝ}
    (ha : Continuous a) (hpos : ∀ r, 0 < a r) (hL : 0 < L) : 0 < rawPrimitive a L := by
  have h := normalLoop_arclength_strictMono ha hpos hL
  simpa [rawPrimitive] using h

theorem normalLoop_arclength_surjective {a : ℝ → ℝ} {L : ℝ}
    (ha : ContDiff ℝ ∞ a) (hpos : ∀ r, 0 < a r)
    (hperiod : Function.Periodic a L) (hL : 0 < L) :
    Function.Surjective (rawPrimitive a) := by
  let T := rawPrimitive a L
  have hT : 0 < T := normalLoop_arclength_period_pos ha.continuous hpos hL
  have hz : rawPrimitive a 0 = 0 := by simp [rawPrimitive]
  have hnat : ∀ n : ℕ, ∀ r : ℝ,
      rawPrimitive a (r + (n : ℝ) * L) = rawPrimitive a r + (n : ℝ) * T := by
    intro n
    induction n with
    | zero => intro r; simp
    | succ n ih =>
      intro r
      rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, ← add_assoc,
        normalLoop_arclength_shift ha.continuous hperiod, ih]
      dsimp [T]
      ring
  intro y
  obtain ⟨n, hn⟩ := exists_nat_gt (|y| / T)
  have habs : |y| < (n : ℝ) * T := (div_lt_iff₀ hT).mp hn
  have hupper : rawPrimitive a ((n : ℝ) * L) = (n : ℝ) * T := by
    simpa only [zero_add, hz] using hnat n 0
  have hnegative := hnat n (-((n : ℝ) * L))
  rw [neg_add_cancel, hz] at hnegative
  have hlower : rawPrimitive a (-((n : ℝ) * L)) = -((n : ℝ) * T) := by linarith
  apply intermediate_value_univ (-((n : ℝ) * L)) ((n : ℝ) * L)
    (rawPrimitive_contDiff ha).continuous
  rw [hlower, hupper]
  exact ⟨by linarith [neg_abs_le y], by linarith [le_abs_self y]⟩

theorem normalLoop_exists_global_arclength_inverse {a : ℝ → ℝ} {L : ℝ}
    (ha : ContDiff ℝ ∞ a) (hpos : ∀ r, 0 < a r)
    (hperiod : Function.Periodic a L) (hL : 0 < L) :
    ∃ e : ℝ ≃ₜ ℝ, (e : ℝ → ℝ) = rawPrimitive a ∧ ContDiff ℝ ∞ e.symm ∧
      (∀ s, HasDerivAt e.symm (a (e.symm s))⁻¹ s) ∧
      (∀ s, e.symm (s + rawPrimitive a L) = e.symm s + L) := by
  let e := (StrictMono.orderIsoOfSurjective (rawPrimitive a)
    (normalLoop_arclength_strictMono ha.continuous hpos)
    (normalLoop_arclength_surjective ha hpos hperiod hL)).toHomeomorph
  have hefun : (e : ℝ → ℝ) = rawPrimitive a := rfl
  have hf := rawPrimitive_contDiff ha
  refine ⟨e, hefun, ?_, ?_, ?_⟩
  · apply contDiff_iff_contDiffAt.mpr
    intro s
    let F := e.toOpenPartialHomeomorph
    have hd := (rawPrimitive_hasDerivAt ha.continuous (e.symm s)).hasFDerivAt_equiv
      (ne_of_gt (hpos (e.symm s)))
    exact F.contDiffAt_symm (by simp [F])
      (f₀' := ContinuousLinearEquiv.unitsEquivAut ℝ
        (Units.mk0 (a (e.symm s)) (ne_of_gt (hpos (e.symm s)))))
      (by change HasFDerivAt e _ _; rw [hefun]; exact hd)
      (by change ContDiffAt ℝ ∞ e _; rw [hefun]; exact hf.contDiffAt)
  · intro s
    exact (rawPrimitive_hasDerivAt ha.continuous (e.symm s)).of_local_left_inverse
      e.symm.continuous.continuousAt (ne_of_gt (hpos (e.symm s)))
      (Filter.Eventually.of_forall (fun y => by rw [← hefun]; exact e.apply_symm_apply y))
  · intro s
    apply e.injective
    rw [e.apply_symm_apply, hefun, normalLoop_arclength_shift ha.continuous hperiod]
    rw [← hefun, e.apply_symm_apply]

end
end TightVer401
