import TightVer401.ScalarReturnDynamicalControl

namespace TightVer401
noncomputable section
open Filter
open scoped Topology

theorem scalarReturn_expansion_iterates_leave {R : ℝ → ℝ} {e q x : ℝ}
    (hq : 1 < q) (hx : x ≠ 0)
    (hbound : ∀ y : ℝ, y ≠ 0 → |y| < e → q * |y| < |R y|) :
    ∃ n : ℕ, e ≤ |(R^[n]) x| := by
  by_contra hn
  have hsmall (n : ℕ) : |(R^[n]) x| < e :=
    lt_of_not_ge (fun h => hn ⟨n,h⟩)
  have hi : ∀ n : ℕ, q^n * |x| ≤ |(R^[n]) x| := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hp : 0 < q^n * |x| :=
        mul_pos (pow_pos (lt_trans zero_lt_one hq) n) (abs_pos.mpr hx)
      have hne : (R^[n]) x ≠ 0 := abs_pos.mp (hp.trans_le ih)
      rw [Function.iterate_succ_apply']
      have he := (mul_le_mul_of_nonneg_left ih (lt_trans zero_lt_one hq).le).trans
        (hbound _ hne (hsmall n)).le
      simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm] using he
  have ht : Tendsto (fun n : ℕ => q^n * |x|) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hq).atTop_mul_const (abs_pos.mpr hx)
  obtain ⟨n, hlarge⟩ := (ht.eventually (eventually_gt_atTop e)).exists
  exact (not_lt_of_ge (hi n)) (lt_trans (hsmall n) hlarge)

theorem scalarReturn_repels {R : ℝ → ℝ} {μ : ℝ}
    (hd : HasDerivAt R μ 0) (hzero : R 0 = 0) (hμ : 1 < μ) :
    ∃ e > 0, ∀ x : ℝ, x ≠ 0 → |x| < e → ∃ n : ℕ, e ≤ |(R^[n]) x| := by
  obtain ⟨e,q,he,hq,hbound⟩ := scalarReturn_exists_expansion hd hzero hμ
  exact ⟨e,he,fun x hx _ => scalarReturn_expansion_iterates_leave hq hx
    (fun y hy hye => (hbound y hy hye).1)⟩

end
end TightVer401
