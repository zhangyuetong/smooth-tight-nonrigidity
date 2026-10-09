import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic

namespace TightVer401
noncomputable section
open Set Metric
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

def scalarCellPrefix (φ : ℕ → ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => id
  | n + 1 => φ n ∘ scalarCellPrefix φ n

theorem scalarCellPrefix_zero {φ : ℕ → ℝ → ℝ} {N : ℕ}
    (hz : ∀ j < N, φ j 0 = 0) : ∀ n ≤ N, scalarCellPrefix φ n 0 = 0 := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    rw [scalarCellPrefix, Function.comp_apply, ih (Nat.le_of_succ_le hn)]
    exact hz n (Nat.lt_of_succ_le hn)

theorem scalarCellComposition_exists_common_open {φ : ℕ → ℝ → ℝ} {U : ℕ → Set ℝ} {N : ℕ}
    (hU : ∀ j < N, IsOpen (U j)) (h0 : ∀ j < N, (0 : ℝ) ∈ U j)
    (hφ : ∀ j < N, ContDiffOn ℝ ∞ (φ j) (U j)) (hz : ∀ j < N, φ j 0 = 0) :
    ∃ V : Set ℝ, IsOpen V ∧ (0 : ℝ) ∈ V ∧
      (∀ n ≤ N, ContDiffOn ℝ ∞ (scalarCellPrefix φ n) V) ∧
      ∀ j < N, MapsTo (scalarCellPrefix φ j) V (U j) := by
  have hezero := scalarCellPrefix_zero hz
  have aux : ∀ n ≤ N, ∃ V : Set ℝ, IsOpen V ∧ (0 : ℝ) ∈ V ∧
      (∀ j ≤ n, ContDiffOn ℝ ∞ (scalarCellPrefix φ j) V) ∧
      ∀ j < n, MapsTo (scalarCellPrefix φ j) V (U j) := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨univ,isOpen_univ,mem_univ _,?_,?_⟩
      · intro j hj
        have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
        subst j
        exact contDiff_id.contDiffOn
      · intro j hj
        exact (Nat.not_lt_zero j hj).elim
    | succ n ih =>
      intro hn
      obtain ⟨V,hV,hV0,hsm,hmap⟩ := ih (Nat.le_of_succ_le hn)
      have hnN : n < N := Nat.lt_of_succ_le hn
      let W := V ∩ (scalarCellPrefix φ n) ⁻¹' U n
      have hW : IsOpen W := (hsm n le_rfl).continuousOn.isOpen_inter_preimage hV (hU n hnN)
      have hW0 : (0 : ℝ) ∈ W := ⟨hV0, by
        change scalarCellPrefix φ n 0 ∈ U n
        rw [hezero n (Nat.le_of_succ_le hn)]
        exact h0 n hnN⟩
      have hsn : ContDiffOn ℝ ∞ (scalarCellPrefix φ (n+1)) W :=
        (hφ n hnN).comp ((hsm n le_rfl).mono inter_subset_left) (fun _ hp => hp.2)
      refine ⟨W,hW,hW0,?_,?_⟩
      · intro j hj
        rcases Nat.eq_or_lt_of_le hj with hj | hj
        · simpa only [hj] using hsn
        · exact (hsm j (Nat.lt_succ_iff.mp hj)).mono inter_subset_left
      · intro j hj
        rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hj) with hj | hj
        · subst j
          exact fun _ hp => hp.2
        · exact (hmap j hj).mono_left inter_subset_left
  exact aux N le_rfl

theorem scalarCellComposition_exists_common_radius {φ : ℕ → ℝ → ℝ} {U : ℕ → Set ℝ} {N : ℕ}
    (hU : ∀ j < N, IsOpen (U j)) (h0 : ∀ j < N, (0 : ℝ) ∈ U j)
    (hφ : ∀ j < N, ContDiffOn ℝ ∞ (φ j) (U j)) (hz : ∀ j < N, φ j 0 = 0) :
    ∃ e > 0, (∀ n ≤ N, ContDiffOn ℝ ∞ (scalarCellPrefix φ n) (ball 0 e)) ∧
      ∀ j < N, ∀ x : ℝ, |x| < e → scalarCellPrefix φ j x ∈ U j := by
  obtain ⟨V,hV,hV0,hsm,hmap⟩ := scalarCellComposition_exists_common_open hU h0 hφ hz
  obtain ⟨e,he,hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hV0)
  refine ⟨e,he,fun n hn => (hsm n hn).mono hball,?_⟩
  intro j hj x hx
  exact hmap j hj (hball (by simpa only [mem_ball,Real.dist_eq,sub_zero] using hx))

end
end TightVer401
