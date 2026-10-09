import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

namespace TightVer401
noncomputable section
open Set

def scalarCellStep (P : ℝ) (N : ℕ) : ℝ := P / (N : ℝ)
def scalarCellTime (P : ℝ) (N j : ℕ) : ℝ := (j : ℝ) * scalarCellStep P N

theorem scalarCellTime_zero (P : ℝ) (N : ℕ) : scalarCellTime P N 0 = 0 := by
  simp [scalarCellTime]

theorem scalarCellTime_end (P : ℝ) {N : ℕ} (hN : 0 < N) : scalarCellTime P N N = P := by
  unfold scalarCellTime scalarCellStep
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  field_simp

theorem scalarCellTime_succ (P : ℝ) (N j : ℕ) :
    scalarCellTime P N (j+1) = scalarCellTime P N j + scalarCellStep P N := by
  simp only [scalarCellTime, Nat.cast_add, Nat.cast_one]
  ring

theorem scalarCellTime_mem_period {P : ℝ} {N j : ℕ} (hP : 0 < P) (hN : 0 < N) (hj : j ≤ N) :
    scalarCellTime P N j ∈ Icc (0 : ℝ) P := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hd : 0 < scalarCellStep P N := div_pos hP hn
  have hc : (j : ℝ) ≤ N := by exact_mod_cast hj
  refine ⟨mul_nonneg (Nat.cast_nonneg j) hd.le, ?_⟩
  have he := mul_le_mul_of_nonneg_right hc hd.le
  change scalarCellTime P N j ≤ scalarCellTime P N N at he
  rwa [scalarCellTime_end P hN] at he

theorem scalarCellTime_cover_neighborhood {P η : ℝ} {N : ℕ}
    (hP : 0 < P) (hN : 0 < N) (hstep : scalarCellStep P N < η) :
    ∀ t ∈ Ioo (-η) (P+η), ∃ j ≤ N, |t - scalarCellTime P N j| < η := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hd : 0 < scalarCellStep P N := div_pos hP hn
  intro t ht
  by_cases ht0 : t < 0
  · refine ⟨0,Nat.zero_le _,?_⟩
    rw [scalarCellTime_zero, sub_zero, abs_of_neg ht0]
    linarith [ht.1]
  by_cases htP : P < t
  · refine ⟨N,le_rfl,?_⟩
    rw [scalarCellTime_end P hN, abs_of_pos (sub_pos.mpr htP)]
    linarith [ht.2]
  have htc : t ∈ Icc (0 : ℝ) P := ⟨le_of_not_gt ht0, le_of_not_gt htP⟩
  let j := Nat.floor (t / scalarCellStep P N)
  have hend : (N : ℝ) * scalarCellStep P N = P := scalarCellTime_end P hN
  have hratio : t / scalarCellStep P N ≤ (N : ℝ) := by
    apply (div_le_iff₀ hd).mpr
    rw [hend]
    exact htc.2
  have hj : j ≤ N := Nat.floor_le_of_le hratio
  have hlo : (j : ℝ) * scalarCellStep P N ≤ t :=
    (le_div_iff₀ hd).mp (Nat.floor_le (div_nonneg htc.1 hd.le))
  have hhi : t < ((j : ℝ)+1) * scalarCellStep P N :=
    (div_lt_iff₀ hd).mp (Nat.lt_floor_add_one (t / scalarCellStep P N))
  refine ⟨j,hj,?_⟩
  change |t - (j : ℝ) * scalarCellStep P N| < η
  rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
  nlinarith

theorem exists_scalarCellTimeGrid {P η : ℝ} (hP : 0 < P) (hη : 0 < η) :
    ∃ N : ℕ, 0 < N ∧ 0 < scalarCellStep P N ∧ scalarCellStep P N < η ∧
      scalarCellTime P N 0 = 0 ∧ scalarCellTime P N N = P ∧
      (∀ j ≤ N, scalarCellTime P N j ∈ Icc (0 : ℝ) P) ∧
      (∀ j, scalarCellTime P N (j+1) = scalarCellTime P N j + scalarCellStep P N) ∧
      ∀ t ∈ Ioo (-η) (P+η), ∃ j ≤ N, |t - scalarCellTime P N j| < η := by
  obtain ⟨N,hN⟩ := exists_nat_gt (P / η)
  have hn : (0 : ℝ) < N := lt_trans (div_pos hP hη) hN
  have hNpos : 0 < N := by exact_mod_cast hn
  have hd : 0 < scalarCellStep P N := div_pos hP hn
  have hsmall : scalarCellStep P N < η := by
    apply (div_lt_iff₀ hn).mpr
    have he := (div_lt_iff₀ hη).mp hN
    simpa only [mul_comm] using he
  exact ⟨N,hNpos,hd,hsmall,scalarCellTime_zero P N,scalarCellTime_end P hNpos,
    fun j hj => scalarCellTime_mem_period hP hNpos hj,scalarCellTime_succ P N,
    scalarCellTime_cover_neighborhood hP hNpos hsmall⟩

end
end TightVer401
