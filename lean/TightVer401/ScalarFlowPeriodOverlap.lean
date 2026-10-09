import TightVer401.ScalarFlowPeriodLocalFamily

namespace TightVer401
noncomputable section
open Set Filter Metric OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

theorem scalarFlowPeriod_phase_hasDerivAt {u f : Coord → ℝ} {V : Set Coord}
    (hV : IsOpen V) (hu : ContDiffOn ℝ ∞ u V) {r x : ℝ}
    (hp : (![r, x] : Coord) ∈ V)
    (hode : coordPartial 0 u ![r, x] = f ![r, u ![r, x]]) :
    HasDerivAt (fun s => (![s, u ![s, x]] : Coord))
      (scalarFlowAutonomization f ![r, u ![r, x]]) r := by
  have hd := ((hasDerivAt_id r).smul_const (Pi.single 0 1 : Coord)).add
    ((scalarFlowPeriod_slice0_hasDerivAt hV hu hp).smul_const (Pi.single 1 1 : Coord))
  convert! hd using 1
  · funext s
    ext i
    fin_cases i <;> simp
  · ext i
    fin_cases i <;> simp [scalarFlowAutonomization, hode]

/-- Actual solution uniqueness upgrades equal initial traces to equality on a rectangle. -/
theorem scalarFlowPeriod_equal_on_rectangle {u v f : Coord → ℝ} {W : Set Coord}
    {T ε : ℝ} (hε : 0 < ε) (hW : IsOpen W) (hf : ContDiffOn ℝ ∞ f W)
    (hu : ContDiffOn ℝ ∞ u (scalarCellSource T ε))
    (hv : ContDiffOn ℝ ∞ v (scalarCellSource T ε))
    (huW : ∀ q ∈ scalarCellSource T ε, (![q 0, u q] : Coord) ∈ W)
    (hvW : ∀ q ∈ scalarCellSource T ε, (![q 0, v q] : Coord) ∈ W)
    (hdu : ∀ q ∈ scalarCellSource T ε, coordPartial 0 u q = f ![q 0, u q])
    (hdv : ∀ q ∈ scalarCellSource T ε, coordPartial 0 v q = f ![q 0, v q])
    (htrace : ∀ x : ℝ, |x| < ε → u ![T, x] = v ![T, x]) :
    EqOn u v (scalarCellSource T (ε / 2)) := by
  intro q hq
  have hx : |q 1| < ε := hq.2.trans (half_lt_self hε)
  have hmem (s : ℝ) (hs : s ∈ Icc (T - ε / 2) (T + ε / 2)) :
      (![s, q 1] : Coord) ∈ scalarCellSource T ε := by
    refine ⟨?_, hx⟩
    change |s - T| < ε
    have hb : |s - T| ≤ ε / 2 := abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
    exact hb.trans_lt (half_lt_self hε)
  have hslice : Continuous (fun s : ℝ => (![s, q 1] : Coord)) := by fun_prop
  have huc : ContinuousOn (fun s => (![s, u ![s, q 1]] : Coord))
      (Icc (T - ε / 2) (T + ε / 2)) := by
    apply continuousOn_pi.mpr
    intro i
    fin_cases i
    · exact continuous_id.continuousOn
    · exact hu.continuousOn.comp hslice.continuousOn hmem
  have hvc : ContinuousOn (fun s => (![s, v ![s, q 1]] : Coord))
      (Icc (T - ε / 2) (T + ε / 2)) := by
    apply continuousOn_pi.mpr
    intro i
    fin_cases i
    · exact continuous_id.continuousOn
    · exact hv.continuousOn.comp hslice.continuousOn hmem
  have he := scalarFlowPeriod_unique_Icc_local hW (scalarFlowAutonomization_contDiffOn hf)
    (t₀ := T) (by constructor <;> linarith) huc hvc
    (fun s hs => scalarFlowPeriod_phase_hasDerivAt (scalarCellSource_isOpen T ε) hu
      (hmem s (Ioo_subset_Icc_self hs)) (hdu _ (hmem s (Ioo_subset_Icc_self hs))))
    (fun s hs => scalarFlowPeriod_phase_hasDerivAt (scalarCellSource_isOpen T ε) hv
      (hmem s (Ioo_subset_Icc_self hs)) (hdv _ (hmem s (Ioo_subset_Icc_self hs))))
    (fun s hs => huW _ (hmem s hs)) (fun s hs => hvW _ (hmem s hs))
    (by rw [htrace (q 1) hx])
  have hqtime : q 0 ∈ Icc (T - ε / 2) (T + ε / 2) := by
    have hb := abs_lt.mp hq.1
    constructor <;> linarith
  have hr := congrFun (he hqtime) (1 : Fin 2)
  have hq' : (![q 0, q 1] : Coord) = q := by ext i; fin_cases i <;> rfl
  simpa only [Matrix.cons_val_one, Matrix.cons_val_zero, hq'] using hr

end
end TightVer401
