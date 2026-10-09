import TightVer401.ScalarFlowPeriodOverlap
import TightVer401.ScalarFlowPeriodReparameter

namespace TightVer401
noncomputable section
open Set Filter Metric OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

theorem scalarFlowPeriod_equal_on_strip {u v f : Coord → ℝ} {W : Set Coord}
    {V : Set ℝ} {T ε : ℝ} (hε : 0 < ε) (hV : IsOpen V)
    (hW : IsOpen W) (hf : ContDiffOn ℝ ∞ f W)
    (hu : ContDiffOn ℝ ∞ u (scalarCellStrip T ε V))
    (hv : ContDiffOn ℝ ∞ v (scalarCellStrip T ε V))
    (huW : ∀ q ∈ scalarCellStrip T ε V, (![q 0, u q] : Coord) ∈ W)
    (hvW : ∀ q ∈ scalarCellStrip T ε V, (![q 0, v q] : Coord) ∈ W)
    (hdu : ∀ q ∈ scalarCellStrip T ε V, coordPartial 0 u q = f ![q 0, u q])
    (hdv : ∀ q ∈ scalarCellStrip T ε V, coordPartial 0 v q = f ![q 0, v q])
    (htrace : ∀ x ∈ V, u ![T, x] = v ![T, x]) :
    EqOn u v (scalarCellStrip T (ε / 2) V) := by
  intro q hq
  have hmem (s : ℝ) (hs : s ∈ Icc (T - ε / 2) (T + ε / 2)) :
      (![s, q 1] : Coord) ∈ scalarCellStrip T ε V := by
    refine ⟨?_, hq.2⟩
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
    (fun s hs => scalarFlowPeriod_phase_hasDerivAt (scalarCellStrip_isOpen hV) hu
      (hmem s (Ioo_subset_Icc_self hs)) (hdu _ (hmem s (Ioo_subset_Icc_self hs))))
    (fun s hs => scalarFlowPeriod_phase_hasDerivAt (scalarCellStrip_isOpen hV) hv
      (hmem s (Ioo_subset_Icc_self hs)) (hdv _ (hmem s (Ioo_subset_Icc_self hs))))
    (fun s hs => huW _ (hmem s hs)) (fun s hs => hvW _ (hmem s hs))
    (by rw [htrace (q 1) hq.2])
  have hqtime : q 0 ∈ Icc (T - ε / 2) (T + ε / 2) := by
    have hb := abs_lt.mp hq.1
    constructor <;> linarith
  have hr := congrFun (he hqtime) (1 : Fin 2)
  have hq' : (![q 0, q 1] : Coord) = q := by ext i; fin_cases i <;> rfl
  simpa only [Matrix.cons_val_one, Matrix.cons_val_zero, hq'] using hr

theorem scalarCellStrip_subset_ball {T x ε : ℝ} (hε : 0 < ε) :
    scalarCellStrip T ε (ball x ε) ⊆ ball (![T, x] : Coord) ε := by
  intro q hq
  apply (dist_pi_lt_iff hε).mpr
  intro i
  fin_cases i
  · change dist (q 0) T < ε
    simpa only [Real.dist_eq] using hq.1
  · change dist (q 1) x < ε
    exact hq.2

/-- Equal transverse initial germs yield equal actual solution germs. -/
theorem scalarFlowPeriod_initial_germ_unique {u v f : Coord → ℝ}
    {U V W : Set Coord} {T x : ℝ}
    (hU : IsOpen U) (hV : IsOpen V) (hW : IsOpen W)
    (hf : ContDiffOn ℝ ∞ f W) (hu : ContDiffOn ℝ ∞ u U) (hv : ContDiffOn ℝ ∞ v V)
    (hpU : (![T, x] : Coord) ∈ U) (hpV : (![T, x] : Coord) ∈ V)
    (huW : ∀ q ∈ U, (![q 0, u q] : Coord) ∈ W)
    (hvW : ∀ q ∈ V, (![q 0, v q] : Coord) ∈ W)
    (hdu : ∀ q ∈ U, coordPartial 0 u q = f ![q 0, u q])
    (hdv : ∀ q ∈ V, coordPartial 0 v q = f ![q 0, v q])
    (htrace : (fun y => u ![T, y]) =ᶠ[𝓝 x] (fun y => v ![T, y])) :
    u =ᶠ[𝓝 (![T, x] : Coord)] v := by
  obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.mp
    ((hU.inter hV).mem_nhds ⟨hpU, hpV⟩)
  obtain ⟨ν, hν, htr⟩ := Metric.mem_nhds_iff.mp htrace
  let ε := min η ν
  have hε : 0 < ε := lt_min hη hν
  have hsub : scalarCellStrip T ε (ball x ε) ⊆ U ∩ V :=
    (scalarCellStrip_subset_ball hε).trans
      ((ball_subset_ball (min_le_left η ν)).trans hball)
  have he := scalarFlowPeriod_equal_on_strip hε (isOpen_ball (x := x) (ε := ε)) hW hf
    (hu.mono (fun q hq => (hsub hq).1)) (hv.mono (fun q hq => (hsub hq).2))
    (fun q hq => huW q (hsub hq).1) (fun q hq => hvW q (hsub hq).2)
    (fun q hq => hdu q (hsub hq).1) (fun q hq => hdv q (hsub hq).2)
    (fun y hy => htr ((ball_subset_ball (min_le_right η ν)) hy))
  have hm : scalarCellStrip T (ε / 2) (ball x ε) ∈ 𝓝 (![T, x] : Coord) :=
    (scalarCellStrip_isOpen (isOpen_ball (x := x) (ε := ε))).mem_nhds
      ⟨by simpa using half_pos hε, by simpa using (mem_ball_self (x := x) hε)⟩
  filter_upwards [hm] with q hq
  exact he hq

end
end TightVer401
