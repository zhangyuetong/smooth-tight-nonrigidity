import TightVer401.ScalarFlowPeriodFiniteGerms
import TightVer401.ScalarCellFinitePaste

namespace TightVer401
noncomputable section
open Set Filter Metric OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

/-- A smooth scalar field vanishing on the entire central orbit has an actual smooth
solution family around a full finite period. The domain and family are constructed from
pinned OpenAI local flows, finite endpoint compositions, and actual ODE uniqueness. -/
theorem exists_scalarFlowPeriod_family {f : Coord → ℝ} {W : Set Coord} {P : ℝ}
    (hP : 0 < P) (hW : IsOpen W) (hf : ContDiffOn ℝ ∞ f W)
    (hseam : ∀ r : ℝ, (![r, 0] : Coord) ∈ W)
    (hfzero : ∀ r : ℝ, f ![r, 0] = 0) :
    ∃ (V : Set Coord) (u : Coord → ℝ), IsOpen V ∧ ContDiffOn ℝ ∞ u V ∧
      (∀ q ∈ V, (![q 0, u q] : Coord) ∈ W) ∧
      (∀ q ∈ V, coordPartial 0 u q = f ![q 0, u q]) ∧
      (∀ r ∈ Icc (0 : ℝ) P, (![r, 0] : Coord) ∈ V) ∧
      (∀ r ∈ Icc (0 : ℝ) P, u ![r, 0] = 0) ∧
      (fun x : ℝ => u ![0, x]) =ᶠ[𝓝 (0 : ℝ)] id := by
  obtain ⟨N, ε, e, hN, hε, he, hd, hsmall, w, hw, hactual, hcentral, htrace, hinit⟩ :=
    scalarFlowPeriod_exists_composable_cells hP hW hf hseam hfzero
  have hstep (j : ℕ) (hj : j < N) :
      0 < scalarCellTime P N (j+1) - scalarCellTime P N j := by
    rw [scalarCellTime_succ, add_sub_cancel_left]
    exact hd
  have hs (j : ℕ) (hj : j < N) :
      scalarCellTime P N (j+1) - scalarCellTime P N j < ε / 4 := by
    rw [scalarCellTime_succ, add_sub_cancel_left]
    exact hsmall
  have ha (j : ℕ) (hj : j < N) :
      |scalarCellTime P N (j+1) - scalarCellTime P N j| < ε := by
    rw [abs_of_pos (hstep j hj)]
    linarith [hs j hj]
  have hg := scalarFlowPeriod_adjacent_seam_germs hε ha hW hf hw hactual htrace
  obtain ⟨u, V, hV, hu, himage, hode, hzero, hi⟩ := exists_scalarCellFinitePaste hε
    (scalarCellTime_zero P N) isOpen_ball (mem_ball_self he) hstep hs hw
    (fun j hj q hq => (hactual j hj q hq).1)
    (fun j hj q hq => (hactual j hj q hq).2) hg hcentral hinit
  rw [scalarCellTime_end P hN] at hzero
  exact ⟨V, u, hV, hu, himage, hode,
    fun r hr => (hzero r hr).1, fun r hr => (hzero r hr).2, hi⟩

end
end TightVer401
