import TightVer401.FermiSupportLocalSeam

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

def scalarCellPaste (T : ℝ) (uL uR : Coord → ℝ) (q : Coord) : ℝ :=
  if q 0 < T then uL q else uR q

def scalarCellPasteDomain (T : ℝ) (VL VR : Set Coord) : Set Coord :=
  {q | (q 0 ≤ T → q ∈ VL) ∧ (T ≤ q 0 → q ∈ VR)}

theorem scalarCellPasteDomain_isOpen (T : ℝ) {VL VR : Set Coord}
    (hVL : IsOpen VL) (hVR : IsOpen VR) : IsOpen (scalarCellPasteDomain T VL VR) := by
  apply isOpen_iff_mem_nhds.mpr
  intro q hq
  by_cases hl : q 0 < T
  · have hn : ∀ᶠ p : Coord in 𝓝 q, p 0 < T :=
      ((continuous_apply 0) : Continuous (fun p : Coord => p 0)).continuousAt.eventually
        (gt_mem_nhds hl)
    filter_upwards [hVL.mem_nhds (hq.1 hl.le),hn] with p hp hpt
    exact ⟨fun _ => hp,fun he => (not_lt_of_ge he hpt).elim⟩
  by_cases hr : T < q 0
  · have hn : ∀ᶠ p : Coord in 𝓝 q, T < p 0 :=
      ((continuous_apply 0) : Continuous (fun p : Coord => p 0)).continuousAt.eventually
        (lt_mem_nhds hr)
    filter_upwards [hVR.mem_nhds (hq.2 hr.le),hn] with p hp hpt
    exact ⟨fun he => (not_lt_of_ge he hpt).elim,fun _ => hp⟩
  have he : q 0 = T := le_antisymm (le_of_not_gt hr) (le_of_not_gt hl)
  filter_upwards [hVL.mem_nhds (hq.1 he.le),hVR.mem_nhds (hq.2 he.ge)] with p hpL hpR
  exact ⟨fun _ => hpL,fun _ => hpR⟩

theorem scalarCellPaste_local_branches {T : ℝ} {uL uR : Coord → ℝ} {VL VR : Set Coord}
    (hag : ∀ q ∈ VL ∩ VR, q 0 = T → uL =ᶠ[𝓝 q] uR)
    {q : Coord} (hq : q ∈ scalarCellPasteDomain T VL VR) :
    (q ∈ VL ∧ scalarCellPaste T uL uR =ᶠ[𝓝 q] uL) ∨
      (q ∈ VR ∧ scalarCellPaste T uL uR =ᶠ[𝓝 q] uR) := by
  by_cases hl : q 0 < T
  · refine Or.inl ⟨hq.1 hl.le,?_⟩
    have hn : ∀ᶠ p : Coord in 𝓝 q, p 0 < T :=
      ((continuous_apply 0) : Continuous (fun p : Coord => p 0)).continuousAt.eventually
        (gt_mem_nhds hl)
    filter_upwards [hn] with p hp
    exact if_pos hp
  by_cases hr : T < q 0
  · refine Or.inr ⟨hq.2 hr.le,?_⟩
    have hn : ∀ᶠ p : Coord in 𝓝 q, T < p 0 :=
      ((continuous_apply 0) : Continuous (fun p : Coord => p 0)).continuousAt.eventually
        (lt_mem_nhds hr)
    filter_upwards [hn] with p hp
    exact if_neg (not_lt_of_ge hp.le)
  have he : q 0 = T := le_antisymm (le_of_not_gt hr) (le_of_not_gt hl)
  refine Or.inr ⟨hq.2 he.ge,?_⟩
  filter_upwards [hag q ⟨hq.1 he.le,hq.2 he.ge⟩ he] with p hp
  unfold scalarCellPaste
  split
  · exact hp
  · rfl

theorem scalarCellPaste_contDiffOn {T : ℝ} {uL uR : Coord → ℝ} {VL VR : Set Coord}
    (hVL : IsOpen VL) (hVR : IsOpen VR)
    (huL : ContDiffOn ℝ ∞ uL VL) (huR : ContDiffOn ℝ ∞ uR VR)
    (hag : ∀ q ∈ VL ∩ VR, q 0 = T → uL =ᶠ[𝓝 q] uR) :
    ContDiffOn ℝ ∞ (scalarCellPaste T uL uR) (scalarCellPasteDomain T VL VR) := by
  intro q hq
  rcases scalarCellPaste_local_branches hag hq with ⟨hp,he⟩ | ⟨hp,he⟩
  · exact (((huL q hp).contDiffAt (hVL.mem_nhds hp)).congr_of_eventuallyEq he).contDiffWithinAt
  · exact (((huR q hp).contDiffAt (hVR.mem_nhds hp)).congr_of_eventuallyEq he).contDiffWithinAt

theorem scalarCellPaste_ode {T : ℝ} {uL uR f : Coord → ℝ} {VL VR : Set Coord}
    (hag : ∀ q ∈ VL ∩ VR, q 0 = T → uL =ᶠ[𝓝 q] uR)
    (hL : ∀ q ∈ VL, coordPartial 0 uL q = f ![q 0,uL q])
    (hR : ∀ q ∈ VR, coordPartial 0 uR q = f ![q 0,uR q]) :
    ∀ q ∈ scalarCellPasteDomain T VL VR,
      coordPartial 0 (scalarCellPaste T uL uR) q = f ![q 0,scalarCellPaste T uL uR q] := by
  intro q hq
  rcases scalarCellPaste_local_branches hag hq with ⟨hp,he⟩ | ⟨hp,he⟩
  · rw [(fermiCoordinatePartial_eventuallyEq he 0).eq_of_nhds,he.eq_of_nhds]
    exact hL q hp
  · rw [(fermiCoordinatePartial_eventuallyEq he 0).eq_of_nhds,he.eq_of_nhds]
    exact hR q hp

theorem scalarCellPaste_image {T : ℝ} {uL uR : Coord → ℝ} {VL VR W : Set Coord}
    (hL : ∀ q ∈ VL, (![q 0,uL q] : Coord) ∈ W)
    (hR : ∀ q ∈ VR, (![q 0,uR q] : Coord) ∈ W) :
    ∀ q ∈ scalarCellPasteDomain T VL VR, (![q 0,scalarCellPaste T uL uR q] : Coord) ∈ W := by
  intro q hq
  unfold scalarCellPaste
  split
  · exact hL q (hq.1 ‹q 0 < T›.le)
  · exact hR q (hq.2 (le_of_not_gt ‹¬q 0 < T›))

end
end TightVer401

