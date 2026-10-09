import TightVer401.ScalarFlowPeriodLocalFamily

namespace TightVer401
noncomputable section
open Set Filter Metric OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

def scalarCellReparameter (u : Coord → ℝ) (p : ℝ → ℝ) (q : Coord) : ℝ :=
  u ![q 0, p (q 1)]

def scalarCellStrip (T ε : ℝ) (V : Set ℝ) : Set Coord :=
  {q | |q 0 - T| < ε ∧ q 1 ∈ V}

theorem scalarCellStrip_isOpen {T ε : ℝ} {V : Set ℝ} (hV : IsOpen V) :
    IsOpen (scalarCellStrip T ε V) :=
  (isOpen_lt ((continuous_apply 0).sub continuous_const).abs continuous_const).inter
    (hV.preimage (continuous_apply 1))

theorem scalarFlowPeriod_reparameter_cell {u f : Coord → ℝ} {p : ℝ → ℝ}
    {V : Set ℝ} {W : Set Coord} {T ε : ℝ}
    (hV : IsOpen V) (hu : ContDiffOn ℝ ∞ u (scalarCellSource T ε))
    (hp : ContDiffOn ℝ ∞ p V) (hmap : ∀ x ∈ V, |p x| < ε)
    (huW : ∀ q ∈ scalarCellSource T ε, (![q 0, u q] : Coord) ∈ W)
    (hode : ∀ q ∈ scalarCellSource T ε, coordPartial 0 u q = f ![q 0, u q]) :
    ContDiffOn ℝ ∞ (scalarCellReparameter u p) (scalarCellStrip T ε V) ∧
    (∀ q ∈ scalarCellStrip T ε V, (![q 0, scalarCellReparameter u p q] : Coord) ∈ W) ∧
    ∀ q ∈ scalarCellStrip T ε V, coordPartial 0 (scalarCellReparameter u p) q =
      f ![q 0, scalarCellReparameter u p q] := by
  have hmaps (q : Coord) (hq : q ∈ scalarCellStrip T ε V) :
      (![q 0, p (q 1)] : Coord) ∈ scalarCellSource T ε := ⟨hq.1, hmap _ hq.2⟩
  have hparam : ContDiffOn ℝ ∞ (fun q : Coord => (![q 0, p (q 1)] : Coord))
      (scalarCellStrip T ε V) := by
    apply contDiffOn_pi.mpr
    intro i
    fin_cases i
    · exact (contDiff_apply ℝ ℝ 0).contDiffOn
    · exact hp.comp (contDiff_apply ℝ ℝ 1).contDiffOn (fun _ hq => hq.2)
  have hs : ContDiffOn ℝ ∞ (scalarCellReparameter u p) (scalarCellStrip T ε V) :=
    hu.comp hparam hmaps
  refine ⟨hs, fun q hq => huW _ (hmaps q hq), ?_⟩
  intro q hq
  have hd := scalarFlowPeriod_slice0_hasDerivAt (scalarCellSource_isOpen T ε) hu (hmaps q hq)
  rw [hode _ (hmaps q hq)] at hd
  have hh := scalarFlowPeriod_slice0_hasDerivAt (scalarCellStrip_isOpen hV) hs
    (r := q 0) (x := q 1) (by
      have he : (![q 0, q 1] : Coord) = q := by ext i; fin_cases i <;> rfl
      rw [he]; exact hq)
  have he : (![q 0, q 1] : Coord) = q := by ext i; fin_cases i <;> rfl
  simpa only [scalarCellReparameter, Matrix.cons_val_zero, Matrix.cons_val_one, he] using
    hh.unique hd

theorem scalarFlowPeriod_endpoint_contDiffOn {u : Coord → ℝ} {r s ε : ℝ}
    (hu : ContDiffOn ℝ ∞ u (scalarCellSource r ε)) (hs : |s - r| < ε) :
    ContDiffOn ℝ ∞ (fun x : ℝ => u ![s, x]) (ball 0 ε) := by
  have hparam : ContDiff ℝ ∞ (fun x : ℝ => (![s, x] : Coord)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · exact contDiff_const
    · exact contDiff_id
  exact hu.comp hparam.contDiffOn (fun x hx => ⟨hs, by
    change |x| < ε
    simpa only [mem_ball, Real.dist_eq, sub_zero] using hx⟩)

end
end TightVer401
