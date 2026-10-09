import TightVer401.ScalarFlowPeriodCoordinates

namespace TightVer401
noncomputable section
open Set Filter Metric OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

def scalarCellSource (r ε : ℝ) : Set Coord := {q | |q 0 - r| < ε ∧ |q 1| < ε}
def scalarCellParameter (r : ℝ) (q : Coord) : ℝ × Coord := (q 0 - r, ![r, q 1])
def scalarCellMap (Φ : ℝ × Coord → Coord) (r : ℝ) (q : Coord) : ℝ := Φ (scalarCellParameter r q) 1

theorem scalarCellSource_isOpen (r ε : ℝ) : IsOpen (scalarCellSource r ε) :=
  (isOpen_lt ((continuous_apply 0).sub continuous_const).abs continuous_const).inter
    (isOpen_lt (continuous_apply 1).abs continuous_const)

theorem scalarCellParameter_contDiff (r : ℝ) : ContDiff ℝ ∞ (scalarCellParameter r) := by
  have hv : ContDiff ℝ ∞ (fun q : Coord => (![r, q 1] : Coord)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · exact contDiff_const
    · exact contDiff_apply ℝ ℝ 1
  exact ((contDiff_apply ℝ ℝ 0).sub contDiff_const).prodMk hv

theorem scalarFlowPeriod_slice0_hasDerivAt {u : Coord → ℝ} {V : Set Coord}
    (hV : IsOpen V) (hu : ContDiffOn ℝ ∞ u V) {r x : ℝ} (hp : (![r, x] : Coord) ∈ V) :
    HasDerivAt (fun s => u ![s, x]) (coordPartial 0 u ![r, x]) r := by
  have hi : HasDerivAt (fun s : ℝ => (![s, x] : Coord)) (Pi.single 0 1) r := by
    have h := ((hasDerivAt_id r).smul_const (Pi.single 0 1 : Coord)).const_add
      (Pi.single 1 x : Coord)
    convert! h using 1
    · funext s
      ext i
      fin_cases i <;> simp
    · simp
  exact ((hu _ hp).contDiffAt (hV.mem_nhds hp)).differentiableAt (by simp)
    |>.hasFDerivAt.comp_hasDerivAt r hi

theorem scalarFlowPeriod_extract_scalar_cell {f : Coord → ℝ} {W : Set Coord}
    {D : Set (ℝ × Coord)} {Φ : ℝ × Coord → Coord} {δ r : ℝ}
    (hδ : 0 < δ) (hW : IsOpen W) (hf : ContDiffOn ℝ ∞ f W)
    (hΦ : ContDiffOn ℝ ∞ Φ D)
    (hzero : ∀ y, (0, y) ∈ D → Φ (0, y) = y)
    (hode : ∀ q ∈ D, Φ q ∈ W ∧ HasDerivAt (fun s => Φ (s, q.2))
      (scalarFlowAutonomization f (Φ q)) q.1)
    (hseam : ∀ a : ℝ, (![a, 0] : Coord) ∈ W)
    (hfzero : ∀ a : ℝ, f ![a, 0] = 0)
    (hbox : ∀ s x : ℝ, |s| < δ → |x| < δ → (s, (![r, x] : Coord)) ∈ D) :
    ContDiffOn ℝ ∞ (scalarCellMap Φ r) (scalarCellSource r (δ / 2)) ∧
      (∀ q ∈ scalarCellSource r (δ / 2), (![q 0, scalarCellMap Φ r q] : Coord) ∈ W) ∧
      (∀ q ∈ scalarCellSource r (δ / 2), coordPartial 0 (scalarCellMap Φ r) q =
        f ![q 0, scalarCellMap Φ r q]) ∧
      (∀ a : ℝ, |a - r| < δ / 2 → scalarCellMap Φ r ![a, 0] = 0) ∧
      ∀ x : ℝ, |x| < δ / 2 → scalarCellMap Φ r ![r, x] = x := by
  have hmem (q : Coord) (hq : q ∈ scalarCellSource r (δ / 2)) : scalarCellParameter r q ∈ D :=
    hbox _ _ (hq.1.trans (half_lt_self hδ)) (hq.2.trans (half_lt_self hδ))
  have hs : ContDiffOn ℝ ∞ (scalarCellMap Φ r) (scalarCellSource r (δ / 2)) :=
    (contDiff_apply ℝ ℝ 1).comp_contDiffOn
      (hΦ.comp (scalarCellParameter_contDiff r).contDiffOn hmem)
  have he (q : Coord) (hq : q ∈ scalarCellSource r (δ / 2)) :
      Φ (scalarCellParameter r q) = (![q 0, scalarCellMap Φ r q] : Coord) := by
    have ht := scalarFlowPeriod_time_coordinate hδ hzero (fun p hp => (hode p hp).2)
      (fun s ht => hbox s (q 1) ht (hq.2.trans (half_lt_self hδ)))
      (hq.1.trans (half_lt_self hδ))
    ext i
    fin_cases i
    · change Φ (q 0 - r, ![r, q 1]) 0 = q 0
      linarith
    · rfl
  refine ⟨hs, fun q hq => he q hq ▸ (hode _ (hmem q hq)).1, ?_, ?_, ?_⟩
  · intro q hq
    have hd := (hasDerivAt_pi.mp (hode _ (hmem q hq)).2) (1 : Fin 2)
    change HasDerivAt (fun s => Φ (s, ![r, q 1]) 1)
      (f (Φ (scalarCellParameter r q))) (q 0 - r) at hd
    rw [he q hq] at hd
    have ht := hd.scomp_of_eq (q 0) ((hasDerivAt_id (q 0)).sub_const r) rfl
    have ht' : HasDerivAt (fun a => scalarCellMap Φ r ![a, q 1])
        (f ![q 0, scalarCellMap Φ r q]) (q 0) := by
      simpa only [scalarCellMap, scalarCellParameter, Matrix.cons_val_zero,
        Matrix.cons_val_one, Function.comp_def, id_eq, one_smul] using ht
    have hq' : (![q 0, q 1] : Coord) = q := by ext i; fin_cases i <;> rfl
    have hu := scalarFlowPeriod_slice0_hasDerivAt (scalarCellSource_isOpen r (δ / 2)) hs
      (r := q 0) (x := q 1) (by rw [hq']; exact hq)
    simpa only [hq'] using hu.unique ht'
  · intro a ha
    have hc := scalarFlowPeriod_central_orbit hδ hW hf hΦ hzero hode hseam hfzero
      (fun s hs => hbox s 0 hs (by simpa using hδ)) (a - r) ha
    change Φ (a - r, ![r, 0]) 1 = 0
    rw [hc]
    rfl
  · intro x hx
    change Φ (r - r, ![r, x]) 1 = x
    rw [sub_self, hzero ![r, x] (hbox 0 x (by simpa using hδ) (hx.trans (half_lt_self hδ)))]
    rfl

end
end TightVer401
