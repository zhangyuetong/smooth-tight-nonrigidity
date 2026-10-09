import TightVer401.RuledProfileApplication

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

def coordinateBandExtension {V : Type*} [Zero V] (b : ℝ) (Y : Coord → V) : Coord → V :=
  fun p => if p 1 ∈ Ioo 0 b then Y p else 0

theorem coordinateBandExtension_eventually_eq {V : Type*} [Zero V] {b : ℝ}
    {Y : Coord → V} {p : Coord} (hp : p 1 ∈ Ioo 0 b) :
    coordinateBandExtension b Y =ᶠ[𝓝 p] Y := by
  have hn : ∀ᶠ q : Coord in 𝓝 p, q 1 ∈ Ioo 0 b :=
    (isOpen_Ioo.preimage (continuous_apply 1)).mem_nhds hp
  filter_upwards [hn] with q hq
  exact if_pos hq

theorem coordinateBandExtension_eventually_zero {V : Type*} [Zero V]
    {b lower upper : ℝ} {Y : Coord → V} {p : Coord}
    (hlower : 0 < lower) (hupper : upper < b)
    (hzero : ∀ q : Coord, q 1 ∈ Ioo 0 b → q 1 < lower ∨ upper < q 1 → Y q = 0)
    (hp : p 1 ∉ Ioo 0 b) :
    coordinateBandExtension b Y =ᶠ[𝓝 p] (fun _ => 0) := by
  have hcases : p 1 ≤ 0 ∨ b ≤ p 1 := by simpa only [mem_Ioo, not_and_or, not_lt] using hp
  rcases hcases with hlo | hhi
  · have hn : ∀ᶠ q : Coord in 𝓝 p, q 1 < lower :=
      (continuous_apply 1).continuousAt.eventually_lt continuousAt_const (hlo.trans_lt hlower)
    filter_upwards [hn] with q hq
    by_cases hqb : q 1 ∈ Ioo 0 b
    · simp only [coordinateBandExtension, if_pos hqb]
      exact hzero q hqb (Or.inl hq)
    · exact if_neg hqb
  · have hn : ∀ᶠ q : Coord in 𝓝 p, upper < q 1 :=
      continuousAt_const.eventually_lt (continuous_apply 1).continuousAt (hupper.trans_le hhi)
    filter_upwards [hn] with q hq
    by_cases hqb : q 1 ∈ Ioo 0 b
    · simp only [coordinateBandExtension, if_pos hqb]
      exact hzero q hqb (Or.inr hq)
    · exact if_neg hqb

theorem coordinateBandExtension_contDiff {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {b lower upper : ℝ} {Y : Coord → V} (hlower : 0 < lower) (hupper : upper < b)
    (hY : ContDiffOn ℝ ∞ Y {p : Coord | p 1 ∈ Ioo 0 b})
    (hzero : ∀ q : Coord, q 1 ∈ Ioo 0 b → q 1 < lower ∨ upper < q 1 → Y q = 0) :
    ContDiff ℝ ∞ (coordinateBandExtension b Y) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases hp : p 1 ∈ Ioo 0 b
  · exact ((hY p hp).contDiffAt ((isOpen_Ioo.preimage (continuous_apply 1)).mem_nhds hp)).congr_of_eventuallyEq
      (coordinateBandExtension_eventually_eq hp)
  · exact contDiffAt_const.congr_of_eventuallyEq
      (coordinateBandExtension_eventually_zero hlower hupper hzero hp)

theorem coordinateBandExtension_strain {b lower upper : ℝ} {X Y : Coord → Ambient}
    (hlower : 0 < lower) (hupper : upper < b)
    (hzero : ∀ q : Coord, q 1 ∈ Ioo 0 b → q 1 < lower ∨ upper < q 1 → Y q = 0)
    (hstrain : ∀ p : Coord, p 1 ∈ Ioo 0 b → ∀ i j : Fin 2, strain X Y p i j = 0)
    (p : Coord) (i j : Fin 2) : strain X (coordinateBandExtension b Y) p i j = 0 := by
  by_cases hp : p 1 ∈ Ioo 0 b
  · have he : fderiv ℝ (coordinateBandExtension b Y) p = fderiv ℝ Y p :=
      (coordinateBandExtension_eventually_eq (Y := Y) hp).fderiv_eq
    simpa only [strain, coordPartial, he] using hstrain p hp i j
  · have he : fderiv ℝ (coordinateBandExtension b Y) p = fderiv ℝ (fun _ : Coord => (0 : Ambient)) p :=
      (coordinateBandExtension_eventually_zero hlower hupper hzero hp).fderiv_eq
    have hz : fderiv ℝ (fun _ : Coord => (0 : Ambient)) p = 0 :=
      (hasFDerivAt_const (c := (0 : Ambient)) p).fderiv
    simp only [strain, coordPartial, he, hz, zero_apply,
      inner_zero_left, inner_zero_right, add_zero]

theorem coordinateBandExtension_support_bounds {V : Type*} [Zero V]
    {b lower upper : ℝ} {Y : Coord → V}
    (hzero : ∀ q : Coord, q 1 ∈ Ioo 0 b → q 1 < lower ∨ upper < q 1 → Y q = 0) :
    tsupport (coordinateBandExtension b Y) ⊆ {p : Coord | p 1 ∈ Icc lower upper} := by
  apply closure_minimal _ (isClosed_Icc.preimage (continuous_apply 1))
  intro p hp
  by_contra hn
  have hh : p 1 < lower ∨ upper < p 1 := by
    simpa only [mem_preimage, mem_Icc, not_and_or, not_le] using hn
  by_cases hb : p 1 ∈ Ioo 0 b
  · exact hp (by simp only [coordinateBandExtension, if_pos hb]; exact hzero p hb hh)
  · exact hp (if_neg hb)

theorem coordinateBandExtension_periodic {V : Type*} [Zero V] {L b : ℝ} {Y : Coord → V}
    (hY : ∀ u, Function.Periodic (fun s => Y (![s, u] : Coord)) L) (u : ℝ) :
    Function.Periodic (fun s => coordinateBandExtension b Y (![s, u] : Coord)) L := by
  intro s
  simp only [coordinateBandExtension, Matrix.cons_val_one, Matrix.cons_val_zero, hY u s]
  rfl

end
end TightVer401
