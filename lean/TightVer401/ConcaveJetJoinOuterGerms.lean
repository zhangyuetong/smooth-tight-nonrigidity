import TightVer401.ConcaveJetJoinBlend
import Mathlib.Topology.MetricSpace.Pseudo.Defs

namespace TightVer401
noncomputable section
open Set
open scoped Topology

 theorem exists_concaveJetJoin_controls_outer_zero {n : ℕ} {L : ℝ}
    (ψ : Fin n → ℝ → ℝ) (hψ : ∀ j, tsupport (ψ j) ⊆ Ioo 0 L) :
    (∃ α > 0, ∀ x < α, ∀ j, ψ j x = 0) ∧
    (∃ β < L, ∀ x, β < x → ∀ j, ψ j x = 0) := by
  let S : Set ℝ := ⋃ j, tsupport (ψ j)
  have hS : IsClosed S := isClosed_iUnion_of_finite (fun j => isClosed_closure)
  have hsub : S ⊆ Ioo 0 L := iUnion_subset hψ
  have h0 : (0 : ℝ) ∈ Sᶜ := by intro h; exact (hsub h).1.false
  have hL : L ∈ Sᶜ := by intro h; exact (hsub h).2.false
  obtain ⟨e, he, hball⟩ := Metric.mem_nhds_iff.mp (hS.isOpen_compl.mem_nhds h0)
  obtain ⟨d, hd, hballL⟩ := Metric.mem_nhds_iff.mp (hS.isOpen_compl.mem_nhds hL)
  constructor
  · refine ⟨e, he, ?_⟩
    intro x hx j
    apply image_eq_zero_of_notMem_tsupport
    intro hj
    have hxpos := (hψ j hj).1
    have hb : x ∈ Metric.ball 0 e := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hxpos]
      exact hx
    exact hball hb (mem_iUnion.mpr ⟨j, hj⟩)
  · refine ⟨L - d, by linarith, ?_⟩
    intro x hx j
    apply image_eq_zero_of_notMem_tsupport
    intro hj
    have hxL := (hψ j hj).2
    have hb : x ∈ Metric.ball L d := by
      rw [Metric.mem_ball, Real.dist_eq, abs_of_neg (sub_neg.mpr hxL)]
      linarith
    exact hballL hb (mem_iUnion.mpr ⟨j, hj⟩)

 theorem concaveJetJoin_corrected_outer_germs {n : ℕ} {L c r : ℝ}
    (hr : 0 < r) (hleft : 0 < c - r) (hright : c + r < L)
    (hL hR a : ℝ → ℝ) (ψ : Fin n → ℝ → ℝ)
    (hψ : ∀ j, tsupport (ψ j) ⊆ Ioo 0 L)
    (hsupp : Function.support (fun x => a x - concaveJetJoinBlendAcceleration c r hL hR x)
      ⊆ ⋃ j, Function.support (ψ j)) :
    (∃ α > 0, α < c - r ∧ EqOn a hL (Iio α)) ∧
    (∃ β < L, c + r < β ∧ EqOn a hR (Ioi β)) := by
  obtain ⟨⟨α₀, hα₀, hzL⟩, ⟨β₀, hβ₀, hzR⟩⟩ :=
    exists_concaveJetJoin_controls_outer_zero ψ hψ
  have heq (x : ℝ) (hz : ∀ j, ψ j x = 0) :
      a x = concaveJetJoinBlendAcceleration c r hL hR x := by
    apply sub_eq_zero.mp
    by_contra h
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hsupp h)
    exact hj (hz j)
  constructor
  · let α := min α₀ (c - r) / 2
    have hα : 0 < α := div_pos (lt_min hα₀ hleft) (by norm_num)
    have hα₁ : α < α₀ := by dsimp [α]; linarith [min_le_left α₀ (c-r)]
    have hα₂ : α < c-r := by dsimp [α]; linarith [min_le_right α₀ (c-r)]
    refine ⟨α, hα, hα₂, ?_⟩
    intro x hx
    rw [heq x (hzL x (hx.trans hα₁))]
    exact concaveJetJoinBlendAcceleration_left hr hL hR (hx.trans hα₂).le
  · let β := (max β₀ (c+r) + L) / 2
    have hmax : max β₀ (c+r) < L := max_lt hβ₀ hright
    have hβ : β < L := by dsimp [β]; linarith
    have hβ₁ : β₀ < β := by dsimp [β]; linarith [le_max_left β₀ (c+r)]
    have hβ₂ : c+r < β := by dsimp [β]; linarith [le_max_right β₀ (c+r)]
    refine ⟨β, hβ, hβ₂, ?_⟩
    intro x hx
    rw [heq x (hzR x (hβ₁.trans hx))]
    exact concaveJetJoinBlendAcceleration_right hr hL hR (hβ₂.trans hx).le

end
end TightVer401
