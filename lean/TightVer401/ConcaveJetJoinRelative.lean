import TightVer401.ConcaveJetJoinShift
import TightVer401.ConcaveJetJoinLocalExtension
import TightVer401.ConcaveJetJoinPaste

namespace TightVer401
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

theorem jetLocalExtension_eventuallyEq {c x : ℝ} (β : ContDiffBump c) (q : ℝ → ℝ)
    (hx : x ∈ ball c β.rIn) : jetLocalExtension β q =ᶠ[𝓝 x] q := by
  filter_upwards [isOpen_ball.mem_nhds hx] with y hy
  exact jetLocalExtension_eqOn β q (ball_subset_closedBall hy)

/-- Relative smoothing of a concave first-jet join. Both representatives are
only locally smooth; the prescribed open join neighborhood may be arbitrary. -/
theorem exists_concave_first_jet_join {U V : Set ℝ} (hU : IsOpen U) (hV : IsOpen V)
    {c : ℝ} (hcU : c ∈ U) (hcV : c ∈ V) {qL qR : ℝ → ℝ}
    (hqL : ContDiffOn ℝ ∞ qL U) (hqR : ContDiffOn ℝ ∞ qR U)
    (hv : qL c = qR c) (hd : deriv qL c = deriv qR c)
    (hnegL : ∀ x ∈ U, deriv (deriv qL) x < 0)
    (hnegR : ∀ x ∈ U, deriv (deriv qR) x < 0) :
    ∃ q : ℝ → ℝ, ContDiffOn ℝ ∞ q U ∧
      EqOn q qL ((U ∩ Iic c) \ V) ∧ EqOn q qR ((U ∩ Ici c) \ V) ∧
      (∀ x ∈ U, deriv (deriv q) x < 0) := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
    ((hU.inter hV).mem_nhds ⟨hcU, hcV⟩)
  let β := momentControlBump c (δ / 2) (half_pos hδ)
  have hβ : tsupport (β : ℝ → ℝ) ⊆ U := by
    change tsupport (momentControlBump c (δ / 2) (half_pos hδ) : ℝ → ℝ) ⊆ U
    rw [(momentControlBump c (δ / 2) (half_pos hδ)).tsupport_eq]
    intro x hx
    exact (hball (lt_of_le_of_lt hx (half_lt_self hδ))).1
  let l := jetLocalExtension β qL
  let r := jetLocalExtension β qR
  have hl : ContDiff ℝ ∞ l := jetLocalExtension_contDiff hU hqL β hβ
  have hr : ContDiff ℝ ∞ r := jetLocalExtension_contDiff hU hqR β hβ
  let A := c - δ / 8
  let B := c + δ / 8
  have hAc : A < c := by dsimp [A]; linarith
  have hcB : c < B := by dsimp [B]; linarith
  have hAB : A < B := hAc.trans hcB
  have hstrip : Icc A B ⊆ ball c β.rIn := by
    rw [Real.ball_eq_Ioo]
    intro x hx
    change c - (δ / 2 / 2) < x ∧ x < c + (δ / 2 / 2)
    dsimp [A, B] at hx
    constructor <;> linarith [hx.1, hx.2]
  have hstripUV : Icc A B ⊆ U ∩ V := by
    intro x hx
    apply hball
    have he := hstrip hx
    change dist x c < δ / 2 / 2 at he
    change dist x c < δ
    linarith
  have hcstrip : c ∈ Icc A B := ⟨hAc.le, hcB.le⟩
  have hel (x) (hx : x ∈ Icc A B) : l =ᶠ[𝓝 x] qL := jetLocalExtension_eventuallyEq β qL (hstrip hx)
  have her (x) (hx : x ∈ Icc A B) : r =ᶠ[𝓝 x] qR := jetLocalExtension_eventuallyEq β qR (hstrip hx)
  have hv' : l c = r c := (hel c hcstrip).self_of_nhds.trans (hv.trans (her c hcstrip).self_of_nhds.symm)
  have hd' : deriv l c = deriv r c := (hel c hcstrip).deriv_eq.trans (hd.trans (her c hcstrip).deriv_eq.symm)
  have hnL : ∀ x ∈ Icc A B, deriv (deriv l) x < 0 := by
    intro x hx
    rw [(hel x hx).deriv.deriv_eq]
    exact hnegL x (hstripUV hx).1
  have hnR : ∀ x ∈ Icc A B, deriv (deriv r) x < 0 := by
    intro x hx
    rw [(her x hx).deriv.deriv_eq]
    exact hnegR x (hstripUV hx).1
  obtain ⟨Q, hQ, hnQ, ⟨α, hα, heQL⟩, ⟨γ, hγ, heQR⟩⟩ :=
    exists_concaveJetJoin_global_interval ⟨hAc, hcB⟩ hl hr hv' hd' hnL hnR
  have hAstrip : A ∈ Icc A B := ⟨le_rfl, hAB.le⟩
  have hBstrip : B ∈ Icc A B := ⟨hAB.le, le_rfl⟩
  have hAQ : Q =ᶠ[𝓝 A] qL := by
    have he : Q =ᶠ[𝓝 A] l := by
      filter_upwards [isOpen_Iio.mem_nhds hα] with x hx
      exact heQL hx
    exact he.trans (hel A hAstrip)
  have hBQ : Q =ᶠ[𝓝 B] qR := by
    have he : Q =ᶠ[𝓝 B] r := by
      filter_upwards [isOpen_Ioi.mem_nhds hγ] with x hx
      exact heQR hx
    exact he.trans (her B hBstrip)
  let q := concaveJetJoinPaste A B qL Q qR
  refine ⟨q, concaveJetJoinPaste_contDiffOn hAB hU qL Q qR hqL hQ hqR hAQ hBQ, ?_, ?_,
    concaveJetJoinPaste_second_negative hAB qL Q qR hAQ hBQ hnegL hnQ hnegR⟩
  · intro x hx
    have hxA : x < A := by
      by_contra h
      have hxstrip : x ∈ Icc A B := ⟨le_of_not_gt h, hx.1.2.trans hcB.le⟩
      exact hx.2 (hstripUV hxstrip).2
    exact concaveJetJoinPaste_left A B qL Q qR hxA
  · intro x hx
    have hxB : B < x := by
      by_contra h
      have hxstrip : x ∈ Icc A B := ⟨hAc.le.trans hx.1.2, le_of_not_gt h⟩
      exact hx.2 (hstripUV hxstrip).2
    exact concaveJetJoinPaste_right hAB qL Q qR hxB

end
end TightVer401
