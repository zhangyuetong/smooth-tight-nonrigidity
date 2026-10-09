import Mathlib.Analysis.SpecialFunctions.SmoothTransition

namespace TightVer401
noncomputable section
open Set
open scoped ContDiff

def concaveJetJoinBlendTransition (c r x : ℝ) : ℝ :=
  Real.smoothTransition ((x - (c - r)) / (2 * r))

def concaveJetJoinBlendAcceleration (c r : ℝ) (hL hR : ℝ → ℝ) (x : ℝ) : ℝ :=
  (1 - concaveJetJoinBlendTransition c r x) * hL x + concaveJetJoinBlendTransition c r x * hR x

def concaveJetJoinBlendPiecewise (c : ℝ) (hL hR : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x ≤ c then hL x else hR x

def concaveJetJoinBlendError (c r : ℝ) (hL hR : ℝ → ℝ) (x : ℝ) : ℝ :=
  concaveJetJoinBlendAcceleration c r hL hR x - concaveJetJoinBlendPiecewise c hL hR x

theorem concaveJetJoinBlendTransition_contDiff (c r : ℝ) :
    ContDiff ℝ ∞ (concaveJetJoinBlendTransition c r) :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const (2 * r))

theorem concaveJetJoinBlendTransition_bound (c r x : ℝ) :
    0 ≤ concaveJetJoinBlendTransition c r x ∧ concaveJetJoinBlendTransition c r x ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem concaveJetJoinBlendTransition_left {c r x : ℝ} (hr : 0 < r) (hx : x ≤ c - r) :
    concaveJetJoinBlendTransition c r x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) (by positivity)

theorem concaveJetJoinBlendTransition_right {c r x : ℝ} (hr : 0 < r) (hx : c + r ≤ x) :
    concaveJetJoinBlendTransition c r x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  apply (le_div_iff₀ (by positivity : 0 < 2 * r)).mpr
  linarith

theorem concaveJetJoinBlendAcceleration_contDiff {c r : ℝ} {hL hR : ℝ → ℝ}
    (hfL : ContDiff ℝ ∞ hL) (hfR : ContDiff ℝ ∞ hR) :
    ContDiff ℝ ∞ (concaveJetJoinBlendAcceleration c r hL hR) :=
  ((contDiff_const.sub (concaveJetJoinBlendTransition_contDiff c r)).mul hfL).add
    ((concaveJetJoinBlendTransition_contDiff c r).mul hfR)

theorem concaveJetJoinBlendAcceleration_lower {c r x μ : ℝ} {hL hR : ℝ → ℝ}
    (hbL : μ ≤ hL x) (hbR : μ ≤ hR x) : μ ≤ concaveJetJoinBlendAcceleration c r hL hR x := by
  obtain ⟨hθ0, hθ1⟩ := concaveJetJoinBlendTransition_bound c r x
  have h1 := mul_le_mul_of_nonneg_left hbL (sub_nonneg.mpr hθ1)
  have h2 := mul_le_mul_of_nonneg_left hbR hθ0
  dsimp [concaveJetJoinBlendAcceleration]
  nlinarith

theorem concaveJetJoinBlendAcceleration_pos {c r x μ : ℝ} {hL hR : ℝ → ℝ}
    (hμ : 0 < μ) (hbL : μ ≤ hL x) (hbR : μ ≤ hR x) :
    0 < concaveJetJoinBlendAcceleration c r hL hR x :=
  hμ.trans_le (concaveJetJoinBlendAcceleration_lower hbL hbR)

theorem concaveJetJoinBlendAcceleration_left {c r x : ℝ} (hr : 0 < r) (hL hR : ℝ → ℝ)
    (hx : x ≤ c - r) : concaveJetJoinBlendAcceleration c r hL hR x = hL x := by
  simp [concaveJetJoinBlendAcceleration, concaveJetJoinBlendTransition_left hr hx]

theorem concaveJetJoinBlendAcceleration_right {c r x : ℝ} (hr : 0 < r) (hL hR : ℝ → ℝ)
    (hx : c + r ≤ x) : concaveJetJoinBlendAcceleration c r hL hR x = hR x := by
  simp [concaveJetJoinBlendAcceleration, concaveJetJoinBlendTransition_right hr hx]

theorem concaveJetJoinBlendError_support {c r : ℝ} (hr : 0 < r) (hL hR : ℝ → ℝ) :
    Function.support (concaveJetJoinBlendError c r hL hR) ⊆ Ioo (c - r) (c + r) := by
  intro x hx
  constructor
  · by_contra h
    have hleft : x ≤ c - r := le_of_not_gt h
    apply hx
    change concaveJetJoinBlendAcceleration c r hL hR x - concaveJetJoinBlendPiecewise c hL hR x = 0
    rw [concaveJetJoinBlendAcceleration_left hr hL hR hleft]
    simp [concaveJetJoinBlendPiecewise, show x ≤ c by linarith]
  · by_contra h
    have hright : c + r ≤ x := le_of_not_gt h
    apply hx
    change concaveJetJoinBlendAcceleration c r hL hR x - concaveJetJoinBlendPiecewise c hL hR x = 0
    rw [concaveJetJoinBlendAcceleration_right hr hL hR hright]
    simp [concaveJetJoinBlendPiecewise, show ¬x ≤ c by linarith]

theorem concaveJetJoinBlendError_tsupport {c r : ℝ} (hr : 0 < r) (hL hR : ℝ → ℝ) :
    tsupport (concaveJetJoinBlendError c r hL hR) ⊆ Icc (c - r) (c + r) :=
  closure_minimal ((concaveJetJoinBlendError_support hr hL hR).trans Ioo_subset_Icc_self) isClosed_Icc

end
end TightVer401
