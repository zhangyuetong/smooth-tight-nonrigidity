import TightVer401.ConcaveJetJoinBlend
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace TightVer401
noncomputable section
open Set Filter
open scoped Topology ContDiff

 def concaveJetJoinPaste (A B : ℝ) (qL Q qR : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x < A then qL x else if B < x then qR x else Q x

 theorem concaveJetJoinPaste_left (A B : ℝ) (qL Q qR : ℝ → ℝ) :
    EqOn (concaveJetJoinPaste A B qL Q qR) qL (Iio A) := by
  intro x hx
  change x < A at hx
  simp [concaveJetJoinPaste, hx]

 theorem concaveJetJoinPaste_right {A B : ℝ} (hAB : A < B) (qL Q qR : ℝ → ℝ) :
    EqOn (concaveJetJoinPaste A B qL Q qR) qR (Ioi B) := by
  intro x hx
  change B < x at hx
  simp [concaveJetJoinPaste, hx, show ¬ x < A by linarith]

 theorem concaveJetJoinPaste_middle (A B : ℝ) (qL Q qR : ℝ → ℝ) :
    EqOn (concaveJetJoinPaste A B qL Q qR) Q (Icc A B) := by
  intro x hx
  simp [concaveJetJoinPaste, not_lt.mpr hx.1, not_lt.mpr hx.2]

 theorem concaveJetJoinPaste_local_branches {A B x : ℝ} (hAB : A < B)
    (qL Q qR : ℝ → ℝ) (hA : Q =ᶠ[𝓝 A] qL) (hB : Q =ᶠ[𝓝 B] qR) :
    (x < A ∧ concaveJetJoinPaste A B qL Q qR =ᶠ[𝓝 x] qL) ∨
    (x ∈ Icc A B ∧ concaveJetJoinPaste A B qL Q qR =ᶠ[𝓝 x] Q) ∨
    (B < x ∧ concaveJetJoinPaste A B qL Q qR =ᶠ[𝓝 x] qR) := by
  by_cases hxL : x < A
  · exact Or.inl ⟨hxL, (eventually_lt_nhds hxL).mono (fun y hy => by simp [concaveJetJoinPaste, hy])⟩
  by_cases hxR : B < x
  · exact Or.inr (Or.inr ⟨hxR, (eventually_gt_nhds hxR).mono (fun y hy => by
      simp [concaveJetJoinPaste, hy, show ¬ y < A by linarith])⟩)
  refine Or.inr (Or.inl ⟨⟨le_of_not_gt hxL, le_of_not_gt hxR⟩, ?_⟩)
  by_cases hxA : x = A
  · subst x
    filter_upwards [hA, eventually_lt_nhds hAB] with y hy hyB
    simp only [concaveJetJoinPaste, not_lt.mpr hyB.le, ite_false]
    split_ifs <;> simp_all
  by_cases hxB : x = B
  · subst x
    filter_upwards [hB, eventually_gt_nhds hAB] with y hy hyA
    simp only [concaveJetJoinPaste, not_lt.mpr hyA.le, ite_false]
    split_ifs <;> simp_all
  have hAx : A < x := lt_of_le_of_ne (le_of_not_gt hxL) (Ne.symm hxA)
  have hxB' : x < B := lt_of_le_of_ne (le_of_not_gt hxR) hxB
  filter_upwards [eventually_gt_nhds hAx, eventually_lt_nhds hxB'] with y hyA hyB
  simp [concaveJetJoinPaste, not_lt.mpr hyA.le, not_lt.mpr hyB.le]

 theorem concaveJetJoinPaste_contDiffOn {A B : ℝ} {U : Set ℝ}
    (hAB : A < B) (hU : IsOpen U) (qL Q qR : ℝ → ℝ)
    (hqL : ContDiffOn ℝ ∞ qL U) (hQ : ContDiff ℝ ∞ Q) (hqR : ContDiffOn ℝ ∞ qR U)
    (hA : Q =ᶠ[𝓝 A] qL) (hB : Q =ᶠ[𝓝 B] qR) :
    ContDiffOn ℝ ∞ (concaveJetJoinPaste A B qL Q qR) U := by
  intro x hx
  rcases concaveJetJoinPaste_local_branches hAB qL Q qR hA hB (x := x) with
    ⟨_, heq⟩ | ⟨_, heq⟩ | ⟨_, heq⟩
  · exact ((hqL x hx).contDiffAt (hU.mem_nhds hx)).congr_of_eventuallyEq heq |>.contDiffWithinAt
  · exact (hQ.contDiffAt.congr_of_eventuallyEq heq).contDiffWithinAt
  · exact ((hqR x hx).contDiffAt (hU.mem_nhds hx)).congr_of_eventuallyEq heq |>.contDiffWithinAt

 theorem concaveJetJoinPaste_second_negative {A B : ℝ} {U : Set ℝ}
    (hAB : A < B) (qL Q qR : ℝ → ℝ)
    (hA : Q =ᶠ[𝓝 A] qL) (hB : Q =ᶠ[𝓝 B] qR)
    (hqL : ∀ x ∈ U, deriv (deriv qL) x < 0)
    (hQ : ∀ x ∈ Icc A B, deriv (deriv Q) x < 0)
    (hqR : ∀ x ∈ U, deriv (deriv qR) x < 0) :
    ∀ x ∈ U, deriv (deriv (concaveJetJoinPaste A B qL Q qR)) x < 0 := by
  intro x hx
  rcases concaveJetJoinPaste_local_branches hAB qL Q qR hA hB (x := x) with
    ⟨_, heq⟩ | ⟨hxQ, heq⟩ | ⟨_, heq⟩
  · rw [heq.deriv.deriv_eq]; exact hqL x hx
  · rw [heq.deriv.deriv_eq]; exact hQ x hxQ
  · rw [heq.deriv.deriv_eq]; exact hqR x hx

end
end TightVer401

