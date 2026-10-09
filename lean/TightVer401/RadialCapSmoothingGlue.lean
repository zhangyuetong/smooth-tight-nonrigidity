import TightVer401.ConcaveJetJoinPaste
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace TightVer401
noncomputable section
open Set Filter
open scoped ContDiff Topology

def radialCapSmoothingGlue (B : ℝ) (qL qR : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x < B then qL x else qR x

theorem radialCapSmoothingGlue_local {B x : ℝ} (qL qR : ℝ → ℝ)
    (hB : qL =ᶠ[𝓝 B] qR) :
    (x < B ∧ radialCapSmoothingGlue B qL qR =ᶠ[𝓝 x] qL) ∨
    (B ≤ x ∧ radialCapSmoothingGlue B qL qR =ᶠ[𝓝 x] qR) := by
  by_cases hx : x < B
  · exact Or.inl ⟨hx, (eventually_lt_nhds hx).mono (fun y hy => by simp [radialCapSmoothingGlue, hy])⟩
  refine Or.inr ⟨le_of_not_gt hx, ?_⟩
  by_cases he : x = B
  · subst x
    filter_upwards [hB] with y hy
    simp only [radialCapSmoothingGlue]
    split_ifs <;> simp_all
  · have hBx : B < x := lt_of_le_of_ne (le_of_not_gt hx) (Ne.symm he)
    exact (eventually_gt_nhds hBx).mono (fun y hy => by simp [radialCapSmoothingGlue, not_lt.mpr hy.le])

theorem radialCapSmoothingGlue_contDiffOn {B : ℝ} {U V W : Set ℝ}
    (hU : IsOpen U) (hV : IsOpen V) (qL qR : ℝ → ℝ)
    (hqL : ContDiffOn ℝ ∞ qL U) (hqR : ContDiffOn ℝ ∞ qR V)
    (hB : qL =ᶠ[𝓝 B] qR)
    (hleft : ∀ x ∈ W, x ≤ B → x ∈ U) (hright : ∀ x ∈ W, B ≤ x → x ∈ V) :
    ContDiffOn ℝ ∞ (radialCapSmoothingGlue B qL qR) W := by
  intro x hx
  rcases radialCapSmoothingGlue_local qL qR hB (x := x) with ⟨hxB, he⟩ | ⟨hBx, he⟩
  · exact ((hqL x (hleft x hx hxB.le)).contDiffAt (hU.mem_nhds (hleft x hx hxB.le))).congr_of_eventuallyEq he |>.contDiffWithinAt
  · exact ((hqR x (hright x hx hBx)).contDiffAt (hV.mem_nhds (hright x hx hBx))).congr_of_eventuallyEq he |>.contDiffWithinAt

theorem radialCapSmoothingGlue_second_negative {B : ℝ} {U V W : Set ℝ}
    (qL qR : ℝ → ℝ) (hB : qL =ᶠ[𝓝 B] qR)
    (hleft : ∀ x ∈ W, x ≤ B → x ∈ U) (hright : ∀ x ∈ W, B ≤ x → x ∈ V)
    (hqL : ∀ x ∈ U, deriv (deriv qL) x < 0)
    (hqR : ∀ x ∈ V, deriv (deriv qR) x < 0) :
    ∀ x ∈ W, deriv (deriv (radialCapSmoothingGlue B qL qR)) x < 0 := by
  intro x hx
  rcases radialCapSmoothingGlue_local qL qR hB (x := x) with ⟨hxB, he⟩ | ⟨hBx, he⟩
  · rw [he.deriv.deriv_eq]; exact hqL x (hleft x hx hxB.le)
  · rw [he.deriv.deriv_eq]; exact hqR x (hright x hx hBx)

theorem radialCapSmoothing_deriv_positive_before_endpoint {q : ℝ → ℝ} {u R e : ℝ}
    (he : 0 < e) (hu : u < R) (hq : ContDiffOn ℝ ∞ q (Ioo u (R + e)))
    (hsecond : ∀ x ∈ Ioo u (R + e), deriv (deriv q) x < 0)
    (hend : deriv q R = 0) : ∀ x ∈ Ioo u R, 0 < deriv q x := by
  have hq₁ := (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioo).mp hq |>.2
  have hanti := strictAntiOn_of_deriv_neg (convex_Ioo u (R + e)) hq₁.continuousOn
    (fun x hx => hsecond x (interior_subset hx))
  intro x hx
  have h := hanti ⟨hx.1, by linarith [hx.2]⟩ ⟨hu, by linarith⟩ hx.2
  rwa [hend] at h

end
end TightVer401
