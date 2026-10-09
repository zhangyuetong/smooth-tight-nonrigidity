import TightVer401.ParabolicConvexClosureMeridian
import TightVer401.ParabolicConvexClosurePerturbation

/-! Constructive meridian gate for the ver500 convex closure. All inputs are
the three ordinary positive parameters. Actual surface and convex-body
geometry is assembled separately from the constructed profile. -/
namespace TightVer401
noncomputable section
open Set
open scoped ContDiff

/-- Construct the actual strictly concave, positive and non-even meridian,
including the literal square-root germs at both closed endpoints. -/
theorem exists_parabolic_convex_meridian (RN mu h : ℝ)
    (hRN : 0 < RN) (hmu : 0 < mu) (hh : 0 < h) :
    ∃ r : ℝ → ℝ, ContinuousOn r (Icc (-h) h) ∧
      ContDiffOn ℝ ∞ r (Ioo (-h) h) ∧
      (∀ z ∈ Ioo (-h) h, deriv (deriv r) z < 0) ∧
      StrictConcaveOn ℝ (Icc (-h) h) r ∧ r (-h) = RN ∧ r h = RN ∧
      (∀ z ∈ Ioo (-h) h, RN < r z) ∧
      (∃ δ ∈ Ioo 0 h,
        EqOn r (fun z => RN + Real.sqrt (2 * mu * (h + z))) (Icc (-h) (-h + δ)) ∧
        EqOn r (fun z => RN + Real.sqrt (2 * mu * (h - z))) (Icc (h - δ) h)) ∧
      ∃ z ∈ Ioo 0 h, r (-z) ≠ r z := by
  obtain ⟨r0, hc0, hs0, hn0, _, hl0, hr0, hp0, ⟨δ, hδ, hgl0, hgr0⟩, hev0⟩ :=
    exists_even_parabolic_convex_meridian RN mu h hRN hmu hh
  obtain ⟨r, hc, hs, hn, hconc, hge, heq, hasym⟩ :=
    exists_parabolicConvexClosure_asymmetric_perturbation hh hc0 hs0 hn0 hev0
  have hl : r (-h) = RN := (heq _ (Or.inl (by linarith))).trans hl0
  have hr : r h = RN := (heq _ (Or.inr (by linarith))).trans hr0
  let δ' := min δ (h / 4)
  have hδ' : δ' ∈ Ioo 0 h :=
    ⟨lt_min hδ.1 (by positivity), (min_le_left _ _).trans_lt hδ.2⟩
  refine ⟨r, hc, hs, hn, hconc, hl, hr,
    fun z hz => (hp0 z hz).trans_le (hge z), ⟨δ', hδ', ?_, ?_⟩, hasym⟩
  · intro z hz
    have hzold : z ∈ Icc (-h) (-h + δ) :=
      ⟨hz.1, hz.2.trans (by dsimp [δ']; linarith [min_le_left δ (h / 4)])⟩
    have hzlow : z ≤ h / 4 := by
      have hdle : δ' ≤ h / 4 := min_le_right _ _
      linarith [hz.2]
    exact (heq z (Or.inl hzlow)).trans (hgl0 hzold)
  · intro z hz
    have hzold : z ∈ Icc (h - δ) h :=
      ⟨(by dsimp [δ'] at hz; linarith [min_le_left δ (h / 4), hz.1]), hz.2⟩
    have hzhigh : 3 * h / 4 ≤ z := by
      have hdle : δ' ≤ h / 4 := min_le_right _ _
      linarith [hz.1]
    exact (heq z (Or.inr hzhigh)).trans (hgr0 hzold)

end
end TightVer401
