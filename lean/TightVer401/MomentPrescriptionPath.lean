import TightVer401.MomentDivergenceSigned

namespace TightVer401
noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

theorem momentPrescription_path_eq_base {n : ℕ} (b χ : ℝ → ℝ) (c : Fin n → ℝ)
    (ψ : Fin n → ℝ → ℝ) (t r : ℝ) (hχ : χ r = 0) (hψ : ∀ j, ψ j r = 0) :
    momentPath b χ c ψ t r = b r := by
  simp [momentPath, momentPathCorrection, hχ, hψ]

theorem momentPrescription_path_support {n : ℕ} (b χ : ℝ → ℝ) (c : Fin n → ℝ)
    (ψ : Fin n → ℝ → ℝ) (t : ℝ) :
    Function.support (fun r => momentPath b χ c ψ t r - b r) ⊆
      Function.support χ ∪ ⋃ j, Function.support (ψ j) := by
  intro r hr
  by_contra hout
  have hχ : χ r = 0 := by
    simpa only [mem_union, not_or, Function.mem_support, not_not] using (not_or.mp hout).1
  have hψ : ∀ j, ψ j r = 0 := by
    intro j
    have hj : r ∉ Function.support (ψ j) := fun hh => (not_or.mp hout).2 (mem_iUnion.mpr ⟨j, hh⟩)
    simpa only [Function.mem_support, not_not] using hj
  exact hr (by
    change momentPath b χ c ψ t r - b r = 0
    rw [momentPrescription_path_eq_base b χ c ψ t r hχ hψ, sub_self])

theorem momentPrescription_from_controls {n m : ℕ} {b χ g : ℝ → ℝ} {c : Fin n → ℝ}
    {ψ : Fin n → ℝ → ℝ} {f : ℝ → EuclideanSpace ℝ (Fin m)} {L u v δ η B : ℝ}
    (hb : ContDiff ℝ ∞ b) (hχ : ContDiff ℝ ∞ χ) (hψ : ∀ j, ContDiff ℝ ∞ (ψ j))
    (hg : Continuous g) (hf : Continuous f) (hbpos : ∀ r, 0 < b r) (hδ : 0 < δ)
    (hbL : Function.Periodic b L) (hχL : Function.Periodic χ L)
    (hψL : ∀ j, Function.Periodic (ψ j) L)
    (hχbound : ∀ r, 0 ≤ χ r ∧ χ r ≤ 1)
    (hdisjoint : ∀ r, χ r ≠ 0 → ∀ j, ψ j r = 0)
    (hcontrol : ∀ r, χ r = 0 → δ ≤ b r - ∑ j, |c j| * |ψ j r|)
    (hbalance : (∑ j, c j • momentPathMoment L f (ψ j)) =
      momentPathMoment L f (fun r => χ r * b r))
    (hsmall : (∫ r in 0..L, |χ r * b r|) +
      (∑ j, |c j| * (∫ r in 0..L, |ψ j r|)) < η)
    (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ L)
    (hplateau : ∀ r ∈ Icc u v, χ r = 1)
    (hdirection :
      (momentNonlinearPeriod b g L ≤ B ∧
        (∀ r ∈ Icc 0 L, χ r ≠ 0 → 0 ≤ g r) ∧ (∀ r ∈ Icc u v, 0 < g r)) ∨
      (B ≤ momentNonlinearPeriod b g L ∧
        (∀ r ∈ Icc 0 L, χ r ≠ 0 → g r ≤ 0) ∧ (∀ r ∈ Icc u v, g r < 0))) :
    ∃ a : ℝ → ℝ, ContDiff ℝ ∞ a ∧ Function.Periodic a L ∧ (∀ r, 0 < a r) ∧
      (∫ r in 0..L, ‖a r - b r‖) < η ∧
      momentPathMoment L f a = momentPathMoment L f b ∧ momentNonlinearPeriod a g L = B ∧
      Function.support (fun r => a r - b r) ⊆ Function.support χ ∪ ⋃ j, Function.support (ψ j) := by
  have hattain : ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧
      momentNonlinearPeriod (momentPath b χ c ψ t) g L = B := by
    rcases hdirection with ⟨hB, hgsign, hgpos⟩ | ⟨hB, hgsign, hgneg⟩
    · exact momentDivergence_path_attain_above hb hχ hψ hg hbpos hδ hχbound hdisjoint
        hcontrol hu huv hv hplateau hgsign hgpos hB
    · exact momentDivergence_path_attain_below hb hχ hψ hg hbpos hδ hχbound hdisjoint
        hcontrol hu huv hv hplateau hgsign hgneg hB
  obtain ⟨t, ht, ht1, htarget⟩ := hattain
  refine ⟨momentPath b χ c ψ t, momentPath_contDiff c hb hχ hψ t,
    momentPath_periodic c hbL hχL hψL t, ?_,
    momentPath_l1_lt (hu.trans (huv.le.trans hv)) c hb hχ hψ hsmall ht ht1,
    momentPathMoment_eq L c hb.continuous hχ.continuous (fun j => (hψ j).continuous)
      hf hbalance t, htarget, momentPrescription_path_support b χ c ψ t⟩
  intro r
  exact momentPath_pos ht ht1 (hbpos r) (hχbound r) (hdisjoint r)
    (fun hz => by have hbound := hcontrol r hz; linarith)

end
end TightVer401
