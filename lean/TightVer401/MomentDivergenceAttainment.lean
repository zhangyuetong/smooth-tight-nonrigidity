import TightVer401.MomentDivergencePath

namespace TightVer401
noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

theorem momentDivergence_ivt_attainment {A : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {L t B : ℝ}
    (hL : 0 ≤ L) (ht : 0 ≤ t) (hA : Continuous A.uncurry) (hg : Continuous g)
    (hpos : ∀ u ∈ Icc 0 t, ∀ r, 0 < A u r)
    (hlo : momentNonlinearPeriod (A 0) g L ≤ B)
    (hhi : B ≤ momentNonlinearPeriod (A t) g L) :
    ∃ u ∈ Icc 0 t, momentNonlinearPeriod (A u) g L = B := by
  have hA' : Continuous (Function.uncurry (fun x : Icc (0 : ℝ) t => A x.val)) := by
    exact hA.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hc : Continuous (fun x : Icc (0 : ℝ) t => momentNonlinearPeriod (A x.val) g L) :=
    momentNonlinearPeriod_continuous hA' hg (fun x r => hpos x.val x.property r) hL
  have hcOn : ContinuousOn (fun u => momentNonlinearPeriod (A u) g L) (Icc 0 t) :=
    continuousOn_iff_continuous_restrict.mpr hc
  exact intermediate_value_Icc ht hcOn ⟨hlo, hhi⟩

theorem momentDivergence_path_attain_above {n : ℕ} {b χ g : ℝ → ℝ} {c : Fin n → ℝ}
    {ψ : Fin n → ℝ → ℝ} {L u v δ B : ℝ}
    (hb : ContDiff ℝ ∞ b) (hχ : ContDiff ℝ ∞ χ) (hψ : ∀ j, ContDiff ℝ ∞ (ψ j))
    (hg : Continuous g) (hbpos : ∀ r, 0 < b r) (hδ : 0 < δ)
    (hχbound : ∀ r, 0 ≤ χ r ∧ χ r ≤ 1)
    (hdisjoint : ∀ r, χ r ≠ 0 → ∀ j, ψ j r = 0)
    (hcontrol : ∀ r, χ r = 0 → δ ≤ b r - ∑ j, |c j| * |ψ j r|)
    (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ L)
    (hplateau : ∀ r ∈ Icc u v, χ r = 1)
    (hgsign : ∀ r ∈ Icc 0 L, χ r ≠ 0 → 0 ≤ g r)
    (hgpos : ∀ r ∈ Icc u v, 0 < g r)
    (hB : momentNonlinearPeriod b g L ≤ B) :
    ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧ momentNonlinearPeriod (momentPath b χ c ψ t) g L = B := by
  obtain ⟨t₁, ht₁, ht₁one, hBhi⟩ := momentDivergence_path_unbounded
    hb hχ hψ hg hbpos hδ hχbound hdisjoint hcontrol hu huv hv hplateau hgsign hgpos B
  have hjoint : Continuous (momentPath b χ c ψ).uncurry :=
    (momentPath_joint_contDiff c hb hχ hψ).continuous
  have hpos : ∀ t ∈ Icc 0 t₁, ∀ r, 0 < momentPath b χ c ψ t r := by
    intro t ht r
    exact momentPath_pos ht.1 (ht.2.trans_lt ht₁one) (hbpos r) (hχbound r)
      (hdisjoint r) (fun hz => by have hbnd := hcontrol r hz; linarith)
  have hBzero : momentNonlinearPeriod (momentPath b χ c ψ 0) g L ≤ B := by
    rw [momentPath_at_zero]
    exact hB
  obtain ⟨t, ht, htarget⟩ := momentDivergence_ivt_attainment
    (hu.trans (huv.le.trans hv)) ht₁ hjoint hg hpos hBzero hBhi.le
  exact ⟨t, ht.1, ht.2.trans_lt ht₁one, htarget⟩

end
end TightVer401
