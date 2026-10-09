import OAI.Geometry.SurfaceImmersion.Primitive.PeriodicPrimitive

namespace TightVer401
noncomputable section
open Set

variable {E : Type*} [NormedAddCommGroup E]

theorem speedCurve_baseline_distinct {L δ x y : ℝ} {c : ℝ → E}
    (hδ : 0 < δ) (hinj : Set.InjOn c (Ico 0 L)) (hperiod : c L = c 0)
    (hx : x ∈ Icc 0 L) (hy : y ∈ Icc 0 L)
    (hgap : δ ≤ |x - y|) (hwrap : |x - y| ≤ L - δ) : c x ≠ c y := by
  intro he
  by_cases hxL : x = L
  · subst x
    by_cases hyL : y = L
    · subst y; simp only [sub_self, abs_zero] at hgap; linarith
    · have hy' : y ∈ Ico 0 L := ⟨hy.1, lt_of_le_of_ne hy.2 hyL⟩
      have h0 : (0 : ℝ) ∈ Ico 0 L := ⟨le_rfl, hy.1.trans_lt hy'.2⟩
      have hy0 : y = 0 := hinj hy' h0 (he.symm.trans hperiod)
      rw [hy0, sub_zero, abs_of_nonneg h0.2.le] at hwrap
      linarith
  · by_cases hyL : y = L
    · subst y
      have hx' : x ∈ Ico 0 L := ⟨hx.1, lt_of_le_of_ne hx.2 hxL⟩
      have h0 : (0 : ℝ) ∈ Ico 0 L := ⟨le_rfl, hx.1.trans_lt hx'.2⟩
      have hx0 : x = 0 := hinj hx' h0 (he.trans hperiod)
      rw [hx0, zero_sub, abs_neg, abs_of_nonneg h0.2.le] at hwrap
      linarith
    · have hxy := hinj ⟨hx.1, lt_of_le_of_ne hx.2 hxL⟩
        ⟨hy.1, lt_of_le_of_ne hy.2 hyL⟩ he
      rw [hxy, sub_self, abs_zero] at hgap
      linarith

theorem exists_speedCurve_distant_separation {L δ : ℝ} (hδ : 0 < δ)
    (c : ℝ → E) (hc : Continuous c) (hinj : Set.InjOn c (Ico 0 L)) (hperiod : c L = c 0) :
    ∃ ρ > 0, ∀ x ∈ Icc 0 L, ∀ y ∈ Icc 0 L,
      δ ≤ |x - y| → |x - y| ≤ L - δ → ρ ≤ ‖c x - c y‖ := by
  let K : Set (ℝ × ℝ) := (Icc 0 L ×ˢ Icc 0 L) ∩
    {p | δ ≤ |p.1 - p.2|} ∩ {p | |p.1 - p.2| ≤ L - δ}
  have hK : IsCompact K := ((isCompact_Icc.prod isCompact_Icc).inter_right
    (isClosed_le continuous_const ((continuous_fst.sub continuous_snd).abs))).inter_right
    (isClosed_le ((continuous_fst.sub continuous_snd).abs) continuous_const)
  have hf : Continuous (fun p : ℝ × ℝ => ‖c p.1 - c p.2‖) :=
    ((hc.comp continuous_fst).sub (hc.comp continuous_snd)).norm
  by_cases hne : K.Nonempty
  · obtain ⟨p, hp, hmin⟩ := hK.exists_isMinOn hne hf.continuousOn
    have hn : c p.1 ≠ c p.2 := speedCurve_baseline_distinct hδ hinj hperiod
      hp.1.1.1 hp.1.1.2 hp.1.2 hp.2
    refine ⟨‖c p.1 - c p.2‖, norm_pos_iff.mpr (sub_ne_zero.mpr hn), ?_⟩
    intro x hx y hy hg hw
    exact hmin (show (x, y) ∈ K from ⟨⟨⟨hx, hy⟩, hg⟩, hw⟩)
  · refine ⟨1, by norm_num, ?_⟩
    intro x hx y hy hg hw
    exact False.elim (hne ⟨(x, y), ⟨⟨⟨hx, hy⟩, hg⟩, hw⟩⟩)

end
end TightVer401
