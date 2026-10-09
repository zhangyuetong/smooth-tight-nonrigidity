import TightVer401.PeriodicCircleFunctions
import Mathlib

namespace TightVer401
noncomputable section
open Set Filter MeasureTheory AddCommGroup
open scoped ContDiff Topology Manifold

def momentPeriodicCircleControl (L : ℝ) [Fact (0 < L)] (ψ : ℝ → ℝ) : AddCircle L → ℝ :=
  AddCircle.liftIco L 0 ψ

def momentPeriodicRepresentative (L : ℝ) [Fact (0 < L)] (ψ : ℝ → ℝ) : ℝ → ℝ :=
  momentPeriodicCircleControl L ψ ∘ periodProjection L

theorem momentPeriodicRepresentative_periodic (L : ℝ) [Fact (0 < L)] (ψ : ℝ → ℝ) :
    Function.Periodic (momentPeriodicRepresentative L ψ) L := by
  intro s
  change momentPeriodicCircleControl L ψ ((s + L : ℝ) : AddCircle L) =
    momentPeriodicCircleControl L ψ (s : AddCircle L)
  rw [AddCircle.coe_add_period]

theorem momentPeriodicControl_endpoints {L : ℝ} {ψ : ℝ → ℝ}
    (hinside : tsupport ψ ⊆ Ioo 0 L) : ψ 0 = 0 ∧ ψ L = 0 := by
  constructor
  · apply image_eq_zero_of_notMem_tsupport
    intro h
    have := (hinside h).1
    linarith
  · apply image_eq_zero_of_notMem_tsupport
    intro h
    have := (hinside h).2
    linarith

theorem momentPeriodicRepresentative_eqOn (L : ℝ) [hL : Fact (0 < L)] {ψ : ℝ → ℝ}
    (hinside : tsupport ψ ⊆ Ioo 0 L) : EqOn (momentPeriodicRepresentative L ψ) ψ (Icc 0 L) := by
  intro s hs
  have he := momentPeriodicControl_endpoints hinside
  by_cases hlt : s < L
  · exact AddCircle.liftIco_coe_apply (by simpa using (⟨hs.1, hlt⟩ : s ∈ Ico 0 L))
  · have hsL : s = L := by linarith [hs.2]
    subst s
    change AddCircle.liftIco L 0 ψ (L : AddCircle L) = ψ L
    rw [AddCircle.coe_period]
    have hzero : (0 : ℝ) ∈ Ico 0 (0 + L) := by simp [hL.out]
    rw [← AddCircle.coe_zero, AddCircle.liftIco_coe_apply hzero, he.1, he.2]

theorem momentPeriodicCircleControl_nonneg (L : ℝ) [Fact (0 < L)] {ψ : ℝ → ℝ}
    (hψ : ∀ s, 0 ≤ ψ s) (q : AddCircle L) : 0 ≤ momentPeriodicCircleControl L ψ q :=
  hψ ((AddCircle.equivIco L 0 q : Ico 0 (0 + L)) : ℝ)

theorem momentPeriodicRepresentative_nonneg (L : ℝ) [Fact (0 < L)] {ψ : ℝ → ℝ}
    (hψ : ∀ s, 0 ≤ ψ s) (s : ℝ) : 0 ≤ momentPeriodicRepresentative L ψ s :=
  momentPeriodicCircleControl_nonneg L hψ (periodProjection L s)

theorem momentPeriodicCircleControl_support (L : ℝ) [Fact (0 < L)] (ψ : ℝ → ℝ) :
    Function.support (momentPeriodicCircleControl L ψ) ⊆ periodProjection L '' tsupport ψ := by
  intro q hq
  let r := AddCircle.equivIco L 0 q
  refine ⟨r.val, ?_, ?_⟩
  · apply subset_closure
    exact hq
  · exact AddCircle.coe_equivIco

theorem momentPeriodicCircleControl_tsupport (L : ℝ) [Fact (0 < L)] {ψ : ℝ → ℝ}
    (hcompact : HasCompactSupport ψ) :
    tsupport (momentPeriodicCircleControl L ψ) ⊆ periodProjection L '' tsupport ψ := by
  apply closure_minimal (momentPeriodicCircleControl_support L ψ)
  exact (hcompact.isCompact.image (AddCircle.continuous_mk' L)).isClosed

theorem momentPeriodicCircleControl_zero_not_support (L : ℝ) [hL : Fact (0 < L)]
    {ψ : ℝ → ℝ} (hinside : tsupport ψ ⊆ Ioo 0 L) :
    (0 : AddCircle L) ∉ periodProjection L '' tsupport ψ := by
  rintro ⟨r, hr, he⟩
  have hrr := hinside hr
  have hr0 : r = 0 := (AddCircle.coe_eq_zero_iff_of_mem_Ico
    (⟨hrr.1.le, hrr.2⟩ : r ∈ Ico 0 L)).mp he
  linarith [hrr.1]

theorem momentPeriodicRepresentative_contDiff (L : ℝ) [hL : Fact (0 < L)] {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hcompact : HasCompactSupport ψ)
    (hinside : tsupport ψ ⊆ Ioo 0 L) : ContDiff ℝ ∞ (momentPeriodicRepresentative L ψ) := by
  rw [contDiff_iff_contDiffAt]
  intro s
  by_cases hs : periodProjection L s = 0
  · have hclosed : IsClosed (periodProjection L '' tsupport ψ) :=
      (hcompact.isCompact.image (AddCircle.continuous_mk' L)).isClosed
    have hnot : periodProjection L s ∉ periodProjection L '' tsupport ψ := by
      rw [hs]
      exact momentPeriodicCircleControl_zero_not_support L hinside
    have hn := (AddCircle.continuous_mk' L).continuousAt.preimage_mem_nhds
      (hclosed.isOpen_compl.mem_nhds hnot)
    have he : momentPeriodicRepresentative L ψ =ᶠ[𝓝 s] (fun _ => (0 : ℝ)) := by
      filter_upwards [hn] with y hy
      apply Function.notMem_support.mp
      intro h
      exact hy (momentPeriodicCircleControl_support L ψ h)
    exact contDiffAt_const.congr_of_eventuallyEq he
  · have hm : ¬ s ≡ (0 : ℝ) [PMOD L] := by
      apply not_modEq_iff_ne_mod_zmultiples.mpr
      exact hs
    have he : momentPeriodicRepresentative L ψ =ᶠ[𝓝 s]
        (fun y => ψ (y - toIcoDiv hL.out 0 s • L)) := by
      filter_upwards [eventuallyEq_toIcoDiv_nhds hL.out 0 hm] with y hy
      change ψ (toIcoMod hL.out 0 y) = ψ (y - toIcoDiv hL.out 0 s • L)
      rw [toIcoMod, hy]
    exact (hψ.contDiffAt.comp s (contDiffAt_id.sub contDiffAt_const)).congr_of_eventuallyEq he

theorem momentPeriodicCircleControl_contMDiff (L : ℝ) [Fact (0 < L)] {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hcompact : HasCompactSupport ψ)
    (hinside : tsupport ψ ⊆ Ioo 0 L) :
    letI := periodCircleChartedSpace L
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (momentPeriodicCircleControl L ψ) :=
  periodCircle_descend_smooth L _ (momentPeriodicRepresentative_contDiff L hψ hcompact hinside)

theorem momentPeriodicRepresentative_intervalIntegral (L : ℝ) [hL : Fact (0 < L)]
    {ψ : ℝ → ℝ} (hinside : tsupport ψ ⊆ Ioo 0 L) :
    (∫ s in 0..L, momentPeriodicRepresentative L ψ s) = ∫ s in 0..L, ψ s := by
  apply intervalIntegral.integral_congr
  simpa only [uIcc_of_le hL.out.le] using momentPeriodicRepresentative_eqOn L hinside

theorem momentPeriodicCircleControl_arc (L : ℝ) [Fact (0 < L)] {ψ : ℝ → ℝ}
    (hcompact : HasCompactSupport ψ) {a b : ℝ} (hsupport : tsupport ψ ⊆ Icc a b) :
    tsupport (momentPeriodicCircleControl L ψ) ⊆ periodProjection L '' Icc a b :=
  (momentPeriodicCircleControl_tsupport L hcompact).trans (image_mono hsupport)

theorem momentPeriodicRepresentative_normalized (L : ℝ) [Fact (0 < L)]
    {ψ : ℝ → ℝ} (hinside : tsupport ψ ⊆ Ioo 0 L) (hmean : (∫ s in 0..L, ψ s) = 1) :
    (∫ s in 0..L, momentPeriodicRepresentative L ψ s) = 1 := by
  rw [momentPeriodicRepresentative_intervalIntegral L hinside, hmean]

theorem momentPeriodicRepresentative_intervalMoment {m : ℕ} (L : ℝ) [hL : Fact (0 < L)]
    {ψ : ℝ → ℝ} (hinside : tsupport ψ ⊆ Ioo 0 L)
    (f : ℝ → EuclideanSpace ℝ (Fin m)) :
    (∫ s in 0..L, momentPeriodicRepresentative L ψ s • f s) =
      ∫ s in 0..L, ψ s • f s := by
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le hL.out.le] at hs
  change momentPeriodicRepresentative L ψ s • f s = ψ s • f s
  rw [momentPeriodicRepresentative_eqOn L hinside hs]

theorem momentPeriodicCircleControl_disjoint (L : ℝ) [Fact (0 < L)] {ψ χ : ℝ → ℝ}
    (hψcompact : HasCompactSupport ψ) (hχcompact : HasCompactSupport χ)
    (hψinside : tsupport ψ ⊆ Ioo 0 L) (hχinside : tsupport χ ⊆ Ioo 0 L)
    (hdisjoint : Disjoint (tsupport ψ) (tsupport χ)) :
    Disjoint (tsupport (momentPeriodicCircleControl L ψ))
      (tsupport (momentPeriodicCircleControl L χ)) := by
  apply Set.disjoint_left.mpr
  intro q hqψ hqχ
  obtain ⟨a, ha, haq⟩ := momentPeriodicCircleControl_tsupport L hψcompact hqψ
  obtain ⟨b, hb, hbq⟩ := momentPeriodicCircleControl_tsupport L hχcompact hqχ
  have haI : a ∈ Ico 0 (0 + L) := by
    exact ⟨(hψinside ha).1.le, by simpa only [zero_add] using (hψinside ha).2⟩
  have hbI : b ∈ Ico 0 (0 + L) := by
    exact ⟨(hχinside hb).1.le, by simpa only [zero_add] using (hχinside hb).2⟩
  have hab : a = b := (AddCircle.coe_eq_coe_iff_of_mem_Ico haI hbI).mp (haq.trans hbq.symm)
  subst b
  exact Set.disjoint_left.mp hdisjoint ha hb

theorem momentPeriodicRepresentative_disjoint_zero (L : ℝ) [Fact (0 < L)] {ψ χ : ℝ → ℝ}
    (hψcompact : HasCompactSupport ψ) (hχcompact : HasCompactSupport χ)
    (hψinside : tsupport ψ ⊆ Ioo 0 L) (hχinside : tsupport χ ⊆ Ioo 0 L)
    (hdisjoint : Disjoint (tsupport ψ) (tsupport χ)) (s : ℝ)
    (hχ : momentPeriodicRepresentative L χ s ≠ 0) :
    momentPeriodicRepresentative L ψ s = 0 := by
  by_contra hψ
  have hp : periodProjection L s ∈ tsupport (momentPeriodicCircleControl L ψ) :=
    subset_closure hψ
  have hc : periodProjection L s ∈ tsupport (momentPeriodicCircleControl L χ) :=
    subset_closure hχ
  exact Set.disjoint_left.mp (momentPeriodicCircleControl_disjoint L hψcompact hχcompact
    hψinside hχinside hdisjoint) hp hc

end
end TightVer401
