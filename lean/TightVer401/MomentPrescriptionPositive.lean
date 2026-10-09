import TightVer401.MomentSlowdownConstruction
import TightVer401.MomentControlBasis
import TightVer401.MomentPrescriptionCircleLift
import TightVer401.MomentPrescriptionSigns
import TightVer401.MomentPrescriptionArcLength

namespace TightVer401
noncomputable section
open Set MeasureTheory Metric
open scoped ContDiff Manifold
set_option backward.isDefEq.respectTransparency false

theorem momentPrescription_circle_above {m : ℕ} (L : ℝ) [Fact (0 < L)]
    (f : AddCircle L → EuclideanSpace ℝ (Fin m)) (g b : AddCircle L → ℝ)
    (hf : Continuous f) (hfSmooth : ContDiff ℝ ∞ (f ∘ periodProjection L))
    (hg : Continuous g) (hb : ContDiff ℝ ∞ (b ∘ periodProjection L))
    (hbpos : ∀ q, 0 < b q) (hgpos : ∃ q, 0 < g q) {η ε B : ℝ}
    (hη : 0 < η) (hε : 0 < ε)
    (hB : momentNonlinearPeriod (b ∘ periodProjection L) (g ∘ periodProjection L) L ≤ B) :
    letI := periodCircleChartedSpace L
    ∃ A : AddCircle L → ℝ, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ A ∧
      (∀ q, 0 < A q) ∧
      (∫ r in 0..L, ‖A (periodProjection L r) - b (periodProjection L r)‖) < η ∧
      (∫ r in 0..L, A (periodProjection L r) • f (periodProjection L r)) =
        (∫ r in 0..L, b (periodProjection L r) • f (periodProjection L r)) ∧
      (∫ r in 0..L, g (periodProjection L r) / Real.sqrt (A (periodProjection L r))) = B ∧
      ∃ centers radii : Fin (Module.finrank ℝ (circleMomentSpan L f) + 1) → ℝ,
        (∀ j, 0 ≤ radii j) ∧ (∑ j, 2 * radii j) < ε ∧
        Function.support (fun q => A q - b q) ⊆
          ⋃ j, periodProjection L '' Icc (centers j - radii j) (centers j + radii j) := by
  letI := periodCircleChartedSpace L
  rw [circleMomentSpan_eq_representative L hf]
  let f₀ := f ∘ periodProjection L
  let b₀ := b ∘ periodProjection L
  let g₀ := g ∘ periodProjection L
  let d := Module.finrank ℝ (momentSampleSpan f₀ (Ioo 0 L))
  have hbL : Function.Periodic b₀ L := by
    intro s
    change b ((s + L : ℝ) : AddCircle L) = b (s : AddCircle L)
    rw [AddCircle.coe_add_period]
  have hbpositive : ∀ s, 0 < b₀ s := fun s => hbpos _
  have hgcontinuous : Continuous g₀ := hg.comp (AddCircle.continuous_mk' L)
  obtain ⟨a, ha, hga⟩ := momentPrescription_positive_center L hg hgpos
  have htol : 0 < ε / (d + 1 : ℝ) / 2 := by positivity
  obtain ⟨R, ψ, hR, hRε, hleft, hright, hψ, hψnonneg, hψmass, hψinside,
    hψshape, _hψpair, hψaway, hψLI, _hψspan⟩ :=
    exists_short_independent_interval_controls (f := f₀) hfSmooth.continuous ha htol
  have hψcompact (j) : HasCompactSupport (ψ j) := by
    obtain ⟨c, hc⟩ := hψshape j
    change IsCompact (tsupport (ψ j))
    rw [hc]
    exact isCompact_Icc
  obtain ⟨T, C, _hC, hT⟩ := exists_bounded_interval_moment_coordinates ψ
    (fun j => subset_closure.trans (hψinside j)) hψLI
  obtain ⟨D⟩ := exists_momentSlowdown_data L ψ ha hR hR hη hb hbL hbpositive
    hfSmooth.continuous hgcontinuous hga hψ hψcompact hψinside hψnonneg hψmass hψaway
    T (fun u => (hT u).1)
  let χ := momentSlowdownChi L a D.r D.hr
  let Ψ := fun j => momentPeriodicRepresentative L (ψ j)
  obtain ⟨a₀, ha₀, ha₀L, ha₀pos, hsmall, hmoment, htarget, hsupport⟩ :=
    momentPrescription_from_controls hb D.smooth D.controls_smooth hgcontinuous
      hfSmooth.continuous hbpositive D.δpos hbL D.periodic D.controls_periodic D.bound
      D.disjoint D.control D.balance D.small
      (show 0 ≤ a - D.r / 2 by linarith [D.left, D.hr])
      (show a - D.r / 2 < a + D.r / 2 by linarith [D.hr])
      (show a + D.r / 2 ≤ L by linarith [D.right, D.hr]) D.plateau
      (Or.inl ⟨hB, fun s hs hχ => (D.sign s hs hχ).le, D.plateau_sign⟩)
  obtain ⟨A, hASmooth, hA, hApos, hAsmall, hAmoment, hAtarget⟩ :=
    momentPrescription_lift_to_circle L b g f ha₀ ha₀L ha₀pos hsmall hmoment htarget
  let χcircle := momentPeriodicCircleControl L (momentControlBump a D.r D.hr)
  let Ψcircle := fun j => momentPeriodicCircleControl L (ψ j)
  have hcircsupport : Function.support (fun q => A q - b q) ⊆
      Function.support χcircle ∪ ⋃ j, Function.support (Ψcircle j) :=
    momentPrescription_circle_support L hA hsupport
  have hχarc : ∃ c r : ℝ, 0 ≤ r ∧ 2 * r < ε / (d + 1 : ℝ) ∧
      Function.support χcircle ⊆ periodProjection L '' Icc (c - r) (c + r) := by
    refine ⟨a, D.r, D.hr.le, by linarith [D.rR], ?_⟩
    have hh := momentPeriodicCircleControl_support L (momentControlBump a D.r D.hr)
    simpa only [momentSlowdown_bump_tsupport D.hr] using hh
  have hΨarc (j) : ∃ c r : ℝ, 0 ≤ r ∧ 2 * r < ε / (d + 1 : ℝ) ∧
      Function.support (Ψcircle j) ⊆ periodProjection L '' Icc (c - r) (c + r) := by
    obtain ⟨c, hc⟩ := hψshape j
    refine ⟨c, R, hR.le, by linarith, ?_⟩
    simpa only [hc] using momentPeriodicCircleControl_support L (ψ j)
  exact ⟨A, hASmooth, hApos, hAsmall, hAmoment, hAtarget,
    momentPrescription_circle_arcs_total L hcircsupport hχarc hΨarc⟩

end
end TightVer401

