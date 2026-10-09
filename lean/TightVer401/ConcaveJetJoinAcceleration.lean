import TightVer401.ConcaveJetJoinControl
import TightVer401.ConcaveJetJoinBlendSmallness
import TightVer401.ConcaveJetJoinBlendSpan
import TightVer401.MomentControlBasis
import TightVer401.MomentControlCoefficients

namespace TightVer401
noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

/-- Actual moment-preserving smoothing of a positive piecewise acceleration.
The controls and the radius are constructed, and the inverse bound determines
the required smallness of the actual blend error. -/
theorem exists_concaveJetJoin_acceleration {m : ℕ} {L c : ℝ}
    (hc : c ∈ Ioo 0 L) (f : ℝ → EuclideanSpace ℝ (Fin m)) (hf : Continuous f)
    {hL hR : ℝ → ℝ} (hfL : ContDiff ℝ ∞ hL) (hfR : ContDiff ℝ ∞ hR)
    {μ : ℝ} (hμ : 0 < μ)
    (hleft : ∀ x ∈ Icc 0 L, μ ≤ hL x) (hright : ∀ x ∈ Icc 0 L, μ ≤ hR x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (r : ℝ) (ψ : Fin (Module.finrank ℝ (momentSampleSpan f (Ioo 0 L))) → ℝ → ℝ)
      (a : ℝ → ℝ),
      0 < r ∧ r < ε ∧ 0 < c - r ∧ c + r < L ∧
      (∀ j, ContDiff ℝ ∞ (ψ j)) ∧ (∀ j, tsupport (ψ j) ⊆ Ioo 0 L) ∧
      ContDiff ℝ ∞ a ∧ (∀ x ∈ Icc 0 L, 0 < a x) ∧
      jetAccelerationMoment 0 L f a =
        jetAccelerationMoment 0 L f (concaveJetJoinBlendPiecewise c hL hR) ∧
      Function.support (fun x => a x - concaveJetJoinBlendAcceleration c r hL hR x)
        ⊆ ⋃ j, Function.support (ψ j) := by
  obtain ⟨R, ψ, hRpos, _, hcR, hRL, hψ, _, _, hψS, _, _, _, hLI, _⟩ :=
    exists_short_independent_interval_controls hf hc (show 0 < (1 : ℝ) by norm_num)
  have hψsupport (j) : Function.support (ψ j) ⊆ Ioo 0 L := subset_closure.trans (hψS j)
  obtain ⟨T, C, hC, hT⟩ := exists_bounded_interval_moment_coordinates ψ hψsupport hLI
  obtain ⟨η, hη, hsolve⟩ := exists_jetAccelerationControl_threshold 0 L f hf ψ hψ
    (momentSampleSpan f (Ioo 0 L)) T (fun u => (hT u).1) hμ
  obtain ⟨r, hr, hrR, hrε, hi, hsmall⟩ := exists_concaveJetJoinBlend_small_radius
    hRpos hη hε hcR.le hRL.le hfL hfR hf
  have hl : 0 ≤ c - r := by linarith
  have hu : c + r ≤ L := by linarith
  have hmem := concaveJetJoinBlendError_moment_mem_span hr hL hR f hl hu
  have hbase (x) (hx : x ∈ Icc 0 L) : μ ≤ concaveJetJoinBlendAcceleration c r hL hR x :=
    concaveJetJoinBlendAcceleration_lower (hleft x hx) (hright x hx)
  obtain ⟨a, ha, hapos, hmoment, hsupp⟩ := hsolve
    (concaveJetJoinBlendAcceleration c r hL hR) (concaveJetJoinBlendPiecewise c hL hR)
    (concaveJetJoinBlendAcceleration_contDiff hfL hfR)
    (concaveJetJoinBlendPiecewise_intervalIntegrable hfL.continuous hfR.continuous hf)
    hbase hmem hsmall
  exact ⟨r, ψ, a, hr, hrε, by linarith, by linarith, hψ, hψS, ha, hapos, hmoment, hsupp⟩

end
end TightVer401
