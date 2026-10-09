import TightVer401.BandBendingMetricStability
import TightVer401.BandBendingMetricPeriodicity
import TightVer401.BandLiftStrain
import TightVer401.SeamPeriodicity

/-! A uniform curvature bound for an actual supported bending of the constructed
periodic ruled band. The lifted support is periodic rather than compact; one
compact fundamental rectangle and actual curvature periodicity suffice. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Manifold Topology
set_option backward.isDefEq.respectTransparency false

/-- Small actual bendings preserve strict negative intrinsic curvature throughout
all physical band coordinates. No perturbed embedding is asserted. -/
theorem periodicRuledFrame_supported_bending_curvature_threshold
    {L b lower upper : ℝ} [Fact (0 < L)] (d : PeriodicRuledFrame L)
    {Y : AddCircle L × Ioo (0 : ℝ) b → Ambient}
    (hY : IsBandBending (d.bandMap (b := b)) Y)
    (hlower : 0 < lower) (hupper : upper < b)
    (hsupport : ∀ p ∈ tsupport Y, lower ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ upper) :
    ∃ δ > 0, ∀ a : ℝ, |a| < δ → ∀ p : Coord,
      gaussianCurvature (inducedMetric
        (fun q => ruledMap d.γ d.E q + a • bandCoordinateLift Y q)) p < 0 := by
  have hX : ContDiff ℝ ∞ (ruledMap d.γ d.E) :=
    (d.smooth_γ.comp (contDiff_apply ℝ ℝ 0)).add
      ((contDiff_apply ℝ ℝ 1).smul (d.smooth_E.comp (contDiff_apply ℝ ℝ 0)))
  have hYs := bandCoordinateLift_contDiff hY.1 hlower hupper hsupport
  have hB : IsInfinitesimalBendingOn (ruledMap d.γ d.E) (bandCoordinateLift Y) univ :=
    ⟨hYs.contDiffOn, fun p _ i j =>
      bandCoordinateLift_zero_strain d hY hlower hupper hsupport p i j⟩
  have himm (p : Coord) : Function.Injective (fderiv ℝ (ruledMap d.γ d.E) p) :=
    ruled_differential_injective (d.deriv_γ (p 0)) (d.deriv_E (p 0))
      (d.orthonormal (p 0)) (d.torsion_ne_zero (p 0))
  have hneg (p : Coord) : gaussianCurvature (inducedMetric (ruledMap d.γ d.E)) p < 0 :=
    ruled_gaussianCurvature_neg d.deriv_γ d.deriv_E hX.contDiffOn isOpen_univ
      (fun q _ => d.orthonormal (q 0)) (fun q _ => d.torsion_ne_zero (q 0)) (mem_univ _)
  let K : Set Coord := (fun z : ℝ × ℝ => (![z.1, z.2] : Coord)) ''
    (Icc (0 : ℝ) L ×ˢ Icc lower upper)
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).image
    ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.continuous)
  obtain ⟨δ, hδ, hbound⟩ := bandBending_compact_actual_curvature_threshold
    hX.contDiffOn hB isOpen_univ (fun p _ => himm p) hK
    (subset_univ K) (fun p _ => hneg p)
  refine ⟨δ, hδ, fun a ha p => ?_⟩
  by_cases hp : p 1 ∈ Icc lower upper
  · have hAs : ContDiff ℝ ∞
        (fun q => ruledMap d.γ d.E q + a • bandCoordinateLift Y q) :=
      hX.add ((contDiff_const : ContDiff ℝ ∞ (fun _ : Coord => a)).smul hYs)
    have hAi (q : Coord) : Function.Injective
        (fderiv ℝ (fun r => ruledMap d.γ d.E r + a • bandCoordinateLift Y r) q) :=
      bandBending_coordinate_branch_immersion (hX.differentiable (by simp) q)
        (hYs.differentiable (by simp) q) (hB.2 q (mem_univ _)) (himm q) a
    have hAp (q : Coord) :
        ruledMap d.γ d.E (smoothingSeamShift L q) + a • bandCoordinateLift Y (smoothingSeamShift L q) =
        ruledMap d.γ d.E q + a • bandCoordinateLift Y q := by
      have hYp := bandCoordinateLift_periodic Y (q 1) (q 0)
      change bandCoordinateLift Y (![q 0 + L, q 1] : Coord) =
        bandCoordinateLift Y (![q 0, q 1] : Coord) at hYp
      have hq : (![q 0, q 1] : Coord) = q := by ext i; fin_cases i <;> rfl
      simp only [smoothingSeamShift, ruledMap, Matrix.cons_val_zero, Matrix.cons_val_one,
        d.period_γ (q 0), d.period_E (q 0)]
      rw [hYp, hq]
    have hperiod := bandBending_actual_curvature_periodic hAs hAp hAi (p 1)
    have heq := seam_periodic_eq_representative (Fact.out : 0 < L) hperiod (p 0)
    have hrepr : (![toIcoMod (Fact.out : 0 < L) 0 (p 0), p 1] : Coord) ∈ K := by
      refine ⟨(toIcoMod (Fact.out : 0 < L) 0 (p 0), p 1), ⟨?_, hp⟩, rfl⟩
      exact Ico_subset_Icc_self (toIcoMod_mem_Ico' (Fact.out : 0 < L) (p 0))
    have hq : (![p 0, p 1] : Coord) = p := by ext i; fin_cases i <;> rfl
    rw [hq] at heq
    rw [heq]
    exact hbound a ha _ hrepr
  · have hout : p ∉ tsupport (bandCoordinateLift Y) :=
      fun hs => hp (bandCoordinateLift_support_bounds hsupport hs)
    have houta : p ∉ tsupport (fun q => a • bandCoordinateLift Y q) :=
      fun hs => hout (tsupport_smul_subset_right (fun _ : Coord => a) (bandCoordinateLift Y) hs)
    rw [curvature_unchanged_off_support (ruledMap d.γ d.E)
      (fun q => a • bandCoordinateLift Y q) houta]
    exact hneg p

/-- Compactness supplies the height bounds; the caller provides no curvature-stability grant. -/
theorem periodicRuledFrame_compact_bending_curvature_threshold
    {L b : ℝ} [Fact (0 < L)] (d : PeriodicRuledFrame L) (hb : 0 < b)
    {Y : AddCircle L × Ioo (0 : ℝ) b → Ambient}
    (hY : IsBandBending (d.bandMap (b := b)) Y) (hcompact : HasCompactSupport Y) :
    ∃ δ > 0, ∀ a : ℝ, |a| < δ → ∀ p : Coord,
      gaussianCurvature (inducedMetric
        (fun q => ruledMap d.γ d.E q + a • bandCoordinateLift Y q)) p < 0 := by
  obtain ⟨lower, upper, hlo, _, hhi, hs⟩ := compact_band_support_uniform_bounds hb hcompact
  exact periodicRuledFrame_supported_bending_curvature_threshold d hY hlo hhi hs

end
end TightVer401
