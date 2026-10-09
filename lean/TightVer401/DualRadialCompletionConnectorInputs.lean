import TightVer401.DualRadialCompletionIncoming
import TightVer401.DualRadialCompletionExitTrace
import TightVer401.DualRadialCompletionTraceReflection
import TightVer401.VisibleConnectorContract

/-! Construct the two actual connector input data from the ordinary original
completion hypotheses. No incoming trace or connector package is assumed. -/
namespace TightVer401
noncomputable section
open Set Metric OAI.SmoothLocal.Geometry
open scoped ContDiff Topology RealInnerProductSpace Matrix ComplexConjugate
local instance : Fact ((0 : ℝ) < 1) := ⟨by norm_num⟩

private theorem connectorInputs_frontier {H : ℂ ≃ₜ ℂ} {f : ℝ → ℂ}
    (hf : DualRadialCompletionPositiveTrace H f) (t : ℝ) :
    f t ∈ frontier (H '' ball (0 : ℂ) 1) := by
  rw [← H.image_frontier, frontier_ball _ one_ne_zero,
    ← dualRadialCompletion_positiveTrace_range hf]
  exact mem_range_self t

private theorem connectorInputs_deriv {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (t : ℝ) :
    deriv (seamComplexCoord ∘ f) t = seamComplexCoord (deriv f t) :=
  (seamComplexCoord.hasFDerivAt.comp_hasDerivAt t
    (hf.differentiable (by simp) t).hasDerivAt).deriv

private theorem connectorInputs_dot (z w : ℂ) :
    seamComplexCoord z ⬝ᵥ seamComplexCoord w = inner ℝ z w := by
  rw [Complex.inner]
  simp only [seamComplexCoord_apply, dotProduct, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

private theorem connectorInputs_complexTrace (f : ℝ → ℂ) :
    positiveExitComplexTrace (seamComplexCoord ∘ f) = f := by
  funext t
  apply Complex.ext <;> rfl

private theorem connectorInputs_reflected_origin {H : ℂ ≃ₜ ℂ}
    (h0 : (0 : ℂ) ∈ H '' ball (0 : ℂ) 1) :
    (0 : ℂ) ∈ (H.trans Complex.conjCLE.toHomeomorph) '' ball (0 : ℂ) 1 := by
  obtain ⟨w, hw, he⟩ := h0
  refine ⟨w, hw, ?_⟩
  change conj (H w) = 0
  simpa using congrArg conj he

/-- Construct both actual ordinary connector inputs, with exact original and
swapped reflected/reversed physical loops, from the initial completion data. -/
theorem exists_dualRadialCompletionConnectorInputs
    {G : Coord → ℝ} (e0 : OpenPartialHomeomorph Coord Coord)
    {HpPlus HpMinus HgPlus HgMinus : ℂ ≃ₜ ℂ}
    {pPlus pMinus gammaPlus gammaMinus : ℝ → ℂ} {RPlus RMinus : ℝ}
    (hG : ContDiffOn ℝ ∞ G e0.source)
    (hNegative : ∀ q ∈ e0.source, (planarHessian G q).det < 0)
    (heG : ∀ q ∈ e0.source, e0 q = planarGradient G q)
    (hInverse : ContDiffOn ℝ ∞ e0.symm e0.target)
    (hpPlus : DualRadialCompletionPositiveTrace HpPlus pPlus)
    (hpMinus : DualRadialCompletionPositiveTrace HpMinus pMinus)
    (hgammaPlus : DualRadialCompletionPositiveTrace HgPlus gammaPlus)
    (hgammaMinus : DualRadialCompletionPositiveTrace HgMinus gammaMinus)
    (hSourceNesting : closure (HpMinus '' ball (0 : ℂ) 1) ⊆ HpPlus '' ball (0 : ℂ) 1)
    (hGradientNesting : closure (HgPlus '' ball (0 : ℂ) 1) ⊆ HgMinus '' ball (0 : ℂ) 1)
    (hpMinus0 : (0 : ℂ) ∈ HpMinus '' ball (0 : ℂ) 1)
    (hgammaPlus0 : (0 : ℂ) ∈ HgPlus '' ball (0 : ℂ) 1)
    (hClosedBand : seamComplexCoord '' (closure (HpPlus '' ball (0 : ℂ) 1) \
      (HpMinus '' ball (0 : ℂ) 1)) ⊆ e0.source)
    (hActualPlus : ∀ t, e0 (seamComplexCoord (pPlus t)) = seamComplexCoord (gammaPlus t))
    (hActualMinus : ∀ t, e0 (seamComplexCoord (pMinus t)) = seamComplexCoord (gammaMinus t))
    (hPairPlus : ∀ t, 0 < inner ℝ (deriv pPlus t) (deriv gammaPlus t))
    (hPairMinus : ∀ t, 0 < inner ℝ (deriv pMinus t) (deriv gammaMinus t))
    (hRPlus : 0 < RPlus) (hRMinus : 0 < RMinus)
    (hVisPlus : ComplexVisiblePair RPlus pPlus (fun t => Complex.I * gammaPlus t))
    (hVisMinus : ComplexVisiblePair RMinus (corrugatedReverseReflect gammaMinus)
      (fun t => Complex.I * corrugatedReverseReflect pMinus t)) :
    ∃ DPlus : VisibleConnectorIncomingData G e0.source 1 RPlus,
      ∃ DMinus : VisibleConnectorIncomingData (dualRadialCompletionIncomingDual G e0)
        (dualRadialCompletionIncomingChart e0).source 1 RMinus,
        DPlus.incoming.p = seamComplexCoord ∘ pPlus ∧
        DPlus.incoming.gamma = seamComplexCoord ∘ gammaPlus ∧
        DMinus.incoming.p = seamComplexCoord ∘ corrugatedReverseReflect gammaMinus ∧
        DMinus.incoming.gamma = seamComplexCoord ∘ corrugatedReverseReflect pMinus := by
  have hPlusOpen : IsOpen (HpPlus '' ball (0 : ℂ) 1) := HpPlus.isOpenMap _ isOpen_ball
  have hMinusOpen : IsOpen (HpMinus '' ball (0 : ℂ) 1) := HpMinus.isOpenMap _ isOpen_ball
  have hSourcePlus (t : ℝ) : seamComplexCoord (pPlus t) ∈ e0.source := by
    have hFront := connectorInputs_frontier hpPlus t
    apply hClosedBand
    refine ⟨pPlus t, ⟨frontier_subset_closure hFront, ?_⟩, rfl⟩
    intro hInside
    exact hFront.2 (by rw [hPlusOpen.interior_eq]; exact hSourceNesting (subset_closure hInside))
  have hSourceMinus (t : ℝ) : seamComplexCoord (pMinus t) ∈ e0.source := by
    have hFront := connectorInputs_frontier hpMinus t
    apply hClosedBand
    refine ⟨pMinus t, ⟨subset_closure (hSourceNesting (frontier_subset_closure hFront)), ?_⟩, rfl⟩
    intro hInside
    exact hFront.2 (by rw [hMinusOpen.interior_eq]; exact hInside)
  have hpPlus0 := hSourceNesting (subset_closure hpMinus0)
  have hgammaMinus0 := hGradientNesting (subset_closure hgammaPlus0)
  obtain ⟨dPlus, hdPlusP, hdPlusGamma⟩ := dualRadialCompletion_exitTrace e0 hG heG
    hpPlus hgammaPlus hpPlus0 hgammaPlus0 hSourcePlus hActualPlus hPairPlus
  obtain ⟨hDual, hDualNegative, hDualActual, _⟩ :=
    dualRadialCompletionIncoming_dual_data e0 hG hNegative heG hInverse
  have hDualChart : ∀ q ∈ (dualRadialCompletionIncomingChart e0).source,
      dualRadialCompletionIncomingChart e0 q =
        planarGradient (dualRadialCompletionIncomingDual G e0) q := by
    intro q hq
    exact hDualActual hq
  have hPcoord : ContDiff ℝ ∞ (seamComplexCoord ∘ pMinus) := seamComplexCoord.contDiff.comp hpMinus.1
  have hGcoord : ContDiff ℝ ∞ (seamComplexCoord ∘ gammaMinus) :=
    seamComplexCoord.contDiff.comp hgammaMinus.1
  have hPperiod : Function.Periodic (seamComplexCoord ∘ pMinus) 1 :=
    fun t => congrArg seamComplexCoord (hpMinus.2.1 t)
  have hGperiod : Function.Periodic (seamComplexCoord ∘ gammaMinus) 1 :=
    fun t => congrArg seamComplexCoord (hgammaMinus.2.1 t)
  have hCoordPair (t : ℝ) : 0 < deriv (seamComplexCoord ∘ pMinus) t ⬝ᵥ
      deriv (seamComplexCoord ∘ gammaMinus) t := by
    rw [connectorInputs_deriv hpMinus.1, connectorInputs_deriv hgammaMinus.1, connectorInputs_dot]
    exact hPairMinus t
  obtain ⟨_, _, _, _, hRefSource, hRefGradient, hRefPair⟩ :=
    dualRadialCompletionIncoming_reflected_traces e0 hG heG hInverse hPcoord hGcoord
      hPperiod hGperiod hSourceMinus hActualMinus hCoordPair
  have hRefGamma : (fun t => dualRadialCompletionReflection ((seamComplexCoord ∘ gammaMinus) (-t))) =
      seamComplexCoord ∘ corrugatedReverseReflect gammaMinus := by
    funext t
    exact dualRadialCompletionIncoming_complex_reflection (gammaMinus (-t))
  have hRefP : (fun t => dualRadialCompletionReflection ((seamComplexCoord ∘ pMinus) (-t))) =
      seamComplexCoord ∘ corrugatedReverseReflect pMinus := by
    funext t
    exact dualRadialCompletionIncoming_complex_reflection (pMinus (-t))
  have hInnerSource (t : ℝ) : seamComplexCoord (corrugatedReverseReflect gammaMinus t) ∈
      (dualRadialCompletionIncomingChart e0).source := by
    simpa only [Function.comp_apply, dualRadialCompletionIncoming_complex_reflection,
      corrugatedReverseReflect] using hRefSource t
  have hInnerActual (t : ℝ) : dualRadialCompletionIncomingChart e0
      (seamComplexCoord (corrugatedReverseReflect gammaMinus t)) =
      seamComplexCoord (corrugatedReverseReflect pMinus t) := by
    apply (hDualChart _ (hInnerSource t)).trans
    simpa only [Function.comp_apply, dualRadialCompletionIncoming_complex_reflection,
      corrugatedReverseReflect] using hRefGradient t
  have hInnerP := dualRadialCompletionTraceReflection_positive hgammaMinus
  have hInnerGamma := dualRadialCompletionTraceReflection_positive hpMinus
  have hInnerPair (t : ℝ) : 0 < inner ℝ (deriv (corrugatedReverseReflect gammaMinus) t)
      (deriv (corrugatedReverseReflect pMinus) t) := by
    have h := hRefPair t
    rw [hRefGamma, hRefP, connectorInputs_deriv hInnerP.1,
      connectorInputs_deriv hInnerGamma.1, connectorInputs_dot] at h
    exact h
  obtain ⟨dMinus, hdMinusP, hdMinusGamma⟩ :=
    dualRadialCompletion_exitTrace (dualRadialCompletionIncomingChart e0) hDual hDualChart
      hInnerP hInnerGamma (connectorInputs_reflected_origin hgammaMinus0)
      (connectorInputs_reflected_origin hpMinus0) hInnerSource hInnerActual hInnerPair
  let DPlus : VisibleConnectorIncomingData G e0.source 1 RPlus := {
    incoming := dPlus
    radius_pos := hRPlus
    domain_open := e0.open_source
    potential_smooth := hG
    potential_saddle := hNegative
    delta := fun t => Complex.I * gammaPlus t
    actual_delta := by
      rw [hdPlusGamma]
      funext t
      congr 1
    visibility := by
      change ComplexVisiblePair RPlus (positiveExitComplexTrace dPlus.p)
        (fun t => Complex.I * gammaPlus t)
      rw [hdPlusP, connectorInputs_complexTrace]
      exact hVisPlus }
  let DMinus : VisibleConnectorIncomingData (dualRadialCompletionIncomingDual G e0)
      (dualRadialCompletionIncomingChart e0).source 1 RMinus := {
    incoming := dMinus
    radius_pos := hRMinus
    domain_open := (dualRadialCompletionIncomingChart e0).open_source
    potential_smooth := hDual
    potential_saddle := hDualNegative
    delta := fun t => Complex.I * corrugatedReverseReflect pMinus t
    actual_delta := by
      rw [hdMinusGamma]
      funext t
      congr 1
    visibility := by
      change ComplexVisiblePair RMinus (positiveExitComplexTrace dMinus.p)
        (fun t => Complex.I * corrugatedReverseReflect pMinus t)
      rw [hdMinusP, connectorInputs_complexTrace]
      exact hVisMinus }
  exact ⟨DPlus, DMinus, hdPlusP, hdPlusGamma, hdMinusP, hdMinusGamma⟩

end
end TightVer401
