import TightVer401.DualRadialCompletionInnerRetain
import TightVer401.DualRadialCompletionFillingDomain
import TightVer401.DualRadialCompletionTraceReflection
import TightVer401.QuadraticRadialFillingGlue

/-! Reflect the same actual inner dual patch back to the original physical
source. The incoming retained neighborhood is shrunk only by a derived radial
separation; the original supplied Jordan filling is retained throughout. -/
namespace TightVer401
noncomputable section
open Set Filter Metric OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix ComplexConjugate
set_option backward.isDefEq.respectTransparency false

/-- The reflected incoming gradient disk is the reflection of the SAME
ordinary physical Jordan disk, with parameter reversal leaving its range fixed. -/
theorem dualRadialCompletionInnerBranch_inside_reflection
    {G : Coord → ℝ} {e0 : OpenPartialHomeomorph Coord Coord}
    {L R : ℝ} [Fact (0 < L)]
    (D : VisibleConnectorIncomingData (dualRadialCompletionIncomingDual G e0)
      (dualRadialCompletionIncomingChart e0).source L R)
    {HMinus : ℂ ≃ₜ ℂ} {pMinus : ℝ → ℂ}
    (hpMinus : DualRadialCompletionPositiveTrace HMinus pMinus)
    (hDgamma : D.incoming.gamma = seamComplexCoord ∘ corrugatedReverseReflect pMinus) :
    positiveExitInside D.incoming.gamma = dualRadialCompletionReflection ⁻¹'
      (seamComplexCoord '' (HMinus '' ball (0 : ℂ) 1)) := by
  have h := dualRadialCompletionTraceInside_eq
    (dualRadialCompletionTraceReflection_positive hpMinus)
  rw [← hDgamma] at h
  rw [h]
  ext y
  constructor
  · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
    change dualRadialCompletionReflection
      (seamComplexCoord (conj (HMinus w))) ∈
      seamComplexCoord '' (HMinus '' ball (0 : ℂ) 1)
    have hc : conj (conj (HMinus w)) = HMinus w := by
      apply Complex.ext <;> simp only [Complex.conj_re, Complex.conj_im, neg_neg]
    rw [dualRadialCompletionIncoming_complex_reflection, hc]
    exact ⟨HMinus w, ⟨w, hw, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨w, hw, rfl⟩, he⟩
    refine ⟨conj (HMinus w), ⟨w, hw, rfl⟩, ?_⟩
    calc
      seamComplexCoord (conj (HMinus w)) =
          dualRadialCompletionReflection (seamComplexCoord (HMinus w)) :=
        (dualRadialCompletionIncoming_complex_reflection _).symm
      _ = y := by rw [he, dualRadialCompletionReflection_involutive]

/-- The actual patched dual gives one actual physical inner branch, its open
carrier and an open retained neighborhood of the original physical seam.
All patch hypotheses refer to the already constructed SAME scalar P and H. -/
theorem exists_dualRadialCompletion_inner_branch
    {G : Coord → ℝ} (e0 : OpenPartialHomeomorph Coord Coord)
    {L R etaMax S0 delta M : ℝ} [Fact (0 < L)]
    {D : VisibleConnectorIncomingData (dualRadialCompletionIncomingDual G e0)
      (dualRadialCompletionIncomingChart e0).source L R}
    (C : VisibleConnectorConstructionData D etaMax)
    (eC : OpenPartialHomeomorph Coord Coord)
    (hClosed : closure C.source_annulus ⊆ eC.source)
    (hActualC : (eC : Coord → Coord) = planarGradient C.G)
    {HMinus : ℂ ≃ₜ ℂ} {pMinus : ℝ → ℂ}
    (hpMinus : DualRadialCompletionPositiveTrace HMinus pMinus)
    (hDgamma : D.incoming.gamma = seamComplexCoord ∘ corrugatedReverseReflect pMinus)
    {W : Set Coord} (hW : IsOpen W)
    (hSeamW : range (seamComplexCoord ∘ pMinus) ⊆ W)
    (hWSource : W ⊆ e0.source)
    (hWTarget : W ⊆ dualRadialCompletionReflection ⁻¹' eC.target)
    (hRecover : EqOn (fun p => planarLegendre C.G eC
      (dualRadialCompletionReflection p)) G W)
    {H P : Coord → ℝ}
    (hRS0 : R < S0) (hDelta : 0 < delta) (hDeltaR : delta < S0 - R)
    (hDisk : {p : Coord | 0 < planarRadius p ∧ planarRadius p < S0} ⊆
      quadraticRadialFillingDomain R (dualRadialCompletionFillingDomain C eC))
    (hCircle : ∀ theta, saddlePolarChart ![S0,theta] ∈ dualRadialCompletionFillingDomain C eC)
    (hP : ContDiffOn ℝ ∞ P (quadraticRadialFillingDomain S0 eC.target))
    (hnP : ∀ p ∈ quadraticRadialFillingDomain S0 eC.target, (planarHessian P p).det < 0)
    (hPH : EqOn P H {p | 0 < planarRadius p ∧ planarRadius p < S0 + delta})
    (hPF : EqOn P (planarLegendre C.G eC) (eC.target ∩ {p | S0 - delta < planarRadius p}))
    (hInnerH : ∀ p : Coord, 0 < planarRadius p → planarRadius p < R/2 →
      H =ᶠ[𝓝 p] dualRadialQuadraticPotential R M (-M*R^2/2)) :
    ∃ (Fi : Coord → ℝ) (Ui Nin : Set Coord),
      Fi = (fun p => P (dualRadialCompletionReflection p)) ∧
      Ui = dualRadialCompletionReflection ⁻¹' (quadraticRadialFillingDomain S0 eC.target) ∧
      IsOpen Ui ∧ IsOpen Nin ∧
      frontier (seamComplexCoord '' (HMinus '' ball (0 : ℂ) 1)) ⊆ Nin ∧
      Nin ⊆ e0.source ∧
      ((seamComplexCoord '' (HMinus '' ball (0 : ℂ) 1)) ∩
        {p : Coord | 0 < planarRadius p}) ∪ Nin ⊆ Ui ∧
      ContDiffOn ℝ ∞ Fi Ui ∧
      (∀ p ∈ Ui, (planarHessian Fi p).det < 0) ∧
      EqOn Fi G Nin ∧ (∀ p ∈ Nin, Fi =ᶠ[𝓝 p] G) ∧
      EqOn Fi (fun p => (M*R)*planarRadius p-M*planarRadius p^2/2-M*R^2/2)
        {p | 0 < planarRadius p ∧ planarRadius p < R/2} ∧
      (∀ p, 0 < planarRadius p → planarRadius p < R/2 →
        Fi =ᶠ[𝓝 p] (fun q => (M*R)*planarRadius q-M*planarRadius q^2/2-M*R^2/2)) := by
  let I := seamComplexCoord '' (HMinus '' ball (0 : ℂ) 1)
  let V := quadraticRadialFillingDomain S0 eC.target
  let Fi := fun p => P (dualRadialCompletionReflection p)
  let Ui := dualRadialCompletionReflection ⁻¹' V
  let Nin := W ∩ {p : Coord | S0 - delta < planarRadius p}
  have hR : 0 < R := D.radius_pos
  have hS0 : 0 < S0 := hR.trans hRS0
  have hBound : 0 < S0 - delta := by linarith
  have hV : IsOpen V :=
    (isOpen_lt continuous_const quadraticRadialFillingRadius_continuous).inter
      ((isOpen_lt quadraticRadialFillingRadius_continuous continuous_const).union eC.open_target)
  have hUi : IsOpen Ui := hV.preimage dualRadialCompletionReflection.continuous
  have hNin : IsOpen Nin := hW.inter
    (isOpen_lt continuous_const quadraticRadialFillingRadius_continuous)
  have hInside : positiveExitInside D.incoming.gamma = dualRadialCompletionReflection ⁻¹' I :=
    dualRadialCompletionInnerBranch_inside_reflection D hpMinus hDgamma
  have hTarget : C.gradient_annulus ⊆ eC.target := by
    intro y hy
    let q := C.gradient_chart.symm y
    have hyT : y ∈ C.gradient_chart.target := by rwa [C.gradient_chart_target]
    have hqS : q ∈ C.source_annulus := by
      rw [← C.gradient_chart_source]
      exact C.gradient_chart.map_target hyT
    have he : eC q = y := by
      rw [hActualC, ← C.gradient_chart_actual hqS]
      exact C.gradient_chart.right_inv hyT
    rw [← he]
    exact eC.map_source (hClosed (subset_closure hqS))
  have hSmallInside : ∀ y : Coord, planarRadius y ≤ S0 → y ∈ positiveExitInside D.incoming.gamma := by
    intro y hy
    by_cases hyR : planarRadius y ≤ R
    · apply C.gradient_nesting
      rw [dualRadialCompletionFillingDomain_terminal_closure]
      exact hyR
    · have hyPos : 0 < planarRadius y := hR.trans (lt_of_not_ge hyR)
      by_cases hyS0 : planarRadius y < S0
      · rcases (hDisk ⟨hyPos,hyS0⟩).2 with hyR' | hyU
        · change planarRadius y < R at hyR'
          apply C.gradient_nesting
          rw [dualRadialCompletionFillingDomain_terminal_closure]
          exact le_of_lt hyR'
        · exact hyU.2
      · have hyEq : planarRadius y = S0 := le_antisymm hy (le_of_not_gt hyS0)
        obtain ⟨theta, rfl⟩ := quadraticRadialFilling_radiusLevel_exists_polar hS0 hyEq
        exact (hCircle theta).2
  have hSeamRadius : ∀ s : ℝ, S0 < planarRadius (D.incoming.gamma s) := by
    intro s
    by_contra hs
    have hi := hSmallInside (D.incoming.gamma s) (le_of_not_gt hs)
    exact Schoenflies.inside_subset_compl hi (mem_range_self s)
  have hPhysicalRadius : ∀ s : ℝ, S0 < planarRadius (seamComplexCoord (pMinus s)) := by
    intro s
    have he : D.incoming.gamma (-s) = dualRadialCompletionReflection (seamComplexCoord (pMinus s)) := by
      rw [hDgamma]
      change seamComplexCoord (conj (pMinus (-(-s)))) = _
      rw [neg_neg, dualRadialCompletionIncoming_complex_reflection]
    simpa only [he, dualRadialCompletionReflection_radius] using hSeamRadius (-s)
  have hFront : frontier I = range (seamComplexCoord ∘ pMinus) := by
    change frontier ((seamComplexCoord.toHomeomorph : ℂ → Coord) ''
      (HMinus '' ball (0 : ℂ) 1)) = range (seamComplexCoord ∘ pMinus)
    rw [← seamComplexCoord.toHomeomorph.image_frontier, ← HMinus.image_frontier,
      frontier_ball _ one_ne_zero, ← dualRadialCompletion_positiveTrace_range hpMinus]
    change seamComplexCoord '' range pMinus = range (seamComplexCoord ∘ pMinus)
    exact (range_comp (seamComplexCoord : ℂ → Coord) pMinus).symm
  have hFrontN : frontier I ⊆ Nin := by
    rw [hFront]
    rintro p ⟨s,rfl⟩
    exact ⟨hSeamW (mem_range_self s), by
      change S0 - delta < planarRadius (seamComplexCoord (pMinus s))
      linarith [hPhysicalRadius s]⟩
  have hNinUi : Nin ⊆ Ui := by
    intro p hp
    have hr : 0 < planarRadius p := hBound.trans hp.2
    have hrS : 0 < planarRadius (dualRadialCompletionReflection p) := by
      rw [dualRadialCompletionReflection_radius]
      exact hr
    exact ⟨hrS, Or.inr (hWTarget hp.1)⟩
  have hCover : (I ∩ {p : Coord | 0 < planarRadius p}) ∪ Nin ⊆ Ui := by
    intro p hp
    rcases hp with hp | hp
    · have hr : 0 < planarRadius (dualRadialCompletionReflection p) := by
        rw [dualRadialCompletionReflection_radius]
        exact hp.2
      by_cases hpSmall : planarRadius p < S0
      · exact ⟨hr, Or.inl (by
          change planarRadius (dualRadialCompletionReflection p) < S0
          rw [dualRadialCompletionReflection_radius]
          exact hpSmall)⟩
      · have hpi : dualRadialCompletionReflection p ∈ positiveExitInside D.incoming.gamma := by
          rw [hInside]
          simpa only [mem_preimage, dualRadialCompletionReflection_involutive] using hp.1
        have hpa : dualRadialCompletionReflection p ∈ C.gradient_annulus := by
          rw [C.gradient_annulus_eq, dualRadialCompletionFillingDomain_terminal_closure]
          exact ⟨hpi, by
            change ¬planarRadius (dualRadialCompletionReflection p) ≤ R
            rw [dualRadialCompletionReflection_radius]
            linarith [le_of_not_gt hpSmall]⟩
        exact ⟨hr, Or.inr (hTarget hpa)⟩
    · exact hNinUi hp
  have hEq : EqOn Fi G Nin := by
    intro p hp
    have hr : S0 - delta < planarRadius (dualRadialCompletionReflection p) := by
      rw [dualRadialCompletionReflection_radius]
      exact hp.2
    exact (hPF ⟨hWTarget hp.1, hr⟩).trans (hRecover hp.1)
  have hInner : EqOn Fi (fun p => (M*R)*planarRadius p-M*planarRadius p^2/2-M*R^2/2)
      {p | 0 < planarRadius p ∧ planarRadius p < R/2} := by
    intro p hp
    have hr : 0 < planarRadius (dualRadialCompletionReflection p) := by
      rw [dualRadialCompletionReflection_radius]
      exact hp.1
    have hrR : planarRadius (dualRadialCompletionReflection p) < R/2 := by
      rw [dualRadialCompletionReflection_radius]
      exact hp.2
    calc
      Fi p = H (dualRadialCompletionReflection p) := hPH ⟨hr, by linarith [hrR,hRS0,hDelta]⟩
      _ = dualRadialQuadraticPotential R M (-M*R^2/2) (dualRadialCompletionReflection p) :=
        (hInnerH _ hr hrR).eq_of_nhds
      _ = _ := by
        simp only [dualRadialQuadraticPotential, radialPlanarPotential, dualRadialQuadraticProfile,
          dualRadialCompletionReflection_radius]
        ring
  refine ⟨Fi,Ui,Nin,rfl,rfl,hUi,hNin,hFrontN,(fun p hp => hWSource hp.1),hCover,
    dualRadialCompletionReflection_contDiffOn hP,?_,hEq,?_,hInner,?_⟩
  · intro p hp
    rw [dualRadialCompletionReflection_hessian_det hP hV hp]
    exact hnP _ hp
  · intro p hp
    filter_upwards [hNin.mem_nhds hp] with q hq
    exact hEq hq
  · intro p hp hr
    have hOpen : IsOpen {q : Coord | 0 < planarRadius q ∧ planarRadius q < R/2} :=
      (isOpen_lt continuous_const quadraticRadialFillingRadius_continuous).inter
        (isOpen_lt quadraticRadialFillingRadius_continuous continuous_const)
    filter_upwards [hOpen.mem_nhds (show p ∈ {q : Coord | 0 < planarRadius q ∧ planarRadius q < R/2} from ⟨hp,hr⟩)] with q hq
    exact hInner hq

end
end TightVer401
