import TightVer401.PositiveExitConstructionAmbientJetVisibility
import TightVer401.PositiveExitConstructionGraphTrace

/-! Consume the actual finite-jet estimates returned by the paired graph.
Value and derivative bounds are derived by evaluating the actual multilinear
maps, before applying the same-potential ambient-jet visibility producer. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

/-- The returned orders zero and one really bound the actual first jet. -/
theorem positiveExit_firstJet_close_of_iteratedFDeriv
    {f g : ℝ → Ambient} {K : Set ℝ} {ν : ℝ}
    (h : ∀ j ≤ 1, ∀ s ∈ K,
      ‖iteratedFDeriv ℝ j f s - iteratedFDeriv ℝ j g s‖ < ν) :
    ∀ s ∈ K, ‖f s - g s‖ < ν ∧ ‖deriv f s - deriv g s‖ < ν := by
  intro s hs
  have h0 : ‖f s-g s‖ ≤ ‖iteratedFDeriv ℝ 0 f s-iteratedFDeriv ℝ 0 g s‖ := by
    simpa using (iteratedFDeriv ℝ 0 f s-iteratedFDeriv ℝ 0 g s).le_opNorm
      (fun _ : Fin 0 => (1 : ℝ))
  have h1 : ‖deriv f s-deriv g s‖ ≤
      ‖iteratedFDeriv ℝ 1 f s-iteratedFDeriv ℝ 1 g s‖ := by
    simpa only [ContinuousMultilinearMap.sub_apply,iteratedFDeriv_one_apply,
      fderiv_apply_one_eq_deriv,norm_one,Finset.prod_const_one,mul_one] using
      (iteratedFDeriv ℝ 1 f s-iteratedFDeriv ℝ 1 g s).le_opNorm
        (fun _ : Fin 1 => (1 : ℝ))
  exact ⟨h0.trans_lt (h 0 (by omega) s hs),h1.trans_lt (h 1 (by omega) s hs)⟩

private theorem exitGraphVisibility_complex_eq :
    positiveExitComplexPoint = angularDescentComplex := by
  funext q
  apply Complex.ext <;> simp [positiveExitComplexPoint,angularDescentComplex]

/-- Choose both tolerances before the patch and graph. The actual graph trace
then inherits actual visibility from its returned finite-jet bounds and the
actual coordinate C2 budget on the SAME original potential's domain. -/
theorem positiveExit_exists_graph_trace_visibility_threshold {R P : ℝ}
    (hR : 0 ≤ R) (hP : 0 < P) {G : Coord → ℝ} {U : Set Coord}
    (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U) {ζ : ℝ → Ambient}
    (hζ : ContDiff ℝ ∞ ζ) (hnorth : ∀ s, 0 < ζ s 2)
    (hsource : ∀ s, gnomonicInverse (ζ s) ∈ U)
    (hvisible : ComplexVisiblePair R (angularDescentComplex ∘ gnomonicInverse ∘ ζ)
      (fun s => Complex.I * angularDescentComplex (planarGradient G (gnomonicInverse (ζ s))))) :
    ∃ η > 0, ∃ ν > 0, ∀ (J : Coord → ℝ) (c : ℝ → Ambient),
      ContDiff ℝ ∞ J → ContDiff ℝ ∞ c → Function.Periodic c P →
      (∀ q ∈ U, fermiCoordinateC2Size J q < η) →
      (∀ j ≤ 1, ∀ s ∈ Icc (0 : ℝ) P,
        ‖iteratedFDeriv ℝ j c s-iteratedFDeriv ℝ j ζ s‖ < ν) →
      ∀ tr : PositiveExitRegularGraphTrace (fun q => G q+J q) U P,
      (∀ s, tr.p s=gnomonicInverse (c s)) →
      ComplexVisiblePair R (positiveExitComplexTrace tr.p)
        (fun s => Complex.I * positiveExitComplexTrace tr.gamma s) := by
  obtain ⟨η,hη,ν,hν,h⟩ := positiveExit_exists_ambientJet_visibility_threshold
    hR hP hU hG hζ hnorth hsource hvisible
  refine ⟨η,hη,ν,hν,?_⟩
  intro J c hJ hc hcP hbudget hjets tr hactual
  obtain ⟨_,hv⟩ := h J c hJ hc hcP hbudget
    (positiveExit_firstJet_close_of_iteratedFDeriv hjets)
  have heq : tr.p=gnomonicInverse ∘ c := funext hactual
  rw [positiveExitComplexTrace,positiveExitComplexTrace,
    tr.actual_gradient,heq,exitGraphVisibility_complex_eq]
  simpa only [Function.comp_apply] using hv

end
end TightVer401
