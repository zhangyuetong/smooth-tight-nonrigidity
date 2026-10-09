import TightVer401.DualRadialCompletionPatch
import TightVer401.DualRadialCompletionCircularExhaustion

/-! Internal same-potential two-ended assembly from actual scalar pieces and
an independently proved local circular-degree specialization. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix

/-- Assemble the scalar patch once, then derive the actual global gradient
inverse of that same potential. The caller must construct the pieces and
ordinary overlap/cover facts and prove the local degree specialization. -/
theorem exists_dualRadialCompletion_assembly_of_circular_degree
    (hDegree : DualRadialCompletionCircularDegreeClaim)
    {U0 U1 U2 W : Set Coord} {F0 F1 F2 G : Coord → ℝ}
    {RN mu A B d0 dInfinity epsilon L : ℝ}
    (hA : 0 < A) (hAR : A < RN) (hmu : 0 < mu) (hB : 0 < B)
    (hepsilon : 0 < epsilon)
    (hU0 : IsOpen U0) (hU1 : IsOpen U1) (hU2 : IsOpen U2)
    (hcover : {p : Coord | 0 < planarRadius p} ⊆ U0 ∪ U1 ∪ U2)
    (h01 : EqOn F0 F1 (U0 ∩ U1)) (h02 : EqOn F0 F2 (U0 ∩ U2))
    (h12 : EqOn F1 F2 (U1 ∩ U2)) (hF0 : ContDiffOn ℝ ∞ F0 U0)
    (hF1 : ContDiffOn ℝ ∞ F1 U1) (hF2 : ContDiffOn ℝ ∞ F2 U2)
    (hn0 : ∀ p ∈ U0, (planarHessian F0 p).det < 0)
    (hn1 : ∀ p ∈ U1, (planarHessian F1 p).det < 0)
    (hn2 : ∀ p ∈ U2, (planarHessian F2 p).det < 0)
    (hW : IsOpen W) (hWU1 : W ⊆ U1) (hRetain : EqOn F1 G W)
    (hInnerSet : {p : Coord | 0 < planarRadius p ∧ planarRadius p < epsilon} ⊆ U0)
    (hOuterSet : {p : Coord | L < planarRadius p} ⊆ U2)
    (hInner : EqOn F0 (fun p => RN * planarRadius p - mu * planarRadius p ^ 2 / 2 + d0)
      {p | 0 < planarRadius p ∧ planarRadius p < epsilon})
    (hOuter : EqOn F2 (fun p => A * planarRadius p - B / planarRadius p + dInfinity)
      {p | L < planarRadius p}) :
    ∃ (F : Coord → ℝ) (e : OpenPartialHomeomorph Coord Coord),
      ContDiffOn ℝ ∞ F {p | 0 < planarRadius p} ∧
      (∀ p, 0 < planarRadius p → (planarHessian F p).det < 0) ∧
      EqOn F G W ∧ (∀ p ∈ W, F =ᶠ[𝓝 p] G) ∧
      EqOn F (fun p => RN * planarRadius p - mu * planarRadius p ^ 2 / 2 + d0)
        {p | 0 < planarRadius p ∧ planarRadius p < epsilon} ∧
      EqOn F (fun p => A * planarRadius p - B / planarRadius p + dInfinity)
        {p | L < planarRadius p} ∧
      (∀ p, 0 < planarRadius p → planarRadius p < epsilon →
        F =ᶠ[𝓝 p] (fun q => RN * planarRadius q - mu * planarRadius q ^ 2 / 2 + d0)) ∧
      (∀ p, L < planarRadius p →
        F =ᶠ[𝓝 p] (fun q => A * planarRadius q - B / planarRadius q + dInfinity)) ∧
      e.source = {p | 0 < planarRadius p} ∧
      e.target = {y | A < planarRadius y ∧ planarRadius y < RN} ∧
      (e : Coord → Coord) = planarGradient F ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  obtain ⟨F, hF, hn, hOld, hOldGerm, hInnerF, hOuterF, hInnerGerm, hOuterGerm⟩ :=
    exists_dualRadialCompletion_patch hU0 hU1 hU2 hcover h01 h02 h12 hF0 hF1 hF2
      hn0 hn1 hn2 hW hWU1 hRetain hInnerSet hOuterSet hInner hOuter
  obtain ⟨e, hSource, hTarget, hActual, hInverse⟩ :=
    exists_dualRadialCompletion_gradient_inverse_of_circular_degree hDegree
      hA hAR hmu hB hepsilon hF hn hInnerF hOuterF
  exact ⟨F, e, hF, hn, hOld, hOldGerm, hInnerF, hOuterF, hInnerGerm, hOuterGerm,
    hSource, hTarget, hActual, hInverse⟩

end
end TightVer401
