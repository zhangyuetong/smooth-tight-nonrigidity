import TightVer401.QuadraticFillerCartesianGradientAnnulusSmooth

/-! Internal three-piece scalar assembly on actual open overlaps.
The full completion theorem must construct these pieces and overlap equalities.
-/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix

def dualRadialCompletionPatch (U0 U1 : Set Coord) (F0 F1 F2 : Coord → ℝ) :
    Coord → ℝ := by
  classical
  exact fun p => if p ∈ U0 then F0 p else if p ∈ U1 then F1 p else F2 p

theorem dualRadialCompletionPatch_eqOn {U0 U1 U2 : Set Coord}
    {F0 F1 F2 : Coord → ℝ}
    (h01 : EqOn F0 F1 (U0 ∩ U1)) (h02 : EqOn F0 F2 (U0 ∩ U2))
    (h12 : EqOn F1 F2 (U1 ∩ U2)) :
    EqOn (dualRadialCompletionPatch U0 U1 F0 F1 F2) F0 U0 ∧
      EqOn (dualRadialCompletionPatch U0 U1 F0 F1 F2) F1 U1 ∧
      EqOn (dualRadialCompletionPatch U0 U1 F0 F1 F2) F2 U2 := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    simp only [dualRadialCompletionPatch, if_pos hp]
  · intro p hp
    by_cases hp0 : p ∈ U0
    · simpa only [dualRadialCompletionPatch, if_pos hp0] using h01 ⟨hp0, hp⟩
    · simp only [dualRadialCompletionPatch, if_neg hp0, if_pos hp]
  · intro p hp
    by_cases hp0 : p ∈ U0
    · simpa only [dualRadialCompletionPatch, if_pos hp0] using h02 ⟨hp0, hp⟩
    · by_cases hp1 : p ∈ U1
      · simpa only [dualRadialCompletionPatch, if_neg hp0, if_pos hp1] using h12 ⟨hp1, hp⟩
      · simp only [dualRadialCompletionPatch, if_neg hp0, if_neg hp1]

theorem dualRadialCompletionPatch_germs {U0 U1 U2 : Set Coord}
    {F0 F1 F2 : Coord → ℝ} (hU0 : IsOpen U0) (hU1 : IsOpen U1) (hU2 : IsOpen U2)
    (h01 : EqOn F0 F1 (U0 ∩ U1)) (h02 : EqOn F0 F2 (U0 ∩ U2))
    (h12 : EqOn F1 F2 (U1 ∩ U2)) :
    (∀ p ∈ U0, dualRadialCompletionPatch U0 U1 F0 F1 F2 =ᶠ[𝓝 p] F0) ∧
      (∀ p ∈ U1, dualRadialCompletionPatch U0 U1 F0 F1 F2 =ᶠ[𝓝 p] F1) ∧
      (∀ p ∈ U2, dualRadialCompletionPatch U0 U1 F0 F1 F2 =ᶠ[𝓝 p] F2) := by
  obtain ⟨he0, he1, he2⟩ := dualRadialCompletionPatch_eqOn h01 h02 h12
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    filter_upwards [hU0.mem_nhds hp] with q hq
    exact he0 hq
  · intro p hp
    filter_upwards [hU1.mem_nhds hp] with q hq
    exact he1 hq
  · intro p hp
    filter_upwards [hU2.mem_nhds hp] with q hq
    exact he2 hq

theorem dualRadialCompletionPatch_contDiffOn {U0 U1 U2 : Set Coord}
    {F0 F1 F2 : Coord → ℝ} (hU0 : IsOpen U0) (hU1 : IsOpen U1) (hU2 : IsOpen U2)
    (h01 : EqOn F0 F1 (U0 ∩ U1)) (h02 : EqOn F0 F2 (U0 ∩ U2))
    (h12 : EqOn F1 F2 (U1 ∩ U2)) (hF0 : ContDiffOn ℝ ∞ F0 U0)
    (hF1 : ContDiffOn ℝ ∞ F1 U1) (hF2 : ContDiffOn ℝ ∞ F2 U2) :
    ContDiffOn ℝ ∞ (dualRadialCompletionPatch U0 U1 F0 F1 F2) (U0 ∪ U1 ∪ U2) := by
  obtain ⟨hg0, hg1, hg2⟩ := dualRadialCompletionPatch_germs hU0 hU1 hU2 h01 h02 h12
  intro p hp
  rcases hp with (hp | hp) | hp
  · exact ((hF0.contDiffAt (hU0.mem_nhds hp)).congr_of_eventuallyEq (hg0 p hp)).contDiffWithinAt
  · exact ((hF1.contDiffAt (hU1.mem_nhds hp)).congr_of_eventuallyEq (hg1 p hp)).contDiffWithinAt
  · exact ((hF2.contDiffAt (hU2.mem_nhds hp)).congr_of_eventuallyEq (hg2 p hp)).contDiffWithinAt

private theorem completionPatch_hessian_eq {F H : Coord → ℝ} {p : Coord}
    (he : F =ᶠ[𝓝 p] H) : planarHessian F p = planarHessian H p := by
  ext i j
  have hj : coordPartial j F =ᶠ[𝓝 p] coordPartial j H := by
    filter_upwards [he.fderiv (𝕜 := ℝ)] with q hq
    unfold coordPartial
    rw [hq]
  change fderiv ℝ (coordPartial j F) p (Pi.single i 1) =
    fderiv ℝ (coordPartial j H) p (Pi.single i 1)
  rw [hj.fderiv_eq]

theorem dualRadialCompletionPatch_saddle {U0 U1 U2 : Set Coord}
    {F0 F1 F2 : Coord → ℝ} (hU0 : IsOpen U0) (hU1 : IsOpen U1) (hU2 : IsOpen U2)
    (h01 : EqOn F0 F1 (U0 ∩ U1)) (h02 : EqOn F0 F2 (U0 ∩ U2))
    (h12 : EqOn F1 F2 (U1 ∩ U2))
    (hn0 : ∀ p ∈ U0, (planarHessian F0 p).det < 0)
    (hn1 : ∀ p ∈ U1, (planarHessian F1 p).det < 0)
    (hn2 : ∀ p ∈ U2, (planarHessian F2 p).det < 0) :
    ∀ p ∈ U0 ∪ U1 ∪ U2,
      (planarHessian (dualRadialCompletionPatch U0 U1 F0 F1 F2) p).det < 0 := by
  obtain ⟨hg0, hg1, hg2⟩ := dualRadialCompletionPatch_germs hU0 hU1 hU2 h01 h02 h12
  intro p hp
  rcases hp with (hp | hp) | hp
  · rw [completionPatch_hessian_eq (hg0 p hp)]
    exact hn0 p hp
  · rw [completionPatch_hessian_eq (hg1 p hp)]
    exact hn1 p hp
  · rw [completionPatch_hessian_eq (hg2 p hp)]
    exact hn2 p hp

/-- Internal assembly from constructed scalar pieces; it is not the public
completion theorem and does not produce its connector or filling pieces. -/
theorem exists_dualRadialCompletion_patch {U0 U1 U2 W : Set Coord}
    {F0 F1 F2 G : Coord → ℝ} {RN mu A B d0 dInfinity epsilon L : ℝ}
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
      {p : Coord | 0 < planarRadius p ∧ planarRadius p < epsilon})
    (hOuter : EqOn F2 (fun p => A * planarRadius p - B / planarRadius p + dInfinity)
      {p : Coord | L < planarRadius p}) :
    ∃ F : Coord → ℝ,
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
        F =ᶠ[𝓝 p] (fun q => A * planarRadius q - B / planarRadius q + dInfinity)) := by
  let F := dualRadialCompletionPatch U0 U1 F0 F1 F2
  obtain ⟨he0, he1, he2⟩ := dualRadialCompletionPatch_eqOn h01 h02 h12
  have hRG : EqOn F G W := fun _ hp => (he1 (hWU1 hp)).trans (hRetain hp)
  have hRI : EqOn F (fun p => RN * planarRadius p - mu * planarRadius p ^ 2 / 2 + d0)
      {p | 0 < planarRadius p ∧ planarRadius p < epsilon} :=
    fun _ hp => (he0 (hInnerSet hp)).trans (hInner hp)
  have hRO : EqOn F (fun p => A * planarRadius p - B / planarRadius p + dInfinity)
      {p | L < planarRadius p} :=
    fun _ hp => (he2 (hOuterSet hp)).trans (hOuter hp)
  refine ⟨F, (dualRadialCompletionPatch_contDiffOn hU0 hU1 hU2 h01 h02 h12
    hF0 hF1 hF2).mono hcover,
    fun p hp => dualRadialCompletionPatch_saddle hU0 hU1 hU2 h01 h02 h12 hn0 hn1 hn2
      p (hcover hp), hRG, ?_, hRI, hRO, ?_, ?_⟩
  · intro p hp
    filter_upwards [hW.mem_nhds hp] with q hq
    exact hRG hq
  · intro p hp heps
    have hOpen : IsOpen {q : Coord | 0 < planarRadius q ∧ planarRadius q < epsilon} :=
      (isOpen_lt continuous_const quadraticFillerCartesianGradient_radius_continuous).inter
        (isOpen_lt quadraticFillerCartesianGradient_radius_continuous continuous_const)
    filter_upwards [hOpen.mem_nhds ⟨hp, heps⟩] with q hq
    exact hRI hq
  · intro p hp
    have hOpen : IsOpen {q : Coord | L < planarRadius q} :=
      isOpen_lt continuous_const quadraticFillerCartesianGradient_radius_continuous
    filter_upwards [hOpen.mem_nhds hp] with q hq
    exact hRO hq

end
end TightVer401
