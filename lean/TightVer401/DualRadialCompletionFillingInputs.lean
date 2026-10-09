import TightVer401.DualRadialCompletionFillingDomain
import TightVer401.DualRadialCompletionTerminal

/-! The whole actual connector inverse supplies ordinary filling inputs on
a derived positive radial neighborhood inside the incoming gradient disk. -/
namespace TightVer401
noncomputable section
open Set Filter Function OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix

private theorem fillingInputs_polar (R theta : ℝ) :
    R • visibleConnectorUnitDirection theta = saddlePolarChart ![R,theta] := by
  ext i
  fin_cases i <;> rfl

theorem exists_dualRadialCompletion_filling_inputs
    {Gin : Coord → ℝ} {Uin : Set Coord} {L R etaMax : ℝ} [Fact (0 < L)]
    {D : VisibleConnectorIncomingData Gin Uin L R}
    (C : VisibleConnectorConstructionData D etaMax)
    (E : OpenPartialHomeomorph Coord Coord)
    (hClosed : closure C.source_annulus ⊆ E.source)
    (hG : ContDiffOn ℝ ∞ C.G E.source)
    (hNeg : ∀ p ∈ E.source, (planarHessian C.G p).det < 0)
    (hActual : (E : Coord → Coord) = planarGradient C.G)
    (hi : ContDiffOn ℝ ∞ E.symm E.target) :
    let F := planarLegendre C.G E
    ∃ U : Set Coord, IsOpen U ∧ U ⊆ dualRadialCompletionFillingDomain C E ∧
      (∀ theta, saddlePolarChart ![R,theta] ∈ U) ∧
      ContDiffOn ℝ ∞ F U ∧ (∀ p ∈ U, (planarHessian F p).det < 0) ∧
      (∀ p ∈ U, 0 < planarGradient F p ⬝ᵥ p) ∧
      (∀ theta, 0 < planarGradient F (saddlePolarChart ![R,theta]) ⬝ᵥ
        quadraticRadialFillingRadialUnit theta) ∧
      (∀ theta, 0 < quadraticRadialFillingTangentialUnit theta ⬝ᵥ
        (planarHessian F (saddlePolarChart ![R,theta]) *ᵥ
          quadraticRadialFillingTangentialUnit theta)) ∧
      Schoenflies.IsJordanCurve (range (jordanComplexCoordinates.symm ∘
        quadraticRadialFillingGradientComplexTrace F R)) := by
  let F := planarLegendre C.G E
  let V := dualRadialCompletionFillingDomain C E
  obtain ⟨hV,hCircleV,_⟩ := dualRadialCompletionFillingDomain_properties C E hClosed hActual
  have hVT : V ⊆ E.target := inter_subset_left
  have heG : ∀ p ∈ E.source, E p = planarGradient C.G p :=
    fun p _ => congrFun hActual p
  have hF : ContDiffOn ℝ ∞ F V := (planarLegendre_contDiffOn E hG hi).mono hVT
  have hCircle (theta : ℝ) : saddlePolarChart ![R,theta] ∈ V :=
    hCircleV (angularDescent_radius_polar (q := ![R,theta]) D.radius_pos)
  have hSource (s : ℝ) : C.terminal.p s ∈ E.source := by
    apply hClosed
    apply frontier_subset_closure
    rw [C.source_boundary_exact]
    exact Or.inr (mem_range_self s)
  have hBoundary (s : ℝ) : E (C.terminal.p s) = saddlePolarChart ![R,C.theta s] := by
    rw [hActual]
    calc
      planarGradient C.G (C.terminal.p s) = C.terminal.gamma s :=
        (congrFun C.terminal.actual_gradient s).symm
      _ = R • visibleConnectorUnitDirection (C.theta s) := C.terminal_circle s
      _ = saddlePolarChart ![R,C.theta s] := fillingInputs_polar R (C.theta s)
  have hGamma : C.terminal.gamma = fun s => saddlePolarChart ![R,C.theta s] := by
    funext s
    exact (C.terminal_circle s).trans (fillingInputs_polar R (C.theta s))
  have hRad (s : ℝ) : 0 < C.terminal.p s ⬝ᵥ
      quadraticRadialFillingRadialUnit (C.theta s) := C.terminal_radial_positive s
  have hTan (s : ℝ) : 0 < deriv C.terminal.p s ⬝ᵥ
      deriv (fun t => saddlePolarChart ![R,C.theta t]) s := by
    rw [← hGamma]
    exact C.terminal.tangent_pairing s
  obtain ⟨_,_,_,_,hb,hTrace⟩ := dualRadialCompletion_terminal_traces E hG hi heG
    D.radius_pos (Fact.out : 0 < L) C.terminal.p_smooth C.theta_smooth
    C.theta_increasing C.theta_turn hSource hBoundary hRad hTan
  have hRadial (theta : ℝ) : 0 < planarGradient F (saddlePolarChart ![R,theta]) ⬝ᵥ
      quadraticRadialFillingRadialUnit theta := by
    have hp := hb theta
    rw [quadraticRadialFilling_radialTrace_eq hF hV (hCircle theta)] at hp
    exact hp
  have hTangential (theta : ℝ) : 0 < quadraticRadialFillingTangentialUnit theta ⬝ᵥ
      (planarHessian F (saddlePolarChart ![R,theta]) *ᵥ quadraticRadialFillingTangentialUnit theta) := by
    have hp := hTrace theta
    rw [quadraticRadialFilling_tangentialTrace_eq hF hV hCircle] at hp
    exact (mul_pos_iff_of_pos_left (sq_pos_of_pos D.radius_pos)).mp hp
  obtain ⟨tau,_,_,_,hLeft,_,_⟩ := exists_dualRadialCompletion_phase_inverse
    C.theta_smooth C.theta_increasing (Fact.out : 0 < L) C.theta_turn
  have hAngleActual (theta : ℝ) : E (C.terminal.p (tau.symm theta)) =
      saddlePolarChart ![R,theta] := by rw [hBoundary,hLeft]
  have hGradient (theta : ℝ) : planarGradient F (saddlePolarChart ![R,theta]) =
      C.terminal.p (tau.symm theta) := by
    rw [planarLegendre_gradient E hG hi heG (hVT (hCircle theta)), ← hAngleActual theta]
    exact E.left_inv (hSource _)
  have hComplex (p : Coord) : angularDescentComplex p = positiveExitComplexPoint p := by
    apply Complex.ext <;> simp [angularDescentComplex,positiveExitComplexPoint]
  have hComplexTrace : quadraticRadialFillingGradientComplexTrace F R =
      positiveExitComplexTrace C.terminal.p ∘ tau.symm := by
    funext theta
    unfold quadraticRadialFillingGradientComplexTrace quadraticRadialFillingGradientTrace
    rw [hGradient,hComplex]
    rfl
  have hRange : range (jordanComplexCoordinates.symm ∘ quadraticRadialFillingGradientComplexTrace F R) =
      positiveExitJordanRange C.terminal.p := by
    unfold positiveExitJordanRange
    rw [hComplexTrace]
    apply Subset.antisymm
    · rintro z ⟨theta,rfl⟩
      exact ⟨tau.symm theta,rfl⟩
    · rintro z ⟨s,rfl⟩
      exact ⟨tau s,by simp only [Function.comp_apply,tau.symm_apply_apply]⟩
  have hJordan : Schoenflies.IsJordanCurve
      (range (jordanComplexCoordinates.symm ∘ quadraticRadialFillingGradientComplexTrace F R)) := by
    rw [hRange]
    exact C.terminal.source_jordan
  obtain ⟨U,hU,hUV,hCircleU,hPositive⟩ :=
    quadraticRadialFilling_positive_radial_neighborhood hF hV D.radius_pos hCircleV hRadial
  refine ⟨U,hU,hUV,?_,hF.mono hUV,?_,hPositive,hRadial,hTangential,hJordan⟩
  · intro theta
    exact hCircleU (angularDescent_radius_polar (q := ![R,theta]) D.radius_pos)
  · intro p hp
    apply planarLegendre_saddle E hG hi heG (hVT (hUV hp))
    exact hNeg _ (E.map_target (hVT (hUV hp)))

end
end TightVer401
