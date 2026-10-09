import TightVer401.DualRadialCompletionFillingDomain
import TightVer401.DualRadialCompletionContainment
import TightVer401.QuadraticRadialFillingBoundaryOrigin
import TightVer401.QuadraticRadialFillingGradientJordan

/-! A cut strictly inside the actual filling inverse source supplies a full
retained collar. All Jordan disks below belong to the same actual traces. -/
namespace TightVer401
noncomputable section
open Set Filter Metric OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity
open scoped ContDiff Topology Matrix

private theorem retainedContour_exit_point (p : Coord) :
    seamComplexCoord (positiveExitComplexPoint p) = p := by
  ext i
  fin_cases i <;> rfl

private theorem retainedContour_terminal_filling
    {Gin : Coord → ℝ} {Uin : Set Coord} {L R etaMax : ℝ} [Fact (0 < L)]
    {D : VisibleConnectorIncomingData Gin Uin L R}
    (C : VisibleConnectorConstructionData D etaMax) :
    ∃ HT : ℂ ≃ₜ ℂ,
      range (positiveExitComplexTrace C.terminal.p) = HT '' sphere (0 : ℂ) 1 := by
  have hComplex : positiveExitComplexTrace C.terminal.p =
      angularDescentComplex ∘ C.terminal.p := by
    funext s
    apply Complex.ext <;> simp [positiveExitComplexTrace, positiveExitComplexPoint, angularDescentComplex, Function.comp_def]
  have hSmooth : ContDiff ℝ ∞ (positiveExitComplexTrace C.terminal.p) := by
    rw [hComplex]
    exact angularDescentComplex_contDiff.comp C.terminal.p_smooth
  have hPeriod : Function.Periodic (positiveExitComplexTrace C.terminal.p) L := by
    intro s
    exact congrArg positiveExitComplexPoint (C.terminal.p_periodic s)
  have hInj : InjOn (positiveExitComplexTrace C.terminal.p) (Ico 0 L) := by
    intro s hs t ht he
    have hPoint : C.terminal.p s = C.terminal.p t := by
      simpa only [positiveExitComplexTrace, Function.comp_apply,
        retainedContour_exit_point] using congrArg seamComplexCoord he
    have hLift : C.terminal.p_periodic.lift (periodProjection L s) =
        C.terminal.p_periodic.lift (periodProjection L t) := by
      simpa only [periodicLift_coe] using hPoint
    have hCoe := C.terminal.source_injective hLift
    exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := L) (a := 0)
      (by simpa only [zero_add] using hs)
      (by simpa only [zero_add] using ht)).mp hCoe
  exact periodicComplexCurve_exists_filling hSmooth hPeriod hInj

section Connector
variable {Gin : Coord → ℝ} {Uin : Set Coord} {L R etaMax : ℝ} [Fact (0 < L)]
variable {D : VisibleConnectorIncomingData Gin Uin L R}

/-- The SAME retained actual gradient circle has a Jordan disk enclosing
both protected disks and lying inside the actual terminal source disk.
Positive radial pairing is ordinary input on the retained set; it can be
obtained by restricting the original filling input to its positive collar. -/
theorem dualRadialCompletionRetainedContour_geometry
    (C : VisibleConnectorConstructionData D etaMax)
    (eC eF : OpenPartialHomeomorph Coord Coord)
    (hClosed : closure C.source_annulus ⊆ eC.source)
    (hActualC : (eC : Coord → Coord) = planarGradient C.G)
    (hG : ContDiffOn ℝ ∞ C.G eC.source)
    (hi : ContDiffOn ℝ ∞ eC.symm eC.target)
    (hAgreement : EqOn eC.symm C.gradient_chart.symm C.gradient_annulus)
    {H : Coord → ℝ} {V Uc : Set Coord} {S0 : ℝ}
    (hV : IsOpen V) (hH : ContDiffOn ℝ ∞ H V)
    (hActualF : (eF : Coord → Coord) = planarGradient H)
    (hUc : IsOpen Uc)
    (hRetained : Uc ⊆ (dualRadialCompletionFillingDomain C eC ∩ eF.source) ∩ V)
    (hS0 : R < S0)
    (hCircle : quadraticRadialFillingRadiusLevel S0 ⊆ Uc)
    (hGerms : ∀ y ∈ Uc, H =ᶠ[𝓝 y] planarLegendre C.G eC)
    (hPositive : ∀ y ∈ Uc, 0 < planarGradient (planarLegendre C.G eC) y ⬝ᵥ y)
    {HOld GammaS Gamma0 : ℂ ≃ₜ ℂ}
    (hOldRange : range (positiveExitComplexTrace D.incoming.p) = HOld '' sphere (0 : ℂ) 1)
    (hGammaS0 : (0 : ℂ) ∈ jordanInterior GammaS)
    (hTargetOutside : eF.target ⊆ (seamComplexCoord '' closure (jordanInterior GammaS))ᶜ)
    (hRange : range (quadraticRadialFillingGradientComplexTrace H S0) = Gamma0 '' sphere (0 : ℂ) 1) :
      (0 : ℂ) ∈ jordanInterior Gamma0 ∧
      seamComplexCoord '' (Gamma0 '' sphere (0 : ℂ) 1) ⊆ C.source_annulus ∧
      closure (positiveExitInside D.incoming.p) ⊆ seamComplexCoord '' jordanInterior Gamma0 ∧
      seamComplexCoord '' closure (jordanInterior GammaS) ⊆ seamComplexCoord '' jordanInterior Gamma0 ∧
      seamComplexCoord '' closure (jordanInterior Gamma0) ⊆ positiveExitInside C.terminal.p := by
  have hS0pos : 0 < S0 := D.radius_pos.trans hS0
  have hCircleV : quadraticRadialFillingRadiusLevel S0 ⊆ V :=
    fun y hy => (hRetained (hCircle hy)).2

  have hPositiveH (theta : ℝ) :
      0 < planarGradient H (saddlePolarChart ![S0, theta]) ⬝ᵥ saddlePolarChart ![S0, theta] := by
    have hy : saddlePolarChart ![S0, theta] ∈ Uc :=
      hCircle (angularDescent_radius_polar (q := ![S0, theta]) hS0pos)
    rw [quadraticRadialFilling_gradient_eq_of_germ (hGerms _ hy)]
    exact hPositive _ hy
  have hOrigin : (0 : ℂ) ∈ jordanInterior Gamma0 :=
    quadraticRadialFilling_origin_inside_of_position_pairing hS0pos hV hH hCircleV
      hPositiveH hRange
  have hCircleFill (theta : ℝ) :
      saddlePolarChart ![S0, theta] ∈ dualRadialCompletionFillingDomain C eC :=
    (hRetained (hCircle (angularDescent_radius_polar (q := ![S0, theta]) hS0pos))).1.1
  have hCircleGerm (theta : ℝ) : H =ᶠ[𝓝 (saddlePolarChart ![S0, theta])] planarLegendre C.G eC :=
    hGerms _ (hCircle (angularDescent_radius_polar (q := ![S0, theta]) hS0pos))
  obtain ⟨_, _, hExterior⟩ := dualRadialCompletionFillingDomain_properties C eC hClosed hActualC
  have heG : ∀ p ∈ eC.source, eC p = planarGradient C.G p := fun p _ => congrFun hActualC p
  have hSource (theta : ℝ) : planarGradient H (saddlePolarChart ![S0, theta]) ∈ C.source_annulus := by
    have hy := hCircleFill theta
    have hRadius : planarRadius (saddlePolarChart ![S0, theta]) = S0 := by
      simpa only [Matrix.cons_val_zero] using angularDescent_radius_polar (q := ![S0, theta]) hS0pos
    have hAnnulus := hExterior _ hy (by simpa only [hRadius] using hS0)
    rw [quadraticRadialFilling_gradient_eq_of_germ (hCircleGerm theta),
      planarLegendre_gradient eC hG hi heG hy.1, hAgreement hAnnulus]
    rw [← C.gradient_chart_source]
    exact C.gradient_chart.map_target (by simpa only [C.gradient_chart_target] using hAnnulus)
  have hFrontier : seamComplexCoord '' (Gamma0 '' sphere (0 : ℂ) 1) ⊆ C.source_annulus := by
    rintro p ⟨z, hz, rfl⟩
    obtain ⟨theta, htheta⟩ := hRange.symm ▸ hz
    rw [← htheta]
    change seamComplexCoord (angularDescentComplex (planarGradient H
      (saddlePolarChart ![S0, theta]))) ∈ C.source_annulus
    rw [quadraticRadialFillingCoord_complex]
    exact hSource theta
  have hDisjointOldCoord := dualRadialCompletionFillingDomain_boundary_disjoint C eC hClosed hActualC
    hG hi hAgreement hS0 hCircleFill hCircleGerm hRange
  have hDisjointOld := dualRadialCompletionFillingDomain_complex_boundary_disjoint C hOldRange hDisjointOldCoord
  have hOldInside : positiveExitInside D.incoming.p = seamComplexCoord '' jordanInterior HOld :=
    dualRadialCompletionTraceInside_eq_of_range hOldRange D.incoming.source_jordan
  have hOld0 : (0 : ℂ) ∈ jordanInterior HOld := by
    have hz := D.incoming.source_enclosure
    rw [hOldInside] at hz
    obtain ⟨z, hz, he⟩ := hz
    have hz0 : z = 0 := seamComplexCoord.injective (by simpa only [map_zero] using he)
    rwa [hz0] at hz
  have hOldNested : closure (positiveExitInside D.incoming.p) ⊆
      seamComplexCoord '' jordanInterior Gamma0 := by
    rw [hOldInside, ← seamComplexCoord.image_closure]
    exact image_mono (dualRadialCompletionContainment_closed_subset HOld Gamma0 hOld0 hOrigin hDisjointOld)
  have hDisjointS : Disjoint (closure (jordanInterior GammaS)) (frontier (jordanInterior Gamma0)) := by
    apply disjoint_left.mpr
    intro z hzS hz0
    rw [frontier_jordanInterior, ← hRange] at hz0
    obtain ⟨theta, htheta⟩ := hz0
    let y := saddlePolarChart ![S0, theta]
    have hy : y ∈ Uc := hCircle (angularDescent_radius_polar (q := ![S0, theta]) hS0pos)
    have heTarget : eF y ∈ eF.target := eF.map_source (hRetained hy).1.2
    have hPoint : eF y = seamComplexCoord z := by
      rw [hActualF]
      calc
        planarGradient H y = seamComplexCoord (quadraticRadialFillingGradientComplexTrace H S0 theta) :=
          (quadraticRadialFillingCoord_complex _).symm
        _ = seamComplexCoord z := congrArg seamComplexCoord htheta
    apply hTargetOutside heTarget
    rw [hPoint]
    exact ⟨z, hzS, rfl⟩
  have hSNested := dualRadialCompletionContainment_closed_subset GammaS Gamma0 hGammaS0 hOrigin hDisjointS
  obtain ⟨HT, hTRange⟩ := retainedContour_terminal_filling C
  have hTInside : positiveExitInside C.terminal.p = seamComplexCoord '' jordanInterior HT :=
    dualRadialCompletionTraceInside_eq_of_range hTRange C.terminal.source_jordan
  have hInTerminal : frontier (jordanInterior Gamma0) ⊆ jordanInterior HT := by
    intro z hz
    have hCoord : seamComplexCoord z ∈ C.source_annulus := by
      apply hFrontier
      exact ⟨z, by rwa [← frontier_jordanInterior], rfl⟩
    rw [C.source_annulus_eq] at hCoord
    have hzInside := hCoord.1
    rw [hTInside] at hzInside
    obtain ⟨w, hw, he⟩ := hzInside
    have hwz : w = z := seamComplexCoord.injective he
    rwa [hwz] at hw
  have hTerminalNested : seamComplexCoord '' closure (jordanInterior Gamma0) ⊆ positiveExitInside C.terminal.p := by
    rw [hTInside]
    exact image_mono (closed_jordanInterior_subset_of_frontier_subset Gamma0 HT hInTerminal)
  exact ⟨hOrigin, hFrontier, hOldNested, image_mono hSNested, hTerminalNested⟩

/-- The standalone contour constructor is a wrapper around the same-object
geometry theorem. A producer returning Gamma0 should call geometry directly. -/
theorem exists_dualRadialCompletionRetainedContour
    (C : VisibleConnectorConstructionData D etaMax)
    (eC eF : OpenPartialHomeomorph Coord Coord)
    (hClosed : closure C.source_annulus ⊆ eC.source)
    (hActualC : (eC : Coord → Coord) = planarGradient C.G)
    (hG : ContDiffOn ℝ ∞ C.G eC.source)
    (hi : ContDiffOn ℝ ∞ eC.symm eC.target)
    (hAgreement : EqOn eC.symm C.gradient_chart.symm C.gradient_annulus)
    {H : Coord → ℝ} {V Uc : Set Coord} {S0 : ℝ}
    (hV : IsOpen V) (hH : ContDiffOn ℝ ∞ H V)
    (hActualF : (eF : Coord → Coord) = planarGradient H)
    (hUc : IsOpen Uc)
    (hRetained : Uc ⊆ (dualRadialCompletionFillingDomain C eC ∩ eF.source) ∩ V)
    (hS0 : R < S0)
    (hCircle : quadraticRadialFillingRadiusLevel S0 ⊆ Uc)
    (hGerms : ∀ y ∈ Uc, H =ᶠ[𝓝 y] planarLegendre C.G eC)
    (hPositive : ∀ y ∈ Uc, 0 < planarGradient (planarLegendre C.G eC) y ⬝ᵥ y)
    {HOld GammaS : ℂ ≃ₜ ℂ}
    (hOldRange : range (positiveExitComplexTrace D.incoming.p) = HOld '' sphere (0 : ℂ) 1)
    (hGammaS0 : (0 : ℂ) ∈ jordanInterior GammaS)
    (hTargetOutside : eF.target ⊆ (seamComplexCoord '' closure (jordanInterior GammaS))ᶜ) :
    ∃ Gamma0 : ℂ ≃ₜ ℂ,
      range (quadraticRadialFillingGradientComplexTrace H S0) = Gamma0 '' sphere (0 : ℂ) 1 ∧
      (0 : ℂ) ∈ jordanInterior Gamma0 ∧
      seamComplexCoord '' (Gamma0 '' sphere (0 : ℂ) 1) ⊆ C.source_annulus ∧
      closure (positiveExitInside D.incoming.p) ⊆ seamComplexCoord '' jordanInterior Gamma0 ∧
      seamComplexCoord '' closure (jordanInterior GammaS) ⊆ seamComplexCoord '' jordanInterior Gamma0 ∧
      seamComplexCoord '' closure (jordanInterior Gamma0) ⊆ positiveExitInside C.terminal.p := by
  have hS0pos : 0 < S0 := D.radius_pos.trans hS0
  have hCircleV : quadraticRadialFillingRadiusLevel S0 ⊆ V :=
    fun y hy => (hRetained (hCircle hy)).2
  have hInj : InjOn (planarGradient H) Uc := by
    rw [← hActualF]
    exact eF.injOn.mono (fun y hy => (hRetained hy).1.2)
  obtain ⟨Gamma0, hRange⟩ := quadraticRadialFillingGradientComplexTrace_exists_filling
    hS0pos hV hH hCircleV hCircle hInj
  refine ⟨Gamma0, hRange, ?_⟩
  exact dualRadialCompletionRetainedContour_geometry C eC eF hClosed hActualC hG hi hAgreement
    hV hH hActualF hUc hRetained hS0 hCircle hGerms hPositive hOldRange hGammaS0 hTargetOutside hRange
end Connector

/-- The retained cut belongs to the actual inverse target, so its whole
ambient neighborhood has literal inverse agreement with the old collar.
This uses ordinary actual map equality on an open set, not scalar overlap. -/
theorem dualRadialCompletionRetainedContour_inverse_neighborhood
    (eC eF : OpenPartialHomeomorph Coord Coord)
    {H : Coord → ℝ} {Uc : Set Coord} {S0 : ℝ} {Gamma0 : ℂ ≃ₜ ℂ}
    (hUc : IsOpen Uc)
    (hRetained : Uc ⊆ eC.target ∩ eF.source)
    (hCircle : quadraticRadialFillingRadiusLevel S0 ⊆ Uc)
    (hS0 : 0 < S0)
    (hActualF : (eF : Coord → Coord) = planarGradient H)
    (hActualRetained : EqOn (eF : Coord → Coord) eC.symm Uc)
    (hRange : range (quadraticRadialFillingGradientComplexTrace H S0) = Gamma0 '' sphere (0 : ℂ) 1) :
    ∃ W : Set Coord, IsOpen W ∧
      seamComplexCoord '' (Gamma0 '' sphere (0 : ℂ) 1) ⊆ W ∧
      W ⊆ eF.target ∩ eC.source ∧
      ∀ x ∈ W, eF.symm x ∈ Uc ∧ eF.symm x = eC x := by
  let W : Set Coord := eF.target ∩ eF.symm ⁻¹' Uc
  have hW : IsOpen W := eF.symm.continuousOn.isOpen_inter_preimage eF.open_target hUc
  have hRecovery : ∀ x ∈ W, x ∈ eC.source ∧ eF.symm x = eC x := by
    intro x hx
    let y := eF.symm x
    have hy : y ∈ Uc := hx.2
    have hyC : y ∈ eC.target := (hRetained hy).1
    have hForward : eC.symm y = x := (hActualRetained hy).symm.trans (eF.right_inv hx.1)
    have hxC : x ∈ eC.source := by
      rw [← hForward]
      exact eC.map_target hyC
    refine ⟨hxC, ?_⟩
    calc
      y = eC (eC.symm y) := (eC.right_inv hyC).symm
      _ = eC x := congrArg eC hForward
  refine ⟨W, hW, ?_, fun x hx => ⟨hx.1, (hRecovery x hx).1⟩,
    fun x hx => ⟨hx.2, (hRecovery x hx).2⟩⟩
  rintro x ⟨z, hz, rfl⟩
  obtain ⟨theta, htheta⟩ := hRange.symm ▸ hz
  let y := saddlePolarChart ![S0, theta]
  have hy : y ∈ Uc := hCircle (angularDescent_radius_polar (q := ![S0, theta]) hS0)
  have hPoint : seamComplexCoord z = eF y := by
    rw [hActualF, ← htheta]
    exact quadraticRadialFillingCoord_complex _
  rw [hPoint]
  refine ⟨eF.map_source (hRetained hy).2, ?_⟩
  change eF.symm (eF y) ∈ Uc
  rw [eF.left_inv (hRetained hy).2]
  exact hy

end
end TightVer401
