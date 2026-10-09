import TightVer401.VisibleConnectorIncomingParametersCoefficients
import TightVer401.VisibleConnectorDisplacedSeamPhaseSigns

/-! An actual fixed-eta smooth periodic family produces its coefficient rho
margin. These are literal fixed-rho curve derivatives, and no displaced
coefficient sign or connector construction is granted.
-/
namespace TightVer401
noncomputable section
open Set Function Filter Metric OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- Actual joint smoothness, central strict signs and periodicity construct a
uniform positive A/B/C margin for the SAME family after eta has been fixed. -/
theorem visibleConnectorIncomingParameters_uniform_actual_coefficient_signs
    {L : ℝ} [Fact (0 < L)] {Omega : Set (ℝ × ℝ)}
    {P G W : ℝ × ℝ → Coord}
    (hOmega : IsOpen Omega)
    (hP : ContDiffOn ℝ ∞ P Omega) (hG : ContDiffOn ℝ ∞ G Omega)
    (hW : ContDiffOn ℝ ∞ W Omega)
    (haxis : ∀ s, (0, s) ∈ Omega)
    (hPL : ∀ rho, Periodic (fun s => P (rho, s)) L)
    (hGL : ∀ rho, Periodic (fun s => G (rho, s)) L)
    (hWL : ∀ rho, Periodic (fun s => W (rho, s)) L)
    (hcentral : ∀ s,
      0 < visibleConnectorA (fun t => P (0, t)) (fun t => W (0, t)) s ∧
      0 < visibleConnectorB (fun t => G (0, t)) (fun t => W (0, t)) s ∧
      0 < visibleConnectorC (fun t => G (0, t)) (fun t => W (0, t)) s) :
    ∃ delta > 0, ∀ rho s, |rho| < delta →
      0 < visibleConnectorA (fun t => P (rho, t)) (fun t => W (rho, t)) s ∧
      0 < visibleConnectorB (fun t => G (rho, t)) (fun t => W (rho, t)) s ∧
      0 < visibleConnectorC (fun t => G (rho, t)) (fun t => W (rho, t)) s := by
  let A := fun z : ℝ × ℝ => visibleConnectorA
    (fun t => P (z.1, t)) (fun t => W (z.1, t)) z.2
  let B := fun z : ℝ × ℝ => visibleConnectorB
    (fun t => G (z.1, t)) (fun t => W (z.1, t)) z.2
  let C := fun z : ℝ × ℝ => visibleConnectorC
    (fun t => G (z.1, t)) (fun t => W (z.1, t)) z.2
  obtain ⟨hAc, hBc, hCc⟩ :=
    visibleConnectorIncomingParametersFamily_actual_coefficients_continuousOn hOmega hP hG hW
  obtain ⟨hAL, hBL, hCL⟩ :=
    visibleConnectorIncomingParametersFamily_actual_coefficients_periodic hPL hGL hWL
  let VA := Omega ∩ A ⁻¹' Ioi 0
  let VB := VA ∩ B ⁻¹' Ioi 0
  let V := VB ∩ C ⁻¹' Ioi 0
  have hVA : IsOpen VA := hAc.isOpen_inter_preimage hOmega isOpen_Ioi
  have hVB : IsOpen VB :=
    (hBc.mono (show VA ⊆ Omega from inter_subset_left)).isOpen_inter_preimage hVA isOpen_Ioi
  have hV : IsOpen V :=
    (hCc.mono (show VB ⊆ Omega from inter_subset_left.trans inter_subset_left)).isOpen_inter_preimage
      hVB isOpen_Ioi
  let K : Set (ℝ × ℝ) := ({0} : Set ℝ) ×ˢ Icc 0 L
  have hK : IsCompact K := isCompact_singleton.prod isCompact_Icc
  have hKV : K ⊆ V := by
    intro z hz
    have he : z = (0, z.2) := Prod.ext (mem_singleton_iff.mp hz.1) rfl
    rw [he]
    exact ⟨⟨⟨haxis z.2, (hcentral z.2).1⟩, (hcentral z.2).2.1⟩, (hcentral z.2).2.2⟩
  obtain ⟨c, hc, hcV⟩ := hK.exists_cthickening_subset_open hV hKV
  refine ⟨c / 2, half_pos hc, ?_⟩
  intro rho s hρ
  let x := AddCircle.equivIco L 0 (periodProjection L s)
  have hx : (x : ℝ) ∈ Icc 0 L := Ico_subset_Icc_self (by
    simpa only [zero_add] using x.property)
  have hxq : periodProjection L (x : ℝ) = periodProjection L s := AddCircle.coe_equivIco
  have hzV : (rho, (x : ℝ)) ∈ V := by
    apply hcV
    apply Metric.thickening_subset_cthickening c K
    apply Metric.mem_thickening_iff.mpr
    refine ⟨(0, (x : ℝ)), ⟨mem_singleton _, hx⟩, ?_⟩
    rw [Prod.dist_eq, dist_self]
    simp only [Real.dist_eq, sub_zero]
    exact max_lt (hρ.trans (half_lt_self hc)) hc
  have hAeq := congrArg (hAL rho).lift hxq
  have hBeq := congrArg (hBL rho).lift hxq
  have hCeq := congrArg (hCL rho).lift hxq
  rw [periodicLift_coe, periodicLift_coe] at hAeq hBeq hCeq
  have hAx : 0 < visibleConnectorA
      (fun t => P (rho, t)) (fun t => W (rho, t)) (x : ℝ) := hzV.1.1.2
  have hBx : 0 < visibleConnectorB
      (fun t => G (rho, t)) (fun t => W (rho, t)) (x : ℝ) := hzV.1.2
  have hCx : 0 < visibleConnectorC
      (fun t => G (rho, t)) (fun t => W (rho, t)) (x : ℝ) := hzV.2
  rw [hAeq] at hAx
  rw [hBeq] at hBx
  rw [hCeq] at hCx
  exact ⟨hAx, hBx, hCx⟩

end
end TightVer401
