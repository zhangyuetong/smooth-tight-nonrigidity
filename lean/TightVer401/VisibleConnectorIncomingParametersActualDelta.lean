import TightVer401.VisibleConnectorIncomingParametersDelta
import TightVer401.VisibleConnectorIncomingParametersCoefficients

/-! The actual old Delta at the SAME displaced seam is produced from smooth
joint source/gradient/ruling families. An open axis neighborhood mapping into
the old family domain is constructed; no whole-phase-domain containment is
assumed and no independent inverse is selected.
-/
namespace TightVer401
noncomputable section
open Set Function OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Same-e lower-old-Delta positivity, with actual slice derivatives. -/
theorem visibleConnectorIncomingParameters_uniform_actual_lower_delta
    {L : ℝ} [Fact (0 < L)] {p : ℝ → Coord}
    (e : OpenPartialHomeomorph (ℝ × (AddCircle L × ℝ)) (ℝ × Coord))
    {Omega : Set (ℝ × ℝ)} {P G W : ℝ × ℝ → Coord}
    (hOmega : IsOpen Omega)
    (hP : ContDiffOn ℝ ∞ P Omega) (hG : ContDiffOn ℝ ∞ G Omega)
    (hW : ContDiffOn ℝ ∞ W Omega)
    (hOmegaAxis : ∀ s, (0, s) ∈ Omega)
    (hPL : ∀ rho, Periodic (fun s => P (rho, s)) L)
    (hGL : ∀ rho, Periodic (fun s => G (rho, s)) L)
    (hWL : ∀ rho, Periodic (fun s => W (rho, s)) L)
    (hA0 : ∀ s, 0 < visibleConnectorA
      (fun t => P (0, t)) (fun t => W (0, t)) s)
    (hD : IsOpen (visibleConnectorDisplacedRealPhaseDomain e p))
    (ha : ContDiffOn ℝ ∞ (visibleConnectorDisplacedRealPhase e p)
      (visibleConnectorDisplacedRealPhaseDomain e p))
    (hb : ContDiffOn ℝ ∞
      (fun z => (visibleConnectorDisplacedNativeSolution e p z).2)
      (visibleConnectorDisplacedRealPhaseDomain e p))
    (haxis : ∀ s, (0, s) ∈ visibleConnectorDisplacedRealPhaseDomain e p)
    (ha0 : ∀ s, visibleConnectorDisplacedRealPhase e p (0, s) = s)
    (hb0 : ∀ s, (visibleConnectorDisplacedNativeSolution e p (0, s)).2 = 0)
    (hashift : ∀ rho s, visibleConnectorDisplacedRealPhase e p (rho, s + L) =
      visibleConnectorDisplacedRealPhase e p (rho, s) + L)
    (hbL : ∀ rho, Periodic
      (fun s => (visibleConnectorDisplacedNativeSolution e p (rho, s)).2) L) :
    ∃ delta > 0, ∀ rho s, |rho| < delta →
      0 < visibleConnectorDelta
        (fun t => P (rho, t)) (fun t => G (rho, t)) (fun t => W (rho, t))
        (![visibleConnectorDisplacedRealPhase e p (rho, s),
          (visibleConnectorDisplacedNativeSolution e p (rho, s)).2] : Coord) := by
  let D := visibleConnectorDisplacedRealPhaseDomain e p
  let a := visibleConnectorDisplacedRealPhase e p
  let F := fun z : ℝ × ℝ => (z.1, a z)
  let D0 := D ∩ F ⁻¹' Omega
  have hFc : ContinuousOn F D := continuous_fst.continuousOn.prodMk ha.continuousOn
  have hD0 : IsOpen D0 := hFc.isOpen_inter_preimage hD hOmega
  have hD0axis (s : ℝ) : (0, s) ∈ D0 := by
    refine ⟨haxis s, ?_⟩
    change (0, visibleConnectorDisplacedRealPhase e p (0, s)) ∈ Omega
    rw [ha0]
    exact hOmegaAxis s
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
  obtain ⟨delta, hdelta, hpositive⟩ :=
    visibleConnectorIncomingParameters_uniform_lower_delta e
      (A := A) (B := B) (C := C) (D0 := D0) hD0 inter_subset_left
      ha hb hD0axis ha0 hb0 hashift hbL hAc hBc hCc
      (fun z hz => hz.2) hAL hBL hCL hA0
  refine ⟨delta, hdelta, ?_⟩
  intro rho s hρ
  simpa only [visibleConnectorDelta, Matrix.cons_val_zero, Matrix.cons_val_one, A, B, C]
    using hpositive rho s hρ

end
end TightVer401
