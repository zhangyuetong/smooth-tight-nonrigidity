import TightVer401.VisibleConnectorIncomingTerminalQuotient
import TightVer401.VisibleConnectorIncomingTerminalLocalStability

/-! Actual displaced-terminal positive filling from SAME joint P/G/W.
The nonzero-C domain, uniform full-phase smoothness threshold and actual axis
C1 continuity are constructed from the source family. Neither terminal
smoothness nor terminal convergence is an input to this application. -/
namespace TightVer401
noncomputable section
open Set Function Filter Metric OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private theorem incomingTerminalActual_uniform_axis_domain
    {L : ℝ} (hL : 0 < L) {Omega : Set (ℝ × ℝ)}
    (hOmega : IsOpen Omega) (haxis : ∀ s, (0, s) ∈ Omega)
    (hperiod : ∀ rho, Periodic (fun s => (rho, s) ∈ Omega) L) :
    ∃ rhoMax > 0, ∀ rho s, |rho| < rhoMax → (rho, s) ∈ Omega := by
  have hnear : ∀ᶠ rho in 𝓝 (0 : ℝ), ∀ s ∈ Icc (0 : ℝ) L,
      (rho, s) ∈ Omega := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro s hs
    exact hOmega.mem_nhds (haxis s)
  obtain ⟨rhoMax, hrhoMax, hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨rhoMax, hrhoMax, ?_⟩
  intro rho s hrho
  obtain ⟨n, hn, _⟩ := existsUnique_sub_zsmul_mem_Ico hL s 0
  simp only [mem_Ico, zero_add] at hn
  have hrhoBall : rho ∈ ball (0 : ℝ) rhoMax := by
    simpa only [mem_ball, Real.dist_eq, sub_zero] using hrho
  have he := hball hrhoBall (s - n • L) ⟨hn.1, hn.2.le⟩
  have hp := (hperiod rho).sub_zsmul_eq n (x := s)
  change ((rho, s - n • L) ∈ Omega) = ((rho, s) ∈ Omega) at hp
  rw [hp] at he
  exact he

/-- Smooth actual source/gradient/ruling families construct ONE positive rho
threshold for the SAME displaced terminal. Original C positivity and terminal
geometry refer only to rho=0. Every displaced norm/determinant, Jordan
injectivity, filling, origin enclosure and frontier identity is a conclusion. -/
theorem visibleConnectorIncomingTerminal_actualFamily_exists_positive_filling
    {P G W : ℝ × ℝ → Coord} {Omega : Set (ℝ × ℝ)} {L M : ℝ}
    (hL : 0 < L) (hOmega : IsOpen Omega)
    (hP : ContDiffOn ℝ ∞ P Omega) (hG : ContDiffOn ℝ ∞ G Omega)
    (hW : ContDiffOn ℝ ∞ W Omega)
    (haxis : ∀ s, (0, s) ∈ Omega)
    (hOmegaPeriod : ∀ rho, Periodic (fun s => (rho, s) ∈ Omega) L)
    (hPL : ∀ rho, Periodic (fun s => P (rho, s)) L)
    (hGL : ∀ rho, Periodic (fun s => G (rho, s)) L)
    (hWL : ∀ rho, Periodic (fun s => W (rho, s)) L)
    (hC0 : ∀ s, 0 < visibleConnectorC (fun t => G (0, t)) (fun t => W (0, t)) s)
    (hnorm : ∀ s ∈ Icc (0 : ℝ) L,
      M < ‖positiveExitComplexPoint (visibleConnectorIncomingTerminalActualFamily P G W (0, s))‖)
    (hdet : ∀ s ∈ Icc (0 : ℝ) L, 0 < visibleConnectorDet
      (visibleConnectorIncomingTerminalActualFamily P G W (0, s))
      (deriv (fun t => visibleConnectorIncomingTerminalActualFamily P G W (0, t)) s))
    (hne : ∀ s, positiveExitComplexTrace
      (fun t => visibleConnectorIncomingTerminalActualFamily P G W (0, t)) s ≠ 0)
    (hturn : HasPositiveArgumentTurn (positiveExitComplexTrace
      (fun t => visibleConnectorIncomingTerminalActualFamily P G W (0, t))) L) :
    ∃ rhoMax > 0, ∀ rho, |rho| < rhoMax →
      let T := fun s => visibleConnectorIncomingTerminalActualFamily P G W (rho, s)
      (∀ s, M < ‖positiveExitComplexTrace T s‖) ∧
      (∀ s, 0 < visibleConnectorDet (T s) (deriv T s)) ∧
      InjOn T (Ico (0 : ℝ) L) ∧
      ∃ H : ℂ ≃ₜ ℂ,
        DualRadialCompletionPositiveTrace H (visibleConnectorTerminalNormalizedTrace L T) ∧
        (0 : ℂ) ∈ jordanInterior H ∧
        range (positiveExitComplexTrace T) = frontier (jordanInterior H) := by
  let C : ℝ × ℝ → ℝ := fun z => visibleConnectorC
    (fun s => G (z.1, s)) (fun s => W (z.1, s)) z.2
  let OmegaT : Set (ℝ × ℝ) := Omega ∩ C ⁻¹' ({(0 : ℝ)}ᶜ)
  obtain ⟨hAc, hBc, hCc⟩ :=
    visibleConnectorIncomingParametersFamily_actual_coefficients_continuousOn hOmega hP hG hW
  have hCcont : ContinuousOn C Omega := hCc
  have hOmegaT : IsOpen OmegaT :=
    hCcont.isOpen_inter_preimage hOmega
      (isClosed_singleton : IsClosed ({(0 : ℝ)} : Set ℝ)).isOpen_compl
  have hOmegaTAxis (s : ℝ) : (0, s) ∈ OmegaT := by
    refine ⟨haxis s, ?_⟩
    change C (0, s) ∉ ({(0 : ℝ)} : Set ℝ)
    simpa only [C, mem_singleton_iff] using (hC0 s).ne'
  obtain ⟨hAL, hBL, hCL⟩ :=
    visibleConnectorIncomingParametersFamily_actual_coefficients_periodic hPL hGL hWL
  have hCperiod (rho : ℝ) : Periodic (fun s => C (rho, s)) L := hCL rho
  have hOmegaTPeriod (rho : ℝ) : Periodic (fun s => (rho, s) ∈ OmegaT) L := by
    intro s
    change ((rho, s + L) ∈ Omega ∧ C (rho, s + L) ∈ (({(0 : ℝ)} : Set ℝ)ᶜ)) =
      ((rho, s) ∈ Omega ∧ C (rho, s) ∈ (({(0 : ℝ)} : Set ℝ)ᶜ))
    have hOeq : ((rho, s + L) ∈ Omega) = ((rho, s) ∈ Omega) := hOmegaPeriod rho s
    have hCeq : C (rho, s + L) = C (rho, s) := hCperiod rho s
    rw [hOeq, hCeq]
  have hCne : ∀ z ∈ OmegaT, visibleConnectorC
      (fun s => G (z.1, s)) (fun s => W (z.1, s)) z.2 ≠ 0 := by
    intro z hz
    have he := hz.2
    change C z ∉ ({(0 : ℝ)} : Set ℝ) at he
    simpa only [C, mem_singleton_iff] using he
  have hPT := hP.mono (inter_subset_left : OmegaT ⊆ Omega)
  have hGT := hG.mono (inter_subset_left : OmegaT ⊆ Omega)
  have hWT := hW.mono (inter_subset_left : OmegaT ⊆ Omega)
  let F := visibleConnectorIncomingTerminalActualFamily P G W
  have hTsmooth : ContDiffOn ℝ ∞ F OmegaT :=
    visibleConnectorIncomingTerminal_actualFamily_contDiffOn hOmegaT hPT hGT hWT hCne
  obtain ⟨hFc, hFdc⟩ :=
    visibleConnectorIncomingTerminal_actualFamily_C1 hOmegaT hPT hGT hWT hCne
  obtain ⟨rhoSmooth, hrhoSmooth, hfull⟩ :=
    incomingTerminalActual_uniform_axis_domain hL hOmegaT hOmegaTAxis hOmegaTPeriod
  have hFs : ∀ rho, |rho| < rhoSmooth → ContDiff ℝ ∞ (fun s => F (rho, s)) := by
    intro rho hrho
    apply contDiffOn_univ.mp
    exact hTsmooth.comp ((contDiff_const (c := rho)).prodMk contDiff_id).contDiffOn
      (fun s _ => hfull rho s hrho)
  have hFp (rho : ℝ) : Periodic (fun s => F (rho, s)) L := by
    intro s
    change P (rho, s + L) +
      (visibleConnectorA (fun t => P (rho, t)) (fun t => W (rho, t)) (s + L) /
        visibleConnectorC (fun t => G (rho, t)) (fun t => W (rho, t)) (s + L)) • W (rho, s + L) =
      P (rho, s) +
      (visibleConnectorA (fun t => P (rho, t)) (fun t => W (rho, t)) s /
        visibleConnectorC (fun t => G (rho, t)) (fun t => W (rho, t)) s) • W (rho, s)
    have hPe : P (rho, s + L) = P (rho, s) := hPL rho s
    have hAe : visibleConnectorA (fun t => P (rho, t)) (fun t => W (rho, t)) (s + L) =
        visibleConnectorA (fun t => P (rho, t)) (fun t => W (rho, t)) s := hAL rho s
    have hCe : visibleConnectorC (fun t => G (rho, t)) (fun t => W (rho, t)) (s + L) =
        visibleConnectorC (fun t => G (rho, t)) (fun t => W (rho, t)) s := hCL rho s
    have hWe : W (rho, s + L) = W (rho, s) := hWL rho s
    rw [hPe, hAe, hCe, hWe]
  have hFaxis : ∀ s ∈ Icc (0 : ℝ) L, ContinuousAt F (0, s) := by
    intro s hs
    exact (hFc _ (hOmegaTAxis s)).continuousAt (hOmegaT.mem_nhds (hOmegaTAxis s))
  have hFdaxis : ∀ s ∈ Icc (0 : ℝ) L, ContinuousAt
      (fun z : ℝ × ℝ => deriv (fun t => F (z.1, t)) z.2) (0, s) := by
    intro s hs
    exact (hFdc _ (hOmegaTAxis s)).continuousAt (hOmegaT.mem_nhds (hOmegaTAxis s))
  exact visibleConnectorIncomingTerminal_exists_local_displaced_positive_filling
    hL hrhoSmooth hFs hFp hFaxis hFdaxis hnorm hdet hne hturn

end
end TightVer401

