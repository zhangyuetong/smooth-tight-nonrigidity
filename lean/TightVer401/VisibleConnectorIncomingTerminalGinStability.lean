import TightVer401.VisibleConnectorIncomingTerminalActualStability
import TightVer401.VisibleConnectorDisplacedSeamGinFamily

/-! Actual terminal stability for the literal eta-fixed Gin family of D.
Joint smoothness, visibility-domain periodicity and baseline terminal identity
are derived from D and the SAME chosen w0. No generic joint-family regularity,
terminal convergence or displaced filling is an input. -/
namespace TightVer401
noncomputable section
open Set Function Filter OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private theorem incomingTerminalGin_uniform_axis_domain
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
  have hrhoBall : rho ∈ Metric.ball (0 : ℝ) rhoMax := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hrho
  have he := hball hrhoBall (s - n • L) ⟨hn.1, hn.2.le⟩
  have hp := (hperiod rho).sub_zsmul_eq n (x := s)
  change ((rho, s - n • L) ∈ Omega) = ((rho, s) ∈ Omega) at hp
  rw [hp] at he
  exact he
/-- The actual incoming Gin data and SAME fixed-eta ruling produce a positive
terminal rho threshold. Baseline geometry is consumed only for the original
actual terminal of p/gamma/w0; every small-rho filling is constructed. -/
theorem visibleConnectorIncomingTerminal_Gin_exists_positive_filling
    {Gin : Coord → ℝ} {Uin : Set Coord} {L R eta M : ℝ} [Fact (0 < L)]
    (D : VisibleConnectorIncomingData Gin Uin L R) {w0 : ℝ → Coord}
    (hw0 : ContDiff ℝ ∞ w0) (hw0L : Periodic w0 L)
    (hw0same : ∀ s, w0 s = visibleConnectorGinRotatedRuling R eta D.incoming.gamma s)
    (hC0 : ∀ s, 0 < visibleConnectorC D.incoming.gamma w0 s)
    (hnorm : ∀ s ∈ Icc (0 : ℝ) L, M < ‖positiveExitComplexPoint
      (visibleConnectorActualTerminalSource D.incoming.p D.incoming.gamma w0 s)‖)
    (hdet : ∀ s ∈ Icc (0 : ℝ) L, 0 < visibleConnectorDet
      (visibleConnectorActualTerminalSource D.incoming.p D.incoming.gamma w0 s)
      (deriv (visibleConnectorActualTerminalSource D.incoming.p D.incoming.gamma w0) s))
    (hne : ∀ s, positiveExitComplexTrace
      (visibleConnectorActualTerminalSource D.incoming.p D.incoming.gamma w0) s ≠ 0)
    (hturn : HasPositiveArgumentTurn (positiveExitComplexTrace
      (visibleConnectorActualTerminalSource D.incoming.p D.incoming.gamma w0)) L) :
    ∃ rhoMax > 0, ∀ rho, |rho| < rhoMax →
      let pc := fun t => visibleConnectorGinDisplacedPosition D.incoming.p w0 (rho, t)
      let gc := fun t => visibleConnectorGinDisplacedGradient Gin D.incoming.p w0 (rho, t)
      let wc := fun t => visibleConnectorGinDisplacedRuling Gin R eta D.incoming.p w0 (rho, t)
      let T := visibleConnectorActualTerminalSource pc gc wc
      (∀ s, (rho, s) ∈ visibleConnectorGinDisplacedVisibilityDomain Gin Uin R D.incoming.p w0) ∧
      (∀ s, 0 < visibleConnectorC gc wc s) ∧
      ContDiff ℝ ∞ T ∧ Periodic T L ∧
      (∀ s, M < ‖positiveExitComplexTrace T s‖) ∧
      (∀ s, 0 < visibleConnectorDet (T s) (deriv T s)) ∧
      InjOn T (Ico (0 : ℝ) L) ∧
      ∃ H : ℂ ≃ₜ ℂ,
        DualRadialCompletionPositiveTrace H (visibleConnectorTerminalNormalizedTrace L T) ∧
        (0 : ℂ) ∈ jordanInterior H ∧
        range (positiveExitComplexTrace T) = frontier (jordanInterior H) := by
  have hgamma (s : ℝ) : D.incoming.gamma s = planarGradient Gin (D.incoming.p s) := by
    exact congrFun D.incoming.actual_gradient s
  have hcomplex : angularDescentComplex = positiveExitComplexPoint := by
    funext q
    apply Complex.ext <;> simp [positiveExitComplexPoint, angularDescentComplex]
  have hmargin (s : ℝ) : R < ‖Complex.I * angularDescentComplex (D.incoming.gamma s)‖ := by
    have he := (D.visibility s).1
    rw [D.actual_delta] at he
    simpa only [hcomplex] using he
  obtain ⟨hpc, _, hgc, hV, hVsub, hVaxis, hW,
    hpcL, hgcL, hWL, hperiodV, hgc0, hW0⟩ :=
    visibleConnectorGinDisplacedFamily_properties D.radius_pos D.domain_open
      D.potential_smooth D.incoming.p_smooth hw0 D.incoming.p_periodic hw0L
      (fun s => D.incoming.p_in_domain (mem_univ s)) hgamma hmargin hw0same
  let P := visibleConnectorGinDisplacedPosition D.incoming.p w0
  let G := visibleConnectorGinDisplacedGradient Gin D.incoming.p w0
  let W := visibleConnectorGinDisplacedRuling Gin R eta D.incoming.p w0
  let V := visibleConnectorGinDisplacedVisibilityDomain Gin Uin R D.incoming.p w0
  have hVperiod (rho : ℝ) : Periodic (fun s => (rho, s) ∈ V) L := by
    intro s
    exact propext (hperiodV rho s)
  have hpzero : (fun t => P (0, t)) = D.incoming.p := by
    funext t
    simp [P, visibleConnectorGinDisplacedPosition]
  have hgzero : (fun t => G (0, t)) = D.incoming.gamma := funext hgc0
  have hwzero : (fun t => W (0, t)) = w0 := funext hW0
  have hCzero : ∀ s, 0 < visibleConnectorC (fun t => G (0, t)) (fun t => W (0, t)) s := by
    rw [hgzero, hwzero]
    exact hC0
  have hTzero : (fun t => visibleConnectorIncomingTerminalActualFamily P G W (0, t)) =
      visibleConnectorActualTerminalSource D.incoming.p D.incoming.gamma w0 := by
    funext t
    change visibleConnectorActualTerminalSource
      (fun r => P (0, r)) (fun r => G (0, r)) (fun r => W (0, r)) t = _
    rw [hpzero, hgzero, hwzero]
  have hnormActual : ∀ s ∈ Icc (0 : ℝ) L, M < ‖positiveExitComplexPoint
      (visibleConnectorIncomingTerminalActualFamily P G W (0, s))‖ := by
    intro s hs
    have he := congrFun hTzero s
    rw [he]
    exact hnorm s hs
  have hdetActual : ∀ s ∈ Icc (0 : ℝ) L, 0 < visibleConnectorDet
      (visibleConnectorIncomingTerminalActualFamily P G W (0, s))
      (deriv (fun t => visibleConnectorIncomingTerminalActualFamily P G W (0, t)) s) := by
    intro s hs
    rw [hTzero, congrFun hTzero s]
    exact hdet s hs
  have hneActual : ∀ s, positiveExitComplexTrace
      (fun t => visibleConnectorIncomingTerminalActualFamily P G W (0, t)) s ≠ 0 := by
    rw [hTzero]
    exact hne
  have hturnActual : HasPositiveArgumentTurn (positiveExitComplexTrace
      (fun t => visibleConnectorIncomingTerminalActualFamily P G W (0, t))) L := by
    rw [hTzero]
    exact hturn
  obtain ⟨rhoTerminal, hrhoTerminal, hterminal⟩ :=
    visibleConnectorIncomingTerminal_actualFamily_exists_positive_filling
      D.incoming.period_pos hV hpc.contDiffOn (hgc.mono hVsub) hW hVaxis
      hVperiod hpcL hgcL hWL hCzero hnormActual hdetActual hneActual hturnActual
  let C : ℝ × ℝ → ℝ := fun z => visibleConnectorC
    (fun t => G (z.1, t)) (fun t => W (z.1, t)) z.2
  let Vplus := V ∩ C ⁻¹' Ioi (0 : ℝ)
  obtain ⟨_, _, hCc⟩ := visibleConnectorIncomingParametersFamily_actual_coefficients_continuousOn
    hV hpc.contDiffOn (hgc.mono hVsub) hW
  have hCcont : ContinuousOn C V := hCc
  have hVplus : IsOpen Vplus := hCcont.isOpen_inter_preimage hV isOpen_Ioi
  have hVplusAxis (s : ℝ) : (0, s) ∈ Vplus := ⟨hVaxis s, hCzero s⟩
  obtain ⟨hAL, _, hCL⟩ :=
    visibleConnectorIncomingParametersFamily_actual_coefficients_periodic hpcL hgcL hWL
  have hVplusPeriod (rho : ℝ) : Periodic (fun s => (rho, s) ∈ Vplus) L := by
    intro s
    change ((rho, s + L) ∈ V ∧ 0 < C (rho, s + L)) =
      ((rho, s) ∈ V ∧ 0 < C (rho, s))
    have hCe : C (rho, s + L) = C (rho, s) := hCL rho s
    have hVe : ((rho, s + L) ∈ V) = ((rho, s) ∈ V) := hVperiod rho s
    rw [hVe, hCe]
  obtain ⟨rhoDomain, hrhoDomain, hfull⟩ :=
    incomingTerminalGin_uniform_axis_domain D.incoming.period_pos hVplus hVplusAxis hVplusPeriod
  have hCne : ∀ z ∈ Vplus, visibleConnectorC
      (fun t => G (z.1, t)) (fun t => W (z.1, t)) z.2 ≠ 0 := by
    intro z hz
    exact (show 0 < C z from hz.2).ne'
  have hTjoint : ContDiffOn ℝ ∞ (visibleConnectorIncomingTerminalActualFamily P G W) Vplus :=
    visibleConnectorIncomingTerminal_actualFamily_contDiffOn hVplus
      (hpc.contDiffOn.mono inter_subset_left)
      ((hgc.mono hVsub).mono inter_subset_left) (hW.mono inter_subset_left) hCne
  refine ⟨min rhoDomain rhoTerminal, lt_min hrhoDomain hrhoTerminal, ?_⟩
  intro rho hrho
  dsimp only
  have hrhoD : |rho| < rhoDomain := hrho.trans_le (min_le_left _ _)
  have hrhoT : |rho| < rhoTerminal := hrho.trans_le (min_le_right _ _)
  have hTs : ContDiff ℝ ∞ (fun s => visibleConnectorIncomingTerminalActualFamily P G W (rho, s)) := by
    apply contDiffOn_univ.mp
    exact hTjoint.comp ((contDiff_const (c := rho)).prodMk contDiff_id).contDiffOn
      (fun s _ => hfull rho s hrhoD)
  have hTp : Periodic (fun s => visibleConnectorIncomingTerminalActualFamily P G W (rho, s)) L := by
    intro s
    change P (rho, s + L) +
      (visibleConnectorA (fun t => P (rho, t)) (fun t => W (rho, t)) (s + L) /
        visibleConnectorC (fun t => G (rho, t)) (fun t => W (rho, t)) (s + L)) • W (rho, s + L) =
      P (rho, s) +
      (visibleConnectorA (fun t => P (rho, t)) (fun t => W (rho, t)) s /
        visibleConnectorC (fun t => G (rho, t)) (fun t => W (rho, t)) s) • W (rho, s)
    have hPe : P (rho, s + L) = P (rho, s) := hpcL rho s
    have hAe : visibleConnectorA (fun t => P (rho, t)) (fun t => W (rho, t)) (s + L) =
        visibleConnectorA (fun t => P (rho, t)) (fun t => W (rho, t)) s := hAL rho s
    have hCe : visibleConnectorC (fun t => G (rho, t)) (fun t => W (rho, t)) (s + L) =
        visibleConnectorC (fun t => G (rho, t)) (fun t => W (rho, t)) s := hCL rho s
    have hWe : W (rho, s + L) = W (rho, s) := hWL rho s
    rw [hPe, hAe, hCe, hWe]
  exact ⟨fun s => (hfull rho s hrhoD).1, fun s => (hfull rho s hrhoD).2,
    hTs, hTp, hterminal rho hrhoT⟩

end
end TightVer401

