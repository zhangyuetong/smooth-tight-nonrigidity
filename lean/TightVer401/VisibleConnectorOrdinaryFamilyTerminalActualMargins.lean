import TightVer401.VisibleConnectorOrdinaryFamilyTerminalMargins
import TightVer401.VisibleConnectorIncomingTerminalQuotient

/-! Actual joint terminal margins from one source/gradient/ruling family.
The positive coefficient domain and one full-phase domain threshold are
constructed. Endpoint gradients are computed from the literal quotient. -/
namespace TightVer401
noncomputable section
open Set Function Filter Metric OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix

private theorem ordinaryActualMargins_J_smooth : ContDiff ℝ ∞ visibleConnectorJ := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ (fun v : Coord => -(v 1))
    exact (contDiff_apply ℝ ℝ (1 : Fin 2)).neg
  · change ContDiff ℝ ∞ (fun v : Coord => v 0)
    exact contDiff_apply ℝ ℝ (0 : Fin 2)

private theorem ordinaryActualMargins_axis_domain
    {L : ℝ} (hL : 0 < L) {Omega : Set (ℝ × ℝ)}
    (hOmega : IsOpen Omega) (haxis : ∀ s, (0, s) ∈ Omega)
    (hperiod : ∀ rho, Periodic (fun s => (rho, s) ∈ Omega) L) :
    ∃ rhoMax > 0, ∀ rho s, |rho| < rhoMax → (rho, s) ∈ Omega := by
  have hnear : ∀ᶠ rho in 𝓝 (0 : ℝ), ∀ s ∈ Icc (0 : ℝ) L, (rho, s) ∈ Omega := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro s hs
    exact hOmega.mem_nhds (haxis s)
  obtain ⟨rhoMax, hrhoMax, hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨rhoMax, hrhoMax, ?_⟩
  intro rho s hrho
  obtain ⟨n, hn, _⟩ := existsUnique_sub_zsmul_mem_Ico hL s 0
  simp only [mem_Ico, zero_add] at hn
  have hIn : rho ∈ ball (0 : ℝ) rhoMax := by
    simpa only [mem_ball, Real.dist_eq, sub_zero] using hrho
  have he := hball hIn (s - n • L) ⟨hn.1, hn.2.le⟩
  have hp := (hperiod rho).sub_zsmul_eq n (x := s)
  change ((rho, s - n • L) ∈ Omega) = ((rho, s) ∈ Omega) at hp
  rw [hp] at he
  exact he

/-- The actual endpoint gradient is G+J W whenever its literal A/B/C
coefficients are positive. No circular direction or gradient jet is assumed. -/
theorem visibleConnectorOrdinaryFamilyTerminalActualMargins_endpoint_gradient
    {p gamma w : ℝ → Coord} (s : ℝ)
    (hA : 0 < visibleConnectorA p w s)
    (hB : 0 < visibleConnectorB gamma w s)
    (hC : 0 < visibleConnectorC gamma w s) :
    visibleConnectorGradient p gamma w
      ![s, visibleConnectorActualTerminalHeight p gamma w s] =
      gamma s + visibleConnectorJ (w s) := by
  have hDelta : visibleConnectorDelta p gamma w
      ![s, visibleConnectorActualTerminalHeight p gamma w s] =
      visibleConnectorA p w s * visibleConnectorB gamma w s / visibleConnectorC gamma w s := by
    simp only [visibleConnectorDelta, visibleConnectorActualTerminalHeight,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp [hC.ne']
    ring
  have hquot : visibleConnectorActualTerminalHeight p gamma w s *
      visibleConnectorB gamma w s / visibleConnectorDelta p gamma w
      ![s, visibleConnectorActualTerminalHeight p gamma w s] = 1 := by
    rw [hDelta]
    unfold visibleConnectorActualTerminalHeight
    field_simp [hA.ne', hB.ne', hC.ne'] <;> ring
  unfold visibleConnectorGradient
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hquot, one_smul]

/-- One full-phase threshold for the SAME literal quotient terminal and actual
endpoint gradient. Displaced coefficient, radial, tangent and angular signs
are conclusions. Both slice smoothness and actual carrier membership remain
explicit outputs for the same selected rho. -/
theorem visibleConnectorOrdinaryFamilyTerminalActualMargins_uniform
    {P G W : ℝ × ℝ → Coord} {Omega : Set (ℝ × ℝ)} {L : ℝ}
    (hL : 0 < L) (hOmega : IsOpen Omega)
    (hP : ContDiffOn ℝ ∞ P Omega) (hG : ContDiffOn ℝ ∞ G Omega)
    (hW : ContDiffOn ℝ ∞ W Omega) (haxis : ∀ s, (0, s) ∈ Omega)
    (hOmegaPeriod : ∀ rho, Periodic (fun s => (rho, s) ∈ Omega) L)
    (hPL : ∀ rho, Periodic (fun s => P (rho, s)) L)
    (hGL : ∀ rho, Periodic (fun s => G (rho, s)) L)
    (hWL : ∀ rho, Periodic (fun s => W (rho, s)) L)
    (hA0 : ∀ s, 0 < visibleConnectorA (fun t => P (0, t)) (fun t => W (0, t)) s)
    (hB0 : ∀ s, 0 < visibleConnectorB (fun t => G (0, t)) (fun t => W (0, t)) s)
    (hC0 : ∀ s, 0 < visibleConnectorC (fun t => G (0, t)) (fun t => W (0, t)) s)
    (hRadial0 : ∀ s, 0 < visibleConnectorIncomingTerminalActualFamily P G W (0, s) ⬝ᵥ
      (G (0, s) + visibleConnectorJ (W (0, s))))
    (hTangent0 : ∀ s, 0 < deriv (fun t => visibleConnectorIncomingTerminalActualFamily P G W (0, t)) s ⬝ᵥ
      deriv (fun t => G (0, t) + visibleConnectorJ (W (0, t))) s)
    (hAngular0 : ∀ s, 0 < visibleConnectorDet (G (0, s) + visibleConnectorJ (W (0, s)))
      (deriv (fun t => G (0, t) + visibleConnectorJ (W (0, t))) s)) :
    ∃ rhoMax > 0, ∀ rho, |rho| < rhoMax →
      let T := fun s => visibleConnectorIncomingTerminalActualFamily P G W (rho, s)
      let Y := fun s => G (rho, s) + visibleConnectorJ (W (rho, s))
      ContDiff ℝ ∞ T ∧ ContDiff ℝ ∞ Y ∧
      (∀ s, (rho, s) ∈ Omega) ∧
      (∀ s, 0 < visibleConnectorA (fun t => P (rho, t)) (fun t => W (rho, t)) s ∧
        0 < visibleConnectorB (fun t => G (rho, t)) (fun t => W (rho, t)) s ∧
        0 < visibleConnectorC (fun t => G (rho, t)) (fun t => W (rho, t)) s) ∧
      (∀ s, visibleConnectorGradient (fun t => P (rho, t)) (fun t => G (rho, t))
        (fun t => W (rho, t))
        ![s, visibleConnectorActualTerminalHeight (fun t => P (rho, t))
          (fun t => G (rho, t)) (fun t => W (rho, t)) s] = Y s) ∧
      (∀ s, 0 < T s ⬝ᵥ Y s ∧ 0 < deriv T s ⬝ᵥ deriv Y s ∧
        0 < visibleConnectorDet (Y s) (deriv Y s)) := by
  let A : ℝ × ℝ → ℝ := fun z => visibleConnectorA (fun s => P (z.1, s)) (fun s => W (z.1, s)) z.2
  let B : ℝ × ℝ → ℝ := fun z => visibleConnectorB (fun s => G (z.1, s)) (fun s => W (z.1, s)) z.2
  let C : ℝ × ℝ → ℝ := fun z => visibleConnectorC (fun s => G (z.1, s)) (fun s => W (z.1, s)) z.2
  let O : Set (ℝ × ℝ) := (Omega ∩ A ⁻¹' Ioi 0) ∩ (Omega ∩ B ⁻¹' Ioi 0) ∩ (Omega ∩ C ⁻¹' Ioi 0)
  obtain ⟨hAc, hBc, hCc⟩ := visibleConnectorIncomingParametersFamily_actual_coefficients_continuousOn hOmega hP hG hW
  have hO : IsOpen O := ((hAc.isOpen_inter_preimage hOmega isOpen_Ioi).inter
    (hBc.isOpen_inter_preimage hOmega isOpen_Ioi)).inter (hCc.isOpen_inter_preimage hOmega isOpen_Ioi)
  have hOaxis (s : ℝ) : (0, s) ∈ O :=
    ⟨⟨⟨haxis s, hA0 s⟩, ⟨haxis s, hB0 s⟩⟩, ⟨haxis s, hC0 s⟩⟩
  have hOsub : O ⊆ Omega := fun _ hz => hz.1.1.1
  obtain ⟨hAL, hBL, hCL⟩ := visibleConnectorIncomingParametersFamily_actual_coefficients_periodic hPL hGL hWL
  have hOPeriod (rho : ℝ) : Periodic (fun s => (rho, s) ∈ O) L := by
    intro s
    change ((((rho, s + L) ∈ Omega ∧ 0 < A (rho, s + L)) ∧
      ((rho, s + L) ∈ Omega ∧ 0 < B (rho, s + L))) ∧
      ((rho, s + L) ∈ Omega ∧ 0 < C (rho, s + L))) = _
    have hOs : ((rho, s + L) ∈ Omega) = ((rho, s) ∈ Omega) := hOmegaPeriod rho s
    have hAs : A (rho, s + L) = A (rho, s) := hAL rho s
    have hBs : B (rho, s + L) = B (rho, s) := hBL rho s
    have hCs : C (rho, s + L) = C (rho, s) := hCL rho s
    change ((((rho, s + L) ∈ Omega ∧ 0 < A (rho, s + L)) ∧
      ((rho, s + L) ∈ Omega ∧ 0 < B (rho, s + L))) ∧
      ((rho, s + L) ∈ Omega ∧ 0 < C (rho, s + L))) =
      ((((rho, s) ∈ Omega ∧ 0 < A (rho, s)) ∧
      ((rho, s) ∈ Omega ∧ 0 < B (rho, s))) ∧
      ((rho, s) ∈ Omega ∧ 0 < C (rho, s)))
    rw [hOs, hAs, hBs, hCs]
  have hT : ContDiffOn ℝ ∞ (visibleConnectorIncomingTerminalActualFamily P G W) O :=
    visibleConnectorIncomingTerminal_actualFamily_contDiffOn hO (hP.mono hOsub)
      (hG.mono hOsub) (hW.mono hOsub) (fun _ hz => ne_of_gt hz.2.2)
  let Y : ℝ × ℝ → Coord := fun z => G z + visibleConnectorJ (W z)
  have hY : ContDiffOn ℝ ∞ Y O := (hG.mono hOsub).add
    (ordinaryActualMargins_J_smooth.comp_contDiffOn (hW.mono hOsub))
  have hYL (rho : ℝ) : Periodic (fun s => Y (rho, s)) L := by
    intro s
    dsimp [Y]
    have hGs : G (rho, s + L) = G (rho, s) := hGL rho s
    have hWs : W (rho, s + L) = W (rho, s) := hWL rho s
    rw [hGs, hWs]
  have hTL (rho : ℝ) : Periodic (fun s => visibleConnectorIncomingTerminalActualFamily P G W (rho, s)) L := by
    intro s
    change P (rho, s + L) +
      (visibleConnectorA (fun t => P (rho, t)) (fun t => W (rho, t)) (s + L) /
        visibleConnectorC (fun t => G (rho, t)) (fun t => W (rho, t)) (s + L)) • W (rho, s + L) = _
    have hPs : P (rho, s + L) = P (rho, s) := hPL rho s
    have hWs : W (rho, s + L) = W (rho, s) := hWL rho s
    have hAs : A (rho, s + L) = A (rho, s) := hAL rho s
    have hCs : C (rho, s + L) = C (rho, s) := hCL rho s
    change P (rho, s + L) + (A (rho, s + L) / C (rho, s + L)) • W (rho, s + L) =
      P (rho, s) + (A (rho, s) / C (rho, s)) • W (rho, s)
    rw [hPs, hAs, hCs, hWs]
  obtain ⟨rd, hrd, hdomain⟩ := ordinaryActualMargins_axis_domain hL hO hOaxis hOPeriod
  obtain ⟨rm, hrm, hmargins⟩ := visibleConnectorOrdinaryFamilyTerminalMargins_uniform
    hL hO hOaxis hT hY hTL hYL hRadial0 hTangent0 hAngular0
  refine ⟨min rd rm, lt_min hrd hrm, ?_⟩
  intro rho hrho
  dsimp only
  have hfull (s : ℝ) := hdomain rho s (hrho.trans_le (min_le_left rd rm))
  have hsT : ContDiff ℝ ∞ (fun s => visibleConnectorIncomingTerminalActualFamily P G W (rho, s)) :=
    contDiffOn_univ.mp (hT.comp ((contDiff_const (c := rho)).prodMk contDiff_id).contDiffOn
      (fun s _ => hfull s))
  have hsY : ContDiff ℝ ∞ (fun s => Y (rho, s)) :=
    contDiffOn_univ.mp (hY.comp ((contDiff_const (c := rho)).prodMk contDiff_id).contDiffOn
      (fun s _ => hfull s))
  refine ⟨hsT, hsY, fun s => hOsub (hfull s), ?_, ?_, ?_⟩
  · intro s
    exact ⟨(hfull s).1.1.2, (hfull s).1.2.2, (hfull s).2.2⟩
  · intro s
    exact visibleConnectorOrdinaryFamilyTerminalActualMargins_endpoint_gradient s
      (hfull s).1.1.2 (hfull s).1.2.2 (hfull s).2.2
  · exact hmargins rho (hrho.trans_le (min_le_right rd rm))

end
end TightVer401


