import TightVer401.VisibleConnectorOrdinaryFamilyCoefficientContinuity
import TightVer401.VisibleConnectorIncomingTerminalMargins

/-! ONE displacement threshold preserves the actual radial, tangent and
angular terminal inequalities. Only the undisplaced strict inequalities and
joint smoothness are inputs; no displaced inequality is granted. -/
namespace TightVer401
noncomputable section
open Set Function Filter Metric OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix

private theorem ordinaryTerminalMargins_deriv_periodic {f : ℝ → Coord} {L : ℝ}
    (hL : Periodic f L) : Periodic (deriv f) L := by
  intro s
  have he : (fun t => f (t + L)) = f := funext hL
  have hd := congrArg (fun F : ℝ → Coord => deriv F s) he
  simpa only [deriv_comp_add_const] using hd

private theorem ordinaryTerminalMargins_dot_continuousOn
    {F G : ℝ × ℝ → Coord} {Omega : Set (ℝ × ℝ)}
    (hF : ContinuousOn F Omega) (hG : ContinuousOn G Omega) :
    ContinuousOn (fun z => F z ⬝ᵥ G z) Omega := by
  have hF0 := (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)).continuous.comp_continuousOn hF
  have hF1 := (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2)).continuous.comp_continuousOn hF
  have hG0 := (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)).continuous.comp_continuousOn hG
  have hG1 := (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2)).continuous.comp_continuousOn hG
  change ContinuousOn (fun z => F z 0) Omega at hF0
  change ContinuousOn (fun z => F z 1) Omega at hF1
  change ContinuousOn (fun z => G z 0) Omega at hG0
  change ContinuousOn (fun z => G z 1) Omega at hG1
  apply ((hF0.mul hG0).add (hF1.mul hG1)).congr
  intro z hz
  simp [dotProduct, Fin.sum_univ_two]

/-- Uniform all-real rho margins for one SAME actual terminal T and endpoint
gradient Y. Joint smoothness may be established on the actual C-nonzero
quotient domain; this theorem does not require smoothness elsewhere. -/
theorem visibleConnectorOrdinaryFamilyTerminalMargins_uniform
    {L : ℝ} (hL : 0 < L) {T Y : ℝ × ℝ → Coord} {Omega : Set (ℝ × ℝ)}
    (hOmega : IsOpen Omega) (haxis : ∀ s, (0, s) ∈ Omega)
    (hT : ContDiffOn ℝ ∞ T Omega) (hY : ContDiffOn ℝ ∞ Y Omega)
    (hTL : ∀ rho, Periodic (fun s => T (rho, s)) L)
    (hYL : ∀ rho, Periodic (fun s => Y (rho, s)) L)
    (hRadial0 : ∀ s, 0 < T (0, s) ⬝ᵥ Y (0, s))
    (hTangent0 : ∀ s, 0 < deriv (fun t => T (0, t)) s ⬝ᵥ
      deriv (fun t => Y (0, t)) s)
    (hAngular0 : ∀ s, 0 < visibleConnectorDet (Y (0, s))
      (deriv (fun t => Y (0, t)) s)) :
    ∃ rhoMax > 0, ∀ rho, |rho| < rhoMax → ∀ s,
      0 < T (rho, s) ⬝ᵥ Y (rho, s) ∧
      0 < deriv (fun t => T (rho, t)) s ⬝ᵥ deriv (fun t => Y (rho, t)) s ∧
      0 < visibleConnectorDet (Y (rho, s)) (deriv (fun t => Y (rho, t)) s) := by
  let DT : ℝ × ℝ → Coord := fun z => deriv (fun t => T (z.1, t)) z.2
  let DY : ℝ × ℝ → Coord := fun z => deriv (fun t => Y (z.1, t)) z.2
  have hDT : ContinuousOn DT Omega :=
    visibleConnectorOrdinaryFamilyCoefficientContinuity_deriv hOmega hT
  have hDY : ContinuousOn DY Omega :=
    visibleConnectorOrdinaryFamilyCoefficientContinuity_deriv hOmega hY
  have hRadial := ordinaryTerminalMargins_dot_continuousOn hT.continuousOn hY.continuousOn
  have hTangent := ordinaryTerminalMargins_dot_continuousOn hDT hDY
  have hY0 := (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)).continuous.comp_continuousOn hY.continuousOn
  have hY1 := (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2)).continuous.comp_continuousOn hY.continuousOn
  have hDY0 := (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)).continuous.comp_continuousOn hDY
  have hDY1 := (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2)).continuous.comp_continuousOn hDY
  have hAngular : ContinuousOn (fun z => visibleConnectorDet (Y z) (DY z)) Omega :=
    (hY0.mul hDY1).sub (hY1.mul hDY0)
  have hevent : ∀ᶠ rho in 𝓝 (0 : ℝ), ∀ s ∈ Icc (0 : ℝ) L,
      0 < T (rho, s) ⬝ᵥ Y (rho, s) ∧
      0 < DT (rho, s) ⬝ᵥ DY (rho, s) ∧
      0 < visibleConnectorDet (Y (rho, s)) (DY (rho, s)) := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro s hs
    have hr := (hRadial _ (haxis s)).continuousAt (hOmega.mem_nhds (haxis s))
    have ht := (hTangent _ (haxis s)).continuousAt (hOmega.mem_nhds (haxis s))
    have ha := (hAngular _ (haxis s)).continuousAt (hOmega.mem_nhds (haxis s))
    exact (hr.eventually (lt_mem_nhds (hRadial0 s))).and
      ((ht.eventually (lt_mem_nhds (hTangent0 s))).and
        (ha.eventually (lt_mem_nhds (hAngular0 s))))
  obtain ⟨rhoMax, hrhoMax, hball⟩ := Metric.mem_nhds_iff.mp hevent
  refine ⟨rhoMax, hrhoMax, ?_⟩
  intro rho hrho s
  have hIn : rho ∈ ball (0 : ℝ) rhoMax := by
    simpa only [mem_ball, Real.dist_eq, sub_zero] using hrho
  obtain ⟨n, hn, _⟩ := existsUnique_sub_zsmul_mem_Ico hL s 0
  simp only [mem_Ico, zero_add] at hn
  have h := hball hIn (s - n • L) ⟨hn.1, hn.2.le⟩
  have hTd := ordinaryTerminalMargins_deriv_periodic (hTL rho)
  have hYd := ordinaryTerminalMargins_deriv_periodic (hYL rho)
  dsimp only [DT, DY] at h
  rw [(hTL rho).sub_zsmul_eq n, (hYL rho).sub_zsmul_eq n,
    hTd.sub_zsmul_eq n, hYd.sub_zsmul_eq n] at h
  exact h

end
end TightVer401
