import TightVer401.VisibleConnectorIncomingTerminalMargins
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! Stability of the actual SAME terminal under a periodic C1 family. Values
and phase derivatives are jointly continuous at rho=0; actual rho-periodicity
and smoothness for |rho| below rhoSmooth are retained. The small rho turn, injectivity and positive
completion filling are conclusions, not supplied construction data. -/
namespace TightVer401
noncomputable section
open Set Function Filter Metric OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private theorem incomingTerminalLocalStability_complex_eq :
    positiveExitComplexPoint = seamComplexCoord.symm := by
  funext q
  apply seamComplexCoord.injective
  rw [ContinuousLinearEquiv.apply_symm_apply, seamComplexCoord_apply]
  ext i
  fin_cases i <;> rfl

private theorem incomingTerminalLocalStability_deriv_periodic {T : ℝ → Coord} {L : ℝ}
    (hp : Periodic T L) : Periodic (deriv T) L := by
  intro s
  have he : (fun t => T (t + L)) = T := funext hp
  rw [← deriv_comp_add_const T L s, he]
/-- Compact local C1 margins transport to EVERY phase of the actual periodic
family. This supplies the full terminal, not a compact representative slice. -/
theorem visibleConnectorIncomingTerminal_exists_local_periodic_displacement_threshold
    {F : ℝ × ℝ → Coord} {L M : ℝ} (hL : 0 < L)
    (hFp : ∀ rho, Periodic (fun s => F (rho, s)) L)
    (hF : ∀ s ∈ Icc (0 : ℝ) L, ContinuousAt F (0, s))
    (hFd : ∀ s ∈ Icc (0 : ℝ) L, ContinuousAt
      (fun q : ℝ × ℝ => deriv (fun t => F (q.1, t)) q.2) (0, s))
    (hnorm : ∀ s ∈ Icc (0 : ℝ) L,
      M < ‖positiveExitComplexPoint (F (0, s))‖)
    (hdet : ∀ s ∈ Icc (0 : ℝ) L, 0 < visibleConnectorDet (F (0, s))
      (deriv (fun t => F (0, t)) s)) :
    ∃ rhoMax > 0, ∀ rho, |rho| < rhoMax → ∀ s,
      M < ‖positiveExitComplexPoint (F (rho, s))‖ ∧
      0 < visibleConnectorDet (F (rho, s))
        (deriv (fun t => F (rho, t)) s) := by
  obtain ⟨rhoMax, hrhoMax, hm⟩ :=
    visibleConnectorIncomingTerminal_exists_displacement_threshold
      isCompact_Icc hF hFd hnorm hdet
  refine ⟨rhoMax, hrhoMax, ?_⟩
  intro rho hrho s
  obtain ⟨n, hn, _⟩ := existsUnique_sub_zsmul_mem_Ico hL s 0
  simp only [mem_Ico, zero_add] at hn
  have he := hm rho hrho (s - n • L) ⟨hn.1, hn.2.le⟩
  have hdp := incomingTerminalLocalStability_deriv_periodic (hFp rho)
  rw [(hFp rho).sub_zsmul_eq n, hdp.sub_zsmul_eq n] at he
  exact he

/-- A SAME baseline terminal with positive turn, together with joint C1
continuity of the actual periodic displaced family, constructs a positive
filling of every sufficiently small displaced terminal. No displaced Jordan
curve, filling, origin inclusion or desired positive trace is an input. -/
theorem visibleConnectorIncomingTerminal_exists_local_displaced_positive_filling
    {F : ℝ × ℝ → Coord} {L M : ℝ} (hL : 0 < L)
    {rhoSmooth : ℝ} (hrhoSmooth : 0 < rhoSmooth)
    (hFs : ∀ rho, |rho| < rhoSmooth → ContDiff ℝ ∞ (fun s => F (rho, s)))
    (hFp : ∀ rho, Periodic (fun s => F (rho, s)) L)
    (hF : ∀ s ∈ Icc (0 : ℝ) L, ContinuousAt F (0, s))
    (hFd : ∀ s ∈ Icc (0 : ℝ) L, ContinuousAt
      (fun q : ℝ × ℝ => deriv (fun t => F (q.1, t)) q.2) (0, s))
    (hnorm : ∀ s ∈ Icc (0 : ℝ) L,
      M < ‖positiveExitComplexPoint (F (0, s))‖)
    (hdet : ∀ s ∈ Icc (0 : ℝ) L, 0 < visibleConnectorDet (F (0, s))
      (deriv (fun t => F (0, t)) s))
    (hne : ∀ s, positiveExitComplexTrace (fun t => F (0, t)) s ≠ 0)
    (hturn : HasPositiveArgumentTurn (positiveExitComplexTrace (fun t => F (0, t))) L) :
    ∃ rhoMax > 0, ∀ rho, |rho| < rhoMax →
      let T := fun s => F (rho, s)
      (∀ s, M < ‖positiveExitComplexTrace T s‖) ∧
      (∀ s, 0 < visibleConnectorDet (T s) (deriv T s)) ∧
      InjOn T (Ico (0 : ℝ) L) ∧
      ∃ H : ℂ ≃ₜ ℂ,
        DualRadialCompletionPositiveTrace H (visibleConnectorTerminalNormalizedTrace L T) ∧
        (0 : ℂ) ∈ jordanInterior H ∧
        range (positiveExitComplexTrace T) = frontier (jordanInterior H) := by
  let B : ℝ → ℂ := positiveExitComplexTrace (fun t => F (0, t))
  have hBs : ContDiff ℝ ∞ B := by
    change ContDiff ℝ ∞ (positiveExitComplexPoint ∘ (fun t => F (0, t)))
    rw [incomingTerminalLocalStability_complex_eq]
    exact seamComplexCoord.symm.contDiff.comp (hFs 0 (by simpa only [abs_zero] using hrhoSmooth))
  have hBp : Periodic B L := by
    intro s
    dsimp [B, positiveExitComplexTrace]
    exact congrArg positiveExitComplexPoint (hFp 0 s)
  obtain ⟨epsilon, hepsilon, hturnStable⟩ :=
    positiveExit_exists_argumentTurn_C0_threshold hL hBs hBp hne hturn
  have hcloseEvent : ∀ᶠ rho in 𝓝 (0 : ℝ), ∀ s ∈ Icc (0 : ℝ) L,
      ‖positiveExitComplexPoint (F (rho, s)) - B s‖ < epsilon := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro s hs
    have hc : ContinuousAt (fun q : ℝ × ℝ =>
        positiveExitComplexPoint (F q) - B q.2) (0, s) := by
      rw [incomingTerminalLocalStability_complex_eq]
      exact (seamComplexCoord.symm.continuous.continuousAt.comp (hF s hs)).sub
        (hBs.continuous.comp continuous_snd).continuousAt
    have hzero : ‖positiveExitComplexPoint (F (0, s)) - B s‖ < epsilon := by
      simpa only [B, positiveExitComplexTrace, Function.comp_apply, sub_self, norm_zero]
        using hepsilon
    exact hc.norm.eventually (gt_mem_nhds hzero)
  obtain ⟨rhoClose, hrhoClose, hcloseBall⟩ := Metric.mem_nhds_iff.mp hcloseEvent
  obtain ⟨rhoGeom, hrhoGeom, hgeom⟩ :=
    visibleConnectorIncomingTerminal_exists_local_periodic_displacement_threshold
      hL hFp hF hFd hnorm hdet
  refine ⟨min rhoSmooth (min rhoClose rhoGeom),
    lt_min hrhoSmooth (lt_min hrhoClose hrhoGeom), ?_⟩
  intro rho hrho
  dsimp only
  let T : ℝ → Coord := fun s => F (rho, s)
  have hTs : ContDiff ℝ ∞ T := hFs rho (hrho.trans_le (min_le_left _ _))
  have hTp : Periodic T L := hFp rho
  have hTc : ContDiff ℝ ∞ (positiveExitComplexTrace T) := by
    change ContDiff ℝ ∞ (positiveExitComplexPoint ∘ T)
    rw [incomingTerminalLocalStability_complex_eq]
    exact seamComplexCoord.symm.contDiff.comp hTs
  have hTcp : Periodic (positiveExitComplexTrace T) L := by
    intro s
    dsimp [positiveExitComplexTrace]
    exact congrArg positiveExitComplexPoint (hTp s)
  have hclose : ∀ s ∈ Icc (0 : ℝ) L,
      ‖positiveExitComplexTrace T s - B s‖ < epsilon := by
    intro s hs
    apply hcloseBall _ s hs
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using
      hrho.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  obtain ⟨hTturn, hTne⟩ := hturnStable (positiveExitComplexTrace T) hTc hTcp hclose
  have hm (s : ℝ) := hgeom rho (hrho.trans_le ((min_le_right _ _).trans (min_le_right _ _))) s
  have hTdet (s : ℝ) : 0 < visibleConnectorDet (T s) (deriv T s) := (hm s).2
  obtain ⟨hi, _⟩ := visibleConnector_positive_det_turn_jordan hL hTs hTp hTne hTturn hTdet
  obtain ⟨H, hpositive, h0, hfront, _⟩ :=
    visibleConnectorTerminal_exists_positive_completion_trace hL hTs hTp hTne hTdet hTturn hi
  exact ⟨fun s => (hm s).1, hTdet, hi, H, hpositive, h0, hfront⟩

end
end TightVer401



