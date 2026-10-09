import TightVer401.VisibleConnectorIncomingTerminalQuotient
import TightVer401.VisibleConnectorDisplacedSeamGinFamily

/-! Actual terminal radial positivity retains SAME fixed eta and SAME P/G/W.
A uniform rho bound is produced by compact strict positivity. The bound is
intersected before selection; this leaf does not select a second rho. -/
namespace TightVer401
noncomputable section
open Set Function Filter Metric OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private theorem incomingTerminalRadial_J_continuous : Continuous visibleConnectorJ := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact (continuous_apply (1 : Fin 2)).neg
  · exact continuous_apply (0 : Fin 2)

private theorem incomingTerminalRadial_coordinate_continuous
    {F : ℝ × ℝ → Coord} {Omega : Set (ℝ × ℝ)}
    (hF : ContinuousOn F Omega) (i : Fin 2) :
    ContinuousOn (fun z => F z i) Omega :=
  (continuous_apply i).continuousOn.comp hF (fun _ _ => mem_univ _)

private theorem incomingTerminalRadial_dot_continuous
    {F H : ℝ × ℝ → Coord} {Omega : Set (ℝ × ℝ)}
    (hF : ContinuousOn F Omega) (hH : ContinuousOn H Omega) :
    ContinuousOn (fun z => F z ⬝ᵥ H z) Omega := by
  have he : (fun z => F z ⬝ᵥ H z) =
      (fun z => F z 0 * H z 0 + F z 1 * H z 1) := by
    funext z
    simp [dotProduct, Fin.sum_univ_two]
  rw [he]
  exact ((incomingTerminalRadial_coordinate_continuous hF 0).mul
    (incomingTerminalRadial_coordinate_continuous hH 0)).add
      ((incomingTerminalRadial_coordinate_continuous hF 1).mul
        (incomingTerminalRadial_coordinate_continuous hH 1))

/-- The literal ruling identity turns the retained radial covector into R
 times the actual rotated terminal normal direction. -/
theorem visibleConnectorIncomingTerminal_radial_ruling_identity
    (R : ℝ) (gamma direction T : Coord) :
    T ⬝ᵥ (-visibleConnectorJ (visibleConnectorJ gamma -
      (visibleConnectorJ gamma - R • direction))) =
    R * (T ⬝ᵥ (-visibleConnectorJ direction)) := by
  simp only [visibleConnectorJ, dotProduct, Fin.sum_univ_two, Pi.sub_apply,
    Pi.neg_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

def visibleConnectorIncomingTerminalRadialScalar (P G W : ℝ × ℝ → Coord)
    (z : ℝ × ℝ) : ℝ :=
  visibleConnectorIncomingTerminalActualFamily P G W z ⬝ᵥ
    (-visibleConnectorJ (visibleConnectorJ (G z) - W z))

/-- Actual longitudinal derivative paired with the literal ruling normal. -/
def visibleConnectorIncomingTerminalDirectionalScalar (P G W : ℝ × ℝ → Coord)
    (z : ℝ × ℝ) : ℝ :=
  deriv (fun t => visibleConnectorIncomingTerminalActualFamily P G W (z.1, t)) z.2 ⬝ᵥ
    (visibleConnectorJ (G z) - W z)

private theorem incomingTerminalRadial_deriv_periodic {T : ℝ → Coord} {L : ℝ}
    (hp : Periodic T L) : Periodic (deriv T) L := by
  intro s
  have he : (fun t => T (t + L)) = T := funext hp
  rw [← deriv_comp_add_const T L s, he]

theorem visibleConnectorIncomingTerminal_directional_ruling_identity
    (R : ℝ) (gamma direction Td : Coord) :
    Td ⬝ᵥ (visibleConnectorJ gamma - (visibleConnectorJ gamma - R • direction)) =
      R * (Td ⬝ᵥ direction) := by
  simp only [visibleConnectorJ, dotProduct, Fin.sum_univ_two, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring
def visibleConnectorIncomingTerminalExcessScalar (R : ℝ) (G W : ℝ × ℝ → Coord)
    (z : ℝ × ℝ) : ℝ :=
  visibleConnectorJ (G z) ⬝ᵥ (visibleConnectorJ (G z) - W z) - R ^ 2

theorem visibleConnectorIncomingTerminal_excess_ruling_identity
    (R : ℝ) (gamma direction : Coord) :
    visibleConnectorJ gamma ⬝ᵥ
      (visibleConnectorJ gamma - (visibleConnectorJ gamma - R • direction)) - R ^ 2 =
      R * (visibleConnectorJ gamma ⬝ᵥ direction - R) := by
  simp only [visibleConnectorJ, dotProduct, Fin.sum_univ_two, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring
/-- Actual smooth source families and positive baseline C/radial pairing
construct a uniform full-phase radial threshold. Terminal regularity and
radial positivity after displacement are conclusions. -/
theorem visibleConnectorIncomingTerminal_uniform_radial_directional_threshold
    {P G W : ℝ × ℝ → Coord} {Omega : Set (ℝ × ℝ)} {L R : ℝ}
    (hL : 0 < L) (hOmega : IsOpen Omega)
    (hP : ContDiffOn ℝ ∞ P Omega) (hG : ContDiffOn ℝ ∞ G Omega)
    (hW : ContDiffOn ℝ ∞ W Omega) (haxis : ∀ s, (0, s) ∈ Omega)
    (hPL : ∀ rho, Periodic (fun s => P (rho, s)) L)
    (hGL : ∀ rho, Periodic (fun s => G (rho, s)) L)
    (hWL : ∀ rho, Periodic (fun s => W (rho, s)) L)
    (hC0 : ∀ s, 0 < visibleConnectorC (fun t => G (0, t)) (fun t => W (0, t)) s)
    (hrad0 : ∀ s, 0 < visibleConnectorIncomingTerminalRadialScalar P G W (0, s))
    (hdir0 : ∀ s, 0 < visibleConnectorIncomingTerminalDirectionalScalar P G W (0, s))
    (hexcess0 : ∀ s, 0 < visibleConnectorIncomingTerminalExcessScalar R G W (0, s)) :
    ∃ rhoRadial > 0, ∀ rho s, |rho| < rhoRadial →
      0 < visibleConnectorIncomingTerminalRadialScalar P G W (rho, s) ∧
      0 < visibleConnectorIncomingTerminalDirectionalScalar P G W (rho, s) ∧
      0 < visibleConnectorIncomingTerminalExcessScalar R G W (rho, s) := by
  let C : ℝ × ℝ → ℝ := fun z => visibleConnectorC
    (fun t => G (z.1, t)) (fun t => W (z.1, t)) z.2
  let OmegaT := Omega ∩ C ⁻¹' Ioi (0 : ℝ)
  obtain ⟨_, _, hCc⟩ :=
    visibleConnectorIncomingParametersFamily_actual_coefficients_continuousOn hOmega hP hG hW
  have hCcont : ContinuousOn C Omega := hCc
  have hOmegaT : IsOpen OmegaT := hCcont.isOpen_inter_preimage hOmega isOpen_Ioi
  have hAxisT (s : ℝ) : (0, s) ∈ OmegaT := ⟨haxis s, hC0 s⟩
  have hCne : ∀ z ∈ OmegaT, visibleConnectorC
      (fun t => G (z.1, t)) (fun t => W (z.1, t)) z.2 ≠ 0 := by
    intro z hz
    exact (show 0 < C z from hz.2).ne'
  have hGT := hG.mono (inter_subset_left : OmegaT ⊆ Omega)
  have hWT := hW.mono (inter_subset_left : OmegaT ⊆ Omega)
  obtain ⟨hT, hTd⟩ := visibleConnectorIncomingTerminal_actualFamily_C1 hOmegaT
    (hP.mono inter_subset_left) hGT hWT hCne
  have hE : ContinuousOn (fun z => visibleConnectorJ (G z) - W z) OmegaT :=
    (incomingTerminalRadial_J_continuous.continuousOn.comp hGT.continuousOn
      (fun _ _ => mem_univ _)).sub hWT.continuousOn
  have hDirectional : ContinuousOn (visibleConnectorIncomingTerminalDirectionalScalar P G W) OmegaT :=
    incomingTerminalRadial_dot_continuous hTd hE
  have hJG : ContinuousOn (fun z => visibleConnectorJ (G z)) OmegaT :=
    incomingTerminalRadial_J_continuous.continuousOn.comp hGT.continuousOn (fun _ _ => mem_univ _)
  have hExcess : ContinuousOn (visibleConnectorIncomingTerminalExcessScalar R G W) OmegaT :=
    (incomingTerminalRadial_dot_continuous hJG hE).sub continuousOn_const
  have hD : ContinuousOn (fun z => -visibleConnectorJ (visibleConnectorJ (G z) - W z)) OmegaT :=
    (incomingTerminalRadial_J_continuous.continuousOn.comp
      ((incomingTerminalRadial_J_continuous.continuousOn.comp hGT.continuousOn
        (fun _ _ => mem_univ _)).sub hWT.continuousOn)
      (fun _ _ => mem_univ _)).neg
  have hRadial : ContinuousOn (visibleConnectorIncomingTerminalRadialScalar P G W) OmegaT :=
    incomingTerminalRadial_dot_continuous hT hD
  obtain ⟨hAL, _, hCL⟩ :=
    visibleConnectorIncomingParametersFamily_actual_coefficients_periodic hPL hGL hWL
  have hTp (rho : ℝ) : Periodic
      (fun s => visibleConnectorIncomingTerminalActualFamily P G W (rho, s)) L := by
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
  have hFp (rho : ℝ) : Periodic
      (fun s => visibleConnectorIncomingTerminalRadialScalar P G W (rho, s)) L := by
    intro s
    dsimp only [visibleConnectorIncomingTerminalRadialScalar]
    have hTe := hTp rho s
    have hGe : G (rho, s + L) = G (rho, s) := hGL rho s
    have hWe : W (rho, s + L) = W (rho, s) := hWL rho s
    change visibleConnectorIncomingTerminalActualFamily P G W (rho, s + L) =
      visibleConnectorIncomingTerminalActualFamily P G W (rho, s) at hTe
    rw [hTe, hGe, hWe]
  have hFdp (rho : ℝ) : Periodic
      (fun s => visibleConnectorIncomingTerminalDirectionalScalar P G W (rho, s)) L := by
    intro s
    dsimp only [visibleConnectorIncomingTerminalDirectionalScalar]
    have hTdp := incomingTerminalRadial_deriv_periodic (hTp rho)
    have hTde : deriv (fun t => visibleConnectorIncomingTerminalActualFamily P G W (rho, t)) (s + L) =
        deriv (fun t => visibleConnectorIncomingTerminalActualFamily P G W (rho, t)) s := hTdp s
    have hGe : G (rho, s + L) = G (rho, s) := hGL rho s
    have hWe : W (rho, s + L) = W (rho, s) := hWL rho s
    rw [hTde, hGe, hWe]
  have hFep (rho : ℝ) : Periodic
      (fun s => visibleConnectorIncomingTerminalExcessScalar R G W (rho, s)) L := by
    intro s
    dsimp only [visibleConnectorIncomingTerminalExcessScalar]
    have hGe : G (rho, s + L) = G (rho, s) := hGL rho s
    have hWe : W (rho, s + L) = W (rho, s) := hWL rho s
    rw [hGe, hWe]
  have hnear : ∀ᶠ rho in 𝓝 (0 : ℝ), ∀ s ∈ Icc (0 : ℝ) L,
      0 < visibleConnectorIncomingTerminalRadialScalar P G W (rho, s) ∧
      0 < visibleConnectorIncomingTerminalDirectionalScalar P G W (rho, s) ∧
      0 < visibleConnectorIncomingTerminalExcessScalar R G W (rho, s) := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro s hs
    have hc := (hRadial _ (hAxisT s)).continuousAt (hOmegaT.mem_nhds (hAxisT s))
    have hcd := (hDirectional _ (hAxisT s)).continuousAt (hOmegaT.mem_nhds (hAxisT s))
    have hce := (hExcess _ (hAxisT s)).continuousAt (hOmegaT.mem_nhds (hAxisT s))
    exact (hc.eventually (lt_mem_nhds (hrad0 s))).and
      ((hcd.eventually (lt_mem_nhds (hdir0 s))).and
        (hce.eventually (lt_mem_nhds (hexcess0 s))))
  obtain ⟨rhoRadial, hrhoRadial, hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨rhoRadial, hrhoRadial, ?_⟩
  intro rho s hrho
  have hrhoBall : rho ∈ ball (0 : ℝ) rhoRadial := by
    simpa only [mem_ball, Real.dist_eq, sub_zero] using hrho
  obtain ⟨n, hn, _⟩ := existsUnique_sub_zsmul_mem_Ico hL s 0
  simp only [mem_Ico, zero_add] at hn
  have he := hball hrhoBall (s - n • L) ⟨hn.1, hn.2.le⟩
  have hp := (hFp rho).sub_zsmul_eq n (x := s)
  change visibleConnectorIncomingTerminalRadialScalar P G W (rho, s - n • L) =
    visibleConnectorIncomingTerminalRadialScalar P G W (rho, s) at hp
  have hdp := (hFdp rho).sub_zsmul_eq n (x := s)
  change visibleConnectorIncomingTerminalDirectionalScalar P G W (rho, s - n • L) =
    visibleConnectorIncomingTerminalDirectionalScalar P G W (rho, s) at hdp
  have hep := (hFep rho).sub_zsmul_eq n (x := s)
  change visibleConnectorIncomingTerminalExcessScalar R G W (rho, s - n • L) =
    visibleConnectorIncomingTerminalExcessScalar R G W (rho, s) at hep
  rw [hp, hdp, hep] at he
  exact he

/-- Literal Gin-specific radial threshold, with all joint family regularity
and baseline identifications derived from actual incoming D. -/
theorem visibleConnectorIncomingTerminal_Gin_uniform_radial_directional_threshold
    {Gin : Coord → ℝ} {Uin : Set Coord} {L R eta : ℝ} [Fact (0 < L)]
    (D : VisibleConnectorIncomingData Gin Uin L R) {w0 : ℝ → Coord}
    (hw0 : ContDiff ℝ ∞ w0) (hw0L : Periodic w0 L)
    (hw0same : ∀ s, w0 s = visibleConnectorGinRotatedRuling R eta D.incoming.gamma s)
    (hC0 : ∀ s, 0 < visibleConnectorC D.incoming.gamma w0 s)
    (hrad0 : ∀ s, 0 < visibleConnectorActualTerminalSource D.incoming.p D.incoming.gamma w0 s ⬝ᵥ
      (-visibleConnectorJ (visibleConnectorGinRotatedDirection R eta D.incoming.gamma s)))
    (hdir0 : ∀ s, 0 < deriv (visibleConnectorActualTerminalSource D.incoming.p D.incoming.gamma w0) s ⬝ᵥ
      visibleConnectorGinRotatedDirection R eta D.incoming.gamma s)
    (hexcess0 : ∀ s, 0 < visibleConnectorJ (D.incoming.gamma s) ⬝ᵥ
      visibleConnectorGinRotatedDirection R eta D.incoming.gamma s - R) :
    ∃ rhoRadial > 0, ∀ rho, |rho| < rhoRadial →
      let pc := fun t => visibleConnectorGinDisplacedPosition D.incoming.p w0 (rho, t)
      let gc := fun t => visibleConnectorGinDisplacedGradient Gin D.incoming.p w0 (rho, t)
      let wc := fun t => visibleConnectorGinDisplacedRuling Gin R eta D.incoming.p w0 (rho, t)
      ∀ s, 0 < visibleConnectorActualTerminalSource pc gc wc s ⬝ᵥ
        (-visibleConnectorJ (visibleConnectorGinRotatedDirection R eta gc s)) ∧
        0 < deriv (visibleConnectorActualTerminalSource pc gc wc) s ⬝ᵥ
          visibleConnectorGinRotatedDirection R eta gc s ∧
        0 < visibleConnectorJ (gc s) ⬝ᵥ visibleConnectorGinRotatedDirection R eta gc s - R := by
  have hgamma (s : ℝ) : D.incoming.gamma s = planarGradient Gin (D.incoming.p s) :=
    congrFun D.incoming.actual_gradient s
  have hcomplex : angularDescentComplex = positiveExitComplexPoint := by
    funext q
    apply Complex.ext <;> simp [positiveExitComplexPoint, angularDescentComplex]
  have hmargin (s : ℝ) : R < ‖Complex.I * angularDescentComplex (D.incoming.gamma s)‖ := by
    have he := (D.visibility s).1
    rw [D.actual_delta] at he
    simpa only [hcomplex] using he
  obtain ⟨hpc, _, hgc, hV, hVsub, hVaxis, hW,
    hpcL, hgcL, hWL, _, hgc0, hW0⟩ :=
    visibleConnectorGinDisplacedFamily_properties D.radius_pos D.domain_open
      D.potential_smooth D.incoming.p_smooth hw0 D.incoming.p_periodic hw0L
      (fun s => D.incoming.p_in_domain (mem_univ s)) hgamma hmargin hw0same
  let P := visibleConnectorGinDisplacedPosition D.incoming.p w0
  let G := visibleConnectorGinDisplacedGradient Gin D.incoming.p w0
  let W := visibleConnectorGinDisplacedRuling Gin R eta D.incoming.p w0
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
  have hradActual (s : ℝ) : 0 < visibleConnectorIncomingTerminalRadialScalar P G W (0, s) := by
    dsimp only [visibleConnectorIncomingTerminalRadialScalar]
    rw [congrFun hTzero s, congrFun hgzero s, congrFun hwzero s, hw0same s]
    change 0 < visibleConnectorActualTerminalSource D.incoming.p D.incoming.gamma w0 s ⬝ᵥ
      (-visibleConnectorJ (visibleConnectorJ (D.incoming.gamma s) -
        (visibleConnectorJ (D.incoming.gamma s) - R •
          visibleConnectorGinRotatedDirection R eta D.incoming.gamma s)))
    rw [visibleConnectorIncomingTerminal_radial_ruling_identity]
    exact mul_pos D.radius_pos (hrad0 s)
  have hdirActual (s : ℝ) : 0 < visibleConnectorIncomingTerminalDirectionalScalar P G W (0, s) := by
    dsimp only [visibleConnectorIncomingTerminalDirectionalScalar]
    rw [hTzero, congrFun hgzero s, congrFun hwzero s, hw0same s]
    change 0 < deriv (visibleConnectorActualTerminalSource D.incoming.p D.incoming.gamma w0) s ⬝ᵥ
      (visibleConnectorJ (D.incoming.gamma s) -
        (visibleConnectorJ (D.incoming.gamma s) - R •
          visibleConnectorGinRotatedDirection R eta D.incoming.gamma s))
    rw [visibleConnectorIncomingTerminal_directional_ruling_identity]
    exact mul_pos D.radius_pos (hdir0 s)
  have hexcessActual (s : ℝ) : 0 < visibleConnectorIncomingTerminalExcessScalar R G W (0, s) := by
    dsimp only [visibleConnectorIncomingTerminalExcessScalar]
    rw [congrFun hgzero s, congrFun hwzero s, hw0same s]
    change 0 < visibleConnectorJ (D.incoming.gamma s) ⬝ᵥ
      (visibleConnectorJ (D.incoming.gamma s) -
        (visibleConnectorJ (D.incoming.gamma s) - R •
          visibleConnectorGinRotatedDirection R eta D.incoming.gamma s)) - R ^ 2
    rw [visibleConnectorIncomingTerminal_excess_ruling_identity]
    exact mul_pos D.radius_pos (hexcess0 s)
  obtain ⟨rhoRadial, hrhoRadial, hradial⟩ :=
    visibleConnectorIncomingTerminal_uniform_radial_directional_threshold D.incoming.period_pos hV
      hpc.contDiffOn (hgc.mono hVsub) hW hVaxis hpcL hgcL hWL hCzero hradActual hdirActual hexcessActual
  refine ⟨rhoRadial, hrhoRadial, ?_⟩
  intro rho hrho
  dsimp only
  intro s
  obtain ⟨he, hd, hx⟩ := hradial rho s hrho
  dsimp only [visibleConnectorIncomingTerminalRadialScalar] at he
  dsimp only [visibleConnectorIncomingTerminalDirectionalScalar] at hd
  change 0 < visibleConnectorActualTerminalSource
      (fun t => P (rho, t)) (fun t => G (rho, t)) (fun t => W (rho, t)) s ⬝ᵥ
    (-visibleConnectorJ (visibleConnectorJ (G (rho, s)) - W (rho, s))) at he
  have hWe : W (rho, s) = visibleConnectorJ (G (rho, s)) -
      R • visibleConnectorGinRotatedDirection R eta (fun t => G (rho, t)) s := rfl
  rw [hWe, visibleConnectorIncomingTerminal_radial_ruling_identity] at he
  change 0 < deriv (visibleConnectorActualTerminalSource
      (fun t => P (rho, t)) (fun t => G (rho, t)) (fun t => W (rho, t))) s ⬝ᵥ
    (visibleConnectorJ (G (rho, s)) - W (rho, s)) at hd
  rw [hWe, visibleConnectorIncomingTerminal_directional_ruling_identity] at hd
  change 0 < visibleConnectorJ (G (rho, s)) ⬝ᵥ
    (visibleConnectorJ (G (rho, s)) - W (rho, s)) - R ^ 2 at hx
  rw [hWe, visibleConnectorIncomingTerminal_excess_ruling_identity] at hx
  exact ⟨(mul_pos_iff_of_pos_left D.radius_pos).mp he,
    (mul_pos_iff_of_pos_left D.radius_pos).mp hd,
    (mul_pos_iff_of_pos_left D.radius_pos).mp hx⟩
end
end TightVer401


