import TightVer401.VisibleConnectorIncomingGinFamilyStabilityCalculus

/-! Compact strict margins for actual fixed-rho coefficients.  The whole
circle is first placed in the actual joint open domain; only then are its
fixed-rho smooth curves and terminal ratio used.  One uniform negative-height
extension is retained for the SAME inverse lower graph and rebase. -/
namespace TightVer401
noncomputable section
open Set Function Filter Metric OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private theorem incomingFamily_coefficients_periodic {p gamma w : ℝ → Coord} {L : ℝ}
    (hp : Periodic p L) (hg : Periodic gamma L) (hw : Periodic w L) :
    Periodic (visibleConnectorA p w) L ∧ Periodic (visibleConnectorB gamma w) L ∧
      Periodic (visibleConnectorC gamma w) L := by
  have hdp := visibleConnectorIncomingGinFamily_deriv_periodic hp
  have hdg := visibleConnectorIncomingGinFamily_deriv_periodic hg
  have hdw := visibleConnectorIncomingGinFamily_deriv_periodic hw
  have hA : Periodic (visibleConnectorA p w) L := by
    intro s
    unfold visibleConnectorA
    rw [hdp s, hw s]
  have hB : Periodic (visibleConnectorB gamma w) L := by
    intro s
    unfold visibleConnectorB
    rw [hdg s, hw s]
  refine ⟨hA, hB, ?_⟩
  intro s
  unfold visibleConnectorC
  rw [hB s, hdw s, hw s]

private theorem incomingFamily_closed_segment_positive {p gamma w : ℝ → Coord} {s : ℝ}
    (hA : 0 < visibleConnectorA p w s) (hB : 0 < visibleConnectorB gamma w s)
    (hC : 0 < visibleConnectorC gamma w s) :
    0 < visibleConnectorActualTerminalHeight p gamma w s ∧
      ∀ u ∈ Icc (0 : ℝ) (visibleConnectorActualTerminalHeight p gamma w s),
        0 < visibleConnectorDelta p gamma w ![s, u] := by
  refine ⟨div_pos hA hC, ?_⟩
  intro u hu
  have huc : u * visibleConnectorC gamma w s ≤ visibleConnectorA p w s :=
    (le_div_iff₀ hC).mp hu.2
  change 0 < visibleConnectorA p w s + u *
    (visibleConnectorB gamma w s - visibleConnectorC gamma w s)
  by_cases hzero : u = 0
  · simpa only [hzero, zero_mul, add_zero] using hA
  · have hupos : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hzero)
    have hprod : 0 < u * visibleConnectorB gamma w s := mul_pos hupos hB
    nlinarith

private theorem incomingFamily_compact_box {L : ℝ}
    {P G W : ℝ × ℝ → Coord} {Omega : Set (ℝ × ℝ)}
    (hOmega : IsOpen Omega) (hP : ContDiffOn ℝ ∞ P Omega)
    (hG : ContDiffOn ℝ ∞ G Omega) (hW : ContDiffOn ℝ ∞ W Omega)
    (haxis : ∀ s, (0, s) ∈ Omega)
    (hcentral : ∀ s,
      0 < visibleConnectorA (fun x => P (0, x)) (fun x => W (0, x)) s ∧
      0 < visibleConnectorB (fun x => G (0, x)) (fun x => W (0, x)) s ∧
      0 < visibleConnectorC (fun x => G (0, x)) (fun x => W (0, x)) s) :
    ∃ r > 0, ∀ rho s u, s ∈ Icc (0 : ℝ) L → |rho| < r → |u| < r →
      (rho, s) ∈ Omega ∧
      0 < visibleConnectorA (fun x => P (rho, x)) (fun x => W (rho, x)) s ∧
      0 < visibleConnectorB (fun x => G (rho, x)) (fun x => W (rho, x)) s ∧
      0 < visibleConnectorC (fun x => G (rho, x)) (fun x => W (rho, x)) s ∧
      0 < visibleConnectorDelta (fun x => P (rho, x)) (fun x => G (rho, x))
        (fun x => W (rho, x)) ![s, u] := by
  let A := visibleConnectorIncomingGinFamilyA P W
  let B := visibleConnectorIncomingGinFamilyB G W
  let C := visibleConnectorIncomingGinFamilyC G W
  let D : Set ((ℝ × ℝ) × ℝ) := {z | z.1 ∈ Omega}
  let J : (ℝ × ℝ) × ℝ → ℝ := fun z => A z.1 + z.2 * (B z.1 - C z.1)
  let m : (ℝ × ℝ) × ℝ → ℝ := fun z => min (A z.1) (min (B z.1) (min (C z.1) (J z)))
  obtain ⟨hA, hB, hC⟩ := visibleConnectorIncomingGinFamily_coefficients_continuousOn hOmega hP hG hW
  have hA3 : ContinuousOn (fun z : (ℝ × ℝ) × ℝ => A z.1) D :=
    hA.comp continuous_fst.continuousOn (fun _ hz => hz)
  have hB3 : ContinuousOn (fun z : (ℝ × ℝ) × ℝ => B z.1) D :=
    hB.comp continuous_fst.continuousOn (fun _ hz => hz)
  have hC3 : ContinuousOn (fun z : (ℝ × ℝ) × ℝ => C z.1) D :=
    hC.comp continuous_fst.continuousOn (fun _ hz => hz)
  have hJ : ContinuousOn J D := hA3.add (continuous_snd.continuousOn.mul (hB3.sub hC3))
  have hm : ContinuousOn m D := hA3.min (hB3.min (hC3.min hJ))
  let Z := D ∩ m ⁻¹' Ioi 0
  have hD : IsOpen D := hOmega.preimage continuous_fst
  have hZ : IsOpen Z := hm.isOpen_inter_preimage hD isOpen_Ioi
  let K : Set ((ℝ × ℝ) × ℝ) := (fun s : ℝ => ((0, s), 0)) '' Icc 0 L
  have hK : IsCompact K := isCompact_Icc.image
    ((continuous_const.prodMk continuous_id).prodMk continuous_const)
  have hKZ : K ⊆ Z := by
    rintro z ⟨s, hs, rfl⟩
    obtain ⟨hca, hcb, hcc⟩ := hcentral s
    obtain ⟨ha, hb, hc⟩ := visibleConnectorIncomingGinFamily_coefficients_actual hOmega hP hG hW (haxis s)
    have hAp : 0 < A (0, s) := ha.symm ▸ hca
    have hBp : 0 < B (0, s) := hb.symm ▸ hcb
    have hCp : 0 < C (0, s) := hc.symm ▸ hcc
    refine ⟨haxis s, ?_⟩
    change 0 < min (A (0, s)) (min (B (0, s)) (min (C (0, s)) (A (0, s) + 0 * _)))
    simpa only [zero_mul, add_zero] using lt_min hAp (lt_min hBp (lt_min hCp hAp))
  obtain ⟨r, hr, hrZ⟩ := hK.exists_cthickening_subset_open hZ hKZ
  refine ⟨r, hr, ?_⟩
  intro rho s u hs hρ hu
  have hz : ((rho, s), u) ∈ Z := by
    apply hrZ
    apply Metric.thickening_subset_cthickening r K
    apply Metric.mem_thickening_iff.mpr
    refine ⟨((0, s), 0), ⟨s, hs, rfl⟩, ?_⟩
    simpa only [Prod.dist_eq, Real.dist_eq, sub_zero, sub_self, abs_zero,
      max_eq_left (abs_nonneg rho)] using max_lt hρ hu
  have hzOmega : (rho, s) ∈ Omega := hz.1
  obtain ⟨ha, hrest⟩ := lt_min_iff.mp hz.2
  obtain ⟨hb, hrest⟩ := lt_min_iff.mp hrest
  obtain ⟨hc, hj⟩ := lt_min_iff.mp hrest
  obtain ⟨haEq, hbEq, hcEq⟩ := visibleConnectorIncomingGinFamily_coefficients_actual hOmega hP hG hW hzOmega
  change 0 < A (rho, s) + u * (B (rho, s) - C (rho, s)) at hj
  rw [haEq] at ha
  rw [hbEq] at hb
  rw [hcEq] at hc
  rw [haEq, hbEq, hcEq] at hj
  exact ⟨hzOmega, ha, hb, hc, hj⟩

/-- ONE actual rho margin preserves all fixed-rho coefficients and provides
one uniform negative-height extension through the entire terminal segment. -/
theorem visibleConnectorIncomingGinFamily_exists_coefficient_stability
    {L : ℝ} (hL : 0 < L) {P G W : ℝ × ℝ → Coord} {Omega : Set (ℝ × ℝ)}
    (hOmega : IsOpen Omega) (hP : ContDiffOn ℝ ∞ P Omega)
    (hG : ContDiffOn ℝ ∞ G Omega) (hW : ContDiffOn ℝ ∞ W Omega)
    (haxis : ∀ s, (0, s) ∈ Omega)
    (hOmegaL : ∀ rho s, (rho, s + L) ∈ Omega ↔ (rho, s) ∈ Omega)
    (hPperiod : ∀ rho, Periodic (fun s => P (rho, s)) L)
    (hGperiod : ∀ rho, Periodic (fun s => G (rho, s)) L)
    (hWperiod : ∀ rho, Periodic (fun s => W (rho, s)) L)
    (hcentral : ∀ s,
      0 < visibleConnectorA (fun x => P (0, x)) (fun x => W (0, x)) s ∧
      0 < visibleConnectorB (fun x => G (0, x)) (fun x => W (0, x)) s ∧
      0 < visibleConnectorC (fun x => G (0, x)) (fun x => W (0, x)) s) :
    ∃ delta > 0, ∃ r > 0, ∀ rho, |rho| < delta →
      let p := fun s => P (rho, s)
      let gamma := fun s => G (rho, s)
      let w := fun s => W (rho, s)
      let tc := visibleConnectorActualTerminalHeight p gamma w
      (∀ s, (rho, s) ∈ Omega) ∧
      ContDiff ℝ ∞ p ∧ ContDiff ℝ ∞ gamma ∧ ContDiff ℝ ∞ w ∧
      Periodic p L ∧ Periodic gamma L ∧ Periodic w L ∧
      ContDiff ℝ ∞ tc ∧ Periodic tc L ∧
      (∀ s, 0 < visibleConnectorA p w s ∧ 0 < visibleConnectorB gamma w s ∧
        0 < visibleConnectorC gamma w s ∧ 0 < tc s ∧
        ∀ u ∈ Icc (-r) (tc s), 0 < visibleConnectorDelta p gamma w ![s, u]) := by
  obtain ⟨r, hr, hbox⟩ := incomingFamily_compact_box hOmega hP hG hW haxis hcentral
  have hfull (rho s u : ℝ) (hρ : |rho| < r) (hu : |u| < r) :
      (rho, s) ∈ Omega ∧
      0 < visibleConnectorA (fun x => P (rho, x)) (fun x => W (rho, x)) s ∧
      0 < visibleConnectorB (fun x => G (rho, x)) (fun x => W (rho, x)) s ∧
      0 < visibleConnectorC (fun x => G (rho, x)) (fun x => W (rho, x)) s ∧
      0 < visibleConnectorDelta (fun x => P (rho, x)) (fun x => G (rho, x))
        (fun x => W (rho, x)) ![s, u] := by
    let sm := toIcoMod hL 0 s
    have hsm : sm ∈ Icc (0 : ℝ) L := Ico_subset_Icc_self (toIcoMod_mem_Ico' hL s)
    obtain ⟨hΩ, ha, hb, hc, hj⟩ := hbox rho sm u hsm hρ hu
    have hΩp : Periodic (fun x : ℝ => (rho, x) ∈ Omega) L := fun x => propext (hOmegaL rho x)
    obtain ⟨hAp, hBp, hCp⟩ := incomingFamily_coefficients_periodic (hPperiod rho) (hGperiod rho) (hWperiod rho)
    have hJp : Periodic (fun x => visibleConnectorDelta (fun y => P (rho, y))
        (fun y => G (rho, y)) (fun y => W (rho, y)) ![x, u]) L := by
      intro x
      simp only [visibleConnectorDelta, Matrix.cons_val_zero, Matrix.cons_val_one,
        hAp x, hBp x, hCp x]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [seam_periodic_eq_representative hL hΩp s]
      exact hΩ
    · rw [seam_periodic_eq_representative hL hAp s]
      exact ha
    · rw [seam_periodic_eq_representative hL hBp s]
      exact hb
    · rw [seam_periodic_eq_representative hL hCp s]
      exact hc
    · rw [seam_periodic_eq_representative hL hJp s]
      exact hj
  refine ⟨r / 2, half_pos hr, r / 2, half_pos hr, ?_⟩
  intro rho hρ
  dsimp only
  have hρr : |rho| < r := hρ.trans (half_lt_self hr)
  have hΩ (s : ℝ) : (rho, s) ∈ Omega := (hfull rho s 0 hρr (by simpa using hr)).1
  have hp : ContDiff ℝ ∞ (fun s => P (rho, s)) := contDiffOn_univ.mp
    (hP.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun s _ => hΩ s))
  have hg : ContDiff ℝ ∞ (fun s => G (rho, s)) := contDiffOn_univ.mp
    (hG.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun s _ => hΩ s))
  have hw : ContDiff ℝ ∞ (fun s => W (rho, s)) := contDiffOn_univ.mp
    (hW.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun s _ => hΩ s))
  have hsign (s : ℝ) := (hfull rho s 0 hρr (by simpa using hr)).2
  have htc := visibleConnectorActualTerminalHeight_contDiff hp hg hw (fun s => (hsign s).2.2.1.ne')
  obtain ⟨hAp, hBp, hCp⟩ := incomingFamily_coefficients_periodic (hPperiod rho) (hGperiod rho) (hWperiod rho)
  have htcp : Periodic (visibleConnectorActualTerminalHeight (fun s => P (rho, s))
      (fun s => G (rho, s)) (fun s => W (rho, s))) L := by
    intro s
    unfold visibleConnectorActualTerminalHeight
    rw [hAp s, hCp s]
  refine ⟨hΩ, hp, hg, hw, hPperiod rho, hGperiod rho, hWperiod rho, htc, htcp, ?_⟩
  intro s
  obtain ⟨ha, hb, hc, _⟩ := hsign s
  obtain ⟨htcpos, hclosed⟩ := incomingFamily_closed_segment_positive ha hb hc
  refine ⟨ha, hb, hc, htcpos, ?_⟩
  intro u hu
  by_cases hunonnegative : 0 ≤ u
  · exact hclosed u ⟨hunonnegative, hu.2⟩
  · have hunegative : u < 0 := lt_of_not_ge hunonnegative
    have hur : |u| < r := by
      rw [abs_of_neg hunegative]
      linarith [hu.1, half_lt_self hr]
    exact (hfull rho s u hρr hur).2.2.2.2

end
end TightVer401
