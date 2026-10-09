import TightVer401.PositiveExitConstructionCentralTurn
import TightVer401.IdentityBandGlobalFlow
import Mathlib.Topology.MetricSpace.Thickening

/-! Uniform actual origin turns of complete positive leaves, chosen before
the protected bending field. The original band and potential are retained. -/
open scoped Manifold
namespace TightVer401
noncomputable section
open Set Filter MeasureTheory OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private theorem exitFlowTurn_complex_smooth : ContDiff ℝ ∞ positiveExitComplexPoint := by
  have he : positiveExitComplexPoint = (fun q : Coord =>
      (q 0 : ℂ) + Complex.I * (q 1 : ℂ)) := by
    ext q
    apply Complex.ext <;> simp [positiveExitComplexPoint, Complex.mul_re, Complex.mul_im]
  rw [he]
  exact (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 0)).add
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 1)))

set_option backward.isDefEq.respectTransparency true in
private theorem exitFlowTurn_raw_periodic {T : ℝ} (d : PeriodicRuledFrame T) (s u : ℝ) :
    identityBandCentralCoordinates d (![s + T, u] : Coord) =
      identityBandCentralCoordinates d (![s, u] : Coord) := by
  have hN : d.rawGaussMap (![s + T, u] : Coord) = d.rawGaussMap (![s, u] : Coord) := by
    simp only [PeriodicRuledFrame.rawGaussMap, Matrix.cons_val_zero, Matrix.cons_val_one,
      d.period_T s, d.period_n s, d.period_k s, d.period_τ s]
  exact congrArg gnomonicInverse hN

private theorem exitFlowTurn_path_smooth {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (fun s : ℝ => (![s, u s] : Coord)) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ (id : ℝ → ℝ)
    exact contDiff_id
  · change ContDiff ℝ ∞ u
    exact hu

/-- The actual compact central trace determines a uniform positive strip
and complete initial interval on which BOTH actual Cartesian traces retain
one positive origin turn. Pointwise nonzero is an ordinary explicit premise. -/
theorem positiveExit_exists_turn_complete_flow_initial_margin
    {T w : ℝ} [Fact (0 < T)] (d : PeriodicRuledFrame T)
    (hb : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0)
    {G : Coord → ℝ} {U : Set Coord} (hw : 0 < w) (hU : IsOpen U)
    (hG : ContDiffOn ℝ ∞ G U)
    (hP : ContDiffOn ℝ ∞ (identityBandCentralCoordinates d) (identityBandCentralRawDomain w))
    (hPU : MapsTo (identityBandCentralCoordinates d) (identityBandCentralRawDomain w) U)
    (hpne : ∀ s, positiveExitComplexPoint (identityBandCentralCoordinates d ![s, 0]) ≠ 0)
    (hgne : ∀ s, positiveExitComplexPoint
      (planarGradient G (identityBandCentralCoordinates d ![s, 0])) ≠ 0)
    (hpturn : HasPositiveArgumentTurn
      (positiveExitComplexTrace (fun s => identityBandCentralCoordinates d ![s, 0])) T)
    (hgturn : HasPositiveArgumentTurn
      (positiveExitComplexTrace (fun s => planarGradient G
        (identityBandCentralCoordinates d ![s, 0]))) T) :
    ∃ ρ > 0, ρ < w ∧ ∃ δ > 0, δ < ρ ∧ ∀ v ∈ Ioo (0 : ℝ) δ,
      let u := principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 v
      ContDiff ℝ ∞ u ∧ Function.Periodic u T ∧ (∀ s, u s ∈ Ioo (0 : ℝ) ρ) ∧
      ContDiff ℝ ∞ (positiveExitComplexTrace (fun s => identityBandCentralCoordinates d ![s, u s])) ∧
      Function.Periodic (positiveExitComplexTrace (fun s => identityBandCentralCoordinates d ![s, u s])) T ∧
      ContDiff ℝ ∞ (positiveExitComplexTrace (fun s => planarGradient G
        (identityBandCentralCoordinates d ![s, u s]))) ∧
      Function.Periodic (positiveExitComplexTrace (fun s => planarGradient G
        (identityBandCentralCoordinates d ![s, u s]))) T ∧
      HasPositiveArgumentTurn
        (positiveExitComplexTrace (fun s => identityBandCentralCoordinates d ![s, u s])) T ∧
      HasPositiveArgumentTurn
        (positiveExitComplexTrace (fun s => planarGradient G
          (identityBandCentralCoordinates d ![s, u s]))) T ∧
      (∀ s, positiveExitComplexPoint (identityBandCentralCoordinates d ![s, u s]) ≠ 0) ∧
      (∀ s, positiveExitComplexPoint
        (planarGradient G (identityBandCentralCoordinates d ![s, u s])) ≠ 0) := by
  let P := identityBandCentralCoordinates d
  let CP : Coord → ℂ := positiveExitComplexPoint ∘ P
  let CG : Coord → ℂ := positiveExitComplexPoint ∘ planarGradient G ∘ P
  let Bp : ℝ → ℂ := fun s => CP ![s, 0]
  let Bg : ℝ → ℂ := fun s => CG ![s, 0]
  have hD := identityBandCentralRawDomain_isOpen w
  have hCP : ContDiffOn ℝ ∞ CP (identityBandCentralRawDomain w) :=
    exitFlowTurn_complex_smooth.contDiffOn.comp hP (mapsTo_univ _ _)
  have hCG : ContDiffOn ℝ ∞ CG (identityBandCentralRawDomain w) :=
    exitFlowTurn_complex_smooth.contDiffOn.comp
      ((planarGradient_contDiffOn hG hU).comp hP hPU) (mapsTo_univ _ _)
  have hzero : MapsTo (fun s : ℝ => (![s, 0] : Coord)) univ (identityBandCentralRawDomain w) := by
    intro s _
    change -w < (0 : ℝ) ∧ (0 : ℝ) < w
    constructor <;> linarith
  have hBp : ContDiff ℝ ∞ Bp :=
    contDiffOn_univ.mp (hCP.comp (exitFlowTurn_path_smooth contDiff_const).contDiffOn hzero)
  have hBg : ContDiff ℝ ∞ Bg :=
    contDiffOn_univ.mp (hCG.comp (exitFlowTurn_path_smooth contDiff_const).contDiffOn hzero)
  have hBpP : Function.Periodic Bp T := by
    intro s
    change positiveExitComplexPoint (P ![s + T, 0]) = positiveExitComplexPoint (P ![s, 0])
    dsimp only [P]
    rw [exitFlowTurn_raw_periodic]
  have hBgP : Function.Periodic Bg T := by
    intro s
    change positiveExitComplexPoint (planarGradient G (P ![s + T, 0])) =
      positiveExitComplexPoint (planarGradient G (P ![s, 0]))
    dsimp only [P]
    rw [exitFlowTurn_raw_periodic]
  obtain ⟨εp, hεp, htp⟩ := positiveExit_exists_argumentTurn_C0_threshold
    (Fact.out : 0 < T) hBp hBpP hpne hpturn
  obtain ⟨εg, hεg, htg⟩ := positiveExit_exists_argumentTurn_C0_threshold
    (Fact.out : 0 < T) hBg hBgP hgne hgturn
  let V : Set Coord := {q | q ∈ identityBandCentralRawDomain w ∧
    ‖CP q - Bp (q 0)‖ < εp ∧ ‖CG q - Bg (q 0)‖ < εg}
  have hV : IsOpen V := by
    apply isOpen_iff_mem_nhds.mpr
    intro q hq
    have cP := ((hCP q hq.1).contDiffAt (hD.mem_nhds hq.1)).continuousAt
    have cG := ((hCG q hq.1).contDiffAt (hD.mem_nhds hq.1)).continuousAt
    have c0 : Continuous (fun x : Coord => x 0) :=
      (show ContDiff ℝ ∞ (fun x : Coord => x 0) from contDiff_apply ℝ ℝ 0).continuous
    have cBp : Continuous (fun x : Coord => Bp (x 0)) := hBp.continuous.comp c0
    have cBg : Continuous (fun x : Coord => Bg (x 0)) := hBg.continuous.comp c0
    have h1 := (cP.sub cBp.continuousAt).norm.preimage_mem_nhds (Iio_mem_nhds hq.2.1)
    have h2 := (cG.sub cBg.continuousAt).norm.preimage_mem_nhds (Iio_mem_nhds hq.2.2)
    exact inter_mem (hD.mem_nhds hq.1) (inter_mem h1 h2)
  have hpath : Continuous (fun s : ℝ => (![s, 0] : Coord)) :=
    (exitFlowTurn_path_smooth contDiff_const).continuous
  let K : Set Coord := (fun s : ℝ => (![s, 0] : Coord)) '' Icc 0 T
  have hK : IsCompact K := isCompact_Icc.image hpath
  have hKV : K ⊆ V := by
    rintro _ ⟨s, _, rfl⟩
    refine ⟨hzero (mem_univ s), ?_, ?_⟩
    · simpa only [CP, Bp, Matrix.cons_val_zero, sub_self, norm_zero] using hεp
    · simpa only [CG, Bg, Matrix.cons_val_zero, sub_self, norm_zero] using hεg
  obtain ⟨ε, hε, he⟩ := hK.exists_thickening_subset_open hV hKV
  let ρ := min ε (w / 2)
  have hρ : 0 < ρ := lt_min hε (half_pos hw)
  have hρw : ρ < w := (min_le_right _ _).trans_lt (half_lt_self hw)
  have hstrip : ∀ s ∈ Icc (0 : ℝ) T, ∀ u : ℝ, |u| < ρ →
      (![s, u] : Coord) ∈ V := by
    intro s hs u hu
    apply he
    apply Metric.mem_thickening_iff.mpr
    refine ⟨![s, 0], ⟨s, hs, rfl⟩, ?_⟩
    rw [dist_eq_norm]
    have hnorm : ‖(![s, u] : Coord) - ![s, 0]‖ ≤ |u| := by
      apply (pi_norm_le_iff_of_nonneg (abs_nonneg u)).mpr
      intro i
      fin_cases i <;> simp
    exact hnorm.trans_lt (hu.trans_le (min_le_left _ _))
  obtain ⟨δ, hδ, hδρ, hleaves⟩ := periodicRuledFrame_closed_asymptotic_leaves d hb 0 ρ hρ
  refine ⟨ρ, hρ, hρw, δ, hδ, hδρ, ?_⟩
  intro v hv
  dsimp only
  let u := principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 v
  obtain ⟨_, huP, huS, hu, _, _⟩ := hleaves v hv.1 hv.2
  change Function.Periodic u T at huP
  change ContDiff ℝ ∞ u at huS
  change ∀ s, u s ∈ Ioo (0 : ℝ) ρ at hu
  have hraw : MapsTo (fun s : ℝ => (![s, u s] : Coord)) univ (identityBandCentralRawDomain w) := by
    intro s _
    change -w < u s ∧ u s < w
    constructor
    · linarith [(hu s).1]
    · exact (hu s).2.trans hρw
  have hps : ContDiff ℝ ∞ (fun s => CP ![s, u s]) :=
    contDiffOn_univ.mp (hCP.comp (exitFlowTurn_path_smooth huS).contDiffOn hraw)
  have hgs : ContDiff ℝ ∞ (fun s => CG ![s, u s]) :=
    contDiffOn_univ.mp (hCG.comp (exitFlowTurn_path_smooth huS).contDiffOn hraw)
  have hpp : Function.Periodic (fun s => CP ![s, u s]) T := by
    intro s
    change positiveExitComplexPoint (P ![s + T, u (s + T)]) = positiveExitComplexPoint (P ![s, u s])
    rw [huP s]
    dsimp only [P]
    rw [exitFlowTurn_raw_periodic]
  have hgp : Function.Periodic (fun s => CG ![s, u s]) T := by
    intro s
    change positiveExitComplexPoint (planarGradient G (P ![s + T, u (s + T)])) =
      positiveExitComplexPoint (planarGradient G (P ![s, u s]))
    rw [huP s]
    dsimp only [P]
    rw [exitFlowTurn_raw_periodic]
  have hclose (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :=
    hstrip s hs (u s) (by simpa only [abs_of_pos (hu s).1] using (hu s).2)
  have hpt := htp (fun s => CP ![s, u s]) hps hpp (fun s hs => (hclose s hs).2.1)
  have hgt := htg (fun s => CG ![s, u s]) hgs hgp (fun s hs => (hclose s hs).2.2)
  exact ⟨huS, huP, hu, hps, hpp, hgs, hgp, hpt.1, hgt.1, hpt.2, hgt.2⟩

end
end TightVer401
