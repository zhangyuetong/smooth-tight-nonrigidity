import TightVer401.PositiveExitConstructionActualFermi
import TightVer401.PositiveExitConstructionPatch
import TightVer401.SeamPeriodicity

/-! A single actual Cartesian exit of the SAME protected core. The selected
closed leaf supplies the actual Fermi collar and nonlinear return. Compact
separation chooses the cutoff before ε; the explicit weighted change is then
globally smooth, preserves the original bending, and remains saddle everywhere
on the original source image. No exit or inverse package is an input. -/
open scoped Manifold
namespace TightVer401
noncomputable section
open Set Filter MeasureTheory OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff Topology Matrix RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

/-- Compact separation in the actual northern Cartesian source, before any
perturbation is selected. Only ordinary closed-set disjointness is input. -/
theorem positiveExitFermi_exists_protected_cutoff {P : ℝ} (hP : 0 < P)
    {ζ : ℝ → Ambient} (hζ : ContDiff ℝ ∞ ζ) (hp : Function.Periodic ζ P)
    (hnorth : ∀ r, 0 < ζ r 2) {C : Set Coord} (hC : IsClosed C)
    (hdisjoint : ∀ r, gnomonicInverse (ζ r) ∉ C) :
    ∃ ρMax > 0, ∀ r ∈ Icc (0 : ℝ) P, ∀ t : ℝ, |t| ≤ ρMax →
      positiveExitFermiSource ζ (![r,t] : Coord) ∉ C := by
  let N : Set Coord := {q | 0 < fermiNormalMap ζ q 2}
  have hN : IsOpen N := isOpen_lt continuous_const
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) (2 : Fin 3)).continuous.comp
      (fermiNormalMap_contDiff hζ).continuous)
  have hPN : ContDiffOn ℝ ∞ (positiveExitFermiSource ζ) N :=
    positiveExitFermiSource_contDiffOn hζ (fun _ hq => hq)
  let V : Set Coord := N ∩ (positiveExitFermiSource ζ) ⁻¹' Cᶜ
  have hV : IsOpen V := hPN.continuousOn.isOpen_inter_preimage hN hC.isOpen_compl
  have haxis (s : ℝ) (_hs : s ∈ Icc (0 : ℝ) P) : (![s,0] : Coord) ∈ V := by
    constructor
    · simpa [N, fermiNormalMap] using hnorth s
    · simpa [positiveExitFermiSource, fermiNormalMap] using hdisjoint s
  obtain ⟨r, hr, hstrip⟩ := seam_compact_axis_open_collar
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) P)) hV haxis
  exact ⟨r, hr, fun s hs t ht => (hstrip s hs t ht).2⟩

theorem positiveExitFermiCartesianChange_linear {P tube : ℝ}
    {a κ : ℝ → ℝ} (haP : Function.Periodic a P) (hκP : Function.Periodic κ P)
    (ε ρ : ℝ) (hρ : 0 < ρ)
    (e : OpenPartialHomeomorph (AddCircle P × Ioo (-tube) tube) Coord) :
    positiveExitFermiCartesianChange haP hκP ε ρ hρ e =
      (fun y => ε * positiveExitFermiCartesianChange haP hκP 1 ρ hρ e y) := by
  classical
  funext y
  by_cases hy : y ∈ e.target
  · simp only [positiveExitFermiCartesianChange,if_pos hy]
    unfold positiveExitFermiNativeChange
    ring
  · simp [positiveExitFermiCartesianChange,hy]

private theorem positiveExit_actual_chart_raw {P : ℝ} [Fact (0 < P)]
    {G : Coord → ℝ} {U : Set Coord} {ζ : ℝ → Ambient}
    {hp : Function.Periodic ζ P} {η ξ σ ρMax : ℝ}
    (D : PositiveExitActualFermiData G U ζ hp η ξ σ ρMax)
    (s : ℝ) (t : Ioo (-D.tube) D.tube) :
    D.fermi_chart (periodProjection P s,t) =
      positiveExitFermiSource ζ (![s,(t : ℝ)] : Coord) := by
  rw [D.fermi_chart_actual]
  change gnomonicInverse (Real.cos (t : ℝ) • hp.lift (periodProjection P s) +
      Real.sin (t : ℝ) • (normalLoop_actual_periodic D.zeta_smooth hp).1.lift (periodProjection P s)) =
    gnomonicInverse (Real.cos (t : ℝ) • ζ s + Real.sin (t : ℝ) • normalLoopTangent ζ s)
  rw [periodicLift_coe,periodicLift_coe]

/-- The fixed geometric strip has actual fundamental-period representatives
in the constructed compact set, before the perturbation amplitude is chosen. -/
theorem positiveExit_actual_fermi_strip_representation {P : ℝ} [Fact (0 < P)]
    {G : Coord → ℝ} {U : Set Coord} {ζ : ℝ → Ambient}
    {hp : Function.Periodic ζ P} {η ξ σ ρMax : ℝ}
    (D : PositiveExitActualFermiData G U ζ hp η ξ σ ρMax) :
    ∀ y ∈ positiveExitFermiPatchStrip D.fermi_chart D.rho_lt_tube,
      ∃ q ∈ D.K, q 0 ∈ Icc (0 : ℝ) P ∧ |q 1| ≤ D.rho ∧
        positiveExitFermiSource ζ q = y := by
  rintro y ⟨p,rfl⟩
  obtain ⟨s,hs⟩ := QuotientAddGroup.mk_surjective p.1
  let r := toIcoMod (Fact.out : 0 < P) 0 s
  have hr : r ∈ Icc (0 : ℝ) P := Ico_subset_Icc_self
    (toIcoMod_mem_Ico' (Fact.out : 0 < P) s)
  have ht : |(p.2 : ℝ)| ≤ D.rho := abs_le.mpr p.2.property
  have hperiod : Function.Periodic
      (fun u : ℝ => positiveExitFermiSource ζ (![u,(p.2 : ℝ)] : Coord)) P := by
    intro u
    have hshift : (![u,(p.2 : ℝ)] : Coord) + Pi.single 0 P = ![u+P,(p.2 : ℝ)] := by
      ext i; fin_cases i <;> simp
    simpa only [hshift] using positiveExitFermiSource_periodic D.zeta_smooth hp
      (![u,(p.2 : ℝ)] : Coord)
  refine ⟨![r,(p.2 : ℝ)],D.complete_change_strip r hr _ ht,hr,ht,?_⟩
  have hraw := positiveExit_actual_chart_raw D s
    (positiveExitFermiClosedStripInclusion D.rho_lt_tube p).2
  have hquot : periodProjection P s = p.1 := hs
  rw [hquot] at hraw
  exact (seam_periodic_eq_representative (Fact.out : 0 < P) hperiod s).symm.trans hraw.symm

theorem positiveExit_actual_fermi_strip_in_U {P : ℝ} [Fact (0 < P)]
    {G : Coord → ℝ} {U : Set Coord} {ζ : ℝ → Ambient}
    {hp : Function.Periodic ζ P} {η ξ σ ρMax : ℝ}
    (D : PositiveExitActualFermiData G U ζ hp η ξ σ ρMax) :
    positiveExitFermiPatchStrip D.fermi_chart D.rho_lt_tube ⊆ U := by
  intro y hy
  obtain ⟨q,hq,_hr,_ht,rfl⟩ := positiveExit_actual_fermi_strip_representation D y hy
  exact D.source_in_U (D.K_in_W hq)

/-- Fixed explicit unit-amplitude weighted change, used to compute genuine
compact embedding thresholds before selecting the actual exit amplitude. -/
def positiveExitActualUnitChange {P : ℝ} [Fact (0 < P)]
    {G : Coord → ℝ} {U : Set Coord} {ζ : ℝ → Ambient}
    {hp : Function.Periodic ζ P} {η ξ σ ρMax : ℝ}
    (D : PositiveExitActualFermiData G U ζ hp η ξ σ ρMax) : Coord → ℝ :=
  positiveExitFermiCartesianChange
    (fermiSeam_coefficients_periodic (normalLoop_actual_periodic D.zeta_smooth hp).2
      D.height_periodic).1
    (normalLoop_actual_periodic D.zeta_smooth hp).2 1 D.rho D.rho_pos D.fermi_chart

theorem positiveExitActualUnitChange_contDiff {P : ℝ} [Fact (0 < P)]
    {G : Coord → ℝ} {U : Set Coord} {ζ : ℝ → Ambient}
    {hp : Function.Periodic ζ P} {η ξ σ ρMax : ℝ}
    (D : PositiveExitActualFermiData G U ζ hp η ξ σ ρMax) :
    ContDiff ℝ ∞ (positiveExitActualUnitChange D) := by
  have hκ := (normalLoop_actual_smooth D.zeta_smooth).2
  exact positiveExitFermiCartesianChange_contDiff _ _
    (fermiSeam_coefficients_smooth hκ D.W_open D.height_smooth D.scale_nonzero D.seam_in_W).1
    hκ 1 D.rho_pos D.fermi_chart D.fermi_chart_source D.rho_lt_tube
    D.fermi_chart_smooth D.fermi_inverse_smooth

theorem positiveExitActualUnitChange_tsupport {P : ℝ} [Fact (0 < P)]
    {G : Coord → ℝ} {U : Set Coord} {ζ : ℝ → Ambient}
    {hp : Function.Periodic ζ P} {η ξ σ ρMax : ℝ}
    (D : PositiveExitActualFermiData G U ζ hp η ξ σ ρMax) :
    tsupport (positiveExitActualUnitChange D) ⊆
      positiveExitFermiPatchStrip D.fermi_chart D.rho_lt_tube :=
  positiveExitFermiCartesianChange_tsupport _ _ 1 D.rho_pos
    D.fermi_chart D.rho_lt_tube D.fermi_chart_smooth

/-- Ordinary output for precisely the chosen ε, including the actual nonlinear
return and finite-jet positive graphs, coupled to the SAME Cartesian change. -/
structure PositiveExitActualCartesianPatch {P : ℝ} [Fact (0 < P)]
    (G : Coord → ℝ) (U C : Set Coord) (ζ : ℝ → Ambient)
    (hp : Function.Periodic ζ P) (η ξ σ ρMax : ℝ)
    (D : PositiveExitActualFermiData G U ζ hp η ξ σ ρMax) where
  epsilon : ℝ
  epsilon_sign : 0 < epsilon * σ
  epsilon_small : |epsilon| < ξ
  actual_fermi_exit : PositiveExitActualFermiPerturbationAt ζ hp
    (positiveExitFermiHeight G ζ) D.W D.K D.rho_pos η epsilon
  change : Coord → ℝ
  change_actual : change = positiveExitFermiCartesianChange
    (fermiSeam_coefficients_periodic (normalLoop_actual_periodic D.zeta_smooth hp).2
      D.height_periodic).1
    (normalLoop_actual_periodic D.zeta_smooth hp).2 epsilon D.rho D.rho_pos D.fermi_chart
  change_smooth : ContDiff ℝ ∞ change
  change_compact : HasCompactSupport change
  change_support : tsupport change ⊆ positiveExitFermiPatchStrip D.fermi_chart D.rho_lt_tube
  strip_in_U : positiveExitFermiPatchStrip D.fermi_chart D.rho_lt_tube ⊆ U
  strip_disjoint : Disjoint (positiveExitFermiPatchStrip D.fermi_chart D.rho_lt_tube) C
  change_C2 : ∀ y, fermiCoordinateC2Size change y < η
  potential_smooth : ContDiffOn ℝ ∞ (fun y => G y + change y) U
  actual_height : EqOn (positiveExitFermiHeight (fun y => G y + change y) ζ)
    (fermiPerturbedSupport epsilon (normalLoopCurvature ζ) (positiveExitFermiHeight G ζ)
      (fermiExitCutoff D.rho D.rho_pos)) D.W
  protected_open : IsOpen (positiveExitFermiPatchStrip D.fermi_chart D.rho_lt_tube)ᶜ
  protected_contains : C ⊆ (positiveExitFermiPatchStrip D.fermi_chart D.rho_lt_tube)ᶜ
  protected_equal : EqOn (fun y => G y + change y) G
    (positiveExitFermiPatchStrip D.fermi_chart D.rho_lt_tube)ᶜ
  protected_germ : ∀ y ∈ C, (fun z => G z + change z) =ᶠ[𝓝 y] G
  whole_saddle : ∀ y ∈ U, (planarHessian (fun z => G z + change z) y).det < 0

theorem positiveExit_actual_cartesian_patch_with_bound {P : ℝ} [Fact (0 < P)]
    {G : Coord → ℝ} {U C : Set Coord} {ζ : ℝ → Ambient}
    {hp : Function.Periodic ζ P} {η ξ σ ρMax : ℝ}
    (D : PositiveExitActualFermiData G U ζ hp η ξ σ ρMax)
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U)
    (hdet : ∀ y ∈ U, (planarHessian G y).det < 0)
    (hη : 0 < η) (hξ : 0 < ξ) (hσ : σ ≠ 0)
    (havoid : ∀ r ∈ Icc (0 : ℝ) P, ∀ t : ℝ, |t| ≤ ρMax →
      positiveExitFermiSource ζ (![r,t] : Coord) ∉ C)
    {ξExtra : ℝ} (hExtra : 0 < ξExtra) :
    ∃ B : PositiveExitActualCartesianPatch G U C ζ hp η ξ σ ρMax D,
      |B.epsilon| < ξExtra := by
  let κ := normalLoopCurvature ζ
  let H := positiveExitFermiHeight G ζ
  let a := fermiSeamMixed κ H
  have hκ : ContDiff ℝ ∞ κ := (normalLoop_actual_smooth D.zeta_smooth).2
  have hκP : Function.Periodic κ P := (normalLoop_actual_periodic D.zeta_smooth hp).2
  have ha : ContDiff ℝ ∞ a := (fermiSeam_coefficients_smooth hκ D.W_open
    D.height_smooth D.scale_nonzero D.seam_in_W).1
  have haP : Function.Periodic a P := (fermiSeam_coefficients_periodic hκP D.height_periodic).1
  let J1 := positiveExitFermiCartesianChange haP hκP 1 D.rho D.rho_pos D.fermi_chart
  let A := positiveExitFermiPatchStrip D.fermi_chart D.rho_lt_tube
  have hA : IsCompact A := positiveExitFermiPatchStrip_compact D.fermi_chart
    D.rho_lt_tube D.fermi_chart_smooth
  have hJ1 : ContDiff ℝ ∞ J1 := positiveExitFermiCartesianChange_contDiff haP hκP ha hκ
    1 D.rho_pos D.fermi_chart D.fermi_chart_source D.rho_lt_tube
    D.fermi_chart_smooth D.fermi_inverse_smooth
  obtain ⟨ξCart, hξCart, hC2⟩ := exists_fermiPerturbation_C2_threshold hJ1 hA hη
  obtain ⟨ε, hε, hεsmall, hexit⟩ := D.perturbation_small hη
    (lt_min hξ (lt_min hξCart hExtra)) hσ
  let J := positiveExitFermiCartesianChange haP hκP ε D.rho D.rho_pos D.fermi_chart
  let Ge := fun y => G y + J y
  have hJ : ContDiff ℝ ∞ J := positiveExitFermiCartesianChange_contDiff haP hκP ha hκ
    ε D.rho_pos D.fermi_chart D.fermi_chart_source D.rho_lt_tube
    D.fermi_chart_smooth D.fermi_inverse_smooth
  have hGe : ContDiffOn ℝ ∞ Ge U := hG.add hJ.contDiffOn
  have hJlin : J = fun y => ε * J1 y := positiveExitFermiCartesianChange_linear
    haP hκP ε D.rho D.rho_pos D.fermi_chart
  have hrep := positiveExit_actual_fermi_strip_representation D
  have hAU : A ⊆ U := by
    intro y hy
    obtain ⟨q,hq,_hr,_ht,rfl⟩ := hrep y hy
    exact D.source_in_U (D.K_in_W hq)
  have hAC : Disjoint A C := by
    apply disjoint_left.mpr
    intro y hy hcy
    obtain ⟨q,_hq,hr,ht,heq⟩ := hrep y hy
    have hqeq : (![q 0,q 1] : Coord) = q := by ext i; fin_cases i <;> rfl
    apply havoid (q 0) hr (q 1) (ht.trans D.rho_lt_max.le)
    simpa only [hqeq, heq] using hcy
  have hprotected := positiveExitFermiCartesianChange_protected_germ haP hκP ε D.rho_pos
    D.fermi_chart D.rho_lt_tube D.fermi_chart_smooth G
  have hheight : EqOn (positiveExitFermiHeight Ge ζ)
      (fermiPerturbedSupport ε κ H (fermiExitCutoff D.rho D.rho_pos)) D.W := by
    intro q hq
    let p : AddCircle P × Ioo (-D.tube) D.tube :=
      (periodProjection P (q 0), ⟨q 1, abs_lt.mp (D.W_in_tube q hq)⟩)
    have hqeq : (![q 0,q 1] : Coord) = q := by ext i; fin_cases i <;> rfl
    have hpEq : (periodProjection P (q 0),p.2) = p := rfl
    have htval : (p.2 : ℝ) = q 1 := rfl
    have hraw : D.fermi_chart p = positiveExitFermiSource ζ q := by
      have he := positiveExit_actual_chart_raw D (q 0) p.2
      rw [hpEq,htval,hqeq] at he
      exact he
    have hj := positiveExitFermiCartesianChange_height haP hκP ε D.rho D.rho_pos
      D.fermi_chart D.fermi_chart_source p
    rw [hraw] at hj
    have hn := positiveExitFermiNativeChange_raw haP hκP ε D.rho D.rho_pos (q 0) p.2
    rw [hpEq,htval,hqeq] at hn
    change (G (positiveExitFermiSource ζ q) + J (positiveExitFermiSource ζ q)) /
        planarWeight (positiveExitFermiSource ζ q) = _
    rw [add_div, hj, hn]
    rfl
  have hHe : ContDiffOn ℝ ∞ (positiveExitFermiHeight Ge ζ) D.W :=
    positiveExitFermiHeight_contDiffOn D.zeta_smooth hGe D.fermi_north D.source_in_U
  have hwhole : ∀ y ∈ U, (planarHessian Ge y).det < 0 := by
    intro y hy
    by_cases hyA : y ∈ A
    · obtain ⟨q,hq,_hr,_ht,rfl⟩ := hrep y hyA
      have hqW := D.K_in_W hq
      have heg := hheight.eventuallyEq_of_mem (D.W_open.mem_nhds hqW)
      have hentries := fermiSupport_eventuallyEq heg κ
      have hHeps := hexit.1
      have hnegative := hexit.2.2.2.2.2.1 q hq
      have hmetric : inducedMetric (fermiNormalMap ζ) = fermiMetric (fermiNormalScale κ) := by
        funext z
        exact fermiNormalMap_metric D.zeta_smooth D.unit D.unit_speed z
      have hmatrixE := fermiSupport_actual_matrix hκ D.W_open hHe hqW (D.scale_nonzero q hqW)
      have hmatrixP := fermiSupport_actual_matrix hκ D.W_open hHeps hqW (D.scale_nonzero q hqW)
      have htensor : sphereSupportTensor (inducedMetric (fermiNormalMap ζ))
          (positiveExitFermiHeight Ge ζ) q =
          sphereSupportTensor (inducedMetric (fermiNormalMap ζ))
            (fermiPerturbedSupport ε κ H (fermiExitCutoff D.rho D.rho_pos)) q := by
        rw [hmetric, hmatrixE, hmatrixP, hentries.1.eq_of_nhds,
          hentries.2.1.eq_of_nhds, hentries.2.2.eq_of_nhds]
      rw [← htensor, positiveExitFermi_tensor_det D.zeta_smooth D.unit D.unit_speed
        hGe hU D.W_open D.fermi_north D.scale_nonzero D.source_in_U hqW] at hnegative
      have hnum : (positiveExitJacobian (positiveExitFermiSource ζ) q).det^2 *
          (planarHessian Ge (positiveExitFermiSource ζ q)).det < 0 :=
        by simpa only [zero_mul] using
          (div_lt_iff₀ (sq_pos_of_pos (planarWeight_pos _))).mp hnegative
      by_contra hn
      exact (not_lt_of_ge (mul_nonneg (sq_nonneg _) (le_of_not_gt hn))) hnum
    · have hg := hprotected.2.2 y hyA
      have hh (i j : Fin 2) : coordPartial i (coordPartial j Ge) y =
          coordPartial i (coordPartial j G) y :=
        (fermiCoordinatePartial_eventuallyEq (fermiCoordinatePartial_eventuallyEq hg j) i).eq_of_nhds
      have heH : planarHessian Ge y = planarHessian G y := by
        ext i j
        exact hh i j
      rw [heH]
      exact hdet y hy
  have hglobalC2 : ∀ y, fermiCoordinateC2Size J y < η := by
    intro y
    by_cases hy : y ∈ A
    · rw [hJlin]
      exact hC2 ε (hεsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))) y hy
    · have hjzero : J =ᶠ[𝓝 y] (fun _ => 0) := by
        filter_upwards [hA.isClosed.isOpen_compl.mem_nhds hy] with z hz
        exact positiveExitFermiCartesianChange_zero_off_strip haP hκP ε D.rho_pos
          D.fermi_chart D.rho_lt_tube hz
      have h0 := hjzero.eq_of_nhds
      have h1g (i : Fin 2) : coordPartial i J =ᶠ[𝓝 y] (fun _ => 0) := by
        have he := fermiCoordinatePartial_eventuallyEq hjzero i
        have hc : coordPartial i (fun _ : Coord => (0 : ℝ)) = (fun _ => 0) := by
          funext z
          unfold coordPartial
          rw [(hasFDerivAt_const (c := (0 : ℝ)) z).fderiv]
          rfl
        simpa only [hc] using he
      have h1 (i : Fin 2) : coordPartial i J y = 0 := (h1g i).eq_of_nhds
      have h2 (i j : Fin 2) : coordPartial i (coordPartial j J) y = 0 := by
        change fderiv ℝ (coordPartial j J) y (Pi.single i 1) = 0
        rw [(h1g j).fderiv_eq (𝕜 := ℝ),(hasFDerivAt_const (c := (0 : ℝ)) y).fderiv]
        rfl
      simpa [fermiCoordinateC2Size,h0,h1,h2] using hη
  refine ⟨{
    epsilon := ε, epsilon_sign := hε,
    epsilon_small := hεsmall.trans_le (min_le_left _ _), actual_fermi_exit := hexit,
    change := J, change_actual := rfl, change_smooth := hJ,
    change_compact := positiveExitFermiCartesianChange_hasCompactSupport haP hκP ε D.rho_pos
      D.fermi_chart D.rho_lt_tube D.fermi_chart_smooth,
    change_support := positiveExitFermiCartesianChange_tsupport haP hκP ε D.rho_pos
      D.fermi_chart D.rho_lt_tube D.fermi_chart_smooth,
    strip_in_U := hAU, strip_disjoint := hAC, change_C2 := hglobalC2,
    potential_smooth := hGe, actual_height := hheight, protected_open := hprotected.1,
    protected_contains := fun y hy ha => (disjoint_left.mp hAC ha hy),
    protected_equal := hprotected.2.1,
    protected_germ := fun y hy => hprotected.2.2 y (fun ha => disjoint_left.mp hAC ha hy),
    whole_saddle := hwhole },
    hεsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))⟩

theorem positiveExit_actual_cartesian_change_eq_scalar {P : ℝ} [Fact (0 < P)]
    {G : Coord → ℝ} {U C : Set Coord} {ζ : ℝ → Ambient}
    {hp : Function.Periodic ζ P} {η ξ σ ρMax : ℝ}
    (D : PositiveExitActualFermiData G U ζ hp η ξ σ ρMax)
    (B : PositiveExitActualCartesianPatch G U C ζ hp η ξ σ ρMax D) :
    B.change = fun y => B.epsilon * positiveExitActualUnitChange D y := by
  rw [B.change_actual]
  exact positiveExitFermiCartesianChange_linear _ _ B.epsilon D.rho D.rho_pos D.fermi_chart

private theorem positiveExit_actual_patch_bending {T w P : ℝ}
    [Fact (0 < T)] [Fact (0 < P)]
    {G : Coord → ℝ} {C : Set Coord} {ζ : ℝ → Ambient}
    {hp : Function.Periodic ζ P} {η ξ σ ρMax : ℝ}
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) Coord)
    (heS : e.source = univ)
    (heI : ContMDiffOn 𝓘(ℝ, Coord) nativeProductModel ∞ e.symm e.target)
    (Y : AddCircle T × Ioo (0 : ℝ) w → Ambient)
    (hbend : IsInfinitesimalBendingOn (planarSupportMap G) (Y ∘ e.symm) e.target)
    (hsupport : e '' tsupport Y ⊆ C)
    (D : PositiveExitActualFermiData G e.target ζ hp η ξ σ ρMax)
    (B : PositiveExitActualCartesianPatch G e.target C ζ hp η ξ σ ρMax D) :
    IsInfinitesimalBendingOn (planarSupportMap (fun z => G z + B.change z))
      (Y ∘ e.symm) e.target := by
  refine ⟨hbend.1, ?_⟩
  intro y hy i j
  by_cases hs : e.symm y ∈ tsupport Y
  · have hyC : y ∈ C := hsupport ⟨e.symm y, hs, e.right_inv hy⟩
    have hg := B.protected_germ y hyC
    have hm : planarSupportMap (fun z => G z + B.change z) =ᶠ[𝓝 y] planarSupportMap G := by
      filter_upwards [hg, hg.eventuallyEq_nhds] with z hz hzg
      unfold planarSupportMap
      simp only [coordPartial, hzg.fderiv_eq (𝕜 := ℝ), hz]
    have hd := hm.fderiv_eq (𝕜 := ℝ)
    simpa only [strain, coordPartial, hd] using hbend.2 y hy i j
  · have hi : ContinuousAt e.symm y :=
      (heI.continuousOn y hy).continuousAt (e.open_target.mem_nhds hy)
    have hz : (Y ∘ e.symm) =ᶠ[𝓝 y] (fun _ => 0) := by
      filter_upwards [hi.preimage_mem_nhds ((isClosed_tsupport Y).isOpen_compl.mem_nhds hs)] with z hz
      change Y (e.symm z) = 0
      by_contra hn
      exact hz (subset_tsupport Y hn)
    have hd : fderiv ℝ (Y ∘ e.symm) y = 0 :=
      (hz.fderiv_eq (𝕜 := ℝ)).trans (hasFDerivAt_const (c := (0 : Ambient)) y).fderiv
    simp only [strain, coordPartial, hd, ContinuousLinearMap.zero_apply,
      inner_zero_left, inner_zero_right, add_zero]

/-- A single selected complete leaf of the actual core has an actual globally
patched Cartesian exit, with arbitrarily small Cartesian C² change and the same
protected bending field. The cutoff is constructed from compact separation of
the selected leaf from the prescribed protected closure; no avoidance, Fermi
chart, tensor, return or exit witness is assumed. -/
theorem positiveExit_selected_leaf_actual_cartesian_patch {T δ w : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T)
    (hb : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0)
    (hinside : ∀ u ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 u t ∈ Ioo 0 w)
    (v : Ioo (0 : ℝ) δ)
    (hNi : Function.Injective (d.bandGaussMap (b := w)))
    (hbandNorth : ∀ p : AddCircle T × Ioo (0 : ℝ) w, 0 < d.bandGaussMap p 2)
    (horient : ∀ t, ambientCross (d.T t) (d.E t) = d.n t)
    (hτ : ∀ t, d.τ t < 0)
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) Coord)
    (heS : e.source = univ)
    (heF : ∀ p, e p = gnomonicInverse (d.bandGaussMap p))
    (heD : ContMDiff nativeProductModel 𝓘(ℝ, Coord) ∞ e)
    (heI : ContMDiffOn 𝓘(ℝ, Coord) nativeProductModel ∞ e.symm e.target)
    (G : Coord → ℝ) (hG : ContDiffOn ℝ ∞ G e.target)
    (hrec : ∀ p, planarSupportMap G (e p) = d.bandMap p)
    (hdet : ∀ y ∈ e.target, (planarHessian G y).det < 0)
    (C : Set Coord) (hC : IsCompact C)
    (hdisjoint : ∀ t, gnomonicInverse (positiveExitRawLeaf d hb hinside v t) ∉ C)
    (Y : AddCircle T × Ioo (0 : ℝ) w → Ambient)
    (hbend : IsInfinitesimalBendingOn (planarSupportMap G) (Y ∘ e.symm) e.target)
    (hsupport : e '' tsupport Y ⊆ C)
    {η ξ σ : ℝ} (hη : 0 < η) (hξ : 0 < ξ) (hσ : σ ≠ 0) :
    ∃ S : ℝ ≃ₜ ℝ, ∃ P : ℝ, ∃ hP : 0 < P, ∃ ρMax : ℝ, ∃ hρMax : 0 < ρMax,
      ∃ hp : Function.Periodic (positiveExitRawLeaf d hb hinside v ∘ S.symm) P,
      letI : Fact (0 < P) := ⟨hP⟩
      ∃ D : PositiveExitActualFermiData G e.target
        (positiveExitRawLeaf d hb hinside v ∘ S.symm) hp η ξ σ ρMax,
      ∃ B : PositiveExitActualCartesianPatch G e.target C
        (positiveExitRawLeaf d hb hinside v ∘ S.symm) hp η ξ σ ρMax D,
        IsInfinitesimalBendingOn (planarSupportMap (fun z => G z + B.change z))
          (Y ∘ e.symm) e.target ∧
        (S : ℝ → ℝ) = rawPrimitive (positiveExitLeafSpeed d hb hinside v) ∧
        P = rawPrimitive (positiveExitLeafSpeed d hb hinside v) T := by
  obtain ⟨S0, P0, hP0, hS0, hLength0, hSsmooth0, hshift0, hp0, hζ0, hiζ0,
    hunit0, hnorth0, hspeed0⟩ := positiveExitLeaf_exists_unitSpeed d hb hinside v hNi hbandNorth
  have hdisjoint0 (r : ℝ) : gnomonicInverse
      ((positiveExitRawLeaf d hb hinside v ∘ S0.symm) r) ∉ C := hdisjoint (S0.symm r)
  obtain ⟨ρMax, hρMax, havoid⟩ := positiveExitFermi_exists_protected_cutoff hP0
    hζ0 hp0 hnorth0 hC.isClosed hdisjoint0
  obtain ⟨S, P, hP, hS, hLength, hSsmooth, hshift, hp, ⟨D⟩⟩ :=
    positiveExit_selected_leaf_actual_fermi d hb hinside v hNi hbandNorth horient hτ
      e heS heF heD heI G hG hrec hdet hη hξ hσ hρMax
  have hSS : S = S0 := by
    ext s
    exact congrFun (hS.trans hS0.symm) s
  have hPP : P = P0 := hLength.trans hLength0.symm
  subst S
  letI : Fact (0 < P) := ⟨hP⟩
  have havoidP : ∀ r ∈ Icc (0 : ℝ) P, ∀ t : ℝ, |t| ≤ ρMax →
      positiveExitFermiSource (positiveExitRawLeaf d hb hinside v ∘ S0.symm) (![r,t] : Coord) ∉ C := by
    intro r hr t ht
    have hr0 : r ∈ Icc (0 : ℝ) P0 := by rw [← hPP]; exact hr
    exact havoid r hr0 t ht
  obtain ⟨B,_hExtra⟩ := positiveExit_actual_cartesian_patch_with_bound D hG e.open_target
    hdet hη hξ hσ havoidP hξ
  exact ⟨S0,P,hP,ρMax,hρMax,hp,D,B,
    positiveExit_actual_patch_bending e heS heI Y hbend hsupport D B,hS0,hLength⟩

end
end TightVer401
