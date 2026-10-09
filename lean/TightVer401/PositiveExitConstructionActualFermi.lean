import TightVer401.PositiveExitConstructionSeam
import TightVer401.PositiveExitConstructionNullBranch
import TightVer401.FermiExitSmooth

/-! The actual single-selected-leaf application of the retained smooth exit.
Arclength, Fermi chart, support height, chosen null branch and full baseline
identity return are constructed from the same ruled frame and Cartesian G.
The result types below are outputs of the consuming theorem, never inputs. -/
open scoped Manifold
namespace TightVer401
noncomputable section
open Set Filter MeasureTheory OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff Topology Matrix RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- Ordinary retained smooth-exit conclusions for this actual support height.
In particular the return is the actual nonlinear ODE return, and graphs are
close in every prescribed finite order of actual derivatives. -/
def PositiveExitActualFermiPerturbationAt {P ρ : ℝ} [Fact (0 < P)]
    (ζ : ℝ → Ambient) (hζP : Function.Periodic ζ P) (H : Coord → ℝ)
    (W K : Set Coord) (hρ : 0 < ρ) (η ε : ℝ) : Prop :=
    let κ := normalLoopCurvature ζ
    let Hε := fermiPerturbedSupport ε κ H (fermiExitCutoff ρ hρ)
    let v := exitPositiveGraphProfile P (fermiSupportSeamSlope κ Hε)
    ContDiffOn ℝ ∞ Hε W ∧ FermiPeriodic P Hε ∧
    (∀ p, ρ ≤ |p 1| → Hε p = H p) ∧
    (∀ r, Hε ![r,0] = H ![r,0] ∧
      coordPartial 0 Hε ![r,0] = coordPartial 0 H ![r,0] ∧
      coordPartial 1 Hε ![r,0] = coordPartial 1 H ![r,0]) ∧
    (∀ p ∈ K, fermiCoordinateC2Size (fun q => Hε q - H q) p < η) ∧
    (∀ p ∈ K, (sphereSupportTensor (inducedMetric (fermiNormalMap ζ)) Hε p).det < 0) ∧
    ∃ (V : Set Coord) (u : Coord → ℝ), IsOpen V ∧ ContDiffOn ℝ ∞ u V ∧
      (∀ q ∈ V, (![q 0,u q] : Coord) ∈ W) ∧
      (∀ q ∈ V, coordPartial 0 u q = fermiSupportAsymptoticSlope κ Hε ![q 0,u q]) ∧
      (∀ r ∈ Icc (0 : ℝ) P, (![r,0] : Coord) ∈ V ∧ u ![r,0] = 0) ∧
      ((fun x : ℝ => u ![0,x]) =ᶠ[𝓝 (0 : ℝ)] id) ∧
      HasDerivAt (fun x : ℝ => u ![P,x])
        (Real.exp (-(ε / 2 * ∫ r in 0..P, (κ r)^2))) 0 ∧
      (0 < ε → ∃ d > 0, ∀ x : ℝ, |x| < d →
        (∀ n : ℕ, |((fun y : ℝ => u ![P,y])^[n]) x| < d) ∧
        Tendsto (fun n : ℕ => ((fun y : ℝ => u ![P,y])^[n]) x) atTop (𝓝 0)) ∧
      (ε < 0 → ∃ d > 0, ∀ x : ℝ, x ≠ 0 → |x| < d →
        ∃ n : ℕ, d ≤ |((fun y : ℝ => u ![P,y])^[n]) x|) ∧
      ∀ n : ℕ, ∀ ν : ℝ, 0 < ν → ∃ (δ : ℝ) (C : AddCircle P → RoundSphere),
        0 < |δ| ∧ |δ| < ν ∧ 0 < δ * ε ∧
        Topology.IsEmbedding C ∧ ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ C ∧
        (∀ q, Function.Injective (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) C q)) ∧
        (∀ r, (C (periodProjection P r) : Ambient) = fermiNormalMap ζ (exitGraphCurve v δ r)) ∧
        (∀ q, ‖(C q : Ambient) - hζP.lift q‖ < ν) ∧
        (∀ r ∈ Icc (0 : ℝ) P, exitGraphCurve v δ r ∈ W ∧ |δ * v r| < ρ) ∧
        (∀ r ∈ Icc (0 : ℝ) P, 0 < dotProduct (deriv (exitGraphCurve v δ) r)
          (sphereSupportTensor (inducedMetric (fermiNormalMap ζ)) Hε (exitGraphCurve v δ r) *ᵥ
            deriv (exitGraphCurve v δ) r)) ∧
        (∀ r ∈ Icc (0 : ℝ) P,
          (sphereSupportTensor (inducedMetric (fermiNormalMap ζ)) Hε (exitGraphCurve v δ r)).det < 0) ∧
        ∀ j ≤ n, ∀ r ∈ Icc (0 : ℝ) P,
          ‖iteratedFDeriv ℝ j (fun s : ℝ => fermiNormalMap ζ (exitGraphCurve v δ s)) r -
            iteratedFDeriv ℝ j ζ r‖ < ν

/-- The ordinary actual exit conclusions with the chosen perturbation size
retained, so the weighted Cartesian change uses precisely the same ε. -/
def PositiveExitActualFermiPerturbation {P ρ : ℝ} [Fact (0 < P)]
    (ζ : ℝ → Ambient) (hζP : Function.Periodic ζ P) (H : Coord → ℝ)
    (W K : Set Coord) (hρ : 0 < ρ) (η ξ σ : ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε * σ ∧ |ε| < ξ ∧
    PositiveExitActualFermiPerturbationAt ζ hζP H W K hρ η ε

/-- Output of the actual selected-leaf application. The explicit smaller
cutoff and actual Fermi chart are retained for the weighted Cartesian patch. -/
structure PositiveExitActualFermiData {P : ℝ} [Fact (0 < P)]
    (G : Coord → ℝ) (U : Set Coord) (ζ : ℝ → Ambient)
    (hζP : Function.Periodic ζ P) (η ξ σ ρMax : ℝ) where
  zeta_smooth : ContDiff ℝ ∞ ζ
  unit : ∀ r, inner ℝ (ζ r) (ζ r) = 1
  unit_speed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1
  zeta_injective : Function.Injective hζP.lift
  north : ∀ r, 0 < ζ r 2
  tube : ℝ
  tube_pos : 0 < tube
  fermi_chart : OpenPartialHomeomorph (AddCircle P × Ioo (-tube) tube) Coord
  fermi_chart_source : fermi_chart.source = univ
  fermi_chart_actual : ∀ p, fermi_chart p =
    positiveExitFermiCartesian (ρ := tube) zeta_smooth hζP unit unit_speed p
  fermi_chart_smooth : ContMDiff nativeProductModel 𝓘(ℝ, Coord) ∞ fermi_chart
  fermi_inverse_smooth : ContMDiffOn 𝓘(ℝ, Coord) nativeProductModel ∞ fermi_chart.symm fermi_chart.target
  W : Set Coord
  W_open : IsOpen W
  seam_in_W : ∀ r, (![r, 0] : Coord) ∈ W
  W_in_tube : ∀ q ∈ W, |q 1| < tube
  source_in_U : MapsTo (positiveExitFermiSource ζ) W U
  fermi_north : ∀ q ∈ W, 0 < fermiNormalMap ζ q 2
  scale_nonzero : ∀ q ∈ W, fermiNormalScale (normalLoopCurvature ζ) q ≠ 0
  height_smooth : ContDiffOn ℝ ∞ (positiveExitFermiHeight G ζ) W
  height_periodic : FermiPeriodic P (positiveExitFermiHeight G ζ)
  actual_tangent_zero : ∀ r,
    fermiSupportL (normalLoopCurvature ζ) (positiveExitFermiHeight G ζ) ![r, 0] = 0
  actual_mixed_positive : ∀ r,
    0 < fermiSeamMixed (normalLoopCurvature ζ) (positiveExitFermiHeight G ζ) r
  rho : ℝ
  rho_pos : 0 < rho
  rho_lt_tube : rho < tube
  rho_lt_max : rho < ρMax
  K : Set Coord
  K_compact : IsCompact K
  K_in_W : K ⊆ W
  complete_change_strip : ∀ r ∈ Icc (0 : ℝ) P, ∀ t : ℝ, |t| ≤ rho → (![r, t] : Coord) ∈ K
  baseline_V : Set Coord
  baseline_u : Coord → ℝ
  baseline_V_open : IsOpen baseline_V
  baseline_u_smooth : ContDiffOn ℝ ∞ baseline_u baseline_V
  baseline_image : ∀ q ∈ baseline_V, (![q 0, baseline_u q] : Coord) ∈ W
  baseline_ode : ∀ q ∈ baseline_V, coordPartial 0 baseline_u q =
    fermiSupportAsymptoticSlope (normalLoopCurvature ζ) (positiveExitFermiHeight G ζ) ![q 0,baseline_u q]
  baseline_axis : ∀ r ∈ Icc (0 : ℝ) P, (![r, 0] : Coord) ∈ baseline_V
  baseline_zero : ∀ r ∈ Icc (0 : ℝ) P, baseline_u ![r, 0] = 0
  baseline_initial : (fun x : ℝ => baseline_u ![0,x]) =ᶠ[𝓝 (0 : ℝ)] id
  baseline_return : (fun x : ℝ => baseline_u ![P,x]) =ᶠ[𝓝 (0 : ℝ)] id
  curvature_mass : 0 < ∫ r in 0..P, (normalLoopCurvature ζ r)^2
  perturbation : PositiveExitActualFermiPerturbation ζ hζP (positiveExitFermiHeight G ζ)
    W K rho_pos η ξ σ
  perturbation_small : ∀ {η' ξ' σ' : ℝ}, 0 < η' → 0 < ξ' → σ' ≠ 0 →
    PositiveExitActualFermiPerturbation ζ hζP (positiveExitFermiHeight G ζ)
      W K rho_pos η' ξ' σ'

/-- Actual consuming construction for one selected complete leaf of the
same protected core. No Fermi inverse, seam, conservation or return package
is supplied. The core chart identities are its already constructed ordinary
maps, and G is precisely that core's actual potential. -/
theorem positiveExit_selected_leaf_actual_fermi {T δ w : ℝ} [Fact (0 < T)]
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
    {η ξ σ ρMax : ℝ} (hη : 0 < η) (hξ : 0 < ξ) (hσ : σ ≠ 0)
    (hρMax : 0 < ρMax) :
    ∃ S : ℝ ≃ₜ ℝ, ∃ P : ℝ, ∃ hP : 0 < P,
      (S : ℝ → ℝ) = rawPrimitive (positiveExitLeafSpeed d hb hinside v) ∧
      P = rawPrimitive (positiveExitLeafSpeed d hb hinside v) T ∧
      ContDiff ℝ ∞ S.symm ∧ (∀ s, S.symm (s + P) = S.symm s + T) ∧
      ∃ hp : Function.Periodic (positiveExitRawLeaf d hb hinside v ∘ S.symm) P,
        letI : Fact (0 < P) := ⟨hP⟩
        Nonempty (PositiveExitActualFermiData G e.target
          (positiveExitRawLeaf d hb hinside v ∘ S.symm) hp η ξ σ ρMax) := by
  obtain ⟨S, P, hP, hS, hPlength, hSsmooth, hshift, hp, hζ, hiζ, hunit, hnorth, hspeed⟩ :=
    positiveExitLeaf_exists_unitSpeed d hb hinside v hNi hbandNorth
  letI : Fact (0 < P) := ⟨hP⟩
  let ζ := positiveExitRawLeaf d hb hinside v ∘ S.symm
  let H := positiveExitFermiHeight G ζ
  let κ := normalLoopCurvature ζ
  let C := positiveExitFermiLabel d hb e ζ
  have hκ : ContDiff ℝ ∞ κ := (normalLoop_actual_smooth hζ).2
  obtain ⟨tube, htube, _hTubeInj, _hTubeNorth, _hTubeScale, eF, heFS, _heFT, heFF, heFD, heFI⟩ :=
    positiveExit_exists_fermi_collar hζ hp hunit hspeed hiζ hnorth
  let V : Set Coord := (positiveExitFermiLabelDomain e ζ ∩
    {q | fermiNormalScale κ q ≠ 0}) ∩ {q | |q 1| < tube}
  have hV : IsOpen V := ((positiveExitFermiLabelDomain_isOpen e hζ).inter
    (isClosed_singleton.isOpen_compl.preimage (fermiNormalScale_contDiff hκ).continuous)).inter
      (isOpen_lt (continuous_abs.comp (continuous_apply 1)) continuous_const)
  have hVDom : V ⊆ positiveExitFermiLabelDomain e ζ := fun _ hq => hq.1.1
  have hVN : ∀ q ∈ V, 0 < fermiNormalMap ζ q 2 := fun _ hq => hq.1.1.1
  have hVS : ∀ q ∈ V, fermiNormalScale κ q ≠ 0 := fun _ hq => hq.1.2
  have hVP : MapsTo (positiveExitFermiSource ζ) V e.target := fun _ hq => hq.1.1.2
  have hVseam (s : ℝ) : (![s, 0] : Coord) ∈ V := by
    have hpS : positiveExitLeaf d hb hinside v (periodProjection T (S.symm s)) ∈ e.source := by
      rw [heS]; exact mem_univ _
    have hsrc : positiveExitFermiSource ζ (![s, 0] : Coord) =
        e (positiveExitLeaf d hb hinside v (periodProjection T (S.symm s))) := by
      simp only [positiveExitFermiSource, fermiNormalMap, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Real.cos_zero, Real.sin_zero,
        one_smul, zero_smul, add_zero]
      rw [heF]
      rfl
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · simpa [ζ,fermiNormalMap] using hnorth s
    · change positiveExitFermiSource ζ (![s,0] : Coord) ∈ e.target
      rw [hsrc]
      exact e.map_source hpS
    · simp [fermiNormalScale]
    · simpa using htube
  have hrawRec (t : ℝ) : planarSupportMap G (gnomonicInverse
      (d.rawGaussMap (positiveExitLeafRawCoordinates d v t))) =
      ruledMap d.γ d.E (positiveExitLeafRawCoordinates d v t) := by
    let p : AddCircle T × Ioo (0 : ℝ) w :=
      (periodProjection T t, ⟨principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 v t,
        hinside v v.property t⟩)
    have hh := hrec p
    rw [heF p] at hh
    exact hh
  have hseamData := positiveExitFermi_closed_leaf_seam d hb hinside v S hS horient hτ
    hζ hunit hspeed hG e.open_target hV hVN hVS hVP hVseam hrawRec
  obtain ⟨W, hW, hWV, hWs, hconserve, r, hr, hstrip⟩ :=
    positiveExitFermiLabel_selected_chosen_root_collar (P := P) d hb e heS heF heD heI
      hbandNorth hrec hG hV hVDom hζ hunit hspeed hinside v S.symm
      (fun _ => rfl) hVseam hVS (fun s => (hseamData s).2)
  have hWN : ∀ q ∈ W, 0 < fermiNormalMap ζ q 2 := fun _ hq => hVN _ (hWV hq)
  have hWS : ∀ q ∈ W, fermiNormalScale κ q ≠ 0 := fun _ hq => hVS _ (hWV hq)
  have hWP : MapsTo (positiveExitFermiSource ζ) W e.target := fun _ hq => hVP (hWV hq)
  have hH : ContDiffOn ℝ ∞ H W := positiveExitFermiHeight_contDiffOn hζ hG hWN hWP
  have hHP : FermiPeriodic P H := positiveExitFermiHeight_periodic G hζ hp
  have hC : ContDiffOn ℝ ∞ C W := (positiveExitFermiLabel_contDiffOn d hb e hζ heI).mono
    (hWV.trans hVDom)
  have hperiod : (fun x : ℝ => C (![P, x] : Coord)) =ᶠ[𝓝 (0 : ℝ)]
      (fun x : ℝ => C (![0, x] : Coord)) :=
    Filter.Eventually.of_forall (positiveExitFermiLabel_endpoint_periodic d hb e hζ hp)
  have htransverse : coordPartial 1 C (![0, 0] : Coord) ≠ 0 :=
    (positiveExitFermiLabel_selected_transverse d hb e heS heF heD heI hζ hunit hspeed
      hinside v S.symm (fun _ => rfl) (hVDom (hWV (hWs 0)))).2
  have hzero : ∀ s, fermiSupportL κ H ![s, 0] = 0 := fun s => (hseamData s).1
  have hpos : ∀ s, 0 < fermiSeamMixed κ H s := fun s => (hseamData s).2
  obtain ⟨V0, u0, hV0, hu0, himage0, hode0, haxis0, hzero0, hinitial0, hreturn0, _hdet0⟩ :=
    positiveExit_exists_fermi_identity_return hP hκ hW hH hC hWS hWs hzero hpos
      hperiod hconserve htransverse
  let ρ := min (min tube r) ρMax / 2
  have hρ : 0 < ρ := half_pos (lt_min (lt_min htube hr) hρMax)
  have hρtube : ρ < tube := (half_lt_self (lt_min (lt_min htube hr) hρMax)).trans_le
    ((min_le_left _ _).trans (min_le_left _ _))
  have hρr : ρ ≤ r := (half_le_self (le_of_lt (lt_min (lt_min htube hr) hρMax))).trans
    ((min_le_left _ _).trans (min_le_right _ _))
  have hρmax : ρ < ρMax := (half_lt_self (lt_min (lt_min htube hr) hρMax)).trans_le
    (min_le_right _ _)
  let K : Set Coord := Icc (![0, -ρ] : Coord) (![P, ρ] : Coord)
  have hK : IsCompact K := isCompact_Icc
  have hKU : K ⊆ W := by
    intro q hq
    have hq0 : q 0 ∈ Icc (0 : ℝ) P := ⟨hq.1 0, hq.2 0⟩
    have hq1 : |q 1| ≤ ρ := abs_le.mpr ⟨hq.1 1, hq.2 1⟩
    have heq : (![q 0, q 1] : Coord) = q := by ext i; fin_cases i <;> rfl
    rw [← heq]
    exact hstrip _ hq0 _ (hq1.trans hρr)
  have hcomplete : ∀ s ∈ Icc (0 : ℝ) P, ∀ t : ℝ, |t| ≤ ρ → (![s, t] : Coord) ∈ K := by
    intro s hs t ht
    constructor <;> intro i <;> fin_cases i
    · exact hs.1
    · exact (abs_le.mp ht).1
    · exact hs.2
    · exact (abs_le.mp ht).2
  have hdetK : ∀ q ∈ K, (sphereSupportTensor (inducedMetric (fermiNormalMap ζ)) H q).det < 0 := by
    intro q hq
    exact positiveExitFermi_tensor_det_neg hζ hunit hspeed hG e.open_target hW hWN hWS hWP
      (hKU hq) (hdet _ (hWP (hKU hq)))
  let northAxis : Ambient := WithLp.toLp 2 (![0, 0, 1] : Fin 3 → ℝ)
  have hhemisphere : ∀ s, 0 < inner ℝ (ζ s) northAxis := by
    intro s
    simpa [ζ,northAxis,ambient_inner_dot,dotProduct,Fin.sum_univ_succ] using hnorth s
  have hmass := normalLoop_hemisphere_curvature_sq_period_pos hζ hP hp hunit hspeed hhemisphere
  have hchangedSmall {η' ξ' σ' : ℝ} (hη' : 0 < η') (hξ' : 0 < ξ') (hσ' : σ' ≠ 0) :
      PositiveExitActualFermiPerturbation ζ hp H W K hρ η' ξ' σ' := by
    exact exists_fermiExit_smooth_perturbation hP hρ hη' hξ' hσ' hζ hp hunit hspeed hiζ
      hhemisphere hW hH hHP hK hKU hWS hWs hzero hpos hV0 hu0 hode0 haxis0
      hzero0 hinitial0 hreturn0 hdetK
  refine ⟨S, P, hP, hS, hPlength, hSsmooth, hshift, hp, ⟨?_⟩⟩
  exact {
    zeta_smooth := hζ, unit := hunit, unit_speed := hspeed, zeta_injective := hiζ,
    north := hnorth, tube := tube, tube_pos := htube, fermi_chart := eF,
    fermi_chart_source := heFS, fermi_chart_actual := fun p => congrFun heFF p,
    fermi_chart_smooth := heFD, fermi_inverse_smooth := heFI,
    W := W, W_open := hW, seam_in_W := hWs, W_in_tube := fun q hq => (hWV hq).2,
    source_in_U := hWP, fermi_north := hWN, scale_nonzero := hWS,
    height_smooth := hH, height_periodic := hHP, actual_tangent_zero := hzero,
    actual_mixed_positive := hpos, rho := ρ, rho_pos := hρ, rho_lt_tube := hρtube,
    rho_lt_max := hρmax,
    K := K, K_compact := hK, K_in_W := hKU, complete_change_strip := hcomplete,
    baseline_V := V0, baseline_u := u0, baseline_V_open := hV0, baseline_u_smooth := hu0,
    baseline_image := himage0, baseline_ode := hode0, baseline_axis := haxis0,
    baseline_zero := hzero0, baseline_initial := hinitial0, baseline_return := hreturn0,
    curvature_mass := hmass, perturbation := hchangedSmall hη hξ hσ,
    perturbation_small := hchangedSmall }

end
end TightVer401

