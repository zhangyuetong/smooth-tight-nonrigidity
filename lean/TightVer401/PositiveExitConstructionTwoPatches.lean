import TightVer401.PositiveExitConstructionProtectedLeaves
import TightVer401.PositiveExitConstructionActualPatch

/-! Two actual exits of one fixed core, both constructed from the SAME
unperturbed Cartesian potential. Cutoff selection makes their compact change
strips disjoint. The resulting potential retains both actual nonlinear returns
and positive graphs, the original protected bending, and saddle sign throughout
the original domain. No global gradient/Jordan/visibility conclusion is claimed. -/
open scoped Manifold
namespace TightVer401
noncomputable section
open Set Filter MeasureTheory OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-- Actual dynamics retained by one exit after adding the disjoint other change.
This is an output, using the original ε/profile and the actual combined height. -/
structure PositiveExitPairedFermiPreserved {P : ℝ} [Fact (0 < P)]
    {G : Coord → ℝ} {U C : Set Coord} {ζ : ℝ → Ambient}
    {hp : Function.Periodic ζ P} {η ξ σ ρMax : ℝ}
    (D : PositiveExitActualFermiData G U ζ hp η ξ σ ρMax)
    (B : PositiveExitActualCartesianPatch G U C ζ hp η ξ σ ρMax D)
    (Ge : Coord → ℝ) where
  height_germ : ∀ q ∈ D.W, |q 1| ≤ D.rho →
    positiveExitFermiHeight Ge ζ =ᶠ[𝓝 q]
      fermiPerturbedSupport B.epsilon (normalLoopCurvature ζ) (positiveExitFermiHeight G ζ)
        (fermiExitCutoff D.rho D.rho_pos)
  tensor_equal : ∀ q ∈ D.W, |q 1| ≤ D.rho →
    sphereSupportTensor (inducedMetric (fermiNormalMap ζ)) (positiveExitFermiHeight Ge ζ) q =
      sphereSupportTensor (inducedMetric (fermiNormalMap ζ))
        (fermiPerturbedSupport B.epsilon (normalLoopCurvature ζ) (positiveExitFermiHeight G ζ)
          (fermiExitCutoff D.rho D.rho_pos)) q
  actual_return : ∃ (V : Set Coord) (u : Coord → ℝ),
    IsOpen V ∧ ContDiffOn ℝ ∞ u V ∧
    (∀ q ∈ V, (![q 0,u q] : Coord) ∈ D.W ∧ |u q| < D.rho) ∧
    (∀ q ∈ V, coordPartial 0 u q = fermiSupportAsymptoticSlope (normalLoopCurvature ζ)
      (positiveExitFermiHeight Ge ζ) ![q 0,u q]) ∧
    (∀ r ∈ Icc (0 : ℝ) P, (![r,0] : Coord) ∈ V ∧ u ![r,0] = 0) ∧
    ((fun x : ℝ => u ![0,x]) =ᶠ[𝓝 (0 : ℝ)] id) ∧
    HasDerivAt (fun x : ℝ => u ![P,x])
      (Real.exp (-(B.epsilon / 2 * ∫ r in 0..P, (normalLoopCurvature ζ r)^2))) 0 ∧
    (0 < B.epsilon → ∃ d > 0, ∀ x : ℝ, |x| < d →
      (∀ n : ℕ, |((fun y : ℝ => u ![P,y])^[n]) x| < d) ∧
      Tendsto (fun n : ℕ => ((fun y : ℝ => u ![P,y])^[n]) x) atTop (𝓝 0)) ∧
    (B.epsilon < 0 → ∃ d > 0, ∀ x : ℝ, x ≠ 0 → |x| < d →
      ∃ n : ℕ, d ≤ |((fun y : ℝ => u ![P,y])^[n]) x|) ∧
    ∃ μ > 0, ∀ r ∈ Icc (0 : ℝ) P, ∀ x : ℝ, |x| ≤ μ → (![r,x] : Coord) ∈ V
  positive_graphs :
    let κ := normalLoopCurvature ζ
    let Hε := fermiPerturbedSupport B.epsilon κ (positiveExitFermiHeight G ζ)
      (fermiExitCutoff D.rho D.rho_pos)
    let v := exitPositiveGraphProfile P (fermiSupportSeamSlope κ Hε)
    ∀ n : ℕ, ∀ ν : ℝ, 0 < ν → ∃ (δ : ℝ) (C : AddCircle P → RoundSphere),
      0 < |δ| ∧ |δ| < ν ∧ 0 < δ * B.epsilon ∧
      Topology.IsEmbedding C ∧ ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ C ∧
      (∀ q, Function.Injective (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) C q)) ∧
      (∀ r, (C (periodProjection P r) : Ambient) = fermiNormalMap ζ (exitGraphCurve v δ r)) ∧
      (∀ q, ‖(C q : Ambient) - hp.lift q‖ < ν) ∧
      (∀ r ∈ Icc (0 : ℝ) P, exitGraphCurve v δ r ∈ D.W ∧ |δ * v r| < D.rho) ∧
      (∀ r ∈ Icc (0 : ℝ) P, 0 < dotProduct (deriv (exitGraphCurve v δ) r)
        (sphereSupportTensor (inducedMetric (fermiNormalMap ζ))
          (positiveExitFermiHeight Ge ζ) (exitGraphCurve v δ r) *ᵥ deriv (exitGraphCurve v δ) r)) ∧
      (∀ r ∈ Icc (0 : ℝ) P, (sphereSupportTensor (inducedMetric (fermiNormalMap ζ))
        (positiveExitFermiHeight Ge ζ) (exitGraphCurve v δ r)).det < 0) ∧
      ∀ j ≤ n, ∀ r ∈ Icc (0 : ℝ) P,
        ‖iteratedFDeriv ℝ j (fun s : ℝ => fermiNormalMap ζ (exitGraphCurve v δ s)) r -
          iteratedFDeriv ℝ j ζ r‖ < ν

theorem positiveExit_pair_preserves_actual_fermi {P : ℝ} [Fact (0 < P)]
    {G Ge : Coord → ℝ} {U C : Set Coord} {ζ : ℝ → Ambient}
    {hp : Function.Periodic ζ P} {η ξ σ ρMax : ℝ}
    (D : PositiveExitActualFermiData G U ζ hp η ξ σ ρMax)
    (B : PositiveExitActualCartesianPatch G U C ζ hp η ξ σ ρMax D)
    (hGe : ContDiffOn ℝ ∞ Ge U)
    (hgerm : ∀ y ∈ positiveExitFermiPatchStrip D.fermi_chart D.rho_lt_tube,
      Ge =ᶠ[𝓝 y] (fun z => G z + B.change z)) :
    Nonempty (PositiveExitPairedFermiPreserved D B Ge) := by
  let κ := normalLoopCurvature ζ
  let Hε := fermiPerturbedSupport B.epsilon κ (positiveExitFermiHeight G ζ)
    (fermiExitCutoff D.rho D.rho_pos)
  have hκ : ContDiff ℝ ∞ κ := (normalLoop_actual_smooth D.zeta_smooth).2
  have hH : ContDiffOn ℝ ∞ (positiveExitFermiHeight Ge ζ) D.W :=
    positiveExitFermiHeight_contDiffOn D.zeta_smooth hGe D.fermi_north D.source_in_U
  have hHε : ContDiffOn ℝ ∞ Hε D.W := B.actual_fermi_exit.1
  have hh (q : Coord) (hq : q ∈ D.W) (ht : |q 1| ≤ D.rho) :
      positiveExitFermiHeight Ge ζ =ᶠ[𝓝 q] Hε := by
    let p : AddCircle P × Icc (-D.rho) D.rho :=
      (periodProjection P (q 0), ⟨q 1, abs_le.mp ht⟩)
    have hraw : D.fermi_chart (positiveExitFermiClosedStripInclusion D.rho_lt_tube p) =
        positiveExitFermiSource ζ q := by
      rw [D.fermi_chart_actual]
      change gnomonicInverse (Real.cos (q 1) • hp.lift (periodProjection P (q 0)) +
          Real.sin (q 1) • (normalLoop_actual_periodic D.zeta_smooth hp).1.lift
            (periodProjection P (q 0))) =
        gnomonicInverse (Real.cos (q 1) • ζ (q 0) + Real.sin (q 1) • normalLoopTangent ζ (q 0))
      rw [periodicLift_coe,periodicLift_coe]
    have hs : positiveExitFermiSource ζ q ∈ positiveExitFermiPatchStrip D.fermi_chart D.rho_lt_tube :=
      ⟨p, hraw⟩
    have hP := ((positiveExitFermiSource_contDiffOn D.zeta_smooth D.fermi_north q hq).contDiffAt
      (D.W_open.mem_nhds hq)).continuousAt
    have hc := (hgerm _ hs).comp_tendsto hP.tendsto
    have he : positiveExitFermiHeight Ge ζ =ᶠ[𝓝 q]
        positiveExitFermiHeight (fun z => G z + B.change z) ζ := by
      filter_upwards [hc] with z hz
      change Ge (positiveExitFermiSource ζ z) =
        G (positiveExitFermiSource ζ z) + B.change (positiveExitFermiSource ζ z) at hz
      unfold positiveExitFermiHeight
      rw [hz]
    exact he.trans (B.actual_height.eventuallyEq_of_mem (D.W_open.mem_nhds hq))
  have htensor (q : Coord) (hq : q ∈ D.W) (ht : |q 1| ≤ D.rho) :
      sphereSupportTensor (inducedMetric (fermiNormalMap ζ)) (positiveExitFermiHeight Ge ζ) q =
        sphereSupportTensor (inducedMetric (fermiNormalMap ζ)) Hε q := by
    have he := fermiSupport_eventuallyEq (hh q hq ht) κ
    rw [fermiNormalMap_inducedMetric D.zeta_smooth D.unit D.unit_speed,
      fermiSupport_actual_matrix hκ D.W_open hH hq (D.scale_nonzero q hq),
      fermiSupport_actual_matrix hκ D.W_open hHε hq (D.scale_nonzero q hq),
      he.1.eq_of_nhds, he.2.1.eq_of_nhds, he.2.2.eq_of_nhds]
  obtain ⟨V, u, hV, hu, himage, hode, haxis, hinitial, hreturn, hattract, hrepel, hgraphs⟩ :=
    B.actual_fermi_exit.2.2.2.2.2.2
  let V' := V ∩ u ⁻¹' Ioo (-D.rho) D.rho
  have hV' : IsOpen V' := hu.continuousOn.isOpen_inter_preimage hV isOpen_Ioo
  have haxis' (r : ℝ) (hr : r ∈ Icc (0 : ℝ) P) : (![r,0] : Coord) ∈ V' := by
    refine ⟨(haxis r hr).1, ?_⟩
    change u (![r,0] : Coord) ∈ Ioo (-D.rho) D.rho
    rw [(haxis r hr).2]
    exact ⟨neg_neg_of_pos D.rho_pos, D.rho_pos⟩
  have himage' (q : Coord) (hq : q ∈ V') :
      (![q 0,u q] : Coord) ∈ D.W ∧ |u q| < D.rho :=
    ⟨himage q hq.1, abs_lt.mpr hq.2⟩
  have hode' (q : Coord) (hq : q ∈ V') : coordPartial 0 u q =
      fermiSupportAsymptoticSlope κ (positiveExitFermiHeight Ge ζ) ![q 0,u q] := by
    have he := fermiSupport_eventuallyEq
      (hh (![q 0,u q]) (himage' q hq).1
        (by change |u q| ≤ D.rho; exact (himage' q hq).2.le)) κ
    have hodeq : coordPartial 0 u q =
        fermiSupportAsymptoticSlope κ Hε (![q 0,u q] : Coord) := hode q hq.1
    rw [hodeq]
    simp only [fermiSupportAsymptoticSlope, fermiAsymptoticSlope,
      he.1.eq_of_nhds, he.2.1.eq_of_nhds, he.2.2.eq_of_nhds]
  obtain ⟨μ,hμ,hsmall⟩ := seam_compact_axis_open_collar
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) P)) hV' haxis'
  refine ⟨{
    height_germ := hh
    tensor_equal := htensor
    actual_return := ⟨V',u,hV',hu.mono inter_subset_left,himage',hode',
      (fun r hr => ⟨haxis' r hr,(haxis r hr).2⟩),
      hinitial,hreturn,hattract,hrepel,μ,hμ,hsmall⟩
    positive_graphs := ?_ }⟩
  dsimp only
  intro n ν hν
  obtain ⟨δ,C,hδ,hδν,hδε,hCe,hCs,hCi,hCF,hclose,hCW,hpositive,hnegative,hjets⟩ := hgraphs n ν hν
  refine ⟨δ,C,hδ,hδν,hδε,hCe,hCs,hCi,hCF,hclose,hCW,?_,?_,hjets⟩
  · intro r hr
    rw [htensor (exitGraphCurve _ δ r) (hCW r hr).1
      (by simpa [exitGraphCurve] using (hCW r hr).2.le)]
    exact hpositive r hr
  · intro r hr
    rw [htensor (exitGraphCurve _ δ r) (hCW r hr).1
      (by simpa [exitGraphCurve] using (hCW r hr).2.le)]
    exact hnegative r hr

theorem positiveExit_pair_C2_triangle {J K : Coord → ℝ}
    (hJ : ContDiff ℝ ∞ J) (hK : ContDiff ℝ ∞ K) (y : Coord) :
    fermiCoordinateC2Size (fun z => J z + K z) y ≤
      fermiCoordinateC2Size J y + fermiCoordinateC2Size K y := by
  have h1 (i : Fin 2) : coordPartial i (fun z => J z + K z) =
      (fun z => coordPartial i J z + coordPartial i K z) := by
    funext z
    unfold coordPartial
    rw [fderiv_fun_add (hJ.differentiable (by simp) z) (hK.differentiable (by simp) z)]
    rfl
  have h2 (i j : Fin 2) : coordPartial i (coordPartial j (fun z => J z + K z)) y =
      coordPartial i (coordPartial j J) y + coordPartial i (coordPartial j K) y := by
    rw [h1 j]
    change fderiv ℝ (fun z => coordPartial j J z + coordPartial j K z) y (Pi.single i 1) =
      fderiv ℝ (coordPartial j J) y (Pi.single i 1) +
        fderiv ℝ (coordPartial j K) y (Pi.single i 1)
    have hd : fderiv ℝ (fun z => coordPartial j J z + coordPartial j K z) y =
        fderiv ℝ (coordPartial j J) y + fderiv ℝ (coordPartial j K) y :=
      fderiv_fun_add ((fermiCoordinatePartial_contDiff hJ j).differentiable (by simp) y)
        ((fermiCoordinatePartial_contDiff hK j).differentiable (by simp) y)
    rw [hd]
    rfl
  have h2' (i j : Fin 2) : coordPartial i (fun z => coordPartial j J z + coordPartial j K z) y =
      coordPartial i (coordPartial j J) y + coordPartial i (coordPartial j K) y := by
    rw [← h1 j]
    exact h2 i j
  simp only [fermiCoordinateC2Size, h1, h2', Fin.sum_univ_two]
  linarith [norm_add_le (J y) (K y),
    norm_add_le (coordPartial 0 J y) (coordPartial 0 K y),
    norm_add_le (coordPartial 1 J y) (coordPartial 1 K y),
    norm_add_le (coordPartial 0 (coordPartial 0 J) y) (coordPartial 0 (coordPartial 0 K) y),
    norm_add_le (coordPartial 0 (coordPartial 1 J) y) (coordPartial 0 (coordPartial 1 K) y),
    norm_add_le (coordPartial 1 (coordPartial 0 J) y) (coordPartial 1 (coordPartial 0 K) y),
    norm_add_le (coordPartial 1 (coordPartial 1 J) y) (coordPartial 1 (coordPartial 1 K) y)]

theorem positiveExit_pair_change_zero {P : ℝ} [Fact (0 < P)]
    {G : Coord → ℝ} {U C : Set Coord} {ζ : ℝ → Ambient}
    {hp : Function.Periodic ζ P} {η ξ σ ρMax : ℝ}
    {D : PositiveExitActualFermiData G U ζ hp η ξ σ ρMax}
    (B : PositiveExitActualCartesianPatch G U C ζ hp η ξ σ ρMax D)
    {y : Coord} (hy : y ∉ positiveExitFermiPatchStrip D.fermi_chart D.rho_lt_tube) :
    B.change =ᶠ[𝓝 y] (fun _ => 0) := by
  filter_upwards [B.protected_open.mem_nhds hy] with z hz
  have he := B.protected_equal hz
  change G z + B.change z = G z at he
  linarith

/-- Select two actual complete leaves around a prescribed compact protected
core, construct disjoint weighted patches from the SAME original G, and retain
their actual returns/positive graphs for one combined potential. All inputs are
ordinary data of the already constructed core; no exit package is supplied. -/
theorem positiveExit_exists_two_actual_cartesian_patches {T δ w : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T)
    (hb : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0)
    (hδ : 0 < δ)
    (hinside : ∀ u ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 u t ∈ Ioo 0 w)
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
    (C : Set Coord) (hC : IsCompact C) (hne : C.Nonempty)
    (hprotect : C ⊆ e '' range (identityFlowBandInclusion d hb 0 hinside))
    (Y : AddCircle T × Ioo (0 : ℝ) w → Ambient)
    (hbend : IsInfinitesimalBendingOn (planarSupportMap G) (Y ∘ e.symm) e.target)
    (hsupport : e '' tsupport Y ⊆ C)
    {η ξ σin σout : ℝ} (hη : 0 < η) (hξ : 0 < ξ)
    (hσin : σin ≠ 0) (hσout : σout ≠ 0) :
    ∃ vin vout : Ioo (0 : ℝ) δ, (vin : ℝ) < (vout : ℝ) ∧
    ∃ S1 : ℝ ≃ₜ ℝ, ∃ P1 : ℝ, ∃ hP1 : 0 < P1, ∃ ρMax1 : ℝ,
    ∃ hp1 : Function.Periodic (positiveExitRawLeaf d hb hinside vin ∘ S1.symm) P1,
      letI : Fact (0 < P1) := ⟨hP1⟩
      ∃ D1 : PositiveExitActualFermiData G e.target
        (positiveExitRawLeaf d hb hinside vin ∘ S1.symm) hp1 (η/2) ξ σin ρMax1,
      ∃ B1 : PositiveExitActualCartesianPatch G e.target
        (C ∪ range (e ∘ positiveExitLeaf d hb hinside vout))
        (positiveExitRawLeaf d hb hinside vin ∘ S1.symm) hp1 (η/2) ξ σin ρMax1 D1,
      let A1 := positiveExitFermiPatchStrip D1.fermi_chart D1.rho_lt_tube
      ∃ S2 : ℝ ≃ₜ ℝ, ∃ P2 : ℝ, ∃ hP2 : 0 < P2, ∃ ρMax2 : ℝ,
      ∃ hp2 : Function.Periodic (positiveExitRawLeaf d hb hinside vout ∘ S2.symm) P2,
      letI : Fact (0 < P2) := ⟨hP2⟩
      ∃ D2 : PositiveExitActualFermiData G e.target
        (positiveExitRawLeaf d hb hinside vout ∘ S2.symm) hp2 (η/2) ξ σout ρMax2,
      ∃ B2 : PositiveExitActualCartesianPatch G e.target (C ∪ A1)
        (positiveExitRawLeaf d hb hinside vout ∘ S2.symm) hp2 (η/2) ξ σout ρMax2 D2,
      let A2 := positiveExitFermiPatchStrip D2.fermi_chart D2.rho_lt_tube
      let Ge := fun z => G z + B1.change z + B2.change z
      Disjoint A1 A2 ∧
      ContDiffOn ℝ ∞ Ge e.target ∧
      ContDiff ℝ ∞ (fun z => B1.change z + B2.change z) ∧
      HasCompactSupport (fun z => B1.change z + B2.change z) ∧
      (∀ z, fermiCoordinateC2Size (fun q => B1.change q + B2.change q) z < η) ∧
      IsOpen (A1 ∪ A2)ᶜ ∧ C ⊆ (A1 ∪ A2)ᶜ ∧ EqOn Ge G (A1 ∪ A2)ᶜ ∧
      (∀ z ∈ C, Ge =ᶠ[𝓝 z] G) ∧
      IsInfinitesimalBendingOn (planarSupportMap Ge) (Y ∘ e.symm) e.target ∧
      (∀ y ∈ e.target, (planarHessian Ge y).det < 0) ∧
      Nonempty (PositiveExitPairedFermiPreserved D1 B1 Ge) ∧
      Nonempty (PositiveExitPairedFermiPreserved D2 B2 Ge) := by
  obtain ⟨vin,vout,horder,_hlabels,hin,hout,hboth,_hsin,_hsout,_hsboth⟩ :=
    positiveExit_exists_two_protected_complete_leaves d hb e hinside heS heF heI hδ hC hne hprotect
  let Lout : Set Coord := range (e ∘ positiveExitLeaf d hb hinside vout)
  have hLout : IsCompact Lout := isCompact_range (heD.continuous.comp
    (positiveExitLeaf_contMDiff d hb hinside vout).continuous)
  have hraw (v : Ioo (0 : ℝ) δ) (t : ℝ) :
      gnomonicInverse (positiveExitRawLeaf d hb hinside v t) =
        e (positiveExitLeaf d hb hinside v (periodProjection T t)) :=
    positiveExitGaussLeaf_cartesian_source d hb e hinside heF v (periodProjection T t)
  have havoid1 (t : ℝ) : gnomonicInverse (positiveExitRawLeaf d hb hinside vin t) ∉ C ∪ Lout := by
    rw [hraw]
    intro hmem
    rcases hmem with hc | hl
    · exact disjoint_left.mp hin (mem_range_self (periodProjection T t)) hc
    · exact disjoint_left.mp hboth (mem_range_self (periodProjection T t)) hl
  have hsupport1 : e '' tsupport Y ⊆ C ∪ Lout := fun _ hz => Or.inl (hsupport hz)
  obtain ⟨S1,P1,hP1,ρMax1,_hρ1,hp1,D1,B1,_hbend1,_hS1,_hLength1⟩ :=
    positiveExit_selected_leaf_actual_cartesian_patch d hb hinside vin hNi hbandNorth horient hτ
      e heS heF heD heI G hG hrec hdet (C ∪ Lout) (hC.union hLout) havoid1
      Y hbend hsupport1 (half_pos hη) hξ hσin
  letI : Fact (0 < P1) := ⟨hP1⟩
  let A1 := positiveExitFermiPatchStrip D1.fermi_chart D1.rho_lt_tube
  have hA1 : IsCompact A1 := positiveExitFermiPatchStrip_compact D1.fermi_chart
    D1.rho_lt_tube D1.fermi_chart_smooth
  have havoid2 (t : ℝ) : gnomonicInverse (positiveExitRawLeaf d hb hinside vout t) ∉ C ∪ A1 := by
    rw [hraw]
    intro hmem
    rcases hmem with hc | ha
    · exact disjoint_left.mp hout (mem_range_self (periodProjection T t)) hc
    · exact disjoint_left.mp B1.strip_disjoint ha
        (Or.inr (mem_range_self (periodProjection T t)))
  have hsupport2 : e '' tsupport Y ⊆ C ∪ A1 := fun _ hz => Or.inl (hsupport hz)
  obtain ⟨S2,P2,hP2,ρMax2,_hρ2,hp2,D2,B2,_hbend2,_hS2,_hLength2⟩ :=
    positiveExit_selected_leaf_actual_cartesian_patch d hb hinside vout hNi hbandNorth horient hτ
      e heS heF heD heI G hG hrec hdet (C ∪ A1) (hC.union hA1) havoid2
      Y hbend hsupport2 (half_pos hη) hξ hσout
  letI : Fact (0 < P2) := ⟨hP2⟩
  let A2 := positiveExitFermiPatchStrip D2.fermi_chart D2.rho_lt_tube
  let Ge := fun z => G z + B1.change z + B2.change z
  have hA2 : IsCompact A2 := positiveExitFermiPatchStrip_compact D2.fermi_chart
    D2.rho_lt_tube D2.fermi_chart_smooth
  have hdis : Disjoint A1 A2 := by
    apply disjoint_left.mpr
    intro z hz1 hz2
    exact disjoint_left.mp B2.strip_disjoint hz2 (Or.inr hz1)
  have hGe : ContDiffOn ℝ ∞ Ge e.target :=
    (hG.add B1.change_smooth.contDiffOn).add B2.change_smooth.contDiffOn
  have hprotected : C ⊆ (A1 ∪ A2)ᶜ := by
    intro z hz hmem
    rcases hmem with hz1 | hz2
    · exact disjoint_left.mp B1.strip_disjoint hz1 (Or.inl hz)
    · exact disjoint_left.mp B2.strip_disjoint hz2 (Or.inl hz)
  have hprotectedOpen : IsOpen (A1 ∪ A2)ᶜ := (hA1.union hA2).isClosed.isOpen_compl
  have hprotectedEq : EqOn Ge G (A1 ∪ A2)ᶜ := by
    intro z hz
    have hz1 : z ∉ A1 := fun h => hz (Or.inl h)
    have hz2 : z ∉ A2 := fun h => hz (Or.inr h)
    have h1 := (positiveExit_pair_change_zero B1 hz1).eq_of_nhds
    have h2 := (positiveExit_pair_change_zero B2 hz2).eq_of_nhds
    change G z + B1.change z + B2.change z = G z
    rw [h1,h2,add_zero,add_zero]
  have hprotectedGerm (z : Coord) (hz : z ∈ C) : Ge =ᶠ[𝓝 z] G :=
    hprotectedEq.eventuallyEq_of_mem (hprotectedOpen.mem_nhds (hprotected hz))
  have hgerm1 (z : Coord) (hz : z ∈ A1) : Ge =ᶠ[𝓝 z] (fun q => G q + B1.change q) := by
    have hz2 : z ∉ A2 := fun h => disjoint_left.mp hdis hz h
    filter_upwards [positiveExit_pair_change_zero B2 hz2] with q hq
    change G q + B1.change q + B2.change q = G q + B1.change q
    rw [hq,add_zero]
  have hgerm2 (z : Coord) (hz : z ∉ A1) : Ge =ᶠ[𝓝 z] (fun q => G q + B2.change q) := by
    filter_upwards [positiveExit_pair_change_zero B1 hz] with q hq
    change G q + B1.change q + B2.change q = G q + B2.change q
    rw [hq,add_zero]
  have hwhole (z : Coord) (hz : z ∈ e.target) : (planarHessian Ge z).det < 0 := by
    by_cases hz1 : z ∈ A1
    · have he := hgerm1 z hz1
      have hess : planarHessian Ge z = planarHessian (fun q => G q + B1.change q) z := by
        ext i j
        exact (fermiCoordinatePartial_eventuallyEq (fermiCoordinatePartial_eventuallyEq he j) i).eq_of_nhds
      rw [hess]
      exact B1.whole_saddle z hz
    · have he := hgerm2 z hz1
      have hess : planarHessian Ge z = planarHessian (fun q => G q + B2.change q) z := by
        ext i j
        exact (fermiCoordinatePartial_eventuallyEq (fermiCoordinatePartial_eventuallyEq he j) i).eq_of_nhds
      rw [hess]
      exact B2.whole_saddle z hz
  have hBending : IsInfinitesimalBendingOn (planarSupportMap Ge) (Y ∘ e.symm) e.target := by
    refine ⟨hbend.1, ?_⟩
    intro z hz i j
    by_cases hs : e.symm z ∈ tsupport Y
    · have hzc : z ∈ C := hsupport ⟨e.symm z,hs,e.right_inv hz⟩
      have he := hprotectedGerm z hzc
      have hm : planarSupportMap Ge =ᶠ[𝓝 z] planarSupportMap G := by
        filter_upwards [he,he.eventuallyEq_nhds] with q hq hg
        unfold planarSupportMap
        simp only [coordPartial,hg.fderiv_eq (𝕜 := ℝ),hq]
      have hd := hm.fderiv_eq (𝕜 := ℝ)
      simpa only [strain,coordPartial,hd] using hbend.2 z hz i j
    · have hi : ContinuousAt e.symm z :=
        (heI.continuousOn z hz).continuousAt (e.open_target.mem_nhds hz)
      have he : (Y ∘ e.symm) =ᶠ[𝓝 z] (fun _ => 0) := by
        filter_upwards [hi.preimage_mem_nhds ((isClosed_tsupport Y).isOpen_compl.mem_nhds hs)] with q hq
        change Y (e.symm q) = 0
        by_contra hn
        exact hq (subset_tsupport Y hn)
      have hd : fderiv ℝ (Y ∘ e.symm) z = 0 :=
        (he.fderiv_eq (𝕜 := ℝ)).trans (hasFDerivAt_const (c := (0 : Ambient)) z).fderiv
      simp only [strain,coordPartial,hd,ContinuousLinearMap.zero_apply,
        inner_zero_left,inner_zero_right,add_zero]
  have hC2 (z : Coord) : fermiCoordinateC2Size (fun q => B1.change q + B2.change q) z < η :=
    (positiveExit_pair_C2_triangle B1.change_smooth B2.change_smooth z).trans_lt
      (by linarith [B1.change_C2 z,B2.change_C2 z])
  have hpres1 := positiveExit_pair_preserves_actual_fermi D1 B1 hGe hgerm1
  have hpres2 := positiveExit_pair_preserves_actual_fermi D2 B2 hGe
    (fun z hz => hgerm2 z (fun hz1 => disjoint_left.mp hdis hz1 hz))
  exact ⟨vin,vout,horder,S1,P1,hP1,ρMax1,hp1,D1,B1,
    S2,P2,hP2,ρMax2,hp2,D2,B2,hdis,hGe,B1.change_smooth.add B2.change_smooth,
    B1.change_compact.add B2.change_compact,hC2,
    hprotectedOpen,hprotected,hprotectedEq,hprotectedGerm,hBending,hwhole,hpres1,hpres2⟩

end
end TightVer401
