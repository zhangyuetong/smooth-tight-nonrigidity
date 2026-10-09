import TightVer401.PositiveExitConstructionSelectedClock
import TightVer401.PositiveExitConstructionEmbeddingPatch

/-! Two exits of the SAME original potential, with sequential amplitude selection.
The first uses G as its actual gradient baseline; the second uses G plus the
first change. Compact disjoint strips preserve both original Fermi constructions.
Both clocks, both visibility margins and both turn margins are chosen before
actual amplitudes. The SAME corrected frame and final protected Y remain fixed.
The actual combined gradient is embedded and has its actual smooth inverse on
its entire image. No exit, inverse, or perturbed embedding package is an input. -/
open scoped Manifold
namespace TightVer401
noncomputable section
open Set Filter MeasureTheory OAI.SmoothLocal.Geometry
open OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff Topology Matrix RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-- Select both complete leaves from one protected core, choose each exit below
the embedding threshold of its actual current baseline, and construct the
inverse of the SAME final gradient. Original Fermi tensors and returns are
preserved by the derived disjointness of the two compact change strips.
This constructs full actual positive traces without granting source or gradient nesting. -/
theorem positiveExit_exists_two_selected_visible_cartesian_patches {T δ w : ℝ} [Fact (0 < T)]
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
    (hemb : Topology.IsEmbedding (fun y : e.target => planarGradient G y.val))
    (C : Set Coord) (hC : IsCompact C) (hne : C.Nonempty)
    (hprotect : C ⊆ e '' range (identityFlowBandInclusion d hb 0 hinside))
    (Y : AddCircle T × Ioo (0 : ℝ) w → Ambient)
    (hbend : IsInfinitesimalBendingOn (planarSupportMap G) (Y ∘ e.symm) e.target)
    (hsupport : e '' tsupport Y ⊆ C)
    {η ξ σin σout : ℝ} (hηBudget : 0 < η) (hξ : 0 < ξ)
    (hσin : σin ≠ 0) (hσout : σout ≠ 0)
    (hmargin : ∀ v : Ioo (0 : ℝ) δ,
      (∀ s, angularDescentComplex (gnomonicInverse (positiveExitRawLeaf d hb hinside v s)) ≠ 0) ∧
      (∀ s, angularDescentComplex (planarGradient G
        (gnomonicInverse (positiveExitRawLeaf d hb hinside v s))) ≠ 0) ∧
      HasPositiveArgumentTurn
        (angularDescentComplex ∘ gnomonicInverse ∘ positiveExitRawLeaf d hb hinside v) T ∧
      HasPositiveArgumentTurn (angularDescentComplex ∘ planarGradient G ∘
        gnomonicInverse ∘ positiveExitRawLeaf d hb hinside v) T ∧
      ComplexVisiblePair (1/4) (angularDescentComplex ∘ gnomonicInverse ∘ positiveExitRawLeaf d hb hinside v)
        (fun s => Complex.I * angularDescentComplex (planarGradient G
          (gnomonicInverse (positiveExitRawLeaf d hb hinside v s)))) ∧
      ComplexVisiblePair (4/5)
        (corrugatedReverseReflect (angularDescentComplex ∘ planarGradient G ∘
          gnomonicInverse ∘ positiveExitRawLeaf d hb hinside v))
        (fun s => Complex.I * corrugatedReverseReflect
          (angularDescentComplex ∘ gnomonicInverse ∘ positiveExitRawLeaf d hb hinside v) s)) :
    ∃ ηChosen > 0, ηChosen ≤ η ∧
    ∃ vin vout : Ioo (0 : ℝ) δ, (vin : ℝ) < (vout : ℝ) ∧
    ∃ S1 : ℝ ≃ₜ ℝ, ∃ P1 : ℝ, ∃ hP1 : 0 < P1, ∃ ρMax1 : ℝ,
    ∃ hp1 : Function.Periodic (positiveExitRawLeaf d hb hinside vin ∘ S1.symm) P1,
      letI : Fact (0 < P1) := ⟨hP1⟩
      ∃ D1 : PositiveExitActualFermiData G e.target
        (positiveExitRawLeaf d hb hinside vin ∘ S1.symm) hp1 (ηChosen/2) ξ σin ρMax1,
      ∃ B1 : PositiveExitActualCartesianPatch G e.target
        (C ∪ range (e ∘ positiveExitLeaf d hb hinside vout))
        (positiveExitRawLeaf d hb hinside vin ∘ S1.symm) hp1 (ηChosen/2) ξ σin ρMax1 D1,
      let A1 := positiveExitFermiPatchStrip D1.fermi_chart D1.rho_lt_tube
      ∃ S2 : ℝ ≃ₜ ℝ, ∃ P2 : ℝ, ∃ hP2 : 0 < P2, ∃ ρMax2 : ℝ,
      ∃ hp2 : Function.Periodic (positiveExitRawLeaf d hb hinside vout ∘ S2.symm) P2,
      letI : Fact (0 < P2) := ⟨hP2⟩
      ∃ D2 : PositiveExitActualFermiData G e.target
        (positiveExitRawLeaf d hb hinside vout ∘ S2.symm) hp2 (ηChosen/2) ξ σout ρMax2,
      ∃ B2 : PositiveExitActualCartesianPatch G e.target (C ∪ A1)
        (positiveExitRawLeaf d hb hinside vout ∘ S2.symm) hp2 (ηChosen/2) ξ σout ρMax2 D2,
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
      Nonempty (PositiveExitPairedFermiPreserved D2 B2 Ge) ∧
      Topology.IsEmbedding (fun y : e.target => planarGradient Ge y.val) ∧
      ∃ h : OpenPartialHomeomorph e.target Coord,
        h.source = univ ∧
        h.target = range (fun y : e.target => planarGradient Ge y.val) ∧
        (h : e.target → Coord) = (fun y : e.target => planarGradient Ge y.val) ∧
        ContDiffOn ℝ ∞ (fun q => (h.symm q).val) h.target ∧
      let ζ1 := positiveExitRawLeaf d hb hinside vin ∘ S1.symm
      let ζ2 := positiveExitRawLeaf d hb hinside vout ∘ S2.symm
      let v1 := exitPositiveGraphProfile P1 (fermiSupportSeamSlope (normalLoopCurvature ζ1)
        (fermiPerturbedSupport B1.epsilon (normalLoopCurvature ζ1) (positiveExitFermiHeight G ζ1)
          (fermiExitCutoff D1.rho D1.rho_pos)))
      let v2 := exitPositiveGraphProfile P2 (fermiSupportSeamSlope (normalLoopCurvature ζ2)
        (fermiPerturbedSupport B2.epsilon (normalLoopCurvature ζ2) (positiveExitFermiHeight G ζ2)
          (fermiExitCutoff D2.rho D2.rho_pos)))
      (S1 : ℝ → ℝ) = rawPrimitive (positiveExitLeafSpeed d hb hinside vin) ∧
      P1 = rawPrimitive (positiveExitLeafSpeed d hb hinside vin) T ∧
      (S2 : ℝ → ℝ) = rawPrimitive (positiveExitLeafSpeed d hb hinside vout) ∧
      P2 = rawPrimitive (positiveExitLeafSpeed d hb hinside vout) T ∧
      (∀ p ∈ C,
        1 / (ruledRho d.τ 0 * (vout : ℝ)) - ruledOmega d.k d.τ 0 <
          positiveExitCartesianLabel d hb e p ∧
        positiveExitCartesianLabel d hb e p <
          1 / (ruledRho d.τ 0 * (vin : ℝ)) - ruledOmega d.k d.τ 0) ∧
      ∀ νGeom > 0, ∃ δ1 δ2 : ℝ, ∃ t1 : PositiveExitTrace Ge e.target P1,
      ∃ t2 : PositiveExitTrace Ge e.target P2,
        0 < |δ1| ∧ |δ1| < νGeom ∧ 0 < δ1 * B1.epsilon ∧
        0 < |δ2| ∧ |δ2| < νGeom ∧ 0 < δ2 * B2.epsilon ∧
        (∀ s, t1.p s = positiveExitFermiSource ζ1 (exitGraphCurve v1 δ1 s)) ∧
        (∀ s, t2.p s = positiveExitFermiSource ζ2 (exitGraphCurve v2 δ2 s)) ∧
        (∀ s ∈ Icc (0 : ℝ) P1, |δ1 * v1 s| < D1.rho) ∧
        (∀ s ∈ Icc (0 : ℝ) P2, |δ2 * v2 s| < D2.rho) ∧
        (∀ j ≤ 1, ∀ s ∈ Icc (0 : ℝ) P1,
          ‖iteratedFDeriv ℝ j (fun r => fermiNormalMap ζ1 (exitGraphCurve v1 δ1 r)) s -
            iteratedFDeriv ℝ j ζ1 s‖ < νGeom) ∧
        (∀ j ≤ 1, ∀ s ∈ Icc (0 : ℝ) P2,
          ‖iteratedFDeriv ℝ j (fun r => fermiNormalMap ζ2 (exitGraphCurve v2 δ2 r)) s -
            iteratedFDeriv ℝ j ζ2 s‖ < νGeom) ∧
        ComplexVisiblePair (1/4) (positiveExitComplexTrace t1.p)
          (fun s => Complex.I * positiveExitComplexTrace t1.gamma s) ∧
        ComplexVisiblePair (4/5) (corrugatedReverseReflect (positiveExitComplexTrace t1.gamma))
          (fun s => Complex.I * corrugatedReverseReflect (positiveExitComplexTrace t1.p) s) ∧
        ComplexVisiblePair (1/4) (positiveExitComplexTrace t2.p)
          (fun s => Complex.I * positiveExitComplexTrace t2.gamma s) ∧
        ComplexVisiblePair (4/5) (corrugatedReverseReflect (positiveExitComplexTrace t2.gamma))
          (fun s => Complex.I * corrugatedReverseReflect (positiveExitComplexTrace t2.p) s) ∧
        (S1 : ℝ → ℝ) = rawPrimitive (positiveExitLeafSpeed d hb hinside vin) ∧
        P1 = rawPrimitive (positiveExitLeafSpeed d hb hinside vin) T ∧
        (S2 : ℝ → ℝ) = rawPrimitive (positiveExitLeafSpeed d hb hinside vout) ∧
        P2 = rawPrimitive (positiveExitLeafSpeed d hb hinside vout) T ∧
        (∀ p ∈ C,
          1 / (ruledRho d.τ 0 * (vout : ℝ)) - ruledOmega d.k d.τ 0 <
            positiveExitCartesianLabel d hb e p ∧
          positiveExitCartesianLabel d hb e p <
            1 / (ruledRho d.τ 0 * (vin : ℝ)) - ruledOmega d.k d.τ 0) := by
  obtain ⟨vin,vout,horder,hlabels,hin,hout,hboth,_hsin,_hsout,_hsboth⟩ :=
    positiveExit_exists_two_protected_complete_leaves d hb e hinside heS heF heI hδ hC hne hprotect
  have hsourceRaw (v : Ioo (0 : ℝ) δ) (s : ℝ) :
      gnomonicInverse (positiveExitRawLeaf d hb hinside v s) ∈ e.target := by
    have hh : gnomonicInverse (positiveExitRawLeaf d hb hinside v s) =
        e (positiveExitLeaf d hb hinside v (periodProjection T s)) :=
      positiveExitGaussLeaf_cartesian_source d hb e hinside heF v (periodProjection T s)
    rw [hh]
    apply e.mapsTo
    rw [heS]
    exact mem_univ _
  obtain ⟨hpn1,hgn1,hpt1,hgt1,hvo1,hvi1⟩ := hmargin vin
  obtain ⟨S1,P1,hP1,hS1,hLength1,hSs1,hshift1,hpBase1,hζ1,hiζ1,
    hunit1,hspeed1,hnorth1,hsource1,hpnz1,hgnz1,hpturn1,hgturn1,houter1,hinner1⟩ :=
    positiveExit_selected_leaf_exists_visible_turn_unitSpeed d hb hinside vin hNi hbandNorth
      e.open_target hG (hsourceRaw vin) hpn1 hgn1 hpt1 hgt1 hvo1 hvi1
  obtain ⟨hpn2,hgn2,hpt2,hgt2,hvo2,hvi2⟩ := hmargin vout
  obtain ⟨S2,P2,hP2,hS2,hLength2,hSs2,hshift2,hpBase2,hζ2,hiζ2,
    hunit2,hspeed2,hnorth2,hsource2,hpnz2,hgnz2,hpturn2,hgturn2,houter2,hinner2⟩ :=
    positiveExit_selected_leaf_exists_visible_turn_unitSpeed d hb hinside vout hNi hbandNorth
      e.open_target hG (hsourceRaw vout) hpn2 hgn2 hpt2 hgt2 hvo2 hvi2
  obtain ⟨η1,hη1,ν1,hν1,hthreshold1⟩ := positiveExit_selected_graph_trace_threshold hP1
    (by norm_num : (0:ℝ)≤1/4) (by norm_num : (0:ℝ)≤4/5)
    e.open_target hG hζ1 hpBase1 hnorth1 hsource1 hpnz1 hgnz1 hpturn1 hgturn1 houter1 hinner1
  obtain ⟨η2,hη2,ν2,hν2,hthreshold2⟩ := positiveExit_selected_graph_trace_threshold hP2
    (by norm_num : (0:ℝ)≤1/4) (by norm_num : (0:ℝ)≤4/5)
    e.open_target hG hζ2 hpBase2 hnorth2 hsource2 hpnz2 hgnz2 hpturn2 hgturn2 houter2 hinner2
  let ηChosen := min η (min η1 η2)
  have hηChosen : 0 < ηChosen := lt_min hηBudget (lt_min hη1 hη2)
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
  obtain ⟨Snew1,Pnew1,hPnew1,ρMax1,_hρ1,hp1,D1,B1,_hsmall1,hEmbedding1,_hcutoff1,_hbend1,hSnew1,hLengthnew1⟩ :=
    positiveExit_selected_leaf_actual_embedded_cartesian_patch d hb hinside vin hNi hbandNorth horient hτ
      e heS heF heD heI G hG hrec hdet (C ∪ Lout) (hC.union hLout) havoid1
      Y hbend hsupport1 G hG hemb (fun y hy => (hdet y hy).ne)
      (half_pos hηChosen) hξ hσin hξ
  have hSeq1 : Snew1 = S1 := by
    ext s
    exact congrFun (hSnew1.trans hS1.symm) s
  have hPeq1 : Pnew1 = P1 := hLengthnew1.trans hLength1.symm
  clear hLengthnew1
  subst Snew1
  subst Pnew1
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
  let H1 : Coord → ℝ := fun z => G z + B1.change z
  have hH1 : ContDiffOn ℝ ∞ H1 e.target := hG.add B1.change_smooth.contDiffOn
  have hEmbeddingH1 : Topology.IsEmbedding
      (fun y : e.target => planarGradient H1 y.val) := by
    simpa only [H1] using hEmbedding1
  have hdetH1 : ∀ y ∈ e.target, (planarHessian H1 y).det ≠ 0 :=
    fun y hy => (B1.whole_saddle y hy).ne
  obtain ⟨Snew2,Pnew2,hPnew2,ρMax2,_hρ2,hp2,D2,B2,_hsmall2,hEmbedding2,_hcutoff2,_hbend2,hSnew2,hLengthnew2⟩ :=
    positiveExit_selected_leaf_actual_embedded_cartesian_patch d hb hinside vout hNi hbandNorth horient hτ
      e heS heF heD heI G hG hrec hdet (C ∪ A1) (hC.union hA1) havoid2
      Y hbend hsupport2 H1 hH1 hEmbeddingH1 hdetH1 (half_pos hηChosen) hξ hσout hξ
  have hSeq2 : Snew2 = S2 := by
    ext s
    exact congrFun (hSnew2.trans hS2.symm) s
  have hPeq2 : Pnew2 = P2 := hLengthnew2.trans hLength2.symm
  clear hLengthnew2
  subst Snew2
  subst Pnew2
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
  have hC2 (z : Coord) : fermiCoordinateC2Size (fun q => B1.change q + B2.change q) z < ηChosen :=
    (positiveExit_pair_C2_triangle B1.change_smooth B2.change_smooth z).trans_lt
      (by linarith [B1.change_C2 z,B2.change_C2 z])
  have hpres1 := positiveExit_pair_preserves_actual_fermi D1 B1 hGe hgerm1
  have hpres2 := positiveExit_pair_preserves_actual_fermi D2 B2 hGe
    (fun z hz => hgerm2 z (fun hz1 => disjoint_left.mp hdis hz1 hz))
  have hEmbedded : Topology.IsEmbedding (fun y : e.target => planarGradient Ge y.val) :=
    hEmbedding2
  have hneU : e.target.Nonempty := by
    refine ⟨e (positiveExitLeaf d hb hinside vin (periodProjection T 0)), ?_⟩
    apply e.mapsTo
    rw [heS]
    exact mem_univ _
  have hactual : (fun z => G z + (1 : ℝ) * (B1.change z + B2.change z)) = Ge := by
    funext z
    change G z + (1 : ℝ) * (B1.change z + B2.change z) =
      G z + B1.change z + B2.change z
    ring
  have hdetActual : ∀ y ∈ e.target,
      (planarHessian (fun z => G z + (1 : ℝ) * (B1.change z + B2.change z)) y).det ≠ 0 := by
    rw [hactual]
    exact fun y hy => (hwhole y hy).ne
  have hEmbeddedActual : Topology.IsEmbedding (fun y : e.target =>
      planarGradient (fun z => G z + (1 : ℝ) * (B1.change z + B2.change z)) y.val) := by
    rw [hactual]
    exact hEmbedded
  obtain ⟨h,hhS,hhT,hhF,hhI⟩ := positiveExit_actual_gradient_global_inverse
    e.open_target hneU hG (B1.change_smooth.add B2.change_smooth) 1 hdetActual hEmbeddedActual
  rw [hactual] at hhT hhF
  let J : Coord → ℝ := fun z => B1.change z + B2.change z
  have hJ : ContDiff ℝ ∞ J := B1.change_smooth.add B2.change_smooth
  have heqGe : (fun z => G z + J z) = Ge := by
    funext z
    change G z + (B1.change z + B2.change z) = G z + B1.change z + B2.change z
    ring
  refine ⟨ηChosen,hηChosen,min_le_left _ _,vin,vout,horder,S1,P1,hP1,ρMax1,hp1,D1,B1,
    S2,P2,hP2,ρMax2,hp2,D2,B2,hdis,hGe,B1.change_smooth.add B2.change_smooth,
    B1.change_compact.add B2.change_compact,(fun z => (hC2 z).trans_le (min_le_left _ _)),
    hprotectedOpen,hprotected,hprotectedEq,hprotectedGerm,hBending,hwhole,hpres1,hpres2,hEmbedded,
    h,hhS,hhT,hhF,hhI,hS1,hLength1,hS2,hLength2,hlabels,?_⟩
  dsimp only
  intro νGeom hνGeom
  let ζ1 := positiveExitRawLeaf d hb hinside vin ∘ S1.symm
  let v1 := exitPositiveGraphProfile P1 (fermiSupportSeamSlope (normalLoopCurvature ζ1)
    (fermiPerturbedSupport B1.epsilon (normalLoopCurvature ζ1) (positiveExitFermiHeight G ζ1)
      (fermiExitCutoff D1.rho D1.rho_pos)))
  obtain ⟨HP1⟩ := hpres1
  obtain ⟨δ1,Cs1,tr1,hδ1,hδν1,hδside1,htr1,_,hCF1,_,hstrip1,hjetsRaw1⟩ :=
    positiveExit_paired_graph_exists_regular_trace_with_strip D1 B1 HP1 e.open_target hGe hEmbedded 1 (lt_min hν1 hνGeom)
  have hjets1 : ∀ j ≤ 1, ∀ s ∈ Icc (0 : ℝ) P1,
      ‖iteratedFDeriv ℝ j (fun r => fermiNormalMap ζ1 (exitGraphCurve v1 δ1 r)) s -
        iteratedFDeriv ℝ j ζ1 s‖ < ν1 :=
    fun j hj s hs => (hjetsRaw1 j hj s hs).trans_le (min_le_left _ _)
  have hjetsGeom1 : ∀ j ≤ 1, ∀ s ∈ Icc (0 : ℝ) P1,
      ‖iteratedFDeriv ℝ j (fun r => fermiNormalMap ζ1 (exitGraphCurve v1 δ1 r)) s -
        iteratedFDeriv ℝ j ζ1 s‖ < νGeom :=
    fun j hj s hs => (hjetsRaw1 j hj s hs).trans_le (min_le_right _ _)
  have hv1 : ContDiff ℝ ∞ v1 := fermiPerturbedSupport_profile_contDiff
    (normalLoop_actual_smooth D1.zeta_smooth).2 (fermiExitCutoff_contDiff D1.rho D1.rho_pos)
    (fermiExitCutoff_zero D1.rho D1.rho_pos) D1.W_open D1.height_smooth
    D1.scale_nonzero D1.seam_in_W D1.actual_mixed_positive B1.epsilon P1
  let c1 : ℝ → Ambient := fermiNormalMap ζ1 ∘ exitGraphCurve v1 δ1
  have hc1 : ContDiff ℝ ∞ c1 :=
    (fermiNormalMap_contDiff D1.zeta_smooth).comp (exitGraphCurve_contDiff hv1 δ1)
  have hcP1 : Function.Periodic c1 P1 := by
    intro s
    change fermiNormalMap ζ1 (exitGraphCurve v1 δ1 (s + P1)) =
      fermiNormalMap ζ1 (exitGraphCurve v1 δ1 s)
    rw [← hCF1 (s + P1), ← hCF1 s]
    exact congrArg (fun q => (Cs1 q : Ambient)) (AddCircle.coe_add_period P1 s)
  have hbudget1 : ∀ z ∈ e.target, fermiCoordinateC2Size J z < η1 := by
    intro z _
    exact (hC2 z).trans_le ((min_le_right η (min η1 η2)).trans
      (min_le_left η1 η2))
  have hh1 := hthreshold1 J c1 hJ hc1 hcP1 hbudget1 hjets1
  rw [heqGe] at hh1
  obtain ⟨t1,htp1,htg1,hvisibleOuter1,hvisibleInner1⟩ :=
    hh1 tr1 htr1
  have hpgraph1 (s : ℝ) : t1.p s = positiveExitFermiSource ζ1 (exitGraphCurve v1 δ1 s) := by
    rw [htp1]
    exact htr1 s
  let ζ2 := positiveExitRawLeaf d hb hinside vout ∘ S2.symm
  let v2 := exitPositiveGraphProfile P2 (fermiSupportSeamSlope (normalLoopCurvature ζ2)
    (fermiPerturbedSupport B2.epsilon (normalLoopCurvature ζ2) (positiveExitFermiHeight G ζ2)
      (fermiExitCutoff D2.rho D2.rho_pos)))
  obtain ⟨HP2⟩ := hpres2
  obtain ⟨δ2,Cs2,tr2,hδ2,hδν2,hδside2,htr2,_,hCF2,_,hstrip2,hjetsRaw2⟩ :=
    positiveExit_paired_graph_exists_regular_trace_with_strip D2 B2 HP2 e.open_target hGe hEmbedded 1 (lt_min hν2 hνGeom)
  have hjets2 : ∀ j ≤ 1, ∀ s ∈ Icc (0 : ℝ) P2,
      ‖iteratedFDeriv ℝ j (fun r => fermiNormalMap ζ2 (exitGraphCurve v2 δ2 r)) s -
        iteratedFDeriv ℝ j ζ2 s‖ < ν2 :=
    fun j hj s hs => (hjetsRaw2 j hj s hs).trans_le (min_le_left _ _)
  have hjetsGeom2 : ∀ j ≤ 1, ∀ s ∈ Icc (0 : ℝ) P2,
      ‖iteratedFDeriv ℝ j (fun r => fermiNormalMap ζ2 (exitGraphCurve v2 δ2 r)) s -
        iteratedFDeriv ℝ j ζ2 s‖ < νGeom :=
    fun j hj s hs => (hjetsRaw2 j hj s hs).trans_le (min_le_right _ _)
  have hv2 : ContDiff ℝ ∞ v2 := fermiPerturbedSupport_profile_contDiff
    (normalLoop_actual_smooth D2.zeta_smooth).2 (fermiExitCutoff_contDiff D2.rho D2.rho_pos)
    (fermiExitCutoff_zero D2.rho D2.rho_pos) D2.W_open D2.height_smooth
    D2.scale_nonzero D2.seam_in_W D2.actual_mixed_positive B2.epsilon P2
  let c2 : ℝ → Ambient := fermiNormalMap ζ2 ∘ exitGraphCurve v2 δ2
  have hc2 : ContDiff ℝ ∞ c2 :=
    (fermiNormalMap_contDiff D2.zeta_smooth).comp (exitGraphCurve_contDiff hv2 δ2)
  have hcP2 : Function.Periodic c2 P2 := by
    intro s
    change fermiNormalMap ζ2 (exitGraphCurve v2 δ2 (s + P2)) =
      fermiNormalMap ζ2 (exitGraphCurve v2 δ2 s)
    rw [← hCF2 (s + P2), ← hCF2 s]
    exact congrArg (fun q => (Cs2 q : Ambient)) (AddCircle.coe_add_period P2 s)
  have hbudget2 : ∀ z ∈ e.target, fermiCoordinateC2Size J z < η2 := by
    intro z _
    exact (hC2 z).trans_le ((min_le_right η (min η1 η2)).trans
      (min_le_right η1 η2))
  have hh2 := hthreshold2 J c2 hJ hc2 hcP2 hbudget2 hjets2
  rw [heqGe] at hh2
  obtain ⟨t2,htp2,htg2,hvisibleOuter2,hvisibleInner2⟩ :=
    hh2 tr2 htr2
  have hpgraph2 (s : ℝ) : t2.p s = positiveExitFermiSource ζ2 (exitGraphCurve v2 δ2 s) := by
    rw [htp2]
    exact htr2 s
  exact ⟨δ1,δ2,t1,t2,hδ1,hδν1.trans_le (min_le_right _ _),hδside1,
    hδ2,hδν2.trans_le (min_le_right _ _),hδside2,hpgraph1,hpgraph2,hstrip1,hstrip2,
    hjetsGeom1,hjetsGeom2,hvisibleOuter1,hvisibleInner1,hvisibleOuter2,hvisibleInner2,
    hS1,hLength1,hS2,hLength2,hlabels⟩


end
end TightVer401



