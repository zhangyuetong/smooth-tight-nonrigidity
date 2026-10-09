import TightVer401.PositiveExitConstructionAmbientJetDualVisibility
import TightVer401.PositiveExitConstructionAmbientTurnStability
import TightVer401.PositiveExitConstructionWindingBridge

/-! Select both visibility and origin-turn margins before the actual patch and
positive graph. The same actual paired Fermi graph produces a full actual
trace. No source or gradient nesting is asserted here. -/
namespace TightVer401
noncomputable section
open Set Function Filter Metric OAI.SmoothLocal.Geometry
open OAI.CircleDomainRigidity OAI.CircleDomainRigidity.FiniteTransfer
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

private theorem selectedGraph_complex_eq :
    positiveExitComplexPoint = angularDescentComplex := by
  funext q
  apply Complex.ext <;> simp [positiveExitComplexPoint, angularDescentComplex]

private theorem selectedGraph_complex_injective : Injective positiveExitComplexPoint := by
  intro q r he
  have h0 := congrArg Complex.re he
  have h1 := congrArg Complex.im he
  ext i
  fin_cases i
  · exact h0
  · exact h1

/-- The retained actual filling and positive origin turn place the origin in
the bounded complementary component used by the actual exit contract. -/
theorem positiveExit_actual_turn_encloses_origin {P : ℝ} (hP : 0 < P)
    {p : ℝ → Coord} (hs : ContDiff ℝ ∞ p) (hp : Periodic p P)
    (hi : Injective hp.lift) (hnz : ∀ s, p s ≠ 0)
    (hturn : HasPositiveArgumentTurn (positiveExitComplexTrace p) P) :
    (0 : Coord) ∈ positiveExitInside p := by
  letI : Fact (0 < P) := ⟨hP⟩
  let γ := positiveExitComplexTrace p
  have hγ : ContDiff ℝ ∞ γ := by
    simpa only [γ, positiveExitComplexTrace, selectedGraph_complex_eq] using
      angularDescentComplex_contDiff.comp hs
  have hγP : Periodic γ P := fun s => congrArg positiveExitComplexPoint (hp s)
  have hγi : InjOn γ (Ico 0 P) := by
    intro s hs' t ht' he
    have hq : (s : AddCircle P) = (t : AddCircle P) := by
      apply hi
      simpa only [hp.lift_coe] using selectedGraph_complex_injective he
    exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := P) (a := (0 : ℝ))
      (by simpa only [zero_add] using hs') (by simpa only [zero_add] using ht')).mp hq
  have hγnz (s) : γ s ≠ 0 := by
    intro he
    apply hnz s
    apply selectedGraph_complex_injective
    exact he.trans (by rfl : (0 : ℂ) = positiveExitComplexPoint (0 : Coord))
  obtain ⟨H, hfill⟩ := periodicComplexCurve_exists_filling hγ hγP hγi
  have hclosed : γ P = γ 0 := by simpa only [zero_add] using hγP 0
  obtain ⟨φ, hφ, hproj, hinc⟩ := hturn
  have hφne : φ P ≠ φ 0 := by
    intro he
    rw [he, sub_self] at hinc
    exact Real.two_pi_pos.ne' hinc.symm
  have h0 : (0 : ℂ) ∈ jordanInterior H :=
    winding_origin_inside complexCircleDirection_continuousOn hγ.continuous hφ
      hfill hγnz hclosed hproj hφne
  let D : Set Schoenflies.Plane := jordanComplexCoordinates.symm '' jordanInterior H
  let x : Schoenflies.Plane := jordanComplexCoordinates.symm (0 : ℂ)
  have hD : IsOpen D := jordanComplexCoordinates.symm.isOpenMap _ (jordanInterior_isOpen H)
  have hx : x ∈ D := ⟨0, h0, rfl⟩
  have hfront : frontier D = positiveExitJordanRange p := by
    have he := (jordanComplexCoordinates.symm.toHomeomorph.image_frontier
      (jordanInterior H)).symm
    change frontier (jordanComplexCoordinates.symm '' jordanInterior H) =
      jordanComplexCoordinates.symm '' frontier (jordanInterior H) at he
    dsimp only [D]
    rw [he, frontier_jordanInterior, ← hfill]
    ext z
    constructor
    · rintro ⟨y, ⟨s, rfl⟩, rfl⟩
      exact ⟨s, rfl⟩
    · rintro ⟨s, rfl⟩
      exact ⟨γ s, ⟨s, rfl⟩, rfl⟩
  have hxnot : x ∉ positiveExitJordanRange p := by
    rw [← hfront, frontier, hD.interior_eq]
    exact fun h => h.2 hx
  let K := connectedComponentIn (positiveExitJordanRange p)ᶜ x
  have hK : IsPreconnected K := isPreconnected_connectedComponentIn
  have hKx : x ∈ K := mem_connectedComponentIn hxnot
  have hdisj : Disjoint K (frontier D) := by
    rw [hfront]
    exact disjoint_left.mpr (fun z hz hc => connectedComponentIn_subset _ _ hz hc)
  have hside : K ⊆ D ∨ K ⊆ (closure D)ᶜ := by
    apply hK.subset_or_subset hD isClosed_closure.isOpen_compl
    · exact disjoint_left.mpr (fun z hz hz' => hz' (subset_closure hz))
    · intro z hz
      by_cases hzD : z ∈ D
      · exact Or.inl hzD
      · right
        intro hzcl
        apply disjoint_left.mp hdisj hz
        rw [frontier, hD.interior_eq]
        exact ⟨hzcl, hzD⟩
  have hKD : K ⊆ D := hside.resolve_right (fun h => h hKx (subset_closure hx))
  have hcompact : IsCompact (jordanComplexCoordinates.symm '' closure (jordanInterior H)) :=
    (isCompact_closure_jordanInterior H).image jordanComplexCoordinates.symm.continuous
  have hbounded : Bornology.IsBounded K := hcompact.isBounded.subset
    (hKD.trans (image_mono subset_closure))
  change jordanComplexCoordinates.symm (positiveExitComplexPoint (0 : Coord)) ∈
    Schoenflies.inside (positiveExitJordanRange p)
  exact ⟨hxnot, hbounded⟩

/-- Attach the two proved actual turns to the actual regular graph. All
contract fields, including bounded-side enclosure, are conclusions. -/
def positiveExit_selectedTrace_of_regular {Ge : Coord → ℝ} {U : Set Coord} {P : ℝ}
    (hP : 0 < P) (tr : PositiveExitRegularGraphTrace Ge U P)
    (hpturn : HasPositiveArgumentTurn (positiveExitComplexTrace tr.p) P)
    (hgturn : HasPositiveArgumentTurn (positiveExitComplexTrace tr.gamma) P)
    (hpnz : ∀ s, tr.p s ≠ 0) (hgnz : ∀ s, tr.gamma s ≠ 0) :
    PositiveExitTrace Ge U P where
  period_pos := hP
  p := tr.p
  gamma := tr.gamma
  p_smooth := tr.p_smooth
  gamma_smooth := tr.gamma_smooth
  p_periodic := tr.p_periodic
  gamma_periodic := tr.gamma_periodic
  p_in_domain := tr.p_in_domain
  actual_gradient := tr.actual_gradient
  source_regular := tr.source_regular
  gradient_regular := tr.gradient_regular
  source_injective := tr.source_embedding.injective
  gradient_injective := tr.gradient_embedding.injective
  source_jordan := tr.source_jordan
  gradient_jordan := tr.gradient_jordan
  source_nonzero := hpnz
  gradient_nonzero := hgnz
  source_turn := hpturn
  gradient_turn := hgturn
  source_enclosure := positiveExit_actual_turn_encloses_origin hP tr.p_smooth tr.p_periodic
    tr.source_embedding.injective hpnz hpturn
  gradient_enclosure := positiveExit_actual_turn_encloses_origin hP tr.gamma_smooth tr.gamma_periodic
    tr.gradient_embedding.injective hgnz hgturn
  tangent_pairing := tr.tangent_pairing
  value_smooth := tr.value_smooth
  value_periodic := tr.value_periodic
  value_derivative := tr.value_derivative
  zero_action := tr.zero_action

/-- One minimum margin for BOTH actual visibility predicates and BOTH origin
turns, selected before a change or graph exists. The consumer takes only
literal actual C2/first-jet bounds and an actual regular graph output. -/
theorem positiveExit_selected_graph_trace_threshold {P Rout Rin : ℝ}
    (hP : 0 < P) (hRout : 0 ≤ Rout) (hRin : 0 ≤ Rin)
    {G : Coord → ℝ} {U : Set Coord} (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U)
    {ζ : ℝ → Ambient} (hζ : ContDiff ℝ ∞ ζ) (hζP : Periodic ζ P)
    (hnorth : ∀ s, 0 < ζ s 2) (hsource : ∀ s, gnomonicInverse (ζ s) ∈ U)
    (hpnz : ∀ s, angularDescentComplex (gnomonicInverse (ζ s)) ≠ 0)
    (hgnz : ∀ s, angularDescentComplex (planarGradient G (gnomonicInverse (ζ s))) ≠ 0)
    (hpturn : HasPositiveArgumentTurn (angularDescentComplex ∘ gnomonicInverse ∘ ζ) P)
    (hgturn : HasPositiveArgumentTurn
      (angularDescentComplex ∘ planarGradient G ∘ gnomonicInverse ∘ ζ) P)
    (houter : ComplexVisiblePair Rout (angularDescentComplex ∘ gnomonicInverse ∘ ζ)
      (fun s => Complex.I * angularDescentComplex (planarGradient G (gnomonicInverse (ζ s)))))
    (hinner : ComplexVisiblePair Rin
      (corrugatedReverseReflect (angularDescentComplex ∘ planarGradient G ∘ gnomonicInverse ∘ ζ))
      (fun s => Complex.I * corrugatedReverseReflect
        (angularDescentComplex ∘ gnomonicInverse ∘ ζ) s)) :
    ∃ η > 0, ∃ ν > 0, ∀ (J : Coord → ℝ) (c : ℝ → Ambient),
      ContDiff ℝ ∞ J → ContDiff ℝ ∞ c → Periodic c P →
      (∀ q ∈ U, fermiCoordinateC2Size J q < η) →
      (∀ j ≤ 1, ∀ s ∈ Icc (0 : ℝ) P,
        ‖iteratedFDeriv ℝ j c s - iteratedFDeriv ℝ j ζ s‖ < ν) →
      ∀ tr : PositiveExitRegularGraphTrace (fun q => G q + J q) U P,
      (∀ s, tr.p s = gnomonicInverse (c s)) →
      ∃ t : PositiveExitTrace (fun q => G q + J q) U P,
        t.p = tr.p ∧ t.gamma = tr.gamma ∧
        ComplexVisiblePair Rout (positiveExitComplexTrace t.p)
          (fun s => Complex.I * positiveExitComplexTrace t.gamma s) ∧
        ComplexVisiblePair Rin (corrugatedReverseReflect (positiveExitComplexTrace t.gamma))
          (fun s => Complex.I * corrugatedReverseReflect (positiveExitComplexTrace t.p) s) := by
  obtain ⟨ηo, hηo, νo, hνo, ho⟩ := positiveExit_exists_graph_trace_visibility_threshold
    hRout hP hU hG hζ hnorth hsource houter
  obtain ⟨ηi, hηi, νi, hνi, hi⟩ := positiveExit_exists_graph_trace_dual_visibility_threshold
    hRin hP hU hG hζ hnorth hsource hinner
  obtain ⟨ηt, hηt, νt, hνt, ht⟩ := positiveExit_exists_ambient_value_argumentTurn_threshold
    hP hU hG hζ hζP hnorth hsource hpnz hgnz hpturn hgturn
  let η := min ηo (min ηi ηt)
  let ν := min νo (min νi νt)
  refine ⟨η, lt_min hηo (lt_min hηi hηt), ν, lt_min hνo (lt_min hνi hνt), ?_⟩
  intro J c hJ hc hcP hbudget hjets tr hpactual
  have hbo : ∀ q ∈ U, fermiCoordinateC2Size J q < ηo :=
    fun q hq => (hbudget q hq).trans_le (min_le_left _ _)
  have hbi : ∀ q ∈ U, fermiCoordinateC2Size J q < ηi :=
    fun q hq => (hbudget q hq).trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hbt : ∀ q ∈ U, fermiCoordinateC2Size J q < ηt :=
    fun q hq => (hbudget q hq).trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hjo : ∀ j ≤ 1, ∀ s ∈ Icc (0 : ℝ) P,
      ‖iteratedFDeriv ℝ j c s - iteratedFDeriv ℝ j ζ s‖ < νo :=
    fun j hj s hs => (hjets j hj s hs).trans_le (min_le_left _ _)
  have hji : ∀ j ≤ 1, ∀ s ∈ Icc (0 : ℝ) P,
      ‖iteratedFDeriv ℝ j c s - iteratedFDeriv ℝ j ζ s‖ < νi :=
    fun j hj s hs => (hjets j hj s hs).trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hfirst := positiveExit_firstJet_close_of_iteratedFDeriv hjets
  have hval : ∀ s ∈ Icc (0 : ℝ) P, ‖c s - ζ s‖ < νt :=
    fun s hs => (hfirst s hs).1.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨_, _, _, _, _, hpt, hgt, hpn, hgn⟩ := ht J c hJ hc hcP hbt hval
  have heq : tr.p = gnomonicInverse ∘ c := funext hpactual
  have hpt' : HasPositiveArgumentTurn (positiveExitComplexTrace tr.p) P := by
    rw [positiveExitComplexTrace, selectedGraph_complex_eq, heq]
    exact hpt
  have hgt' : HasPositiveArgumentTurn (positiveExitComplexTrace tr.gamma) P := by
    rw [positiveExitComplexTrace, selectedGraph_complex_eq, tr.actual_gradient, heq]
    exact hgt
  have hpn' : ∀ s, tr.p s ≠ 0 := by simpa only [heq, comp_apply] using hpn
  have hgn' : ∀ s, tr.gamma s ≠ 0 := by
    simpa only [tr.actual_gradient, heq, comp_apply] using hgn
  refine ⟨positiveExit_selectedTrace_of_regular hP tr hpt' hgt' hpn' hgn', rfl, rfl, ?_, ?_⟩
  · exact ho J c hJ hc hcP hbo hjo tr hpactual
  · exact hi J c hJ hc hcP hbi hji tr hpactual

/-- Actual selected positive graphs. All margins precede the actual Fermi
data, patch amplitude and graph. The inputs D/B/H are the already constructed
ordinary Fermi and Cartesian outputs, and the change bound is literal. -/
theorem positiveExit_paired_graph_exists_selected_trace {P Rout Rin : ℝ} [Fact (0 < P)]
    (hRout : 0 ≤ Rout) (hRin : 0 ≤ Rin)
    {G : Coord → ℝ} {U : Set Coord} (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U)
    {ζ : ℝ → Ambient} (hζ : ContDiff ℝ ∞ ζ) (hp : Periodic ζ P)
    (hnorth : ∀ s, 0 < ζ s 2) (hsource : ∀ s, gnomonicInverse (ζ s) ∈ U)
    (hpnz : ∀ s, angularDescentComplex (gnomonicInverse (ζ s)) ≠ 0)
    (hgnz : ∀ s, angularDescentComplex (planarGradient G (gnomonicInverse (ζ s))) ≠ 0)
    (hpturn : HasPositiveArgumentTurn (angularDescentComplex ∘ gnomonicInverse ∘ ζ) P)
    (hgturn : HasPositiveArgumentTurn
      (angularDescentComplex ∘ planarGradient G ∘ gnomonicInverse ∘ ζ) P)
    (houter : ComplexVisiblePair Rout (angularDescentComplex ∘ gnomonicInverse ∘ ζ)
      (fun s => Complex.I * angularDescentComplex (planarGradient G (gnomonicInverse (ζ s)))))
    (hinner : ComplexVisiblePair Rin
      (corrugatedReverseReflect (angularDescentComplex ∘ planarGradient G ∘ gnomonicInverse ∘ ζ))
      (fun s => Complex.I * corrugatedReverseReflect
        (angularDescentComplex ∘ gnomonicInverse ∘ ζ) s)) :
    ∃ η > 0, ∃ ν > 0, ∀ (ξ σ ρMax : ℝ) (C : Set Coord)
      (D : PositiveExitActualFermiData G U ζ hp η ξ σ ρMax)
      (B : PositiveExitActualCartesianPatch G U C ζ hp η ξ σ ρMax D)
      (J : Coord → ℝ),
      ContDiff ℝ ∞ J → (∀ q ∈ U, fermiCoordinateC2Size J q < η) →
      PositiveExitPairedFermiPreserved D B (fun q => G q + J q) →
      Topology.IsEmbedding (fun y : U => planarGradient (fun q => G q + J q) y.val) →
      let v := exitPositiveGraphProfile P (fermiSupportSeamSlope (normalLoopCurvature ζ)
        (fermiPerturbedSupport B.epsilon (normalLoopCurvature ζ) (positiveExitFermiHeight G ζ)
          (fermiExitCutoff D.rho D.rho_pos)))
      ∃ (δ : ℝ) (Cs : AddCircle P → RoundSphere)
        (t : PositiveExitTrace (fun q => G q + J q) U P),
        0 < |δ| ∧ |δ| < ν ∧ 0 < δ * B.epsilon ∧
        (∀ s, t.p s = positiveExitFermiSource ζ (exitGraphCurve v δ s)) ∧
        Topology.IsEmbedding Cs ∧
        (∀ s, (Cs (periodProjection P s) : Ambient) = fermiNormalMap ζ (exitGraphCurve v δ s)) ∧
        (∀ s ∈ Icc (0 : ℝ) P, |δ * v s| < D.rho) ∧
        (∀ j ≤ 1, ∀ s ∈ Icc (0 : ℝ) P,
          ‖iteratedFDeriv ℝ j (fun r => fermiNormalMap ζ (exitGraphCurve v δ r)) s -
            iteratedFDeriv ℝ j ζ s‖ < ν) ∧
        ComplexVisiblePair Rout (positiveExitComplexTrace t.p)
          (fun s => Complex.I * positiveExitComplexTrace t.gamma s) ∧
        ComplexVisiblePair Rin (corrugatedReverseReflect (positiveExitComplexTrace t.gamma))
          (fun s => Complex.I * corrugatedReverseReflect (positiveExitComplexTrace t.p) s) := by
  obtain ⟨η, hη, ν, hν, hthreshold⟩ := positiveExit_selected_graph_trace_threshold
    (Fact.out : 0 < P) hRout hRin hU hG hζ hp hnorth hsource hpnz hgnz
    hpturn hgturn houter hinner
  refine ⟨η, hη, ν, hν, ?_⟩
  intro ξ σ ρMax C D B J hJ hbudget H hemb
  dsimp only
  let v := exitPositiveGraphProfile P (fermiSupportSeamSlope (normalLoopCurvature ζ)
    (fermiPerturbedSupport B.epsilon (normalLoopCurvature ζ) (positiveExitFermiHeight G ζ)
      (fermiExitCutoff D.rho D.rho_pos)))
  have hv : ContDiff ℝ ∞ v := fermiPerturbedSupport_profile_contDiff
    (normalLoop_actual_smooth hζ).2 (fermiExitCutoff_contDiff D.rho D.rho_pos)
    (fermiExitCutoff_zero D.rho D.rho_pos) D.W_open D.height_smooth
    D.scale_nonzero D.seam_in_W D.actual_mixed_positive B.epsilon P
  obtain ⟨δ, Cs, tr, hδ, hδν, hδε, htr, hCs, hCF, _, hstrip, hjets⟩ :=
    positiveExit_paired_graph_exists_regular_trace_with_strip D B H hU (hG.add hJ.contDiffOn) hemb 1 hν
  let c : ℝ → Ambient := fermiNormalMap ζ ∘ exitGraphCurve v δ
  have hc : ContDiff ℝ ∞ c := (fermiNormalMap_contDiff hζ).comp (exitGraphCurve_contDiff hv δ)
  have hcP : Periodic c P := by
    intro s
    change fermiNormalMap ζ (exitGraphCurve v δ (s + P)) =
      fermiNormalMap ζ (exitGraphCurve v δ s)
    rw [← hCF (s + P), ← hCF s]
    exact congrArg (fun q => (Cs q : Ambient)) (AddCircle.coe_add_period P s)
  have hpactual : ∀ s, tr.p s = gnomonicInverse (c s) := htr
  obtain ⟨t, htp, htg, hvo, hvi⟩ := hthreshold J c hJ hc hcP hbudget hjets tr hpactual
  refine ⟨δ, Cs, t, hδ, hδν, hδε, ?_, hCs, hCF, hstrip, hjets, hvo, hvi⟩
  intro s
  rw [htp]
  exact htr s

end
end TightVer401
