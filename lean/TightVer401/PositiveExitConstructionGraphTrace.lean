import TightVer401.PositiveExitConstructionTwoPatches
import TightVer401.PositiveExitConstructionContract
import TightVer401.PeriodicComplexJordan
import TightVer401.FermiExitSmoothConvergence

/-! Actual regular source and gradient Jordan traces of a paired positive
graph. Origin turns, nested interiors and visibility remain separate geometric
applications; this output grants none of them. -/
open scoped Manifold
namespace TightVer401
noncomputable section
open Set Filter MeasureTheory OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

/-- The regular, actual-gradient portion of an exit trace, constructed from
the paired positive graph. This deliberately omits origin and nesting data. -/
structure PositiveExitRegularGraphTrace (Ge : Coord → ℝ) (U : Set Coord) (P : ℝ) where
  p : ℝ → Coord
  gamma : ℝ → Coord
  p_smooth : ContDiff ℝ ∞ p
  gamma_smooth : ContDiff ℝ ∞ gamma
  p_periodic : Function.Periodic p P
  gamma_periodic : Function.Periodic gamma P
  p_in_domain : MapsTo p univ U
  actual_gradient : gamma = planarGradient Ge ∘ p
  source_embedding : Topology.IsEmbedding p_periodic.lift
  gradient_embedding : Topology.IsEmbedding gamma_periodic.lift
  source_regular : ∀ s, deriv p s ≠ 0
  gradient_regular : ∀ s, deriv gamma s ≠ 0
  source_jordan : Schoenflies.IsJordanCurve (positiveExitJordanRange p)
  gradient_jordan : Schoenflies.IsJordanCurve (positiveExitJordanRange gamma)
  tangent_pairing : ∀ s, 0 < deriv p s ⬝ᵥ deriv gamma s
  value_smooth : ContDiff ℝ ∞ (Ge ∘ p)
  value_periodic : Function.Periodic (Ge ∘ p) P
  value_derivative : ∀ s, deriv (Ge ∘ p) s = gamma s ⬝ᵥ deriv p s
  zero_action : (∫ s in 0..P, gamma s ⬝ᵥ deriv p s) = 0

/-- Consume the actual paired graph and actual final gradient embedding.
No Jordan, immersion, tangent-pairing, action or trace witness is an input. -/
theorem positiveExit_paired_graph_exists_regular_trace_with_strip {P : ℝ} [Fact (0 < P)]
    {G Ge : Coord → ℝ} {U C : Set Coord} {ζ : ℝ → Ambient}
    {hp : Function.Periodic ζ P} {η ξ σ ρMax : ℝ}
    (D : PositiveExitActualFermiData G U ζ hp η ξ σ ρMax)
    (B : PositiveExitActualCartesianPatch G U C ζ hp η ξ σ ρMax D)
    (H : PositiveExitPairedFermiPreserved D B Ge)
    (hU : IsOpen U) (hGe : ContDiffOn ℝ ∞ Ge U)
    (hemb : Topology.IsEmbedding (fun y : U => planarGradient Ge y.val))
    (n : ℕ) {ν : ℝ} (hν : 0 < ν) :
    let v := exitPositiveGraphProfile P (fermiSupportSeamSlope (normalLoopCurvature ζ)
      (fermiPerturbedSupport B.epsilon (normalLoopCurvature ζ) (positiveExitFermiHeight G ζ)
        (fermiExitCutoff D.rho D.rho_pos)))
    ∃ (δ : ℝ) (Cs : AddCircle P → RoundSphere) (tr : PositiveExitRegularGraphTrace Ge U P),
      0 < |δ| ∧ |δ| < ν ∧ 0 < δ * B.epsilon ∧
      (∀ s, tr.p s = positiveExitFermiSource ζ (exitGraphCurve v δ s)) ∧
      Topology.IsEmbedding Cs ∧
      (∀ s, (Cs (periodProjection P s) : Ambient) =
        fermiNormalMap ζ (exitGraphCurve v δ s)) ∧
      (∀ q, ‖(Cs q : Ambient) - hp.lift q‖ < ν) ∧
      (∀ s ∈ Icc (0 : ℝ) P, |δ * v s| < D.rho) ∧
      ∀ j ≤ n, ∀ s ∈ Icc (0 : ℝ) P,
        ‖iteratedFDeriv ℝ j (fun r => fermiNormalMap ζ (exitGraphCurve v δ r)) s -
          iteratedFDeriv ℝ j ζ s‖ < ν := by
  dsimp only
  let v := exitPositiveGraphProfile P (fermiSupportSeamSlope (normalLoopCurvature ζ)
    (fermiPerturbedSupport B.epsilon (normalLoopCurvature ζ) (positiveExitFermiHeight G ζ)
      (fermiExitCutoff D.rho D.rho_pos)))
  have hv : ContDiff ℝ ∞ v := fermiPerturbedSupport_profile_contDiff
    (normalLoop_actual_smooth D.zeta_smooth).2 (fermiExitCutoff_contDiff D.rho D.rho_pos)
    (fermiExitCutoff_zero D.rho D.rho_pos) D.W_open D.height_smooth
    D.scale_nonzero D.seam_in_W D.actual_mixed_positive B.epsilon P
  obtain ⟨δ,Cs,hδ,hδν,hδε,hCsE,hCsS,hCsI,hCF,hclose,hCW,hpositive,hnegative,hjets⟩ :=
    H.positive_graphs n ν hν
  have hnorth (q : AddCircle P) : 0 < (Cs q).val 2 := by
    let r := AddCircle.equivIco P 0 q
    have hr : (r : ℝ) ∈ Icc 0 P := by
      apply Ico_subset_Icc_self
      simpa only [zero_add] using r.property
    have hrep : periodProjection P (r : ℝ) = q := AddCircle.coe_equivIco
    rw [← hrep,hCF]
    exact D.fermi_north _ (hCW r hr).1
  let pn : AddCircle P → Coord := fun q => gnomonicInverse (Cs q).val
  have hpnS : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Coord) ∞ pn := fun q =>
    (gnomonicInverse_contMDiffAt (hnorth q)).comp q (hCsS q)
  have hpnI : Function.Injective pn := by
    intro q r he
    apply hCsE.injective
    exact (gnomonic_right_inverse (hnorth q)).symm.trans
      ((congrArg gnomonicPoint he).trans (gnomonic_right_inverse (hnorth r)))
  let p : ℝ → Coord := pn ∘ periodProjection P
  have hpS : ContDiff ℝ ∞ p := (hpnS.comp (periodProjection_contMDiff P)).contDiff
  have hpP : Function.Periodic p P := by
    intro s
    change pn ((s + P : ℝ) : AddCircle P) = pn (s : AddCircle P)
    rw [AddCircle.coe_add_period]
  have hpActual (s : ℝ) : p s = positiveExitFermiSource ζ (exitGraphCurve v δ s) := by
    change gnomonicInverse (Cs (periodProjection P s)).val = _
    rw [hCF]
    rfl
  have hpU : MapsTo p univ U := by
    intro s _
    let r := toIcoMod (Fact.out : 0 < P) 0 s
    have hr : r ∈ Icc 0 P := Ico_subset_Icc_self
      (toIcoMod_mem_Ico' (Fact.out : 0 < P) s)
    have he : p r = p s := hpP.sub_zsmul_eq (toIcoDiv (Fact.out : 0 < P) 0 s)
    rw [← he,hpActual]
    exact D.source_in_U (hCW r hr).1
  have hpLift : hpP.lift = pn :=
    (periodicLift_unique hpP pn (fun _ => rfl)).symm
  have hpI : Function.Injective hpP.lift := by rw [hpLift]; exact hpnI
  let gamma : ℝ → Coord := planarGradient Ge ∘ p
  have hgS : ContDiff ℝ ∞ gamma := contDiffOn_univ.mp
    ((planarGradient_contDiffOn hGe hU).comp hpS.contDiffOn hpU)
  have hgP : Function.Periodic gamma P := fun s => congrArg (planarGradient Ge) (hpP s)
  have hgI : Function.Injective hgP.lift := by
    have hdom (q : AddCircle P) : hpP.lift q ∈ U := by
      obtain ⟨s,rfl⟩ := QuotientAddGroup.mk_surjective q
      rw [hpP.lift_coe s]
      exact hpU (mem_univ s)
    have hgrad (q : AddCircle P) : hgP.lift q = planarGradient Ge (hpP.lift q) := by
      obtain ⟨s,rfl⟩ := QuotientAddGroup.mk_surjective q
      rw [hgP.lift_coe s,hpP.lift_coe s]
      rfl
    intro q r he
    apply hpI
    have he' : planarGradient Ge (hpP.lift q) = planarGradient Ge (hpP.lift r) := by
      rw [← hgrad q,← hgrad r]
      exact he
    have heU : (⟨hpP.lift q,hdom q⟩ : U) = ⟨hpP.lift r,hdom r⟩ := hemb.injective he'
    exact congrArg Subtype.val heU
  have hpairI (s : ℝ) (hs : s ∈ Icc 0 P) : 0 < deriv p s ⬝ᵥ deriv gamma s := by
    have hq := (hCW s hs).1
    have hcurve : HasDerivAt (exitGraphCurve v δ) (deriv (exitGraphCurve v δ) s) s :=
      ((exitGraphCurve_contDiff hv δ).differentiable (by simp) s).hasDerivAt
    have hsource := ((positiveExitFermiSource_contDiffOn D.zeta_smooth D.fermi_north
      _ hq).contDiffAt (D.W_open.mem_nhds hq)).differentiableAt (by simp)
    have hpD : HasDerivAt p
        (fderiv ℝ (positiveExitFermiSource ζ) (exitGraphCurve v δ s)
          (deriv (exitGraphCurve v δ) s)) s := by
      have he : p = positiveExitFermiSource ζ ∘ exitGraphCurve v δ := funext hpActual
      rw [he]
      exact hsource.hasFDerivAt.comp_hasDerivAt s hcurve
    have hpull := positiveExitFermi_tensor_pairing D.zeta_smooth D.unit D.unit_speed
      hGe hU D.W_open D.fermi_north D.scale_nonzero D.source_in_U hq
      (deriv (exitGraphCurve v δ) s) (deriv (exitGraphCurve v δ) s)
    rw [← hpActual s,← hpD.deriv] at hpull
    have hx : 0 < (deriv p s ⬝ᵥ (planarHessian Ge (p s) *ᵥ deriv p s)) /
        planarWeight (p s) := by rw [← hpull]; exact hpositive s hs
    change 0 < deriv p s ⬝ᵥ deriv (fun r => planarGradient Ge (p r)) s
    rw [planarTrace_gradient_deriv hGe hU (hpU (mem_univ s))
      (hpS.differentiable (by simp) s)]
    exact (div_pos_iff_of_pos_right (planarWeight_pos (p s))).mp hx
  have hderivP {f : ℝ → Coord} (hf : ContDiff ℝ ∞ f) (hfP : Function.Periodic f P) :
      Function.Periodic (deriv f) P := by
    have he : (f ∘ (fun s : ℝ => s + P)) = f := funext hfP
    intro s
    have hd := ((hf.differentiable (by simp) (s + P)).hasDerivAt).scomp s
      ((hasDerivAt_id s).add_const P)
    change HasDerivAt (f ∘ (fun s : ℝ => s + P)) (1 • deriv f (s + P)) s at hd
    rw [he] at hd
    simpa only [one_smul] using hd.unique (hf.differentiable (by simp) s).hasDerivAt
  have hpairP : Function.Periodic (fun s => deriv p s ⬝ᵥ deriv gamma s) P := by
    intro s
    change deriv p (s + P) ⬝ᵥ deriv gamma (s + P) = deriv p s ⬝ᵥ deriv gamma s
    rw [hderivP hpS hpP s,hderivP hgS hgP s]
  have hpair (s : ℝ) : 0 < deriv p s ⬝ᵥ deriv gamma s := by
    let r := toIcoMod (Fact.out : 0 < P) 0 s
    have hr : r ∈ Icc 0 P := Ico_subset_Icc_self
      (toIcoMod_mem_Ico' (Fact.out : 0 < P) s)
    have he := hpairP.sub_zsmul_eq (x := s) (toIcoDiv (Fact.out : 0 < P) 0 s)
    change deriv p r ⬝ᵥ deriv gamma r = deriv p s ⬝ᵥ deriv gamma s at he
    rw [← he]
    exact hpairI r hr
  have hcomplexS : ContDiff ℝ ∞ positiveExitComplexPoint := by
    have he : positiveExitComplexPoint = (fun q : Coord =>
        (q 0 : ℂ) + Complex.I * (q 1 : ℂ)) := by
      funext q
      apply Complex.ext <;> simp [positiveExitComplexPoint]
    rw [he]
    exact (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 0)).add
      (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 1)))
  have hcomplexI : Function.Injective positiveExitComplexPoint := by
    intro q r he
    have h0 := congrArg Complex.re he
    have h1 := congrArg Complex.im he
    ext i
    fin_cases i
    · exact h0
    · exact h1
  have hjordan {f : ℝ → Coord} (hf : ContDiff ℝ ∞ f)
      (hfP : Function.Periodic f P) (hfi : Function.Injective hfP.lift) :
      Schoenflies.IsJordanCurve (positiveExitJordanRange f) := by
    have he : range (jordanComplexCoordinates.symm ∘ positiveExitComplexPoint ∘ hfP.lift) =
        positiveExitJordanRange f := by
      ext z
      constructor
      · rintro ⟨q,rfl⟩
        obtain ⟨s,rfl⟩ := QuotientAddGroup.mk_surjective q
        refine ⟨s,?_⟩
        change jordanComplexCoordinates.symm (positiveExitComplexPoint (f s)) =
          jordanComplexCoordinates.symm (positiveExitComplexPoint (hfP.lift (s : AddCircle P)))
        rw [hfP.lift_coe s]
      · rintro ⟨s,rfl⟩
        refine ⟨periodProjection P s,?_⟩
        change jordanComplexCoordinates.symm (positiveExitComplexPoint (hfP.lift (s : AddCircle P))) =
          jordanComplexCoordinates.symm (positiveExitComplexPoint (f s))
        rw [hfP.lift_coe s]
    rw [← he]
    exact addCircle_complex_embedding_range_isJordanCurve P (Fact.out : 0 < P).ne'
      (positiveExitComplexPoint ∘ hfP.lift)
      (hcomplexS.continuous.comp (periodicLift_contMDiff hf hfP).continuous)
      (hcomplexI.comp hfi)
  have hvalue : ContDiff ℝ ∞ (Ge ∘ p) := contDiffOn_univ.mp (hGe.comp hpS.contDiffOn hpU)
  let tr : PositiveExitRegularGraphTrace Ge U P := {
    p := p
    gamma := gamma
    p_smooth := hpS
    gamma_smooth := hgS
    p_periodic := hpP
    gamma_periodic := hgP
    p_in_domain := hpU
    actual_gradient := rfl
    source_embedding := ((periodicLift_contMDiff hpS hpP).continuous.isClosedEmbedding hpI).isEmbedding
    gradient_embedding := ((periodicLift_contMDiff hgS hgP).continuous.isClosedEmbedding hgI).isEmbedding
    source_regular := fun s he => by simpa [he] using hpair s
    gradient_regular := fun s he => by simpa [he] using hpair s
    source_jordan := hjordan hpS hpP hpI
    gradient_jordan := hjordan hgS hgP hgI
    tangent_pairing := hpair
    value_smooth := hvalue
    value_periodic := fun s => congrArg Ge (hpP s)
    value_derivative := fun s => planarTrace_value_deriv hGe hU
      (hpU (mem_univ s)) (hpS.differentiable (by simp) s)
    zero_action := planarTrace_periodic_action_zero hGe hU hpS
      (fun _ _ => hpU (mem_univ _)) hpP }
  exact ⟨δ,Cs,tr,hδ,hδν,hδε,hpActual,hCsE,hCF,hclose,(fun s hs => by simpa only [exitGraphCurve, Matrix.cons_val_one, Matrix.cons_val_zero] using (hCW s hs).2),hjets⟩

/-- Compatibility projection of the same actual graph construction. -/
theorem positiveExit_paired_graph_exists_regular_trace {P : ℝ} [Fact (0 < P)]
    {G Ge : Coord → ℝ} {U C : Set Coord} {ζ : ℝ → Ambient}
    {hp : Function.Periodic ζ P} {η ξ σ ρMax : ℝ}
    (D : PositiveExitActualFermiData G U ζ hp η ξ σ ρMax)
    (B : PositiveExitActualCartesianPatch G U C ζ hp η ξ σ ρMax D)
    (H : PositiveExitPairedFermiPreserved D B Ge)
    (hU : IsOpen U) (hGe : ContDiffOn ℝ ∞ Ge U)
    (hemb : Topology.IsEmbedding (fun y : U => planarGradient Ge y.val))
    (n : ℕ) {ν : ℝ} (hν : 0 < ν) :
    let v := exitPositiveGraphProfile P (fermiSupportSeamSlope (normalLoopCurvature ζ)
      (fermiPerturbedSupport B.epsilon (normalLoopCurvature ζ) (positiveExitFermiHeight G ζ)
        (fermiExitCutoff D.rho D.rho_pos)))
    ∃ (δ : ℝ) (Cs : AddCircle P → RoundSphere) (tr : PositiveExitRegularGraphTrace Ge U P),
      0 < |δ| ∧ |δ| < ν ∧ 0 < δ * B.epsilon ∧
      (∀ s, tr.p s = positiveExitFermiSource ζ (exitGraphCurve v δ s)) ∧
      Topology.IsEmbedding Cs ∧
      (∀ s, (Cs (periodProjection P s) : Ambient) =
        fermiNormalMap ζ (exitGraphCurve v δ s)) ∧
      (∀ q, ‖(Cs q : Ambient) - hp.lift q‖ < ν) ∧
      ∀ j ≤ n, ∀ s ∈ Icc (0 : ℝ) P,
        ‖iteratedFDeriv ℝ j (fun r => fermiNormalMap ζ (exitGraphCurve v δ r)) s -
          iteratedFDeriv ℝ j ζ s‖ < ν := by
  obtain ⟨δ,Cs,tr,hδ,hδν,hδε,hactual,hCs,hCF,hclose,_hstrip,hjets⟩ :=
    positiveExit_paired_graph_exists_regular_trace_with_strip D B H hU hGe hemb n hν
  exact ⟨δ,Cs,tr,hδ,hδν,hδε,hactual,hCs,hCF,hclose,hjets⟩

end
end TightVer401
