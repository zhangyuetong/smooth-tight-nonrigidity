import TightVer401.PositiveExitConstructionAmbientJetVisibility
import TightVer401.PositiveExitConstructionGraphVisibility
import TightVer401.CorrugatedSeedVisiblePairs

/-! Actual inner reflected visibility is a separate open full-jet condition.
The SAME actual G and actual Cartesian C2 change give thresholds before any
patch amplitude or graph is selected. Outer visibility is not used as a grant. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology RealInnerProductSpace BigOperators ComplexConjugate
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
private def exitAmbientDualComplexCLM : Coord →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (ContinuousLinearMap.proj (R := ℝ) 0) +
    Complex.I • (Complex.ofRealCLM.comp (ContinuousLinearMap.proj (R := ℝ) 1))

private theorem exitAmbientDualComplexCLM_eq :
    (exitAmbientDualComplexCLM : Coord → ℂ) = angularDescentComplex := by
  ext q
  apply Complex.ext <;>
    simp [exitAmbientDualComplexCLM, angularDescentComplex, Complex.mul_re, Complex.mul_im]

private theorem exitAmbientDual_complex_hasDerivAt {p : ℝ → Coord} {v : Coord} {s : ℝ}
    (hp : HasDerivAt p v s) :
    HasDerivAt (angularDescentComplex ∘ p) (angularDescentComplex v) s := by
  simpa only [exitAmbientDualComplexCLM_eq] using
    exitAmbientDualComplexCLM.hasFDerivAt.comp_hasDerivAt s hp

private theorem exitAmbientDual_gradient_add {G J : Coord → ℝ} {U : Set Coord}
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U) (hJ : ContDiff ℝ ∞ J)
    {q : Coord} (hq : q ∈ U) :
    planarGradient (fun x => G x + J x) q = planarGradient G q + planarGradient J q := by
  ext j
  change fderiv ℝ (fun x => G x + J x) q (Pi.single j 1) = _
  rw [fderiv_fun_add ((hG q hq).contDiffAt (hU.mem_nhds hq) |>.differentiableAt (by simp))
    (hJ.differentiable (by simp) q)]
  rfl

private theorem exitAmbientDual_gradient_fderiv_add {G J : Coord → ℝ} {U : Set Coord}
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U) (hJ : ContDiff ℝ ∞ J)
    {q : Coord} (hq : q ∈ U) :
    fderiv ℝ (planarGradient (fun x => G x + J x)) q =
      fderiv ℝ (planarGradient G) q + fderiv ℝ (planarGradient J) q := by
  have he : planarGradient (fun x => G x + J x) =ᶠ[𝓝 q]
      (fun x => planarGradient G x + planarGradient J x) := by
    filter_upwards [hU.mem_nhds hq] with x hx
    exact exitAmbientDual_gradient_add hG hU hJ hx
  rw [he.fderiv_eq]
  exact fderiv_fun_add
    (((planarGradient_contDiffOn hG hU) q hq).contDiffAt (hU.mem_nhds hq)
      |>.differentiableAt (by simp))
    (((planarGradient_contDiffOn hJ.contDiffOn isOpen_univ) q (mem_univ q)).contDiffAt
      (isOpen_univ.mem_nhds (mem_univ q)) |>.differentiableAt (by simp))

private abbrev ExitAmbientDualJet := Ambient × (Ambient × (Coord × (Coord →L[ℝ] Coord)))

private def exitAmbientDualJetVelocity (x : ExitAmbientDualJet) : Coord :=
  fderiv ℝ gnomonicInverse x.1 x.2.1

private def exitAmbientDualJetVisible (R : ℝ) (G : Coord → ℝ) (x : ExitAmbientDualJet) : Prop :=
  let q := gnomonicInverse x.1
  let v := exitAmbientDualJetVelocity x
  let z := Complex.I * conj (angularDescentComplex q)
  let a := -conj (angularDescentComplex
    ((fderiv ℝ (planarGradient G) q + x.2.2.2) v))
  let b := -Complex.I * conj (angularDescentComplex v)
  R < ‖z‖ ∧ 0 < inner ℝ a (corrugatedVisibilityDirection R z) ∧
    0 < inner ℝ b (corrugatedVisibilityDirection R z)
private theorem exitAmbientDualJet_visible_isOpen {R : ℝ} (hR : 0 ≤ R)
    {G : Coord → ℝ} {U : Set Coord} (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U) :
    IsOpen {x : ExitAmbientDualJet | 0 < x.1 2 ∧ gnomonicInverse x.1 ∈ U ∧
      exitAmbientDualJetVisible R G x} := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  have hphi := gnomonicInverse_contDiffAt (ne_of_gt hx.1)
  have cq : ContinuousAt (fun y : ExitAmbientDualJet => gnomonicInverse y.1) x :=
    hphi.continuousAt.comp continuous_fst.continuousAt
  have cD : ContinuousAt (fun y : ExitAmbientDualJet => fderiv ℝ gnomonicInverse y.1) x :=
    (hphi.continuousAt_fderiv (by simp)).comp continuous_fst.continuousAt
  have cv : ContinuousAt exitAmbientDualJetVelocity x :=
    cD.clm_apply (continuous_fst.comp continuous_snd).continuousAt
  have hgrad := planarGradient_contDiffOn hG hU
  have cgrad : ContinuousAt (fun y : ExitAmbientDualJet =>
      planarGradient G (gnomonicInverse y.1)) x := by
    apply continuousAt_pi.mpr
    intro j
    change ContinuousAt (fun y : ExitAmbientDualJet => coordPartial j G (gnomonicInverse y.1)) x
    have hcomp := (((partial_contDiffOn hG hU j) _ hx.2.1).contDiffAt
      (hU.mem_nhds hx.2.1)).continuousAt.comp (x := x) cq
    simpa only [Function.comp_def] using hcomp
  have cDgrad : ContinuousAt (fun y : ExitAmbientDualJet =>
      fderiv ℝ (planarGradient G) (gnomonicInverse y.1)) x := ((hgrad _ hx.2.1).contDiffAt (hU.mem_nhds hx.2.1)).continuousAt_fderiv
    (by simp) |>.comp (x := x) cq
  have ca0 : ContinuousAt (fun y : ExitAmbientDualJet => y.2.2.1) x := by fun_prop
  have cL : ContinuousAt (fun y : ExitAmbientDualJet => y.2.2.2) x := by fun_prop
  have cp := angularDescentComplex_contDiff.continuous.continuousAt.comp cq
  have cvcomplex := angularDescentComplex_contDiff.continuous.continuousAt.comp cv
  have cvelocity := angularDescentComplex_contDiff.continuous.continuousAt.comp
    ((cDgrad.add cL).clm_apply cv)
  have ca : ContinuousAt (fun y : ExitAmbientDualJet => -conj (angularDescentComplex
      ((fderiv ℝ (planarGradient G) (gnomonicInverse y.1) + y.2.2.2)
        (exitAmbientDualJetVelocity y)))) x := cvelocity.star.neg
  have cz : ContinuousAt (fun y : ExitAmbientDualJet =>
      Complex.I * conj (angularDescentComplex (gnomonicInverse y.1))) x :=
    continuousAt_const.mul cp.star
  have cb : ContinuousAt (fun y : ExitAmbientDualJet =>
      -Complex.I * conj (angularDescentComplex (exitAmbientDualJetVelocity y))) x :=
    continuousAt_const.mul cvcomplex.star
  rcases hx.2.2 with ⟨hz, ha, hb⟩
  have hz0 : (Complex.I * conj (angularDescentComplex (gnomonicInverse x.1))) ≠ 0 :=
    norm_pos_iff.mp (hR.trans_lt hz)
  have cd := (visibilityDirection_continuousAt R hz0).comp (x := x) cz
  have h1 := (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) (2 : Fin 3)).continuous.comp
    continuous_fst).continuousAt).preimage_mem_nhds (Ioi_mem_nhds hx.1)
  have h2 := cq.preimage_mem_nhds (hU.mem_nhds hx.2.1)
  have h3 := cz.norm.preimage_mem_nhds (Ioi_mem_nhds hz)
  have h4 := (ca.inner cd).preimage_mem_nhds (Ioi_mem_nhds ha)
  have h5 := (cb.inner cd).preimage_mem_nhds (Ioi_mem_nhds hb)
  exact inter_mem h1 (inter_mem h2 (inter_mem h3 (inter_mem h4 h5)))

/-- Actual ambient first jets and an actual coordinate C2-small change yield
visibility for the gradient of the same literal potential `G + J`. -/
theorem positiveExit_exists_ambientJet_dual_visibility_threshold {R P : ℝ}
    (hR : 0 ≤ R) (hP : 0 < P) {G : Coord → ℝ} {U : Set Coord}
    (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U) {ζ : ℝ → Ambient}
    (hζ : ContDiff ℝ ∞ ζ) (hnorth : ∀ s, 0 < ζ s 2)
    (hsource : ∀ s, gnomonicInverse (ζ s) ∈ U)
    (hvisible : ComplexVisiblePair R
      (corrugatedReverseReflect (angularDescentComplex ∘ planarGradient G ∘ gnomonicInverse ∘ ζ))
      (fun s => Complex.I * corrugatedReverseReflect
        (angularDescentComplex ∘ gnomonicInverse ∘ ζ) s)) :
    ∃ η > 0, ∃ ν > 0, ∀ (J : Coord → ℝ) (c : ℝ → Ambient),
      ContDiff ℝ ∞ J → ContDiff ℝ ∞ c → Function.Periodic c P →
      (∀ q ∈ U, fermiCoordinateC2Size J q < η) →
      (∀ s ∈ Icc (0 : ℝ) P, ‖c s - ζ s‖ < ν ∧ ‖deriv c s - deriv ζ s‖ < ν) →
      (∀ s, 0 < c s 2 ∧ gnomonicInverse (c s) ∈ U) ∧
      ComplexVisiblePair R
        (corrugatedReverseReflect (angularDescentComplex ∘
          planarGradient (fun q => G q + J q) ∘ gnomonicInverse ∘ c))
        (fun s => Complex.I * corrugatedReverseReflect
          (angularDescentComplex ∘ gnomonicInverse ∘ c) s) := by
  let O : Set ExitAmbientDualJet := {x | 0 < x.1 2 ∧ gnomonicInverse x.1 ∈ U ∧
    exitAmbientDualJetVisible R G x}
  have hO := exitAmbientDualJet_visible_isOpen hR hU hG
  let j0 : ℝ → ExitAmbientDualJet := fun s => (ζ s, (deriv ζ s, (0, 0)))
  have hj0 : Continuous j0 :=
    hζ.continuous.prodMk (((contDiff_infty_iff_deriv.mp hζ).2.continuous).prodMk
      (continuous_const.prodMk continuous_const))
  have hbase : ∀ s, j0 s ∈ O := by
    intro s
    have hq := (gnomonicInverse_contDiffAt (ne_of_gt (hnorth s))).differentiableAt (by simp)
    have hp := hq.hasFDerivAt.comp_hasDerivAt s (hζ.differentiable (by simp) s).hasDerivAt
    have hg := (((planarGradient_contDiffOn hG hU) _ (hsource s)).contDiffAt
      (hU.mem_nhds (hsource s)) |>.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt s hp
    have hpc := exitAmbientDual_complex_hasDerivAt hp
    have hgc := exitAmbientDual_complex_hasDerivAt hg
    have hgr := corrugatedReverseReflect_hasDerivAt (t := -s) (by simpa using hgc)
    have hpr := (corrugatedReverseReflect_hasDerivAt (t := -s) (by simpa using hpc)).const_mul Complex.I
    have hgrEq := hgr.deriv
    have hprEq := hpr.deriv
    change deriv (corrugatedReverseReflect
      (angularDescentComplex ∘ planarGradient G ∘ gnomonicInverse ∘ ζ)) (-s) = _ at hgrEq
    change deriv (fun r => Complex.I * corrugatedReverseReflect
      (angularDescentComplex ∘ gnomonicInverse ∘ ζ) r) (-s) = _ at hprEq
    have hv := hvisible (-s)
    rw [hgrEq, hprEq] at hv
    refine ⟨hnorth s, hsource s, ?_⟩
    simpa only [exitAmbientDualJetVisible, exitAmbientDualJetVelocity, j0, Function.comp_apply,
      corrugatedReverseReflect, neg_neg, add_zero, mul_neg, neg_mul] using hv
  have hK : IsCompact (j0 '' Icc (0 : ℝ) P) := isCompact_Icc.image hj0
  obtain ⟨ε, hε, he⟩ := hK.exists_thickening_subset_open hO (by
    rintro _ ⟨s, _, rfl⟩
    exact hbase s)
  refine ⟨ε, hε, ε, hε, fun J c hJ hc hcP hbudget hclose => ?_⟩
  let jc : ℝ → ExitAmbientDualJet := fun s =>
    (c s, (deriv c s, (planarGradient J (gnomonicInverse (c s)),
      fderiv ℝ (planarGradient J) (gnomonicInverse (c s)))))
  have hsmall : ∀ s ∈ Icc (0 : ℝ) P, jc s ∈ O := by
    intro s hs
    -- First use zero change coordinates to establish membership in the domain.
    have hz : (c s, (deriv c s, ((0 : Coord), (0 : Coord →L[ℝ] Coord)))) ∈ O := by
      apply he
      apply Metric.mem_thickening_iff.mpr
      refine ⟨j0 s, ⟨s, hs, rfl⟩, ?_⟩
      dsimp only [j0]
      rw [Prod.dist_eq, Prod.dist_eq, Prod.dist_eq]
      simpa only [dist_eq_norm, sub_self, norm_zero] using
        max_lt (hclose s hs).1 (max_lt (hclose s hs).2 (max_lt hε hε))
    have hb := hbudget _ hz.2.1
    have hnorm := positiveExit_gradient_jet_norm_le_coordinateC2Size hJ (gnomonicInverse (c s))
    apply he
    apply Metric.mem_thickening_iff.mpr
    refine ⟨j0 s, ⟨s, hs, rfl⟩, ?_⟩
    dsimp only [jc, j0]
    rw [Prod.dist_eq, Prod.dist_eq, Prod.dist_eq]
    simpa only [dist_eq_norm, sub_zero] using
      max_lt (hclose s hs).1 (max_lt (hclose s hs).2
        (max_lt (hnorm.1.trans_lt hb) (hnorm.2.trans_lt hb)))
  have hdcP : Function.Periodic (deriv c) P := by
    have hef : (c ∘ (fun s : ℝ => s + P)) = c := funext hcP
    intro s
    have hd := ((hc.differentiable (by simp) (s + P)).hasDerivAt).scomp s
      ((hasDerivAt_id s).add_const P)
    change HasDerivAt (c ∘ (fun s : ℝ => s + P)) (1 • deriv c (s + P)) s at hd
    rw [hef] at hd
    simpa only [one_smul] using hd.unique (hc.differentiable (by simp) s).hasDerivAt
  have hjcP : Function.Periodic jc P := by
    intro s
    simp only [jc, hcP s, hdcP s]
  have hall : ∀ s, jc s ∈ O := by
    intro s
    let r := toIcoMod hP 0 s
    have hr : r ∈ Icc (0 : ℝ) P := Ico_subset_Icc_self (toIcoMod_mem_Ico' hP s)
    have heq := hjcP.sub_zsmul_eq (x := s) (toIcoDiv hP 0 s)
    change jc r = jc s at heq
    rw [← heq]
    exact hsmall r hr
  refine ⟨fun s => ⟨(hall s).1, (hall s).2.1⟩, ?_⟩
  intro s
  have hs := hall (-s)
  have hnorthC : 0 < c (-s) 2 := hs.1
  have hsourceC : gnomonicInverse (c (-s)) ∈ U := hs.2.1
  have hq := (gnomonicInverse_contDiffAt (ne_of_gt hnorthC)).differentiableAt (by simp)
  have hp := hq.hasFDerivAt.comp_hasDerivAt (-s) (hc.differentiable (by simp) (-s)).hasDerivAt
  have hGe : ContDiffOn ℝ ∞ (fun q => G q + J q) U := hG.add hJ.contDiffOn
  have hg := (((planarGradient_contDiffOn hGe hU) _ hsourceC).contDiffAt
    (hU.mem_nhds hsourceC) |>.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt (-s) hp
  have hpc := exitAmbientDual_complex_hasDerivAt hp
  have hgc := exitAmbientDual_complex_hasDerivAt hg
  have hgr := corrugatedReverseReflect_hasDerivAt hgc
  have hpr := (corrugatedReverseReflect_hasDerivAt hpc).const_mul Complex.I
  have hgrEq := hgr.deriv
  have hprEq := hpr.deriv
  change deriv (corrugatedReverseReflect
    (angularDescentComplex ∘ planarGradient (fun q => G q + J q) ∘ gnomonicInverse ∘ c)) s = _ at hgrEq
  change deriv (fun r => Complex.I * corrugatedReverseReflect
    (angularDescentComplex ∘ gnomonicInverse ∘ c) r) s = _ at hprEq
  rw [hgrEq, hprEq]
  simp only [corrugatedReverseReflect, Function.comp_apply]
  rw [exitAmbientDual_gradient_fderiv_add hG hU hJ hsourceC]
  simpa only [exitAmbientDualJetVisible, exitAmbientDualJetVelocity, jc, Function.comp_apply,
    mul_neg, neg_mul] using hs.2.2

private theorem exitGraphDualVisibility_complex_eq :
    positiveExitComplexPoint = angularDescentComplex := by
  funext q
  apply Complex.ext <;> simp [positiveExitComplexPoint, angularDescentComplex]

/-- The actual graph's returned orders zero and one preserve the inner
reflected visible pair for the SAME actual changed Cartesian potential. -/
theorem positiveExit_exists_graph_trace_dual_visibility_threshold {R P : ℝ}
    (hR : 0 ≤ R) (hP : 0 < P) {G : Coord → ℝ} {U : Set Coord}
    (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U) {ζ : ℝ → Ambient}
    (hζ : ContDiff ℝ ∞ ζ) (hnorth : ∀ s, 0 < ζ s 2)
    (hsource : ∀ s, gnomonicInverse (ζ s) ∈ U)
    (hvisible : ComplexVisiblePair R
      (corrugatedReverseReflect (angularDescentComplex ∘ planarGradient G ∘ gnomonicInverse ∘ ζ))
      (fun s => Complex.I * corrugatedReverseReflect
        (angularDescentComplex ∘ gnomonicInverse ∘ ζ) s)) :
    ∃ η > 0, ∃ ν > 0, ∀ (J : Coord → ℝ) (c : ℝ → Ambient),
      ContDiff ℝ ∞ J → ContDiff ℝ ∞ c → Function.Periodic c P →
      (∀ q ∈ U, fermiCoordinateC2Size J q < η) →
      (∀ j ≤ 1, ∀ s ∈ Icc (0 : ℝ) P,
        ‖iteratedFDeriv ℝ j c s - iteratedFDeriv ℝ j ζ s‖ < ν) →
      ∀ tr : PositiveExitRegularGraphTrace (fun q => G q + J q) U P,
      (∀ s, tr.p s = gnomonicInverse (c s)) →
      ComplexVisiblePair R
        (corrugatedReverseReflect (positiveExitComplexTrace tr.gamma))
        (fun s => Complex.I * corrugatedReverseReflect
          (positiveExitComplexTrace tr.p) s) := by
  obtain ⟨η, hη, ν, hν, h⟩ := positiveExit_exists_ambientJet_dual_visibility_threshold
    hR hP hU hG hζ hnorth hsource hvisible
  refine ⟨η, hη, ν, hν, ?_⟩
  intro J c hJ hc hcP hbudget hjets tr hactual
  obtain ⟨_, hv⟩ := h J c hJ hc hcP hbudget
    (positiveExit_firstJet_close_of_iteratedFDeriv hjets)
  have heq : tr.p = gnomonicInverse ∘ c := funext hactual
  rw [positiveExitComplexTrace, positiveExitComplexTrace,
    tr.actual_gradient, heq, exitGraphDualVisibility_complex_eq]
  simpa only [Function.comp_apply] using hv

end
end TightVer401

