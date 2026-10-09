import TightVer401.PositiveExitConstructionTraceStability
import TightVer401.PositiveExitConstructionOperatorBounds
import TightVer401.GnomonicCoordinates
import TightVer401.PlanarGradientInverse
import TightVer401.AngularDescentCharts

/-! Actual ambient first jets, the same Cartesian potential, and actual C2
changes supply visible Cartesian traces. Thresholds are chosen from the
compact original first-jet image before the change or graph is selected. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology RealInnerProductSpace BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

private def exitAmbientComplexCLM : Coord →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (ContinuousLinearMap.proj (R := ℝ) 0) +
    Complex.I • (Complex.ofRealCLM.comp (ContinuousLinearMap.proj (R := ℝ) 1))

private theorem exitAmbientComplexCLM_eq :
    (exitAmbientComplexCLM : Coord → ℂ) = angularDescentComplex := by
  ext q
  apply Complex.ext <;>
    simp [exitAmbientComplexCLM, angularDescentComplex, Complex.mul_re, Complex.mul_im]

private theorem exitAmbient_complex_hasDerivAt {p : ℝ → Coord} {v : Coord} {s : ℝ}
    (hp : HasDerivAt p v s) :
    HasDerivAt (angularDescentComplex ∘ p) (angularDescentComplex v) s := by
  simpa only [exitAmbientComplexCLM_eq] using
    exitAmbientComplexCLM.hasFDerivAt.comp_hasDerivAt s hp

theorem positiveExit_gradient_norm_le_fderiv_norm (J : Coord → ℝ) (q : Coord) :
    ‖planarGradient J q‖ ≤ ‖fderiv ℝ J q‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro j
  change ‖fderiv ℝ J q (Pi.single j 1)‖ ≤ _
  simpa only [Pi.norm_single, norm_one, mul_one] using (fderiv ℝ J q).le_opNorm (Pi.single j 1 : Coord)

theorem positiveExit_gradient_fderiv_norm_le_secondFDeriv_norm {J : Coord → ℝ}
    (hJ : ContDiff ℝ ∞ J) (q : Coord) :
    ‖fderiv ℝ (planarGradient J) q‖ ≤ ‖fderiv ℝ (fderiv ℝ J) q‖ := by
  have hd : DifferentiableAt ℝ (fderiv ℝ J) q :=
    (hJ.contDiffAt.fderiv_right (m := 1)
      (by exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))).differentiableAt (by norm_num)
  have he (v : Coord) (j : Fin 2) :
      fderiv ℝ (planarGradient J) q v j =
        fderiv ℝ (fderiv ℝ J) q v (Pi.single j 1) := by
    unfold planarGradient
    rw [fderiv_pi (fun j =>
      ((fermiCoordinatePartial_contDiff hJ j).differentiable (by simp) q))]
    change fderiv ℝ (fun x => (fderiv ℝ J x) (Pi.single j 1)) q v = _
    rw [fderiv_clm_apply hd (differentiableAt_const (c := (Pi.single j 1 : Coord)))]
    simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
      ContinuousLinearMap.flip_apply]
  apply (fderiv ℝ (planarGradient J) q).opNorm_le_bound (norm_nonneg (fderiv ℝ (fderiv ℝ J) q))
  intro v
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
  intro j
  rw [he]
  calc
    ‖fderiv ℝ (fderiv ℝ J) q v (Pi.single j 1)‖ ≤
        ‖fderiv ℝ (fderiv ℝ J) q v‖ := by
      simpa only [Pi.norm_single, norm_one, mul_one] using (fderiv ℝ (fderiv ℝ J) q v).le_opNorm (Pi.single j 1 : Coord)
    _ ≤ ‖fderiv ℝ (fderiv ℝ J) q‖ * ‖v‖ :=
      (fderiv ℝ (fderiv ℝ J) q).le_opNorm v

/-- Both actual gradient perturbation norms are bounded by the proved budget. -/
theorem positiveExit_gradient_jet_norm_le_coordinateC2Size {J : Coord → ℝ}
    (hJ : ContDiff ℝ ∞ J) (q : Coord) :
    ‖planarGradient J q‖ ≤ fermiCoordinateC2Size J q ∧
      ‖fderiv ℝ (planarGradient J) q‖ ≤ fermiCoordinateC2Size J q := by
  have h := positiveExit_operatorC2Size_le_coordinateC2Size hJ q
  have h0 := norm_nonneg (J q)
  have h1 := norm_nonneg (fderiv ℝ J q)
  have h2 := norm_nonneg (fderiv ℝ (fderiv ℝ J) q)
  constructor
  · exact (positiveExit_gradient_norm_le_fderiv_norm J q).trans (by linarith)
  · exact (positiveExit_gradient_fderiv_norm_le_secondFDeriv_norm hJ q).trans (by linarith)

private theorem exitAmbient_gradient_add {G J : Coord → ℝ} {U : Set Coord}
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U) (hJ : ContDiff ℝ ∞ J)
    {q : Coord} (hq : q ∈ U) :
    planarGradient (fun x => G x + J x) q = planarGradient G q + planarGradient J q := by
  ext j
  change fderiv ℝ (fun x => G x + J x) q (Pi.single j 1) = _
  rw [fderiv_fun_add ((hG q hq).contDiffAt (hU.mem_nhds hq) |>.differentiableAt (by simp))
    (hJ.differentiable (by simp) q)]
  rfl

private theorem exitAmbient_gradient_fderiv_add {G J : Coord → ℝ} {U : Set Coord}
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U) (hJ : ContDiff ℝ ∞ J)
    {q : Coord} (hq : q ∈ U) :
    fderiv ℝ (planarGradient (fun x => G x + J x)) q =
      fderiv ℝ (planarGradient G) q + fderiv ℝ (planarGradient J) q := by
  have he : planarGradient (fun x => G x + J x) =ᶠ[𝓝 q]
      (fun x => planarGradient G x + planarGradient J x) := by
    filter_upwards [hU.mem_nhds hq] with x hx
    exact exitAmbient_gradient_add hG hU hJ hx
  rw [he.fderiv_eq]
  exact fderiv_fun_add
    (((planarGradient_contDiffOn hG hU) q hq).contDiffAt (hU.mem_nhds hq)
      |>.differentiableAt (by simp))
    (((planarGradient_contDiffOn hJ.contDiffOn isOpen_univ) q (mem_univ q)).contDiffAt
      (isOpen_univ.mem_nhds (mem_univ q)) |>.differentiableAt (by simp))

private abbrev ExitAmbientJet := Ambient × (Ambient × (Coord × (Coord →L[ℝ] Coord)))

private def exitAmbientJetVelocity (x : ExitAmbientJet) : Coord :=
  fderiv ℝ gnomonicInverse x.1 x.2.1

private def exitAmbientJetVisible (R : ℝ) (G : Coord → ℝ) (x : ExitAmbientJet) : Prop :=
  let q := gnomonicInverse x.1
  let v := exitAmbientJetVelocity x
  let z := Complex.I * angularDescentComplex (planarGradient G q + x.2.2.1)
  let a := angularDescentComplex v
  let b := Complex.I * angularDescentComplex
    ((fderiv ℝ (planarGradient G) q + x.2.2.2) v)
  R < ‖z‖ ∧ 0 < inner ℝ a (corrugatedVisibilityDirection R z) ∧
    0 < inner ℝ b (corrugatedVisibilityDirection R z)

private theorem exitAmbientJet_visible_isOpen {R : ℝ} (hR : 0 ≤ R)
    {G : Coord → ℝ} {U : Set Coord} (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U) :
    IsOpen {x : ExitAmbientJet | 0 < x.1 2 ∧ gnomonicInverse x.1 ∈ U ∧
      exitAmbientJetVisible R G x} := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  have hphi := gnomonicInverse_contDiffAt (ne_of_gt hx.1)
  have cq : ContinuousAt (fun y : ExitAmbientJet => gnomonicInverse y.1) x :=
    hphi.continuousAt.comp continuous_fst.continuousAt
  have cD : ContinuousAt (fun y : ExitAmbientJet => fderiv ℝ gnomonicInverse y.1) x :=
    (hphi.continuousAt_fderiv (by simp)).comp continuous_fst.continuousAt
  have cv : ContinuousAt exitAmbientJetVelocity x :=
    cD.clm_apply (continuous_fst.comp continuous_snd).continuousAt
  have hgrad := planarGradient_contDiffOn hG hU
  have cgrad : ContinuousAt (fun y : ExitAmbientJet =>
      planarGradient G (gnomonicInverse y.1)) x := by
    apply continuousAt_pi.mpr
    intro j
    change ContinuousAt (fun y : ExitAmbientJet => coordPartial j G (gnomonicInverse y.1)) x
    have hcomp := (((partial_contDiffOn hG hU j) _ hx.2.1).contDiffAt
      (hU.mem_nhds hx.2.1)).continuousAt.comp (x := x) cq
    simpa only [Function.comp_def] using hcomp
  have cDgrad : ContinuousAt (fun y : ExitAmbientJet =>
      fderiv ℝ (planarGradient G) (gnomonicInverse y.1)) x := ((hgrad _ hx.2.1).contDiffAt (hU.mem_nhds hx.2.1)).continuousAt_fderiv
    (by simp) |>.comp (x := x) cq
  have ca0 : ContinuousAt (fun y : ExitAmbientJet => y.2.2.1) x := by fun_prop
  have cL : ContinuousAt (fun y : ExitAmbientJet => y.2.2.2) x := by fun_prop
  have ca := angularDescentComplex_contDiff.continuous.continuousAt.comp cv
  have cz : ContinuousAt (fun y : ExitAmbientJet => Complex.I *
      angularDescentComplex (planarGradient G (gnomonicInverse y.1) + y.2.2.1)) x :=
    continuousAt_const.mul (angularDescentComplex_contDiff.continuous.continuousAt.comp
      (cgrad.add ca0))
  have cb : ContinuousAt (fun y : ExitAmbientJet => Complex.I * angularDescentComplex
      ((fderiv ℝ (planarGradient G) (gnomonicInverse y.1) + y.2.2.2)
        (exitAmbientJetVelocity y))) x :=
    continuousAt_const.mul (angularDescentComplex_contDiff.continuous.continuousAt.comp
      ((cDgrad.add cL).clm_apply cv))
  rcases hx.2.2 with ⟨hz, ha, hb⟩
  have hz0 : (Complex.I * angularDescentComplex
      (planarGradient G (gnomonicInverse x.1) + x.2.2.1)) ≠ 0 :=
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
theorem positiveExit_exists_ambientJet_visibility_threshold {R P : ℝ}
    (hR : 0 ≤ R) (hP : 0 < P) {G : Coord → ℝ} {U : Set Coord}
    (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U) {ζ : ℝ → Ambient}
    (hζ : ContDiff ℝ ∞ ζ) (hnorth : ∀ s, 0 < ζ s 2)
    (hsource : ∀ s, gnomonicInverse (ζ s) ∈ U)
    (hvisible : ComplexVisiblePair R (angularDescentComplex ∘ gnomonicInverse ∘ ζ)
      (fun s => Complex.I * angularDescentComplex (planarGradient G (gnomonicInverse (ζ s))))) :
    ∃ η > 0, ∃ ν > 0, ∀ (J : Coord → ℝ) (c : ℝ → Ambient),
      ContDiff ℝ ∞ J → ContDiff ℝ ∞ c → Function.Periodic c P →
      (∀ q ∈ U, fermiCoordinateC2Size J q < η) →
      (∀ s ∈ Icc (0 : ℝ) P, ‖c s - ζ s‖ < ν ∧ ‖deriv c s - deriv ζ s‖ < ν) →
      (∀ s, 0 < c s 2 ∧ gnomonicInverse (c s) ∈ U) ∧
      ComplexVisiblePair R (angularDescentComplex ∘ gnomonicInverse ∘ c)
        (fun s => Complex.I * angularDescentComplex
          (planarGradient (fun q => G q + J q) (gnomonicInverse (c s)))) := by
  let O : Set ExitAmbientJet := {x | 0 < x.1 2 ∧ gnomonicInverse x.1 ∈ U ∧
    exitAmbientJetVisible R G x}
  have hO := exitAmbientJet_visible_isOpen hR hU hG
  let j0 : ℝ → ExitAmbientJet := fun s => (ζ s, (deriv ζ s, (0, 0)))
  have hj0 : Continuous j0 :=
    hζ.continuous.prodMk (((contDiff_infty_iff_deriv.mp hζ).2.continuous).prodMk
      (continuous_const.prodMk continuous_const))
  have hbase : ∀ s, j0 s ∈ O := by
    intro s
    have hq := (gnomonicInverse_contDiffAt (ne_of_gt (hnorth s))).differentiableAt (by simp)
    have hp := hq.hasFDerivAt.comp_hasDerivAt s (hζ.differentiable (by simp) s).hasDerivAt
    have hg := (((planarGradient_contDiffOn hG hU) _ (hsource s)).contDiffAt
      (hU.mem_nhds (hsource s)) |>.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt s hp
    have hpc := exitAmbient_complex_hasDerivAt hp
    have hgc := (exitAmbient_complex_hasDerivAt hg).const_mul Complex.I
    dsimp only [Function.comp_def] at hgc
    have hv := hvisible s
    rw [hpc.deriv, hgc.deriv] at hv
    refine ⟨hnorth s, hsource s, ?_⟩
    simpa only [exitAmbientJetVisible, exitAmbientJetVelocity, j0, Function.comp_apply,
      add_zero] using hv
  have hK : IsCompact (j0 '' Icc (0 : ℝ) P) := isCompact_Icc.image hj0
  obtain ⟨ε, hε, he⟩ := hK.exists_thickening_subset_open hO (by
    rintro _ ⟨s, _, rfl⟩
    exact hbase s)
  refine ⟨ε, hε, ε, hε, fun J c hJ hc hcP hbudget hclose => ?_⟩
  let jc : ℝ → ExitAmbientJet := fun s =>
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
  have hs := hall s
  have hnorthC : 0 < c s 2 := hs.1
  have hsourceC : gnomonicInverse (c s) ∈ U := hs.2.1
  have hq := (gnomonicInverse_contDiffAt (ne_of_gt hnorthC)).differentiableAt (by simp)
  have hp := hq.hasFDerivAt.comp_hasDerivAt s (hc.differentiable (by simp) s).hasDerivAt
  have hGe : ContDiffOn ℝ ∞ (fun q => G q + J q) U := hG.add hJ.contDiffOn
  have hg := (((planarGradient_contDiffOn hGe hU) _ hsourceC).contDiffAt
    (hU.mem_nhds hsourceC) |>.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt s hp
  have hpc := exitAmbient_complex_hasDerivAt hp
  have hgc := (exitAmbient_complex_hasDerivAt hg).const_mul Complex.I
  dsimp only [Function.comp_def] at hgc
  rw [hpc.deriv, hgc.deriv]
  simp only [Function.comp_apply]
  rw [exitAmbient_gradient_add hG hU hJ hsourceC,
    exitAmbient_gradient_fderiv_add hG hU hJ hsourceC]
  simpa only [exitAmbientJetVisible, exitAmbientJetVelocity, jc, Function.comp_apply] using hs.2.2

end
end TightVer401
