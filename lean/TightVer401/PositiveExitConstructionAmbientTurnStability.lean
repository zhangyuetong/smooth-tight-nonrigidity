import TightVer401.PositiveExitConstructionBalancedTurn
import TightVer401.PositiveExitConstructionAmbientJetVisibility

/-! Turn margins for actual positive graphs are selected before the change and
graph. Only ambient value closeness and the actual coordinate C2 change bound
are consumed; no factory of Cartesian estimates or graph turns is assumed. -/
namespace TightVer401
noncomputable section
open Set Function Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private abbrev ExitAmbientTurnState := ℝ × (Ambient × Coord)

private theorem exitAmbientTurn_gradient_add {G J : Coord → ℝ} {U : Set Coord}
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U) (hJ : ContDiff ℝ ∞ J)
    {q : Coord} (hq : q ∈ U) :
    planarGradient (fun x => G x + J x) q = planarGradient G q + planarGradient J q := by
  ext j
  change fderiv ℝ (fun x => G x + J x) q (Pi.single j 1) = _
  rw [fderiv_fun_add
    (((hG q hq).contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp))
    (hJ.differentiable (by simp) q)]
  rfl

/-- Both actual source and gradient turns for the literal same potential G+J.
The two margins precede all choices of J and c. Value closeness suffices. -/
theorem positiveExit_exists_ambient_value_argumentTurn_threshold
    {P : ℝ} (hP : 0 < P) {G : Coord → ℝ} {U : Set Coord}
    (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U) {ζ : ℝ → Ambient}
    (hζ : ContDiff ℝ ∞ ζ) (hζP : Periodic ζ P)
    (hnorth : ∀ s, 0 < ζ s 2)
    (hsource : ∀ s, gnomonicInverse (ζ s) ∈ U)
    (hpnz : ∀ s, angularDescentComplex (gnomonicInverse (ζ s)) ≠ 0)
    (hgnz : ∀ s, angularDescentComplex (planarGradient G (gnomonicInverse (ζ s))) ≠ 0)
    (hpturn : HasPositiveArgumentTurn (angularDescentComplex ∘ gnomonicInverse ∘ ζ) P)
    (hgturn : HasPositiveArgumentTurn
      (angularDescentComplex ∘ planarGradient G ∘ gnomonicInverse ∘ ζ) P) :
    ∃ η > 0, ∃ ν > 0, ∀ (J : Coord → ℝ) (c : ℝ → Ambient),
      ContDiff ℝ ∞ J → ContDiff ℝ ∞ c → Periodic c P →
      (∀ q ∈ U, fermiCoordinateC2Size J q < η) →
      (∀ s ∈ Icc (0 : ℝ) P, ‖c s - ζ s‖ < ν) →
      (∀ s, 0 < c s 2 ∧ gnomonicInverse (c s) ∈ U) ∧
      let p := gnomonicInverse ∘ c
      let gamma := planarGradient (fun q => G q + J q) ∘ p
      ContDiff ℝ ∞ p ∧ Periodic p P ∧
        ContDiff ℝ ∞ gamma ∧ Periodic gamma P ∧
        HasPositiveArgumentTurn (angularDescentComplex ∘ p) P ∧
        HasPositiveArgumentTurn (angularDescentComplex ∘ gamma) P ∧
        (∀ s, p s ≠ 0) ∧ (∀ s, gamma s ≠ 0) := by
  let p0 : ℝ → Coord := gnomonicInverse ∘ ζ
  let g0 : ℝ → Coord := planarGradient G ∘ p0
  let Bp : ℝ → ℂ := angularDescentComplex ∘ p0
  let Bg : ℝ → ℂ := angularDescentComplex ∘ g0
  have hp0 : ContDiff ℝ ∞ p0 := by
    rw [contDiff_iff_contDiffAt]
    intro s
    exact (gnomonicInverse_contDiffAt (hnorth s).ne').comp s hζ.contDiffAt
  have hgrad := planarGradient_contDiffOn hG hU
  have hg0 : ContDiff ℝ ∞ g0 := by
    rw [contDiff_iff_contDiffAt]
    intro s
    exact ((hgrad _ (hsource s)).contDiffAt (hU.mem_nhds (hsource s))).comp s hp0.contDiffAt
  have hBp : ContDiff ℝ ∞ Bp := angularDescentComplex_contDiff.comp hp0
  have hBg : ContDiff ℝ ∞ Bg := angularDescentComplex_contDiff.comp hg0
  have hp0P : Periodic p0 P := by
    intro s
    change gnomonicInverse (ζ (s + P)) = gnomonicInverse (ζ s)
    rw [hζP s]
  have hg0P : Periodic g0 P := by
    intro s
    change planarGradient G (p0 (s + P)) = planarGradient G (p0 s)
    rw [hp0P s]
  have hBpP : Periodic Bp P := by
    intro s
    change angularDescentComplex (p0 (s + P)) = angularDescentComplex (p0 s)
    rw [hp0P s]
  have hBgP : Periodic Bg P := by
    intro s
    change angularDescentComplex (g0 (s + P)) = angularDescentComplex (g0 s)
    rw [hg0P s]
  obtain ⟨ep,hep,hpt⟩ := positiveExit_exists_argumentTurn_C0_threshold
    hP hBp hBpP hpnz hpturn
  obtain ⟨eg,heg,hgt⟩ := positiveExit_exists_argumentTurn_C0_threshold
    hP hBg hBgP hgnz hgturn
  let O : Set ExitAmbientTurnState := {x |
    0 < x.2.1 2 ∧ gnomonicInverse x.2.1 ∈ U ∧
      ‖angularDescentComplex (gnomonicInverse x.2.1) - Bp x.1‖ < ep ∧
      ‖angularDescentComplex (planarGradient G (gnomonicInverse x.2.1) + x.2.2) - Bg x.1‖ < eg}
  have hO : IsOpen O := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    have cu : ContinuousAt (fun y : ExitAmbientTurnState => y.2.1) x :=
      (continuous_fst.comp continuous_snd).continuousAt
    have cq : ContinuousAt (fun y : ExitAmbientTurnState => gnomonicInverse y.2.1) x := by
      have hcomp := (gnomonicInverse_contDiffAt hx.1.ne').continuousAt.comp (x := x) cu
      simpa only [Function.comp_def] using hcomp
    have cg : ContinuousAt (fun y : ExitAmbientTurnState =>
        planarGradient G (gnomonicInverse y.2.1)) x := by
      apply continuousAt_pi.mpr
      intro j
      change ContinuousAt (fun y : ExitAmbientTurnState =>
        coordPartial j G (gnomonicInverse y.2.1)) x
      have hcomp := (((partial_contDiffOn hG hU j) _ hx.2.1).contDiffAt
        (hU.mem_nhds hx.2.1)).continuousAt.comp (x := x) cq
      simpa only [Function.comp_def] using hcomp
    have cv : ContinuousAt (fun y : ExitAmbientTurnState => y.2.2) x :=
      (continuous_snd.comp continuous_snd).continuousAt
    have cbp : ContinuousAt (fun y : ExitAmbientTurnState => Bp y.1) x :=
      (hBp.continuous.comp continuous_fst).continuousAt
    have cbg : ContinuousAt (fun y : ExitAmbientTurnState => Bg y.1) x :=
      (hBg.continuous.comp continuous_fst).continuousAt
    have cp : ContinuousAt (fun y : ExitAmbientTurnState =>
        angularDescentComplex (gnomonicInverse y.2.1)) x := by
      have hcomp := angularDescentComplex_contDiff.continuous.continuousAt.comp (x := x) cq
      simpa only [Function.comp_def] using hcomp
    have cgp : ContinuousAt (fun y : ExitAmbientTurnState =>
        angularDescentComplex (planarGradient G (gnomonicInverse y.2.1) + y.2.2)) x := by
      have hcomp := angularDescentComplex_contDiff.continuous.continuousAt.comp
        (x := x) (cg.add cv)
      simpa only [Function.comp_def, Pi.add_apply] using hcomp
    have c2 := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) (2 : Fin 3)).continuous.continuousAt.comp
      (x := x) cu
    have h1 := c2.preimage_mem_nhds (Ioi_mem_nhds hx.1)
    have h2 := cq.preimage_mem_nhds (hU.mem_nhds hx.2.1)
    have h3 := (cp.sub cbp).norm.preimage_mem_nhds (Iio_mem_nhds hx.2.2.1)
    have h4 := (cgp.sub cbg).norm.preimage_mem_nhds (Iio_mem_nhds hx.2.2.2)
    exact inter_mem h1 (inter_mem h2 (inter_mem h3 h4))
  let j0 : ℝ → ExitAmbientTurnState := fun s => (s,(ζ s,0))
  have hj0 : Continuous j0 :=
    continuous_id.prodMk (hζ.continuous.prodMk continuous_const)
  have hbase : ∀ s, j0 s ∈ O := by
    intro s
    refine ⟨hnorth s,hsource s,?_,?_⟩
    · simpa only [j0,Bp,p0,Function.comp_apply,sub_self,norm_zero] using hep
    · simpa only [j0,Bg,g0,p0,Function.comp_apply,add_zero,sub_self,norm_zero] using heg
  have hK : IsCompact (j0 '' Icc (0 : ℝ) P) := isCompact_Icc.image hj0
  obtain ⟨eps,heps,he⟩ := hK.exists_thickening_subset_open hO (by
    rintro _ ⟨s,_,rfl⟩
    exact hbase s)
  refine ⟨eps,heps,eps,heps,?_⟩
  intro J c hJ hc hcP hbudget hclose
  have hzero : ∀ s ∈ Icc (0 : ℝ) P, (s,(c s,(0 : Coord))) ∈ O := by
    intro s hs
    apply he
    apply Metric.mem_thickening_iff.mpr
    refine ⟨j0 s,⟨s,hs,rfl⟩,?_⟩
    dsimp only [j0]
    rw [Prod.dist_eq, Prod.dist_eq]
    simpa only [dist_self, dist_eq_norm, sub_self, norm_zero] using
      max_lt heps (max_lt (hclose s hs) heps)
  have hdomain : ∀ s, 0 < c s 2 ∧ gnomonicInverse (c s) ∈ U := by
    intro s
    obtain ⟨n,hn,_⟩ := existsUnique_sub_zsmul_mem_Ico hP s 0
    simp only [mem_Ico,zero_add] at hn
    have hh := hzero (s - n • P) ⟨hn.1,hn.2.le⟩
    have hcs : c (s - n • P) = c s := hcP.sub_zsmul_eq n
    exact hcs ▸ ⟨hh.1,hh.2.1⟩
  have hsmall : ∀ s ∈ Icc (0 : ℝ) P,
      (s,(c s,planarGradient J (gnomonicInverse (c s)))) ∈ O := by
    intro s hs
    have hb := hbudget _ (hdomain s).2
    have hjnorm := (positiveExit_gradient_jet_norm_le_coordinateC2Size hJ
      (gnomonicInverse (c s))).1.trans_lt hb
    apply he
    apply Metric.mem_thickening_iff.mpr
    refine ⟨j0 s,⟨s,hs,rfl⟩,?_⟩
    dsimp only [j0]
    rw [Prod.dist_eq, Prod.dist_eq]
    simpa only [dist_self, dist_eq_norm, sub_zero] using
      max_lt heps (max_lt (hclose s hs) hjnorm)
  let p : ℝ → Coord := gnomonicInverse ∘ c
  let gamma : ℝ → Coord := planarGradient (fun q => G q + J q) ∘ p
  have hp : ContDiff ℝ ∞ p := by
    rw [contDiff_iff_contDiffAt]
    intro s
    exact (gnomonicInverse_contDiffAt (hdomain s).1.ne').comp s hc.contDiffAt
  have hGe : ContDiffOn ℝ ∞ (fun q => G q + J q) U := hG.add hJ.contDiffOn
  have hgamma : ContDiff ℝ ∞ gamma := by
    rw [contDiff_iff_contDiffAt]
    intro s
    exact (((planarGradient_contDiffOn hGe hU) _ (hdomain s).2).contDiffAt
      (hU.mem_nhds (hdomain s).2)).comp s hp.contDiffAt
  have hpP : Periodic p P := by
    intro s
    change gnomonicInverse (c (s + P)) = gnomonicInverse (c s)
    rw [hcP s]
  have hgammaP : Periodic gamma P := by
    intro s
    change planarGradient (fun q => G q + J q) (p (s + P)) =
      planarGradient (fun q => G q + J q) (p s)
    rw [hpP s]
  have hpcP : Periodic (angularDescentComplex ∘ p) P := by
    intro s
    change angularDescentComplex (p (s + P)) = angularDescentComplex (p s)
    rw [hpP s]
  have hgcP : Periodic (angularDescentComplex ∘ gamma) P := by
    intro s
    change angularDescentComplex (gamma (s + P)) = angularDescentComplex (gamma s)
    rw [hgammaP s]
  have hpclose : ∀ s ∈ Icc (0 : ℝ) P,
      ‖(angularDescentComplex ∘ p) s - Bp s‖ < ep := by
    intro s hs
    exact (hsmall s hs).2.2.1
  have hgclose : ∀ s ∈ Icc (0 : ℝ) P,
      ‖(angularDescentComplex ∘ gamma) s - Bg s‖ < eg := by
    intro s hs
    have hh := (hsmall s hs).2.2.2
    change ‖angularDescentComplex (planarGradient G (gnomonicInverse (c s)) +
      planarGradient J (gnomonicInverse (c s))) - Bg s‖ < eg at hh
    change ‖angularDescentComplex (planarGradient (fun q => G q + J q)
      (gnomonicInverse (c s))) - Bg s‖ < eg
    rw [exitAmbientTurn_gradient_add hG hU hJ (hdomain s).2]
    exact hh
  obtain ⟨hpturn',hpnz'⟩ := hpt (angularDescentComplex ∘ p)
    (angularDescentComplex_contDiff.comp hp) hpcP hpclose
  obtain ⟨hgturn',hgnz'⟩ := hgt (angularDescentComplex ∘ gamma)
    (angularDescentComplex_contDiff.comp hgamma) hgcP hgclose
  refine ⟨hdomain,hp,hpP,hgamma,hgammaP,hpturn',hgturn',?_,?_⟩
  · intro s hs
    change p s = 0 at hs
    apply hpnz' s
    change angularDescentComplex (p s) = 0
    rw [hs]
    simp [angularDescentComplex]
  · intro s hs
    change gamma s = 0 at hs
    apply hgnz' s
    change angularDescentComplex (gamma s) = 0
    rw [hs]
    simp [angularDescentComplex]

end
end TightVer401