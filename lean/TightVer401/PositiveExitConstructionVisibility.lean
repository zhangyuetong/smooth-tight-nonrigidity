import TightVer401.PositiveExitConstructionContract
import TightVer401.PositiveExitConstructionFirstIntegral
import TightVer401.PositiveExitConstructionCentralTrace
import TightVer401.VisibilitySpeedStability
import TightVer401.FermiPeriodicity
import Mathlib.Algebra.Order.ToIntervalMod

/-! The actual complete-flow visibility margin is chosen before the protected
field. All six inequalities use the SAME raw Cartesian chart and gradient;
the inner pair follows the consumer's reverse/reflection and rotation order. -/
open scoped Manifold
namespace TightVer401
noncomputable section
open Set Filter MeasureTheory OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix ComplexConjugate RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

private def exitVisibilityComplexCLM : Coord →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (ContinuousLinearMap.proj (R := ℝ) 0) +
    Complex.I • (Complex.ofRealCLM.comp (ContinuousLinearMap.proj (R := ℝ) 1))

private theorem exitVisibilityComplexCLM_eq :
    (exitVisibilityComplexCLM : Coord → ℂ) = positiveExitComplexPoint := by
  ext q
  apply Complex.ext <;> simp [exitVisibilityComplexCLM, positiveExitComplexPoint,
    Complex.mul_re, Complex.mul_im]

private theorem exitVisibility_complex_hasDerivAt {f : ℝ → Coord} {v : Coord} {s : ℝ}
    (hf : HasDerivAt f v s) :
    HasDerivAt (positiveExitComplexTrace f) (positiveExitComplexPoint v) s := by
  have h := exitVisibilityComplexCLM.hasFDerivAt.comp_hasDerivAt s hf
  simpa only [exitVisibilityComplexCLM_eq, positiveExitComplexTrace] using h

private theorem exitVisibility_null_smooth {T : ℝ} (d : PeriodicRuledFrame T) :
    ContDiff ℝ ∞ (positiveExitRawNullDirection d) := by
  have hk' := (contDiff_infty_iff_deriv.mp d.smooth_k).2
  have hτ' := (contDiff_infty_iff_deriv.mp d.smooth_τ).2
  have hLambda : ContDiff ℝ ∞ (ruledLambda d.τ) := hτ'.div d.smooth_τ d.torsion_ne_zero
  have hD : ContDiff ℝ ∞ (ruledD d.k d.τ) := hk'.sub (d.smooth_k.mul hLambda)
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ (fun _ : Coord => (1 : ℝ))
    exact contDiff_const
  · change ContDiff ℝ ∞ (fun q : Coord =>
      -(q 1 / 2) * (ruledLambda d.τ (q 0) + q 1 * ruledD d.k d.τ (q 0)))
    exact ((contDiff_apply ℝ ℝ 1).div_const 2).neg.mul
      ((hLambda.comp (contDiff_apply ℝ ℝ 0)).add
        ((contDiff_apply ℝ ℝ 1).mul (hD.comp (contDiff_apply ℝ ℝ 0))))

/-- Actual pointwise visibility of the characteristic direction, including
both reflected/reversed derivatives required by the dual inner exit. -/
def positiveExitRawVisibility {T : ℝ} (d : PeriodicRuledFrame T)
    (G : Coord → ℝ) (q : Coord) : Prop :=
  let P := identityBandCentralCoordinates d
  let Γ := planarGradient G ∘ P
  let p := positiveExitComplexPoint (P q)
  let g := positiveExitComplexPoint (Γ q)
  let dp := positiveExitComplexPoint (fderiv ℝ P q (positiveExitRawNullDirection d q))
  let dg := positiveExitComplexPoint (fderiv ℝ Γ q (positiveExitRawNullDirection d q))
  (1 / 4 : ℝ) < ‖Complex.I * g‖ ∧
    0 < inner ℝ dp (corrugatedVisibilityDirection (1 / 4) (Complex.I * g)) ∧
    0 < inner ℝ (Complex.I * dg) (corrugatedVisibilityDirection (1 / 4) (Complex.I * g)) ∧
    (4 / 5 : ℝ) < ‖Complex.I * conj p‖ ∧
    0 < inner ℝ (-conj dg) (corrugatedVisibilityDirection (4 / 5) (Complex.I * conj p)) ∧
    0 < inner ℝ (-Complex.I * conj dp)
      (corrugatedVisibilityDirection (4 / 5) (Complex.I * conj p))

private theorem exitVisibility_central_derivative {f : Coord → Coord} {s : ℝ}
    (hf : DifferentiableAt ℝ f (![s, 0] : Coord)) :
    HasDerivAt (fun r => f (![r, 0] : Coord))
      (fderiv ℝ f (![s, 0] : Coord) (![1, 0] : Coord)) s := by
  exact hf.hasFDerivAt.comp_hasDerivAt s (ruled_graph_hasDerivAt (hasDerivAt_const s (0 : ℝ)))

/-- Actual central visible pairs imply strict raw characteristic visibility
at height zero; no visible complete leaf is an input. -/
theorem positiveExitRawVisibility_central {T w : ℝ} (d : PeriodicRuledFrame T)
    {G : Coord → ℝ} {U : Set Coord} (hw : 0 < w) (hU : IsOpen U)
    (hG : ContDiffOn ℝ ∞ G U)
    (hP : ContDiffOn ℝ ∞ (identityBandCentralCoordinates d) (identityBandCentralRawDomain w))
    (hPU : MapsTo (identityBandCentralCoordinates d) (identityBandCentralRawDomain w) U)
    (houter : ComplexVisiblePair (1 / 4)
      (positiveExitComplexTrace (fun s => identityBandCentralCoordinates d ![s, 0]))
      (fun s => Complex.I * positiveExitComplexPoint
        (planarGradient G (identityBandCentralCoordinates d ![s, 0]))))
    (hinner : ComplexVisiblePair (4 / 5)
      (corrugatedReverseReflect (positiveExitComplexTrace
        (fun s => planarGradient G (identityBandCentralCoordinates d ![s, 0]))))
      (fun s => Complex.I * corrugatedReverseReflect
        (positiveExitComplexTrace (fun s => identityBandCentralCoordinates d ![s, 0])) s))
    (s : ℝ) : positiveExitRawVisibility d G (![s, 0] : Coord) := by
  let P := identityBandCentralCoordinates d
  let Γ := planarGradient G ∘ P
  have hs : (![s, 0] : Coord) ∈ identityBandCentralRawDomain w := by
    change -w < (0 : ℝ) ∧ (0 : ℝ) < w
    constructor <;> linarith
  have hdP := ((hP _ hs).contDiffAt ((identityBandCentralRawDomain_isOpen w).mem_nhds hs)).differentiableAt (by simp)
  have hΓ : ContDiffOn ℝ ∞ Γ (identityBandCentralRawDomain w) :=
    (planarGradient_contDiffOn hG hU).comp hP hPU
  have hdΓ := ((hΓ _ hs).contDiffAt ((identityBandCentralRawDomain_isOpen w).mem_nhds hs)).differentiableAt (by simp)
  have hp := exitVisibility_complex_hasDerivAt (exitVisibility_central_derivative hdP)
  have hg := exitVisibility_complex_hasDerivAt (exitVisibility_central_derivative hdΓ)
  have hgo := hg.const_mul Complex.I
  have hgr := corrugatedReverseReflect_hasDerivAt (t := -s) (by simpa using hg)
  have hpr := (corrugatedReverseReflect_hasDerivAt (t := -s) (by simpa using hp)).const_mul Complex.I
  have ho := houter s
  have hi := hinner (-s)
  have hgoEq := hgo.deriv
  have hgrEq := hgr.deriv
  have hprEq := hpr.deriv
  simp only [positiveExitComplexTrace, Γ, Function.comp_apply] at hgoEq hgrEq hprEq
  rw [hp.deriv, hgoEq] at ho
  change deriv (corrugatedReverseReflect (positiveExitComplexTrace
    (fun r => planarGradient G (identityBandCentralCoordinates d ![r, 0])))) (-s) = _ at hgrEq
  change deriv (fun r => Complex.I * corrugatedReverseReflect
    (positiveExitComplexTrace (fun r => identityBandCentralCoordinates d ![r, 0])) r) (-s) = _ at hprEq
  rw [hgrEq, hprEq] at hi
  have hn : positiveExitRawNullDirection d (![s, 0] : Coord) = (![1, 0] : Coord) := by
    simp [positiveExitRawNullDirection]
  simpa [positiveExitRawVisibility, P, Γ, hn, corrugatedReverseReflect,
    positiveExitComplexTrace, mul_neg, neg_mul] using
      And.intro ho.1 (And.intro ho.2.1 (And.intro ho.2.2 hi))

/-- The true source and gradient derivatives evaluated on the actual
characteristic tangent are smooth throughout the raw two-sided source. -/
theorem positiveExitRawVisibility_directional_smooth {T w : ℝ} (d : PeriodicRuledFrame T)
    {G : Coord → ℝ} {U : Set Coord} (hU : IsOpen U)
    (hG : ContDiffOn ℝ ∞ G U)
    (hP : ContDiffOn ℝ ∞ (identityBandCentralCoordinates d) (identityBandCentralRawDomain w))
    (hPU : MapsTo (identityBandCentralCoordinates d) (identityBandCentralRawDomain w) U) :
    ContDiffOn ℝ ∞ (fun q => fderiv ℝ (identityBandCentralCoordinates d) q
      (positiveExitRawNullDirection d q)) (identityBandCentralRawDomain w) ∧
    ContDiffOn ℝ ∞ (fun q => fderiv ℝ (planarGradient G ∘ identityBandCentralCoordinates d) q
      (positiveExitRawNullDirection d q)) (identityBandCentralRawDomain w) := by
  have hD := identityBandCentralRawDomain_isOpen w
  have hΓ := (planarGradient_contDiffOn hG hU).comp hP hPU
  exact ⟨(hP.fderiv_of_isOpen hD (by simp)).clm_apply
      (exitVisibility_null_smooth d).contDiffOn,
    (hΓ.fderiv_of_isOpen hD (by simp)).clm_apply
      (exitVisibility_null_smooth d).contDiffOn⟩
/-- The strict actual inequalities define an open subset of the smooth
raw two-sided Cartesian source, rather than a granted visibility collar. -/
theorem positiveExitRawVisibility_isOpen {T w : ℝ} (d : PeriodicRuledFrame T)
    {G : Coord → ℝ} {U : Set Coord} (hU : IsOpen U)
    (hG : ContDiffOn ℝ ∞ G U)
    (hP : ContDiffOn ℝ ∞ (identityBandCentralCoordinates d) (identityBandCentralRawDomain w))
    (hPU : MapsTo (identityBandCentralCoordinates d) (identityBandCentralRawDomain w) U) :
    IsOpen {q | q ∈ identityBandCentralRawDomain w ∧ positiveExitRawVisibility d G q} := by
  let P := identityBandCentralCoordinates d
  let Γ := planarGradient G ∘ P
  let n := positiveExitRawNullDirection d
  have hD := identityBandCentralRawDomain_isOpen w
  have hΓ : ContDiffOn ℝ ∞ Γ (identityBandCentralRawDomain w) :=
    (planarGradient_contDiffOn hG hU).comp hP hPU
  have hp := hP.continuousOn
  have hg := hΓ.continuousOn
  have hdp := (hP.continuousOn_fderiv_of_isOpen hD (by simp)).clm_apply
    (exitVisibility_null_smooth d).continuous.continuousOn
  have hdg := (hΓ.continuousOn_fderiv_of_isOpen hD (by simp)).clm_apply
    (exitVisibility_null_smooth d).continuous.continuousOn
  have hcomplex : Continuous positiveExitComplexPoint := by
    rw [← exitVisibilityComplexCLM_eq]
    exact exitVisibilityComplexCLM.continuous
  apply isOpen_iff_mem_nhds.mpr
  intro q hq
  have hn := hD.mem_nhds hq.1
  have cp := hcomplex.continuousAt.comp ((hp q hq.1).continuousAt hn)
  have cg := hcomplex.continuousAt.comp ((hg q hq.1).continuousAt hn)
  have cdp := hcomplex.continuousAt.comp ((hdp q hq.1).continuousAt hn)
  have cdg := hcomplex.continuousAt.comp ((hdg q hq.1).continuousAt hn)
  have co : ContinuousAt (fun z => Complex.I * positiveExitComplexPoint (Γ z)) q :=
    continuousAt_const.mul cg
  have ci : ContinuousAt (fun z => Complex.I * conj (positiveExitComplexPoint (P z))) q :=
    continuousAt_const.mul cp.star
  rcases hq.2 with ⟨ho, hop, hog, hi, hig, hip⟩
  have hzo : (Complex.I * positiveExitComplexPoint (Γ q)) ≠ 0 :=
    norm_pos_iff.mp (lt_trans (by norm_num) ho)
  have hzi : (Complex.I * conj (positiveExitComplexPoint (P q))) ≠ 0 :=
    norm_pos_iff.mp (lt_trans (by norm_num) hi)
  have cvo : ContinuousAt (fun z => corrugatedVisibilityDirection (1 / 4)
      (Complex.I * positiveExitComplexPoint (Γ z))) q :=
    (visibilityDirection_continuousAt (1 / 4) hzo).comp (x := q) (f := fun z : Coord => Complex.I * positiveExitComplexPoint (Γ z)) co
  have cvi : ContinuousAt (fun z => corrugatedVisibilityDirection (4 / 5)
      (Complex.I * conj (positiveExitComplexPoint (P z)))) q :=
    (visibilityDirection_continuousAt (4 / 5) hzi).comp (x := q) (f := fun z : Coord => Complex.I * conj (positiveExitComplexPoint (P z))) ci
  have c2 : ContinuousAt (fun z => inner ℝ
      (positiveExitComplexPoint (fderiv ℝ P z (n z)))
      (corrugatedVisibilityDirection (1 / 4) (Complex.I * positiveExitComplexPoint (Γ z)))) q :=
    cdp.inner cvo
  have cdgo : ContinuousAt (fun z => Complex.I * positiveExitComplexPoint
      (fderiv ℝ Γ z (n z))) q := continuousAt_const.mul cdg
  have c3 : ContinuousAt (fun z => inner ℝ
      (Complex.I * positiveExitComplexPoint (fderiv ℝ Γ z (n z)))
      (corrugatedVisibilityDirection (1 / 4) (Complex.I * positiveExitComplexPoint (Γ z)))) q :=
    cdgo.inner cvo
  have c5 : ContinuousAt (fun z => inner ℝ
      (-conj (positiveExitComplexPoint (fderiv ℝ Γ z (n z))))
      (corrugatedVisibilityDirection (4 / 5) (Complex.I * conj (positiveExitComplexPoint (P z))))) q :=
    cdg.star.neg.inner cvi
  have cdpi : ContinuousAt (fun z => -Complex.I * conj (positiveExitComplexPoint
      (fderiv ℝ P z (n z)))) q := continuousAt_const.mul cdp.star
  have c6 : ContinuousAt (fun z => inner ℝ
      (-Complex.I * conj (positiveExitComplexPoint (fderiv ℝ P z (n z))))
      (corrugatedVisibilityDirection (4 / 5) (Complex.I * conj (positiveExitComplexPoint (P z))))) q :=
    cdpi.inner cvi
  have h1 := co.norm.preimage_mem_nhds (Ioi_mem_nhds ho)
  have h2 := c2.preimage_mem_nhds (Ioi_mem_nhds hop)
  have h3 := c3.preimage_mem_nhds (Ioi_mem_nhds hog)
  have h4 := ci.norm.preimage_mem_nhds (Ioi_mem_nhds hi)
  have h5 := c5.preimage_mem_nhds (Ioi_mem_nhds hig)
  have h6 := c6.preimage_mem_nhds (Ioi_mem_nhds hip)
  exact inter_mem hn (inter_mem h1 (inter_mem h2 (inter_mem h3
    (inter_mem h4 (inter_mem h5 h6)))))

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 200000 in
private theorem exitVisibility_raw_periodic {T : ℝ} (d : PeriodicRuledFrame T)
    (G : Coord → ℝ) (q : Coord) :
    positiveExitRawVisibility d G (q + Pi.single 0 T) ↔ positiveExitRawVisibility d G q := by
  let P := identityBandCentralCoordinates d
  let Γ := planarGradient G ∘ P
  have hp (z : Coord) : P (z + Pi.single 0 T) = P z := by
    have h0 : (z + (Pi.single (0 : Fin 2) T : Coord)) (0 : Fin 2) = z 0 + T := by rfl
    have h1 : (z + (Pi.single (0 : Fin 2) T : Coord)) (1 : Fin 2) = z 1 := by
      change z 1 + (0 : ℝ) = z 1
      exact add_zero _
    have hN : d.rawGaussMap (z + (Pi.single (0 : Fin 2) T : Coord)) = d.rawGaussMap z := by
      simp only [PeriodicRuledFrame.rawGaussMap, h0, h1, d.period_T (z 0),
        d.period_n (z 0), d.period_k (z 0), d.period_τ (z 0)]
    exact congrArg gnomonicInverse hN
  have hg (z : Coord) : Γ (z + Pi.single 0 T) = Γ z := by
    dsimp only [Γ, Function.comp_apply]
    exact congrArg (planarGradient G) (hp z)
  have hdp (z : Coord) : fderiv ℝ P (z + Pi.single 0 T) = fderiv ℝ P z := by
    have h := fderiv_comp_add_right (𝕜 := ℝ) (f := P) (x := z) (Pi.single 0 T)
    have he : (fun y : Coord => P (y + Pi.single 0 T)) = P := funext hp
    exact h.symm.trans (congrArg (fun f : Coord → Coord => fderiv ℝ f z) he)
  have hdg (z : Coord) : fderiv ℝ Γ (z + Pi.single 0 T) = fderiv ℝ Γ z := by
    have h := fderiv_comp_add_right (𝕜 := ℝ) (f := Γ) (x := z) (Pi.single 0 T)
    have he : (fun y : Coord => Γ (y + Pi.single 0 T)) = Γ := funext hg
    exact h.symm.trans (congrArg (fun f : Coord → Coord => fderiv ℝ f z) he)
  have hn : positiveExitRawNullDirection d (q + Pi.single 0 T) = positiveExitRawNullDirection d q := by
    have h0 : (q + (Pi.single (0 : Fin 2) T : Coord)) (0 : Fin 2) = q 0 + T := by rfl
    have h1 : (q + (Pi.single (0 : Fin 2) T : Coord)) (1 : Fin 2) = q 1 := by
      change q 1 + (0 : ℝ) = q 1
      exact add_zero _
    unfold positiveExitRawNullDirection
    rw [h0, h1]
    simp only [ruledD, ruledLambda, d.period_τ (q 0), d.period_k (q 0),
      deriv_periodic d.period_k (q 0), deriv_periodic d.period_τ (q 0)]
  dsimp only [Γ, P] at hp hg hdp hdg
  simp only [positiveExitRawVisibility, hp, hg, hdp, hdg, hn]

/-- Compactness of one period and actual periodic derivatives produce a
uniform two-sided raw visibility strip. This width precedes field selection. -/
theorem positiveExitRawVisibility_exists_strip {T w : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T) {G : Coord → ℝ} {U : Set Coord}
    (hw : 0 < w) (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U)
    (hP : ContDiffOn ℝ ∞ (identityBandCentralCoordinates d) (identityBandCentralRawDomain w))
    (hPU : MapsTo (identityBandCentralCoordinates d) (identityBandCentralRawDomain w) U)
    (hcentral : ∀ s : ℝ, positiveExitRawVisibility d G (![s, 0] : Coord)) :
    ∃ ρ > 0, ρ < w ∧ ∀ s u : ℝ, |u| < ρ →
      (![s, u] : Coord) ∈ identityBandCentralRawDomain w ∧ positiveExitRawVisibility d G ![s, u] := by
  let V : Set Coord := {q | q ∈ identityBandCentralRawDomain w ∧ positiveExitRawVisibility d G q}
  have hV := positiveExitRawVisibility_isOpen d hU hG hP hPU
  let K : Set Coord := (fun s : ℝ => (![s, 0] : Coord)) '' Icc 0 T
  have hpath : Continuous (fun s : ℝ => (![s, 0] : Coord)) := by
    apply continuous_pi
    intro i
    fin_cases i
    · change Continuous (fun s : ℝ => s)
      exact continuous_id
    · change Continuous (fun _ : ℝ => (0 : ℝ))
      exact continuous_const
  have hK : IsCompact K := isCompact_Icc.image hpath
  have hKV : K ⊆ V := by
    rintro _ ⟨s, _, rfl⟩
    refine ⟨?_, hcentral s⟩
    change -w < (0 : ℝ) ∧ (0 : ℝ) < w
    constructor <;> linarith
  obtain ⟨ε, hε, hεV⟩ := hK.exists_thickening_subset_open hV hKV
  refine ⟨min ε (w / 2), lt_min hε (half_pos hw),
    (min_le_right _ _).trans_lt (half_lt_self hw), ?_⟩
  intro s u hu
  let r := toIcoMod (Fact.out : 0 < T) 0 s
  have hr : r ∈ Icc 0 T := Ico_subset_Icc_self (toIcoMod_mem_Ico' (Fact.out : 0 < T) s)
  have hm : (![r, u] : Coord) ∈ V := by
    apply hεV
    apply Metric.mem_thickening_iff.mpr
    refine ⟨![r, 0], ⟨r, hr, rfl⟩, ?_⟩
    rw [dist_eq_norm]
    have hnorm : ‖(![r, u] : Coord) - ![r, 0]‖ ≤ |u| := by
      apply (pi_norm_le_iff_of_nonneg (abs_nonneg u)).mpr
      intro i
      fin_cases i <;> simp
    exact hnorm.trans_lt (hu.trans_le (min_le_left _ _))
  have hperiod : Function.Periodic (fun t : ℝ => (![t, u] : Coord) ∈ V) T := by
    intro t
    have he : (![t + T, u] : Coord) = ![t, u] + Pi.single 0 T := by
      ext i
      fin_cases i <;> simp
    change ((![t + T, u] : Coord) ∈ V) = ((![t, u] : Coord) ∈ V)
    rw [he]
    change (_ ∧ _) = (_ ∧ _)
    apply propext
    have hd : ((![t, u] : Coord) + Pi.single 0 T ∈ identityBandCentralRawDomain w) ↔
        ((![t, u] : Coord) ∈ identityBandCentralRawDomain w) := by
      have hs : (Pi.single (0 : Fin 2) T : Coord) (1 : Fin 2) = 0 := by simp
      change (-w < ((![t, u] : Coord) + (Pi.single (0 : Fin 2) T : Coord)) (1 : Fin 2) ∧
        ((![t, u] : Coord) + (Pi.single (0 : Fin 2) T : Coord)) (1 : Fin 2) < w) ↔ (-w < u ∧ u < w)
      simp only [Pi.add_apply, hs, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons, add_zero]
    exact and_congr hd (exitVisibility_raw_periodic d G ![t, u])
  have heq : ((![r, u] : Coord) ∈ V) = ((![s, u] : Coord) ∈ V) := by
    exact hperiod.sub_zsmul_eq (toIcoDiv (Fact.out : 0 < T) 0 s)
  change (![s, u] : Coord) ∈ V
  exact heq ▸ hm

private theorem exitVisibility_actual_flow {T w : ℝ} (d : PeriodicRuledFrame T)
    {G : Coord → ℝ} {U : Set Coord} (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U)
    (hP : ContDiffOn ℝ ∞ (identityBandCentralCoordinates d) (identityBandCentralRawDomain w))
    (hPU : MapsTo (identityBandCentralCoordinates d) (identityBandCentralRawDomain w) U)
    {u : ℝ → ℝ}
    (hu : ∀ s, (![s, u s] : Coord) ∈ identityBandCentralRawDomain w)
    (hode : ∀ s, HasDerivAt u
      (-(u s / 2) * (ruledLambda d.τ s + u s * ruledD d.k d.τ s)) s)
    (hvisible : ∀ s, positiveExitRawVisibility d G (![s, u s] : Coord)) :
    ComplexVisiblePair (1 / 4)
      (positiveExitComplexTrace (fun s => identityBandCentralCoordinates d ![s, u s]))
      (fun s => Complex.I * positiveExitComplexPoint
        (planarGradient G (identityBandCentralCoordinates d ![s, u s]))) ∧
    ComplexVisiblePair (4 / 5)
      (corrugatedReverseReflect (positiveExitComplexTrace
        (fun s => planarGradient G (identityBandCentralCoordinates d ![s, u s]))))
      (fun s => Complex.I * corrugatedReverseReflect
        (positiveExitComplexTrace (fun s => identityBandCentralCoordinates d ![s, u s])) s) := by
  let P := identityBandCentralCoordinates d
  let Γ := planarGradient G ∘ P
  have hD := identityBandCentralRawDomain_isOpen w
  have hΓ : ContDiffOn ℝ ∞ Γ (identityBandCentralRawDomain w) :=
    (planarGradient_contDiffOn hG hU).comp hP hPU
  have hpath (s) : HasDerivAt (fun r => (![r, u r] : Coord))
      (positiveExitRawNullDirection d (![s, u s] : Coord)) s := by
    simpa only [positiveExitRawNullDirection, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons] using ruled_graph_hasDerivAt (hode s)
  have hp (s : ℝ) : HasDerivAt
      (positiveExitComplexTrace (fun r => identityBandCentralCoordinates d ![r, u r]))
      (positiveExitComplexPoint (fderiv ℝ P ![s, u s]
        (positiveExitRawNullDirection d ![s, u s]))) s := by
    simpa only [Function.comp_def] using exitVisibility_complex_hasDerivAt
      ((((hP _ (hu s)).contDiffAt (hD.mem_nhds (hu s))).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt s (hpath s))
  have hg (s : ℝ) : HasDerivAt
      (positiveExitComplexTrace (fun r => planarGradient G (identityBandCentralCoordinates d ![r, u r])))
      (positiveExitComplexPoint (fderiv ℝ Γ ![s, u s]
        (positiveExitRawNullDirection d ![s, u s]))) s := by
    simpa only [Function.comp_def, Γ, P] using exitVisibility_complex_hasDerivAt
      ((((hΓ _ (hu s)).contDiffAt (hD.mem_nhds (hu s))).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt s (hpath s))
  constructor
  · intro s
    have ho := (hvisible s)
    rcases ho with ⟨hr, hpv, hgv, _⟩
    have hgo := (hg s).const_mul Complex.I
    have hgoEq := hgo.deriv
    simp only [positiveExitComplexTrace, Γ, Function.comp_apply] at hgoEq
    rw [(hp s).deriv, hgoEq]
    exact ⟨hr, hpv, hgv⟩
  · intro s
    have hi := hvisible (-s)
    rcases hi with ⟨_, _, _, hr, hgv, hpv⟩
    have hgr := corrugatedReverseReflect_hasDerivAt (hg (-s))
    have hpr := (corrugatedReverseReflect_hasDerivAt (hp (-s))).const_mul Complex.I
    have hgrEq := hgr.deriv
    have hprEq := hpr.deriv
    simp only [positiveExitComplexTrace, Γ, Function.comp_apply] at hgrEq hprEq
    change deriv (corrugatedReverseReflect (positiveExitComplexTrace
      (fun r => planarGradient G (identityBandCentralCoordinates d ![r, u r])))) s = _ at hgrEq
    change deriv (fun r => Complex.I * corrugatedReverseReflect
      (positiveExitComplexTrace (fun r => identityBandCentralCoordinates d ![r, u r])) r) s = _ at hprEq
    rw [hgrEq, hprEq]
    simpa only [positiveExitRawVisibility, P, Γ, corrugatedReverseReflect,
      positiveExitComplexTrace, Function.comp_apply, mul_neg, neg_mul] using And.intro hr (And.intro hgv hpv)

/-- The complete-flow initial margin is derived before any protected field.
Every positive initial height below δ gives both actual visible pairs for
this SAME Cartesian potential, together with actual complete band containment. -/
theorem positiveExit_exists_visible_complete_flow_initial_margin
    {T w : ℝ} [Fact (0 < T)] (d : PeriodicRuledFrame T)
    (hb : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0)
    {G : Coord → ℝ} {U : Set Coord} (hw : 0 < w) (hU : IsOpen U)
    (hG : ContDiffOn ℝ ∞ G U)
    (hP : ContDiffOn ℝ ∞ (identityBandCentralCoordinates d) (identityBandCentralRawDomain w))
    (hPU : MapsTo (identityBandCentralCoordinates d) (identityBandCentralRawDomain w) U)
    (houter : ComplexVisiblePair (1 / 4)
      (positiveExitComplexTrace (fun s => identityBandCentralCoordinates d ![s, 0]))
      (fun s => Complex.I * positiveExitComplexPoint
        (planarGradient G (identityBandCentralCoordinates d ![s, 0]))))
    (hinner : ComplexVisiblePair (4 / 5)
      (corrugatedReverseReflect (positiveExitComplexTrace
        (fun s => planarGradient G (identityBandCentralCoordinates d ![s, 0]))))
      (fun s => Complex.I * corrugatedReverseReflect
        (positiveExitComplexTrace (fun s => identityBandCentralCoordinates d ![s, 0])) s)) :
    ∃ δ > 0, δ < w ∧ ∀ v ∈ Ioo (0 : ℝ) δ,
      let u := principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 v
      (∀ s, u s ∈ Ioo (0 : ℝ) w) ∧
      ComplexVisiblePair (1 / 4)
        (positiveExitComplexTrace (fun s => identityBandCentralCoordinates d ![s, u s]))
        (fun s => Complex.I * positiveExitComplexPoint
          (planarGradient G (identityBandCentralCoordinates d ![s, u s]))) ∧
      ComplexVisiblePair (4 / 5)
        (corrugatedReverseReflect (positiveExitComplexTrace
          (fun s => planarGradient G (identityBandCentralCoordinates d ![s, u s]))))
        (fun s => Complex.I * corrugatedReverseReflect
          (positiveExitComplexTrace (fun s => identityBandCentralCoordinates d ![s, u s])) s) := by
  obtain ⟨ρ, hρ, hρw, hstrip⟩ := positiveExitRawVisibility_exists_strip d hw hU hG hP hPU
    (positiveExitRawVisibility_central d hw hU hG hP hPU houter hinner)
  obtain ⟨δ, hδ, hδρ, hleaves⟩ := periodicRuledFrame_closed_asymptotic_leaves d hb 0 ρ hρ
  refine ⟨δ, hδ, hδρ.trans hρw, ?_⟩
  intro v hv
  obtain ⟨_, _, _, hu, hode, _⟩ := hleaves v hv.1 hv.2
  have hraw (s) := hstrip s
    (principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 v s)
    (by simpa only [abs_of_pos (hu s).1] using (hu s).2)
  refine ⟨fun s => ⟨(hu s).1, (hu s).2.trans hρw⟩, ?_⟩
  exact exitVisibility_actual_flow d hU hG hP hPU
    (fun s => (hraw s).1) hode (fun s => (hraw s).2)

end
end TightVer401