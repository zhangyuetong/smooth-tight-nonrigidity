import TightVer401.PositiveExitConstructionVisibility
import TightVer401.CorrugatedSeedBalancedOuter
import TightVer401.CorrugatedSeedBalancedSpatial
import TightVer401.IdentityBandCentralSupportPhysical
import TightVer401.IdentityBandProtectedBending
import TightVer401.IdentityBandBendingPullback

/-! Same corrected seed/frame/potential consumer. The complete visible-flow
margin is chosen FIRST, and the protected field is then constructed inside
that exact flow range. No old field is asserted to survive a width change. -/
open scoped Manifold
namespace TightVer401
noncomputable section
open Set Function Filter MeasureTheory OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff Topology Matrix ComplexConjugate RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

private theorem exitSeed_inner_I (v z : ℂ) :
    inner ℝ (Complex.I * v) (Complex.I * z) = inner ℝ v z := by
  simp only [corrugated_complex_inner, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im]
  ring

private theorem exitSeed_visible_rotate_I {R : ℝ} {p g : ℝ → ℂ}
    (h : ComplexVisiblePair R p g) (hp : ContDiff ℝ ∞ p) (hg : ContDiff ℝ ∞ g) :
    ComplexVisiblePair R (fun s => Complex.I * p s) (fun s => Complex.I * g s) := by
  intro s
  have hpd := (((hp.differentiable (by simp) s).hasDerivAt).const_mul Complex.I).deriv
  have hgd := (((hg.differentiable (by simp) s).hasDerivAt).const_mul Complex.I).deriv
  refine ⟨by simpa only [norm_mul, Complex.norm_I, one_mul] using (h s).1, ?_, ?_⟩
  · rw [hpd, corrugatedVisibilityDirection_rotate R (by simp : ‖Complex.I‖ = 1), exitSeed_inner_I]
    exact (h s).2.1
  · rw [hgd, corrugatedVisibilityDirection_rotate R (by simp : ‖Complex.I‖ = 1), exitSeed_inner_I]
    exact (h s).2.2

private theorem exitSeed_horizontal (u : Ambient) :
    positiveExitComplexPoint (identityBandPlanarHorizontalCLM u) = corrugatedAmbientHorizontal u := by
  apply Complex.ext <;> simp [positiveExitComplexPoint, identityBandPlanarHorizontalCLM,
    corrugatedAmbientHorizontal, ContinuousLinearMap.pi_apply, PiLp.proj_apply]

/-- The actual corrected seed produces the exact central visible pairs of
its actual Cartesian potential, including the consumer's inner rotation. -/
theorem positiveExit_seed_central_visible {T w N ell : ℝ}
    (d : PeriodicRuledFrame T) {ψ a : ℝ → ℝ} {G : Coord → ℝ}
    (hw : 0 < w) (hψ : ContDiff ℝ ∞ ψ) (ha : ContDiff ℝ ∞ a)
    (hapos : ∀ r, 0 < a r) (S : ℝ ≃ₜ ℝ)
    (hS : (S : ℝ → ℝ) = rawPrimitive a) (hSs : ContDiff ℝ ∞ S.symm)
    (hγ : d.γ = corrugatedSeedBalancedSpatial N ψ ell a ∘ S.symm)
    (hn : d.n = (corrugatedSeedSphere N ∘ ψ) ∘ S.symm)
    (hrec : EqOn (planarSupportMap G ∘ identityBandCentralCoordinates d)
      (ruledMap d.γ d.E) (identityBandCentralRawDomain w))
    (hout : ComplexVisiblePair (1 / 4) (corrugatedSeedBeta N ∘ ψ)
      (corrugatedSeedBalancedPartner N ψ ell a))
    (href : ComplexVisiblePair (4 / 5)
      (corrugatedReverseReflect (corrugatedSeedBalancedPartner N ψ ell a))
      (corrugatedReverseReflect (corrugatedSeedBeta N ∘ ψ))) :
    ComplexVisiblePair (1 / 4)
      (positiveExitComplexTrace (fun s => identityBandCentralCoordinates d ![s, 0]))
      (fun s => Complex.I * positiveExitComplexPoint
        (planarGradient G (identityBandCentralCoordinates d ![s, 0]))) ∧
    ComplexVisiblePair (4 / 5)
      (corrugatedReverseReflect (positiveExitComplexTrace
        (fun s => planarGradient G (identityBandCentralCoordinates d ![s, 0]))))
      (fun s => Complex.I * corrugatedReverseReflect
        (positiveExitComplexTrace (fun s => identityBandCentralCoordinates d ![s, 0])) s) := by
  let β := corrugatedSeedBeta N ∘ ψ
  let D := corrugatedSeedBalancedPartner N ψ ell a
  have hβ : ContDiff ℝ ∞ β := (corrugatedSeedBeta_contDiff N).comp hψ
  have hD : ContDiff ℝ ∞ D := corrugatedSeedBalancedPartner_contDiff N ell hψ ha
  have hclock (s) : HasDerivAt S.symm (a (S.symm s))⁻¹ s :=
    identityBand_arclengthInverse_hasDerivAt ha.continuous hapos S hS s
  have hclockpos (s) : 0 < deriv S.symm s := by
    rw [(hclock s).deriv]
    exact inv_pos.mpr (hapos _)
  have houter := hout.comp (hβ.differentiable (by simp)) (hD.differentiable (by simp))
    (hSs.differentiable (by simp)) hclockpos
  let ψrev : ℝ → ℝ := fun s => -S.symm (-s)
  have hrev : ContDiff ℝ ∞ ψrev := by
    exact (hSs.comp contDiff_neg).neg
  have hrevD (s) : HasDerivAt ψrev (a (S.symm (-s)))⁻¹ s := by
    simpa only [ψrev, Function.comp_def, Pi.neg_apply, smul_eq_mul, mul_neg, mul_one, neg_mul, one_mul, neg_neg] using
      (hasDerivAt_neg (S.symm (-s))).comp s
        ((hclock (-s)).comp s (hasDerivAt_neg s))
  have hrevpos (s) : 0 < deriv ψrev s := by
    rw [(hrevD s).deriv]
    exact inv_pos.mpr (hapos _)
  have hreflect := href.comp
    ((corrugatedReverseReflect_contDiff hD).differentiable (by simp))
    ((corrugatedReverseReflect_contDiff hβ).differentiable (by simp))
    (hrev.differentiable (by simp)) hrevpos
  have hreflect' : ComplexVisiblePair (4 / 5)
      (corrugatedReverseReflect (D ∘ S.symm)) (corrugatedReverseReflect (β ∘ S.symm)) := by
    convert hreflect using 1 <;> funext s <;>
      simp only [ψrev, D, β, corrugatedReverseReflect, Function.comp_apply, neg_neg]
  have hinner := exitSeed_visible_rotate_I hreflect'
    (corrugatedReverseReflect_contDiff (hD.comp hSs))
    (corrugatedReverseReflect_contDiff (hβ.comp hSs))
  have hpEq : positiveExitComplexTrace (fun s => identityBandCentralCoordinates d ![s, 0]) =
      β ∘ S.symm := by
    funext s
    change positiveExitComplexPoint (identityBandCentralCoordinates d ![s, 0]) = β (S.symm s)
    rw [← identityBandCentralSourceTrace_eq_raw]
    simp only [positiveExitComplexTrace, comp_apply, identityBandCentralSourceTrace, hn,
      corrugatedSeedSphere, gnomonic_left_inverse, β]
    rfl
  have hgEq : positiveExitComplexTrace
      (fun s => planarGradient G (identityBandCentralCoordinates d ![s, 0])) =
      (fun s => -Complex.I * D (S.symm s)) := by
    funext s
    change positiveExitComplexPoint (planarGradient G
      (identityBandCentralCoordinates d ![s, 0])) = _
    rw [← identityBandCentralSourceTrace_eq_raw,
      ← identityBandCentralGradientTrace_eq_gradient d hw hrec, identityBandCentralGradientTrace,
      exitSeed_horizontal, hγ]
    simp only [comp_apply]
    rw [corrugatedSeedBalancedSpatial_horizontal N ell hψ ha.continuous]
    simp [D, corrugatedSeedBalancedPartner, ← mul_assoc]
  constructor
  · change ComplexVisiblePair (1 / 4) _
      (fun s => Complex.I * positiveExitComplexTrace
        (fun r => planarGradient G (identityBandCentralCoordinates d ![r, 0])) s)
    rw [hpEq, hgEq]
    simpa only [β, D, Function.comp_def, ← mul_assoc, Complex.I_mul_I, mul_neg, neg_mul, one_mul, neg_neg] using houter
  · rw [hpEq, hgEq]
    convert hinner using 1 <;> funext s <;>
      simp only [corrugatedReverseReflect, Function.comp_apply, map_mul, map_neg,
        Complex.conj_I, neg_neg, mul_neg, neg_mul]

/-- SAME corrected frame and SAME tensor potential, with an actual visible
flow margin selected before constructing the actual protected bending field. -/
theorem positiveExit_same_seed_visible_protected_field
    {T w N ell : ℝ} [Fact (0 < T)] (d : PeriodicRuledFrame T)
    {ψ a κ : ℝ → ℝ} {G : Coord → ℝ} {U : Set Coord}
    (hw : 0 < w) (hidentity : PrincipalNormalIdentityBand d)
    (hψ : ContDiff ℝ ∞ ψ) (ha : ContDiff ℝ ∞ a) (hapos : ∀ r, 0 < a r)
    (S : ℝ ≃ₜ ℝ) (hS : (S : ℝ → ℝ) = rawPrimitive a) (hSs : ContDiff ℝ ∞ S.symm)
    (hγ : d.γ = corrugatedSeedBalancedSpatial N ψ ell a ∘ S.symm)
    (hn : d.n = (corrugatedSeedSphere N ∘ ψ) ∘ S.symm)
    (hc : IdentityBandCentralSupportWithPotential d w a κ S G U)
    (hout : ComplexVisiblePair (1 / 4) (corrugatedSeedBeta N ∘ ψ)
      (corrugatedSeedBalancedPartner N ψ ell a))
    (href : ComplexVisiblePair (4 / 5)
      (corrugatedReverseReflect (corrugatedSeedBalancedPartner N ψ ell a))
      (corrugatedReverseReflect (corrugatedSeedBeta N ∘ ψ))) :
    let hb := periodicRuledFrame_identity_band_period_zero d hidentity
    ∃ δ > 0, δ < w ∧
      ∃ hinside : ∀ v ∈ Ioo (0 : ℝ) δ, ∀ s : ℝ,
        principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 v s ∈ Ioo 0 w,
      ∃ Y : AddCircle T × Ioo (0 : ℝ) w → Ambient,
        IsBandBending (d.bandMap (b := w)) Y ∧ HasCompactSupport Y ∧
        (∃ p, Y p ≠ 0) ∧ tsupport Y ⊆ range (identityFlowBandInclusion d hb 0 hinside) ∧
        ∀ v ∈ Ioo (0 : ℝ) δ,
          let u := principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 v
          ComplexVisiblePair (1 / 4)
            (positiveExitComplexTrace (fun s => identityBandCentralCoordinates d ![s, u s]))
            (fun s => Complex.I * positiveExitComplexPoint
              (planarGradient G (identityBandCentralCoordinates d ![s, u s]))) ∧
          ComplexVisiblePair (4 / 5)
            (corrugatedReverseReflect (positiveExitComplexTrace
              (fun s => planarGradient G (identityBandCentralCoordinates d ![s, u s]))))
            (fun s => Complex.I * corrugatedReverseReflect
              (positiveExitComplexTrace (fun s => identityBandCentralCoordinates d ![s, u s])) s) := by
  let hb := periodicRuledFrame_identity_band_period_zero d hidentity
  rcases hc with ⟨hU, _, hG, _, hP, hPU, hrec, _⟩
  obtain ⟨hco, hci⟩ := positiveExit_seed_central_visible d hw hψ ha hapos S hS hSs hγ hn hrec hout href
  obtain ⟨δ, hδ, hδw, hflows⟩ := positiveExit_exists_visible_complete_flow_initial_margin
    d hb hw hU hG hP hPU hco hci
  have hinside : ∀ v ∈ Ioo (0 : ℝ) δ, ∀ s : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 v s ∈ Ioo 0 w :=
    fun v hv => (hflows v hv).1
  obtain ⟨Y, hY, hcompact, hnonzero, hsupport, _⟩ :=
    periodicRuledFrame_exists_protected_bending (δ := δ) d hidentity 0 hw hδ
  have hsupport' := identityFlowBandInclusion_support_in_range d hb 0 hinside
    (Y := Y) (fun p hp => hsupport ⟨p, hp, rfl⟩)
  exact ⟨δ, hδ, hδw, hinside, Y, hY, hcompact, hnonzero, hsupport',
    fun v hv => (hflows v hv).2⟩

end
end TightVer401
