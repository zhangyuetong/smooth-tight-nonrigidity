import TightVer401.PositiveExitConstructionSelectedGraph
import TightVer401.PositiveExitConstructionVisibleTurnSeed
import TightVer401.PositiveExitConstructionLeaf
import TightVer401.CorrugatedSeedFrameVisibility

/-! The selected actual complete leaf is reparametrized ONCE before any
perturbation budget. Inner reflection uses its own positive clock
`s ↦ -S.symm(-s)`; it is not inferred from outer visibility. -/
namespace TightVer401
noncomputable section
open Set Function MeasureTheory OAI.SmoothLocal.Geometry
open OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff Topology ComplexConjugate
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

private theorem selectedClock_visible_transport {Rout Rin : ℝ}
    {p gamma : ℝ → ℂ} (hp : ContDiff ℝ ∞ p) (hg : ContDiff ℝ ∞ gamma)
    (ho : ComplexVisiblePair Rout p (fun s => Complex.I * gamma s))
    (hi : ComplexVisiblePair Rin (corrugatedReverseReflect gamma)
      (fun s => Complex.I * corrugatedReverseReflect p s))
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hpos : ∀ s, 0 < deriv ψ s) :
    ComplexVisiblePair Rout (p ∘ ψ) (fun s => Complex.I * (gamma ∘ ψ) s) ∧
    ComplexVisiblePair Rin (corrugatedReverseReflect (gamma ∘ ψ))
      (fun s => Complex.I * corrugatedReverseReflect (p ∘ ψ) s) := by
  have ho' := ho.comp (hp.differentiable (by simp))
    ((contDiff_const.mul hg).differentiable (by simp))
    (hψ.differentiable (by simp)) hpos
  let ψr : ℝ → ℝ := fun s => -ψ (-s)
  have hψr : ContDiff ℝ ∞ ψr := (hψ.comp contDiff_neg).neg
  have hψrD (s) : HasDerivAt ψr (deriv ψ (-s)) s := by
    simpa only [ψr, Function.comp_def, smul_eq_mul, mul_neg, neg_mul, mul_one, one_mul, neg_neg] using
      (hasDerivAt_neg (ψ (-s))).comp s
        ((hψ.differentiable (by simp) (-s)).hasDerivAt.comp s (hasDerivAt_neg s))
  have hi' := hi.comp
    ((corrugatedReverseReflect_contDiff hg).differentiable (by simp))
    ((contDiff_const.mul (corrugatedReverseReflect_contDiff hp)).differentiable (by simp))
    (hψr.differentiable (by simp)) (fun s => by rw [(hψrD s).deriv]; exact hpos (-s))
  constructor
  · simpa only [Function.comp_def] using ho'
  · change ComplexVisiblePair Rin (fun s => starRingEnd ℂ (gamma (ψ (-s))))
      (fun s => Complex.I * starRingEnd ℂ (p (ψ (-s))))
    simpa only [ψr, corrugatedReverseReflect, Function.comp_def, neg_neg] using hi' 

/-- Both actual visibility predicates, both actual turns and both nonzero
traces survive the constructed unit-speed clock of this SAME complete flow
leaf. The raw premises are the literal complete-leaf conclusions supplied by
the one corrected seed's final visibility/turn margin. -/
theorem positiveExit_selected_leaf_exists_visible_turn_unitSpeed
    {T δ w Rout Rin : ℝ} [Fact (0 < T)] (d : PeriodicRuledFrame T)
    (hb : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0)
    (hinside : ∀ u ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 u t ∈ Ioo 0 w)
    (v : Ioo (0 : ℝ) δ)
    (hNi : Injective (d.bandGaussMap (b := w)))
    (hn : ∀ p : AddCircle T × Ioo (0 : ℝ) w, 0 < d.bandGaussMap p 2)
    {G : Coord → ℝ} {U : Set Coord} (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U)
    (hsource : ∀ s, gnomonicInverse (positiveExitRawLeaf d hb hinside v s) ∈ U)
    (hpnz : ∀ s, angularDescentComplex
      (gnomonicInverse (positiveExitRawLeaf d hb hinside v s)) ≠ 0)
    (hgnz : ∀ s, angularDescentComplex
      (planarGradient G (gnomonicInverse (positiveExitRawLeaf d hb hinside v s))) ≠ 0)
    (hpturn : HasPositiveArgumentTurn
      (angularDescentComplex ∘ gnomonicInverse ∘ positiveExitRawLeaf d hb hinside v) T)
    (hgturn : HasPositiveArgumentTurn
      (angularDescentComplex ∘ planarGradient G ∘ gnomonicInverse ∘ positiveExitRawLeaf d hb hinside v) T)
    (houter : ComplexVisiblePair Rout
      (angularDescentComplex ∘ gnomonicInverse ∘ positiveExitRawLeaf d hb hinside v)
      (fun s => Complex.I * angularDescentComplex
        (planarGradient G (gnomonicInverse (positiveExitRawLeaf d hb hinside v s)))))
    (hinner : ComplexVisiblePair Rin
      (corrugatedReverseReflect (angularDescentComplex ∘ planarGradient G ∘
        gnomonicInverse ∘ positiveExitRawLeaf d hb hinside v))
      (fun s => Complex.I * corrugatedReverseReflect
        (angularDescentComplex ∘ gnomonicInverse ∘ positiveExitRawLeaf d hb hinside v) s)) :
    ∃ S : ℝ ≃ₜ ℝ, ∃ P > 0,
      (S : ℝ → ℝ) = rawPrimitive (positiveExitLeafSpeed d hb hinside v) ∧
      P = rawPrimitive (positiveExitLeafSpeed d hb hinside v) T ∧
      ContDiff ℝ ∞ S.symm ∧
      (∀ s, S.symm (s + P) = S.symm s + T) ∧
      ∃ hp : Periodic (positiveExitRawLeaf d hb hinside v ∘ S.symm) P,
        let ζ := positiveExitRawLeaf d hb hinside v ∘ S.symm
        ContDiff ℝ ∞ ζ ∧ Injective hp.lift ∧
        (∀ s, inner ℝ (ζ s) (ζ s) = 1) ∧
        (∀ s, inner ℝ (deriv ζ s) (deriv ζ s) = 1) ∧
        (∀ s, 0 < ζ s 2) ∧ (∀ s, gnomonicInverse (ζ s) ∈ U) ∧
        (∀ s, angularDescentComplex (gnomonicInverse (ζ s)) ≠ 0) ∧
        (∀ s, angularDescentComplex (planarGradient G (gnomonicInverse (ζ s))) ≠ 0) ∧
        HasPositiveArgumentTurn (angularDescentComplex ∘ gnomonicInverse ∘ ζ) P ∧
        HasPositiveArgumentTurn (angularDescentComplex ∘ planarGradient G ∘ gnomonicInverse ∘ ζ) P ∧
        ComplexVisiblePair Rout (angularDescentComplex ∘ gnomonicInverse ∘ ζ)
          (fun s => Complex.I * angularDescentComplex (planarGradient G (gnomonicInverse (ζ s)))) ∧
        ComplexVisiblePair Rin
          (corrugatedReverseReflect (angularDescentComplex ∘ planarGradient G ∘ gnomonicInverse ∘ ζ))
          (fun s => Complex.I * corrugatedReverseReflect (angularDescentComplex ∘ gnomonicInverse ∘ ζ) s) := by
  obtain ⟨S, P, hP, hS, hLength, hSs, hshift, hp, hζ, hiζ, hunit, hnorth, hspeed⟩ :=
    positiveExitLeaf_exists_unitSpeed d hb hinside v hNi hn
  let ξ := positiveExitRawLeaf d hb hinside v
  let p := angularDescentComplex ∘ gnomonicInverse ∘ ξ
  let gamma := angularDescentComplex ∘ planarGradient G ∘ gnomonicInverse ∘ ξ
  have hrawnorth (s) : 0 < ξ s 2 :=
    positiveExitGaussLeaf_north d hb hinside v hn (periodProjection T s)
  have hpS : ContDiff ℝ ∞ p := by
    rw [contDiff_iff_contDiffAt]
    intro s
    exact angularDescentComplex_contDiff.contDiffAt.comp s
      ((gnomonicInverse_contDiffAt (hrawnorth s).ne').comp s
        (positiveExitRawLeaf_contDiff d hb hinside v).contDiffAt)
  have hgS : ContDiff ℝ ∞ gamma := by
    rw [contDiff_iff_contDiffAt]
    intro s
    exact angularDescentComplex_contDiff.contDiffAt.comp s
      ((((planarGradient_contDiffOn hG hU) _ (hsource s)).contDiffAt
        (hU.mem_nhds (hsource s))).comp s
        ((gnomonicInverse_contDiffAt (hrawnorth s).ne').comp s
          (positiveExitRawLeaf_contDiff d hb hinside v).contDiffAt))
  have hderiv (s) : HasDerivAt S.symm
      (positiveExitLeafSpeed d hb hinside v (S.symm s))⁻¹ s :=
    (rawPrimitive_hasDerivAt (positiveExitLeafSpeed_contDiff d hb hinside v).continuous
      (S.symm s)).of_local_left_inverse S.symm.continuous.continuousAt
      (positiveExitLeafSpeed_pos d hb hinside v (S.symm s)).ne'
      (Filter.Eventually.of_forall (fun y => by rw [← hS]; exact S.apply_symm_apply y))
  have hderivpos (s) : 0 < deriv S.symm s := by
    rw [(hderiv s).deriv]
    exact inv_pos.mpr (positiveExitLeafSpeed_pos d hb hinside v (S.symm s))
  have hS0 : S 0 = 0 := by rw [hS]; simp [rawPrimitive]
  have hS0' : S.symm 0 = 0 :=
    (congrArg S.symm hS0.symm).trans (S.symm_apply_apply 0)
  have hST : S T = P := by rw [hS, hLength]
  have hST' : S.symm P = T :=
    (congrArg S.symm hST.symm).trans (S.symm_apply_apply T)
  obtain ⟨hvo, hvi⟩ := selectedClock_visible_transport hpS hgS houter hinner hSs hderivpos
  have hpt := positiveExit_argumentTurn_comp_clock hpturn S.symm.continuous hS0' hST'
  have hgt := positiveExit_argumentTurn_comp_clock hgturn S.symm.continuous hS0' hST'
  refine ⟨S, P, hP, hS, hLength, hSs, hshift, hp, hζ, hiζ, hunit, hspeed,
    hnorth, fun s => hsource (S.symm s), fun s => hpnz (S.symm s),
    fun s => hgnz (S.symm s), ?_, ?_, ?_, ?_⟩
  · simpa only [comp_assoc] using hpt
  · simpa only [comp_assoc] using hgt
  · simpa only [p, gamma, ξ, Function.comp_def] using hvo
  · simpa only [p, gamma, ξ, Function.comp_def] using hvi

end
end TightVer401
