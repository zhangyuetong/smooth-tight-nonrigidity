import TightVer401.PositiveExitConstructionSeedTurn
import TightVer401.PositiveExitConstructionVisibleTurnSeed
import TightVer401.PositiveExitConstructionFinalSeedConnection
import TightVer401.PositiveExitConstructionFinalMarginConnection
import TightVer401.PositiveExitConstructionSinglePrefix
import TightVer401.NormalLoopOrientation
import TightVer401.CorrugatedSeedFrameSetup

/-! An actual corrected seed and one final protected field construct the
selected caller data with no original construction premises.
No original geometric package or external construction grant is a premise. -/
open scoped Manifold
namespace TightVer401
noncomputable section
open Set Function MeasureTheory OAI.SmoothLocal.Geometry
open OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- Existence of the original selected data. Only the universal ordinary
connector producer remains outside this actual seed/source construction. -/
theorem actualSeed_exists_selected_single_prefix :
    ∃ T : ℝ, ∃ hT : 0 < T,
      letI : Fact (0 < T) := ⟨hT⟩
      ∃ d : PeriodicRuledFrame T, ∃ w : ℝ,
      ∃ c0 : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) Coord,
      ∃ G0 : Coord → ℝ, ∃ Y : AddCircle T × Ioo (0 : ℝ) w → Ambient,
        0 < w ∧ c0.source = univ ∧
        ContMDiffOn nativeProductModel 𝓘(ℝ, Coord) ∞ c0 c0.source ∧
        ContMDiffOn 𝓘(ℝ, Coord) nativeProductModel ∞ c0.symm c0.target ∧
        (∀ p ∈ c0.source, planarSupportMap G0 (c0 p) = d.bandMap p) ∧
        IsBandBending (d.bandMap (b := w)) Y ∧ HasCompactSupport Y ∧
        (∃ p, Y p ≠ 0) ∧ tsupport Y ⊆ c0.source ∧
        Nonempty (PositiveExitSinglePrefixGeometry d c0 G0 Y) := by
  have hN : 10000 ≤ (10000 : ℕ) := le_rfl
  have hNr : 1 < ((10000 : ℕ) : ℝ) := by norm_num
  have hseed := positiveExit_central_support_with_balanced_turn hN
    (η := (1 : ℝ)) zero_lt_one
  dsimp only at hseed
  obtain ⟨arc, harc, harcs, a, ha, haPeriod, hapos, hsmall, hMoment, hBalance,
    hPartnerTurn, hOuter, hReflected, S, hS, hSs, d,
    hgamma, hTan, hE, hn, hk, htau, hidentity, hT,
    w, hw, hcollar, _holdField, G0, U, hc⟩ := hseed
  let T := rawPrimitive a (((10000 : ℕ) : ℝ) * corrugatedSeedArcCell ((10000 : ℕ) : ℝ))
  letI : Fact (0 < T) := ⟨hT⟩
  -- Recover derivative information for the SAME exact arc map by uniqueness.
  obtain ⟨arcWitness, hArcWitness, _hArcWitnessSmooth, hArcDerivative, _⟩ :=
    corrugatedSeed_exists_cell_arclength hNr
  have hArcEq : arcWitness = arc := by
    ext r
    exact congrFun (hArcWitness.trans harc.symm) r
  subst arcWitness
  let zeta : ℝ → Ambient := corrugatedSeedSphere ((10000 : ℕ) : ℝ) ∘ arc.symm
  have hzeta : ContDiff ℝ ∞ zeta :=
    (corrugatedSeedSphere_contDiff _).comp harcs
  obtain ⟨hUnit, hSpeed⟩ := corrugatedSeed_arclength_unit_frame hNr harcs hArcDerivative
  have horient : ∀ s, ambientCross (d.T s) (d.E s) = d.n s := by
    intro s
    rw [hTan, hE, hn]
    exact (normalLoop_orientation
      (fun r => (hzeta.differentiable (by simp) r).hasDerivAt)
      hUnit hSpeed (S.symm s)).1
  have htauNeg : ∀ s, d.τ s < 0 := by
    intro s
    rw [htau]
    exact neg_lt_zero.mpr (inv_pos.mpr (hapos (S.symm s)))
  have hmem (p : AddCircle T × Ioo (0 : ℝ) w) :
      (p.1, (p.2 : ℝ)) ∈ (univ ×ˢ Icc (-w) w : Set (AddCircle T × ℝ)) := by
    refine ⟨mem_univ _, ?_, p.2.property.2.le⟩
    linarith [p.2.property.1]
  have hNi : Injective (d.bandGaussMap (b := w)) := by
    intro p q heq
    have hfull : d.fullGaussMap (p.1, (p.2 : ℝ)) =
        d.fullGaussMap (q.1, (q.2 : ℝ)) := heq
    have he := hcollar.1 (hmem p) (hmem q) hfull
    have hfirst : p.1 = q.1 := congrArg (fun z : AddCircle T × ℝ => z.1) he
    have hsecond : (p.2 : ℝ) = (q.2 : ℝ) := congrArg (fun z : AddCircle T × ℝ => z.2) he
    exact Prod.ext hfirst (Subtype.ext hsecond)
  have hnorth : ∀ p : AddCircle T × Ioo (0 : ℝ) w, 0 < d.bandGaussMap p 2 := by
    intro p
    exact hcollar.2.1 _ (hmem p)
  -- The old support-package field is discarded. Select final Y only now.
  obtain ⟨delta, hdelta, _hdeltaW, hinside, Y, hY, hcompact, hnonzero, hsupport, hmargin⟩ :=
    positiveExit_same_seed_visible_turn_protected_field hN arc harc harcs ha hapos
      S hS hSs d hgamma hn hw hidentity hc hPartnerTurn hOuter hReflected
  let hb := periodicRuledFrame_identity_band_period_zero d hidentity
  obtain ⟨c0, hcS, _hcT, hcF, hcD, hcI, hG, hrec, hdet, hEmbedding, hbend,
    C, _hCeq, hC, hCne, hprotect, hsupportC⟩ :=
    positiveExit_final_seed_support_connection d hc hb hinside Y hY hcompact hnonzero hsupport
  have hrawMargin := positiveExit_final_margin_selected_raw_leaves d hb hinside G0 hmargin
  have hselected : Nonempty (PositiveExitSinglePrefixGeometry d c0 G0 Y) :=
    positiveExit_exists_single_prefix_source_geometry d hb hdelta hinside
      hNi hnorth horient htauNeg c0 hcS hcF hcD hcI
      G0 hG hrec hdet hEmbedding C hC hCne hprotect Y hbend hsupportC
      (η := (1 : ℝ)) (ξ := (1 : ℝ)) (σin := (1 : ℝ)) (σout := (1 : ℝ))
      zero_lt_one zero_lt_one one_ne_zero one_ne_zero hrawMargin
  refine ⟨T, hT, d, w, c0, G0, Y, hw, hcS, hcD.contMDiffOn, hcI,
    (fun p _ => hrec p), hY, hcompact, hnonzero, ?_, hselected⟩
  rw [hcS]
  exact subset_univ _

end
end TightVer401
