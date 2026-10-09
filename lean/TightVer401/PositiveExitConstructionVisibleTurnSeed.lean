import TightVer401.PositiveExitConstructionFlowTurn
import TightVer401.PositiveExitConstructionVisibleSeed

/-! Select one common complete visible/positive-turn flow margin before
constructing the SAME corrected band's protected field. No old field is
reused after narrowing a margin. The original band width and potential stay fixed. -/
open scoped Manifold
namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff Topology ComplexConjugate
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The SAME SeedTurn witnesses supply both turns and both visibility pairs
of every leaf in a final common margin. The protected bending is chosen ONCE
inside that final margin, after all required complete-leaf properties hold. -/
theorem positiveExit_same_seed_visible_turn_protected_field {N : ℕ} (hN : 10000 ≤ N)
    (e : ℝ ≃ₜ ℝ) (he : (e : ℝ → ℝ) = corrugatedSeedArcMap (N : ℝ))
    (hes : ContDiff ℝ ∞ e.symm) {a : ℝ → ℝ} (ha : ContDiff ℝ ∞ a)
    (hapos : ∀ r, 0 < a r) (S : ℝ ≃ₜ ℝ)
    (hS : (S : ℝ → ℝ) = rawPrimitive a) (hSs : ContDiff ℝ ∞ S.symm)
    (d : PeriodicRuledFrame (rawPrimitive a ((N : ℝ) * corrugatedSeedArcCell (N : ℝ))))
    [Fact (0 < rawPrimitive a ((N : ℝ) * corrugatedSeedArcCell (N : ℝ)))]
    (hγ : d.γ = corrugatedSeedBalancedSpatial (N : ℝ) e.symm
      (corrugatedSeedArcCell (N : ℝ)) a ∘ S.symm)
    (hn : d.n = (corrugatedSeedSphere (N : ℝ) ∘ e.symm) ∘ S.symm)
    {w : ℝ} (hw : 0 < w) (hidentity : PrincipalNormalIdentityBand d)
    {κ : ℝ → ℝ} {G : Coord → ℝ} {U : Set Coord}
    (hc : IdentityBandCentralSupportWithPotential d w a κ S G U)
    (hDturn : HasPositiveArgumentTurn
      (corrugatedSeedBalancedPartner (N : ℝ) e.symm (corrugatedSeedArcCell (N : ℝ)) a)
      ((N : ℝ) * corrugatedSeedArcCell (N : ℝ)))
    (hout : ComplexVisiblePair (1 / 4) (corrugatedSeedBeta (N : ℝ) ∘ e.symm)
      (corrugatedSeedBalancedPartner (N : ℝ) e.symm (corrugatedSeedArcCell (N : ℝ)) a))
    (href : ComplexVisiblePair (4 / 5)
      (corrugatedReverseReflect
        (corrugatedSeedBalancedPartner (N : ℝ) e.symm (corrugatedSeedArcCell (N : ℝ)) a))
      (corrugatedReverseReflect (corrugatedSeedBeta (N : ℝ) ∘ e.symm))) :
    let T := rawPrimitive a ((N : ℝ) * corrugatedSeedArcCell (N : ℝ))
    let hb := periodicRuledFrame_identity_band_period_zero d hidentity
    ∃ δ > 0, δ < w ∧
      ∃ hinside : ∀ v ∈ Ioo (0 : ℝ) δ, ∀ s : ℝ,
        principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 v s ∈ Ioo 0 w,
      ∃ Y : AddCircle T × Ioo (0 : ℝ) w → Ambient,
        IsBandBending (d.bandMap (b := w)) Y ∧ HasCompactSupport Y ∧
        (∃ p, Y p ≠ 0) ∧ tsupport Y ⊆ range (identityFlowBandInclusion d hb 0 hinside) ∧
        ∀ v ∈ Ioo (0 : ℝ) δ,
          let u := principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 v
          ContDiff ℝ ∞ u ∧ Function.Periodic u T ∧
          HasPositiveArgumentTurn
            (positiveExitComplexTrace (fun s => identityBandCentralCoordinates d ![s, u s])) T ∧
          HasPositiveArgumentTurn
            (positiveExitComplexTrace (fun s => planarGradient G
              (identityBandCentralCoordinates d ![s, u s]))) T ∧
          (∀ s, positiveExitComplexPoint (identityBandCentralCoordinates d ![s, u s]) ≠ 0) ∧
          (∀ s, positiveExitComplexPoint
            (planarGradient G (identityBandCentralCoordinates d ![s, u s])) ≠ 0) ∧
          ComplexVisiblePair (1 / 4)
            (positiveExitComplexTrace (fun s => identityBandCentralCoordinates d ![s, u s]))
            (fun s => Complex.I * positiveExitComplexPoint
              (planarGradient G (identityBandCentralCoordinates d ![s, u s]))) ∧
          ComplexVisiblePair (4 / 5)
            (corrugatedReverseReflect (positiveExitComplexTrace
              (fun s => planarGradient G (identityBandCentralCoordinates d ![s, u s]))))
            (fun s => Complex.I * corrugatedReverseReflect
              (positiveExitComplexTrace (fun s => identityBandCentralCoordinates d ![s, u s])) s) := by
  dsimp only
  let T := rawPrimitive a ((N : ℝ) * corrugatedSeedArcCell (N : ℝ))
  let hb := periodicRuledFrame_identity_band_period_zero d hidentity
  rcases hc with ⟨hU, _, hG, _, hP, hPU, hrec, _⟩
  obtain ⟨hco, hci⟩ := positiveExit_seed_central_visible d hw hes ha hapos S hS hSs hγ hn hrec hout href
  obtain ⟨hpt, hgt⟩ := positiveExit_seed_central_positive_turns
    hN e he hes ha hapos S hS d hγ hn hw hrec hDturn hout
  have hpne (s : ℝ) : positiveExitComplexPoint (identityBandCentralCoordinates d ![s, 0]) ≠ 0 := by
    apply norm_ne_zero_iff.mp
    have h := (hci (-s)).1
    have hr : (4 / 5 : ℝ) < ‖positiveExitComplexPoint (identityBandCentralCoordinates d ![s, 0])‖ := by
      simpa only [corrugatedReverseReflect, positiveExitComplexTrace, neg_neg,
        norm_mul, Complex.norm_I, one_mul, Complex.norm_conj, Function.comp_apply] using h
    linarith
  have hgne (s : ℝ) : positiveExitComplexPoint
      (planarGradient G (identityBandCentralCoordinates d ![s, 0])) ≠ 0 := by
    apply norm_ne_zero_iff.mp
    have hr := (hco s).1
    simp only [norm_mul, Complex.norm_I, one_mul] at hr
    linarith
  obtain ⟨δvis, hδvis, hδvisw, hvisible⟩ :=
    positiveExit_exists_visible_complete_flow_initial_margin d hb hw hU hG hP hPU hco hci
  obtain ⟨ρ, hρ, hρw, δturn, hδturn, hδturnρ, hturn⟩ :=
    positiveExit_exists_turn_complete_flow_initial_margin d hb hw hU hG hP hPU hpne hgne hpt hgt
  let δ := min δvis δturn
  have hδ : 0 < δ := lt_min hδvis hδturn
  have hδw : δ < w := (min_le_left _ _).trans_lt hδvisw
  have hvt {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) δ) : v ∈ Ioo (0 : ℝ) δturn :=
    ⟨hv.1, hv.2.trans_le (min_le_right _ _)⟩
  have hvv {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) δ) : v ∈ Ioo (0 : ℝ) δvis :=
    ⟨hv.1, hv.2.trans_le (min_le_left _ _)⟩
  have hinside : ∀ v ∈ Ioo (0 : ℝ) δ, ∀ s : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 v s ∈ Ioo 0 w := by
    intro v hv s
    have hu := (hturn v (hvt hv)).2.2.1 s
    exact ⟨hu.1, hu.2.trans hρw⟩
  obtain ⟨Y, hY, hcompact, hnonzero, hsupport, _⟩ :=
    periodicRuledFrame_exists_protected_bending (δ := δ) d hidentity 0 hw hδ
  have hsupport' := identityFlowBandInclusion_support_in_range d hb 0 hinside
    (Y := Y) (fun p hp => hsupport ⟨p, hp, rfl⟩)
  refine ⟨δ, hδ, hδw, hinside, Y, hY, hcompact, hnonzero, hsupport', ?_⟩
  intro v hv
  obtain ⟨huS, huP, _, _, _, _, _, hpt', hgt', hpne', hgne'⟩ := hturn v (hvt hv)
  obtain ⟨_, hvo, hvi⟩ := hvisible v (hvv hv)
  exact ⟨huS, huP, hpt', hgt', hpne', hgne', hvo, hvi⟩

end
end TightVer401
