import TightVer401.PositiveExitConstructionSeedTurn
import TightVer401.PositiveExitConstructionCentralTrace
import TightVer401.PositiveExitConstructionContract
import TightVer401.CorrugatedSeedBalancedSpatial

/-! The SAME seed, corrected speed, arclength clocks and reconstructed
Cartesian potential retain positive turns of both actual central traces. -/
open scoped Manifold
namespace TightVer401
noncomputable section
open Set Function OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

/-- Actual endpoint-preserving clock transport of the argument lift. -/
theorem positiveExit_argumentTurn_comp_clock {f : ℝ → ℂ} {L T : ℝ}
    (hf : HasPositiveArgumentTurn f L) {ψ : ℝ → ℝ}
    (hψ : Continuous ψ) (h0 : ψ 0 = 0) (hT : ψ T = L) :
    HasPositiveArgumentTurn (f ∘ ψ) T := by
  obtain ⟨φ, hφ, harg, hinc⟩ := hf
  refine ⟨φ ∘ ψ, hφ.comp hψ, fun s => harg (ψ s), ?_⟩
  simpa only [comp_apply, hT, h0] using hinc

/-- A fixed actual phase rotation preserves the turn of a nonzero trace. -/
theorem positiveExit_argumentTurn_const_phase {f : ℝ → ℂ} {L : ℝ}
    (hf : HasPositiveArgumentTurn f L) (hne : ∀ s, f s ≠ 0) (θ : ℝ) :
    HasPositiveArgumentTurn (fun s => (Circle.exp θ : ℂ) * f s) L := by
  obtain ⟨φ, hφ, harg, hinc⟩ := hf
  refine ⟨fun s => θ + φ s, continuous_const.add hφ, ?_, ?_⟩
  · intro s
    have hrot : (Circle.exp θ : ℂ) * f s ≠ 0 :=
      mul_ne_zero (by exact norm_ne_zero_iff.mp (by simp)) (hne s)
    apply Subtype.ext
    rw [Circle.exp_add]
    change (complexCircleDirection ((Circle.exp θ : ℂ) * f s) : ℂ) =
      (Circle.exp θ : ℂ) * (Circle.exp (φ s) : ℂ)
    rw [← harg s, complexCircleDirection_normalized hrot,
      complexCircleDirection_normalized (hne s), norm_mul]
    simp only [Circle.norm_coe, one_mul, Complex.real_smul]
    ring
  · linarith

private theorem exitCentralTurn_horizontal (u : Ambient) :
    positiveExitComplexPoint (identityBandPlanarHorizontalCLM u) =
      corrugatedAmbientHorizontal u := by
  apply Complex.ext <;> simp [positiveExitComplexPoint, identityBandPlanarHorizontalCLM,
    corrugatedAmbientHorizontal, ContinuousLinearMap.pi_apply, PiLp.proj_apply]

/-- The proved SAME balanced-partner turn supplies the actual central
gradient turn. The source turn comes from the SAME seed beta, with both actual
clocks' endpoints derived from their given primitive identities. -/
theorem positiveExit_seed_central_positive_turns {N : ℕ} (hN : 10000 ≤ N)
    (e : ℝ ≃ₜ ℝ) (he : (e : ℝ → ℝ) = corrugatedSeedArcMap (N : ℝ))
    (hes : ContDiff ℝ ∞ e.symm) {a : ℝ → ℝ} (ha : ContDiff ℝ ∞ a)
    (_hapos : ∀ r, 0 < a r) (S : ℝ ≃ₜ ℝ)
    (hS : (S : ℝ → ℝ) = rawPrimitive a)
    (d : PeriodicRuledFrame (rawPrimitive a ((N : ℝ) * corrugatedSeedArcCell (N : ℝ))))
    (hγ : d.γ = corrugatedSeedBalancedSpatial (N : ℝ) e.symm
      (corrugatedSeedArcCell (N : ℝ)) a ∘ S.symm)
    (hn : d.n = (corrugatedSeedSphere (N : ℝ) ∘ e.symm) ∘ S.symm)
    {w : ℝ} (hw : 0 < w) {G : Coord → ℝ}
    (hrec : EqOn (planarSupportMap G ∘ identityBandCentralCoordinates d)
      (ruledMap d.γ d.E) (identityBandCentralRawDomain w))
    (hDturn : HasPositiveArgumentTurn
      (corrugatedSeedBalancedPartner (N : ℝ) e.symm (corrugatedSeedArcCell (N : ℝ)) a)
      ((N : ℝ) * corrugatedSeedArcCell (N : ℝ)))
    (hout : ComplexVisiblePair (1 / 4) (corrugatedSeedBeta (N : ℝ) ∘ e.symm)
      (corrugatedSeedBalancedPartner (N : ℝ) e.symm (corrugatedSeedArcCell (N : ℝ)) a)) :
    HasPositiveArgumentTurn
      (positiveExitComplexTrace (fun s => identityBandCentralCoordinates d ![s, 0]))
      (rawPrimitive a ((N : ℝ) * corrugatedSeedArcCell (N : ℝ))) ∧
    HasPositiveArgumentTurn
      (positiveExitComplexTrace (fun s => planarGradient G
        (identityBandCentralCoordinates d ![s, 0])))
      (rawPrimitive a ((N : ℝ) * corrugatedSeedArcCell (N : ℝ))) := by
  let ell := corrugatedSeedArcCell (N : ℝ)
  let L := (N : ℝ) * ell
  let T := rawPrimitive a L
  let D := corrugatedSeedBalancedPartner (N : ℝ) e.symm ell a
  have he0 : e 0 = 0 := by rw [he]; simp [corrugatedSeedArcMap, rawPrimitive]
  have he0' : e.symm 0 = 0 :=
    (congrArg e.symm he0.symm).trans (e.symm_apply_apply 0)
  have heL : e (2 * Real.pi) = L := by
    rw [he]
    exact corrugatedSeedArcMap_full_period (by omega : 2 ≤ N)
  have heL' : e.symm L = 2 * Real.pi :=
    (congrArg e.symm heL.symm).trans (e.symm_apply_apply _)
  have hS0 : S 0 = 0 := by rw [hS]; simp [rawPrimitive]
  have hS0' : S.symm 0 = 0 :=
    (congrArg S.symm hS0.symm).trans (S.symm_apply_apply 0)
  have hST : S L = T := by rw [hS]
  have hST' : S.symm T = L :=
    (congrArg S.symm hST.symm).trans (S.symm_apply_apply _)
  have hβturn : HasPositiveArgumentTurn (corrugatedSeedBeta (N : ℝ) ∘ e.symm) L :=
    positiveExit_argumentTurn_comp_clock (corrugatedSeed_positive_argument_turns hN).1
      e.symm.continuous he0' heL'
  have hpturn := positiveExit_argumentTurn_comp_clock hβturn S.symm.continuous hS0' hST'
  have hγturn := positiveExit_argumentTurn_comp_clock hDturn S.symm.continuous hS0' hST'
  have hDne (s : ℝ) : D s ≠ 0 := by
    apply norm_ne_zero_iff.mp
    have h := (hout s).1
    change (1 / 4 : ℝ) < ‖D s‖ at h
    linarith [norm_nonneg (D s)]
  have hγrot := positiveExit_argumentTurn_const_phase hγturn
    (fun s => hDne (S.symm s)) (-Real.pi / 2)
  have hphase : (Circle.exp (-Real.pi / 2) : ℂ) = -Complex.I := by
    simp only [Circle.coe_exp, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat]
    exact Complex.exp_neg_pi_div_two_mul_I
  rw [hphase] at hγrot
  have hpEq : positiveExitComplexTrace (fun s => identityBandCentralCoordinates d ![s, 0]) =
      (corrugatedSeedBeta (N : ℝ) ∘ e.symm) ∘ S.symm := by
    funext s
    change positiveExitComplexPoint (identityBandCentralCoordinates d ![s, 0]) = _
    rw [← identityBandCentralSourceTrace_eq_raw]
    simp only [positiveExitComplexTrace, comp_apply, identityBandCentralSourceTrace, hn,
      corrugatedSeedSphere, gnomonic_left_inverse]
    rfl
  have hγEq : positiveExitComplexTrace (fun s => planarGradient G
      (identityBandCentralCoordinates d ![s, 0])) =
      (fun s => -Complex.I * D (S.symm s)) := by
    funext s
    change positiveExitComplexPoint (planarGradient G
      (identityBandCentralCoordinates d ![s, 0])) = _
    rw [← identityBandCentralSourceTrace_eq_raw,
      ← identityBandCentralGradientTrace_eq_gradient d hw hrec, identityBandCentralGradientTrace,
      exitCentralTurn_horizontal, hγ]
    simp only [comp_apply]
    rw [corrugatedSeedBalancedSpatial_horizontal (N : ℝ) ell hes ha.continuous]
    simp [D, corrugatedSeedBalancedPartner, ← mul_assoc]
  constructor
  · rw [hpEq]
    exact hpturn
  · rw [hγEq]
    exact hγrot

end
end TightVer401
