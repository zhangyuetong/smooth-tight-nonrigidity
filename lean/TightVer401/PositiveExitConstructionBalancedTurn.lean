import TightVer401.PositiveExitConstructionWindingBridge
import TightVer401.CorrugatedSeedBalancedOuter
import TightVer401.CorrugatedSeedFrameEmbedding
import TightVer401.CorrugatedSeedFrameSetup
import TightVer401.CovariantSpeedCellBounds
import TightVer401.IdentityBandCentralSupportPhysical

/-! The same corrected seed retains its positive origin turn under an actual
cell L1 bound. The threshold is chosen BEFORE constructing the speed a;
callers request the minimum of this threshold and their other scalar bound. -/
namespace TightVer401
noncomputable section
open Set Function Filter MeasureTheory OAI.SmoothLocal.Geometry
open OAI.CircleDomainRigidity OAI.CircleDomainRigidity.FiniteTransfer
open OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

private theorem exitBalancedTurn_direction (z : ℂ) :
    AddCircle.toCircle (normalizedArgument z) = complexCircleDirection z := by
  rw [normalizedArgument_eq, AddCircle.toCircle_apply_mk, div_one]
  have he : 2 * Real.pi * (z.arg / (2 * Real.pi)) = z.arg := by field_simp
  rw [he]
  apply Subtype.ext
  simpa only [Circle.coe_exp] using (complexCircleDirection_coe z).symm

/-- Application of the pinned continuous integer increment calculus to the
actual straight-line correction family. No turn for the corrected curve is
assumed. All curve hypotheses below are discharged by the same seed. -/
theorem positiveExit_argument_turn_of_uniform_close {B D : ℝ → ℂ} {L ε : ℝ}
    (hB : ContDiff ℝ ∞ B) (hD : ContDiff ℝ ∞ D)
    (hpB : Periodic B L) (hpD : Periodic D L)
    (hradius : ∀ r, ε ≤ ‖B r‖)
    (hclose : ∀ r, ‖D r - B r‖ < ε)
    (hturn : HasPositiveArgumentTurn (fun t => B (L * t)) 1) :
    HasPositiveArgumentTurn D L := by
  let H (l : unitInterval) (r : ℝ) : ℂ := B r + (l : ℝ) • (D r - B r)
  have herror (l : unitInterval) (r : ℝ) : ‖H l r - B r‖ < ε := by
    dsimp only [H]
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg l.property.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) l.property.2).trans_lt (hclose r)
  have havoid (l : unitInterval) (r : ℝ) : H l r ≠ 0 := by
    intro he
    have h := herror l r
    rw [he, zero_sub, norm_neg] at h
    exact (not_lt_of_ge (hradius r)) h
  let path (l : unitInterval) : C(unitInterval, ℂ) :=
    ⟨fun t => H l (L * t), by
      dsimp only [H]
      simp only [Complex.real_smul]
      fun_prop⟩
  have hpath : Continuous path := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun p : unitInterval × unitInterval =>
      B (L * (p.2 : ℝ)) + (p.1 : ℝ) • (D (L * (p.2 : ℝ)) - B (L * (p.2 : ℝ))))
    fun_prop
  let avoiding (l : unitInterval) : AvoidingPathPoint :=
    ⟨(path l, 0), by
      rintro ⟨t, ht⟩
      exact havoid l (L * t) ht⟩
  have havoiding : Continuous avoiding :=
    (hpath.prodMk continuous_const).subtype_mk _
  have hclosed (l : unitInterval) : (path l) 1 = (path l) 0 := by
    change H l (L * 1) = H l (L * 0)
    simp only [mul_one, mul_zero, H]
    rw [show B L = B 0 by simpa only [zero_add] using hpB 0,
      show D L = D 0 by simpa only [zero_add] using hpD 0]
  let inc : unitInterval → ℝ := pathArgumentIncrement ∘ avoiding
  have hinc : Continuous inc := continuous_pathArgumentIncrement.comp havoiding
  have hmaps : MapsTo inc univ (range ((↑) : ℤ → ℝ)) := by
    intro l _
    obtain ⟨n, hn⟩ := pathArgumentIncrement_integer_of_closed (avoiding l) (hclosed l)
    exact ⟨n, hn.symm⟩
  have hequal : inc (1 : unitInterval) = inc (0 : unitInterval) :=
    isPreconnected_univ.constant_of_mapsTo
      Real.isClosedEmbedding_intCast.isEmbedding.isInducing.isDiscrete_range
      hinc.continuousOn hmaps (mem_univ _) (mem_univ _)
  obtain ⟨v, hv, hproj, hvinc⟩ := positiveExit_positive_turn_unit_lift hturn
  let vI : C(unitInterval, ℝ) := ⟨fun t => v t, hv.comp continuous_subtype_val⟩
  have hinc0 : inc (0 : unitInterval) = 1 := by
    simp only [inc, Function.comp_apply, pathArgumentIncrement]
    rw [circlePathIncrement_eq_lift _ vI (fun t => by
      change (v t : UnitAddCircle) = normalizedArgument (H 0 (L * t) - 0)
      simpa only [H, Set.Icc.coe_zero, zero_smul, add_zero, sub_zero] using hproj t)]
    exact hvinc
  have hinc1 : inc (1 : unitInterval) = 1 := hequal.trans hinc0
  have hH1 (r : ℝ) : H 1 r = D r := by
    simp only [H, Set.Icc.coe_one, one_smul]
    ring
  have hne (r : ℝ) : D r ≠ 0 := by
    simpa only [hH1] using havoid 1 r
  let O : Set ℂ := {z | z ≠ 0}
  have hO : IsOpen O := isClosed_singleton.isOpen_compl
  obtain ⟨u, hu, huproj, _⟩ := annularAngularForm_exists_smooth_lift
    (F := id) (y := 0) hO contDiff_id.contDiffOn (fun z hz => hz)
    hD hne
  let uI : C(unitInterval, ℝ) :=
    ⟨fun t => u (L * t), hu.continuous.comp (continuous_const.mul continuous_subtype_val)⟩
  have huinc : u L - u 0 = 1 := by
    simp only [inc, Function.comp_apply, pathArgumentIncrement] at hinc1
    rw [circlePathIncrement_eq_lift _ uI (fun t => by
      change (u (L * t) : UnitAddCircle) = normalizedArgument (H 1 (L * t) - 0)
      simpa only [hH1, id_eq, sub_zero] using huproj (L * t))] at hinc1
    change u (L * 1) - u (L * 0) = 1 at hinc1
    simpa only [mul_one, mul_zero] using hinc1
  refine ⟨fun r => 2 * Real.pi * u r, continuous_const.mul hu.continuous, ?_, ?_⟩
  · intro r
    have he := congrArg AddCircle.toCircle (huproj r)
    simp only [id_eq, sub_zero] at he
    rw [exitBalancedTurn_direction, AddCircle.toCircle_apply_mk, div_one] at he
    exact he.symm
  · calc
      2 * Real.pi * u L - 2 * Real.pi * u 0 =
          2 * Real.pi * (u L - u 0) := by ring
      _ = 2 * Real.pi := by rw [huinc, mul_one]

/-- A genuine compact C0 neighborhood of an actual nonzero periodic
trace preserves its positive origin turn. The margin is constructed here. -/
theorem positiveExit_exists_argumentTurn_C0_threshold {B : ℝ → ℂ} {L : ℝ}
    (hL : 0 < L) (hB : ContDiff ℝ ∞ B) (hpB : Periodic B L)
    (hne : ∀ s, B s ≠ 0) (hturn : HasPositiveArgumentTurn B L) :
    ∃ ε > 0, ∀ D : ℝ → ℂ, ContDiff ℝ ∞ D → Periodic D L →
      (∀ s ∈ Icc (0 : ℝ) L, ‖D s - B s‖ < ε) →
      HasPositiveArgumentTurn D L ∧ (∀ s, D s ≠ 0) := by
  obtain ⟨r,hr,hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr hL.le) hB.continuous.norm.continuousOn
  have hε : 0 < ‖B r‖ := norm_pos_iff.mpr (hne r)
  have hrad (s : ℝ) : ‖B r‖ ≤ ‖B s‖ := by
    obtain ⟨n,hn,_⟩ := existsUnique_sub_zsmul_mem_Ico hL s 0
    simp only [mem_Ico,zero_add] at hn
    have hh := hmin (Ico_subset_Icc_self ⟨hn.1,hn.2⟩)
    change ‖B r‖ ≤ ‖B (s - n • L)‖ at hh
    rw [hpB.sub_zsmul_eq n] at hh
    exact hh
  have hnormturn : HasPositiveArgumentTurn (fun t => B (L*t)) 1 := by
    obtain ⟨phi,hphi,hproj,hinc⟩ := hturn
    refine ⟨fun t => phi (L*t), hphi.comp (continuous_const.mul continuous_id),
      fun t => hproj (L*t), ?_⟩
    simpa only [mul_one,mul_zero] using hinc
  refine ⟨‖B r‖,hε,?_⟩
  intro D hD hpD hclose
  have hperiod : Periodic (fun s => ‖D s - B s‖) L := by
    intro s
    change ‖D (s+L)-B (s+L)‖ = _
    rw [hpD s,hpB s]
  have hglobal (s : ℝ) : ‖D s-B s‖ < ‖B r‖ := by
    obtain ⟨n,hn,_⟩ := existsUnique_sub_zsmul_mem_Ico hL s 0
    simp only [mem_Ico,zero_add] at hn
    have hh := hclose (s-n • L) ⟨hn.1,hn.2.le⟩
    rw [hperiod.sub_zsmul_eq n] at hh
    exact hh
  refine ⟨positiveExit_argument_turn_of_uniform_close hB hD hpB hpD hrad hglobal hnormturn,?_⟩
  intro s he
  have hh := hglobal s
  rw [he,zero_sub,norm_neg] at hh
  exact (not_lt_of_ge (hrad s)) hh

/-- Choose this positive bound before the single corrected-speed construction.
Every smooth cell-periodic a within it gives the SAME actual balanced partner
one positive radian turn over its full period. No desired turn is an input. -/
theorem positiveExit_balancedPartner_positive_turn_threshold {N : ℕ}
    (hN : 10000 ≤ N) (e : ℝ ≃ₜ ℝ)
    (he : (e : ℝ → ℝ) = corrugatedSeedArcMap (N : ℝ))
    (hψ : ContDiff ℝ ∞ e.symm) :
    let ell := corrugatedSeedArcCell (N : ℝ)
    let L := (N : ℝ) * ell
    ∃ ηTurn > 0, ∀ a : ℝ → ℝ,
      ContDiff ℝ ∞ a → Periodic a ell →
      (∫ r in 0..ell, ‖a r - corrugatedSeedInitialSpeed (N : ℝ) e.symm r‖) < ηTurn →
      HasPositiveArgumentTurn (corrugatedSeedBalancedPartner (N : ℝ) e.symm ell a) L := by
  dsimp only
  let ell := corrugatedSeedArcCell (N : ℝ)
  let L := (N : ℝ) * ell
  let b := corrugatedSeedInitialSpeed (N : ℝ) e.symm
  let P := corrugatedSeedFrameHorizontal (N : ℝ) e.symm
  let B := corrugatedSeedBalancedPartner (N : ℝ) e.symm ell b
  have hNr : (10000 : ℝ) ≤ N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) < N := by linarith
  have hNz : N ≠ 0 := by omega
  have hell : 0 < ell := corrugatedSeedArcCell_pos hN1
  have hL : 0 < L := mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hNz)) hell
  have hb : ContDiff ℝ ∞ b := corrugatedSeedInitialSpeed_contDiff _ hψ
  have hP : ContDiff ℝ ∞ P := corrugatedSeedFrameHorizontal_contDiff _ hψ
  have hc := corrugatedSeedArcInverse_cell hN1 e he
  have hbperiod : Periodic b ell :=
    corrugatedSeedInitialSpeed_periodic (ne_of_gt (by linarith : (0 : ℝ) < N)) hc
  have hi (r : ℝ) : HasDerivAt e.symm
      (corrugatedSeedSphericalSpeed (N : ℝ) (e.symm r))⁻¹ r :=
    identityBand_arclengthInverse_hasDerivAt
      (corrugatedSeedSphericalSpeed_contDiff hN1).continuous
      (corrugatedSeedSphericalSpeed_pos hN1) e he r
  have hcell (r : ℝ) : P (r + ell) = corrugatedSeedRotation (N : ℝ) * P r :=
    corrugatedSeedFrameHorizontal_cell hN1 hψ hi hc r
  have hperiod (a : ℝ → ℝ) (ha : Continuous a) (hap : Periodic a ell) :
      Periodic (corrugatedSeedBalancedPartner (N : ℝ) e.symm ell a) L := by
    have h := covariantSpeedCurve_periodic ha hP.continuous hap hcell
      (corrugatedSeedRotation_ne_one hN1) N (corrugatedSeedRotation_pow hNz)
    intro r
    change Complex.I * covariantSpeedCurve ell (corrugatedSeedRotation (N : ℝ)) a P (r + L) = _
    rw [h r]
    rfl
  have hB : ContDiff ℝ ∞ B := corrugatedSeedBalancedPartner_contDiff _ _ hψ hb
  have hpB : Periodic B L := hperiod b hb.continuous hbperiod
  have hBeq : B = corrugatedSeedPartner (N : ℝ) ∘ e.symm :=
    corrugatedSeedBalancedPartner_initial hN1 hψ hc
  have hradius (r : ℝ) : (49 / 100 : ℝ) ≤ ‖B r‖ := by
    rw [hBeq]
    exact (corrugatedSeedPartner_radius_bounds hNr _).1
  have hz : e 0 = 0 := by rw [he]; simp [corrugatedSeedArcMap, rawPrimitive]
  have hsz : e.symm 0 = 0 := (congrArg e.symm hz.symm).trans (e.symm_apply_apply 0)
  have hfull : e (2 * Real.pi) = L := by
    rw [he]
    exact corrugatedSeedArcMap_full_period (by omega : 2 ≤ N)
  have hsfull : e.symm L = 2 * Real.pi :=
    (congrArg e.symm hfull.symm).trans (e.symm_apply_apply _)
  obtain ⟨φ, hφ, hφproj, hφinc⟩ := (corrugatedSeed_positive_argument_turns hN).2
  have hturn : HasPositiveArgumentTurn (fun t => B (L * t)) 1 := by
    refine ⟨fun t => φ (e.symm (L * t)),
      hφ.comp (e.symm.continuous.comp (continuous_const.mul continuous_id)), ?_, ?_⟩
    · intro t
      rw [hBeq]
      exact hφproj _
    · simpa only [mul_one, mul_zero, hsfull, hsz] using hφinc
  obtain ⟨ηTurn, hηTurn, hthreshold⟩ :=
    exists_covariantSpeedCurve_cell_L1_uniform_threshold
      (ξ := corrugatedSeedRotation (N : ℝ)) hb.continuous hP.continuous
      hbperiod hell N hNz (by norm_num : (0 : ℝ) < 1 / 8)
  refine ⟨ηTurn, hηTurn, ?_⟩
  intro a ha hap hsmall
  let D := corrugatedSeedBalancedPartner (N : ℝ) e.symm ell a
  have hD : ContDiff ℝ ∞ D := corrugatedSeedBalancedPartner_contDiff _ _ hψ ha
  have hpD : Periodic D L := hperiod a ha.continuous hap
  have hsmall' : (∫ r in 0..ell, |a r - b r|) < ηTurn := by
    simpa only [Real.norm_eq_abs] using hsmall
  have hclose0 (r : ℝ) (hr : r ∈ Icc 0 L) : ‖D r - B r‖ < (1 / 8 : ℝ) := by
    have hh := hthreshold a ha.continuous hap hsmall' r hr
    have hd : D r - B r = Complex.I *
        (covariantSpeedCurve ell (corrugatedSeedRotation (N : ℝ)) a P r -
          covariantSpeedCurve ell (corrugatedSeedRotation (N : ℝ)) b P r) := by
      dsimp only [D, B, corrugatedSeedBalancedPartner, P]
      ring
    rw [hd, norm_mul, Complex.norm_I, one_mul]
    exact hh
  have herrorperiod : Periodic (fun r => ‖D r - B r‖) L := by
    intro r
    change ‖D (r + L) - B (r + L)‖ = _
    rw [hpD r, hpB r]
  have hclose (r : ℝ) : ‖D r - B r‖ < (1 / 8 : ℝ) := by
    obtain ⟨n, hn, _⟩ := existsUnique_sub_zsmul_mem_Ico hL r 0
    simp only [mem_Ico, zero_add] at hn
    have hh := hclose0 (r - n • L) ⟨hn.1, hn.2.le⟩
    rw [herrorperiod.sub_zsmul_eq n] at hh
    exact hh
  exact positiveExit_argument_turn_of_uniform_close hB hD hpB hpD
    (fun r => (by norm_num : (1 / 8 : ℝ) ≤ 49 / 100).trans (hradius r)) hclose hturn

/-- The scalar threshold may be selected even before the existing whole seed
constructor selects its arclength homeomorphism. The actual ArcMap determines
that homeomorphism uniquely, so its SAME returned speed satisfies this turn
when the constructor is called with the minimum of its requested bound and ηTurn. -/
theorem positiveExit_balancedPartner_positive_turn_uniform_threshold {N : ℕ}
    (hN : 10000 ≤ N) :
    let ell := corrugatedSeedArcCell (N : ℝ)
    let L := (N : ℝ) * ell
    ∃ ηTurn > 0, ∀ e : ℝ ≃ₜ ℝ,
      (e : ℝ → ℝ) = corrugatedSeedArcMap (N : ℝ) → ∀ a : ℝ → ℝ,
      ContDiff ℝ ∞ a → Periodic a ell →
      (∫ r in 0..ell, ‖a r - corrugatedSeedInitialSpeed (N : ℝ) e.symm r‖) < ηTurn →
      HasPositiveArgumentTurn (corrugatedSeedBalancedPartner (N : ℝ) e.symm ell a) L := by
  dsimp only
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  obtain ⟨e₀, he₀, hψ₀, _⟩ := corrugatedSeed_exists_cell_arclength hN1
  obtain ⟨ηTurn, hηTurn, hthreshold⟩ :=
    positiveExit_balancedPartner_positive_turn_threshold hN e₀ he₀ hψ₀
  refine ⟨ηTurn, hηTurn, ?_⟩
  intro e he a ha hap hsmall
  have heq : e = e₀ := Homeomorph.ext (fun r => congrFun (he.trans he₀.symm) r)
  subst e
  exact hthreshold a ha hap hsmall

end
end TightVer401