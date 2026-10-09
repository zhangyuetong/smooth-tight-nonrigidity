import TightVer401.PositiveExitConstructionContract
import TightVer401.AnnularDegreeJordanWinding
import TightVer401.DualRadialCompletionTraceDefinitions
import TightVer401.PeriodicPlanarSchoenflies

/-! Positive-exit consumer bridge: a positive actual origin turn determines
unit winding at EVERY interior point of the actual filled Jordan disk.
The moving-point step uses the published annularLoopIncrementOn_eq producer;
the covering lifts and fillings use the retained pinned constructions. -/
namespace TightVer401
noncomputable section
open Set Function Filter Metric OAI.SmoothLocal.Geometry
open OAI.CircleDomainRigidity OAI.CircleDomainRigidity.FiniteTransfer
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

private theorem exitWinding_normalized_direction (z : ℂ) :
    AddCircle.toCircle (normalizedArgument z) = complexCircleDirection z := by
  rw [normalizedArgument_eq, AddCircle.toCircle_apply_mk, div_one]
  have he : 2 * Real.pi * (z.arg / (2 * Real.pi)) = z.arg := by
    field_simp
  rw [he]
  apply Subtype.ext
  simpa only [Circle.coe_exp] using (complexCircleDirection_coe z).symm

/-- The actual radian origin lift becomes a unit-turn quotient lift. -/
theorem positiveExit_positive_turn_unit_lift {γ : ℝ → ℂ} {L : ℝ}
    (hturn : HasPositiveArgumentTurn γ L) :
    ∃ u : ℝ → ℝ, Continuous u ∧
      (∀ t, (u t : UnitAddCircle) = normalizedArgument (γ t)) ∧ u L - u 0 = 1 := by
  obtain ⟨φ, hφ, hproj, hinc⟩ := hturn
  refine ⟨fun t => φ t / (2 * Real.pi), hφ.div_const _, ?_, ?_⟩
  · intro t
    apply AddCircle.injective_toCircle one_ne_zero
    rw [exitWinding_normalized_direction, AddCircle.toCircle_apply_mk, div_one]
    have he : 2 * Real.pi * (φ t / (2 * Real.pi)) = φ t := by field_simp
    rw [he]
    exact (hproj t).symm
  · calc
      φ L / (2 * Real.pi) - φ 0 / (2 * Real.pi) =
          (φ L - φ 0) / (2 * Real.pi) := by ring
      _ = 1 := by rw [hinc, div_self Real.two_pi_pos.ne']

/-- Actual smooth circle charts promote the continuous turn lift to a
smooth lift at the SAME period. No smooth phase is assumed. -/
theorem positiveExit_positive_turn_smooth_unit_lift {γ : ℝ → ℂ} {L : ℝ}
    (hγ : ContDiff ℝ ∞ γ) (hzero : ∀ t, γ t ≠ 0)
    (hturn : HasPositiveArgumentTurn γ L) :
    ∃ u : ℝ → ℝ, ContDiff ℝ ∞ u ∧
      (∀ t, (u t : UnitAddCircle) = normalizedArgument (γ t)) ∧ u L - u 0 = 1 := by
  obtain ⟨u,hu,hproj,hinc⟩ := positiveExit_positive_turn_unit_lift hturn
  have hs : SmoothCircleOn normalizedArgument ({0}ᶜ : Set ℂ) := by
    intro z hz a ha
    have hza : normalizedArgument (z - 0) ≠ (a : UnitAddCircle) := by simpa using ha
    simpa only [centeredArgument, sub_zero] using smoothCircleOn_centeredArgument 0 z hz a hza
  exact ⟨u,annular_contDiff_real_lift_along hs hγ (fun t => hzero t) hu hproj,hproj,hinc⟩

/-- Construct a smooth radian argument with its full period shift.
The shift is derived from the actual periodic curve and the pinned integer
quotient equality; it is not assumed as an angular descent package. -/
theorem positiveExit_actual_positive_argument_lift {γ : ℝ → ℂ} {L : ℝ}
    (hγ : ContDiff ℝ ∞ γ) (hp : Periodic γ L) (hzero : ∀ t, γ t ≠ 0)
    (hturn : HasPositiveArgumentTurn γ L) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧
      (∀ t, complexCircleDirection (γ t) = Circle.exp (φ t)) ∧
      ∀ t, φ (t+L) = φ t + 2*Real.pi := by
  obtain ⟨u,hu,hproj,hinc⟩ := positiveExit_positive_turn_smooth_unit_lift hγ hzero hturn
  have hint (t : ℝ) : ∃ k : ℤ, u (t+L) - u t = (k : ℝ) := by
    have he : (u (t+L) : UnitAddCircle) = (u t : UnitAddCircle) := by
      rw [hproj,hproj,hp t]
    obtain ⟨k,hk⟩ := (addCircle_eq_iff_exists_int 1 (u (t+L)) (u t)).mp he
    refine ⟨k,?_⟩
    rw [mul_one] at hk
    exact sub_eq_iff_eq_add.mpr (hk.trans (add_comm _ _))
  choose k hk using hint
  have hcast : (fun t => (k t : ℝ)) = (fun t => u (t+L) - u t) := by
    funext t
    exact (hk t).symm
  have hkc : Continuous k := by
    apply Real.isClosedEmbedding_intCast.isEmbedding.isInducing.continuous_iff.mpr
    change Continuous (fun t => (k t : ℝ))
    rw [hcast]
    exact (hu.continuous.comp (continuous_id.add continuous_const)).sub hu.continuous
  have hsame (t : ℝ) : k t = k 0 :=
    (isPreconnected_range hkc).subsingleton (mem_range_self t) (mem_range_self 0)
  have hshift (t : ℝ) : u (t+L) - u t = 1 := by
    rw [hk t,hsame]
    have h0 := hk 0
    simp only [zero_add] at h0
    exact h0.symm.trans hinc
  refine ⟨fun t => 2*Real.pi*u t,contDiff_const.mul hu,?_,?_⟩
  · intro t
    rw [← exitWinding_normalized_direction,← hproj,AddCircle.toCircle_apply_mk,div_one]
  · intro t
    have ht := hshift t
    dsimp only
    linear_combination (2*Real.pi)*ht

/-- Actual origin winding propagates to every point of the actual connected
filled interior. A positive unit lift is constructed at each such point. -/
theorem positiveExit_positive_turn_all_interior_lifts {γ : ℝ → ℂ}
    (hγ : Continuous γ) (hClosed : γ 1 = γ 0)
    (hturn : HasPositiveArgumentTurn γ 1) (H : ℂ ≃ₜ ℂ)
    (hboundary : range γ ⊆ frontier (jordanInterior H))
    (h0 : (0 : ℂ) ∈ jordanInterior H) :
    ∀ z ∈ jordanInterior H, ∃ u : C(unitInterval, ℝ),
      (∀ t, (u t : UnitAddCircle) = normalizedArgument (γ t - z)) ∧ u 1 = u 0 + 1 := by
  have hAvoid : ∀ z ∈ jordanInterior H, ∀ t, γ t ≠ z := by
    intro z hz t he
    have ht := hboundary (mem_range_self t)
    rw [(jordanInterior_isOpen H).frontier_eq] at ht
    exact ht.2 (he.symm ▸ hz)
  obtain ⟨v, hv, hproj, hinc⟩ := positiveExit_positive_turn_unit_lift hturn
  let vI : C(unitInterval, ℝ) := ⟨fun t => v t, hv.comp continuous_subtype_val⟩
  have hinc0 : annularLoopIncrementOn γ hγ (jordanInterior H) hAvoid ⟨0, h0⟩ = 1 := by
    unfold annularLoopIncrementOn pathArgumentIncrement
    rw [circlePathIncrement_eq_lift _ vI (fun t => by
      change (v t : UnitAddCircle) = normalizedArgument (γ t - 0)
      simpa only [sub_zero] using hproj t)]
    exact hinc
  intro z hz
  let p : AvoidingPathPoint := ⟨(annularLoopPath γ hγ, z), by
    rintro ⟨t, ht⟩
    exact hAvoid z hz t ht⟩
  let u := realCirclePathLift (pathArgument p)
  refine ⟨u, fun t => realCirclePathLift_projects (pathArgument p) t, ?_⟩
  have hi := (annularLoopIncrementOn_eq γ hγ hClosed (jordanInterior H)
    (isConnected_jordanInterior H).isPreconnected hAvoid ⟨z, hz⟩ ⟨0, h0⟩).trans hinc0
  change u 1 - u 0 = 1 at hi
  linarith

private theorem exitWinding_periodic_image {γ : ℝ → ℂ} (hp : Periodic γ 1) :
    γ '' Icc 0 1 = range γ := by
  apply Subset.antisymm (image_subset_range _ _)
  rintro z ⟨t, rfl⟩
  let x := AddCircle.equivIco (1 : ℝ) 0 (t : UnitAddCircle)
  have hx : (x : ℝ) ∈ Icc 0 1 := by
    apply Ico_subset_Icc_self
    simpa only [zero_add] using x.property
  have hq : ((x : ℝ) : UnitAddCircle) = (t : UnitAddCircle) := AddCircle.coe_equivIco
  refine ⟨x, hx, ?_⟩
  rw [← hp.lift_coe (x : ℝ), ← hp.lift_coe t, hq]

/-- Construct the actual filling and all the ordinary positive boundary
fields required by the completion consumer from an actual regular loop. -/
theorem positiveExit_positive_turn_exists_completion_trace {γ : ℝ → ℂ}
    (hγ : ContDiff ℝ ∞ γ) (hp : Periodic γ 1) (hi : InjOn γ (Ico 0 1))
    (hregular : ∀ t, deriv γ t ≠ 0) (hne : ∀ t, γ t ≠ 0)
    (hturn : HasPositiveArgumentTurn γ 1) :
    ∃ H : ℂ ≃ₜ ℂ, DualRadialCompletionPositiveTrace H γ ∧
      (0 : ℂ) ∈ H '' ball (0 : ℂ) 1 := by
  letI : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  obtain ⟨H, hfill⟩ := periodicComplexCurve_exists_filling hγ hp hi
  have hClosed : γ 1 = γ 0 := by simpa only [zero_add] using hp 0
  have hturnSave := hturn
  obtain ⟨φ, hφ, hproj, hinc⟩ := hturn
  have hφne : φ 1 ≠ φ 0 := by
    intro he
    rw [he, sub_self] at hinc
    exact Real.two_pi_pos.ne' hinc.symm
  have h0 : (0 : ℂ) ∈ H '' ball (0 : ℂ) 1 :=
    winding_origin_inside complexCircleDirection_continuousOn hγ.continuous hφ
      hfill hne hClosed hproj hφne
  have hb : range γ = frontier (jordanInterior H) := by
    rw [frontier_jordanInterior]
    exact hfill
  refine ⟨H, ⟨hγ, hp, hi, hregular, ?_, ?_⟩, h0⟩
  · rw [exitWinding_periodic_image hp]
    exact hb
  · exact positiveExit_positive_turn_all_interior_lifts hγ.continuous hClosed hturnSave H hb.subset h0

private def exitWinding_complexCLM : Coord →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (ContinuousLinearMap.proj (R := ℝ) 0) +
    Complex.I • (Complex.ofRealCLM.comp (ContinuousLinearMap.proj (R := ℝ) 1))

private theorem exitWinding_complexCLM_eq :
    (exitWinding_complexCLM : Coord → ℂ) = positiveExitComplexPoint := by
  ext q
  apply Complex.ext <;> simp [exitWinding_complexCLM, positiveExitComplexPoint,
    Complex.mul_re, Complex.mul_im]

private theorem exitWinding_complex_injective : Injective positiveExitComplexPoint := by
  intro p q he
  have hre := congrArg Complex.re he
  have him := congrArg Complex.im he
  ext i
  fin_cases i
  · exact hre
  · exact him

private theorem exitWinding_coordinate_trace {p : ℝ → Coord}
    (hs : ContDiff ℝ ∞ p) (hp : Periodic p 1) (hi : Injective hp.lift)
    (hregular : ∀ t, deriv p t ≠ 0) (hne : ∀ t, p t ≠ 0)
    (hturn : HasPositiveArgumentTurn (positiveExitComplexTrace p) 1) :
    ∃ H : ℂ ≃ₜ ℂ, DualRadialCompletionPositiveTrace H (positiveExitComplexTrace p) ∧
      (0 : ℂ) ∈ H '' ball (0 : ℂ) 1 := by
  have hcs : ContDiff ℝ ∞ positiveExitComplexPoint := by
    rw [← exitWinding_complexCLM_eq]
    exact exitWinding_complexCLM.contDiff
  have hγ : ContDiff ℝ ∞ (positiveExitComplexTrace p) := hcs.comp hs
  have hperiod : Periodic (positiveExitComplexTrace p) 1 :=
    fun s => congrArg positiveExitComplexPoint (hp s)
  have hinj : InjOn (positiveExitComplexTrace p) (Ico 0 1) := by
    intro s hs' t ht' he
    have he' : p s = p t := exitWinding_complex_injective he
    have hq : (s : UnitAddCircle) = (t : UnitAddCircle) := by
      apply hi
      simpa only [hp.lift_coe] using he'
    exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) (a := (0 : ℝ))
      (by simpa only [zero_add] using hs') (by simpa only [zero_add] using ht')).mp hq
  have hd (s) : HasDerivAt (positiveExitComplexTrace p)
      (positiveExitComplexPoint (deriv p s)) s := by
    have h := exitWinding_complexCLM.hasFDerivAt.comp_hasDerivAt s
      ((hs.differentiable (by simp) s).hasDerivAt)
    simpa only [exitWinding_complexCLM_eq, positiveExitComplexTrace] using h
  have hreg (s) : deriv (positiveExitComplexTrace p) s ≠ 0 := by
    rw [(hd s).deriv]
    intro he
    apply hregular s
    apply exitWinding_complex_injective
    exact he.trans (by rfl : (0 : ℂ) = positiveExitComplexPoint (0 : Coord))
  have hn (s) : positiveExitComplexTrace p s ≠ 0 := by
    intro he
    apply hne s
    apply exitWinding_complex_injective
    change positiveExitComplexPoint (p s) = 0 at he
    exact he.trans (by rfl : (0 : ℂ) = positiveExitComplexPoint (0 : Coord))
  exact positiveExit_positive_turn_exists_completion_trace hγ hperiod hinj hreg hn hturn

/-- A normalized actual positive exit trace supplies BOTH completed positive
Jordan input traces, including unit lifts about every actual interior point.
Both filling homeomorphisms are constructed here, not input as packages. -/
theorem positiveExitTrace_exists_completion_positive_traces {G : Coord → ℝ}
    {U : Set Coord} (h : PositiveExitTrace G U 1) :
    ∃ Hp Hg : ℂ ≃ₜ ℂ,
      DualRadialCompletionPositiveTrace Hp (positiveExitComplexTrace h.p) ∧
      DualRadialCompletionPositiveTrace Hg (positiveExitComplexTrace h.gamma) ∧
      (0 : ℂ) ∈ Hp '' ball (0 : ℂ) 1 ∧ (0 : ℂ) ∈ Hg '' ball (0 : ℂ) 1 := by
  obtain ⟨Hp, hp, hp0⟩ := exitWinding_coordinate_trace h.p_smooth h.p_periodic
    h.source_injective h.source_regular h.source_nonzero h.source_turn
  obtain ⟨Hg, hg, hg0⟩ := exitWinding_coordinate_trace h.gamma_smooth h.gamma_periodic
    h.gradient_injective h.gradient_regular h.gradient_nonzero h.gradient_turn
  exact ⟨Hp, Hg, hp, hg, hp0, hg0⟩

end
end TightVer401
