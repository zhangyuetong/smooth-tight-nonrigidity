import TightVer401.IdentityBandBendingPullback
import TightVer401.RuledLeaves
import Mathlib.Topology.Order.Compact

/-! Strict protected levels for the same actual identity-flow inclusion and
compact bending. No geometric collar or new support potential is assumed. -/
namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.SmoothLocal.Geometry
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- The actual first-integral label on the original positive native band. -/
def positiveExitLevel {T w : ℝ} (d : PeriodicRuledFrame T)
    (hbalance : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0)
    (p : AddCircle T × Ioo (0 : ℝ) w) : ℝ :=
  1 / ((ruledRho_periodic d.period_τ).lift p.1 * (p.2 : ℝ)) -
    (periodicRuledFrame_omega_periodic d hbalance).lift p.1

/-- The lower endpoint of labels attained by the actual initial interval. -/
def positiveExitCompleteLower {T : ℝ} (d : PeriodicRuledFrame T) (δ : ℝ) : ℝ :=
  1 / (ruledRho d.τ 0 * δ) - ruledOmega d.k d.τ 0

theorem positiveExitLevel_continuous {T w : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T)
    (hbalance : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0) :
    Continuous (positiveExitLevel (w := w) d hbalance) := by
  have hρ : Continuous (ruledRho_periodic d.period_τ).lift :=
    (periodicLift_contMDiff (ruledRho_contDiff d.smooth_τ d.torsion_ne_zero)
      (ruledRho_periodic d.period_τ)).continuous
  have hω : Continuous (periodicRuledFrame_omega_periodic d hbalance).lift :=
    (periodicLift_contMDiff
      (OAI.ClosedSurfaceR4.PeriodicPrimitive.rawPrimitive_contDiff
        (ruledPeriodCoefficient_contDiff d.smooth_k d.smooth_τ d.torsion_ne_zero))
      (periodicRuledFrame_omega_periodic d hbalance)).continuous
  have hρne (q : AddCircle T) : (ruledRho_periodic d.period_τ).lift q ≠ 0 := by
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact (ruledRho_pos (d.torsion_ne_zero t)).ne'
  exact (continuous_const.div ((hρ.comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd))
    (fun p => mul_ne_zero (hρne _) p.2.property.1.ne')).sub
    (hω.comp continuous_fst)

private theorem positiveExit_flow_label_algebra {a b v W Ws : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hv : v ≠ 0)
    (hd : 1 + a * v * (W - Ws) ≠ 0) :
    1 / (b * (a * v / (b * (1 + a * v * (W - Ws))))) - W =
      1 / (a * v) - Ws := by
  field_simp [ha, hb, hv, hd]
  <;> ring

/-- Positivity of the actual in-band trajectory rules out a zero denominator. -/
theorem positiveExit_trajectory_denominator_ne_zero {T δ w : ℝ}
    (d : PeriodicRuledFrame T)
    (hinside : ∀ v ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 v t ∈ Ioo 0 w)
    {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) δ) (t : ℝ) :
    1 + ruledRho d.τ 0 * v * (ruledOmega d.k d.τ t - ruledOmega d.k d.τ 0) ≠ 0 := by
  intro hd
  have hp := (hinside v hv t).1
  simp only [principalTrajectory, hd, mul_zero, div_zero] at hp
  exact (lt_irrefl (0 : ℝ)) hp

/-- The same label identity in the actual unquotiented trajectory formula. -/
theorem positiveExit_trajectory_first_integral {T δ w : ℝ}
    (d : PeriodicRuledFrame T)
    (hinside : ∀ v ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 v t ∈ Ioo 0 w)
    {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) δ) (t : ℝ) :
    1 / (ruledRho d.τ t *
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 v t) -
      ruledOmega d.k d.τ t =
        1 / (ruledRho d.τ 0 * v) - ruledOmega d.k d.τ 0 := by
  exact positiveExit_flow_label_algebra (ruledRho_pos (d.torsion_ne_zero 0)).ne'
    (ruledRho_pos (d.torsion_ne_zero t)).ne' hv.1.ne'
    (positiveExit_trajectory_denominator_ne_zero d hinside hv t)
/-- The label is constant on each actual complete identity-flow leaf. -/
theorem positiveExitLevel_identityFlowBandInclusion {T δ w : ℝ}
    (d : PeriodicRuledFrame T)
    (hbalance : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0)
    (hinside : ∀ v ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 v t ∈ Ioo 0 w)
    (p : AddCircle T × Ioo (0 : ℝ) δ) :
    positiveExitLevel d hbalance (identityFlowBandInclusion d hbalance 0 hinside p) =
      1 / (ruledRho d.τ 0 * (p.2 : ℝ)) - ruledOmega d.k d.τ 0 := by
  rcases p with ⟨q, v⟩
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective q
  change 1 / (ruledRho d.τ t *
      (ruledRho d.τ 0 * (v : ℝ) / (ruledRho d.τ t *
        (1 + ruledRho d.τ 0 * (v : ℝ) *
          (ruledOmega d.k d.τ t - ruledOmega d.k d.τ 0))))) - ruledOmega d.k d.τ t = _
  exact positiveExit_flow_label_algebra (ruledRho_pos (d.torsion_ne_zero 0)).ne'
    (ruledRho_pos (d.torsion_ne_zero t)).ne' v.property.1.ne'
    (positiveExit_trajectory_denominator_ne_zero d hinside v.property t)

/-- Every label above the lower endpoint is realized by an actual initial value. -/
theorem positiveExit_initialLevel_range {T δ : ℝ} (d : PeriodicRuledFrame T)
    (hδ : 0 < δ) :
    range (fun v : Ioo (0 : ℝ) δ =>
      1 / (ruledRho d.τ 0 * (v : ℝ)) - ruledOmega d.k d.τ 0) =
      Ioi (positiveExitCompleteLower d δ) := by
  have hρ := ruledRho_pos (d.torsion_ne_zero 0)
  ext c
  constructor
  · rintro ⟨v, rfl⟩
    change 1 / (ruledRho d.τ 0 * δ) - ruledOmega d.k d.τ 0 < _
    exact sub_lt_sub_right (one_div_lt_one_div_of_lt (mul_pos hρ v.property.1)
      (mul_lt_mul_of_pos_left v.property.2 hρ)) _
  · intro hc
    change 1 / (ruledRho d.τ 0 * δ) - ruledOmega d.k d.τ 0 < c at hc
    have hv := ruledLeaf_in_band (ρ := ruledRho d.τ) («ω» := ruledOmega d.k d.τ)
      (c := c) (s := 0) (b := δ) hρ hδ hc
    have hcpos : 0 < c + ruledOmega d.k d.τ 0 := by
      have hp := one_div_pos.mpr (mul_pos hρ hδ)
      linarith
    exact ⟨⟨ruledLeaf (ruledRho d.τ) (ruledOmega d.k d.τ) c 0, hv⟩,
      ruledLeaf_first_integral (ρ := ruledRho d.τ) («ω» := ruledOmega d.k d.τ)
        (c := c) (s := 0) hρ.ne' hcpos.ne'⟩

/-- Exact actual label image of the given complete-flow annulus. -/
theorem positiveExitLevel_complete_image {T δ w : ℝ}
    (d : PeriodicRuledFrame T)
    (hbalance : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0)
    (hδ : 0 < δ)
    (hinside : ∀ v ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 v t ∈ Ioo 0 w) :
    positiveExitLevel d hbalance '' range (identityFlowBandInclusion d hbalance 0 hinside) =
      Ioi (positiveExitCompleteLower d δ) := by
  rw [← positiveExit_initialLevel_range d hδ]
  ext c
  constructor
  · rintro ⟨p, ⟨q, rfl⟩, hc⟩
    refine ⟨q.2, ?_⟩
    change 1 / (ruledRho d.τ 0 * (q.2 : ℝ)) - ruledOmega d.k d.τ 0 = c
    rw [← positiveExitLevel_identityFlowBandInclusion d hbalance hinside q]
    exact hc
  · rintro ⟨v, hv⟩
    let q : AddCircle T × Ioo (0 : ℝ) δ := (0, v)
    refine ⟨identityFlowBandInclusion d hbalance 0 hinside q, mem_range_self q, ?_⟩
    rw [positiveExitLevel_identityFlowBandInclusion]
    exact hv

/-- Compactness of the SAME protected field gives strict separated levels,
all realized inside the SAME actual complete-flow annulus. -/
theorem positiveExit_exists_protected_levels {T δ w : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T)
    (hbalance : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0)
    (hδ : 0 < δ)
    (hinside : ∀ v ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 v t ∈ Ioo 0 w)
    {Y : AddCircle T × Ioo (0 : ℝ) w → Ambient}
    (hcompact : HasCompactSupport Y) (hnonzero : ∃ p, Y p ≠ 0)
    (hprotect : tsupport Y ⊆ range (identityFlowBandInclusion d hbalance 0 hinside)) :
    ∃ c1 cminus cplus c2 : ℝ,
      positiveExitCompleteLower d δ < c1 ∧ c1 < cminus ∧
      cminus < cplus ∧ cplus < c2 ∧
      tsupport Y ⊆ (positiveExitLevel d hbalance) ⁻¹' Ioo cminus cplus ∧
      Icc c1 c2 ⊆ positiveExitLevel d hbalance ''
        range (identityFlowBandInclusion d hbalance 0 hinside) ∧
      Icc c1 c2 ⊆ range (fun v : Ioo (0 : ℝ) δ =>
        1 / (ruledRho d.τ 0 * (v : ℝ)) - ruledOmega d.k d.τ 0) := by
  let C := positiveExitLevel (w := w) d hbalance
  let cb := positiveExitCompleteLower d δ
  have hC : Continuous C := positiveExitLevel_continuous d hbalance
  have hK : IsCompact (tsupport Y) := hcompact
  obtain ⟨p0, hp0⟩ := hnonzero
  have hne : (tsupport Y).Nonempty := ⟨p0, subset_tsupport Y hp0⟩
  have hlower (p) (hp : p ∈ tsupport Y) : cb < C p := by
    have hi : C p ∈ positiveExitLevel d hbalance ''
        range (identityFlowBandInclusion d hbalance 0 hinside) :=
      ⟨p, hprotect hp, rfl⟩
    rw [positiveExitLevel_complete_image d hbalance hδ hinside] at hi
    exact hi
  obtain ⟨pmin, hpmin, hmin⟩ := hK.exists_isMinOn hne hC.continuousOn
  obtain ⟨pmax, hpmax, hmax⟩ := hK.exists_isMaxOn hne hC.continuousOn
  let m := C pmin
  let M := C pmax
  have hm : cb < m := hlower pmin hpmin
  have hmM : m ≤ M := hmin hpmax
  let c1 := cb + (m - cb) / 3
  let cminus := cb + 2 * (m - cb) / 3
  let cplus := M + 1
  let c2 := M + 2
  have hc1 : cb < c1 := by dsimp [c1]; linarith
  refine ⟨c1, cminus, cplus, c2, hc1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [c1, cminus]; linarith
  · dsimp [cminus, cplus]; linarith
  · dsimp [cplus, c2]; linarith
  · intro p hp
    have hmp : m ≤ C p := hmin hp
    have hpM : C p ≤ M := hmax hp
    change cminus < C p ∧ C p < cplus
    dsimp [cminus, cplus]
    constructor <;> linarith
  · rw [positiveExitLevel_complete_image d hbalance hδ hinside]
    intro c hc
    exact hc1.trans_le hc.1
  · rw [positiveExit_initialLevel_range d hδ]
    intro c hc
    exact hc1.trans_le hc.1

end
end TightVer401

