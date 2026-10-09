import TightVer401.PositiveExitConstructionSelectedSourceGeometryRoundFlow
import TightVer401.PositiveExitConstructionSelectedSourceGeometryFlowCore
import TightVer401.PositiveExitConstructionSeam

/-! Literal image of the SAME original flow on round polar parameters.
The full open radius-one/radius-two strip is exactly the already constructed
protected flow core; no Jordan domain or desired nesting is assumed. -/
namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.SmoothLocal.Geometry
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The raw round-flow source is the SAME selected original leaf in the
SAME native-to-Cartesian inverse chart. -/
theorem positiveExitSelected_roundFlowSource_eq_leaf
    {T δ w : ℝ} [Fact (0 < T)] (d : PeriodicRuledFrame T)
    (hb : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0)
    (hinside : ∀ u ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 u t ∈ Ioo 0 w)
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) Coord)
    (heF : ∀ p, e p = gnomonicInverse (d.bandGaussMap p))
    (vin vout : ℝ) (q : Coord)
    (hv : positiveExitSelected_roundFlowInitial vin vout (q 0) ∈ Ioo (0 : ℝ) δ) :
    positiveExitSelected_roundFlowSource d vin vout q =
      e (positiveExitLeaf d hb hinside ⟨positiveExitSelected_roundFlowInitial vin vout (q 0), hv⟩
        (periodProjection T (positiveExitSelected_roundFlowPhase T (q 1)))) := by
  rw [heF]
  rfl

/-- The full open round strip maps onto precisely the strict original flow
core between the SAME selected initial values. -/
theorem positiveExitSelected_roundFlowSource_image_open_band
    {T δ w : ℝ} [Fact (0 < T)] (d : PeriodicRuledFrame T)
    (hb : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0)
    (hinside : ∀ u ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 u t ∈ Ioo 0 w)
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) Coord)
    (heF : ∀ p, e p = gnomonicInverse (d.bandGaussMap p))
    (vin vout : Ioo (0 : ℝ) δ) (horder : (vin : ℝ) < (vout : ℝ)) :
    positiveExitSelected_roundFlowSource d vin vout '' {q : Coord | 1 < q 0 ∧ q 0 < 2} =
      positiveExit_selectedSourceGeometry_flowCore d hb hinside e vin vout := by
  have hdiff : 0 < (vout : ℝ) - (vin : ℝ) := sub_pos.mpr horder
  apply Set.Subset.antisymm
  · rintro x ⟨q, hq, rfl⟩
    let u := positiveExitSelected_roundFlowInitial vin vout (q 0)
    have hu : (vin : ℝ) < u ∧ u < (vout : ℝ) := by
      dsimp [u, positiveExitSelected_roundFlowInitial]
      constructor <;> nlinarith [mul_pos (sub_pos.mpr hq.1) hdiff,
        mul_pos (sub_pos.mpr hq.2) hdiff]
    have hv : u ∈ Ioo (0 : ℝ) δ := ⟨vin.property.1.trans hu.1, hu.2.trans vout.property.2⟩
    let v : Ioo (0 : ℝ) δ := ⟨u, hv⟩
    let s := periodProjection T (positiveExitSelected_roundFlowPhase T (q 1))
    refine ⟨positiveExitLeaf d hb hinside v s, ⟨(s, v), hu, rfl⟩, ?_⟩
    exact (positiveExitSelected_roundFlowSource_eq_leaf d hb hinside e heF vin vout q hv).symm
  · rintro x ⟨z, ⟨p, hp, hpz⟩, hzx⟩
    obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective p.1
    let r : ℝ := 1 + ((p.2 : ℝ) - (vin : ℝ)) / ((vout : ℝ) - (vin : ℝ))
    let theta : ℝ := 2 * Real.pi * t / T
    let q : Coord := ![r, theta]
    have hr : 1 < r ∧ r < 2 := by
      have hf0 := div_pos (sub_pos.mpr hp.1) hdiff
      have hf1 : ((p.2 : ℝ) - (vin : ℝ)) / ((vout : ℝ) - (vin : ℝ)) < 1 :=
        (div_lt_one hdiff).mpr (by linarith [hp.2])
      dsimp [r]
      constructor <;> linarith
    have hi : positiveExitSelected_roundFlowInitial vin vout (q 0) = (p.2 : ℝ) := by
      dsimp [positiveExitSelected_roundFlowInitial, q, r]
      field_simp [hdiff.ne']
      <;> ring
    have hs : positiveExitSelected_roundFlowPhase T (q 1) = t := by
      have hT : T ≠ 0 := (Fact.out : 0 < T).ne'
      dsimp [positiveExitSelected_roundFlowPhase, q, theta]
      field_simp [hT, Real.pi_ne_zero]
      <;> ring
    have hv : positiveExitSelected_roundFlowInitial vin vout (q 0) ∈ Ioo (0 : ℝ) δ := by
      rw [hi]
      exact p.2.property
    refine ⟨q, hr, ?_⟩
    rw [positiveExitSelected_roundFlowSource_eq_leaf d hb hinside e heF vin vout q hv]
    have hparams :
        (periodProjection T (positiveExitSelected_roundFlowPhase T (q 1)),
          (⟨positiveExitSelected_roundFlowInitial vin vout (q 0), hv⟩ : Ioo (0 : ℝ) δ)) = p :=
      Prod.ext (by rw [hs]; exact ht) (Subtype.ext hi)
    change e (identityFlowBandInclusion d hb 0 hinside _) = x
    rw [hparams, hpz, hzx]

end
end TightVer401
