import TightVer401.PeriodicRuledNativeGauss
import TightVer401.PositiveExitConstructionSelectedSourceGeometryGaussBand
import TightVer401.PositiveExitConstructionSelectedSourceGeometryFlowDerivative
import TightVer401.VisibleConnectorSourceInverseJacobian

/-! Literal raw selected-flow source on polar parameters. The selected initial
values and the original complete flow are retained once; no coordinate
orientation or Jacobian sign is an input. This is the polar-parameter map,
not yet its descended Cartesian map on the round annulus. -/
namespace TightVer401
noncomputable section
open Set Filter MeasureTheory OAI.SmoothLocal.Geometry
open OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

def positiveExitSelected_roundFlowInitial (vin vout r : ℝ) : ℝ :=
  vin + (r - 1) * (vout - vin)

def positiveExitSelected_roundFlowPhase (T theta : ℝ) : ℝ :=
  T * theta / (2 * Real.pi)

def positiveExitSelected_roundFlowParameters (T vin vout : ℝ) (q : Coord) : Coord :=
  ![positiveExitSelected_roundFlowPhase T (q 1), positiveExitSelected_roundFlowInitial vin vout (q 0)]

def positiveExitSelected_flowRawHeight {T : ℝ} (d : PeriodicRuledFrame T) (q : Coord) : ℝ :=
  principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 (q 1) (q 0)

def positiveExitSelected_flowRaw {T : ℝ} (d : PeriodicRuledFrame T) (q : Coord) : Coord :=
  ![q 0, positiveExitSelected_flowRawHeight d q]

def positiveExitSelected_roundFlowRaw {T : ℝ} (d : PeriodicRuledFrame T)
    (vin vout : ℝ) (q : Coord) : Coord :=
  ![positiveExitSelected_roundFlowPhase T (q 1),
    principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0
      (positiveExitSelected_roundFlowInitial vin vout (q 0))
      (positiveExitSelected_roundFlowPhase T (q 1))]

def positiveExitSelected_roundFlowSource {T : ℝ} (d : PeriodicRuledFrame T)
    (vin vout : ℝ) : Coord → Coord :=
  gnomonicInverse ∘ d.rawGaussMap ∘ positiveExitSelected_roundFlowRaw d vin vout

def positiveExitSelected_roundFlowDomain (δ vin vout : ℝ) : Set Coord :=
  {q | positiveExitSelected_roundFlowInitial vin vout (q 0) ∈ Ioo (0 : ℝ) δ}

theorem positiveExitSelected_roundFlowRaw_comp {T : ℝ} (d : PeriodicRuledFrame T)
    (vin vout : ℝ) :
    positiveExitSelected_roundFlowRaw d vin vout =
      positiveExitSelected_flowRaw d ∘ positiveExitSelected_roundFlowParameters T vin vout := rfl

theorem positiveExitSelected_roundFlowParameters_contDiff (T vin vout : ℝ) :
    ContDiff ℝ ∞ (positiveExitSelected_roundFlowParameters T vin vout) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> simp only [positiveExitSelected_roundFlowParameters,
    positiveExitSelected_roundFlowInitial, positiveExitSelected_roundFlowPhase,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  · exact (contDiff_const.mul (contDiff_apply ℝ ℝ 1)).div_const (2 * Real.pi)
  · exact contDiff_const.add (((contDiff_apply ℝ ℝ 0).sub contDiff_const).mul contDiff_const)

theorem positiveExitSelected_roundFlowDomain_isOpen (δ vin vout : ℝ) :
    IsOpen (positiveExitSelected_roundFlowDomain δ vin vout) := by
  exact isOpen_Ioo.preimage
    ((continuous_const.add ((continuous_apply 0).sub continuous_const |>.mul continuous_const)))

/-- Smooth actual complete flow on the entire original initial interval. -/
theorem positiveExitSelected_flowRawHeight_contDiffOn
    {T δ w : ℝ} (d : PeriodicRuledFrame T)
    (hinside : ∀ u ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 u t ∈ Ioo 0 w) :
    ContDiffOn ℝ ∞ (positiveExitSelected_flowRawHeight d) {q : Coord | q 1 ∈ Ioo (0 : ℝ) δ} := by
  have hρ : ContDiff ℝ ∞ (fun q : Coord => ruledRho d.τ (q 0)) :=
    (ruledRho_contDiff d.smooth_τ d.torsion_ne_zero).comp (contDiff_apply ℝ ℝ 0)
  have hW : ContDiff ℝ ∞ (fun q : Coord => ruledOmega d.k d.τ (q 0)) :=
    (rawPrimitive_contDiff (ruledPeriodCoefficient_contDiff d.smooth_k d.smooth_τ
      d.torsion_ne_zero)).comp (contDiff_apply ℝ ℝ 0)
  have hnum : ContDiff ℝ ∞ (fun q : Coord => ruledRho d.τ 0 * q 1) :=
    contDiff_const.mul (contDiff_apply ℝ ℝ 1)
  have hden : ContDiff ℝ ∞ (fun q : Coord => ruledRho d.τ (q 0) *
      (1 + ruledRho d.τ 0 * q 1 * (ruledOmega d.k d.τ (q 0) - ruledOmega d.k d.τ 0))) :=
    hρ.mul (contDiff_const.add (hnum.mul (hW.sub contDiff_const)))
  exact hnum.contDiffOn.div hden.contDiffOn (fun q hq =>
    mul_ne_zero (ruledRho_pos (d.torsion_ne_zero (q 0))).ne'
      (positiveExit_trajectory_denominator_ne_zero d hinside hq (q 0)))

theorem positiveExitSelected_flowRaw_contDiffOn
    {T δ w : ℝ} (d : PeriodicRuledFrame T)
    (hinside : ∀ u ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 u t ∈ Ioo 0 w) :
    ContDiffOn ℝ ∞ (positiveExitSelected_flowRaw d) {q : Coord | q 1 ∈ Ioo (0 : ℝ) δ} := by
  apply contDiffOn_pi.mpr
  intro i
  fin_cases i
  · exact (contDiff_apply ℝ ℝ 0).contDiffOn
  · exact positiveExitSelected_flowRawHeight_contDiffOn d hinside

/-- The initial coordinate is unchanged, so the actual flow Jacobian is its
produced positive initial-value derivative. -/
theorem positiveExitSelected_flowRawHeight_partial_initial
    {T δ w : ℝ} (d : PeriodicRuledFrame T)
    (hinside : ∀ u ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 u t ∈ Ioo 0 w)
    {q : Coord} (hq : q 1 ∈ Ioo (0 : ℝ) δ) :
    coordPartial 1 (positiveExitSelected_flowRawHeight d) q =
      ruledRho d.τ 0 / (ruledRho d.τ (q 0) *
        (1 + ruledRho d.τ 0 * q 1 * (ruledOmega d.k d.τ (q 0) - ruledOmega d.k d.τ 0))^2) := by
  have hU : IsOpen {q : Coord | q 1 ∈ Ioo (0 : ℝ) δ} :=
    isOpen_Ioo.preimage (continuous_apply 1)
  have hH := ((positiveExitSelected_flowRawHeight_contDiffOn d hinside) q hq).contDiffAt
    (hU.mem_nhds hq) |>.differentiableAt (by simp)
  have hpath : HasDerivAt (fun u => (![q 0, u] : Coord)) (Pi.single 1 (1 : ℝ) : Coord) (q 1) := by
    have he : (fun u => (![q 0, u] : Coord)) = Function.update (![q 0, 0] : Coord) 1 := by
      funext u i
      fin_cases i <;> simp
    rw [he]
    exact hasDerivAt_update _ _ _
  have he : (![q 0, q 1] : Coord) = q := by ext i; fin_cases i <;> rfl
  have hH' : DifferentiableAt ℝ (positiveExitSelected_flowRawHeight d) (![q 0, q 1] : Coord) := by rw [he]; exact hH
  have hd := hH'.hasFDerivAt.comp_hasDerivAt (q 1) hpath
  rw [he] at hd
  change HasDerivAt
    (fun u => principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 u (q 0))
    (coordPartial 1 (positiveExitSelected_flowRawHeight d) q) (q 1) at hd
  exact hd.unique (positiveExit_selectedSourceGeometry_ruledFlow_initialValue_deriv_pos d hinside hq (q 0)).1

private theorem selectedRoundFlow_component_partial
    {F : Coord → Coord} {q : Coord} (hF : DifferentiableAt ℝ F q) (i a : Fin 2) :
    coordPartial i (fun p => F p a) q = coordPartial i F q a := by
  have hc := (hasFDerivAt_apply (𝕜 := ℝ) a (F q)).comp q hF.hasFDerivAt
  have hc' := hc.congr_of_eventuallyEq (f₁ := fun p => F p a)
    (Eventually.of_forall (fun _ => rfl))
  unfold coordPartial
  rw [hc'.fderiv]
  rfl

private theorem selectedRoundFlow_annular_eq_seam
    {F : Coord → Coord} {q : Coord} (hF : DifferentiableAt ℝ F q) :
    annularJacobian F q = (seamCoordinateJacobian F q).det := by
  rw [annularJacobian, ← LinearMap.det_toMatrix', Matrix.det_fin_two, Matrix.det_fin_two]
  simp only [LinearMap.toMatrix'_apply, seamCoordinateJacobian,
    selectedRoundFlow_component_partial hF, ContinuousLinearMap.coe_coe]
  rfl

/-- The actual raw flow determinant is positive throughout the original
complete initial interval, without any shrinking. -/
theorem positiveExitSelected_flowRaw_jacobian_pos
    {T δ w : ℝ} (d : PeriodicRuledFrame T)
    (hinside : ∀ u ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 u t ∈ Ioo 0 w)
    {q : Coord} (hq : q 1 ∈ Ioo (0 : ℝ) δ) :
    0 < annularJacobian (positiveExitSelected_flowRaw d) q := by
  have hU : IsOpen {q : Coord | q 1 ∈ Ioo (0 : ℝ) δ} :=
    isOpen_Ioo.preimage (continuous_apply 1)
  have hQ := ((positiveExitSelected_flowRaw_contDiffOn d hinside) q hq).contDiffAt
    (hU.mem_nhds hq) |>.differentiableAt (by simp)
  rw [selectedRoundFlow_annular_eq_seam hQ, Matrix.det_fin_two]
  change 0 < coordPartial 0 (fun p : Coord => p 0) q *
    coordPartial 1 (positiveExitSelected_flowRawHeight d) q -
    coordPartial 1 (fun p : Coord => p 0) q * coordPartial 0 (positiveExitSelected_flowRawHeight d) q
  rw [coordPartial_proj, coordPartial_proj, positiveExitSelected_flowRawHeight_partial_initial d hinside hq]
  simp only [Pi.single_eq_same, Pi.single_eq_of_ne (show (0 : Fin 2) ≠ 1 by decide),
    one_mul, zero_mul, sub_zero]
  exact div_pos (ruledRho_pos (d.torsion_ne_zero 0))
    (mul_pos (ruledRho_pos (d.torsion_ne_zero (q 0)))
      (sq_pos_of_ne_zero (positiveExit_trajectory_denominator_ne_zero d hinside hq (q 0))))

/-- Actual phase-first, initial-value-second affine parameter determinant. -/
theorem positiveExitSelected_roundFlowParameters_jacobian (T vin vout : ℝ) (q : Coord) :
    annularJacobian (positiveExitSelected_roundFlowParameters T vin vout) q =
      -(T / (2 * Real.pi)) * (vout - vin) := by
  have hs := ((ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2)).hasFDerivAt (x := q)).const_mul (T / (2 * Real.pi))
  have hphasefn : (fun p : Coord => T * p 1 / (2 * Real.pi)) =
      (fun p : Coord => (T / (2 * Real.pi)) * p 1) := by funext p; ring
  have ha := (hasFDerivAt_const vin q).add
    ((((ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)).hasFDerivAt (x := q)).sub_const 1).mul_const (vout - vin))
  have hsF : fderiv ℝ (fun p : Coord => (T / (2 * Real.pi)) * p 1) q =
      (T / (2 * Real.pi)) • ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2) := by
    simpa using hs.fderiv
  have haF : fderiv ℝ (fun p : Coord => vin + (p 0 - 1) * (vout - vin)) q =
      (vout - vin) • ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2) := by
    have ha' := ha.congr_of_eventuallyEq (f₁ := fun p : Coord => vin + (p 0 - 1) * (vout - vin))
      (Eventually.of_forall (fun _ => rfl))
    simpa only [zero_add] using ha'.fderiv
  have hj : seamCoordinateJacobian (positiveExitSelected_roundFlowParameters T vin vout) q =
      (!![0, T / (2 * Real.pi); vout - vin, 0] : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext a i
    fin_cases a <;> fin_cases i
    · change fderiv ℝ (fun p : Coord => T * p 1 / (2 * Real.pi)) q (Pi.single (0 : Fin 2) 1) = 0
      rw [hphasefn, hsF]
      simp
    · change fderiv ℝ (fun p : Coord => T * p 1 / (2 * Real.pi)) q (Pi.single (1 : Fin 2) 1) = T / (2 * Real.pi)
      rw [hphasefn, hsF]
      simp
    · change fderiv ℝ (fun p : Coord => vin + (p 0 - 1) * (vout - vin)) q (Pi.single (0 : Fin 2) 1) = vout - vin
      rw [haF]
      simp
    · change fderiv ℝ (fun p : Coord => vin + (p 0 - 1) * (vout - vin)) q (Pi.single (1 : Fin 2) 1) = 0
      rw [haF]
      simp
  rw [selectedRoundFlow_annular_eq_seam
    ((positiveExitSelected_roundFlowParameters_contDiff T vin vout).differentiable (by simp) q),
    hj, Matrix.det_fin_two]
  simp

theorem positiveExitSelected_roundFlowRaw_contDiffOn
    {T δ w : ℝ} (d : PeriodicRuledFrame T) (vin vout : ℝ)
    (hinside : ∀ u ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 u t ∈ Ioo 0 w) :
    ContDiffOn ℝ ∞ (positiveExitSelected_roundFlowRaw d vin vout)
      (positiveExitSelected_roundFlowDomain δ vin vout) := by
  rw [positiveExitSelected_roundFlowRaw_comp]
  exact (positiveExitSelected_flowRaw_contDiffOn d hinside).comp
    (positiveExitSelected_roundFlowParameters_contDiff T vin vout).contDiffOn
    (fun q hq => hq)

/-- The SAME original northern band contains the full actual raw flow image. -/
theorem positiveExitSelected_roundFlowRaw_north
    {T δ w : ℝ} (d : PeriodicRuledFrame T) (vin vout : ℝ)
    (hinside : ∀ u ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 u t ∈ Ioo 0 w)
    (hnorth : ∀ p : AddCircle T × Ioo (0 : ℝ) w, 0 < d.bandGaussMap p 2)
    {q : Coord} (hq : q ∈ positiveExitSelected_roundFlowDomain δ vin vout) :
    0 < d.rawGaussMap (positiveExitSelected_roundFlowRaw d vin vout q) 2 := by
  let s := positiveExitSelected_roundFlowPhase T (q 1)
  let u := principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0
    (positiveExitSelected_roundFlowInitial vin vout (q 0)) s
  have hu : u ∈ Ioo (0 : ℝ) w := hinside _ hq s
  have hh := hnorth (periodProjection T s, ⟨u, hu⟩)
  simpa only [PeriodicRuledFrame.bandGaussMap, PeriodicRuledFrame.fullGaussMap,
    PeriodicRuledFrame.rawGaussMap, periodicLift_coe, positiveExitSelected_roundFlowRaw,
    Matrix.cons_val_zero, Matrix.cons_val_one] using hh

/-- Smoothness of the actual projected raw selected source on the full open
initial-value domain follows from the actual original north condition. -/
theorem positiveExitSelected_roundFlowSource_contDiffOn
    {T δ w : ℝ} (d : PeriodicRuledFrame T) (vin vout : ℝ)
    (hinside : ∀ u ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 u t ∈ Ioo 0 w)
    (hnorth : ∀ p : AddCircle T × Ioo (0 : ℝ) w, 0 < d.bandGaussMap p 2) :
    ContDiffOn ℝ ∞ (positiveExitSelected_roundFlowSource d vin vout)
      (positiveExitSelected_roundFlowDomain δ vin vout) := by
  intro q hq
  have hRaw := ((positiveExitSelected_roundFlowRaw_contDiffOn d vin vout hinside) q hq).contDiffAt
    ((positiveExitSelected_roundFlowDomain_isOpen δ vin vout).mem_nhds hq)
  have hN := (periodicRuledFrame_rawGaussMap_contDiff d).contDiffAt.comp q hRaw
  exact ((gnomonicInverse_contDiffAt
    (positiveExitSelected_roundFlowRaw_north d vin vout hinside hnorth hq).ne').comp q hN).contDiffWithinAt

/-- The two actual orientation reversals give a positive polar-parameter
source Jacobian. The initial values increase from vin to vout with radius. -/
theorem positiveExitSelected_roundFlowSource_jacobian_pos
    {T δ w : ℝ} [Fact (0 < T)] (d : PeriodicRuledFrame T) (vin vout : ℝ)
    (horder : vin < vout)
    (hinside : ∀ u ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 u t ∈ Ioo 0 w)
    (hnorth : ∀ p : AddCircle T × Ioo (0 : ℝ) w, 0 < d.bandGaussMap p 2)
    (horient : ∀ s, ambientCross (d.T s) (d.E s) = d.n s)
    {q : Coord} (hq : q ∈ positiveExitSelected_roundFlowDomain δ vin vout) :
    0 < annularJacobian (positiveExitSelected_roundFlowSource d vin vout) q := by
  let A := positiveExitSelected_roundFlowParameters T vin vout
  let R := positiveExitSelected_flowRaw d
  have hA : DifferentiableAt ℝ A q :=
    (positiveExitSelected_roundFlowParameters_contDiff T vin vout).differentiable (by simp) q
  have hU : IsOpen {p : Coord | p 1 ∈ Ioo (0 : ℝ) δ} :=
    isOpen_Ioo.preimage (continuous_apply 1)
  have hR : DifferentiableAt ℝ R (A q) :=
    (((positiveExitSelected_flowRaw_contDiffOn d hinside) (A q) hq).contDiffAt
      (hU.mem_nhds hq)).differentiableAt (by simp)
  have hRaw : DifferentiableAt ℝ (positiveExitSelected_roundFlowRaw d vin vout) q :=
    (((positiveExitSelected_roundFlowRaw_contDiffOn d vin vout hinside) q hq).contDiffAt
      ((positiveExitSelected_roundFlowDomain_isOpen δ vin vout).mem_nhds hq)).differentiableAt (by simp)
  have hNorth := positiveExitSelected_roundFlowRaw_north d vin vout hinside hnorth hq
  have hP : DifferentiableAt ℝ (gnomonicInverse ∘ d.rawGaussMap)
      (positiveExitSelected_roundFlowRaw d vin vout q) :=
    ((gnomonicInverse_contDiffAt hNorth.ne').differentiableAt (by simp)).comp _
      ((periodicRuledFrame_rawGaussMap_contDiff d).differentiable (by simp) _)
  have hAR : annularJacobian (positiveExitSelected_roundFlowRaw d vin vout) q < 0 := by
    rw [positiveExitSelected_roundFlowRaw_comp, visibleConnectorSourceInverseJacobian_comp hR hA,
      positiveExitSelected_roundFlowParameters_jacobian]
    exact mul_neg_of_pos_of_neg (positiveExitSelected_flowRaw_jacobian_pos d hinside hq)
      (mul_neg_of_neg_of_pos (neg_neg_of_pos (div_pos (Fact.out : 0 < T) Real.two_pi_pos))
        (sub_pos.mpr horder))
  change 0 < annularJacobian ((gnomonicInverse ∘ d.rawGaussMap) ∘
    positiveExitSelected_roundFlowRaw d vin vout) q
  rw [visibleConnectorSourceInverseJacobian_comp hP hRaw]
  exact mul_pos_of_neg_of_neg
    (positiveExit_selectedSourceGeometry_raw_gnomonic_jacobian_neg d _ (horient _) hNorth) hAR

/-- Every radius in the full closed round 1--2 band uses an original
initial value in the SAME complete interval. -/
theorem positiveExitSelected_roundFlowDomain_contains_closed_band
    {δ : ℝ} (vin vout : Ioo (0 : ℝ) δ) (horder : (vin : ℝ) < (vout : ℝ)) :
    {q : Coord | 1 ≤ q 0 ∧ q 0 ≤ 2} ⊆
      positiveExitSelected_roundFlowDomain δ vin vout := by
  intro q hq
  have hdiff : 0 ≤ (vout : ℝ) - (vin : ℝ) := sub_nonneg.mpr horder.le
  have hlo := mul_nonneg (sub_nonneg.mpr hq.1) hdiff
  have hhi := mul_nonneg (sub_nonneg.mpr hq.2) hdiff
  change 0 < (vin : ℝ) + (q 0 - 1) * ((vout : ℝ) - (vin : ℝ)) ∧
    (vin : ℝ) + (q 0 - 1) * ((vout : ℝ) - (vin : ℝ)) < δ
  constructor <;> nlinarith [vin.property.1, vout.property.2]

/-- The literal raw selected source is angularly periodic on the entire
polar cylinder. Its original balance proves flow periodicity; no new source
or phase witness is selected. -/
theorem positiveExitSelected_roundFlowSource_periodic
    {T : ℝ} (d : PeriodicRuledFrame T)
    (hb : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0)
    (vin vout r theta : ℝ) :
    positiveExitSelected_roundFlowSource d vin vout (![r, theta + 2 * Real.pi] : Coord) =
      positiveExitSelected_roundFlowSource d vin vout (![r, theta] : Coord) := by
  have hphase : positiveExitSelected_roundFlowPhase T (theta + 2 * Real.pi) =
      positiveExitSelected_roundFlowPhase T theta + T := by
    dsimp [positiveExitSelected_roundFlowPhase]
    field_simp [Real.pi_ne_zero]
    <;> ring
  have hflow := principalTrajectory_periodic (ruledRho_periodic d.period_τ)
    (periodicRuledFrame_omega_periodic d hb) 0 (positiveExitSelected_roundFlowInitial vin vout r)
    (positiveExitSelected_roundFlowPhase T theta)
  simp only [positiveExitSelected_roundFlowSource, Function.comp_apply,
    positiveExitSelected_roundFlowRaw, Matrix.cons_val_zero, Matrix.cons_val_one, hphase, hflow]
  congr 1
  simp only [PeriodicRuledFrame.rawGaussMap, Matrix.cons_val_zero, Matrix.cons_val_one,
    d.period_T (positiveExitSelected_roundFlowPhase T theta),
    d.period_n (positiveExitSelected_roundFlowPhase T theta),
    d.period_k (positiveExitSelected_roundFlowPhase T theta),
    d.period_τ (positiveExitSelected_roundFlowPhase T theta)]

end
end TightVer401


