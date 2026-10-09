import TightVer401.PositiveExitConstructionSelectedSourceGeometryRoundCartesian
import TightVer401.PositiveExitConstructionWindingBridge
import TightVer401.PositiveExitConstructionLeaf
import TightVer401.VisibleConnectorSourceOrderRound

/-! Actual positive Jordan boundary of each SAME original selected raw leaf.
The normalized clock is the original positive period T; fillings and origin
enclosures are produced from the retained actual turn. No nesting, filling,
or source orientation is an input. -/
namespace TightVer401
noncomputable section
open Set Function Filter MeasureTheory OAI.SmoothLocal.Geometry
open OAI.CircleDomainRigidity
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

private theorem selectedRawBoundary_complex_inverse (p : Coord) :
    seamComplexCoord (angularDescentComplex p) = p := by
  ext i
  fin_cases i <;> simp [seamComplexCoord_apply, angularDescentComplex]

variable {T δ w : ℝ} [Fact (0 < T)] (d : PeriodicRuledFrame T)
  (hb : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0)
  (hinside : ∀ u ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
    principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 u t ∈ Ioo 0 w)
  (v : Ioo (0 : ℝ) δ)

/-- The literal original raw selected source boundary, normalized once by T. -/
def positiveExitSelected_rawBoundary (t : ℝ) : ℂ :=
  angularDescentComplex (gnomonicInverse (positiveExitRawLeaf d hb hinside v (T * t)))

/-- Actual sphere reconstruction of the SAME normalized raw boundary. -/
theorem positiveExitSelected_rawBoundary_gauss_reconstruction
    (hnorth : ∀ p : AddCircle T × Ioo (0 : ℝ) w, 0 < d.bandGaussMap p 2) (t : ℝ) :
    planarUnitNormal (seamComplexCoord (positiveExitSelected_rawBoundary d hb hinside v t)) =
      positiveExitRawLeaf d hb hinside v (T * t) := by
  rw [positiveExitSelected_rawBoundary, selectedRawBoundary_complex_inverse]
  exact congrArg (fun p : RoundSphere => p.val)
    (gnomonic_right_inverse (positiveExitGaussLeaf_north d hb hinside v hnorth (periodProjection T (T * t))))

theorem positiveExitSelected_rawBoundary_contDiff
    (hnorth : ∀ p : AddCircle T × Ioo (0 : ℝ) w, 0 < d.bandGaussMap p 2) :
    ContDiff ℝ ∞ (positiveExitSelected_rawBoundary d hb hinside v) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  have hζ : ContDiff ℝ ∞ (fun s => positiveExitRawLeaf d hb hinside v (T * s)) :=
    (positiveExitRawLeaf_contDiff d hb hinside v).comp (contDiff_const.mul contDiff_id)
  change ContDiffAt ℝ ∞ (angularDescentComplex ∘ gnomonicInverse ∘
    (fun s => positiveExitRawLeaf d hb hinside v (T * s))) t
  exact angularDescentComplex_contDiff.contDiffAt.comp t
    ((gnomonicInverse_contDiffAt
      (positiveExitGaussLeaf_north d hb hinside v hnorth (periodProjection T (T * t))).ne').comp t hζ.contDiffAt)

theorem positiveExitSelected_rawBoundary_periodic :
    Periodic (positiveExitSelected_rawBoundary d hb hinside v) 1 := by
  intro t
  have ht : T * (t + 1) = T * t + T := by ring
  simp only [positiveExitSelected_rawBoundary, ht, positiveExitRawLeaf_periodic d hb hinside v (T * t)]

/-- Gauss injectivity and actual northern inversion prove boundary
injectivity on one original traversal; no Jordan package is supplied. -/
theorem positiveExitSelected_rawBoundary_injOn
    (hNi : Injective (d.bandGaussMap (b := w)))
    (hnorth : ∀ p : AddCircle T × Ioo (0 : ℝ) w, 0 < d.bandGaussMap p 2) :
    InjOn (positiveExitSelected_rawBoundary d hb hinside v) (Ico 0 1) := by
  intro s hs t ht he
  have hscaled : positiveExitRawLeaf d hb hinside v (T * s) =
      positiveExitRawLeaf d hb hinside v (T * t) := by
    rw [← positiveExitSelected_rawBoundary_gauss_reconstruction d hb hinside v hnorth s,
      ← positiveExitSelected_rawBoundary_gauss_reconstruction d hb hinside v hnorth t, he]
  have hT : 0 < T := Fact.out
  have hsT : T * s ∈ Ico (0 : ℝ) T :=
    ⟨mul_nonneg hT.le hs.1, by simpa using mul_lt_mul_of_pos_left hs.2 hT⟩
  have htT : T * t ∈ Ico (0 : ℝ) T :=
    ⟨mul_nonneg hT.le ht.1, by simpa using mul_lt_mul_of_pos_left ht.2 hT⟩
  exact mul_left_cancel₀ hT.ne'
    (positiveExitRawLeaf_injOn d hb hinside v hNi hsT htT hscaled)

/-- Actual spherical reconstruction transfers raw-leaf regularity to its
Cartesian boundary, without assuming a projected regularity conclusion. -/
theorem positiveExitSelected_rawBoundary_deriv_ne_zero
    (hnorth : ∀ p : AddCircle T × Ioo (0 : ℝ) w, 0 < d.bandGaussMap p 2) (t : ℝ) :
    deriv (positiveExitSelected_rawBoundary d hb hinside v) t ≠ 0 := by
  let f : ℂ → Ambient := planarUnitNormal ∘ seamComplexCoord
  have hf : ContDiff ℝ ∞ f := gnomonicNormal_contDiff.comp seamComplexCoord.contDiff
  have hγ := positiveExitSelected_rawBoundary_contDiff d hb hinside v hnorth
  have hζ := ((positiveExitRawLeaf_contDiff d hb hinside v).differentiable (by simp) (T * t)).hasDerivAt.scomp t
    ((hasDerivAt_id t).const_mul T)
  have heq : f ∘ positiveExitSelected_rawBoundary d hb hinside v =
      (fun s => positiveExitRawLeaf d hb hinside v (T * s)) := by
    funext s
    exact positiveExitSelected_rawBoundary_gauss_reconstruction d hb hinside v hnorth s
  intro hz
  have hd := (hf.differentiable (by simp) (positiveExitSelected_rawBoundary d hb hinside v t)).hasFDerivAt.comp_hasDerivAt
    t ((hγ.differentiable (by simp) t).hasDerivAt)
  rw [hz, map_zero] at hd
  change HasDerivAt (f ∘ positiveExitSelected_rawBoundary d hb hinside v) 0 t at hd
  rw [heq] at hd
  have hzero : T • deriv (positiveExitRawLeaf d hb hinside v) (T * t) = 0 := by
    simpa only [mul_one] using (hd.unique hζ).symm
  exact positiveExitRawLeaf_deriv_ne_zero d hb hinside v (T * t)
    ((smul_eq_zero.mp hzero).resolve_left (Fact.out : 0 < T).ne')

/-- The retained raw source margin produces an actual positive filling,
positive Jordan parametrization and origin enclosure for this SAME leaf. -/
theorem positiveExitSelected_rawBoundary_exists_positive_jordan
    (hNi : Injective (d.bandGaussMap (b := w)))
    (hnorth : ∀ p : AddCircle T × Ioo (0 : ℝ) w, 0 < d.bandGaussMap p 2)
    (hne : ∀ s, angularDescentComplex (gnomonicInverse (positiveExitRawLeaf d hb hinside v s)) ≠ 0)
    (hturn : HasPositiveArgumentTurn
      (angularDescentComplex ∘ gnomonicInverse ∘ positiveExitRawLeaf d hb hinside v) T) :
    ∃ H : ℂ ≃ₜ ℂ,
      PositiveJordanParametrization H (positiveExitSelected_rawBoundary d hb hinside v) ∧
      DualRadialCompletionPositiveTrace H (positiveExitSelected_rawBoundary d hb hinside v) ∧
      (0 : ℂ) ∈ jordanInterior H := by
  have hturn1 : HasPositiveArgumentTurn (positiveExitSelected_rawBoundary d hb hinside v) 1 := by
    obtain ⟨φ, hφ, hproj, hinc⟩ := hturn
    refine ⟨fun t => φ (T * t), hφ.comp (continuous_const.mul continuous_id),
      fun t => hproj (T * t), ?_⟩
    simpa only [mul_one, mul_zero] using hinc
  obtain ⟨H, htrace, h0⟩ := positiveExit_positive_turn_exists_completion_trace
    (positiveExitSelected_rawBoundary_contDiff d hb hinside v hnorth)
    (positiveExitSelected_rawBoundary_periodic d hb hinside v)
    (positiveExitSelected_rawBoundary_injOn d hb hinside v hNi hnorth)
    (positiveExitSelected_rawBoundary_deriv_ne_zero d hb hinside v hnorth)
    (fun t => hne (T * t)) hturn1
  refine ⟨H, ?_, htrace, h0⟩
  rcases htrace with ⟨hs, hp, hi, hr, hbnd, hw⟩
  exact ⟨hs, hp, hi, hr, hbnd, hw⟩

/-- The SAME two original selected boundaries cannot meet: the actual Gauss
inverse and the checked explicit complete-flow inverse recover the original
initial value. Boundary separation is produced, not assumed. -/
theorem positiveExitSelected_rawBoundary_ranges_disjoint
    (vin vout : Ioo (0 : ℝ) δ) (horder : (vin : ℝ) < (vout : ℝ))
    (hNi : Injective (d.bandGaussMap (b := w)))
    (hnorth : ∀ p : AddCircle T × Ioo (0 : ℝ) w, 0 < d.bandGaussMap p 2) :
    Disjoint (range (positiveExitSelected_rawBoundary d hb hinside vin))
      (range (positiveExitSelected_rawBoundary d hb hinside vout)) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨s, hs⟩ ⟨t, ht⟩
  have hγ : positiveExitSelected_rawBoundary d hb hinside vin s =
      positiveExitSelected_rawBoundary d hb hinside vout t := hs.trans ht.symm
  have hraw : positiveExitRawLeaf d hb hinside vin (T * s) =
      positiveExitRawLeaf d hb hinside vout (T * t) := by
    rw [← positiveExitSelected_rawBoundary_gauss_reconstruction d hb hinside vin hnorth s,
      ← positiveExitSelected_rawBoundary_gauss_reconstruction d hb hinside vout hnorth t, hγ]
  change d.bandGaussMap (positiveExitLeaf d hb hinside vin (periodProjection T (T * s))) =
    d.bandGaussMap (positiveExitLeaf d hb hinside vout (periodProjection T (T * t))) at hraw
  have hleaf := hNi hraw
  have hcoord := congrArg
    (fun p : AddCircle T × Ioo (0 : ℝ) w => (p.1, (p.2 : ℝ))) hleaf
  change identityFlowCoordinates d hb 0 (periodProjection T (T * s), vin) =
    identityFlowCoordinates d hb 0 (periodProjection T (T * t), vout) at hcoord
  have hinj := identityFlowCoordinates_injective d hb 0
    (fun u hu r => positiveExit_trajectory_denominator_ne_zero d hinside hu r)
  have hsame := congrArg (fun p : AddCircle T × Ioo (0 : ℝ) δ => (p.2 : ℝ)) (hinj hcoord)
  exact horder.ne hsame

end
end TightVer401

