import TightVer401.IdentityBandCentralSupportInterior

/-! Physical arclength derivatives and interior pairings for the same actual
corrected speed and frame. The inverse derivative is proved from the actual
primitive identity, rather than supplied as an independent premise. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff Topology Matrix RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false

/-- Any actual homeomorphism equal to the positive-speed primitive has the
derived inverse arclength derivative. No periodicity or inverse derivative
hypothesis is needed. -/
theorem identityBand_arclengthInverse_hasDerivAt {a : ℝ → ℝ}
    (ha : Continuous a) (hpos : ∀ r, 0 < a r)
    (S : ℝ ≃ₜ ℝ) (hS : (S : ℝ → ℝ) = rawPrimitive a) (s : ℝ) :
    HasDerivAt S.symm (a (S.symm s))⁻¹ s := by
  exact (rawPrimitive_hasDerivAt ha (S.symm s)).of_local_left_inverse
    S.symm.continuous.continuousAt (ne_of_gt (hpos (S.symm s)))
    (Filter.Eventually.of_forall (fun y => by rw [← hS]; exact S.apply_symm_apply y))

/-- The corrected frame's actual lambda and D coefficients, with all speed,
curvature and inverse derivatives obtained from the given smooth functions. -/
theorem identityBand_corrected_frame_coefficients {L : ℝ}
    (d : PeriodicRuledFrame L) {a κ : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hκ : ContDiff ℝ ∞ κ) (hpos : ∀ r, 0 < a r)
    (S : ℝ ≃ₜ ℝ) (hS : (S : ℝ → ℝ) = rawPrimitive a)
    (hk : d.k = normalLoopPhysicalK a κ S.symm)
    (hτ : d.τ = normalLoopPhysicalTau a S.symm) (s : ℝ) :
    ruledLambda d.τ s = -deriv a (S.symm s) / (a (S.symm s))^2 ∧
      ruledD d.k d.τ s = deriv κ (S.symm s) / (a (S.symm s))^2 := by
  have hψ := identityBand_arclengthInverse_hasDerivAt ha.continuous hpos S hS s
  have hda := (ha.differentiable (by simp) (S.symm s)).hasDerivAt
  have hdκ := (hκ.differentiable (by simp) (S.symm s)).hasDerivAt
  constructor
  · rw [hτ]
    exact identityBand_physical_lambda hda (hpos (S.symm s)) hψ
  · rw [hk, hτ]
    exact normalLoop_physical_D hda hdκ (hpos (S.symm s)) hψ

/-- The actual interior tangential entry for a positive smooth corrected
speed and its actual primitive inverse. All derivative premises are derived. -/
theorem identityBand_corrected_frame_tangential_pairing {L : ℝ}
    (d : PeriodicRuledFrame L) {a κ : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hκ : ContDiff ℝ ∞ κ) (hpos : ∀ r, 0 < a r)
    (S : ℝ ≃ₜ ℝ) (hS : (S : ℝ → ℝ) = rawPrimitive a)
    (hk : d.k = normalLoopPhysicalK a κ S.symm)
    (hτ : d.τ = normalLoopPhysicalTau a S.symm) (s u : ℝ) :
    inner ℝ
      (fderiv ℝ (ruledMap d.γ d.E) (![s, u] : Coord) (Pi.single 0 1 : Coord))
      (fderiv ℝ d.rawGaussMap (![s, u] : Coord) (Pi.single 0 1 : Coord)) =
      u * (-deriv a (S.symm s) + u * deriv κ (S.symm s)) /
        ((a (S.symm s))^3 * Real.sqrt (ruledEnergy (d.k s) (d.τ s) u)) := by
  exact identityBand_interior_tangential_pairing_physical d hk hτ
    (ha.differentiable (by simp) (S.symm s)).hasDerivAt
    (hκ.differentiable (by simp) (S.symm s)).hasDerivAt
    (hpos (S.symm s))
    (identityBand_arclengthInverse_hasDerivAt ha.continuous hpos S hS s)

/-- Specialization to the actual spherical normal-loop curvature; its
smoothness follows from the supplied smooth normal loop. -/
theorem identityBand_normalLoop_frame_tangential_pairing {L : ℝ}
    (d : PeriodicRuledFrame L) {ζ : ℝ → Ambient} {a : ℝ → ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (ha : ContDiff ℝ ∞ a) (hpos : ∀ r, 0 < a r)
    (S : ℝ ≃ₜ ℝ) (hS : (S : ℝ → ℝ) = rawPrimitive a)
    (hk : d.k = normalLoopPhysicalK a (normalLoopCurvature ζ) S.symm)
    (hτ : d.τ = normalLoopPhysicalTau a S.symm) (s u : ℝ) :
    inner ℝ
      (fderiv ℝ (ruledMap d.γ d.E) (![s, u] : Coord) (Pi.single 0 1 : Coord))
      (fderiv ℝ d.rawGaussMap (![s, u] : Coord) (Pi.single 0 1 : Coord)) =
      u * (-deriv a (S.symm s) + u * deriv (normalLoopCurvature ζ) (S.symm s)) /
        ((a (S.symm s))^3 * Real.sqrt (ruledEnergy (d.k s) (d.τ s) u)) := by
  exact identityBand_corrected_frame_tangential_pairing d ha
    (normalLoop_actual_smooth hζ).2 hpos S hS hk hτ s u

end
end TightVer401
