import TightVer401.CorrugatedSeedEnclosure
import TightVer401.CorrugatedSeedVisiblePairs
import TightVer401.CorrugatedSeedSphereNative
import TightVer401.CorrugatedSeedSphereCurvature

/-! The exact analytic seed package of manuscript lemma `lem:seed`.
Positive orientation is expressed by an actual continuous argument lift of
increment +2π about the origin, which is separately proved to lie inside
both actual Jordan curves. No orientation or filling hypothesis is assumed. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Manifold Topology
local instance analyticSeedPositivePeriod : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
local instance analyticSeedChart : ChartedSpace ℝ (AddCircle (2 * Real.pi)) :=
  periodCircleChartedSpace _
local instance analyticSeedSphereDimension : Fact (Module.finrank ℝ Ambient = 2 + 1) :=
  ⟨by simp [Ambient]⟩

structure CorrugatedAnalyticSeed (N : ℕ) (hN : 10000 ≤ N) : Prop where
  beta_analytic : ContDiff ℝ ω (corrugatedSeedBeta (N : ℝ))
  partner_analytic : ContDiff ℝ ω (corrugatedSeedPartner (N : ℝ))
  beta_regular : ∀ t, deriv (corrugatedSeedBeta (N : ℝ)) t ≠ 0
  partner_regular : ∀ t, deriv (corrugatedSeedPartner (N : ℝ)) t ≠ 0
  beta_embedding : Topology.IsEmbedding (corrugatedSeedBeta_periodic (show 2 ≤ N by omega)).lift
  partner_embedding : Topology.IsEmbedding
    (corrugatedSeedPartner_periodic (show 2 ≤ N by omega)).lift
  beta_jordan : Schoenflies.IsJordanCurve
    (range (jordanComplexCoordinates.symm ∘ corrugatedSeedBeta (N : ℝ)))
  partner_jordan : Schoenflies.IsJordanCurve
    (range (jordanComplexCoordinates.symm ∘ corrugatedSeedPartner (N : ℝ)))
  beta_origin_inside : (0 : Schoenflies.Plane) ∈ Schoenflies.inside
    (range (jordanComplexCoordinates.symm ∘ corrugatedSeedBeta (N : ℝ)))
  partner_origin_inside : (0 : Schoenflies.Plane) ∈ Schoenflies.inside
    (range (jordanComplexCoordinates.symm ∘ corrugatedSeedPartner (N : ℝ)))
  beta_positive_turn : HasPositiveArgumentTurn (corrugatedSeedBeta (N : ℝ)) (2 * Real.pi)
  partner_positive_turn : HasPositiveArgumentTurn (corrugatedSeedPartner (N : ℝ)) (2 * Real.pi)
  beta_covariance : ∀ t, corrugatedSeedBeta (N : ℝ) (t + corrugatedSeedCell (N : ℝ)) =
    corrugatedSeedRotation (N : ℝ) * corrugatedSeedBeta (N : ℝ) t
  partner_covariance : ∀ t,
    corrugatedSeedPartner (N : ℝ) (t + corrugatedSeedCell (N : ℝ)) =
    corrugatedSeedRotation (N : ℝ) * corrugatedSeedPartner (N : ℝ) t
  partner_derivative : ∀ t, deriv (corrugatedSeedPartner (N : ℝ)) t =
    corrugatedSeedMultiplier (corrugatedSeedRoot (N : ℝ)) (N : ℝ) t •
      deriv (corrugatedSeedBeta (N : ℝ)) t
  multiplier_positive : ∀ t,
    0 < corrugatedSeedMultiplier (corrugatedSeedRoot (N : ℝ)) (N : ℝ) t
  zero_action : (∫ t in (0 : ℝ)..2 * Real.pi, corrugatedSeedPlaneDet
    (corrugatedSeedBeta (N : ℝ) t) (deriv (corrugatedSeedPartner (N : ℝ)) t)) = 0
  outer_visible : ComplexVisiblePair (1 / 4)
    (corrugatedSeedBeta (N : ℝ)) (corrugatedSeedPartner (N : ℝ))
  reflected_visible : ComplexVisiblePair (4 / 5)
    (corrugatedReverseReflect (corrugatedSeedPartner (N : ℝ)))
    (corrugatedReverseReflect (corrugatedSeedBeta (N : ℝ)))
  sphere_embedding : Topology.IsEmbedding
    (corrugatedSeedSpherePoint_periodic (show 2 ≤ N by omega)).lift
  sphere_north : ∀ t, 0 < corrugatedSeedSphere (N : ℝ) t 2
  sphere_curvature_positive :
    0 < sphericalCurveGeodesicCurvature (corrugatedSeedSphere (N : ℝ)) 0
  sphere_curvature_negative :
    sphericalCurveGeodesicCurvature (corrugatedSeedSphere (N : ℝ)) (Real.pi / N) < 0

theorem corrugated_analytic_seed {N : ℕ} (hN : 10000 ≤ N) :
    CorrugatedAnalyticSeed N hN := by
  have hN2 : 2 ≤ N := by omega
  have hNr : (10000 : ℝ) ≤ N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) < N := by linarith
  have hb : ∀ t, deriv (corrugatedSeedBeta (N : ℝ)) t ≠ 0 := by
    intro t
    rw [corrugatedSeedBeta_deriv (ne_of_gt (by linarith : (0 : ℝ) < N))]
    exact corrugatedSeedBetaVelocity_ne_zero hN1 t
  have hd : ∀ t, deriv (corrugatedSeedPartner (N : ℝ)) t ≠ 0 := by
    intro t
    rw [corrugatedSeedPartner_deriv hN1]
    exact smul_ne_zero (ne_of_gt (corrugatedSeedMultiplier_pos _ _ t)) (hb t)
  have hi := corrugatedSeed_origin_inside hN
  have ht := corrugatedSeed_positive_argument_turns hN
  exact {
    beta_analytic := corrugatedSeedBeta_contDiff_analytic _
    partner_analytic := corrugatedSeedPartner_contDiff_analytic _
    beta_regular := hb
    partner_regular := hd
    beta_embedding := (corrugatedSeedBeta_native_embedding hN2).2
    partner_embedding := (corrugatedSeedPartner_native_embedding hN).2
    beta_jordan := corrugatedSeedBeta_isJordanCurve hN2
    partner_jordan := corrugatedSeedPartner_isJordanCurve hN
    beta_origin_inside := hi.1
    partner_origin_inside := hi.2
    beta_positive_turn := ht.1
    partner_positive_turn := ht.2
    beta_covariance := corrugatedSeedBeta_cell (ne_of_gt (by linarith : (0 : ℝ) < N))
    partner_covariance := corrugatedSeedPartner_cell hN1
    partner_derivative := corrugatedSeedPartner_deriv hN1
    multiplier_positive := corrugatedSeedMultiplier_pos _ _
    zero_action := corrugatedSeedPartner_action hN2
    outer_visible := corrugatedSeed_outer_visible hNr
    reflected_visible := corrugatedSeed_reflected_visible hNr
    sphere_embedding := (corrugatedSeedSphere_native_embedding hN2).2
    sphere_north := corrugatedSeedSphere_north _
    sphere_curvature_positive := corrugatedSeedSphere_curvature_positive hN1
    sphere_curvature_negative := corrugatedSeedSphere_curvature_negative hN1 }
end
end TightVer401
