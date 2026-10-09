import TightVer401.NativeProductPlaneMetricBundleTransport
import Mathlib.Geometry.Manifold.Riemannian.Basic

/-! Actual incoming curve differentials and induced Riemannian lengths.
Smoothness is transported only for orders n ≤ ∞; analytic smoothness is not
asserted. Incoming mfderiv transport holds for all maps by its standard zero
default outside differentiability. All norms below come from the constructed
induced metric bundles, never from the coordinate product's max norm.
-/
open Manifold Bundle MeasureTheory
open scoped Manifold ContDiff Topology Bundle ENNReal
namespace TightVer401
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set OAI.ClosedSurfaceR4

section Curves
variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ModelProd ℝ ℝ) M]
  [IsManifold nativeProductModel ∞ M]

local instance intrinsicCurvesPlaneChartedSpace : ChartedSpace Plane M :=
  nativeProductPlaneChartedSpace M
local instance intrinsicCurvesPlaneIsManifold : IsManifold planeModel ∞ M :=
  nativeProductPlane_isManifold M

section Incoming
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {K : ModelWithCorners ℝ E H}
  {D : Type*} [TopologicalSpace D] [ChartedSpace H D]

/-- Incoming smoothness is unchanged at every differentiability order up to smooth. -/
theorem nativeProductPlane_incoming_contMDiff_iff {n : ℕ∞ω} (hn : n ≤ (∞ : ℕ∞ω)) (c : D → M) :
    ContMDiff K planeModel n c ↔ ContMDiff K nativeProductModel n c := by
  constructor
  · intro hc
    exact ((nativeProductPlane_inverse_contMDiff M).of_le hn).comp hc
  · intro hc
    exact ((nativeProductPlane_identity_contMDiff M).of_le hn).comp hc

theorem nativeProductPlane_incoming_contMDiffOn_iff {n : ℕ∞ω} (hn : n ≤ (∞ : ℕ∞ω))
    (c : D → M) (s : Set D) :
    ContMDiffOn K planeModel n c s ↔ ContMDiffOn K nativeProductModel n c s := by
  constructor
  · intro hc
    exact ((nativeProductPlane_inverse_contMDiff M).of_le hn).comp_contMDiffOn hc
  · intro hc
    exact ((nativeProductPlane_identity_contMDiff M).of_le hn).comp_contMDiffOn hc

theorem nativeProductPlane_incoming_contMDiffWithinAt_iff {n : ℕ∞ω} (hn : n ≤ (∞ : ℕ∞ω))
    (c : D → M) (s : Set D) (x : D) :
    ContMDiffWithinAt K planeModel n c s x ↔
      ContMDiffWithinAt K nativeProductModel n c s x := by
  constructor
  · intro hc
    exact (((nativeProductPlane_inverse_contMDiff M).of_le hn) (c x)).comp_contMDiffWithinAt x hc
  · intro hc
    exact (((nativeProductPlane_identity_contMDiff M).of_le hn) (c x)).comp_contMDiffWithinAt x hc

/-- Incoming differentiability is unchanged by the actual smooth atlas identities. -/
theorem nativeProductPlane_incoming_mdifferentiableAt_iff (c : D → M) (x : D) :
    MDifferentiableAt K planeModel c x ↔ MDifferentiableAt K nativeProductModel c x := by
  constructor
  · intro hc
    exact (nativeProductPlane_inverse_hasMFDerivAt M (c x)).mdifferentiableAt.comp x hc
  · intro hc
    exact (nativeProductPlane_identity_hasMFDerivAt M (c x)).mdifferentiableAt.comp x hc

/-- Actual incoming derivative transport, including the standard nondifferentiable zero case. -/
theorem nativeProductPlane_incoming_mfderiv (c : D → M) (x : D) :
    mfderiv K planeModel c x = nativeProductPlaneEquiv.toContinuousLinearMap.comp
      (mfderiv K nativeProductModel c x) := by
  by_cases hc : MDifferentiableAt K nativeProductModel c x
  · have h := mfderiv_comp x
      (nativeProductPlane_identity_hasMFDerivAt M (c x)).mdifferentiableAt hc
    rw [(nativeProductPlane_identity_hasMFDerivAt M (c x)).mfderiv] at h
    exact h
  · have hp : ¬ MDifferentiableAt K planeModel c x := fun h =>
      hc ((nativeProductPlane_incoming_mdifferentiableAt_iff c x).mp h)
    rw [mfderiv_zero_of_not_mdifferentiableAt hp, mfderiv_zero_of_not_mdifferentiableAt hc]
    simp

end Incoming

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Opt-in native Riemannian bundle built from the actual smooth immersion metric. -/
@[instance_reducible]
def nativeProductImmersionRiemannianBundle (F : M → V)
    (hF : ContMDiff nativeProductModel 𝓘(ℝ, V) ∞ F)
    (hinj : ∀ p, Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, V) F p)) :
    RiemannianBundle (fun p : M => TangentSpace nativeProductModel p) :=
  ⟨(nativeProductImmersionMetric F hF hinj).toRiemannianMetric⟩

/-- Opt-in Plane Riemannian bundle of the same immersion. -/
@[instance_reducible]
def nativeProductPlaneImmersionRiemannianBundle (F : M → V)
    (hF : ContMDiff nativeProductModel 𝓘(ℝ, V) ∞ F)
    (hinj : ∀ p, Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, V) F p)) :
    RiemannianBundle (fun p : M => TangentSpace planeModel p) :=
  ⟨(nativeProductPlaneImmersionMetric F hF hinj).toRiemannianMetric⟩

/-- Explicit metric-derived native tangent ENorm, with no global norm instance. -/
@[instance_reducible]
def nativeProductImmersionENorm (F : M → V)
    (hF : ContMDiff nativeProductModel 𝓘(ℝ, V) ∞ F)
    (hinj : ∀ p, Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, V) F p))
    (p : M) : ENorm (TangentSpace nativeProductModel p) := by
  letI := nativeProductImmersionRiemannianBundle F hF hinj
  infer_instance

@[instance_reducible]
def nativeProductPlaneImmersionENorm (F : M → V)
    (hF : ContMDiff nativeProductModel 𝓘(ℝ, V) ∞ F)
    (hinj : ∀ p, Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, V) F p))
    (p : M) : ENorm (TangentSpace planeModel p) := by
  letI := nativeProductPlaneImmersionRiemannianBundle F hF hinj
  infer_instance

/-- Genuine metric ENorms agree on transported tangent vectors. -/
theorem nativeProductPlaneImmersion_enorm_transport (F : M → V)
    (hF : ContMDiff nativeProductModel 𝓘(ℝ, V) ∞ F)
    (hinj : ∀ p, Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, V) F p))
    (p : M) (v : TangentSpace nativeProductModel p) :
    @enorm (TangentSpace planeModel p) (nativeProductPlaneImmersionENorm F hF hinj p)
      (nativeProductPlaneEquiv v) =
    @enorm (TangentSpace nativeProductModel p) (nativeProductImmersionENorm F hF hinj p) v := by
  letI := nativeProductImmersionRiemannianBundle F hF hinj
  letI := nativeProductPlaneImmersionRiemannianBundle F hF hinj
  change ‖(show TangentSpace planeModel p from nativeProductPlaneEquiv v)‖ₑ = ‖v‖ₑ
  have hinner :
      @inner ℝ (TangentSpace planeModel p) _ (nativeProductPlaneEquiv v) (nativeProductPlaneEquiv v) =
      @inner ℝ (TangentSpace nativeProductModel p) _ v v :=
    nativeProductPlaneImmersionMetric_transport F hF hinj p v v
  have hn : ‖(show TangentSpace planeModel p from nativeProductPlaneEquiv v)‖ = ‖v‖ := by
    rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner, hinner]
  exact enorm_eq_iff_norm_eq.mpr hn

section Speed
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {K : ModelWithCorners ℝ E H}
  {D : Type*} [TopologicalSpace D] [ChartedSpace H D]

/-- Actual differential speed equality for any incoming map and source tangent vector. -/
theorem nativeProductPlaneImmersion_speed_transport (F : M → V)
    (hF : ContMDiff nativeProductModel 𝓘(ℝ, V) ∞ F)
    (hinj : ∀ p, Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, V) F p))
    (c : D → M) (x : D) (v : TangentSpace K x) :
    @enorm (TangentSpace planeModel (c x)) (nativeProductPlaneImmersionENorm F hF hinj (c x))
      (mfderiv K planeModel c x v) =
    @enorm (TangentSpace nativeProductModel (c x)) (nativeProductImmersionENorm F hF hinj (c x))
      (mfderiv K nativeProductModel c x v) := by
  rw [nativeProductPlane_incoming_mfderiv c x]
  change @enorm (TangentSpace planeModel (c x))
      (nativeProductPlaneImmersionENorm F hF hinj (c x))
      (nativeProductPlaneEquiv (mfderiv K nativeProductModel c x v)) = _
  exact nativeProductPlaneImmersion_enorm_transport F hF hinj (c x)
    (mfderiv K nativeProductModel c x v)

end Speed

/-- Actual native induced-metric length of a real curve. -/
def nativeProductImmersionPathELength (F : M → V)
    (hF : ContMDiff nativeProductModel 𝓘(ℝ, V) ∞ F)
    (hinj : ∀ p, Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, V) F p))
    (c : ℝ → M) (a b : ℝ) : ℝ≥0∞ :=
  letI := nativeProductImmersionRiemannianBundle F hF hinj
  pathELength nativeProductModel c a b

def nativeProductPlaneImmersionPathELength (F : M → V)
    (hF : ContMDiff nativeProductModel 𝓘(ℝ, V) ∞ F)
    (hinj : ∀ p, Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, V) F p))
    (c : ℝ → M) (a b : ℝ) : ℝ≥0∞ :=
  letI := nativeProductPlaneImmersionRiemannianBundle F hF hinj
  pathELength planeModel c a b

/-- Length equality holds for all real curves; differentiability is needed only for admissibility. -/
theorem nativeProductPlaneImmersion_pathELength_transport (F : M → V)
    (hF : ContMDiff nativeProductModel 𝓘(ℝ, V) ∞ F)
    (hinj : ∀ p, Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, V) F p))
    (c : ℝ → M) (a b : ℝ) :
    nativeProductImmersionPathELength F hF hinj c a b =
      nativeProductPlaneImmersionPathELength F hF hinj c a b := by
  letI := nativeProductImmersionRiemannianBundle F hF hinj
  letI := nativeProductPlaneImmersionRiemannianBundle F hF hinj
  change pathELength nativeProductModel c a b = pathELength planeModel c a b
  rw [pathELength_eq_lintegral_mfderiv_Icc, pathELength_eq_lintegral_mfderiv_Icc]
  apply setLIntegral_congr_fun measurableSet_Icc
  intro t _
  exact (nativeProductPlaneImmersion_speed_transport (K := 𝓘(ℝ, ℝ)) F hF hinj c t 1).symm

attribute [local instance] Measure.Subtype.measureSpace

/-- Unit-interval integral equality directly matches the actual riemannianEDist infimum.
The source tangent vector 1 is the chart-aware oneTangentSpaceIcc from the pinned API. -/
theorem nativeProductPlaneImmersion_pathIntegral_transport (F : M → V)
    (hF : ContMDiff nativeProductModel 𝓘(ℝ, V) ∞ F)
    (hinj : ∀ p, Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, V) F p))
    (γ : unitInterval → M) :
    (letI := nativeProductImmersionRiemannianBundle F hF hinj
      ∫⁻ t : unitInterval, ‖mfderiv (𝓡∂ 1) nativeProductModel γ t 1‖ₑ) =
    (letI := nativeProductPlaneImmersionRiemannianBundle F hF hinj
      ∫⁻ t : unitInterval, ‖mfderiv (𝓡∂ 1) planeModel γ t 1‖ₑ) := by
  letI := nativeProductImmersionRiemannianBundle F hF hinj
  letI := nativeProductPlaneImmersionRiemannianBundle F hF hinj
  apply lintegral_congr
  intro t
  exact (nativeProductPlaneImmersion_speed_transport (K := 𝓡∂ 1) F hF hinj γ t 1).symm

end Curves
end
end TightVer401
