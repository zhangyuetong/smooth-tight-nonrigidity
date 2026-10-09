import TightVer401.NativeProductPlaneForms
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Actual smooth induced metric bundles for native product-model immersions.
The metric is constructed from the actual manifold derivative. Its unit ball
is bounded by finite-dimensional injectivity, and smoothness is proved in the
bilinear hom bundle. Neither an intrinsic distance nor a torus immersion is
assumed or constructed here. The transported Plane atlas is opt-in.
-/
open Manifold Bundle
open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter ContinuousLinearMap OAI.ClosedSurfaceR4

namespace NativeProductPlaneMetricBundle
section GeneralConstruction
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The actual derivative pulls back the ambient continuous bilinear inner product. -/
def immersionBilinear (F : M → V) (p : M) :
    TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ :=
  (mfderiv I 𝓘(ℝ, V) F p).precomp ℝ |>.comp
    ((innerSL ℝ : V →L[ℝ] V →L[ℝ] ℝ).comp (mfderiv I 𝓘(ℝ, V) F p))

@[simp] theorem immersionBilinear_apply (F : M → V) (p : M)
    (v w : TangentSpace I p) :
    immersionBilinear (I := I) F p v w =
      @inner ℝ V _ (mfderiv I 𝓘(ℝ, V) F p v : V)
        (mfderiv I 𝓘(ℝ, V) F p w : V) := rfl

/-- No injectivity hypothesis is needed for smoothness of the actual induced form. -/
theorem immersionBilinear_contMDiff [IsManifold I ∞ M]
    {F : M → V} (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) p
        (immersionBilinear (I := I) F p)) := by
  intro p
  rw [contMDiffAt_section]
  let d : M → E →L[ℝ] V := fun q =>
    (mfderiv I 𝓘(ℝ, V) F q).comp
      ((trivializationAt E (TangentSpace I) p).symmL ℝ q)
  have hd : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] V) ∞ d p := by
    have h := (hF p).mfderiv_const (m := ∞) (by simp)
    convert! h using 1
    ext q v
    simp [d, inTangentCoordinates, ContinuousLinearMap.inCoordinates]
    rfl
  let B : V →L[ℝ] V →L[ℝ] ℝ := innerSL ℝ
  have hi : ContMDiffAt I 𝓘(ℝ, V →L[ℝ] V →L[ℝ] ℝ) ∞
      (fun _ : M => B) p :=
    contMDiffAt_const
  have hg := hd.clm_precomp (F₃ := ℝ) |>.clm_comp (hi.clm_comp hd)
  apply hg.congr_of_eventuallyEq
  filter_upwards [(chartAt H p).open_source.mem_nhds (mem_chart_source H p)] with q hq
  rw [hom_trivializationAt_apply]
  ext v w
  have hqt : q ∈ (trivializationAt E (TangentSpace I) p).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hq
  rw [inCoordinates_apply_eq₂ hqt hqt (by simp)]
  simp only [Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization,
    LinearMap.id_coe, id_eq, immersionBilinear_apply]
  change @inner ℝ V _
      (mfderiv I 𝓘(ℝ, V) F q ((trivializationAt E (TangentSpace I) p).symm q v) : V)
      (mfderiv I 𝓘(ℝ, V) F q ((trivializationAt E (TangentSpace I) p).symm q w) : V) =
    @inner ℝ V _
      (mfderiv I 𝓘(ℝ, V) F q ((trivializationAt E (TangentSpace I) p).symmL ℝ q v) : V)
      (mfderiv I 𝓘(ℝ, V) F q ((trivializationAt E (TangentSpace I) p).symmL ℝ q w) : V)
  rw [(trivializationAt E (TangentSpace I) p).symmL_apply hqt,
    (trivializationAt E (TangentSpace I) p).symmL_apply hqt]

/-- The actual induced unit ball is bounded in the preexisting tangent topology. -/
theorem immersionBilinear_unitBall_bounded [FiniteDimensional ℝ E]
    {F : M → V} (p : M)
    (hinj : Function.Injective (mfderiv I 𝓘(ℝ, V) F p)) :
    Bornology.IsVonNBounded ℝ
      {v : TangentSpace I p | immersionBilinear (I := I) F p v v < 1} := by
  letI : NormedAddCommGroup (TangentSpace I p) :=
    inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TangentSpace I p) := inferInstanceAs (NormedSpace ℝ E)
  letI : FiniteDimensional ℝ (TangentSpace I p) := inferInstanceAs (FiniteDimensional ℝ E)
  let L : TangentSpace I p →L[ℝ] V := mfderiv I 𝓘(ℝ, V) F p
  obtain ⟨K, _, hK⟩ := L.toLinearMap.injective_iff_antilipschitz.mp hinj
  apply (NormedSpace.isVonNBounded_iff ℝ).mpr
  apply (hK.isBounded_preimage (Metric.isBounded_ball (x := (0 : V)) (r := 1))).subset
  intro v hv
  change @inner ℝ V _ (L v) (L v) < 1 at hv
  rw [real_inner_self_eq_norm_sq] at hv
  simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right]
  change ‖L v‖ < 1
  nlinarith [norm_nonneg (L v)]

/-- Construct the genuine smooth Riemannian metric of a smooth immersion.
Finite-dimensional injectivity proves topology compatibility rather than assuming it. -/
def immersionMetric [FiniteDimensional ℝ E] [IsManifold I ∞ M]
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ, V) ∞ F)
    (hinj : ∀ p, Function.Injective (mfderiv I 𝓘(ℝ, V) F p)) :
    Bundle.ContMDiffRiemannianMetric I ∞ E (fun p : M => TangentSpace I p) where
  inner := immersionBilinear (I := I) F
  symm p v w := by
    simp only [immersionBilinear_apply]
    exact real_inner_comm _ _
  pos p v hv := by
    rw [immersionBilinear_apply]
    apply real_inner_self_pos.mpr
    intro hz
    apply hv
    apply hinj p
    simpa only [map_zero] using hz
  isVonNBounded p := immersionBilinear_unitBall_bounded p (hinj p)
  contMDiff := immersionBilinear_contMDiff hF

end GeneralConstruction
end NativeProductPlaneMetricBundle

section NativeMetric
variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ModelProd ℝ ℝ) M]
  [IsManifold nativeProductModel ∞ M]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Actual smooth metric bundle on the native source; compactness is unnecessary. -/
def nativeProductImmersionMetric (F : M → V)
    (hF : ContMDiff nativeProductModel 𝓘(ℝ, V) ∞ F)
    (hinj : ∀ p, Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, V) F p)) :
    Bundle.ContMDiffRiemannianMetric nativeProductModel ∞ (ℝ × ℝ)
      (fun p : M => TangentSpace nativeProductModel p) :=
  NativeProductPlaneMetricBundle.immersionMetric F hF hinj

@[simp] theorem nativeProductImmersionMetric_inner (F : M → V)
    (hF : ContMDiff nativeProductModel 𝓘(ℝ, V) ∞ F)
    (hinj : ∀ p, Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, V) F p))
    (p : M) (v w : ℝ × ℝ) :
    (nativeProductImmersionMetric F hF hinj).inner p v w =
      nativeProductInducedForm F p v w := rfl

local instance metricBundlePlaneChartedSpace : ChartedSpace Plane M :=
  nativeProductPlaneChartedSpace M
local instance metricBundlePlaneIsManifold : IsManifold planeModel ∞ M :=
  nativeProductPlane_isManifold M

/-- The OpenAI Plane-model smooth induced metric, constructed from transported immersion data. -/
def nativeProductPlaneImmersionMetric (F : M → V)
    (hF : ContMDiff nativeProductModel 𝓘(ℝ, V) ∞ F)
    (hinj : ∀ p, Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, V) F p)) :
    Bundle.ContMDiffRiemannianMetric planeModel ∞ Plane
      (fun p : M => TangentSpace planeModel p) :=
  NativeProductPlaneMetricBundle.immersionMetric F
    ((nativeProductPlane_contMDiff_iff M F).mpr hF)
    (fun p => (nativeProductPlane_immersion_iff
      ((hF p).mdifferentiableAt (by simp))).mpr (hinj p))

@[simp] theorem nativeProductPlaneImmersionMetric_inner (F : M → V)
    (hF : ContMDiff nativeProductModel 𝓘(ℝ, V) ∞ F)
    (hinj : ∀ p, Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, V) F p))
    (p : M) (v w : TangentSpace planeModel p) :
    (nativeProductPlaneImmersionMetric F hF hinj).inner p v w = inducedForm F p v w := rfl

/-- The two constructed smooth metric bundles agree on the actual transported tangent vectors. -/
theorem nativeProductPlaneImmersionMetric_transport (F : M → V)
    (hF : ContMDiff nativeProductModel 𝓘(ℝ, V) ∞ F)
    (hinj : ∀ p, Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, V) F p))
    (p : M) (v w : ℝ × ℝ) :
    (nativeProductPlaneImmersionMetric F hF hinj).inner p
      (nativeProductPlaneEquiv v) (nativeProductPlaneEquiv w) =
    (nativeProductImmersionMetric F hF hinj).inner p v w := by
  rw [nativeProductPlaneImmersionMetric_inner, nativeProductImmersionMetric_inner]
  exact nativeProductPlane_inducedForm ((hF p).mdifferentiableAt (by simp)) v w

end NativeMetric
end
end TightVer401




