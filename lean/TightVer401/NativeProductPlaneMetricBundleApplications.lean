import TightVer401.NativeProductPlaneMetricBundleTransport
import TightVer401.NativeProductPlaneFormsApplications

/-! A genuine common smooth metric for opposite native bending branches.

Primary interface: X is an actual native smooth immersion into three-space,
and Y is an actual native smooth zero-strain bending. The quadratic metric
identity derives immersion of every scaled branch; a genuine common smooth
positive Plane metric equals the actual induced forms of both opposite branches.
Lower-level helpers also accept an actual plus-branch immersion. Intrinsic
distance and construction of the embedded torus remain application gates.
-/
open Manifold Bundle
open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
set_option backward.isDefEq.respectTransparency false
open OAI.ClosedSurfaceR4

section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ModelProd ℝ ℝ) M]

/-- Equal actual opposite-branch forms transfer differential injectivity. -/
theorem nativeProduct_opposite_branch_immersion {X Y : M → Manifold.ThreeSpace}
    (hX : ContMDiff nativeProductModel 𝓘(ℝ, Manifold.ThreeSpace) ∞ X)
    (hY : nativeProductIsBending X Y)
    (hinj : ∀ p, Function.Injective
      (mfderiv nativeProductModel 𝓘(ℝ, Manifold.ThreeSpace) (X + Y) p)) :
    ∀ p, Function.Injective
      (mfderiv nativeProductModel 𝓘(ℝ, Manifold.ThreeSpace) (X - Y) p) := by
  intro p v w hvw
  have hzero : mfderiv nativeProductModel 𝓘(ℝ, Manifold.ThreeSpace)
      (X - Y) p (v - w) = 0 := by
    rw [map_sub, hvw, sub_self]
  have hform : nativeProductInducedForm (X + Y) p (v - w) (v - w) = 0 := by
    rw [nativeProduct_exact_sign_pair hX hY]
    simp only [nativeProductInducedForm, hzero, inner_zero_left]
  change @inner ℝ Manifold.ThreeSpace _
    (mfderiv nativeProductModel 𝓘(ℝ, Manifold.ThreeSpace) (X + Y) p (v - w))
    (mfderiv nativeProductModel 𝓘(ℝ, Manifold.ThreeSpace) (X + Y) p (v - w)) = 0 at hform
  have hz : mfderiv nativeProductModel 𝓘(ℝ, Manifold.ThreeSpace)
      (X + Y) p (v - w) = 0 := inner_self_eq_zero.mp hform
  exact sub_eq_zero.mp (hinj p (by simpa only [map_zero] using hz))

local instance nativeProductPlaneMetricApplicationsChartedSpace : ChartedSpace Plane M :=
  nativeProductPlaneChartedSpace M

local instance nativeProductPlaneMetricApplicationsIsManifold
    [IsManifold nativeProductModel ∞ M] : IsManifold planeModel ∞ M :=
  nativeProductPlane_isManifold M

/-- Construct one actual smooth positive metric bundle shared by both branches. -/
theorem nativeProductPlane_bending_common_smooth_metric
    [IsManifold nativeProductModel ∞ M] {X Y : M → Manifold.ThreeSpace}
    (hX : ContMDiff nativeProductModel 𝓘(ℝ, Manifold.ThreeSpace) ∞ X)
    (hY : nativeProductIsBending X Y)
    (hinj : ∀ p, Function.Injective
      (mfderiv nativeProductModel 𝓘(ℝ, Manifold.ThreeSpace) (X + Y) p)) :
    ∃ g : Bundle.ContMDiffRiemannianMetric planeModel ∞ Plane
        (fun p : M => TangentSpace planeModel p),
      ContMDiff planeModel 𝓘(ℝ, Manifold.ThreeSpace) ∞ (X + Y) ∧
      ContMDiff planeModel 𝓘(ℝ, Manifold.ThreeSpace) ∞ (X - Y) ∧
      (∀ (p : M) (v w : TangentSpace planeModel p),
        g.inner p v w = inducedForm (X + Y) p v w ∧
        g.inner p v w = inducedForm (X - Y) p v w) ∧
      (∀ p : M, Function.Injective (surfaceDifferential (X + Y) p) ∧
        Function.Injective (surfaceDifferential (X - Y) p)) := by
  have hplus := hX.add hY.1
  have hminus := hX.sub hY.1
  refine ⟨nativeProductPlaneImmersionMetric (X + Y) hplus hinj,
    (nativeProductPlane_contMDiff_iff M _).mpr hplus,
    (nativeProductPlane_contMDiff_iff M _).mpr hminus, ?_, ?_⟩
  · intro p v w
    have hg := nativeProductPlaneImmersionMetric_inner (X + Y) hplus hinj p v w
    exact ⟨hg, hg.trans (Manifold.exact_sign_pair
      ((nativeProductPlane_contMDiff_iff M X).mpr hX)
      ((nativeProductPlane_isBending_iff hX).mpr hY) p v w)⟩
  · intro p
    exact ⟨(nativeProductPlane_immersion_iff
      ((hplus p).mdifferentiableAt (by simp))).mpr (hinj p),
      (nativeProductPlane_immersion_iff
        ((hminus p).mdifferentiableAt (by simp))).mpr
        (nativeProduct_opposite_branch_immersion hX hY hinj p)⟩

/-- Scalar amplitudes preserve the actual native zero-strain bending condition. -/
theorem nativeProduct_bending_const_smul {X Y : M → Manifold.ThreeSpace}
    (hX : ContMDiff nativeProductModel 𝓘(ℝ, Manifold.ThreeSpace) ∞ X)
    (hY : nativeProductIsBending X Y) (ε : ℝ) :
    nativeProductIsBending X (ε • Y) := by
  have hc : ContMDiff nativeProductModel 𝓘(ℝ, ℝ) ∞ (fun _ : M => ε) := contMDiff_const
  have hεY : ContMDiff nativeProductModel 𝓘(ℝ, Manifold.ThreeSpace) ∞ (ε • Y) := hc.smul hY.1
  have hplane := (nativeProductPlane_isBending_iff hX).mpr hY
  apply (nativeProductPlane_isBending_iff hX).mp
  refine ⟨(nativeProductPlane_contMDiff_iff M _).mpr hεY, ?_⟩
  intro p v w
  have hs := Manifold.strain_const_smul (X := X) (y := Y)
    ((hplane.1 p).mdifferentiableAt (by simp)) ε v w
  rw [hs, hplane.2 p v w, mul_zero]

/-- Every real amplitude has a genuine common metric once its actual plus branch
is an immersion. No amplitude threshold is granted. -/
theorem nativeProductPlane_bending_scaled_common_smooth_metric_of_plus_immersion
    [IsManifold nativeProductModel ∞ M] {X Y : M → Manifold.ThreeSpace}
    (hX : ContMDiff nativeProductModel 𝓘(ℝ, Manifold.ThreeSpace) ∞ X)
    (hY : nativeProductIsBending X Y) (ε : ℝ)
    (hinj : ∀ p, Function.Injective
      (mfderiv nativeProductModel 𝓘(ℝ, Manifold.ThreeSpace) (X + ε • Y) p)) :
    ∃ g : Bundle.ContMDiffRiemannianMetric planeModel ∞ Plane
        (fun p : M => TangentSpace planeModel p),
      ContMDiff planeModel 𝓘(ℝ, Manifold.ThreeSpace) ∞ (X + ε • Y) ∧
      ContMDiff planeModel 𝓘(ℝ, Manifold.ThreeSpace) ∞ (X - ε • Y) ∧
      (∀ (p : M) (v w : TangentSpace planeModel p),
        g.inner p v w = inducedForm (X + ε • Y) p v w ∧
        g.inner p v w = inducedForm (X - ε • Y) p v w) ∧
      (∀ p : M, Function.Injective (surfaceDifferential (X + ε • Y) p) ∧
        Function.Injective (surfaceDifferential (X - ε • Y) p)) :=
  nativeProductPlane_bending_common_smooth_metric hX
    (nativeProduct_bending_const_smul hX hY ε) hinj

/-- Actual zero strain preserves immersion for every amplitude, from the
positive baseline induced form and the checked quadratic metric identity. -/
theorem nativeProduct_bending_branch_immersion {X Y : M → Manifold.ThreeSpace}
    (hX : ContMDiff nativeProductModel 𝓘(ℝ, Manifold.ThreeSpace) ∞ X)
    (hY : nativeProductIsBending X Y) (ε : ℝ)
    (hinj : ∀ p, Function.Injective
      (mfderiv nativeProductModel 𝓘(ℝ, Manifold.ThreeSpace) X p)) :
    ∀ p, Function.Injective
      (mfderiv nativeProductModel 𝓘(ℝ, Manifold.ThreeSpace) (X + ε • Y) p) := by
  intro p v w he
  let z := v - w
  have hdz : mfderiv nativeProductModel 𝓘(ℝ, Manifold.ThreeSpace)
      (X + ε • Y) p z = 0 := by
    simp only [z, map_sub, he, sub_self]
  have hmetric := nativeProduct_bending_common_metric hX hY ε p z z
  have hmetriczero : nativeProductInducedForm (X + ε • Y) p z z = 0 := by
    simp only [nativeProductInducedForm, hdz, inner_zero_left]
  rw [hmetriczero] at hmetric
  have hnonneg : 0 ≤ ε ^ 2 * nativeProductInducedForm Y p z z :=
    mul_nonneg (sq_nonneg ε) real_inner_self_nonneg
  have hbasenonneg : 0 ≤ nativeProductInducedForm X p z z := real_inner_self_nonneg
  have hbasezero : nativeProductInducedForm X p z z = 0 := by linarith
  have hdzX : mfderiv nativeProductModel 𝓘(ℝ, Manifold.ThreeSpace) X p z = 0 :=
    inner_self_eq_zero.mp hbasezero
  apply hinj p
  exact sub_eq_zero.mp (by simpa only [z, map_sub] using hdzX)

/-- From an actual native baseline immersion and actual native bending,
construct the genuine common smooth positive metric for every real amplitude. -/
theorem nativeProductPlane_bending_scaled_common_smooth_metric
    [IsManifold nativeProductModel ∞ M] {X Y : M → Manifold.ThreeSpace}
    (hX : ContMDiff nativeProductModel 𝓘(ℝ, Manifold.ThreeSpace) ∞ X)
    (hY : nativeProductIsBending X Y) (ε : ℝ)
    (hinj : ∀ p, Function.Injective
      (mfderiv nativeProductModel 𝓘(ℝ, Manifold.ThreeSpace) X p)) :
    ∃ g : Bundle.ContMDiffRiemannianMetric planeModel ∞ Plane
        (fun p : M => TangentSpace planeModel p),
      ContMDiff planeModel 𝓘(ℝ, Manifold.ThreeSpace) ∞ (X + ε • Y) ∧
      ContMDiff planeModel 𝓘(ℝ, Manifold.ThreeSpace) ∞ (X - ε • Y) ∧
      (∀ (p : M) (v w : TangentSpace planeModel p),
        g.inner p v w = inducedForm (X + ε • Y) p v w ∧
        g.inner p v w = inducedForm (X - ε • Y) p v w) ∧
      (∀ p : M, Function.Injective (surfaceDifferential (X + ε • Y) p) ∧
        Function.Injective (surfaceDifferential (X - ε • Y) p)) :=
  nativeProductPlane_bending_scaled_common_smooth_metric_of_plus_immersion hX hY ε
    (nativeProduct_bending_branch_immersion hX hY ε hinj)

end
end
end TightVer401

