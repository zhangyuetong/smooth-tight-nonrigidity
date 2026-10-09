import TightVer401.NativeProductPlaneMetricBundle

/-! Smooth compatibility of the actual native and Plane tangent metric bundles.
The maps are the actual tangent maps of the atlas-changing identities. Their
fiber formulas, inverse laws, total-space smoothness and metric pairings are
proved from the existing derivative and smooth metric constructions.
-/
open Manifold Bundle
open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
set_option backward.isDefEq.respectTransparency false
open OAI.ClosedSurfaceR4

section TangentTransport
variable (M : Type*) [TopologicalSpace M] [ChartedSpace (ModelProd ℝ ℝ) M]
  [IsManifold nativeProductModel ∞ M]

local instance metricBundleTransportPlaneChartedSpace : ChartedSpace Plane M :=
  nativeProductPlaneChartedSpace M
local instance metricBundleTransportPlaneIsManifold : IsManifold planeModel ∞ M :=
  nativeProductPlane_isManifold M

/-- Actual bundled differential of the native-to-Plane atlas identity. -/
def nativeProductPlaneTangentMap :
    TangentBundle nativeProductModel M → TangentBundle planeModel M :=
  tangentMap nativeProductModel planeModel (id : M → M)

/-- Actual bundled differential of the inverse atlas identity. -/
def nativeProductPlaneInverseTangentMap :
    TangentBundle planeModel M → TangentBundle nativeProductModel M :=
  tangentMap planeModel nativeProductModel (id : M → M)

/-- Smoothness is in the actual tangent total-space chart models. -/
theorem nativeProductPlaneTangentMap_contMDiff :
    ContMDiff (nativeProductModel.prod 𝓘(ℝ, ℝ × ℝ))
      (planeModel.prod 𝓘(ℝ, Plane)) ∞ (nativeProductPlaneTangentMap M) :=
  (nativeProductPlane_identity_contMDiff M).contMDiff_tangentMap (m := ∞) (by simp)

theorem nativeProductPlaneInverseTangentMap_contMDiff :
    ContMDiff (planeModel.prod 𝓘(ℝ, Plane))
      (nativeProductModel.prod 𝓘(ℝ, ℝ × ℝ)) ∞ (nativeProductPlaneInverseTangentMap M) :=
  (nativeProductPlane_inverse_contMDiff M).contMDiff_tangentMap (m := ∞) (by simp)

@[simp] theorem nativeProductPlaneTangentMap_base
    (z : TangentBundle nativeProductModel M) :
    (nativeProductPlaneTangentMap M z).1 = z.1 := rfl

@[simp] theorem nativeProductPlaneInverseTangentMap_base
    (z : TangentBundle planeModel M) :
    (nativeProductPlaneInverseTangentMap M z).1 = z.1 := rfl

/-- Fiber map of the actual bundled differential is the proved continuous linear equivalence. -/
@[simp] theorem nativeProductPlaneTangentMap_fiber
    (z : TangentBundle nativeProductModel M) :
    (nativeProductPlaneTangentMap M z).2 = nativeProductPlaneEquiv z.2 := by
  change mfderiv nativeProductModel planeModel (id : M → M) z.1 z.2 = _
  rw [(nativeProductPlane_identity_hasMFDerivAt M z.1).mfderiv]
  rfl

@[simp] theorem nativeProductPlaneInverseTangentMap_fiber
    (z : TangentBundle planeModel M) :
    (nativeProductPlaneInverseTangentMap M z).2 = nativeProductPlaneEquiv.symm z.2 := by
  change mfderiv planeModel nativeProductModel (id : M → M) z.1 z.2 = _
  rw [(nativeProductPlane_inverse_hasMFDerivAt M z.1).mfderiv]
  rfl

@[simp] theorem nativeProductPlaneTangentMap_apply (p : M)
    (v : TangentSpace nativeProductModel p) :
    nativeProductPlaneTangentMap M (TotalSpace.mk' (ℝ × ℝ) p v) =
      TotalSpace.mk' Plane p (nativeProductPlaneEquiv v) := by
  change TotalSpace.mk' Plane p
    (mfderiv nativeProductModel planeModel (id : M → M) p v) = _
  rw [(nativeProductPlane_identity_hasMFDerivAt M p).mfderiv]
  rfl

@[simp] theorem nativeProductPlaneInverseTangentMap_apply (p : M)
    (v : TangentSpace planeModel p) :
    nativeProductPlaneInverseTangentMap M (TotalSpace.mk' Plane p v) =
      TotalSpace.mk' (ℝ × ℝ) p (nativeProductPlaneEquiv.symm v) := by
  change TotalSpace.mk' (ℝ × ℝ) p
    (mfderiv planeModel nativeProductModel (id : M → M) p v) = _
  rw [(nativeProductPlane_inverse_hasMFDerivAt M p).mfderiv]
  rfl

/-- The actual tangent maps are mutually inverse on total spaces. -/
theorem nativeProductPlaneTangentMap_leftInverse :
    Function.LeftInverse (nativeProductPlaneInverseTangentMap M)
      (nativeProductPlaneTangentMap M) := by
  rintro ⟨p, v⟩
  rw [nativeProductPlaneTangentMap_apply, nativeProductPlaneInverseTangentMap_apply,
    nativeProductPlaneEquiv.symm_apply_apply]

theorem nativeProductPlaneTangentMap_rightInverse :
    Function.RightInverse (nativeProductPlaneInverseTangentMap M)
      (nativeProductPlaneTangentMap M) := by
  rintro ⟨p, v⟩
  rw [nativeProductPlaneInverseTangentMap_apply, nativeProductPlaneTangentMap_apply,
    nativeProductPlaneEquiv.apply_symm_apply]

/-- An actual equivalence of tangent total spaces, with both directions smooth above. -/
def nativeProductPlaneTangentEquiv :
    TangentBundle nativeProductModel M ≃ TangentBundle planeModel M where
  toFun := nativeProductPlaneTangentMap M
  invFun := nativeProductPlaneInverseTangentMap M
  left_inv := nativeProductPlaneTangentMap_leftInverse M
  right_inv := nativeProductPlaneTangentMap_rightInverse M

/-- The smooth tangent equivalence also preserves the actual total-space topology. -/
def nativeProductPlaneTangentHomeomorph :
    TangentBundle nativeProductModel M ≃ₜ TangentBundle planeModel M where
  toEquiv := nativeProductPlaneTangentEquiv M
  continuous_toFun := (nativeProductPlaneTangentMap_contMDiff M).continuous
  continuous_invFun := (nativeProductPlaneInverseTangentMap_contMDiff M).continuous

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The actual smooth bundle map preserves the constructed induced metric pairing. -/
theorem nativeProductPlaneTangentMap_pairing (F : M → V)
    (hF : ContMDiff nativeProductModel 𝓘(ℝ, V) ∞ F)
    (hinj : ∀ p, Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, V) F p))
    (p : M) (v w : TangentSpace nativeProductModel p) :
    (nativeProductPlaneImmersionMetric F hF hinj).inner p
      (nativeProductPlaneTangentMap M (TotalSpace.mk' (ℝ × ℝ) p v)).2
      (nativeProductPlaneTangentMap M (TotalSpace.mk' (ℝ × ℝ) p w)).2 =
    (nativeProductImmersionMetric F hF hinj).inner p v w := by
  rw [nativeProductPlaneTangentMap_fiber, nativeProductPlaneTangentMap_fiber]
  exact nativeProductPlaneImmersionMetric_transport F hF hinj p v w

/-- Inverse smooth bundle transport preserves the same actual metric pairing. -/
theorem nativeProductPlaneInverseTangentMap_pairing (F : M → V)
    (hF : ContMDiff nativeProductModel 𝓘(ℝ, V) ∞ F)
    (hinj : ∀ p, Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, V) F p))
    (p : M) (v w : TangentSpace planeModel p) :
    (nativeProductImmersionMetric F hF hinj).inner p
      (nativeProductPlaneInverseTangentMap M (TotalSpace.mk' Plane p v)).2
      (nativeProductPlaneInverseTangentMap M (TotalSpace.mk' Plane p w)).2 =
    (nativeProductPlaneImmersionMetric F hF hinj).inner p v w := by
  rw [nativeProductPlaneInverseTangentMap_fiber, nativeProductPlaneInverseTangentMap_fiber]
  have h := nativeProductPlaneImmersionMetric_transport F hF hinj p
    (nativeProductPlaneEquiv.symm v) (nativeProductPlaneEquiv.symm w)
  simpa only [nativeProductPlaneEquiv.apply_symm_apply] using h.symm

end TangentTransport
end
end TightVer401
