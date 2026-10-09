import TightVer401.CompletedSaddleTorusBandChartConnection
import TightVer401.CompletedSaddleTorusConnection
import TightVer401.TorusMetricBranching

/-! Connect one actual completed saddle and its protected band bending to one
constructed smooth embedded torus. The chart, affine placement, extension field,
and opposite branch metrics all refer to that same saddle and chosen meridian.
This application does not assume or assert tightness or branch embeddings. -/
open Manifold Bundle
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4
set_option backward.isDefEq.respectTransparency false

local instance : ChartedSpace Plane NonrigidTorusSource :=
  nativeProductPlaneChartedSpace NonrigidTorusSource
local instance : IsManifold planeModel ∞ NonrigidTorusSource :=
  nativeProductPlane_isManifold NonrigidTorusSource

variable {T w RN μ h : ℝ} [Fact (0 < T)]
variable {d : PeriodicRuledFrame T} {K : Set (AddCircle T × Ioo (0 : ℝ) w)}
variable (Q : CompletedSaddleAnnulusGeometryOutput d K RN μ h)

/-- The literal reflection and translation used by the protected saddle. -/
def completedSaddleTorusBandAffine : Ambient ≃ᵃⁱ[ℝ] Ambient :=
  AffineIsometryEquiv.constVSub ℝ (Q.verticalOffset • revolutionAxis)

@[simp] theorem completedSaddleTorusBandAffine_apply (x : Ambient) :
    completedSaddleTorusBandAffine Q x = -x + Q.verticalOffset • revolutionAxis := by
  change Q.verticalOffset • revolutionAxis - x = _
  rw [sub_eq_add_neg, add_comm]

/-- Any assembly retaining this actual saddle has exactly the required placement. -/
theorem completedSaddleTorusBending_placement
    (D : ProtectedTorusAssemblyInput RN μ h)
    (hD : D.toProtectedSaddleCylinderInput = Q.cylinder) :
    ∀ p ∈ (completedSaddleTorusBandChart Q).source,
      protectedTorusMap D.saddle D.meridian h (completedSaddleTorusBandChart Q p) =
        completedSaddleTorusBandAffine Q ((d.bandMap (b := w)) p) := by
  have hs : D.saddle = Q.cylinder.saddle :=
    congrArg ProtectedSaddleCylinderInput.saddle hD
  intro p hp
  rw [completedSaddleTorusBandAffine_apply, hs]
  exact completedSaddleTorusBandChart_placement Q D.meridian h hp

/-- The actual supported field misses a literal seam point; no exterior-point
hypothesis is needed in the branching application. -/
theorem completedSaddleTorusBending_exists_outside
    {Y : AddCircle T × Ioo (0 : ℝ) w → Ambient} (hsK : tsupport Y ⊆ K) :
    ∃ q : NonrigidTorusSource, q ∉ (completedSaddleTorusBandChart Q) '' tsupport Y := by
  refine ⟨0, ?_⟩
  intro hzero
  exact completedSaddleTorusBandChart_zero_not_mem_protected_image Q
    (image_mono hsK hzero)

/-- Construct the matching convex meridian once and extend the given compact
nonzero band bending onto the SAME actual embedded torus. -/
theorem exists_completedSaddleTorus_compact_nonzero_bending
    {Y : AddCircle T × Ioo (0 : ℝ) w → Ambient}
    (hX : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ (d.bandMap (b := w)))
    (hY : IsBandBending (d.bandMap (b := w)) Y) (hcompact : HasCompactSupport Y)
    (hnonzero : ∃ p, Y p ≠ 0) (hsK : tsupport Y ⊆ K) :
    ∃ D : ProtectedTorusAssemblyInput RN μ h,
      D.toProtectedSaddleCylinderInput = Q.cylinder ∧
      NativeTorusSmoothEmbedding (protectedTorusMap D.saddle D.meridian h) ∧
      (∀ p ∈ (completedSaddleTorusBandChart Q).source,
        protectedTorusMap D.saddle D.meridian h (completedSaddleTorusBandChart Q p) =
          completedSaddleTorusBandAffine Q ((d.bandMap (b := w)) p)) ∧
      let F := protectedTorusMap D.saddle D.meridian h
      let Z := protectedTorusBendingField
        (completedSaddleTorusBandChart Q) (completedSaddleTorusBandAffine Q) Y
      ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ Z ∧
        (∀ p (v z : ℝ × ℝ), nativeProductLinearMetricForm F Z p v z = 0) ∧
        HasCompactSupport Z ∧ (∃ p, Z p ≠ 0) ∧
        tsupport Z ⊆ (completedSaddleTorusBandChart Q) '' tsupport Y := by
  obtain ⟨D, hD, hF, _, _, _, _, _⟩ :=
    exists_protectedTorusAssembly_from_saddle Q.cylinder
  have hsupport : tsupport Y ⊆ (completedSaddleTorusBandChart Q).source :=
    hsK.trans (completedSaddleTorusBandChart_protected_source Q)
  have hplace := completedSaddleTorusBending_placement Q D hD
  refine ⟨D, hD, hF, hplace, ?_⟩
  exact protectedTorus_compact_nonzero_bending hX hY hcompact hnonzero
    (completedSaddleTorusBandChart Q) hsupport
    (completedSaddleTorusBandChart_inverse_smooth Q) (completedSaddleTorusBandAffine Q)
    (protectedTorusMap D.saddle D.meridian h) hplace

/-- Same-object constructed metric branches. Both actual maps are smooth
immersions with one common positive smooth metric and agree with the constructed
baseline on a nonempty open set. Nonzero amplitude separates parametrized maps. -/
theorem exists_completedSaddleTorus_metric_branching
    {Y : AddCircle T × Ioo (0 : ℝ) w → Ambient}
    (hX : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ (d.bandMap (b := w)))
    (hY : IsBandBending (d.bandMap (b := w)) Y) (hcompact : HasCompactSupport Y)
    (hnonzero : ∃ p, Y p ≠ 0) (hsK : tsupport Y ⊆ K)
    {ε : ℝ} (hε : ε ≠ 0) :
    ∃ D : ProtectedTorusAssemblyInput RN μ h,
      D.toProtectedSaddleCylinderInput = Q.cylinder ∧
      NativeTorusSmoothEmbedding (protectedTorusMap D.saddle D.meridian h) ∧
      let F := protectedTorusMap D.saddle D.meridian h
      let e := completedSaddleTorusBandChart Q
      let Z := protectedTorusBendingField e (completedSaddleTorusBandAffine Q) Y
      let U := (e '' tsupport Y)ᶜ
      (ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ Z ∧
        (∀ p (v z : ℝ × ℝ), nativeProductLinearMetricForm F Z p v z = 0) ∧
        HasCompactSupport Z ∧ (∃ p, Z p ≠ 0) ∧ tsupport Z ⊆ e '' tsupport Y) ∧
      ∃ g : Bundle.ContMDiffRiemannianMetric planeModel ∞ Plane
          (fun p : NonrigidTorusSource => TangentSpace planeModel p),
        ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ (F + ε • Z) ∧
        ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ (F - ε • Z) ∧
        ContMDiff planeModel 𝓘(ℝ, Ambient) ∞ (F + ε • Z) ∧
        ContMDiff planeModel 𝓘(ℝ, Ambient) ∞ (F - ε • Z) ∧
        (∀ (p : NonrigidTorusSource) (v z : TangentSpace planeModel p),
          g.inner p v z = inducedForm (F + ε • Z) p v z ∧
          g.inner p v z = inducedForm (F - ε • Z) p v z) ∧
        (∀ p (v z : ℝ × ℝ),
          nativeProductInducedForm (F + ε • Z) p v z =
            nativeProductInducedForm (F - ε • Z) p v z ∧
          nativeProductInducedForm (F + ε • Z) p v z =
            nativeProductInducedForm F p v z + ε ^ 2 * nativeProductInducedForm Z p v z) ∧
        (∀ p (v : ℝ × ℝ), v ≠ 0 →
          0 < nativeProductInducedForm (F + ε • Z) p v v) ∧
        (∀ p, Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient) (F + ε • Z) p) ∧
          Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient) (F - ε • Z) p)) ∧
        (IsOpen U ∧ U.Nonempty ∧ EqOn (F + ε • Z) F U ∧ EqOn (F - ε • Z) F U) ∧
        F + ε • Z ≠ F - ε • Z := by
  obtain ⟨D, hD, hF, hplace, hZ⟩ :=
    exists_completedSaddleTorus_compact_nonzero_bending Q hX hY hcompact hnonzero hsK
  have hsupport : tsupport Y ⊆ (completedSaddleTorusBandChart Q).source :=
    hsK.trans (completedSaddleTorusBandChart_protected_source Q)
  refine ⟨D, hD, hF, hZ, ?_⟩
  exact protectedTorus_metric_branching hX hY hcompact hnonzero
    (completedSaddleTorusBandChart Q) hsupport
    (completedSaddleTorusBandChart_inverse_smooth Q) (completedSaddleTorusBandAffine Q)
    (protectedTorusMap D.saddle D.meridian h) hplace hF.1 hF.2.1
    (completedSaddleTorusBending_exists_outside Q hsK) hε

end
end TightVer401
