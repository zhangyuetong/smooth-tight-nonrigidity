import TightVer401.NativeProductPlaneForms
import TightVer401.BandBendingBranches

/-! Applications of the proved native-product/Plane atlas and tangent transport.
All Plane atlases here are local opt-in instances; the registered native atlas
of the band and torus is preserved. The native band branch calculus is reused.
-/
open Manifold
open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
set_option backward.isDefEq.respectTransparency false
open OAI.ClosedSurfaceR4

section NativeBending
variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ModelProd ℝ ℝ) M]

/-- Actual smooth native bending, using the native manifold differential. -/
def nativeProductIsBending (X Y : M → Manifold.ThreeSpace) : Prop :=
  ContMDiff nativeProductModel 𝓘(ℝ, Manifold.ThreeSpace) ∞ Y ∧
    ∀ p v w, nativeProductLinearMetricForm X Y p v w = 0

local instance nativeProductPlaneApplicationsChartedSpace : ChartedSpace Plane M := nativeProductPlaneChartedSpace M

/-- Genuine native strain and OpenAI strain agree under the proved tangent map. -/
theorem nativeProductPlane_isBending_iff {X Y : M → Manifold.ThreeSpace}
    (hX : ContMDiff nativeProductModel 𝓘(ℝ, Manifold.ThreeSpace) ∞ X) :
    Manifold.IsBending X Y ↔ nativeProductIsBending X Y := by
  constructor
  · intro hY
    have hYn := (nativeProductPlane_contMDiff_iff M Y).mp hY.1
    refine ⟨hYn, ?_⟩
    intro p
    exact (nativeProductPlane_zero_strain_iff
      ((hX p).mdifferentiableAt (by simp))
      ((hYn p).mdifferentiableAt (by simp))).mp (hY.2 p)
  · intro hY
    refine ⟨(nativeProductPlane_contMDiff_iff M Y).mpr hY.1, ?_⟩
    intro p
    exact (nativeProductPlane_zero_strain_iff
      ((hX p).mdifferentiableAt (by simp))
      ((hY.1 p).mdifferentiableAt (by simp))).mpr (hY.2 p)

/-- Pull the checked global opposite-branch theorem back to native tangents. -/
theorem nativeProduct_exact_sign_pair {X Y : M → Manifold.ThreeSpace}
    (hX : ContMDiff nativeProductModel 𝓘(ℝ, Manifold.ThreeSpace) ∞ X)
    (hY : nativeProductIsBending X Y) (p : M) (v w : ℝ × ℝ) :
    nativeProductInducedForm (X + Y) p v w =
      nativeProductInducedForm (X - Y) p v w := by
  have h := Manifold.exact_sign_pair
    ((nativeProductPlane_contMDiff_iff M X).mpr hX)
    ((nativeProductPlane_isBending_iff hX).mpr hY)
    p (nativeProductPlaneEquiv v) (nativeProductPlaneEquiv w)
  calc
    nativeProductInducedForm (X + Y) p v w =
        inducedForm (X + Y) p (nativeProductPlaneEquiv v) (nativeProductPlaneEquiv w) :=
      (nativeProductPlane_inducedForm (F := X + Y)
        (((hX.add hY.1) p).mdifferentiableAt (by simp)) v w).symm
    _ = inducedForm (X - Y) p (nativeProductPlaneEquiv v) (nativeProductPlaneEquiv w) := h
    _ = nativeProductInducedForm (X - Y) p v w :=
      nativeProductPlane_inducedForm (F := X - Y)
        (((hX.sub hY.1) p).mdifferentiableAt (by simp)) v w

/-- The checked quadratic metric formula applies to the actual native derivatives. -/
theorem nativeProduct_bending_common_metric {X Y : M → Manifold.ThreeSpace}
    (hX : ContMDiff nativeProductModel 𝓘(ℝ, Manifold.ThreeSpace) ∞ X)
    (hY : nativeProductIsBending X Y) (ε : ℝ) (p : M) (v w : ℝ × ℝ) :
    nativeProductInducedForm (X + ε • Y) p v w =
      nativeProductInducedForm X p v w + ε ^ 2 * nativeProductInducedForm Y p v w := by
  have hc : ContMDiff nativeProductModel 𝓘(ℝ, ℝ) ∞ (fun _ : M => ε) :=
    contMDiff_const
  have hεY : ContMDiff nativeProductModel 𝓘(ℝ, Manifold.ThreeSpace) ∞ (ε • Y) :=
    hc.smul hY.1
  have hXp := ((nativeProductPlane_contMDiff_iff M X).mpr hX p).mdifferentiableAt
    (by simp)
  have hYp := ((nativeProductPlane_contMDiff_iff M Y).mpr hY.1 p).mdifferentiableAt
    (by simp)
  have h := Manifold.metric_quadratic hXp (hYp.const_smul ε)
    (nativeProductPlaneEquiv v) (nativeProductPlaneEquiv w)
  have hs : linearMetricForm X (ε • Y) p
      (nativeProductPlaneEquiv v) (nativeProductPlaneEquiv w) =
      ε * linearMetricForm X Y p (nativeProductPlaneEquiv v) (nativeProductPlaneEquiv w) :=
    Manifold.strain_const_smul (X := X) (y := Y) hYp ε
      (nativeProductPlaneEquiv v) (nativeProductPlaneEquiv w)
  have hb : linearMetricForm X Y p
      (nativeProductPlaneEquiv v) (nativeProductPlaneEquiv w) = 0 :=
    ((nativeProductPlane_isBending_iff hX).mpr hY).2 p _ _
  have hm : inducedForm (ε • Y) p
      (nativeProductPlaneEquiv v) (nativeProductPlaneEquiv w) =
      ε ^ 2 * inducedForm Y p (nativeProductPlaneEquiv v) (nativeProductPlaneEquiv w) :=
    Manifold.metric_const_smul (y := Y) hYp ε
      (nativeProductPlaneEquiv v) (nativeProductPlaneEquiv w)
  rw [hs, hb, hm, mul_zero, add_zero] at h
  have hpull := nativeProductPlane_inducedForm (F := X + ε • Y)
    (((hX.add hεY) p).mdifferentiableAt (by simp)) v w
  have hXpull := nativeProductPlane_inducedForm (F := X)
    ((hX p).mdifferentiableAt (by simp)) v w
  have hYpull := nativeProductPlane_inducedForm (F := Y)
    ((hY.1 p).mdifferentiableAt (by simp)) v w
  rw [hpull, hXpull, hYpull] at h
  exact h

end NativeBending

section BandApplication
variable {L b : ℝ} [Fact (0 < L)]
local instance nativeProductPlaneBandApplicationsChartedSpace : ChartedSpace Plane (AddCircle L × Set.Ioo (0 : ℝ) b) :=
  nativeProductPlaneChartedSpace _

/-- The retained native-band bending condition is the generic native condition. -/
theorem isBandBending_iff_nativeProductIsBending
    {X Y : AddCircle L × Set.Ioo (0 : ℝ) b → OAI.SmoothLocal.Geometry.Ambient} :
    IsBandBending X Y ↔ nativeProductIsBending X Y := by
  rfl

/-- Apply the checked plane-model bending API to the actual native band field. -/
theorem isBandBending_to_manifold
    {X Y : AddCircle L × Set.Ioo (0 : ℝ) b → OAI.SmoothLocal.Geometry.Ambient}
    (hX : ContMDiff nativeProductModel 𝓘(ℝ, OAI.SmoothLocal.Geometry.Ambient) ∞ X)
    (hY : IsBandBending X Y) : Manifold.IsBending X Y :=
  (nativeProductPlane_isBending_iff hX).mpr
    (isBandBending_iff_nativeProductIsBending.mp hY)

/-- OpenAI's induced form pulls back to the existing bandInducedForm. -/
theorem nativeProductPlane_bandInducedForm
    {X : AddCircle L × Set.Ioo (0 : ℝ) b → OAI.SmoothLocal.Geometry.Ambient}
    {p : AddCircle L × Set.Ioo (0 : ℝ) b}
    (hX : MDifferentiableAt nativeProductModel 𝓘(ℝ, OAI.SmoothLocal.Geometry.Ambient) X p)
    (v w : ℝ × ℝ) :
    inducedForm X p (nativeProductPlaneEquiv v) (nativeProductPlaneEquiv w) =
      bandInducedForm X p v w :=
  nativeProductPlane_inducedForm hX v w

/-- The actual native band opposite branches also have equal OpenAI induced forms. -/
theorem bandBending_plane_exact_sign_pair
    {X Y : AddCircle L × Set.Ioo (0 : ℝ) b → OAI.SmoothLocal.Geometry.Ambient}
    (hX : ContMDiff nativeProductModel 𝓘(ℝ, OAI.SmoothLocal.Geometry.Ambient) ∞ X)
    (hY : IsBandBending X Y) (ε : ℝ)
    (p : AddCircle L × Set.Ioo (0 : ℝ) b) (v w : TangentSpace planeModel p) :
    inducedForm (X + ε • Y) p v w = inducedForm (X - ε • Y) p v w := by
  obtain ⟨v, rfl⟩ := nativeProductPlaneEquiv.surjective v
  obtain ⟨w, rfl⟩ := nativeProductPlaneEquiv.surjective w
  obtain ⟨hplus, hminus⟩ := bandBending_branches_contMDiff hX hY ε
  rw [nativeProductPlane_bandInducedForm ((hplus p).mdifferentiableAt (by simp)),
    nativeProductPlane_bandInducedForm ((hminus p).mdifferentiableAt (by simp))]
  exact congrFun (congrFun (congrFun (bandBending_opposite_branches_metric hX hY ε) p) v) w

end BandApplication

/-- Reusable exact metric pair on the registered native torus source.
The immersion, global embedding, protected support and torus bending construction
remain separate application inputs. -/
theorem nonrigidTorusSource_native_exact_sign_pair
    {X Y : NonrigidTorusSource → Manifold.ThreeSpace}
    (hX : ContMDiff nativeProductModel 𝓘(ℝ, Manifold.ThreeSpace) ∞ X)
    (hY : nativeProductIsBending X Y) (p : NonrigidTorusSource) (v w : ℝ × ℝ) :
    nativeProductInducedForm (X + Y) p v w =
      nativeProductInducedForm (X - Y) p v w :=
  nativeProduct_exact_sign_pair hX hY p v w

end
end TightVer401


