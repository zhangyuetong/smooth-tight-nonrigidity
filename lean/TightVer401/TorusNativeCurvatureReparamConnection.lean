import TightVer401.ClassicalExternal
import TightVer401.ProtectedTorusPositiveGaussCurvatureReparam
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-! Actual native-source curvature covariance, consuming the already proved
physical Coord covariance. All chart domains and transition derivatives are
constructed from the actual native charts and a smooth source homeomorphism.
The pointwise normal is derived from actual independent tangents. -/
open Manifold
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false

local instance : IsManifold nativeProductModel ∞ NonrigidTorusSource :=
  nonrigidTorusSource_isManifold

/-- The actual native preferred chart expressed in the existing physical Coord. -/
def torusNativeCurvatureCoordChart (p : NonrigidTorusSource) :
    OpenPartialHomeomorph NonrigidTorusSource Coord :=
  (chartAt (ModelProd ℝ ℝ) p).trans
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.toHomeomorph.toOpenPartialHomeomorph

@[simp] theorem torusNativeCurvatureCoordChart_apply (p q : NonrigidTorusSource) :
    torusNativeCurvatureCoordChart p q =
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm (chartAt (ModelProd ℝ ℝ) p q) := rfl

@[simp] theorem torusNativeCurvatureCoordChart_symm_apply
    (p : NonrigidTorusSource) (q : Coord) :
    (torusNativeCurvatureCoordChart p).symm q =
      (chartAt (ModelProd ℝ ℝ) p).symm ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ) q) := rfl

private theorem native_to_coord_smooth :
    ContMDiff nativeProductModel 𝓘(ℝ, Coord) ∞
      (fun q : ModelProd ℝ ℝ =>
        (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm (nativeProductModel q)) := by
  have hL : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, Coord) ∞
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm :=
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.contDiff.contMDiff
  exact hL.comp nativeProductModel.contMDiff

private theorem coord_to_native_smooth :
    ContMDiff 𝓘(ℝ, Coord) nativeProductModel ∞
      (fun q : Coord =>
        (nativeProductModel.symm ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ) q) : ModelProd ℝ ℝ)) := by
  have hi : ContMDiff 𝓘(ℝ, ℝ × ℝ) nativeProductModel ∞
      (nativeProductModel.symm : ℝ × ℝ → ModelProd ℝ ℝ) := by
    intro x
    have hx : x ∈ range nativeProductModel := by
      rw [ModelWithCorners.range_eq_univ nativeProductModel]
      exact mem_univ x
    exact (nativeProductModel.contMDiffOn_symm x hx).contMDiffAt
      (by rw [ModelWithCorners.range_eq_univ nativeProductModel]; exact univ_mem)
  exact hi.comp (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).contDiff.contMDiff

private theorem coord_mfderiv_injective_iff
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : Coord → W) (q : Coord) :
    Function.Injective (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, W) f q) ↔
      Function.Injective (fderiv ℝ f q) := by
  rw [mfderiv_eq_fderiv]
  rfl

/-- Both directions of the actual Coord chart are smooth on their true domains. -/
theorem torusNativeCurvatureCoordChart_smooth (p : NonrigidTorusSource) :
    ContMDiffOn nativeProductModel 𝓘(ℝ, Coord) ∞
        (torusNativeCurvatureCoordChart p) (torusNativeCurvatureCoordChart p).source ∧
      ContMDiffOn 𝓘(ℝ, Coord) nativeProductModel ∞
        (torusNativeCurvatureCoordChart p).symm (torusNativeCurvatureCoordChart p).target := by
  constructor
  · intro q hq
    have hq' : q ∈ (chartAt (ModelProd ℝ ℝ) p).source := by
      simpa [torusNativeCurvatureCoordChart] using hq
    have hc : ContMDiffAt nativeProductModel nativeProductModel ∞
        (chartAt (ModelProd ℝ ℝ) p) q :=
      (contMDiffOn_chart (I := nativeProductModel) (n := ∞)).contMDiffAt
        ((chartAt (ModelProd ℝ ℝ) p).open_source.mem_nhds hq')
    exact ((native_to_coord_smooth _).comp q hc).contMDiffWithinAt
  · intro q hq
    have hq' : (nativeProductModel.symm ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ) q) : ModelProd ℝ ℝ) ∈
        (chartAt (ModelProd ℝ ℝ) p).target := by
      rw [torusNativeCurvatureCoordChart, OpenPartialHomeomorph.trans_target] at hq
      exact hq.2
    have hc : ContMDiffAt nativeProductModel nativeProductModel ∞
        (chartAt (ModelProd ℝ ℝ) p).symm
        (nativeProductModel.symm ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ) q) : ModelProd ℝ ℝ) :=
      (contMDiffOn_chart_symm (I := nativeProductModel) (n := ∞)).contMDiffAt
        ((chartAt (ModelProd ℝ ℝ) p).open_target.mem_nhds hq')
    exact (hc.comp q (coord_to_native_smooth q)).contMDiffWithinAt

/-- Inverse differentiation gives actual regularity of each chart direction. -/
theorem torusNativeCurvatureCoordChart_mdifferentiable (p : NonrigidTorusSource) :
    (torusNativeCurvatureCoordChart p).MDifferentiable nativeProductModel 𝓘(ℝ, Coord) := by
  have hc := torusNativeCurvatureCoordChart_smooth p
  exact ⟨hc.1.mdifferentiableOn (by simp), hc.2.mdifferentiableOn (by simp)⟩

/-- Actual source reparameterization covariance in the native preferred charts.
No supplied curvature function or covariance premise occurs in the inputs. -/
theorem nativeTorusChartCurvature_comp_homeomorph
    {F : NonrigidTorusSource → Ambient}
    (hF : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ F)
    (himm : ∀ q, Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient) F q))
    (e : NonrigidTorusSource ≃ₜ NonrigidTorusSource)
    (he : ContMDiff nativeProductModel nativeProductModel ∞ e)
    (hi : ContMDiff nativeProductModel nativeProductModel ∞ e.symm)
    (p : NonrigidTorusSource) :
    nativeTorusChartCurvature (F ∘ e) p = nativeTorusChartCurvature F (e p) := by
  let cp := torusNativeCurvatureCoordChart p
  let ct := torusNativeCurvatureCoordChart (e p)
  let ep := e.toOpenPartialHomeomorph
  let k : OpenPartialHomeomorph Coord Coord := (cp.symm.trans ep).trans ct
  let X : Coord → Ambient := F ∘ ct.symm
  let U : Set Coord := ct.target
  let V : Set Coord := k.source
  let z : Coord := cp p
  have hcp := torusNativeCurvatureCoordChart_smooth p
  have hct := torusNativeCurvatureCoordChart_smooth (e p)
  have hdcp := torusNativeCurvatureCoordChart_mdifferentiable p
  have hdct := torusNativeCurvatureCoordChart_mdifferentiable (e p)
  have hsep : ContMDiffOn nativeProductModel nativeProductModel ∞ ep ep.source := he.contMDiffOn
  have hsiep : ContMDiffOn nativeProductModel nativeProductModel ∞ ep.symm ep.target := hi.contMDiffOn
  have hdep : ep.MDifferentiable nativeProductModel nativeProductModel :=
    ⟨hsep.mdifferentiableOn (by simp), hsiep.mdifferentiableOn (by simp)⟩
  have hdk : k.MDifferentiable 𝓘(ℝ, Coord) 𝓘(ℝ, Coord) :=
    (hdcp.symm.trans hdep).trans hdct
  have hX : ContDiffOn ℝ ∞ X U :=
    (hF.comp_contMDiffOn hct.2).contDiffOn
  have hk : ContDiffOn ℝ ∞ (k : Coord → Coord) V := by
    have hs := hct.1.comp' (hsep.comp' hcp.2)
    simpa [k, ep, cp, ct, V, Function.comp_def] using hs.contDiffOn
  have hcpSource : p ∈ cp.source := by
    simpa [cp, torusNativeCurvatureCoordChart] using mem_chart_source (ModelProd ℝ ℝ) p
  have hctSource : e p ∈ ct.source := by
    simpa [ct, torusNativeCurvatureCoordChart] using mem_chart_source (ModelProd ℝ ℝ) (e p)
  have hz : z ∈ V := by
    simp [z, V, k, ep, cp.left_inv hcpSource, cp.map_source hcpSource, hctSource]
  have hmap : MapsTo (k : Coord → Coord) V U := by
    intro q hq
    have hq' : e (cp.symm q) ∈ ct.source := by
      simpa [V, k, ep] using hq.2
    exact ct.map_source hq'
  have hXinj : ∀ q ∈ U, Function.Injective (fderiv ℝ X q) := by
    intro q hq
    have hdF := (hF (ct.symm q)).mdifferentiableAt (by simp)
    have hdInv := hdct.mdifferentiableAt_symm hq
    have hd := mfderiv_comp q hdF hdInv
    have hj : Function.Injective
        ((mfderiv nativeProductModel 𝓘(ℝ, Ambient) F (ct.symm q)).comp
          (mfderiv 𝓘(ℝ, Coord) nativeProductModel ct.symm q)) :=
      (himm (ct.symm q)).comp (hdct.symm.mfderiv_injective hq)
    rw [← hd] at hj
    exact (coord_mfderiv_injective_iff X q).mp hj
  have hkinj : ∀ q ∈ V, Function.Injective (fderiv ℝ (k : Coord → Coord) q) := by
    intro q hq
    exact (coord_mfderiv_injective_iff (k : Coord → Coord) q).mp (hdk.mfderiv_injective hq)
  have hg := inducedMetric_smoothPositiveOn hX ct.open_target hXinj
  have hIsom := inducedMetric_isometricOn hX
  obtain ⟨n, hnUnit, hnTangents⟩ := exists_unit_normal_of_independent_tangents
    (fun i => coordPartial i X (k z)) (isometric_tangents_independent hg hIsom (hmap hz))
  have hn : IsUnitNormalAt X n (k z) := by
    refine ⟨hnUnit, ?_⟩
    intro v
    rw [fderiv_two_coordinates, inner_add_left, real_inner_smul_left,
      real_inner_smul_left, hnTangents 0, hnTangents 1]
    simp
  have hcov := protectedTorus_curvature_reparam ct.open_target k.open_source hX hk
    hmap hXinj hkinj hz hn
  have hvalue : k z = ct (e p) := by
    change ct (e (cp.symm (cp p))) = ct (e p)
    rw [cp.left_inv hcpSource]
  have hgerm : nativeProductCoordinateMap (F ∘ e) p =ᶠ[𝓝 z] (X ∘ k) := by
    filter_upwards [k.open_source.mem_nhds hz] with q hq
    have hq' : e (cp.symm q) ∈ ct.source := by
      simpa [V, k, ep] using hq.2
    change F (e (cp.symm q)) = F (ct.symm (ct (e (cp.symm q))))
    rw [ct.left_inv hq']
  have hlocal := gaussianCurvature_eq_of_eventuallyEq (inducedMetric_eventuallyEq hgerm)
  change gaussianCurvature (inducedMetric (nativeProductCoordinateMap (F ∘ e) p)) z =
    gaussianCurvature (inducedMetric X) (ct (e p))
  rw [hlocal, hcov, hvalue]

end
end TightVer401


