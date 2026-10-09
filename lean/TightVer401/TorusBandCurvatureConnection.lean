import TightVer401.TorusNativeCurvatureReparamConnection
import TightVer401.TorusRigidCurvatureConnection
import TightVer401.BandBendingNativeCurvature
import TightVer401.TorusMetricBranchingPositive

/-! Actual local curvature comparison between the protected native band and
native torus, through their same smooth partial homeomorphism and literal
ambient affine-isometry placement. The compact bending bound is consumed on
the same field and support image. No curvature covariance is assumed. -/
open Manifold
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false

local instance : IsManifold nativeProductModel ∞ NonrigidTorusSource :=
  nonrigidTorusSource_isManifold

variable {T w : ℝ} [Fact (0 < T)]

/-- The actual preferred band chart in the existing physical Coord model. -/
def bandNativeCurvatureCoordChart (p : AddCircle T × Ioo (0 : ℝ) w) :
    OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) Coord :=
  (chartAt (ModelProd ℝ ℝ) p).trans
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.toHomeomorph.toOpenPartialHomeomorph

@[simp] theorem bandNativeCurvatureCoordChart_apply
    (p q : AddCircle T × Ioo (0 : ℝ) w) :
    bandNativeCurvatureCoordChart p q =
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm (chartAt (ModelProd ℝ ℝ) p q) := rfl

@[simp] theorem bandNativeCurvatureCoordChart_symm_apply
    (p : AddCircle T × Ioo (0 : ℝ) w) (q : Coord) :
    (bandNativeCurvatureCoordChart p).symm q =
      (chartAt (ModelProd ℝ ℝ) p).symm ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ) q) := rfl

private theorem band_native_to_coord_smooth :
    ContMDiff nativeProductModel 𝓘(ℝ, Coord) ∞
      (fun q : ModelProd ℝ ℝ =>
        (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm (nativeProductModel q)) := by
  have hL : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, Coord) ∞
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm :=
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.contDiff.contMDiff
  exact hL.comp nativeProductModel.contMDiff

private theorem band_coord_to_native_smooth :
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

/-- Both chart directions are smooth on their true open domains. -/
theorem bandNativeCurvatureCoordChart_smooth (p : AddCircle T × Ioo (0 : ℝ) w) :
    ContMDiffOn nativeProductModel 𝓘(ℝ, Coord) ∞
        (bandNativeCurvatureCoordChart p) (bandNativeCurvatureCoordChart p).source ∧
      ContMDiffOn 𝓘(ℝ, Coord) nativeProductModel ∞
        (bandNativeCurvatureCoordChart p).symm (bandNativeCurvatureCoordChart p).target := by
  constructor
  · intro q hq
    have hq' : q ∈ (chartAt (ModelProd ℝ ℝ) p).source := by
      simpa [bandNativeCurvatureCoordChart] using hq
    have hc : ContMDiffAt nativeProductModel nativeProductModel ∞
        (chartAt (ModelProd ℝ ℝ) p) q :=
      (contMDiffOn_chart (I := nativeProductModel) (n := ∞)).contMDiffAt
        ((chartAt (ModelProd ℝ ℝ) p).open_source.mem_nhds hq')
    exact ((band_native_to_coord_smooth _).comp q hc).contMDiffWithinAt
  · intro q hq
    have hq' : (nativeProductModel.symm ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ) q) : ModelProd ℝ ℝ) ∈
        (chartAt (ModelProd ℝ ℝ) p).target := by
      rw [bandNativeCurvatureCoordChart, OpenPartialHomeomorph.trans_target] at hq
      exact hq.2
    have hc : ContMDiffAt nativeProductModel nativeProductModel ∞
        (chartAt (ModelProd ℝ ℝ) p).symm
        (nativeProductModel.symm ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ) q) : ModelProd ℝ ℝ) :=
      (contMDiffOn_chart_symm (I := nativeProductModel) (n := ∞)).contMDiffAt
        ((chartAt (ModelProd ℝ ℝ) p).open_target.mem_nhds hq')
    exact (hc.comp q (band_coord_to_native_smooth q)).contMDiffWithinAt

/-- True inverse differentiation supplies the chart ranks. -/
theorem bandNativeCurvatureCoordChart_mdifferentiable
    (p : AddCircle T × Ioo (0 : ℝ) w) :
    (bandNativeCurvatureCoordChart p).MDifferentiable nativeProductModel 𝓘(ℝ, Coord) := by
  have hc := bandNativeCurvatureCoordChart_smooth p
  exact ⟨hc.1.mdifferentiableOn (by simp), hc.2.mdifferentiableOn (by simp)⟩

private theorem band_coord_mfderiv_injective_iff
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : Coord → W) (q : Coord) :
    Function.Injective (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, W) f q) ↔
      Function.Injective (fderiv ℝ f q) := by
  rw [mfderiv_eq_fderiv]
  rfl

/-- A literal placement through an actual smooth partial homeomorphism
identifies the true intrinsic preferred-chart curvatures of both surfaces.
The band map may be arbitrary away from the open placement source. -/
theorem nativeTorusChartCurvature_of_band_placement
    (X : AddCircle T × Ioo (0 : ℝ) w → Ambient)
    (G : NonrigidTorusSource → Ambient)
    (hG : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ G)
    (himm : ∀ q, Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient) G q))
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) NonrigidTorusSource)
    (he : ContMDiffOn nativeProductModel nativeProductModel ∞ e e.source)
    (hi : ContMDiffOn nativeProductModel nativeProductModel ∞ e.symm e.target)
    (A : Ambient ≃ᵃⁱ[ℝ] Ambient)
    (hplacement : ∀ p ∈ e.source, G (e p) = A (X p))
    {p : AddCircle T × Ioo (0 : ℝ) w} (hp : p ∈ e.source) :
    nativeTorusChartCurvature G (e p) =
      gaussianCurvature (inducedMetric (nativeProductPlaneCoordinateMap X p))
        ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm (chartAt (ModelProd ℝ ℝ) p p)) := by
  let cp := bandNativeCurvatureCoordChart p
  let ct := torusNativeCurvatureCoordChart (e p)
  let k : OpenPartialHomeomorph Coord Coord := (cp.symm.trans e).trans ct
  let S : Coord → Ambient := G ∘ ct.symm
  let U : Set Coord := ct.target
  let V : Set Coord := k.source
  let z : Coord := cp p
  have hcp := bandNativeCurvatureCoordChart_smooth p
  have hct := torusNativeCurvatureCoordChart_smooth (e p)
  have hdcp := bandNativeCurvatureCoordChart_mdifferentiable p
  have hdct := torusNativeCurvatureCoordChart_mdifferentiable (e p)
  have hde : e.MDifferentiable nativeProductModel nativeProductModel :=
    ⟨he.mdifferentiableOn (by simp), hi.mdifferentiableOn (by simp)⟩
  have hdk : k.MDifferentiable 𝓘(ℝ, Coord) 𝓘(ℝ, Coord) :=
    (hdcp.symm.trans hde).trans hdct
  have hS : ContDiffOn ℝ ∞ S U :=
    (hG.comp_contMDiffOn hct.2).contDiffOn
  have hk : ContDiffOn ℝ ∞ (k : Coord → Coord) V := by
    have hs := hct.1.comp' (he.comp' hcp.2)
    simpa [k, cp, ct, V, Function.comp_def] using hs.contDiffOn
  have hcpSource : p ∈ cp.source := by
    simpa [cp, bandNativeCurvatureCoordChart] using mem_chart_source (ModelProd ℝ ℝ) p
  have hctSource : e p ∈ ct.source := by
    simpa [ct, torusNativeCurvatureCoordChart] using mem_chart_source (ModelProd ℝ ℝ) (e p)
  have hz : z ∈ V := by
    change (z ∈ cp.target ∧ cp.symm z ∈ e.source) ∧ e (cp.symm z) ∈ ct.source
    refine ⟨⟨cp.map_source hcpSource, ?_⟩, ?_⟩
    · simpa only [z, cp.left_inv hcpSource] using hp
    · simpa only [z, cp.left_inv hcpSource] using hctSource
  have hmap : MapsTo (k : Coord → Coord) V U := by
    intro q hq
    change (q ∈ cp.target ∧ cp.symm q ∈ e.source) ∧ e (cp.symm q) ∈ ct.source at hq
    exact ct.map_source hq.2
  have hSinj : ∀ q ∈ U, Function.Injective (fderiv ℝ S q) := by
    intro q hq
    have hdG := (hG (ct.symm q)).mdifferentiableAt (by simp)
    have hdInv := hdct.mdifferentiableAt_symm hq
    have hd := mfderiv_comp q hdG hdInv
    have hj : Function.Injective
        ((mfderiv nativeProductModel 𝓘(ℝ, Ambient) G (ct.symm q)).comp
          (mfderiv 𝓘(ℝ, Coord) nativeProductModel ct.symm q)) :=
      (himm (ct.symm q)).comp (hdct.symm.mfderiv_injective hq)
    rw [← hd] at hj
    exact (band_coord_mfderiv_injective_iff S q).mp hj
  have hkinj : ∀ q ∈ V, Function.Injective (fderiv ℝ (k : Coord → Coord) q) := by
    intro q hq
    exact (band_coord_mfderiv_injective_iff (k : Coord → Coord) q).mp (hdk.mfderiv_injective hq)
  have hg := inducedMetric_smoothPositiveOn hS ct.open_target hSinj
  have hIsom := inducedMetric_isometricOn hS
  obtain ⟨n, hnUnit, hnTangents⟩ := exists_unit_normal_of_independent_tangents
    (fun i => coordPartial i S (k z)) (isometric_tangents_independent hg hIsom (hmap hz))
  have hn : IsUnitNormalAt S n (k z) := by
    refine ⟨hnUnit, ?_⟩
    intro v
    rw [fderiv_two_coordinates, inner_add_left, real_inner_smul_left,
      real_inner_smul_left, hnTangents 0, hnTangents 1]
    simp
  have hcov := protectedTorus_curvature_reparam ct.open_target k.open_source hS hk
    hmap hSinj hkinj hz hn
  have hvalue : k z = ct (e p) := by
    change ct (e (cp.symm (cp p))) = ct (e p)
    rw [cp.left_inv hcpSource]
  have hgerm : nativeProductCoordinateMap (A ∘ X) p =ᶠ[𝓝 z] (S ∘ k) := by
    filter_upwards [k.open_source.mem_nhds hz] with q hq
    change (q ∈ cp.target ∧ cp.symm q ∈ e.source) ∧ e (cp.symm q) ∈ ct.source at hq
    change A (X (cp.symm q)) = G (ct.symm (ct (e (cp.symm q))))
    rw [ct.left_inv hq.2, hplacement (cp.symm q) hq.1.2]
  have hlocal := gaussianCurvature_eq_of_eventuallyEq (inducedMetric_eventuallyEq hgerm)
  have hmetric : inducedMetric (nativeProductCoordinateMap (A ∘ X) p) =
      inducedMetric (nativeProductPlaneCoordinateMap X p) := by
    rw [nativeProductPlane_coordinateMap_eq]
    exact torusRigid_coord_inducedMetric A (nativeProductCoordinateMap X p)
  change gaussianCurvature (inducedMetric S) (ct (e p)) =
    gaussianCurvature (inducedMetric (nativeProductPlaneCoordinateMap X p)) z
  rw [hmetric] at hlocal
  exact (hlocal.trans (hcov.trans (congrArg
    (fun q => gaussianCurvature (inducedMetric S) q) hvalue))).symm

/-- The explicit band-center form is exactly the retained threshold's form. -/
theorem nativeTorusChartCurvature_of_band_placement_at_height
    (X : AddCircle T × Ioo (0 : ℝ) w → Ambient)
    (G : NonrigidTorusSource → Ambient)
    (hG : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ G)
    (himm : ∀ q, Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient) G q))
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) NonrigidTorusSource)
    (he : ContMDiffOn nativeProductModel nativeProductModel ∞ e e.source)
    (hi : ContMDiffOn nativeProductModel nativeProductModel ∞ e.symm e.target)
    (A : Ambient ≃ᵃⁱ[ℝ] Ambient)
    (hplacement : ∀ p ∈ e.source, G (e p) = A (X p))
    {p : AddCircle T × Ioo (0 : ℝ) w} (hp : p ∈ e.source) :
    nativeTorusChartCurvature G (e p) =
      gaussianCurvature (inducedMetric (nativeProductPlaneCoordinateMap X p))
        (![0, (p.2 : ℝ)] : Coord) := by
  rw [← nativeProductPlane_band_chart_center p]
  exact nativeTorusChartCurvature_of_band_placement X G hG himm e he hi A hplacement hp

/-- Both literal branch placements use the same e and affine placement. -/
theorem protectedTorus_bending_branch_placement
    (X Y : AddCircle T × Ioo (0 : ℝ) w → Ambient)
    (F : NonrigidTorusSource → Ambient)
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) NonrigidTorusSource)
    (A : Ambient ≃ᵃⁱ[ℝ] Ambient)
    (hplacement : ∀ p ∈ e.source, F (e p) = A (X p))
    (a : ℝ) {p : AddCircle T × Ioo (0 : ℝ) w} (hp : p ∈ e.source) :
    (F + a • protectedTorusBendingField e A Y) (e p) = A ((X + a • Y) p) := by
  simp only [Pi.add_apply, Pi.smul_apply]
  rw [hplacement p hp, protectedTorusBendingField_source e A Y hp]
  have h := A.map_vadd (X p) (a • Y p)
  simpa only [vadd_eq_add, map_smul, add_comm] using h.symm

/-- The retained actual band threshold gives actual torus curvature stability
on the SAME compact support image. This theorem concerns affine-isometry
placement; it makes no inference for contragredient marked branches. -/
theorem protectedTorus_ruled_bending_curvature_threshold
    (d : PeriodicRuledFrame T) (hw : 0 < w)
    {Y : AddCircle T × Ioo (0 : ℝ) w → Ambient}
    (hY : IsBandBending (d.bandMap (b := w)) Y)
    (hcompact : HasCompactSupport Y) (hnonzero : ∃ p, Y p ≠ 0)
    (F : NonrigidTorusSource → Ambient)
    (hF : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ F)
    (hinj : ∀ q, Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient) F q))
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) NonrigidTorusSource)
    (hsupport : tsupport Y ⊆ e.source)
    (he : ContMDiffOn nativeProductModel nativeProductModel ∞ e e.source)
    (hi : ContMDiffOn nativeProductModel nativeProductModel ∞ e.symm e.target)
    (A : Ambient ≃ᵃⁱ[ℝ] Ambient)
    (hplacement : ∀ p ∈ e.source, F (e p) = A ((d.bandMap (b := w)) p)) :
    ∃ δ > 0, ∀ a : ℝ, |a| < δ → ∀ q ∈ e '' tsupport Y,
      nativeTorusChartCurvature F q < 0 ∧
      nativeTorusChartCurvature (F + a • protectedTorusBendingField e A Y) q < 0 ∧
      nativeTorusChartCurvature (F - a • protectedTorusBendingField e A Y) q < 0 := by
  let Z := protectedTorusBendingField e A Y
  have hZ : nativeProductIsBending F Z := protectedTorus_isNativeBending
    d.bandMap_contMDiff hY hcompact hnonzero e hsupport hi A F hplacement
  obtain ⟨δ, hδ, hbound⟩ :=
    periodicRuledFrame_native_compact_bending_curvature_threshold d hw hY hcompact
  refine ⟨δ, hδ, ?_⟩
  intro a ha q hq
  obtain ⟨p, hp, rfl⟩ := hq
  have hps := hsupport hp
  have hbase := nativeTorusChartCurvature_of_band_placement_at_height
    d.bandMap F hF hinj e he hi A hplacement hps
  have hplus := nativeTorusChartCurvature_of_band_placement_at_height
    (d.bandMap + a • Y) (F + a • Z) (hF.add (nativeProduct_bending_const_smul hF hZ a).1)
    (nativeProduct_bending_branch_immersion hF hZ a hinj) e he hi A
    (fun p hp => protectedTorus_bending_branch_placement d.bandMap Y F e A hplacement a hp) hps
  have hminus := nativeTorusChartCurvature_of_band_placement_at_height
    (d.bandMap + (-a) • Y) (F + (-a) • Z) (hF.add (nativeProduct_bending_const_smul hF hZ (-a)).1)
    (nativeProduct_bending_branch_immersion hF hZ (-a) hinj) e he hi A
    (fun p hp => protectedTorus_bending_branch_placement d.bandMap Y F e A hplacement (-a) hp) hps
  refine ⟨hbase.symm ▸ nativeProductPlane_band_curvature_neg d p,
    hplus.symm ▸ hbound a ha p, ?_⟩
  have hm : nativeTorusChartCurvature (F + (-a) • Z) (e p) < 0 :=
    hminus.symm ▸ hbound (-a) (by simpa only [abs_neg] using ha) p
  simpa only [neg_smul, sub_eq_add_neg] using hm

end
end TightVer401