import TightVer401.TorusNativeCurvatureReparamConnection
import TightVer401.TorusMetricBranchingPositive
import TightVer401.SurfaceMetric
import TightVer401.GaussBridge
import Mathlib.Analysis.InnerProductSpace.Dual

/-! No open planar patch from actual dense nonzero intrinsic curvature.
Local planar flatness is proved using actual constant height derivatives and
OpenAI's Gauss equation. Density of the constructed torus is an application
obligation, not a granted construction or curvature package. -/
open Manifold
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false

local instance : IsManifold nativeProductModel ∞ NonrigidTorusSource :=
  nonrigidTorusSource_isManifold

/-- A smooth regular actual Coord patch in an affine plane has zero actual
intrinsic Gaussian curvature. Its normal is constructed from the Riesz vector
of the actual nonzero functional, and its second form is derived to be zero. -/
theorem coord_curvature_zero_of_open_plane
    {X : Coord → Ambient} {U : Set Coord}
    (hX : ContDiffOn ℝ ∞ X U) (hU : IsOpen U)
    (hinj : ∀ q ∈ U, Function.Injective (fderiv ℝ X q))
    (ell : Ambient →L[ℝ] ℝ) (hell : ell ≠ 0) (c : ℝ)
    (hplane : ∀ q ∈ U, ell (X q) = c)
    {p : Coord} (hp : p ∈ U) :
    gaussianCurvature (inducedMetric X) p = 0 := by
  let v := (InnerProductSpace.toDual ℝ Ambient).symm ell
  have hv : v ≠ 0 := by
    intro hz
    apply hell
    have he := (InnerProductSpace.toDual ℝ Ambient).apply_symm_apply ell
    change (InnerProductSpace.toDual ℝ Ambient) v = ell at he
    rw [hz, map_zero] at he
    exact he.symm
  have hpair (w : Ambient) : inner ℝ v w = ell w :=
    InnerProductSpace.toDual_symm_apply
  let n : Ambient := ‖v‖⁻¹ • v
  have hnunit : inner ℝ n n = 1 := by
    have hnorm : ‖n‖ = 1 := norm_smul_inv_norm (𝕜 := ℝ) hv
    rw [real_inner_self_eq_norm_sq, hnorm, one_pow]
  have hheight : height X n =ᶠ[𝓝 p] (fun _ : Coord => ‖v‖⁻¹ * c) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    change inner ℝ (X q) (‖v‖⁻¹ • v) = ‖v‖⁻¹ * c
    have hcomm : inner ℝ (X q) v = inner ℝ v (X q) := real_inner_comm v (X q)
    rw [real_inner_smul_right, hcomm, hpair, hplane q hq]
  have hfirst (j : Fin 2) : coordPartial j (height X n) =ᶠ[𝓝 p]
      (fun _ : Coord => (0 : ℝ)) := by
    filter_upwards [hheight.eventuallyEq_nhds] with q hq
    have hconst : fderiv ℝ (fun _ : Coord => ‖v‖⁻¹ * c) q = 0 :=
      (hasFDerivAt_const (‖v‖⁻¹ * c) q).fderiv
    change fderiv ℝ (height X n) q (Pi.single j 1) = 0
    exact congrArg (fun L : Coord →L[ℝ] ℝ => L (Pi.single j 1))
      (hq.fderiv_eq.trans hconst)
  have hnormal : IsUnitNormalAt X n p := by
    refine ⟨hnunit, ?_⟩
    intro w
    have hz := congrArg (fun L : Coord →L[ℝ] ℝ => L w) hheight.fderiv_eq
    have hdX : DifferentiableAt ℝ X p :=
      ((hX p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
    change fderiv ℝ (fun q => inner ℝ (X q) n) p w =
      fderiv ℝ (fun _ : Coord => ‖v‖⁻¹ * c) p w at hz
    rw [fderiv_inner_apply ℝ hdX (differentiableAt_const (c := n))] at hz
    simpa using hz
  have hsecond : secondFundamental X n p = 0 := by
    ext i j
    change inner ℝ (coordPartial i (coordPartial j X) p) n = 0
    rw [← second_partial_height hX hU hp n i j]
    have hconst : fderiv ℝ (fun _ : Coord => (0 : ℝ)) p = 0 :=
      (hasFDerivAt_const (0 : ℝ) p).fderiv
    change fderiv ℝ (coordPartial j (height X n)) p (Pi.single i 1) = 0
    exact congrArg (fun L : Coord →L[ℝ] ℝ => L (Pi.single i 1))
      ((hfirst j).fderiv_eq.trans hconst)
  rw [curvature_eq_second_form_det_div_metric_det
    (inducedMetric_smoothPositiveOn hX hU hinj)
    (inducedMetric_isometricOn hX) hU hp hnormal, hsecond]
  simp

private theorem noPlanar_coord_mfderiv_injective_iff
    (f : Coord → Ambient) (q : Coord) :
    Function.Injective (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) f q) ↔
      Function.Injective (fderiv ℝ f q) := by
  rw [mfderiv_eq_fderiv]
  rfl

/-- A native smooth immersed patch in an actual affine plane has zero SAME
preferred-chart intrinsic curvature, on the actual native torus source. -/
theorem nativeTorusChartCurvature_zero_of_open_plane
    {X : NonrigidTorusSource → Ambient}
    (hX : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ X)
    (hinj : ∀ q, Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient) X q))
    {U : Set NonrigidTorusSource} (hU : IsOpen U)
    (ell : Ambient →L[ℝ] ℝ) (hell : ell ≠ 0) (c : ℝ)
    (hplane : ∀ q ∈ U, ell (X q) = c)
    {p : NonrigidTorusSource} (hp : p ∈ U) :
    nativeTorusChartCurvature X p = 0 := by
  let cp := torusNativeCurvatureCoordChart p
  let F : Coord → Ambient := X ∘ cp.symm
  let V : Set Coord := cp.target ∩ cp.symm ⁻¹' U
  have hs := torusNativeCurvatureCoordChart_smooth p
  have hdcp := torusNativeCurvatureCoordChart_mdifferentiable p
  have hF : ContDiffOn ℝ ∞ F cp.target :=
    (hX.comp_contMDiffOn hs.2).contDiffOn
  have hV : IsOpen V := cp.isOpen_inter_preimage_symm hU
  have hsource : p ∈ cp.source := by
    simpa [cp, torusNativeCurvatureCoordChart] using mem_chart_source (ModelProd ℝ ℝ) p
  have hc : cp p ∈ V := by
    exact ⟨cp.map_source hsource, by simpa only [mem_preimage, cp.left_inv hsource] using hp⟩
  have hFinj : ∀ q ∈ V, Function.Injective (fderiv ℝ F q) := by
    intro q hq
    have hdX := (hX (cp.symm q)).mdifferentiableAt (by simp)
    have hdInv := hdcp.mdifferentiableAt_symm hq.1
    have hd := mfderiv_comp q hdX hdInv
    have hj : Function.Injective
        ((mfderiv nativeProductModel 𝓘(ℝ, Ambient) X (cp.symm q)).comp
          (mfderiv 𝓘(ℝ, Coord) nativeProductModel cp.symm q)) :=
      (hinj (cp.symm q)).comp (hdcp.symm.mfderiv_injective hq.1)
    rw [← hd] at hj
    exact (noPlanar_coord_mfderiv_injective_iff F q).mp hj
  have hplanar : ∀ q ∈ V, ell (F q) = c := by
    intro q hq
    exact hplane _ hq.2
  change gaussianCurvature (inducedMetric F) (cp p) = 0
  exact coord_curvature_zero_of_open_plane (hF.mono inter_subset_left)
    hV hFinj ell hell c hplanar hc

/-- The actual native smooth immersion and a dense actual nonzero-K locus
exclude every nonempty open affine planar patch. Embedding is not required. -/
theorem nativeTorus_hasNoOpenPlanarPatch_of_dense_nonzero_curvature
    {X : NonrigidTorusSource → Ambient}
    (hX : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ X)
    (hinj : ∀ q, Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient) X q))
    (hdense : Dense {p | nativeTorusChartCurvature X p ≠ 0}) :
    HasNoOpenPlanarPatch X := by
  intro U hU hne ell hell c hplane
  obtain ⟨p, hpK, hpU⟩ := hdense.exists_mem_open hU hne
  exact hpK (nativeTorusChartCurvature_zero_of_open_plane
    hX hinj hU ell hell c hplane hpU)

/-- Actual branch negativity on the SAME support and actual curvature equality
off it transfer the baseline dense nonzero locus to that branch. This generic
consumer constructs no baseline/torus density or support-stability estimate. -/
theorem nativeTorus_nonzero_curvature_dense_of_support_negative
    {F G : NonrigidTorusSource → Ambient} (K : Set NonrigidTorusSource)
    (hdense : Dense {p | nativeTorusChartCurvature F p ≠ 0})
    (hnegative : ∀ p ∈ K, nativeTorusChartCurvature G p < 0)
    (hoff : ∀ p ∉ K, nativeTorusChartCurvature G p = nativeTorusChartCurvature F p) :
    Dense {p | nativeTorusChartCurvature G p ≠ 0} := by
  apply hdense.mono
  intro p hp
  by_cases hK : p ∈ K
  · exact (hnegative p hK).ne
  · change nativeTorusChartCurvature G p ≠ 0
    change nativeTorusChartCurvature F p ≠ 0 at hp
    rw [hoff p hK]
    exact hp

end
end TightVer401




