import TightVer401.NativeProductPlaneGaussCoordinates
import TightVer401.NativeProductPlaneForms
import TightVer401.PeriodicRuledNativeGauss
import TightVer401.GaussImageInverse

/-! Actual Gauss inverse and support reconstruction for the native ruled band.

Interface: the actual `bandSphereGauss` is smooth in the transported Plane
atlas, its actual ambient normal differential is injective, and its normal
annihilates the actual surface differential. On an open subset where that
actual Gauss map is injective, the retained checked Gauss-image theorem gives
an open image, a smooth inverse in the Plane atlas, and a smooth spherical
support potential reconstructing `bandMap`. At each band point, injective
neighborhoods and local support reconstruction are derived from differential
regularity, with no injectivity or inverse premise. Global Gauss injectivity
of a protected annulus remains a separate construction input.

The checked inverse API uses Coord charts. Its hypotheses are discharged
through the explicit Coord adapter, not a definitional identification with
Plane or ModelProd. All chart structures are local opt-in instances.
-/
open Manifold
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace TightVer401
noncomputable section
open Set Filter OAI.ClosedSurfaceR4 OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false

section
variable {L b : ℝ} [Fact (0 < L)]
local instance nativeProductPlaneGaussBandChartedSpace :
    ChartedSpace Plane (AddCircle L × Ioo (0 : ℝ) b) := nativeProductPlaneChartedSpace _
local instance nativeProductPlaneGaussBandCoordChartedSpace :
    ChartedSpace Coord (AddCircle L × Ioo (0 : ℝ) b) := nativeProductGaussChartedSpace _
local instance nativeProductPlaneGaussBandCoordManifold :
    IsManifold 𝓘(ℝ, Coord) ∞ (AddCircle L × Ioo (0 : ℝ) b) := nativeProductGauss_isManifold _
local instance nativeProductPlaneGaussAmbientDimension : Fact (Module.finrank ℝ Ambient = 2 + 1) :=
  ⟨by simp [Ambient]⟩

/-- The actual sphere Gauss map is smooth in the transported Plane atlas. -/
theorem nativeProductPlane_bandSphereGauss_contMDiff (d : PeriodicRuledFrame L) :
    ContMDiff planeModel (𝓡 2) ∞ (d.bandSphereGauss (b := b)) :=
  (periodicRuledFrame_bandSphereGauss_contMDiff d).comp
    (nativeProductPlane_inverse_contMDiff _)

/-- The actual normal differential remains injective in the Plane tangent model. -/
theorem nativeProductPlane_bandGaussMap_differential_injective (d : PeriodicRuledFrame L)
    (p : AddCircle L × Ioo (0 : ℝ) b) :
    Function.Injective (surfaceDifferential d.bandGaussMap p) :=
  (nativeProductPlane_immersion_iff
    ((periodicRuledFrame_bandGaussMap_contMDiff d p).mdifferentiableAt (by simp))).mpr
      (periodicRuledFrame_bandGaussMap_differential_injective d p)

/-- The genuine normal annihilates the transported actual surface differential. -/
theorem nativeProductPlane_bandGaussMap_orthogonal (d : PeriodicRuledFrame L)
    (p : AddCircle L × Ioo (0 : ℝ) b) (v : TangentSpace planeModel p) :
    inner ℝ (surfaceDifferential d.bandMap p v) (d.bandGaussMap p) = 0 := by
  obtain ⟨w, rfl⟩ := nativeProductPlaneEquiv.surjective v
  rw [nativeProductPlane_mfderiv_apply ((d.bandMap_contMDiff p).mdifferentiableAt (by simp))]
  exact periodicRuledFrame_bandGaussMap_orthogonal d p w

private theorem nativeProductPlane_bandSphereGauss_coord_smooth (d : PeriodicRuledFrame L) :
    ContMDiff 𝓘(ℝ, Coord) (𝓡 2) ∞ (d.bandSphereGauss (b := b)) :=
  (periodicRuledFrame_bandSphereGauss_contMDiff d).comp
    (nativeProductGauss_inverse_contMDiff _)

private theorem nativeProductPlane_bandGauss_coord_regular (d : PeriodicRuledFrame L)
    (p : AddCircle L × Ioo (0 : ℝ) b) :
    Function.Injective (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient)
      (fun x => (d.bandSphereGauss x).val) p) := by
  change Function.Injective (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) d.bandGaussMap p)
  rw [nativeProductGauss_mfderiv _
    ((periodicRuledFrame_bandGaussMap_contMDiff d p).mdifferentiableAt (by simp))]
  exact (periodicRuledFrame_bandGaussMap_differential_injective d p).comp
    nativeProductGaussCoordinateEquiv.symm.injective

private theorem nativeProductPlane_bandMap_coord_smooth (d : PeriodicRuledFrame L) :
    ContMDiff 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) ∞ (d.bandMap (b := b)) :=
  d.bandMap_contMDiff.comp (nativeProductGauss_inverse_contMDiff _)

private theorem nativeProductPlane_band_coord_normal (d : PeriodicRuledFrame L)
    (p : AddCircle L × Ioo (0 : ℝ) b) (v : TangentSpace 𝓘(ℝ, Coord) p) :
    @inner ℝ Ambient _ (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) d.bandMap p v : Ambient)
      ((d.bandSphereGauss p).val : Ambient) = 0 := by
  rw [nativeProductGauss_mfderiv _ ((d.bandMap_contMDiff p).mdifferentiableAt (by simp))]
  exact periodicRuledFrame_bandGaussMap_orthogonal d p
    (nativeProductGaussCoordinateEquiv.symm v)

/-- Every point has an actual smooth local Gauss inverse, read in the Plane atlas. -/
theorem nativeProductPlane_band_gauss_local_inverse (d : PeriodicRuledFrame L)
    {U : Set (AddCircle L × Ioo (0 : ℝ) b)} (hU : IsOpen U)
    {p : AddCircle L × Ioo (0 : ℝ) b} (hp : p ∈ U) :
    ∃ e : OpenPartialHomeomorph (AddCircle L × Ioo (0 : ℝ) b) RoundSphere,
      p ∈ e.source ∧ e.source ⊆ U ∧
      (∀ q ∈ e.source, e q = d.bandSphereGauss q) ∧
      ContMDiffOn (𝓡 2) planeModel ∞ e.symm e.target := by
  obtain ⟨e, hep, heU, heN, he⟩ := gaussManifold_exists_smooth_local_inverse
    (nativeProductPlane_bandSphereGauss_coord_smooth d).contMDiffOn hU
    (fun q _ => nativeProductPlane_bandGauss_coord_regular d q) hp
  exact ⟨e, hep, heU, heN,
    (nativeProductGauss_to_plane_contMDiff _).comp_contMDiffOn he⟩

/-- The same actual local inverse is smooth in the original native product model.
Consumers need no Coord atlas in the theorem statement. -/
theorem nativeProductPlane_band_gauss_local_inverse_native (d : PeriodicRuledFrame L)
    {U : Set (AddCircle L × Ioo (0 : ℝ) b)} (hU : IsOpen U)
    {p : AddCircle L × Ioo (0 : ℝ) b} (hp : p ∈ U) :
    ∃ e : OpenPartialHomeomorph (AddCircle L × Ioo (0 : ℝ) b) RoundSphere,
      p ∈ e.source ∧ e.source ⊆ U ∧
      (∀ q ∈ e.source, e q = d.bandSphereGauss q) ∧
      ContMDiffOn (𝓡 2) nativeProductModel ∞ e.symm e.target := by
  obtain ⟨e, hep, heU, heN, he⟩ := nativeProductPlane_band_gauss_local_inverse d hU hp
  exact ⟨e, hep, heU, heN,
    (nativeProductPlane_inverse_contMDiff _).comp_contMDiffOn he⟩

/-- Openness of the actual Gauss image needs only actual differential regularity. -/
theorem nativeProductPlane_band_gauss_image_open (d : PeriodicRuledFrame L)
    {U : Set (AddCircle L × Ioo (0 : ℝ) b)} (hU : IsOpen U) :
    IsOpen (d.bandSphereGauss '' U) :=
  gaussManifold_image_isOpen (nativeProductPlane_bandSphereGauss_coord_smooth d).contMDiffOn hU
    (fun q _ => nativeProductPlane_bandGauss_coord_regular d q)

/-- On a Gauss-injective open subset, derive the actual inverse and its smoothness. -/
theorem nativeProductPlane_band_gauss_image_inverse [Nonempty (AddCircle L × Ioo (0 : ℝ) b)]
    (d : PeriodicRuledFrame L) {U : Set (AddCircle L × Ioo (0 : ℝ) b)}
    (hU : IsOpen U) (hNi : InjOn d.bandSphereGauss U) :
    IsOpen (d.bandSphereGauss '' U) ∧
      ContMDiffOn (𝓡 2) planeModel ∞ (gaussImageInverse d.bandSphereGauss U)
        (d.bandSphereGauss '' U) ∧
      (∀ p ∈ U, gaussImageInverse d.bandSphereGauss U (d.bandSphereGauss p) = p) ∧
      (∀ q ∈ d.bandSphereGauss '' U, gaussImageInverse d.bandSphereGauss U q ∈ U ∧
        d.bandSphereGauss (gaussImageInverse d.bandSphereGauss U q) = q) := by
  obtain ⟨hΩ, hI, hleft, hright⟩ := gaussImage_inverse
    (nativeProductPlane_bandSphereGauss_coord_smooth d).contMDiffOn hU
    (fun q _ => nativeProductPlane_bandGauss_coord_regular d q) hNi
  exact ⟨hΩ, (nativeProductGauss_to_plane_contMDiff _).comp_contMDiffOn hI, hleft, hright⟩

/-- The actual image inverse is smooth back into the original native product atlas. -/
theorem nativeProductPlane_band_gauss_image_inverse_native
    [Nonempty (AddCircle L × Ioo (0 : ℝ) b)]
    (d : PeriodicRuledFrame L) {U : Set (AddCircle L × Ioo (0 : ℝ) b)}
    (hU : IsOpen U) (hNi : InjOn d.bandSphereGauss U) :
    IsOpen (d.bandSphereGauss '' U) ∧
      ContMDiffOn (𝓡 2) nativeProductModel ∞ (gaussImageInverse d.bandSphereGauss U)
        (d.bandSphereGauss '' U) ∧
      (∀ p ∈ U, gaussImageInverse d.bandSphereGauss U (d.bandSphereGauss p) = p) ∧
      (∀ q ∈ d.bandSphereGauss '' U, gaussImageInverse d.bandSphereGauss U q ∈ U ∧
        d.bandSphereGauss (gaussImageInverse d.bandSphereGauss U q) = q) := by
  obtain ⟨hΩ, hI, hleft, hright⟩ := nativeProductPlane_band_gauss_image_inverse d hU hNi
  exact ⟨hΩ, (nativeProductPlane_inverse_contMDiff _).comp_contMDiffOn hI, hleft, hright⟩

/-- Recover a smooth actual spherical support potential on an injective Gauss image. -/
theorem nativeProductPlane_band_gauss_support (d : PeriodicRuledFrame L)
    {U : Set (AddCircle L × Ioo (0 : ℝ) b)} (hU : IsOpen U)
    (hNi : InjOn d.bandSphereGauss U) :
    ∃ H : RoundSphere → ℝ, IsOpen (d.bandSphereGauss '' U) ∧
      ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H (d.bandSphereGauss '' U) ∧
      (∀ p ∈ U, d.bandMap p = globalSphereSupport H (d.bandSphereGauss p)) :=
  gaussImage_support_exists (nativeProductPlane_bandSphereGauss_coord_smooth d).contMDiffOn hU
    (fun q _ => nativeProductPlane_bandGauss_coord_regular d q) hNi
    (nativeProductPlane_bandMap_coord_smooth d).contMDiffOn
    (fun p _ v => nativeProductPlane_band_coord_normal d p v)

/-- Local support reconstruction is derived at every band point without an
assumed inverse, injective neighborhood, or support potential. -/
theorem nativeProductPlane_band_gauss_local_support (d : PeriodicRuledFrame L)
    {U : Set (AddCircle L × Ioo (0 : ℝ) b)} (hU : IsOpen U)
    {p : AddCircle L × Ioo (0 : ℝ) b} (hp : p ∈ U) :
    ∃ V : Set (AddCircle L × Ioo (0 : ℝ) b), p ∈ V ∧ IsOpen V ∧ V ⊆ U ∧
      InjOn d.bandSphereGauss V ∧
      ∃ H : RoundSphere → ℝ, IsOpen (d.bandSphereGauss '' V) ∧
        ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H (d.bandSphereGauss '' V) ∧
        (∀ q ∈ V, d.bandMap q = globalSphereSupport H (d.bandSphereGauss q)) := by
  obtain ⟨e, hep, heU, heN, _⟩ := nativeProductPlane_band_gauss_local_inverse d hU hp
  have hi : InjOn d.bandSphereGauss e.source := by
    intro x hx y hy hxy
    apply e.injOn hx hy
    simpa only [heN x hx, heN y hy] using hxy
  exact ⟨e.source, hep, e.open_source, heU, hi,
    nativeProductPlane_band_gauss_support d e.open_source hi⟩

end
end
end TightVer401
