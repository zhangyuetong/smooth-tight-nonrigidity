import TightVer401.IdentityBandPlanarSupportHorizontal
import TightVer401.IdentityBandPlanarSupportBending
import TightVer401.NativeProductPlaneGaussCoordinates
import TightVer401.CorrugatedIdentityBendingBand

/-! The actual protected native band represented by one Cartesian potential.
The output records constructed maps and the original retained bending. -/
open scoped Manifold
namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.SmoothLocal.Geometry
open scoped ContDiff Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- Constructed global support and gradient coordinates for this actual band.
All smooth maps back to the band use its original native product atlas. -/
def IdentityBandPlanarSupportAnnulus {T : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T) (w : ℝ) : Prop :=
  ∃ G : Coord → ℝ, ∃ e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) Coord,
    ∃ h : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) Coord,
    ∃ g : OpenPartialHomeomorph Coord Coord,
    e.source = univ ∧ e.target = range (identityBandPlanarSource (d.bandSphereGauss (b := w))) ∧
    (e : _ → Coord) = identityBandPlanarSource (d.bandSphereGauss (b := w)) ∧
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Coord) ∞ e ∧
    ContMDiffOn 𝓘(ℝ, Coord) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞ e.symm e.target ∧
    h.source = univ ∧ h.target = range (fun p : AddCircle T × Ioo (0 : ℝ) w => identityBandPlanarHorizontalCLM (d.bandMap p)) ∧
    (h : _ → Coord) = (fun p => identityBandPlanarHorizontalCLM (d.bandMap p)) ∧
    ContMDiffOn 𝓘(ℝ, Coord) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞ h.symm h.target ∧
    ContDiffOn ℝ ∞ G e.target ∧ (∀ p, planarSupportMap G (e p) = d.bandMap p) ∧
    g.source = e.target ∧ g.target = h.target ∧ EqOn g (planarGradient G) g.source ∧
    ContDiffOn ℝ ∞ g g.source ∧ ContDiffOn ℝ ∞ g.symm g.target ∧
    ∃ he : e.source = univ,
      ∃ hbalance : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0,
      ∃ δ > 0, δ < w ∧
      ∃ hinside : ∀ v ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
        principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 v t ∈ Ioo 0 w,
      ∃ Y : AddCircle T × Ioo (0 : ℝ) w → Ambient,
        IsBandBending d.bandMap Y ∧ HasCompactSupport Y ∧ (∃ p, Y p ≠ 0) ∧
        IsInfinitesimalBendingOn (planarSupportMap G) (Y ∘ e.symm) e.target ∧
        (let Z := identityBandPlanarRegionField e he Y
         HasCompactSupport Z ∧ (∃ q, Z q ≠ 0) ∧
           (Subtype.val : e.target → Coord) '' tsupport Z = e '' tsupport Y ∧
           (Subtype.val : e.target → Coord) '' tsupport Z ⊆
             range (e ∘ identityFlowBandInclusion d hbalance 0 hinside))

section
variable {T w : ℝ} [Fact (0 < T)]
local instance identityBandPlanarSupportBandCoordChartedSpace :
    ChartedSpace Coord (AddCircle T × Ioo (0 : ℝ) w) := nativeProductGaussChartedSpace _
local instance identityBandPlanarSupportBandCoordManifold :
    IsManifold 𝓘(ℝ, Coord) ∞ (AddCircle T × Ioo (0 : ℝ) w) := nativeProductGauss_isManifold _
local instance identityBandPlanarSupportBandSphereDimension :
    Fact (Module.finrank ℝ Ambient = 2 + 1) := ⟨by simp [Ambient]⟩

/-- Actual geometric premises retained by the corrected-band construction
suffice; no global inverse, potential, annulus or bending transport is input. -/
theorem identityBandPlanarSupport_actual_band (d : PeriodicRuledFrame T)
    (hw : 0 < w) (hNi : Function.Injective (d.bandSphereGauss (b := w)))
    (hnorth : ∀ p : AddCircle T × Ioo (0 : ℝ) w, 0 < d.bandGaussMap p 2)
    (hproj : Topology.IsEmbedding (corrugatedAmbientHorizontalCLM ∘ d.bandMap (b := w)))
    (hprojs : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℂ) ∞
      (corrugatedAmbientHorizontalCLM ∘ d.bandMap (b := w)))
    (hproji : ∀ p : AddCircle T × Ioo (0 : ℝ) w,
      Function.Injective (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℂ)
        (corrugatedAmbientHorizontalCLM ∘ d.bandMap (b := w)) p))
    (hprotected : ProtectedIdentityBendingSubband d w) : IdentityBandPlanarSupportAnnulus d w := by
  let M := AddCircle T × Ioo (0 : ℝ) w
  letI : Nonempty M := ⟨(0, ⟨w / 2, by constructor <;> linarith⟩)⟩
  have hN : ContMDiff 𝓘(ℝ, Coord) (𝓡 2) ∞ (d.bandSphereGauss (b := w)) :=
    (periodicRuledFrame_bandSphereGauss_contMDiff d).comp (nativeProductGauss_inverse_contMDiff M)
  have hX : ContMDiff 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) ∞ (d.bandMap (b := w)) :=
    d.bandMap_contMDiff.comp (nativeProductGauss_inverse_contMDiff M)
  have hiN (p : M) : Function.Injective (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient)
      (fun x => (d.bandSphereGauss x).val) p) := by
    change Function.Injective (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) d.bandGaussMap p)
    rw [nativeProductGauss_mfderiv M
      ((periodicRuledFrame_bandGaussMap_contMDiff d p).mdifferentiableAt (by simp))]
    exact (periodicRuledFrame_bandGaussMap_differential_injective d p).comp
      nativeProductGaussCoordinateEquiv.symm.injective
  have horth (p : M) (v : TangentSpace 𝓘(ℝ, Coord) p) :
      @inner ℝ Ambient _ (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) d.bandMap p v)
        (d.bandSphereGauss p).val = 0 := by
    rw [nativeProductGauss_mfderiv M ((d.bandMap_contMDiff p).mdifferentiableAt (by simp))]
    exact periodicRuledFrame_bandGaussMap_orthogonal d p (nativeProductGaussCoordinateEquiv.symm v)
  have hPC := hprojs.comp (nativeProductGauss_inverse_contMDiff M)
  have hiPC (p : M) : Function.Injective (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, ℂ)
      (corrugatedAmbientHorizontalCLM ∘ d.bandMap) p) := by
    rw [nativeProductGauss_mfderiv M ((hprojs p).mdifferentiableAt (by simp))]
    exact (hproji p).comp nativeProductGaussCoordinateEquiv.symm.injective
  obtain ⟨G, e, h, g, heS, heT, heF, heD, heI, hhS, hhT, hhF, hhI, hG, hrec,
    hgS, hgT, hgF, hgD, hgI⟩ := identityBandPlanarSupport_exists_source_gradient_images
      hN hiN hNi hnorth hX horth
      (identityBandPlanarHorizontalCLM_differential_injective hPC hiPC)
      (identityBandPlanarHorizontalCLM_injective hproj.injective)
  obtain ⟨hbalance, δ, hδ, hδw, _hflow, _hflowi, _hflowe, hinside, Y,
    hY, hcompact, hnonzero, hsupport, _hsurface, _hYflow, _hleaves⟩ := hprotected
  have hYC : ContMDiff 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) ∞ Y :=
    hY.1.comp (nativeProductGauss_inverse_contMDiff M)
  have hstrain (p : M) (v z : TangentSpace 𝓘(ℝ, Coord) p) :
      @inner ℝ Ambient _ (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) d.bandMap p v)
        (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) Y p z) +
      @inner ℝ Ambient _ (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) Y p v)
        (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) d.bandMap p z) = 0 := by
    rw [nativeProductGauss_mfderiv M ((d.bandMap_contMDiff p).mdifferentiableAt (by simp)),
      nativeProductGauss_mfderiv M ((hY.1 p).mdifferentiableAt (by simp))]
    exact hY.2 p (nativeProductGaussCoordinateEquiv.symm v) (nativeProductGaussCoordinateEquiv.symm z)
  refine ⟨G, e, h, g, heS, heT, heF,
    heD.comp (nativeProductGauss_identity_contMDiff M),
    (nativeProductGauss_inverse_contMDiff M).comp_contMDiffOn heI,
    hhS, hhT, hhF, (nativeProductGauss_inverse_contMDiff M).comp_contMDiffOn hhI,
    hG, hrec, hgS, hgT, hgF, hgD, hgI, heS, hbalance, δ, hδ, hδw, hinside, Y,
    hY, hcompact, hnonzero, identityBandPlanarSupport_bending_transfer hX hYC hstrain e heS heI hrec,
    identityBandPlanarRegionField_hasCompactSupport e heS hcompact,
    identityBandPlanarRegionField_nonzero e heS hnonzero,
    identityBandPlanarRegionField_tsupport e heS Y,
    identityBandPlanarRegionField_flow_support d hbalance hinside e heS hsupport⟩

end
end
end TightVer401