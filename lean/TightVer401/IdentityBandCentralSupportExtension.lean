import TightVer401.IdentityBandCentralSupportNative
import TightVer401.IdentityBandCentralSupportCollar
import TightVer401.IdentityBandPlanarSupportImage
import TightVer401.IdentityBandPlanarSupportCoordinates

/-! One actual Cartesian support potential on a two-sided annular image,
including the central circle in its smooth domain. -/
open scoped Manifold
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

def identityBandCentralCoordinates {T : ℝ} (d : PeriodicRuledFrame T) (q : Coord) : Coord :=
  gnomonicInverse (d.rawGaussMap q)

def identityBandCentralRawDomain (w : ℝ) : Set Coord := {q | q 1 ∈ Ioo (-w) w}

theorem identityBandCentralRawDomain_isOpen (w : ℝ) : IsOpen (identityBandCentralRawDomain w) :=
  isOpen_Ioo.preimage (continuous_apply 1)

section
variable {T w : ℝ} [Fact (0 < T)]
local instance identityBandCentralSupportExtensionCoordChartedSpace :
    ChartedSpace Coord (AddCircle T × Ioo (-w) w) := nativeProductGaussChartedSpace _
local instance identityBandCentralSupportExtensionCoordManifold :
    IsManifold 𝓘(ℝ, Coord) ∞ (AddCircle T × Ioo (-w) w) := nativeProductGauss_isManifold _
local instance identityBandCentralSupportExtensionSphereDimension :
    Fact (Module.finrank ℝ Ambient = 2 + 1) := ⟨by simp [Ambient]⟩

/-- Both inverse and potential are constructed from actual two-sided geometry.
The same potential reconstructs the raw ruled surface throughout the strip,
so its Hessian is defined at the central seam. -/
theorem identityBandTwoSided_exists_cartesian_support (d : PeriodicRuledFrame T)
    (hw : 0 < w) (hc : IdentityBandTwoSidedCollar d w) :
    ∃ G : Coord → ℝ, ∃ U : Set Coord,
      IsOpen U ∧ U = range (identityBandPlanarSource (identityBandTwoSidedSphereGauss (w := w) d)) ∧
      ContDiffOn ℝ ∞ G U ∧
      (∀ p : AddCircle T × Ioo (-w) w,
        planarSupportMap G (identityBandPlanarSource (identityBandTwoSidedSphereGauss d) p) =
          identityBandTwoSidedMap d p) ∧
      ContDiffOn ℝ ∞ (identityBandCentralCoordinates d) (identityBandCentralRawDomain w) ∧
      MapsTo (identityBandCentralCoordinates d) (identityBandCentralRawDomain w) U ∧
      EqOn (planarSupportMap G ∘ identityBandCentralCoordinates d) (ruledMap d.γ d.E)
        (identityBandCentralRawDomain w) ∧
      EqOn (planarUnitNormal ∘ identityBandCentralCoordinates d) d.rawGaussMap
        (identityBandCentralRawDomain w) := by
  let M := AddCircle T × Ioo (-w) w
  letI : Nonempty M := ⟨(0, ⟨0, by constructor <;> linarith⟩)⟩
  obtain ⟨hXn, hNn, hgeom⟩ := identityBandTwoSided_native_geometry (w := w) d
  have hX : ContMDiff 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) ∞ (identityBandTwoSidedMap (w := w) d) := by
    simpa only [Function.comp_id] using hXn.comp (nativeProductGauss_inverse_contMDiff M)
  have hN : ContMDiff 𝓘(ℝ, Coord) (𝓡 2) ∞ (identityBandTwoSidedSphereGauss (w := w) d) := by
    simpa only [Function.comp_id] using hNn.comp (nativeProductGauss_inverse_contMDiff M)
  have hNgauss : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞
      (identityBandTwoSidedGaussMap (w := w) d) :=
    (periodicRuledFrame_fullGaussMap_contMDiff d).comp (identityBandTwoSidedInclusion_contMDiff T w)
  have hiN (p : M) : Function.Injective (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient)
      (fun x => (identityBandTwoSidedSphereGauss d x).val) p) := by
    change Function.Injective (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) (identityBandTwoSidedGaussMap d) p)
    rw [nativeProductGauss_mfderiv M
      ((hNgauss p).mdifferentiableAt (by simp))]
    exact (hgeom p).2.1.comp nativeProductGaussCoordinateEquiv.symm.injective
  have hmem (p : M) : identityBandTwoSidedInclusion T w p ∈
      (univ ×ˢ Icc (-w) w : Set (AddCircle T × ℝ)) :=
    ⟨mem_univ _, p.2.property.1.le, p.2.property.2.le⟩
  have hNi : Function.Injective (identityBandTwoSidedSphereGauss (w := w) d) := by
    intro p q hpq
    have hv := congrArg Subtype.val hpq
    have he := hc.1 (hmem p) (hmem q) hv
    change (p.1, (p.2 : ℝ)) = (q.1, (q.2 : ℝ)) at he
    have hfirst : p.1 = q.1 := congrArg (fun z : AddCircle T × ℝ => z.1) he
    have hsecond : (p.2 : ℝ) = (q.2 : ℝ) := congrArg (fun z : AddCircle T × ℝ => z.2) he
    exact Prod.ext hfirst (Subtype.ext hsecond)
  have hnorth (p : M) : 0 < (identityBandTwoSidedSphereGauss d p).val 2 := hc.2.1 _ (hmem p)
  have horth (p : M) (v : TangentSpace 𝓘(ℝ, Coord) p) :
      @inner ℝ Ambient _ (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) (identityBandTwoSidedMap d) p v)
        (identityBandTwoSidedSphereGauss d p).val = 0 := by
    rw [nativeProductGauss_mfderiv M ((hXn p).mdifferentiableAt (by simp))]
    exact (hgeom p).2.2 (nativeProductGaussCoordinateEquiv.symm v)
  obtain ⟨G, hG, hrec, _hfirst⟩ := identityBandPlanarSupport_exists_potential hN hiN hNi hnorth hX horth
  let U := identityBandPlanarSourceDomain (identityBandTwoSidedSphereGauss (w := w) d)
  have hU : IsOpen U := identityBandPlanarSourceDomain_isOpen hN hiN
  have hUr : U = range (identityBandPlanarSource (identityBandTwoSidedSphereGauss (w := w) d)) :=
    identityBandPlanarSourceDomain_eq_range hnorth
  have hpdata (q : Coord) (hq : q ∈ identityBandCentralRawDomain w) :
      ∃ p : M, identityBandPlanarSource (identityBandTwoSidedSphereGauss d) p =
        identityBandCentralCoordinates d q ∧ identityBandTwoSidedMap d p = ruledMap d.γ d.E q ∧
        (identityBandTwoSidedSphereGauss d p).val = d.rawGaussMap q := by
    let p : M := (periodProjection T (q 0), ⟨q 1, hq⟩)
    refine ⟨p, ?_, ?_, ?_⟩ <;>
      simp only [p, identityBandPlanarSource, identityBandCentralCoordinates,
        identityBandTwoSidedSphereGauss, identityBandTwoSidedGaussMap,
        identityBandTwoSidedMap, identityBandTwoSidedInclusion,
        PeriodicRuledFrame.fullBandMap, PeriodicRuledFrame.fullGaussMap,
        PeriodicRuledFrame.rawGaussMap, ruledMap, Prod.map_apply,
        id_eq, periodicLift_coe]
  have hnraw (q : Coord) (hq : q ∈ identityBandCentralRawDomain w) :
      0 < d.rawGaussMap q 2 := by
    obtain ⟨p, _, _, hnp⟩ := hpdata q hq
    rw [← hnp]
    exact hnorth p
  have hP : ContDiffOn ℝ ∞ (identityBandCentralCoordinates d) (identityBandCentralRawDomain w) := by
    apply contDiffOn_pi.mpr
    intro i
    have hd (j : Fin 3) : ContDiff ℝ ∞ (fun q => d.rawGaussMap q j) :=
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j).contDiff.comp
        (periodicRuledFrame_rawGaussMap_contDiff d)
    have hcdiv := (hd (Fin.castSucc i)).contDiffOn.div (hd 2).contDiffOn
      (fun q hq => (hnraw q hq).ne')
    fin_cases i <;> exact hcdiv
  refine ⟨G, U, hU, hUr, hG, hrec, hP, ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨p, hp, _, _⟩ := hpdata q hq
    rw [hUr, ← hp]
    exact mem_range_self p
  · intro q hq
    obtain ⟨p, hp, hxp, _⟩ := hpdata q hq
    change planarSupportMap G (identityBandCentralCoordinates d q) = ruledMap d.γ d.E q
    rw [← hp, hrec p, hxp]
  · intro q hq
    obtain ⟨p, _, _, hnp⟩ := hpdata q hq
    change planarUnitNormal (gnomonicInverse (d.rawGaussMap q)) = d.rawGaussMap q
    apply identityBand_gnomonic_unitNormal
    · rw [← hnp]
      exact periodicRuledFrame_fullGaussMap_unit d (identityBandTwoSidedInclusion T w p)
    · exact hnraw q hq

end
end
end TightVer401