import TightVer401.PeriodicRuledNativeGauss
import TightVer401.PeriodProjectionDifferential
import TightVer401.NativeProductPlaneGaussCoordinates
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-! Actual full-cylinder and two-sided ruled-band geometry in the native
product model. The committed coordinate equivalence is used only for raw
calculus; no transported atlas instance or global inverse is introduced. -/
open scoped Manifold
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- Actual quotient map on the full real product, with no height restriction. -/
def identityBandNativeCylinderProjection (T : ℝ) : ℝ × ℝ → AddCircle T × ℝ :=
  Prod.map (periodProjection T) id

theorem identityBandNativeCylinderProjection_contMDiff (T : ℝ) [Fact (0 < T)] :
    ContMDiff nativeProductModel nativeProductModel ∞
      (identityBandNativeCylinderProjection T) :=
  (periodProjection_contMDiff T).prodMap contMDiff_id

theorem identityBandNativeCylinderProjection_mfderiv_surjective
    (T : ℝ) [Fact (0 < T)] (p : ℝ × ℝ) :
    Function.Surjective (mfderiv nativeProductModel nativeProductModel
      (identityBandNativeCylinderProjection T) p) := by
  intro v
  obtain ⟨s, hs⟩ := periodProjection_mfderiv_surjective T p.1 v.1
  refine ⟨(s, v.2), ?_⟩
  rw [identityBandNativeCylinderProjection, mfderiv_prodMap
    ((periodProjection_contMDiff T p.1).mdifferentiableAt (by simp)) mdifferentiableAt_id,
    mfderiv_id]
  change (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (periodProjection T) p.1 s, v.2) = v
  rw [hs]
  exact Prod.eta v

private theorem identityBandNative_rawMap_contDiff {T : ℝ} (d : PeriodicRuledFrame T) :
    ContDiff ℝ ∞ (ruledMap d.γ d.E) :=
  (d.smooth_γ.comp (contDiff_apply ℝ ℝ 0)).add
    ((contDiff_apply ℝ ℝ 1).smul (d.smooth_E.comp (contDiff_apply ℝ ℝ 0)))

/-- Actual smooth surface on the full native quotient cylinder. -/
theorem identityBand_fullBandMap_contMDiff {T : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T) :
    ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ d.fullBandMap := by
  have hγ : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞
      (fun p : AddCircle T × ℝ => d.period_γ.lift p.1) :=
    (periodicLift_contMDiff d.smooth_γ d.period_γ).comp contMDiff_fst
  have hE : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞
      (fun p : AddCircle T × ℝ => d.period_E.lift p.1) :=
    (periodicLift_contMDiff d.smooth_E d.period_E).comp contMDiff_fst
  exact hγ.add (contMDiff_snd.smul hE)

private theorem identityBandNative_raw_mfderiv {F : Coord → Ambient}
    (hF : ContDiff ℝ ∞ F) (p : ℝ × ℝ) :
    mfderiv nativeProductModel 𝓘(ℝ, Ambient)
      (F ∘ nativeProductGaussCoordinateEquiv) p =
      (fderiv ℝ F (nativeProductGaussCoordinateEquiv p)).comp
        nativeProductGaussCoordinateEquiv.toContinuousLinearMap := by
  unfold nativeProductModel
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod, mfderiv_eq_fderiv]
  rw [fderiv_comp p (hF.differentiable (by simp) _)
    nativeProductGaussCoordinateEquiv.differentiableAt]
  congr 1
  exact nativeProductGaussCoordinateEquiv.hasFDerivAt.fderiv

private theorem identityBandNative_full_regular_of_raw
    {T : ℝ} [Fact (0 < T)] {F : AddCircle T × ℝ → Ambient} {R : Coord → Ambient}
    (hF : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ F)
    (hR : ContDiff ℝ ∞ R)
    (hrep : F ∘ identityBandNativeCylinderProjection T = R ∘ nativeProductGaussCoordinateEquiv)
    (hRi : ∀ q, Function.Injective (fderiv ℝ R q)) (p : AddCircle T × ℝ) :
    Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient) F p) := by
  obtain ⟨s, hs⟩ := QuotientAddGroup.mk_surjective p.1
  let q : ℝ × ℝ := (s, p.2)
  have hq : identityBandNativeCylinderProjection T q = p := Prod.ext hs rfl
  have hd := mfderiv_comp q
    ((hF (identityBandNativeCylinderProjection T q)).mdifferentiableAt (by simp))
    ((identityBandNativeCylinderProjection_contMDiff T q).mdifferentiableAt (by simp))
  have hraw : mfderiv nativeProductModel 𝓘(ℝ, Ambient)
      (F ∘ identityBandNativeCylinderProjection T) q =
      (fderiv ℝ R (nativeProductGaussCoordinateEquiv q)).comp
        nativeProductGaussCoordinateEquiv.toContinuousLinearMap := by
    rw [hrep]
    exact identityBandNative_raw_mfderiv hR q
  intro v w hvw
  obtain ⟨v', hv⟩ := identityBandNativeCylinderProjection_mfderiv_surjective T q v
  obtain ⟨w', hw⟩ := identityBandNativeCylinderProjection_mfderiv_surjective T q w
  have hprod : mfderiv nativeProductModel 𝓘(ℝ, Ambient)
      (F ∘ identityBandNativeCylinderProjection T) q v' =
      mfderiv nativeProductModel 𝓘(ℝ, Ambient)
        (F ∘ identityBandNativeCylinderProjection T) q w' := by
    rw [hd]
    change mfderiv nativeProductModel 𝓘(ℝ, Ambient) F (identityBandNativeCylinderProjection T q)
        (mfderiv nativeProductModel nativeProductModel (identityBandNativeCylinderProjection T) q v') =
      mfderiv nativeProductModel 𝓘(ℝ, Ambient) F (identityBandNativeCylinderProjection T q)
        (mfderiv nativeProductModel nativeProductModel (identityBandNativeCylinderProjection T) q w')
    rw [hv, hw, hq]
    exact hvw
  rw [hraw] at hprod
  have hsame : v' = w' := nativeProductGaussCoordinateEquiv.injective
    (hRi (nativeProductGaussCoordinateEquiv q) hprod)
  rw [← hv, ← hw, hsame]

/-- Ambient differential regularity of the actual surface, at every height. -/
theorem identityBand_fullBandMap_differential_injective {T : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T) (p : AddCircle T × ℝ) :
    Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient) d.fullBandMap p) := by
  apply identityBandNative_full_regular_of_raw (identityBand_fullBandMap_contMDiff d)
    (identityBandNative_rawMap_contDiff d) _ _ p
  · funext q
    exact ruledCircleChart_fullBandMap d q.1 (nativeProductGaussCoordinateEquiv q)
  · intro q
    exact ruled_differential_injective (d.deriv_γ (q 0)) (d.deriv_E (q 0))
      (d.orthonormal (q 0)) (d.torsion_ne_zero (q 0))

/-- Ambient normal differential regularity of the actual Gauss map, at every height. -/
theorem identityBand_fullGaussMap_differential_injective {T : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T) (p : AddCircle T × ℝ) :
    Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient) d.fullGaussMap p) := by
  apply identityBandNative_full_regular_of_raw (periodicRuledFrame_fullGaussMap_contMDiff d)
    (periodicRuledFrame_rawGaussMap_contDiff d) _ _ p
  · funext q
    exact ruledCircleChart_fullGaussMap d q.1 (nativeProductGaussCoordinateEquiv q)
  · exact periodicRuledFrame_rawGaussMap_differential_injective d

/-- The actual full-cylinder unit normal annihilates each actual native surface tangent. -/
theorem identityBand_fullBandMap_normal_orthogonal {T : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T) (p : AddCircle T × ℝ) (v : ℝ × ℝ) :
    @inner ℝ Ambient _ (mfderiv nativeProductModel 𝓘(ℝ, Ambient) d.fullBandMap p v)
      (d.fullGaussMap p) = 0 := by
  obtain ⟨s, hs⟩ := QuotientAddGroup.mk_surjective p.1
  let q : ℝ × ℝ := (s, p.2)
  have hq : identityBandNativeCylinderProjection T q = p := Prod.ext hs rfl
  obtain ⟨v', hv⟩ := identityBandNativeCylinderProjection_mfderiv_surjective T q v
  have hd := mfderiv_comp q
    ((identityBand_fullBandMap_contMDiff d (identityBandNativeCylinderProjection T q)).mdifferentiableAt (by simp))
    ((identityBandNativeCylinderProjection_contMDiff T q).mdifferentiableAt (by simp))
  have hrep : d.fullBandMap ∘ identityBandNativeCylinderProjection T =
      ruledMap d.γ d.E ∘ nativeProductGaussCoordinateEquiv := by
    funext z
    exact ruledCircleChart_fullBandMap d z.1 (nativeProductGaussCoordinateEquiv z)
  have hraw : mfderiv nativeProductModel 𝓘(ℝ, Ambient)
      (d.fullBandMap ∘ identityBandNativeCylinderProjection T) q =
      (fderiv ℝ (ruledMap d.γ d.E) (nativeProductGaussCoordinateEquiv q)).comp
        nativeProductGaussCoordinateEquiv.toContinuousLinearMap := by
    rw [hrep]
    exact identityBandNative_raw_mfderiv (identityBandNative_rawMap_contDiff d) q
  have hx : mfderiv nativeProductModel 𝓘(ℝ, Ambient) d.fullBandMap p v =
      fderiv ℝ (ruledMap d.γ d.E) (nativeProductGaussCoordinateEquiv q)
        (nativeProductGaussCoordinateEquiv v') := by
    have hh := congrArg (fun D => D v') (hd.symm.trans hraw)
    change mfderiv nativeProductModel 𝓘(ℝ, Ambient) d.fullBandMap
        (identityBandNativeCylinderProjection T q)
        (mfderiv nativeProductModel nativeProductModel
          (identityBandNativeCylinderProjection T) q v') =
      fderiv ℝ (ruledMap d.γ d.E) (nativeProductGaussCoordinateEquiv q)
        (nativeProductGaussCoordinateEquiv v') at hh
    rw [hv, hq] at hh
    exact hh
  have hn : d.fullGaussMap p = d.rawGaussMap (nativeProductGaussCoordinateEquiv q) := by
    rw [← hq]
    exact ruledCircleChart_fullGaussMap d q.1 (nativeProductGaussCoordinateEquiv q)
  rw [hx, hn]
  exact (ruled_isUnitNormal (d.deriv_γ _) (d.deriv_E _)
    (d.orthonormal _) (d.torsion_ne_zero _)).2 (nativeProductGaussCoordinateEquiv v')

/-- The two-sided height interval, carrying its ordinary open-subtype structure. -/
def identityBandTwoSidedOpen (w : ℝ) : TopologicalSpace.Opens ℝ :=
  ⟨Ioo (-w) w, isOpen_Ioo⟩

instance identityBandTwoSidedHeight_chartedSpace (w : ℝ) :
    ChartedSpace ℝ (Ioo (-w) w) :=
  inferInstanceAs (ChartedSpace ℝ (identityBandTwoSidedOpen w))

instance identityBandTwoSidedHeight_manifold (w : ℝ) :
    IsManifold 𝓘(ℝ, ℝ) ∞ (Ioo (-w) w) :=
  inferInstanceAs (IsManifold 𝓘(ℝ, ℝ) ∞ (identityBandTwoSidedOpen w))

def identityBandTwoSidedInclusion (T w : ℝ) :
    AddCircle T × Ioo (-w) w → AddCircle T × ℝ := Prod.map id Subtype.val

theorem identityBandTwoSidedInclusion_contMDiff (T w : ℝ) [Fact (0 < T)] :
    ContMDiff nativeProductModel nativeProductModel ∞ (identityBandTwoSidedInclusion T w) :=
  contMDiff_id.prodMap (contMDiff_subtype_val (U := identityBandTwoSidedOpen w))

theorem identityBandTwoSidedInclusion_mfderiv (T w : ℝ) [Fact (0 < T)]
    (p : AddCircle T × Ioo (-w) w) (v : ℝ × ℝ) :
    mfderiv nativeProductModel nativeProductModel (identityBandTwoSidedInclusion T w) p v = v := by
  have hv : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      (Subtype.val : Ioo (-w) w → ℝ) p.2 = ContinuousLinearMap.id ℝ ℝ := by
    exact mfderiv_extChartAt_self (I := 𝓘(ℝ, ℝ)) (x := p.2)
  have hf : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      (id : AddCircle T → AddCircle T) p.1 := mdifferentiableAt_id
  have hg : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      (Subtype.val : Ioo (-w) w → ℝ) p.2 :=
    (contMDiff_subtype_val (n := ∞) (U := identityBandTwoSidedOpen w) p.2).mdifferentiableAt (by simp)
  have hh := congrArg (fun D => D v) (mfderiv_prodMap hf hg)
  change mfderiv nativeProductModel nativeProductModel (identityBandTwoSidedInclusion T w) p v =
    (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (id : AddCircle T → AddCircle T) p.1 v.1,
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (Subtype.val : Ioo (-w) w → ℝ) p.2 v.2) at hh
  rw [mfderiv_id, hv] at hh
  change mfderiv nativeProductModel nativeProductModel (identityBandTwoSidedInclusion T w) p v =
    (v.1, v.2) at hh
  exact hh.trans (Prod.eta v)
def identityBandTwoSidedMap {T w : ℝ} (d : PeriodicRuledFrame T)
    (p : AddCircle T × Ioo (-w) w) : Ambient :=
  d.fullBandMap (identityBandTwoSidedInclusion T w p)

def identityBandTwoSidedGaussMap {T w : ℝ} (d : PeriodicRuledFrame T)
    (p : AddCircle T × Ioo (-w) w) : Ambient :=
  d.fullGaussMap (identityBandTwoSidedInclusion T w p)

local instance identityBandCentralSupportNativeSphereDimension :
    Fact (Module.finrank ℝ Ambient = 2 + 1) := ⟨by simp [Ambient]⟩

def identityBandTwoSidedSphereGauss {T w : ℝ} (d : PeriodicRuledFrame T)
    (p : AddCircle T × Ioo (-w) w) : RoundSphere :=
  ⟨identityBandTwoSidedGaussMap d p, by
    simpa [identityBandTwoSidedGaussMap] using
      periodicRuledFrame_fullGaussMap_norm d (identityBandTwoSidedInclusion T w p)⟩

/-- Actual two-sided geometry in the native product model. Smoothness,
both ambient differential injections and normal orthogonality are derived;
no injectivity of the Gauss image or inverse/potential is an input. -/
theorem identityBandTwoSided_native_geometry {T w : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T) :
    ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ (identityBandTwoSidedMap (w := w) d) ∧
      ContMDiff nativeProductModel (𝓡 2) ∞ (identityBandTwoSidedSphereGauss (w := w) d) ∧
      ∀ p : AddCircle T × Ioo (-w) w,
        Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient) (identityBandTwoSidedMap d) p) ∧
        Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient) (identityBandTwoSidedGaussMap d) p) ∧
        ∀ v : ℝ × ℝ,
          @inner ℝ Ambient _ (mfderiv nativeProductModel 𝓘(ℝ, Ambient) (identityBandTwoSidedMap d) p v)
            (identityBandTwoSidedSphereGauss d p).val = 0 := by
  have hJ := identityBandTwoSidedInclusion_contMDiff T w
  have hX : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ (identityBandTwoSidedMap (w := w) d) :=
    (identityBand_fullBandMap_contMDiff d).comp hJ
  have hN : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ (identityBandTwoSidedGaussMap (w := w) d) :=
    (periodicRuledFrame_fullGaussMap_contMDiff d).comp hJ
  have hS : ContMDiff nativeProductModel (𝓡 2) ∞ (identityBandTwoSidedSphereGauss (w := w) d) :=
    hN.codRestrict_sphere (fun p => by simpa [identityBandTwoSidedGaussMap] using
      periodicRuledFrame_fullGaussMap_norm d (identityBandTwoSidedInclusion T w p))
  refine ⟨hX, hS, ?_⟩
  intro p
  have hDX := mfderiv_comp p
    ((identityBand_fullBandMap_contMDiff d (identityBandTwoSidedInclusion T w p)).mdifferentiableAt (by simp))
    ((hJ p).mdifferentiableAt (by simp))
  have hDN := mfderiv_comp p
    ((periodicRuledFrame_fullGaussMap_contMDiff d (identityBandTwoSidedInclusion T w p)).mdifferentiableAt (by simp))
    ((hJ p).mdifferentiableAt (by simp))
  have hJv (v : ℝ × ℝ) : mfderiv nativeProductModel nativeProductModel
      (identityBandTwoSidedInclusion T w) p v = v :=
    identityBandTwoSidedInclusion_mfderiv T w p v
  have hDXv (v : ℝ × ℝ) :
      mfderiv nativeProductModel 𝓘(ℝ, Ambient) (identityBandTwoSidedMap d) p v =
        mfderiv nativeProductModel 𝓘(ℝ, Ambient) d.fullBandMap
          (identityBandTwoSidedInclusion T w p) v := by
    have hh := congrArg (fun D => D v) hDX
    change mfderiv nativeProductModel 𝓘(ℝ, Ambient) (identityBandTwoSidedMap d) p v =
      mfderiv nativeProductModel 𝓘(ℝ, Ambient) d.fullBandMap
        (identityBandTwoSidedInclusion T w p)
        (mfderiv nativeProductModel nativeProductModel (identityBandTwoSidedInclusion T w) p v) at hh
    rw [hJv] at hh
    exact hh
  have hDNv (v : ℝ × ℝ) :
      mfderiv nativeProductModel 𝓘(ℝ, Ambient) (identityBandTwoSidedGaussMap d) p v =
        mfderiv nativeProductModel 𝓘(ℝ, Ambient) d.fullGaussMap
          (identityBandTwoSidedInclusion T w p) v := by
    have hh := congrArg (fun D => D v) hDN
    change mfderiv nativeProductModel 𝓘(ℝ, Ambient) (identityBandTwoSidedGaussMap d) p v =
      mfderiv nativeProductModel 𝓘(ℝ, Ambient) d.fullGaussMap
        (identityBandTwoSidedInclusion T w p)
        (mfderiv nativeProductModel nativeProductModel (identityBandTwoSidedInclusion T w) p v) at hh
    rw [hJv] at hh
    exact hh
  refine ⟨?_, ?_, ?_⟩
  · intro v z hvz
    apply identityBand_fullBandMap_differential_injective d (identityBandTwoSidedInclusion T w p)
    rw [← hDXv v, ← hDXv z]
    exact hvz
  · intro v z hvz
    apply identityBand_fullGaussMap_differential_injective d (identityBandTwoSidedInclusion T w p)
    rw [← hDNv v, ← hDNv z]
    exact hvz
  · intro v
    rw [hDXv]
    exact identityBand_fullBandMap_normal_orthogonal d (identityBandTwoSidedInclusion T w p) v

end
end TightVer401






