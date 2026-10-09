import TightVer401.ExitPositiveGraphFermiEmbedding
import TightVer401.FermiScaleCalculus
import TightVer401.IdentityBandCentralSupportNative
import TightVer401.IdentityBandPlanarSupportImage
import Mathlib.Topology.MetricSpace.Thickening

/-! Actual Fermi collars for the positive-exit application. The northern
strip and nonvanishing scale are constructed by compactness; regularity
comes from the actual Fermi metric. The Cartesian inverse is the retained
Gauss-image inverse transported through the existing native/Coord bridge. -/
open scoped Manifold
namespace TightVer401
noncomputable section
open Set Filter Metric OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- The actual Fermi longitudinal scale on the quotient cylinder. -/
def positiveExitFermiNativeScale {P : ℝ} {ζ : ℝ → Ambient}
    (hζ : ContDiff ℝ ∞ ζ) (hζP : Function.Periodic ζ P)
    (p : AddCircle P × ℝ) : ℝ :=
  Real.cos p.2 + (normalLoop_actual_periodic hζ hζP).2.lift p.1 * Real.sin p.2

/-- Restrict the actual sphere-valued Fermi map to its two-sided open tube. -/
def positiveExitFermiSphere {P ρ : ℝ} {ζ : ℝ → Ambient}
    (hζ : ContDiff ℝ ∞ ζ) (hζP : Function.Periodic ζ P)
    (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1)
    (p : AddCircle P × Ioo (-ρ) ρ) : RoundSphere :=
  fermiNativeSphereMap hζ hζP hunit hspeed (identityBandTwoSidedInclusion P ρ p)

/-- Actual Cartesian gnomonic coordinates of the Fermi tube. -/
def positiveExitFermiCartesian {P ρ : ℝ} {ζ : ℝ → Ambient}
    (hζ : ContDiff ℝ ∞ ζ) (hζP : Function.Periodic ζ P)
    (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1)
    (p : AddCircle P × Ioo (-ρ) ρ) : Coord :=
  gnomonicInverse (positiveExitFermiSphere (ρ := ρ) hζ hζP hunit hspeed p).val

private theorem positiveExitFermiNativeScale_continuous {P : ℝ} [Fact (0 < P)]
    {ζ : ℝ → Ambient} (hζ : ContDiff ℝ ∞ ζ) (hζP : Function.Periodic ζ P) :
    Continuous (positiveExitFermiNativeScale hζ hζP) := by
  have hk := ((periodicLift_contMDiff (normalLoop_actual_smooth hζ).2
    (normalLoop_actual_periodic hζ hζP).2).comp
      (contMDiff_fst : ContMDiff nativeProductModel 𝓘(ℝ, ℝ) ∞
        (Prod.fst : AddCircle P × ℝ → AddCircle P))).continuous
  exact (Real.continuous_cos.comp continuous_snd).add
    (hk.mul (Real.continuous_sin.comp continuous_snd))

/-- Actual raw Fermi differential regularity follows from its diagonal metric. -/
theorem positiveExitFermi_raw_differential_injective {ζ : ℝ → Ambient}
    (hζ : ContDiff ℝ ∞ ζ) (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1) (q : Coord)
    (hscale : fermiNormalScale (normalLoopCurvature ζ) q ≠ 0) :
    Function.Injective (fderiv ℝ (fermiNormalMap ζ) q) := by
  intro v z hvz
  have hz : fderiv ℝ (fermiNormalMap ζ) q (v - z) = 0 := by
    simp [map_sub, hvz]
  have he := inducedMetric_bilinear (fermiNormalMap ζ) q (v - z) (v - z)
  rw [hz, inner_zero_left, fermiNormalMap_metric hζ hunit hspeed] at he
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, zero_mul, one_mul, add_zero, zero_add] at he
  norm_num at he
  have h0 : (v - z) 0 = 0 := by
    have hp : (fermiNormalScale (normalLoopCurvature ζ) q) ^ 2 * ((v - z) 0) ^ 2 = 0 := by
      change (fermiNormalScale (normalLoopCurvature ζ) q) ^ 2 * (v 0 - z 0) ^ 2 = 0
      nlinarith [sq_nonneg (v 1 - z 1),
        mul_nonneg (sq_nonneg (fermiNormalScale (normalLoopCurvature ζ) q))
          (sq_nonneg (v 0 - z 0))]
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hp).resolve_left (pow_ne_zero 2 hscale))
  have h1 : (v - z) 1 = 0 := by
    change v 1 - z 1 = 0
    nlinarith [mul_nonneg (sq_nonneg (fermiNormalScale (normalLoopCurvature ζ) q))
      (sq_nonneg (v 0 - z 0))]
  apply sub_eq_zero.mp
  ext i
  fin_cases i <;> assumption

private theorem positiveExitFermi_quotient_derivative {P : ℝ} [Fact (0 < P)]
    {ζ : ℝ → Ambient} (hζ : ContDiff ℝ ∞ ζ) (hζP : Function.Periodic ζ P)
    (q v : ℝ × ℝ) :
    mfderiv nativeProductModel 𝓘(ℝ, Ambient) (fermiNativeMap ζ hζ hζP)
        (identityBandNativeCylinderProjection P q)
        (mfderiv nativeProductModel nativeProductModel
          (identityBandNativeCylinderProjection P) q v) =
      fderiv ℝ (fermiNormalMap ζ) (nativeProductGaussCoordinateEquiv q)
        (nativeProductGaussCoordinateEquiv v) := by
  have hrep : fermiNativeMap ζ hζ hζP ∘ identityBandNativeCylinderProjection P =
      fermiNormalMap ζ ∘ nativeProductGaussCoordinateEquiv := by
    funext p
    rfl
  have hraw : mfderiv nativeProductModel 𝓘(ℝ, Ambient)
      (fermiNormalMap ζ ∘ nativeProductGaussCoordinateEquiv) q =
      (fderiv ℝ (fermiNormalMap ζ) (nativeProductGaussCoordinateEquiv q)).comp
        nativeProductGaussCoordinateEquiv.toContinuousLinearMap := by
    unfold nativeProductModel
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod, mfderiv_eq_fderiv,
      fderiv_comp q ((fermiNormalMap_contDiff hζ).differentiable (by simp) _)
        nativeProductGaussCoordinateEquiv.differentiableAt]
    congr 1
    exact nativeProductGaussCoordinateEquiv.hasFDerivAt.fderiv
  have hcomp := mfderiv_comp q
    ((fermiNativeMap_contMDiff hζ hζP _).mdifferentiableAt (by simp))
    ((identityBandNativeCylinderProjection_contMDiff P q).mdifferentiableAt (by simp))
  rw [hrep] at hcomp
  have hh := congrArg (fun D => D v) (hcomp.symm.trans hraw)
  change mfderiv nativeProductModel 𝓘(ℝ, Ambient) (fermiNativeMap ζ hζ hζP)
      (identityBandNativeCylinderProjection P q)
      (mfderiv nativeProductModel nativeProductModel (identityBandNativeCylinderProjection P) q v) =
    fderiv ℝ (fermiNormalMap ζ) (nativeProductGaussCoordinateEquiv q)
      (nativeProductGaussCoordinateEquiv v) at hh
  exact hh

private theorem positiveExitFermi_native_differential_injective
    {P : ℝ} [Fact (0 < P)] {ζ : ℝ → Ambient}
    (hζ : ContDiff ℝ ∞ ζ) (hζP : Function.Periodic ζ P)
    (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1)
    (p : AddCircle P × ℝ) (hscale : positiveExitFermiNativeScale hζ hζP p ≠ 0) :
    Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient)
      (fermiNativeMap ζ hζ hζP) p) := by
  obtain ⟨r, hr⟩ := QuotientAddGroup.mk_surjective p.1
  let q : ℝ × ℝ := (r, p.2)
  have hq : identityBandNativeCylinderProjection P q = p := Prod.ext hr rfl
  have hrawscale : fermiNormalScale (normalLoopCurvature ζ)
      (nativeProductGaussCoordinateEquiv q) ≠ 0 := by
    simp only [positiveExitFermiNativeScale, ← hr, Function.Periodic.lift_coe] at hscale
    exact hscale
  have hi := positiveExitFermi_raw_differential_injective hζ hunit hspeed
    (nativeProductGaussCoordinateEquiv q) hrawscale
  intro v z hvz
  obtain ⟨v', hv⟩ := identityBandNativeCylinderProjection_mfderiv_surjective P q v
  obtain ⟨z', hz⟩ := identityBandNativeCylinderProjection_mfderiv_surjective P q z
  have he : fderiv ℝ (fermiNormalMap ζ) (nativeProductGaussCoordinateEquiv q)
      (nativeProductGaussCoordinateEquiv v') =
      fderiv ℝ (fermiNormalMap ζ) (nativeProductGaussCoordinateEquiv q)
        (nativeProductGaussCoordinateEquiv z') := by
    rw [← positiveExitFermi_quotient_derivative hζ hζP q v',
      ← positiveExitFermi_quotient_derivative hζ hζP q z', hv, hz, hq]
    exact hvz
  have hsame := nativeProductGaussCoordinateEquiv.injective (hi he)
  rw [← hv, ← hz, hsame]

/-- One actual closed strip is simultaneously embedded, northern and regular. -/
theorem positiveExit_exists_fermi_strip {P : ℝ} [Fact (0 < P)] {ζ : ℝ → Ambient}
    (hζ : ContDiff ℝ ∞ ζ) (hζP : Function.Periodic ζ P)
    (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1)
    (hi : Function.Injective hζP.lift) (hnorth : ∀ r, 0 < ζ r 2) :
    ∃ ρ > 0,
      InjOn (fermiNativeMap ζ hζ hζP) (univ ×ˢ Icc (-ρ) ρ) ∧
      (∀ p ∈ (univ ×ˢ Icc (-ρ) ρ : Set (AddCircle P × ℝ)),
        0 < fermiNativeMap ζ hζ hζP p 2 ∧ 0 < positiveExitFermiNativeScale hζ hζP p) ∧
      (∀ q : Coord, |q 1| ≤ ρ → 0 < fermiNormalScale (normalLoopCurvature ζ) q) := by
  obtain ⟨ε, hε, hinj, _⟩ := fermiNativeMap_exists_thin_embedded_strip hζ hζP hunit hspeed hi
  let K : Set (AddCircle P × ℝ) := (fun q : AddCircle P => (q, (0 : ℝ))) '' univ
  let U : Set (AddCircle P × ℝ) := {p | 0 < fermiNativeMap ζ hζ hζP p 2 ∧
    0 < positiveExitFermiNativeScale hζ hζP p}
  have hK : IsCompact K := isCompact_univ.image (continuous_id.prodMk continuous_const)
  have hc : Continuous (fun p : AddCircle P × ℝ => fermiNativeMap ζ hζ hζP p 2) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) 2).continuous.comp
      (fermiNativeMap_contMDiff hζ hζP).continuous
  have hU : IsOpen U := (isOpen_lt continuous_const hc).inter
    (isOpen_lt continuous_const (positiveExitFermiNativeScale_continuous hζ hζP))
  have hKU : K ⊆ U := by
    rintro _ ⟨p, _, rfl⟩
    obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective p
    constructor
    · simpa [fermiNativeMap, Function.Periodic.lift_coe] using hnorth r
    · simp [positiveExitFermiNativeScale]
  obtain ⟨η, hη, hthick⟩ := hK.exists_cthickening_subset_open hU hKU
  let ρ := min ε (η / 2)
  have hρ : 0 < ρ := lt_min hε (half_pos hη)
  have hsub : (univ ×ˢ Icc (-ρ) ρ : Set (AddCircle P × ℝ)) ⊆ univ ×ˢ Icc (-ε) ε := by
    intro p hp
    exact ⟨hp.1, ⟨by linarith [hp.2.1, min_le_left ε (η / 2)],
      hp.2.2.trans (min_le_left ε (η / 2))⟩⟩
  have hpos : ∀ p ∈ (univ ×ˢ Icc (-ρ) ρ : Set (AddCircle P × ℝ)), p ∈ U := by
    intro p hp
    apply hthick
    apply Metric.thickening_subset_cthickening η K
    apply Metric.mem_thickening_iff.mpr
    refine ⟨(p.1, 0), ⟨p.1, mem_univ _, rfl⟩, ?_⟩
    rw [dist_prod_same_left, Real.dist_eq, sub_zero]
    exact ((abs_le.mpr hp.2).trans (min_le_right ε (η / 2))).trans_lt (half_lt_self hη)
  refine ⟨ρ, hρ, hinj.mono hsub, hpos, ?_⟩
  intro q hq
  have hh := (hpos (periodProjection P (q 0), q 1) ⟨mem_univ _, abs_le.mp hq⟩).2
  exact hh

/-- The actual thin Fermi tube has its actual smooth Cartesian coordinates
and a smooth inverse, constructed rather than supplied as an assumption. -/
theorem positiveExit_exists_fermi_collar {P : ℝ} [Fact (0 < P)] {ζ : ℝ → Ambient}
    (hζ : ContDiff ℝ ∞ ζ) (hζP : Function.Periodic ζ P)
    (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1)
    (hi : Function.Injective hζP.lift) (hnorth : ∀ r, 0 < ζ r 2) :
    ∃ ρ > 0,
      InjOn (fermiNativeMap ζ hζ hζP) (univ ×ˢ Icc (-ρ) ρ) ∧
      (∀ p ∈ (univ ×ˢ Icc (-ρ) ρ : Set (AddCircle P × ℝ)),
        0 < fermiNativeMap ζ hζ hζP p 2 ∧ 0 < positiveExitFermiNativeScale hζ hζP p) ∧
      (∀ q : Coord, |q 1| ≤ ρ → 0 < fermiNormalScale (normalLoopCurvature ζ) q) ∧
      ∃ e : OpenPartialHomeomorph (AddCircle P × Ioo (-ρ) ρ) Coord,
        e.source = univ ∧ e.target = range (positiveExitFermiCartesian (ρ := ρ) hζ hζP hunit hspeed) ∧
        (e : (AddCircle P × Ioo (-ρ) ρ) → Coord) = positiveExitFermiCartesian (ρ := ρ) hζ hζP hunit hspeed ∧
        ContMDiff nativeProductModel 𝓘(ℝ, Coord) ∞ e ∧
        ContMDiffOn 𝓘(ℝ, Coord) nativeProductModel ∞ e.symm e.target := by
  obtain ⟨ρ, hρ, hI, hpos, hrawscale⟩ := positiveExit_exists_fermi_strip hζ hζP hunit hspeed hi hnorth
  let M := AddCircle P × Ioo (-ρ) ρ
  letI : Nonempty M := ⟨(0, ⟨0, by constructor <;> linarith⟩)⟩
  letI : ChartedSpace Coord M := nativeProductGaussChartedSpace M
  letI : IsManifold 𝓘(ℝ, Coord) ∞ M := nativeProductGauss_isManifold M
  letI : Fact (Module.finrank ℝ Ambient = 2 + 1) := ⟨by simp [Ambient]⟩
  let N : M → RoundSphere := positiveExitFermiSphere (ρ := ρ) hζ hζP hunit hspeed
  let A : M → Ambient := fermiNativeMap ζ hζ hζP ∘ identityBandTwoSidedInclusion P ρ
  have hJ := identityBandTwoSidedInclusion_contMDiff P ρ
  have hAn : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ A :=
    (fermiNativeMap_contMDiff hζ hζP).comp hJ
  have hNn : ContMDiff nativeProductModel (𝓡 2) ∞ N :=
    (fermiNativeSphereMap_contMDiff hζ hζP hunit hspeed).comp hJ
  have hNC : ContMDiff 𝓘(ℝ, Coord) (𝓡 2) ∞ N :=
    hNn.comp (nativeProductGauss_inverse_contMDiff M)
  have hmem (p : M) : identityBandTwoSidedInclusion P ρ p ∈
      (univ ×ˢ Icc (-ρ) ρ : Set (AddCircle P × ℝ)) :=
    ⟨mem_univ _, p.2.property.1.le, p.2.property.2.le⟩
  have hn (p : M) : 0 < (N p).val 2 := (hpos _ (hmem p)).1
  have hNi : Function.Injective N := by
    intro p q hpq
    have hh := hI (hmem p) (hmem q) (congrArg Subtype.val hpq)
    apply Prod.ext
    · exact congrArg (fun z : AddCircle P × ℝ => z.1) hh
    · exact Subtype.ext (congrArg (fun z : AddCircle P × ℝ => z.2) hh)
  have hAi (p : M) : Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient) A p) := by
    have hD := mfderiv_comp p
      ((fermiNativeMap_contMDiff hζ hζP _).mdifferentiableAt (by simp))
      ((hJ p).mdifferentiableAt (by simp))
    have hv (v : ℝ × ℝ) : mfderiv nativeProductModel 𝓘(ℝ, Ambient) A p v =
        mfderiv nativeProductModel 𝓘(ℝ, Ambient) (fermiNativeMap ζ hζ hζP)
          (identityBandTwoSidedInclusion P ρ p) v := by
      have hh := congrArg (fun D => D v) hD
      change mfderiv nativeProductModel 𝓘(ℝ, Ambient) A p v =
        mfderiv nativeProductModel 𝓘(ℝ, Ambient) (fermiNativeMap ζ hζ hζP)
          (identityBandTwoSidedInclusion P ρ p)
          (mfderiv nativeProductModel nativeProductModel (identityBandTwoSidedInclusion P ρ) p v) at hh
      rw [identityBandTwoSidedInclusion_mfderiv] at hh
      exact hh
    intro v z hvz
    apply positiveExitFermi_native_differential_injective hζ hζP hunit hspeed
      (identityBandTwoSidedInclusion P ρ p) (hpos _ (hmem p)).2.ne'
    rw [← hv v, ← hv z]
    exact hvz
  have hCi (p : M) : Function.Injective (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient)
      (fun x => (N x).val) p) := by
    change Function.Injective (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) A p)
    rw [nativeProductGauss_mfderiv M ((hAn p).mdifferentiableAt (by simp))]
    exact (hAi p).comp nativeProductGaussCoordinateEquiv.symm.injective
  let e := identityBandPlanarSourceChart hNC hCi hNi hn
  have heT : e.target = range (positiveExitFermiCartesian (ρ := ρ) hζ hζP hunit hspeed) :=
    identityBandPlanarSourceDomain_eq_range hn
  have heS : ContMDiff nativeProductModel 𝓘(ℝ, Coord) ∞ e :=
    (identityBandPlanarSource_contMDiff hNC hn).comp (nativeProductGauss_identity_contMDiff M)
  have heI : ContMDiffOn 𝓘(ℝ, Coord) nativeProductModel ∞ e.symm e.target :=
    (nativeProductGauss_inverse_contMDiff M).comp_contMDiffOn
      (identityBandPlanarSourceInverse_contMDiffOn hNC hCi hNi)
  exact ⟨ρ, hρ, hI, hpos, hrawscale, e, rfl, heT, rfl, heS, heI⟩

end
end TightVer401
