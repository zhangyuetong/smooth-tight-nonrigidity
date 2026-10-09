import TightVer401.PositiveExitConstructionFirstIntegral
import TightVer401.PositiveExitConstructionLeaf
import TightVer401.PositiveExitConstructionPullback
import TightVer401.ScalarFlowPeriodLocalFamily

/-! The actual first integral transported through the same Cartesian source
inverse and the actual Fermi source. Nonvanishing of its differential is
derived from the raw transverse derivative and actual coordinate ranks.
Constancy on the same selected leaf then forces Fermi transversality. -/
open scoped Manifold
namespace TightVer401
noncomputable section
open Set Filter MeasureTheory OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {T w : ℝ} (d : PeriodicRuledFrame T)
  (hb : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0)

/-- The actual label in the same Cartesian source coordinates. -/
def positiveExitCartesianLabel
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) Coord) (q : Coord) : ℝ :=
  positiveExitLevel d hb (e.symm q)

/-- Pull back that actual label through the actual Fermi source. -/
def positiveExitFermiLabel
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) Coord)
    (ζ : ℝ → Ambient) : Coord → ℝ :=
  positiveExitCartesianLabel d hb e ∘ positiveExitFermiSource ζ

/-- The actual inverse-image domain, restricted to the northern chart. -/
def positiveExitFermiLabelDomain
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) Coord)
    (ζ : ℝ → Ambient) : Set Coord :=
  {q | 0 < fermiNormalMap ζ q 2} ∩ positiveExitFermiSource ζ ⁻¹' e.target

variable [Fact (0 < T)]

/-- Smoothness of the actual first integral on the original native band. -/
theorem positiveExitLevel_contMDiff :
    ContMDiff nativeProductModel 𝓘(ℝ, ℝ) ∞ (positiveExitLevel (w := w) d hb) := by
  have hρ := (periodicLift_contMDiff (ruledRho_contDiff d.smooth_τ d.torsion_ne_zero)
    (ruledRho_periodic d.period_τ)).comp
      (contMDiff_fst : ContMDiff nativeProductModel 𝓘(ℝ, ℝ) ∞
        (Prod.fst : AddCircle T × Ioo (0 : ℝ) w → AddCircle T))
  have hω := (periodicLift_contMDiff (OAI.ClosedSurfaceR4.PeriodicPrimitive.rawPrimitive_contDiff
    (ruledPeriodCoefficient_contDiff d.smooth_k d.smooth_τ d.torsion_ne_zero))
      (periodicRuledFrame_omega_periodic d hb)).comp
        (contMDiff_fst : ContMDiff nativeProductModel 𝓘(ℝ, ℝ) ∞
          (Prod.fst : AddCircle T × Ioo (0 : ℝ) w → AddCircle T))
  have hu : ContMDiff nativeProductModel 𝓘(ℝ, ℝ) ∞
      (fun p : AddCircle T × Ioo (0 : ℝ) w => (p.2 : ℝ)) :=
    (contMDiff_subtype_val (U := bandOpen w)).comp contMDiff_snd
  have hρ0 (p : AddCircle T × Ioo (0 : ℝ) w) :
      (ruledRho_periodic d.period_τ).lift p.1 ≠ 0 := by
    obtain ⟨r, hr⟩ := QuotientAddGroup.mk_surjective p.1
    rw [← hr, Function.Periodic.lift_coe]
    exact (ruledRho_pos (d.torsion_ne_zero r)).ne'
  exact (contMDiff_const.div₀ (hρ.mul hu)
    (fun p => mul_ne_zero (hρ0 p) p.2.property.1.ne')).sub hω

/-- Actual native label regularity, transported from the retained raw partial. -/
theorem positiveExitLevel_mfderiv_ne_zero (p : AddCircle T × Ioo (0 : ℝ) w) :
    mfderiv nativeProductModel 𝓘(ℝ, ℝ) (positiveExitLevel d hb) p ≠ 0 := by
  obtain ⟨r, hr⟩ := QuotientAddGroup.mk_surjective p.1
  let q : coordinateBandOpen w := ⟨![r, (p.2 : ℝ)], p.2.property⟩
  have hq : bandFromCoordinates T w q = p := Prod.ext hr (Subtype.ext rfl)
  have hrep : positiveExitLevel d hb ∘ bandFromCoordinates T w =
      (fun z : coordinateBandOpen w => positiveExitRawFirstIntegral d z.val) := by
    funext z
    exact (positiveExitRawFirstIntegral_native_label d hb (z.val 0)
      (⟨z.val 1, z.property⟩ : Ioo (0 : ℝ) w)).symm
  have hraw : DifferentiableAt ℝ (positiveExitRawFirstIntegral d) q.val :=
    ((positiveExitRawFirstIntegral_contDiffOn d) q.val q.property.1).contDiffAt
      ((isOpen_lt continuous_const (continuous_apply 1)).mem_nhds q.property.1)
      |>.differentiableAt (by simp)
  have hv : MDifferentiableAt 𝓘(ℝ, Coord) 𝓘(ℝ, Coord)
      (Subtype.val : coordinateBandOpen w → Coord) q :=
    (contMDiff_subtype_val (n := ∞) q).mdifferentiableAt (by simp)
  have hres : (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, ℝ)
      (fun z : coordinateBandOpen w => positiveExitRawFirstIntegral d z.val) q : Coord →L[ℝ] ℝ) =
      (fderiv ℝ (positiveExitRawFirstIntegral d) q.val).comp
        (openCoordinateInclusionDifferential (coordinateBandOpen w) q) :=
    (hraw.hasFDerivAt.hasMFDerivAt.comp q hv.hasMFDerivAt).mfderiv
  rw [openCoordinate_inclusion_derivative, ContinuousLinearMap.comp_id] at hres
  have hD := mfderiv_comp q
    ((positiveExitLevel_contMDiff d hb _).mdifferentiableAt (by simp))
    ((bandFromCoordinates_contMDiff T w q).mdifferentiableAt (by simp))
  rw [hrep, hres, hq] at hD
  intro hz
  rw [hz, ContinuousLinearMap.zero_comp] at hD
  apply positiveExitRawFirstIntegral_partial1_ne_zero d q.val q.property.1
  change fderiv ℝ (positiveExitRawFirstIntegral d) q.val (Pi.single 1 1) = 0
  rw [hD, ContinuousLinearMap.zero_apply]

variable (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) Coord)

theorem positiveExitCartesianLabel_contDiffOn
    (heI : ContMDiffOn 𝓘(ℝ, Coord) nativeProductModel ∞ e.symm e.target) :
    ContDiffOn ℝ ∞ (positiveExitCartesianLabel d hb e) e.target :=
  ((positiveExitLevel_contMDiff d hb).comp_contMDiffOn heI).contDiffOn

/-- The actual inverse does not destroy label rank. -/
theorem positiveExitCartesianLabel_fderiv_ne_zero
    (heS : e.source = univ)
    (heD : ContMDiff nativeProductModel 𝓘(ℝ, Coord) ∞ e)
    (heI : ContMDiffOn 𝓘(ℝ, Coord) nativeProductModel ∞ e.symm e.target)
    {q : Coord} (hq : q ∈ e.target) :
    fderiv ℝ (positiveExitCartesianLabel d hb e) q ≠ 0 := by
  let p := e.symm q
  have hp : p ∈ e.source := by rw [heS]; exact mem_univ p
  have heq : e p = q := e.right_inv hq
  have hC := (positiveExitLevel_contMDiff d hb).comp_contMDiffOn heI
  have hCd := ((hC q hq).contMDiffAt (e.open_target.mem_nhds hq)).mdifferentiableAt (by simp)
  have hrep : positiveExitCartesianLabel d hb e ∘ e = positiveExitLevel d hb := by
    funext z
    change positiveExitLevel d hb (e.symm (e z)) = positiveExitLevel d hb z
    rw [e.left_inv (by rw [heS]; exact mem_univ z)]
  have hD := mfderiv_comp p (heq.symm ▸ hCd) ((heD p).mdifferentiableAt (by simp))
  change mfderiv nativeProductModel 𝓘(ℝ, ℝ)
      (positiveExitCartesianLabel d hb e ∘ e) p =
    (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, ℝ) (positiveExitCartesianLabel d hb e) (e p)).comp
      (mfderiv nativeProductModel 𝓘(ℝ, Coord) e p) at hD
  rw [hrep, heq] at hD
  intro hz
  apply positiveExitLevel_mfderiv_ne_zero d hb p
  ext v
  have hh := congrArg (fun D => D v) hD
  change mfderiv nativeProductModel 𝓘(ℝ, ℝ) (positiveExitLevel d hb) p v =
    mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, ℝ) (positiveExitCartesianLabel d hb e) q
      (mfderiv nativeProductModel 𝓘(ℝ, Coord) e p v) at hh
  rw [mfderiv_eq_fderiv, hz] at hh
  simpa only [ContinuousLinearMap.zero_apply] using hh

variable {ζ : ℝ → Ambient}

theorem positiveExitFermiLabelDomain_isOpen (hζ : ContDiff ℝ ∞ ζ) :
    IsOpen (positiveExitFermiLabelDomain e ζ) := by
  let N : Set Coord := {q | 0 < fermiNormalMap ζ q 2}
  have hN : IsOpen N := isOpen_lt continuous_const
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) 2).continuous.comp
      (fermiNormalMap_contDiff hζ).continuous)
  exact (positiveExitFermiSource_contDiffOn (V := N) hζ (fun _ hq => hq)).continuousOn.isOpen_inter_preimage
    hN e.open_target

theorem positiveExitFermiLabel_contDiffOn
    (hζ : ContDiff ℝ ∞ ζ)
    (heI : ContMDiffOn 𝓘(ℝ, Coord) nativeProductModel ∞ e.symm e.target) :
    ContDiffOn ℝ ∞ (positiveExitFermiLabel d hb e ζ) (positiveExitFermiLabelDomain e ζ) :=
  (positiveExitCartesianLabel_contDiffOn d hb e heI).comp
    (positiveExitFermiSource_contDiffOn hζ (fun _ hq => hq.1)) (fun _ hq => hq.2)

/-- Periodicity is literal equality of the actual Fermi source, so even the
chosen total inverse extension gives the same endpoint label. -/
theorem positiveExitFermiLabel_periodic {P : ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (hζP : Function.Periodic ζ P) :
    FermiPeriodic P (positiveExitFermiLabel d hb e ζ) := by
  intro q
  simp only [positiveExitFermiLabel, Function.comp_apply,
    positiveExitFermiSource_periodic hζ hζP q]

theorem positiveExitFermiLabel_endpoint_periodic {P : ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (hζP : Function.Periodic ζ P) (x : ℝ) :
    positiveExitFermiLabel d hb e ζ (![P, x] : Coord) =
      positiveExitFermiLabel d hb e ζ (![0, x] : Coord) := by
  have hh := ((fermiPeriodic_iff_slices P _).mp (positiveExitFermiLabel_periodic d hb e hζ hζP)) x 0
  simpa only [zero_add] using hh

/-- Actual Fermi rank and actual Cartesian label rank imply nonzero label
functional everywhere on the actual regular northern inverse-image domain. -/
theorem positiveExitFermiLabel_fderiv_ne_zero
    (heS : e.source = univ)
    (heD : ContMDiff nativeProductModel 𝓘(ℝ, Coord) ∞ e)
    (heI : ContMDiffOn 𝓘(ℝ, Coord) nativeProductModel ∞ e.symm e.target)
    (hζ : ContDiff ℝ ∞ ζ) (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1)
    {q : Coord} (hq : q ∈ positiveExitFermiLabelDomain e ζ)
    (hscale : fermiNormalScale (normalLoopCurvature ζ) q ≠ 0) :
    fderiv ℝ (positiveExitFermiLabel d hb e ζ) q ≠ 0 := by
  let V := positiveExitFermiLabelDomain e ζ
  let P := positiveExitFermiSource ζ
  have hV : IsOpen V := positiveExitFermiLabelDomain_isOpen e hζ
  have hP : ContDiffOn ℝ ∞ P V := positiveExitFermiSource_contDiffOn hζ (fun _ hp => hp.1)
  have hdP := ((hP q hq).contDiffAt (hV.mem_nhds hq)).differentiableAt (by simp)
  have hnorm := positiveExitFermi_normal_eq hζ hunit hspeed (fun _ hp => hp.1 : ∀ p ∈ V, 0 < fermiNormalMap ζ p 2)
  have hn := (hnorm.eventuallyEq_of_mem (hV.mem_nhds hq)).fderiv_eq (𝕜 := ℝ)
  have hN : fderiv ℝ (fermiNormalMap ζ) q =
      (fderiv ℝ planarUnitNormal (P q)).comp (fderiv ℝ P q) := by
    rw [← hn]
    exact fderiv_comp q (gnomonicNormal_contDiff.differentiable (by simp) _) hdP
  have hiN := positiveExitFermi_raw_differential_injective hζ hunit hspeed q hscale
  have hiP : Function.Injective (fderiv ℝ P q) := by
    intro v z hvz
    apply hiN
    rw [hN]
    simp only [ContinuousLinearMap.comp_apply, hvz]
  have hsP : Function.Surjective (fderiv ℝ P q) :=
    (LinearMap.injective_iff_surjective (f := (fderiv ℝ P q).toLinearMap)).mp hiP
  have hL := positiveExitCartesianLabel_contDiffOn d hb e heI
  have hdL := ((hL _ hq.2).contDiffAt (e.open_target.mem_nhds hq.2)).differentiableAt (by simp)
  have hD := fderiv_comp q hdL hdP
  intro hz
  apply positiveExitCartesianLabel_fderiv_ne_zero d hb e heS heD heI hq.2
  ext v
  obtain ⟨z, rfl⟩ := hsP v
  have hh := congrArg (fun D => D z) hD
  change fderiv ℝ (positiveExitFermiLabel d hb e ζ) q z =
    fderiv ℝ (positiveExitCartesianLabel d hb e) (P q) (fderiv ℝ P q z) at hh
  rw [hz, ContinuousLinearMap.zero_apply] at hh
  exact hh.symm

/-- The same selected actual leaf, with any actual reparametrization ψ,
has the same actual first-integral label on the Fermi seam. -/
theorem positiveExitFermiLabel_selected_seam {δ : ℝ}
    (heS : e.source = univ)
    (heF : ∀ p, e p = gnomonicInverse (d.bandGaussMap p))
    (hinside : ∀ u ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 u t ∈ Ioo 0 w)
    (v : Ioo (0 : ℝ) δ) (ψ : ℝ → ℝ)
    (hζeq : ∀ r, ζ r = positiveExitRawLeaf d hb hinside v (ψ r)) (r : ℝ) :
    positiveExitFermiLabel d hb e ζ (![r, 0] : Coord) =
      1 / (ruledRho d.τ 0 * (v : ℝ)) - ruledOmega d.k d.τ 0 := by
  let p := positiveExitLeaf d hb hinside v (periodProjection T (ψ r))
  have heq : positiveExitFermiSource ζ (![r, 0] : Coord) = e p := by
    simp only [positiveExitFermiSource, fermiNormalMap, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Real.cos_zero, Real.sin_zero,
      one_smul, zero_smul, add_zero]
    rw [hζeq r, heF p]
    rfl
  change positiveExitLevel d hb (e.symm (positiveExitFermiSource ζ ![r, 0])) = _
  rw [heq, e.left_inv (by rw [heS]; exact mem_univ p)]
  exact positiveExitLevel_identityFlowBandInclusion d hb hinside
    (periodProjection T (ψ r), v)

/-- The full actual label functional is nonzero and its selected-seam
longitudinal derivative is zero; therefore its Fermi transverse derivative
is nonzero, without a transversality premise. -/
theorem positiveExitFermiLabel_selected_transverse {δ : ℝ}
    (heS : e.source = univ)
    (heF : ∀ p, e p = gnomonicInverse (d.bandGaussMap p))
    (heD : ContMDiff nativeProductModel 𝓘(ℝ, Coord) ∞ e)
    (heI : ContMDiffOn 𝓘(ℝ, Coord) nativeProductModel ∞ e.symm e.target)
    (hζ : ContDiff ℝ ∞ ζ) (hunit : ∀ s, inner ℝ (ζ s) (ζ s) = 1)
    (hspeed : ∀ s, inner ℝ (deriv ζ s) (deriv ζ s) = 1)
    (hinside : ∀ u ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 u t ∈ Ioo 0 w)
    (v : Ioo (0 : ℝ) δ) (ψ : ℝ → ℝ)
    (hζeq : ∀ s, ζ s = positiveExitRawLeaf d hb hinside v (ψ s))
    {r : ℝ} (hr : (![r, 0] : Coord) ∈ positiveExitFermiLabelDomain e ζ) :
    coordPartial 0 (positiveExitFermiLabel d hb e ζ) ![r, 0] = 0 ∧
      coordPartial 1 (positiveExitFermiLabel d hb e ζ) ![r, 0] ≠ 0 := by
  let C := positiveExitFermiLabel d hb e ζ
  have hV := positiveExitFermiLabelDomain_isOpen e hζ
  have hC := positiveExitFermiLabel_contDiffOn d hb e hζ heI
  have hconst : (fun s : ℝ => C ![s, 0]) =
      (fun _ : ℝ => 1 / (ruledRho d.τ 0 * (v : ℝ)) - ruledOmega d.k d.τ 0) :=
    funext (positiveExitFermiLabel_selected_seam d hb e heS heF hinside v ψ hζeq)
  have hzero : coordPartial 0 C ![r, 0] = 0 := by
    have hd := scalarFlowPeriod_slice0_hasDerivAt hV hC hr
    rw [hconst] at hd
    exact hd.unique (hasDerivAt_const r _)
  refine ⟨hzero, ?_⟩
  have hscale : fermiNormalScale (normalLoopCurvature ζ) (![r, 0] : Coord) ≠ 0 := by
    simp [fermiNormalScale]
  intro h1
  apply positiveExitFermiLabel_fderiv_ne_zero d hb e heS heD heI hζ hunit hspeed hr hscale
  ext z
  rw [fderiv_two_scalar_coordinates, hzero, h1]
  simp

end
end TightVer401
