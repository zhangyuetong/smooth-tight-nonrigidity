import TightVer401.PositiveExitConstructionLabel
import TightVer401.PositiveExitConstructionReturn
import TightVer401.SeamCompactCollar

/-! The actual first-integral kernel is an asymptotic line of the same ruled
band. Its pullback selects the retained positive mixed-entry Fermi root near
the seam. No conservation or return-identity package is assumed. -/
open scoped Manifold
namespace TightVer401
noncomputable section
open Set Filter MeasureTheory OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The positive mixed branch is the quadratic root whose normal derivative
M + N*t is positive. Positivity of M also keeps the rational denominator nonzero. -/
theorem positiveExit_quadratic_root_identification {L M N t : ℝ}
    (hM : 0 < M) (hbranch : 0 < M + N * t)
    (hroot : L + 2 * M * t + N * t ^ 2 = 0) :
    -L / (M + Real.sqrt (M ^ 2 - L * N)) = t := by
  have hqt : 2 * M * t + N * t ^ 2 = -L := by linarith
  have hrad : M ^ 2 - L * N = (M + N * t) ^ 2 := by
    calc
      M ^ 2 - L * N = M ^ 2 + N * (-L) := by ring
      _ = M ^ 2 + N * (2 * M * t + N * t ^ 2) := by rw [hqt]
      _ = (M + N * t) ^ 2 := by ring
  have hs : Real.sqrt (M ^ 2 - L * N) = M + N * t := by
    rw [hrad, Real.sqrt_sq_eq_abs, abs_of_pos hbranch]
  have hden : M + (M + N * t) ≠ 0 := (add_pos hM hbranch).ne'
  rw [hs, div_eq_iff hden]
  nlinarith [hroot]

/-- Every actual raw tangent annihilated by the actual first integral is
asymptotic for the actual ruled immersion and its actual Gauss map. -/
theorem positiveExitRawFirstIntegral_kernel_pairing {T : ℝ}
    (d : PeriodicRuledFrame T) {q : Coord} (hq : 0 < q 1) (v : Coord)
    (hv : fderiv ℝ (positiveExitRawFirstIntegral d) q v = 0) :
    inner ℝ (fderiv ℝ (ruledMap d.γ d.E) q v)
      (fderiv ℝ d.rawGaussMap q v) = 0 := by
  have hρ := (ruledRho_pos (d.torsion_ne_zero (q 0))).ne'
  rw [fderiv_two_scalar_coordinates,
    (positiveExitRawFirstIntegral_partials d q hq).1,
    (positiveExitRawFirstIntegral_partials d q hq).2] at hv
  have hline : q 1 * (ruledLambda d.τ (q 0) + q 1 * ruledD d.k d.τ (q 0)) * v 0 +
      2 * v 1 = 0 := by
    field_simp [hρ, hq.ne'] at hv
    nlinarith [hv]
  rw [identityBand_interior_differential_pairing]
  have hnum : q 1 * d.τ (q 0) *
      (ruledLambda d.τ (q 0) + q 1 * ruledD d.k d.τ (q 0)) * v 0 * v 0 +
      d.τ (q 0) * (v 0 * v 1 + v 1 * v 0) = 0 := by
    calc
      _ = d.τ (q 0) * v 0 *
        (q 1 * (ruledLambda d.τ (q 0) + q 1 * ruledD d.k d.τ (q 0)) * v 0 +
          2 * v 1) := by ring
      _ = 0 := by rw [hline]; ring
  rw [hnum]
  simp

variable {T w : ℝ} [Fact (0 < T)] (d : PeriodicRuledFrame T)
  (hb : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0)

/-- The genuine quotient chart transports the actual kernel identity to all
native band tangents; surjectivity comes from the retained chart derivative. -/
theorem positiveExitLevel_kernel_pairing (p : AddCircle T × Ioo (0 : ℝ) w)
    (v : ℝ × ℝ)
    (hv : mfderiv nativeProductModel 𝓘(ℝ, ℝ) (positiveExitLevel d hb) p v = 0) :
    inner ℝ (bandDifferential d.bandMap p v) (bandDifferential d.bandGaussMap p v) = 0 := by
  obtain ⟨r, hr⟩ := QuotientAddGroup.mk_surjective p.1
  let q : coordinateBandOpen w := ⟨![r, (p.2 : ℝ)], p.2.property⟩
  have hq : bandFromCoordinates T w q = p := Prod.ext hr (Subtype.ext rfl)
  obtain ⟨z, hz⟩ := periodicRuledFrame_coordinate_differential_surjective d q v
  have hX : ContDiff ℝ ∞ (ruledMap d.γ d.E) :=
    (d.smooth_γ.comp (contDiff_apply ℝ ℝ (0 : Fin 2))).add
      ((contDiff_apply ℝ ℝ (1 : Fin 2)).smul (d.smooth_E.comp (contDiff_apply ℝ ℝ (0 : Fin 2))))
  have hrawX : openCoordinateDifferential (d.bandMap ∘ bandFromCoordinates T w) q =
      fderiv ℝ (ruledMap d.γ d.E) q.val :=
    openCoordinate_restriction_derivative q (hX.differentiable (by simp) q.val)
  have hDX : fderiv ℝ (ruledMap d.γ d.E) q.val =
      (bandDifferential d.bandMap (bandFromCoordinates T w q)).comp
        (bandFromCoordinatesDifferential T w q) := by
    rw [← hrawX]
    exact mfderiv_comp q ((d.bandMap_contMDiff _).mdifferentiableAt (by simp))
      ((bandFromCoordinates_contMDiff T w q).mdifferentiableAt (by simp))
  have hrawN : openCoordinateDifferential (d.bandGaussMap ∘ bandFromCoordinates T w) q =
      fderiv ℝ d.rawGaussMap q.val :=
    openCoordinate_restriction_derivative q
      ((periodicRuledFrame_rawGaussMap_contDiff d).differentiable (by simp) q.val)
  have hDN : fderiv ℝ d.rawGaussMap q.val =
      (bandDifferential d.bandGaussMap (bandFromCoordinates T w q)).comp
        (bandFromCoordinatesDifferential T w q) := by
    rw [← hrawN]
    exact mfderiv_comp q ((periodicRuledFrame_bandGaussMap_contMDiff d _).mdifferentiableAt (by simp))
      ((bandFromCoordinates_contMDiff T w q).mdifferentiableAt (by simp))
  have hrep : positiveExitLevel d hb ∘ bandFromCoordinates T w =
      (fun x : coordinateBandOpen w => positiveExitRawFirstIntegral d x.val) := by
    funext x
    exact (positiveExitRawFirstIntegral_native_label d hb (x.val 0)
      (⟨x.val 1, x.property⟩ : Ioo (0 : ℝ) w)).symm
  have hdC : DifferentiableAt ℝ (positiveExitRawFirstIntegral d) q.val :=
    ((positiveExitRawFirstIntegral_contDiffOn d) q.val q.property.1).contDiffAt
      ((isOpen_lt continuous_const (continuous_apply 1)).mem_nhds q.property.1)
      |>.differentiableAt (by simp)
  have hval : MDifferentiableAt 𝓘(ℝ, Coord) 𝓘(ℝ, Coord)
      (Subtype.val : coordinateBandOpen w → Coord) q :=
    (contMDiff_subtype_val (n := ∞) q).mdifferentiableAt (by simp)
  have hres : (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, ℝ)
      (fun x : coordinateBandOpen w => positiveExitRawFirstIntegral d x.val) q : Coord →L[ℝ] ℝ) =
      (fderiv ℝ (positiveExitRawFirstIntegral d) q.val).comp
        (openCoordinateInclusionDifferential (coordinateBandOpen w) q) :=
    (hdC.hasFDerivAt.hasMFDerivAt.comp q hval.hasMFDerivAt).mfderiv
  rw [openCoordinate_inclusion_derivative, ContinuousLinearMap.comp_id] at hres
  have hDC := mfderiv_comp q
    ((positiveExitLevel_contMDiff d hb _).mdifferentiableAt (by simp))
    ((bandFromCoordinates_contMDiff T w q).mdifferentiableAt (by simp))
  rw [hrep, hres] at hDC
  have hcz : fderiv ℝ (positiveExitRawFirstIntegral d) q.val z = 0 := by
    rw [hDC]
    change (mfderiv nativeProductModel 𝓘(ℝ, ℝ) (positiveExitLevel d hb)
      (bandFromCoordinates T w q) : (ℝ × ℝ) →L[ℝ] ℝ)
        (bandFromCoordinatesDifferential T w q z) = (0 : ℝ)
    rw [hq, hz]
    change (mfderiv nativeProductModel 𝓘(ℝ, ℝ) (positiveExitLevel d hb) p :
      (ℝ × ℝ) →L[ℝ] ℝ) v = (0 : ℝ) at hv
    exact hv
  have hpair := positiveExitRawFirstIntegral_kernel_pairing d q.property.1 z hcz
  rw [hDX, hDN] at hpair
  simpa only [ContinuousLinearMap.comp_apply, hq, hz] using hpair

/-- Actual inverse-coordinate transport. Reconstruction and normal identities
are ordinary identities of the SAME support chart, not a null-line premise. -/
theorem positiveExitFermiLabel_kernel_tensor
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) Coord)
    {ζ : ℝ → Ambient} {G : Coord → ℝ} {V : Set Coord}
    (heF : ∀ p, e p = gnomonicInverse (d.bandGaussMap p))
    (heI : ContMDiffOn 𝓘(ℝ, Coord) nativeProductModel ∞ e.symm e.target)
    (hbandNorth : ∀ p : AddCircle T × Ioo (0 : ℝ) w, 0 < d.bandGaussMap p 2)
    (hrec : ∀ p : AddCircle T × Ioo (0 : ℝ) w, planarSupportMap G (e p) = d.bandMap p)
    (hG : ContDiffOn ℝ ∞ G e.target)
    (hV : IsOpen V) (hVDom : V ⊆ positiveExitFermiLabelDomain e ζ)
    (hζ : ContDiff ℝ ∞ ζ) (hunit : ∀ s, inner ℝ (ζ s) (ζ s) = 1)
    (hspeed : ∀ s, inner ℝ (deriv ζ s) (deriv ζ s) = 1)
    {q : Coord} (hq : q ∈ V)
    (hscale : ∀ p ∈ V,
      fermiNormalScale (normalLoopCurvature ζ) p ≠ 0)
    (v : Coord) (hv : fderiv ℝ (positiveExitFermiLabel d hb e ζ) q v = 0) :
    v ⬝ᵥ (sphereSupportTensor (inducedMetric (fermiNormalMap ζ))
      (positiveExitFermiHeight G ζ) q *ᵥ v) = 0 := by
  let P := positiveExitFermiSource ζ
  let A : Coord → AddCircle T × Ioo (0 : ℝ) w := e.symm ∘ P
  let X := d.bandMap ∘ A
  let N := d.bandGaussMap ∘ A
  have hP : ContDiffOn ℝ ∞ P V := positiveExitFermiSource_contDiffOn hζ (fun _ hp => (hVDom hp).1)
  have hPU : MapsTo P V e.target := fun _ hp => (hVDom hp).2
  have hA : ContMDiffOn 𝓘(ℝ, Coord) nativeProductModel ∞ A V :=
    heI.comp hP.contMDiffOn hPU
  have hdA := ((hA q hq).contMDiffAt (hV.mem_nhds hq)).mdifferentiableAt (by simp)
  have hDC := mfderiv_comp q
    ((positiveExitLevel_contMDiff d hb (A q)).mdifferentiableAt (by simp)) hdA
  have hDX := mfderiv_comp q ((d.bandMap_contMDiff (A q)).mdifferentiableAt (by simp)) hdA
  have hDN := mfderiv_comp q
    ((periodicRuledFrame_bandGaussMap_contMDiff d (A q)).mdifferentiableAt (by simp)) hdA
  rw [mfderiv_eq_fderiv] at hDC hDX hDN
  change fderiv ℝ X q = (bandDifferential d.bandMap (A q)).comp
    (mfderiv 𝓘(ℝ, Coord) nativeProductModel A q) at hDX
  change fderiv ℝ N q = (bandDifferential d.bandGaussMap (A q)).comp
    (mfderiv 𝓘(ℝ, Coord) nativeProductModel A q) at hDN
  have hcv : mfderiv nativeProductModel 𝓘(ℝ, ℝ) (positiveExitLevel d hb) (A q)
      (mfderiv 𝓘(ℝ, Coord) nativeProductModel A q v) = 0 := by
    change (mfderiv nativeProductModel 𝓘(ℝ, ℝ) (positiveExitLevel d hb) (A q) :
      (ℝ × ℝ) →L[ℝ] ℝ) (mfderiv 𝓘(ℝ, Coord) nativeProductModel A q v) = (0 : ℝ)
    have hh := congrArg (fun D => D v) hDC
    change fderiv ℝ (positiveExitFermiLabel d hb e ζ) q v =
      (mfderiv nativeProductModel 𝓘(ℝ, ℝ) (positiveExitLevel d hb) (A q) :
        (ℝ × ℝ) →L[ℝ] ℝ) (mfderiv 𝓘(ℝ, Coord) nativeProductModel A q v) at hh
    rw [← hh]
    exact hv
  have hpair := positiveExitLevel_kernel_pairing d hb (A q)
    (mfderiv 𝓘(ℝ, Coord) nativeProductModel A q v) hcv
  have hpair' : inner ℝ (fderiv ℝ X q v) (fderiv ℝ N q v) = 0 := by
    rw [hDX, hDN]
    exact hpair
  have hrecV : EqOn (planarSupportMap G ∘ P) X V := by
    intro p hp
    change planarSupportMap G (P p) = d.bandMap (A p)
    calc
      _ = planarSupportMap G (e (A p)) :=
        congrArg (planarSupportMap G) (e.right_inv ((hVDom hp).2)).symm
      _ = _ := hrec (A p)
  have hnormV : EqOn (planarUnitNormal ∘ P) N V := by
    intro p hp
    change planarUnitNormal (P p) = d.bandGaussMap (A p)
    calc
      _ = planarUnitNormal (e (A p)) :=
        congrArg planarUnitNormal (e.right_inv ((hVDom hp).2)).symm
      _ = planarUnitNormal (gnomonicInverse (d.bandGaussMap (A p))) := by rw [heF]
      _ = _ := identityBand_bandGauss_planarUnitNormal d (A p) (hbandNorth (A p))
  have hcart := identityBand_cartesian_pullback_pairing hG e.open_target hV hP hPU
    hrecV hnormV hq v v
  have hfermi := positiveExitFermi_tensor_pairing hζ hunit hspeed hG e.open_target hV
    (fun _ hp => (hVDom hp).1) hscale hPU hq v v
  exact hfermi.trans (hcart.symm.trans hpair')

/-- Scalar kernel polynomial obtained from the actual tensor correspondence. -/
theorem positiveExitFermiLabel_kernel_polynomial
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) Coord)
    {ζ : ℝ → Ambient} {G : Coord → ℝ} {V : Set Coord}
    (heF : ∀ p, e p = gnomonicInverse (d.bandGaussMap p))
    (heI : ContMDiffOn 𝓘(ℝ, Coord) nativeProductModel ∞ e.symm e.target)
    (hbandNorth : ∀ p : AddCircle T × Ioo (0 : ℝ) w, 0 < d.bandGaussMap p 2)
    (hrec : ∀ p : AddCircle T × Ioo (0 : ℝ) w, planarSupportMap G (e p) = d.bandMap p)
    (hG : ContDiffOn ℝ ∞ G e.target)
    (hV : IsOpen V) (hVDom : V ⊆ positiveExitFermiLabelDomain e ζ)
    (hζ : ContDiff ℝ ∞ ζ) (hunit : ∀ s, inner ℝ (ζ s) (ζ s) = 1)
    (hspeed : ∀ s, inner ℝ (deriv ζ s) (deriv ζ s) = 1)
    {q : Coord} (hq : q ∈ V)
    (hscale : ∀ p ∈ V,
      fermiNormalScale (normalLoopCurvature ζ) p ≠ 0) :
    let C := positiveExitFermiLabel d hb e ζ
    let H := positiveExitFermiHeight G ζ
    let κ := normalLoopCurvature ζ
    fermiSupportL κ H q * (coordPartial 1 C q)^2 -
      2 * fermiSupportM κ H q * coordPartial 0 C q * coordPartial 1 C q +
      fermiSupportN H q * (coordPartial 0 C q)^2 = 0 := by
  let C := positiveExitFermiLabel d hb e ζ
  let H := positiveExitFermiHeight G ζ
  let κ := normalLoopCurvature ζ
  let v : Coord := ![coordPartial 1 C q, -coordPartial 0 C q]
  have hv : fderiv ℝ C q v = 0 := by
    rw [fderiv_two_scalar_coordinates]
    simp only [v, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    ring
  have hp := positiveExitFermiLabel_kernel_tensor d hb e heF heI hbandNorth hrec hG hV hVDom
    hζ hunit hspeed hq hscale v hv
  have hκ : ContDiff ℝ ∞ κ := (normalLoop_actual_smooth hζ).2
  have hH := positiveExitFermiHeight_contDiffOn hζ hG (fun _ hp => (hVDom hp).1) (fun _ hp => (hVDom hp).2 : MapsTo (positiveExitFermiSource ζ) V e.target)
  have hg : SmoothPositiveOn (fermiMetric (fermiNormalScale κ)) V :=
    fermiMetric_smoothPositiveOn (fermiNormalScale_contDiff hκ) hscale
  have hsym := sphereSupportTensor_symm hg hH hV hq 1 0
  rw [fermiNormalMap_inducedMetric hζ hunit hspeed] at hp
  obtain ⟨h00, h01, h11⟩ := fermiSupport_actual_entries hκ H (hscale q hq)
  change v ⬝ᵥ (sphereSupportTensor (fermiMetric (fermiNormalScale κ)) H q *ᵥ v) = 0 at hp
  change sphereSupportTensor (fermiMetric (fermiNormalScale κ)) H q 1 0 =
    sphereSupportTensor (fermiMetric (fermiNormalScale κ)) H q 0 1 at hsym
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, v,
    Matrix.cons_val_zero, Matrix.cons_val_one] at hp
  rw [hsym, h00, h01, h11] at hp
  change fermiSupportL κ H q * (coordPartial 1 C q)^2 -
    2 * fermiSupportM κ H q * coordPartial 0 C q * coordPartial 1 C q +
    fermiSupportN H q * (coordPartial 0 C q)^2 = 0
  nlinarith [hp]

/-- A regular label kernel selects the actual rational Fermi root pointwise. -/
theorem positiveExit_label_chosen_root {C L M N : Coord → ℝ} {q : Coord}
    (h1 : coordPartial 1 C q ≠ 0) (hM : 0 < M q)
    (hb : 0 < M q + N q * (-coordPartial 0 C q / coordPartial 1 C q))
    (hQ : L q * (coordPartial 1 C q)^2 -
      2 * M q * coordPartial 0 C q * coordPartial 1 C q +
      N q * (coordPartial 0 C q)^2 = 0) :
    fderiv ℝ C q (![1, fermiAsymptoticSlope L M N q] : Coord) = 0 := by
  have hroot : L q + 2 * M q * (-coordPartial 0 C q / coordPartial 1 C q) +
      N q * (-coordPartial 0 C q / coordPartial 1 C q)^2 = 0 := by
    field_simp [h1]
    nlinarith [hQ]
  have hs := positiveExit_quadratic_root_identification hM hb hroot
  rw [fderiv_two_scalar_coordinates]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_mul,
    fermiAsymptoticSlope, hs]
  field_simp [h1]
  <;> ring

/-- Construct an actual open branch neighborhood and a uniform thin strip
around a compact seam. The null polynomial is the proved actual tensor
identity above; no conserved-flow or return witness is an input. -/
theorem positiveExit_label_chosen_root_collar {C L M N : Coord → ℝ} {U : Set Coord}
    {P : ℝ} (hU : IsOpen U) (hC : ContDiffOn ℝ ∞ C U)
    (hM : ContDiffOn ℝ ∞ M U) (hN : ContDiffOn ℝ ∞ N U)
    (hseam : ∀ r : ℝ, (![r, 0] : Coord) ∈ U)
    (hzero : ∀ r : ℝ, coordPartial 0 C ![r, 0] = 0)
    (h1 : ∀ r : ℝ, coordPartial 1 C ![r, 0] ≠ 0)
    (hpos : ∀ r : ℝ, 0 < M ![r, 0])
    (hQ : ∀ q ∈ U, L q * (coordPartial 1 C q)^2 -
      2 * M q * coordPartial 0 C q * coordPartial 1 C q +
      N q * (coordPartial 0 C q)^2 = 0) :
    ∃ W : Set Coord, IsOpen W ∧ W ⊆ U ∧
      (∀ r : ℝ, (![r, 0] : Coord) ∈ W) ∧
      (∀ q ∈ W, fderiv ℝ C q (![1, fermiAsymptoticSlope L M N q] : Coord) = 0) ∧
      ∃ ε > 0, ∀ r ∈ Icc (0 : ℝ) P, ∀ t : ℝ,
        |t| ≤ ε → (![r, t] : Coord) ∈ W := by
  let U1 := U ∩ (coordPartial 1 C) ⁻¹' ({0}ᶜ : Set ℝ)
  have hU1 : IsOpen U1 := (partial_contDiffOn hC hU 1).continuousOn.isOpen_inter_preimage
    hU isClosed_singleton.isOpen_compl
  have h10 : ∀ q ∈ U1, coordPartial 1 C q ≠ 0 := fun _ hq => hq.2
  let B : Coord → ℝ := fun q => M q + N q * (-coordPartial 0 C q / coordPartial 1 C q)
  have hB : ContDiffOn ℝ ∞ B U1 := (hM.mono inter_subset_left).add
    ((hN.mono inter_subset_left).mul
      (((partial_contDiffOn hC hU 0).mono inter_subset_left).neg.div
        ((partial_contDiffOn hC hU 1).mono inter_subset_left) h10))
  let U2 := U1 ∩ M ⁻¹' Ioi 0
  have hU2 : IsOpen U2 := (hM.mono inter_subset_left).continuousOn.isOpen_inter_preimage hU1 isOpen_Ioi
  let W := U2 ∩ B ⁻¹' Ioi 0
  have hW : IsOpen W := (hB.mono inter_subset_left).continuousOn.isOpen_inter_preimage hU2 isOpen_Ioi
  have hWU : W ⊆ U := fun _ hq => hq.1.1.1
  have hWs : ∀ r : ℝ, (![r, 0] : Coord) ∈ W := by
    intro r
    refine ⟨⟨⟨hseam r, h1 r⟩, hpos r⟩, ?_⟩
    change 0 < M ![r, 0] + N ![r, 0] * (-coordPartial 0 C ![r, 0] / coordPartial 1 C ![r, 0])
    simpa only [hzero r, neg_zero, zero_div, mul_zero, add_zero] using hpos r
  refine ⟨W, hW, hWU, hWs, ?_, ?_⟩
  · intro q hq
    exact positiveExit_label_chosen_root hq.1.1.2 hq.1.2 hq.2 (hQ q (hWU hq))
  · exact seam_compact_axis_open_collar isCompact_Icc hW (fun r _ => hWs r)

/-- Consumer export for `exists_positive_exits_fixed_core`: on an actually
constructed open seam neighborhood, the retained chosen Fermi branch
annihilates the actual label of the SAME d, G, inverse e and selected leaf.
The seam label facts are derived from that selected leaf, and the null tensor
identity is derived from the actual raw first integral above. -/
theorem positiveExitFermiLabel_selected_chosen_root_collar
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) Coord)
    {ζ : ℝ → Ambient} {G : Coord → ℝ} {V : Set Coord} {δ P : ℝ}
    (heS : e.source = univ)
    (heF : ∀ p, e p = gnomonicInverse (d.bandGaussMap p))
    (heD : ContMDiff nativeProductModel 𝓘(ℝ, Coord) ∞ e)
    (heI : ContMDiffOn 𝓘(ℝ, Coord) nativeProductModel ∞ e.symm e.target)
    (hbandNorth : ∀ p : AddCircle T × Ioo (0 : ℝ) w, 0 < d.bandGaussMap p 2)
    (hrec : ∀ p : AddCircle T × Ioo (0 : ℝ) w, planarSupportMap G (e p) = d.bandMap p)
    (hG : ContDiffOn ℝ ∞ G e.target)
    (hV : IsOpen V) (hVDom : V ⊆ positiveExitFermiLabelDomain e ζ)
    (hζ : ContDiff ℝ ∞ ζ) (hunit : ∀ s, inner ℝ (ζ s) (ζ s) = 1)
    (hspeed : ∀ s, inner ℝ (deriv ζ s) (deriv ζ s) = 1)
    (hinside : ∀ u ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 u t ∈ Ioo 0 w)
    (v : Ioo (0 : ℝ) δ) (ψ : ℝ → ℝ)
    (hζeq : ∀ s, ζ s = positiveExitRawLeaf d hb hinside v (ψ s))
    (hseam : ∀ r : ℝ, (![r, 0] : Coord) ∈ V)
    (hscale : ∀ q ∈ V,
      fermiNormalScale (normalLoopCurvature ζ) q ≠ 0)
    (hM : ∀ r : ℝ, 0 < fermiSupportM (normalLoopCurvature ζ)
      (positiveExitFermiHeight G ζ) ![r, 0]) :
    ∃ W : Set Coord, IsOpen W ∧ W ⊆ V ∧
      (∀ r : ℝ, (![r, 0] : Coord) ∈ W) ∧
      (∀ q ∈ W, fderiv ℝ (positiveExitFermiLabel d hb e ζ) q
        (![1, fermiSupportAsymptoticSlope (normalLoopCurvature ζ)
          (positiveExitFermiHeight G ζ) q] : Coord) = 0) ∧
      ∃ ε > 0, ∀ r ∈ Icc (0 : ℝ) P, ∀ t : ℝ,
        |t| ≤ ε → (![r, t] : Coord) ∈ W := by
  let C := positiveExitFermiLabel d hb e ζ
  let H := positiveExitFermiHeight G ζ
  let κ := normalLoopCurvature ζ
  let U := V
  have hU : IsOpen U := hV
  have hC : ContDiffOn ℝ ∞ C U := (positiveExitFermiLabel_contDiffOn d hb e hζ heI).mono hVDom
  have hH : ContDiffOn ℝ ∞ H U := positiveExitFermiHeight_contDiffOn hζ hG
    (fun _ hq => (hVDom hq).1) (fun _ hq => (hVDom hq).2)
  have hκ : ContDiff ℝ ∞ κ := (normalLoop_actual_smooth hζ).2
  obtain ⟨hL, hMixed, hN⟩ := fermiSupport_contDiffOn hκ hU hH hscale
  have hseamData (r : ℝ) := positiveExitFermiLabel_selected_transverse d hb e
    heS heF heD heI hζ hunit hspeed hinside v ψ hζeq (hVDom (hseam r))
  have hQ : ∀ q ∈ U, fermiSupportL κ H q * (coordPartial 1 C q)^2 -
      2 * fermiSupportM κ H q * coordPartial 0 C q * coordPartial 1 C q +
      fermiSupportN H q * (coordPartial 0 C q)^2 = 0 := by
    intro q hq
    exact positiveExitFermiLabel_kernel_polynomial d hb e heF heI hbandNorth hrec hG hV hVDom
      hζ hunit hspeed hq hscale
  exact positiveExit_label_chosen_root_collar (P := P) hU hC hMixed hN hseam
    (fun r => (hseamData r).1) (fun r => (hseamData r).2) hM hQ

end
end TightVer401