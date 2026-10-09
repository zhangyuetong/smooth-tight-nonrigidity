import TightVer401.VisibleConnectorRuledCoordinates
import TightVer401.AngularDescentCharts
import TightVer401.CorrugatedSeedVisiblePairs

/-! The actual unit tangent/transverse pair for a visible Cartesian exit.
The coefficients are those of the actual ruled connector at η=0. No angle
lift, annular inverse, turn, or global connector is assumed or constructed. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

def visibleConnectorTangentDirection (R : ℝ) (gamma : ℝ → Coord) (s : ℝ) : Coord :=
  let z := corrugatedVisibilityDirection R (Complex.I * angularDescentComplex (gamma s))
  ![z.re,z.im]

def visibleConnectorTangentTransverse (R : ℝ) (gamma : ℝ → Coord) (s : ℝ) : Coord :=
  -visibleConnectorJ (visibleConnectorTangentDirection R gamma s)

private theorem visibleConnector_complex_curve_deriv {p : ℝ → Coord}
    (hp : ContDiff ℝ ∞ p) (s : ℝ) :
    deriv (angularDescentComplex ∘ p) s = angularDescentComplex (deriv p s) := by
  have hd := (hp.differentiable (by simp) s).hasDerivAt
  have h0 := (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)).hasFDerivAt.comp_hasDerivAt s hd
  have h1 := (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2)).hasFDerivAt.comp_hasDerivAt s hd
  have hc := (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt s h0).add
    ((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt s h1).mul_const Complex.I)
  have he : HasDerivAt (angularDescentComplex ∘ p) (angularDescentComplex (deriv p s)) s := hc
  exact he.deriv

private theorem visibleConnector_complex_direction_contDiff {R : ℝ} (hR : 0 < R)
    {δ : ℝ → ℂ} (hδ : ContDiff ℝ ∞ δ) (hr : ∀ s, R < ‖δ s‖) :
    ContDiff ℝ ∞ (fun s => corrugatedVisibilityDirection R (δ s)) := by
  have hN : ContDiff ℝ ∞ (fun s => ‖δ s‖^2) := by
    have hh := ((Complex.reCLM.contDiff.comp hδ).pow 2).add
      ((Complex.imCLM.contDiff.comp hδ).pow 2)
    have he : (fun s : ℝ => ‖δ s‖^2) =
        (fun s : ℝ => (δ s).re^2 + (δ s).im^2) := by
      funext s
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    rw [he]
    exact hh
  have hpos (s : ℝ) : 0 < ‖δ s‖^2 - R^2 := by
    have hs := hr s
    have hn := norm_nonneg (δ s)
    nlinarith
  have hsqrt : ContDiff ℝ ∞ (fun s => Real.sqrt (‖δ s‖^2 - R^2)) :=
    (hN.sub contDiff_const).sqrt (fun s => (hpos s).ne')
  have hden (s : ℝ) : ((‖δ s‖^2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (ne_of_gt (hR.trans (hr s))))
  have hnum : ContDiff ℝ ∞ (fun s : ℝ =>
      ((R : ℂ) + (Real.sqrt (‖δ s‖^2 - R^2) : ℂ) * Complex.I) * δ s) :=
    ((contDiff_const (c := (R : ℂ))).add
      ((Complex.ofRealCLM.contDiff.comp hsqrt).mul (contDiff_const (c := Complex.I)))).mul hδ
  have hdenDiff : ContDiff ℝ ∞ (fun s : ℝ => ((‖δ s‖^2 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hN
  have hinv : ContDiff ℝ ∞ (fun s : ℝ => (((‖δ s‖^2 : ℝ) : ℂ))⁻¹) :=
    hdenDiff.inv hden
  have hprod : ContDiff ℝ ∞ (fun s : ℝ =>
      ((R : ℂ) + (Real.sqrt (‖δ s‖^2 - R^2) : ℂ) * Complex.I) * δ s *
        (((‖δ s‖^2 : ℝ) : ℂ))⁻¹) := hnum.mul hinv
  simpa only [corrugatedVisibilityDirection, div_eq_mul_inv] using hprod

private theorem visibleConnector_complex_direction_support {R : ℝ} (hR : 0 < R)
    {z : ℂ} (hz : R < ‖z‖) : inner ℝ z (corrugatedVisibilityDirection R z) = R := by
  have hn : ‖z‖ ≠ 0 := ne_of_gt (hR.trans hz)
  have hzne : z ≠ 0 := norm_ne_zero_iff.mp hn
  have hsq : z.re^2 + z.im^2 = ‖z‖^2 := by
    simpa only [Complex.normSq_apply,pow_two] using (Complex.sq_norm z).symm
  rw [corrugatedVisibilityDirection_eq hzne]
  simp only [corrugated_complex_inner, corrugatedVisibilityCoefficient, Complex.real_smul,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, mul_one, one_mul]
  field_simp [hn]
  linear_combination R * hsq

/-- The actual direction is smooth and unit in the Euclidean dot product.
`Coord` uses its product norm, so unit length is stated by the actual planar
quadratic form rather than the product norm. Both actual ruled coefficients
are precisely the strictly positive visibility pairings. -/
theorem visibleConnector_tangent_direction_properties {R : ℝ} (hR : 0 < R)
    {p gamma : ℝ → Coord} (hp : ContDiff ℝ ∞ p) (hgamma : ContDiff ℝ ∞ gamma)
    (hvisible : ComplexVisiblePair R (angularDescentComplex ∘ p)
      (fun s => Complex.I * angularDescentComplex (gamma s))) :
    ContDiff ℝ ∞ (visibleConnectorTangentDirection R gamma) ∧
    ContDiff ℝ ∞ (visibleConnectorTangentTransverse R gamma) ∧
    ∀ s, visibleConnectorTangentDirection R gamma s ⬝ᵥ
        visibleConnectorTangentDirection R gamma s = 1 ∧
      visibleConnectorTangentTransverse R gamma s ⬝ᵥ
        visibleConnectorTangentTransverse R gamma s = 1 ∧
      gamma s ⬝ᵥ visibleConnectorTangentTransverse R gamma s = R ∧
      0 < visibleConnectorA p (visibleConnectorTangentTransverse R gamma) s ∧
      0 < visibleConnectorB gamma (visibleConnectorTangentTransverse R gamma) s := by
  let δ : ℝ → ℂ := fun s => Complex.I * angularDescentComplex (gamma s)
  let Z : ℝ → ℂ := fun s => corrugatedVisibilityDirection R (δ s)
  have hδ : ContDiff ℝ ∞ δ := contDiff_const.mul (angularDescentComplex_contDiff.comp hgamma)
  have hZ : ContDiff ℝ ∞ Z := visibleConnector_complex_direction_contDiff hR hδ
    (fun s => (hvisible s).1)
  have hv : ContDiff ℝ ∞ (visibleConnectorTangentDirection R gamma) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · exact Complex.reCLM.contDiff.comp hZ
    · exact Complex.imCLM.contDiff.comp hZ
  have hw : ContDiff ℝ ∞ (visibleConnectorTangentTransverse R gamma) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · change ContDiff ℝ ∞ (fun s : ℝ => -(-(visibleConnectorTangentDirection R gamma s 1)))
      simpa only [neg_neg, Function.comp_def] using ((contDiff_apply ℝ ℝ 1).comp hv)
    · change ContDiff ℝ ∞ (fun s : ℝ => -(visibleConnectorTangentDirection R gamma s 0))
      simpa only [Function.comp_def] using ((contDiff_apply ℝ ℝ 0).comp hv).neg
  refine ⟨hv,hw,?_⟩
  intro s
  have hnorm : ‖Z s‖ = 1 := corrugatedVisibilityDirection_norm hR.le (hvisible s).1
  have hunit : (Z s).re^2 + (Z s).im^2 = 1 := by
    have hh := Complex.sq_norm (Z s)
    simpa only [hnorm,one_pow,Complex.normSq_apply,pow_two,one_mul] using hh.symm
  have hvalue : gamma s ⬝ᵥ visibleConnectorTangentTransverse R gamma s = R := by
    have hh := visibleConnector_complex_direction_support hR (hvisible s).1
    simp [δ,Z,visibleConnectorTangentTransverse,visibleConnectorTangentDirection,
      visibleConnectorJ,corrugated_complex_inner,angularDescentComplex,dotProduct,
      Fin.sum_univ_two,mul_comm] at hh ⊢
    linarith
  have hA : visibleConnectorA p (visibleConnectorTangentTransverse R gamma) s =
      inner ℝ (deriv (angularDescentComplex ∘ p) s) (Z s) := by
    rw [visibleConnector_complex_curve_deriv hp s]
    simp [visibleConnectorA,visibleConnectorDet,visibleConnectorTangentTransverse,
      visibleConnectorJ,visibleConnectorTangentDirection,δ,Z,corrugated_complex_inner,
      angularDescentComplex,dotProduct,Fin.sum_univ_two]
    <;> ring
  have hdδ : deriv δ s = Complex.I * angularDescentComplex (deriv gamma s) := by
    have hh := ((angularDescentComplex_contDiff.comp hgamma).differentiable (by simp) s).hasDerivAt
    change HasDerivAt (angularDescentComplex ∘ gamma) (deriv (angularDescentComplex ∘ gamma) s) s at hh
    rw [visibleConnector_complex_curve_deriv hgamma s] at hh
    have hactual : HasDerivAt δ (Complex.I * angularDescentComplex (deriv gamma s)) s :=
      hh.const_mul Complex.I
    exact hactual.deriv
  have hB : visibleConnectorB gamma (visibleConnectorTangentTransverse R gamma) s =
      inner ℝ (deriv δ s) (Z s) := by
    rw [hdδ]
    simp [visibleConnectorB,visibleConnectorTangentTransverse,visibleConnectorJ,
      visibleConnectorTangentDirection,δ,Z,corrugated_complex_inner,angularDescentComplex,
      dotProduct,Fin.sum_univ_two]
    <;> ring
  refine ⟨?_,?_,hvalue,?_,?_⟩
  · simpa [visibleConnectorTangentDirection,Z,dotProduct,Fin.sum_univ_two,pow_two] using hunit
  · simpa [visibleConnectorTangentTransverse,visibleConnectorTangentDirection,
      visibleConnectorJ,δ,Z,dotProduct,Fin.sum_univ_two,pow_two,add_comm] using hunit
  · rw [hA]
    exact (hvisible s).2.1
  · rw [hB]
    exact (hvisible s).2.2

end
end TightVer401
