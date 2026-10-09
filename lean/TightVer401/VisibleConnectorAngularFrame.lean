import TightVer401.VisibleConnectorContract
import TightVer401.VisibleConnectorTerminalCircle
import TightVer401.PositiveExitConstructionWindingBridge
import TightVer401.CorrugatedSeedVisibilityAngleAlgebra

/-! The actual angular frame of a visible exit. The full shift comes from
its proved positive origin turn; strict angular speed comes from the actual
visibility pairing, by differentiating the actual tangent decomposition. -/
namespace TightVer401
noncomputable section
open Set Function Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

private theorem connectorAngle_complex_eq : positiveExitComplexPoint = angularDescentComplex := by
  funext q
  apply Complex.ext <;> simp [positiveExitComplexPoint, angularDescentComplex]

private theorem connectorAngle_complex_hasDerivAt {f : ℝ → Coord} {v : Coord} {s : ℝ}
    (hf : HasDerivAt f v s) :
    HasDerivAt (positiveExitComplexTrace f) (positiveExitComplexPoint v) s := by
  let C : Coord →L[ℝ] ℂ :=
    Complex.ofRealCLM.comp (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)) +
      Complex.I • (Complex.ofRealCLM.comp (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2)))
  have hC : (C : Coord → ℂ) = positiveExitComplexPoint := by
    funext q
    apply Complex.ext <;> simp [C, positiveExitComplexPoint, Complex.mul_re, Complex.mul_im]
  simpa only [hC, positiveExitComplexTrace] using C.hasFDerivAt.comp_hasDerivAt s hf

/-- The constructed angle also supplies the exact actual derivative premise
needed by the terminal ruling at theta minus a small constant angle. -/
theorem visibleConnectorUnitDirection_hasDerivAt {theta : ℝ → ℝ} {k s : ℝ}
    (htheta : HasDerivAt theta k s) :
    HasDerivAt (fun r => visibleConnectorUnitDirection (theta r))
      (k • visibleConnectorJ (visibleConnectorUnitDirection (theta s))) s := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · change HasDerivAt (fun r => Real.cos (theta r)) (k * -Real.sin (theta s)) s
    simpa only [neg_mul, mul_neg, mul_comm] using htheta.cos
  · change HasDerivAt (fun r => Real.sin (theta r)) (k * Real.cos (theta s)) s
    simpa only [mul_comm] using htheta.sin

theorem visibleConnectorUnitDirection_contDiff : ContDiff ℝ ∞ visibleConnectorUnitDirection := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ Real.cos
    exact Real.contDiff_cos
  · change ContDiff ℝ ∞ Real.sin
    exact Real.contDiff_sin

private theorem connectorAngle_unit_sq (theta : ℝ) :
    (visibleConnectorUnitDirection theta) 0 ^ 2 +
      (visibleConnectorUnitDirection theta) 1 ^ 2 = 1 := by
  exact Real.cos_sq_add_sin_sq theta

/-- Construct the actual smooth visible angle and positive transverse length.
Norms are the actual Euclidean complex norms, rather than Coord's product norm.
The ordinary curve turn and visible pair are the only angular/topological inputs. -/
theorem visibleConnector_exists_actual_angular_frame {R L : ℝ} (hR : 0 < R)
    {p gamma : ℝ → Coord} (hgamma : ContDiff ℝ ∞ gamma)
    (hperiod : Periodic gamma L)
    (hturn : HasPositiveArgumentTurn (positiveExitComplexTrace gamma) L)
    (hvisible : ComplexVisiblePair R (positiveExitComplexTrace p)
      (fun s => Complex.I * positiveExitComplexTrace gamma s)) :
    ∃ theta kappa : ℝ → ℝ,
      ContDiff ℝ ∞ theta ∧ ContDiff ℝ ∞ kappa ∧
      (∀ s, theta (s + L) = theta s + 2 * Real.pi) ∧
      (∀ s, 0 < deriv theta s) ∧ (∀ s, 0 < kappa s) ∧
      (∀ s, kappa s = Real.sqrt (‖positiveExitComplexTrace gamma s‖ ^ 2 - R ^ 2)) ∧
      (∀ s, visibleConnectorTangentDirection R gamma s = visibleConnectorUnitDirection (theta s)) ∧
      ∀ s, visibleConnectorJ (gamma s) =
        R • visibleConnectorUnitDirection (theta s) -
          kappa s • visibleConnectorJ (visibleConnectorUnitDirection (theta s)) := by
  let z := positiveExitComplexTrace gamma
  let delta : ℝ → ℂ := fun s => Complex.I * z s
  have hz : ContDiff ℝ ∞ z := by
    change ContDiff ℝ ∞ (positiveExitComplexPoint ∘ gamma)
    rw [connectorAngle_complex_eq]
    exact angularDescentComplex_contDiff.comp hgamma
  have hd : ContDiff ℝ ∞ delta := contDiff_const.mul hz
  have hnorm (s : ℝ) : ‖delta s‖ = ‖z s‖ := by simp [delta, norm_mul]
  have hr (s : ℝ) : R < ‖z s‖ := by
    have h := (hvisible s).1
    simpa only [norm_mul, Complex.norm_I, one_mul] using h
  have hne (s : ℝ) : z s ≠ 0 := norm_pos_iff.mp (hR.trans (hr s))
  have hpz : Periodic z L := by
    intro s
    change positiveExitComplexPoint (gamma (s + L)) = positiveExitComplexPoint (gamma s)
    rw [hperiod s]
  obtain ⟨phi, hphi, hphiproj, hphiper⟩ :=
    positiveExit_actual_positive_argument_lift hz hpz hne hturn
  let theta (s : ℝ) := phi s + Real.pi / 2 + Real.arccos (R / ‖z s‖)
  let kappa (s : ℝ) := Real.sqrt (‖z s‖ ^ 2 - R ^ 2)
  have hkpos (s : ℝ) : 0 < kappa s := by
    apply Real.sqrt_pos.mpr
    have hh := hr s
    have hn := norm_nonneg (z s)
    nlinarith
  have hksq (s : ℝ) : kappa s ^ 2 = ‖z s‖ ^ 2 - R ^ 2 :=
    Real.sq_sqrt (by have hh := hr s; have hn := norm_nonneg (z s); nlinarith)
  have hnormsq : ContDiff ℝ ∞ (fun s => ‖z s‖ ^ 2) := by
    have he : (fun s => ‖z s‖ ^ 2) = (fun s => (z s).re ^ 2 + (z s).im ^ 2) := by
      funext s
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    rw [he]
    exact ((Complex.reCLM.contDiff.comp hz).pow 2).add ((Complex.imCLM.contDiff.comp hz).pow 2)
  have hk : ContDiff ℝ ∞ kappa :=
    (hnormsq.sub contDiff_const).sqrt (fun s => by
      have hh := hr s
      have hn := norm_nonneg (z s)
      nlinarith)
  have ht : ContDiff ℝ ∞ theta := by
    apply contDiff_iff_contDiffAt.mpr
    intro s
    have hn := hz.contDiffAt.norm ℂ (hne s)
    have hq := (contDiffAt_const (c := R)).div hn (ne_of_gt (hR.trans (hr s)))
    have hlo : (-1 : ℝ) < R / ‖z s‖ := by
      have hh : 0 < R / ‖z s‖ := div_pos hR (hR.trans (hr s))
      linarith
    have hhi : R / ‖z s‖ < 1 := (div_lt_one (hR.trans (hr s))).mpr (hr s)
    change ContDiffAt ℝ ∞ (fun t => R / ‖z t‖) s at hq
    have harc : ContDiffAt ℝ ∞ (Real.arccos ∘ (fun t => R / ‖z t‖)) s :=
      ContDiffAt.comp (g := Real.arccos) (f := fun t => R / ‖z t‖) s
        (Real.contDiffAt_arccos (ne_of_gt hlo) (ne_of_lt hhi)) hq
    exact (hphi.contDiffAt.add contDiffAt_const).add
      (by simpa only [Function.comp_def] using harc)
  let Z (s : ℝ) := Complex.exp ((theta s : ℂ) * Complex.I)
  have hZ (s : ℝ) : Z s = corrugatedVisibilityDirection R (delta s) := by
    have hpe : Complex.exp ((phi s : ℂ) * Complex.I) = ‖z s‖⁻¹ • z s := by
      have h := congrArg (fun w : Circle => (w : ℂ)) (hphiproj s)
      rw [complexCircleDirection_normalized (hne s), Circle.coe_exp] at h
      exact h.symm
    dsimp only [Z, theta]
    rw [Complex.ofReal_add, Complex.ofReal_add, add_mul, add_mul,
      Complex.exp_add, Complex.exp_add, Complex.ofReal_div, Complex.ofReal_ofNat,
      Complex.exp_pi_div_two_mul_I, hpe,
      ← corrugatedVisibilityCoefficient_exp_arccos hR.le (hr s),
      corrugatedVisibilityDirection_eq (mul_ne_zero Complex.I_ne_zero (hne s)), hnorm]
    simp only [delta, Complex.real_smul]
    ring
  have hdir (s : ℝ) : visibleConnectorTangentDirection R gamma s =
      visibleConnectorUnitDirection (theta s) := by
    have he : corrugatedVisibilityDirection R (delta s) = Z s := (hZ s).symm
    unfold visibleConnectorTangentDirection
    rw [show angularDescentComplex (gamma s) = z s by
      rw [← connectorAngle_complex_eq]; rfl]
    ext i
    fin_cases i
    · change (corrugatedVisibilityDirection R (delta s)).re = Real.cos (theta s)
      rw [he]
      simp [Z, Complex.exp_mul_I, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
    · change (corrugatedVisibilityDirection R (delta s)).im = Real.sin (theta s)
      rw [he]
      simp [Z, Complex.exp_mul_I, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  have hdecomp (s : ℝ) : delta s = (R : ℂ) * Z s - (kappa s : ℂ) * Complex.I * Z s := by
    rw [hZ]
    unfold corrugatedVisibilityDirection
    rw [hnorm]
    change delta s = (R : ℂ) * (((R : ℂ) + (kappa s : ℂ) * Complex.I) * delta s /
      ((‖z s‖ ^ 2 : ℝ) : ℂ)) - (kappa s : ℂ) * Complex.I *
      (((R : ℂ) + (kappa s : ℂ) * Complex.I) * delta s / ((‖z s‖ ^ 2 : ℝ) : ℂ))
    have hden : ((‖z s‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr (hne s)))
    field_simp [hden]
    apply Complex.ext <;>
      simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add]
    · linear_combination -(delta s).re * hksq s
    · linear_combination -(delta s).im * hksq s
  have hc (s : ℝ) : visibleConnectorJ (gamma s) =
      R • visibleConnectorUnitDirection (theta s) -
        kappa s • visibleConnectorJ (visibleConnectorUnitDirection (theta s)) := by
    have he := hdecomp s
    ext i
    fin_cases i
    · have hh := congrArg Complex.re he
      simpa [delta, z, positiveExitComplexTrace, positiveExitComplexPoint, visibleConnectorJ,
        visibleConnectorUnitDirection, Z, Complex.exp_mul_I, Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.mul_re, Complex.mul_im] using hh
    · have hh := congrArg Complex.im he
      simpa [delta, z, positiveExitComplexTrace, positiveExitComplexPoint, visibleConnectorJ,
        visibleConnectorUnitDirection, Z, Complex.exp_mul_I, Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.mul_re, Complex.mul_im] using hh
  have hpositive (s : ℝ) : 0 < deriv theta s := by
    let u (r : ℝ) := visibleConnectorUnitDirection (theta r)
    have hu := visibleConnectorUnitDirection_hasDerivAt ((ht.differentiable (by simp) s).hasDerivAt)
    have hactual := ((visibleConnectorJ_hasDerivAt
      ((hgamma.differentiable (by simp) s).hasDerivAt))).congr_of_eventuallyEq
      (f₁ := fun r => R • u r - kappa r • visibleConnectorJ (u r))
      (Eventually.of_forall (fun r => (hc r).symm))
    have hright := (hu.const_smul R).sub
      (((hk.differentiable (by simp) s).hasDerivAt).smul (visibleConnectorJ_hasDerivAt hu))
    have hcoeff := hactual.unique hright
    have hpair : visibleConnectorJ (deriv gamma s) ⬝ᵥ u s = kappa s * deriv theta s := by
      calc
        _ = (kappa s * deriv theta s) * ((u s) 0 ^ 2 + (u s) 1 ^ 2) := by
          rw [hcoeff]
          simp only [visibleConnectorJ, dotProduct, Fin.sum_univ_two, Pi.sub_apply,
            Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
            Matrix.cons_val_one, Matrix.head_cons]
          ring
        _ = _ := by
          change (kappa s * deriv theta s) *
            ((visibleConnectorUnitDirection (theta s)) 0 ^ 2 +
              (visibleConnectorUnitDirection (theta s)) 1 ^ 2) = _
          rw [connectorAngle_unit_sq, mul_one]
    have hdactual := (connectorAngle_complex_hasDerivAt
      ((hgamma.differentiable (by simp) s).hasDerivAt)).const_mul Complex.I
    have hdEq : deriv delta s = Complex.I * positiveExitComplexPoint (deriv gamma s) := hdactual.deriv
    have hs := (hvisible s).2.2
    change 0 < inner ℝ (deriv delta s) (corrugatedVisibilityDirection R (delta s)) at hs
    rw [hdEq, ← hZ s] at hs
    have hZre : (Z s).re = Real.cos (theta s) := by
      simp [Z, Complex.exp_mul_I, Complex.cos_ofReal_re]
    have hZim : (Z s).im = Real.sin (theta s) := by
      simp [Z, Complex.exp_mul_I, Complex.sin_ofReal_re]
    have hs' : 0 < visibleConnectorJ (deriv gamma s) ⬝ᵥ u s := by
      simpa [u, positiveExitComplexPoint, visibleConnectorJ, visibleConnectorUnitDirection,
        hZre, hZim, corrugated_complex_inner, Complex.mul_re, Complex.mul_im,
        dotProduct, Fin.sum_univ_two, mul_comm] using hs
    rw [hpair] at hs'
    exact (mul_pos_iff_of_pos_left (hkpos s)).mp hs'
  refine ⟨theta, kappa, ht, hk, ?_, hpositive, hkpos, fun _ => rfl, hdir, hc⟩
  intro s
  dsimp only [theta]
  rw [hphiper s, hpz s]
  ring

end
end TightVer401