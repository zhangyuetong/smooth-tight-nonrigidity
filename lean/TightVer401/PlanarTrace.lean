import TightVer401.PlanarGradientInverse
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix

theorem planarGradient_dot_fderiv (G : Coord → ℝ) (p v : Coord) :
    fderiv ℝ G p v = planarGradient G p ⬝ᵥ v := by
  have hv : v = v 0 • (Pi.single 0 1 : Coord) + v 1 • (Pi.single 1 1 : Coord) := by
    ext i
    fin_cases i <;> simp
  conv_lhs => rw [hv]
  simp [planarGradient, coordPartial, dotProduct, Fin.sum_univ_two, mul_comm]

theorem planarTrace_value_hasDerivAt {G : Coord → ℝ} {U : Set Coord} {p : ℝ → Coord}
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U) {t : ℝ} (ht : p t ∈ U)
    {v : Coord} (hp : HasDerivAt p v t) :
    HasDerivAt (fun s => G (p s)) (planarGradient G (p t) ⬝ᵥ v) t := by
  have hdG := ((hG (p t) ht).contDiffAt (hU.mem_nhds ht)).differentiableAt (by simp)
  have hd := hdG.hasFDerivAt.comp_hasDerivAt t hp
  simpa only [Function.comp_def, planarGradient_dot_fderiv] using hd

theorem planarTrace_gradient_hasDerivAt {G : Coord → ℝ} {U : Set Coord} {p : ℝ → Coord}
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U) {t : ℝ} (ht : p t ∈ U)
    {v : Coord} (hp : HasDerivAt p v t) :
    HasDerivAt (fun s => planarGradient G (p s)) (planarHessian G (p t) *ᵥ v) t := by
  have hdG := (((planarGradient_contDiffOn hG hU) (p t) ht).contDiffAt
    (hU.mem_nhds ht)).differentiableAt (by simp)
  have hd := hdG.hasFDerivAt.comp_hasDerivAt t hp
  simpa only [Function.comp_def, planarGradient_fderiv_apply hG hU ht] using hd

theorem planarTrace_value_deriv {G : Coord → ℝ} {U : Set Coord} {p : ℝ → Coord}
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U) {t : ℝ} (ht : p t ∈ U)
    (hp : DifferentiableAt ℝ p t) :
    deriv (fun s => G (p s)) t = planarGradient G (p t) ⬝ᵥ deriv p t :=
  (planarTrace_value_hasDerivAt hG hU ht hp.hasDerivAt).deriv

theorem planarTrace_gradient_deriv {G : Coord → ℝ} {U : Set Coord} {p : ℝ → Coord}
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U) {t : ℝ} (ht : p t ∈ U)
    (hp : DifferentiableAt ℝ p t) :
    deriv (fun s => planarGradient G (p s)) t = planarHessian G (p t) *ᵥ deriv p t :=
  (planarTrace_gradient_hasDerivAt hG hU ht hp.hasDerivAt).deriv

theorem planarTrace_tangent_pairing {G : Coord → ℝ} {U : Set Coord} {p : ℝ → Coord}
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U) {t : ℝ} (ht : p t ∈ U)
    (hp : DifferentiableAt ℝ p t) :
    deriv p t ⬝ᵥ deriv (fun s => planarGradient G (p s)) t =
      deriv p t ⬝ᵥ (planarHessian G (p t) *ᵥ deriv p t) := by
  rw [planarTrace_gradient_deriv hG hU ht hp]

theorem planarTrace_action_integral {G : Coord → ℝ} {U : Set Coord} {p : ℝ → Coord}
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U) (hp : ContDiff ℝ ∞ p)
    {a b : ℝ} (hmap : MapsTo p (uIcc a b) U) :
    (∫ t in a..b, planarGradient G (p t) ⬝ᵥ deriv p t) = G (p b) - G (p a) := by
  have hγ : ContinuousOn (fun t => planarGradient G (p t)) (uIcc a b) :=
    (planarGradient_contDiffOn hG hU).continuousOn.comp hp.continuous.continuousOn hmap
  have hd : Continuous (deriv p) := hp.continuous_deriv (by simp)
  have hf : ContinuousOn (fun t => planarGradient G (p t) ⬝ᵥ deriv p t) (uIcc a b) := by
    unfold dotProduct
    exact continuousOn_finsetSum _ (fun i _ => ((continuousOn_pi.mp hγ) i).mul
      ((continuous_apply i).comp hd).continuousOn)
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => planarTrace_value_hasDerivAt hG hU (hmap ht)
      (hp.contDiffAt.differentiableAt (by simp)).hasDerivAt) hf.intervalIntegrable

theorem planarTrace_closed_action_zero {G : Coord → ℝ} {U : Set Coord} {p : ℝ → Coord}
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U) (hp : ContDiff ℝ ∞ p)
    {a b : ℝ} (hmap : MapsTo p (uIcc a b) U) (hclosed : p b = p a) :
    (∫ t in a..b, planarGradient G (p t) ⬝ᵥ deriv p t) = 0 := by
  rw [planarTrace_action_integral hG hU hp hmap, hclosed, sub_self]

theorem planarTrace_periodic_action_zero {G : Coord → ℝ} {U : Set Coord} {p : ℝ → Coord}
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U) (hp : ContDiff ℝ ∞ p)
    {L : ℝ} (hmap : MapsTo p (uIcc 0 L) U) (hperiod : Function.Periodic p L) :
    (∫ t in 0..L, planarGradient G (p t) ⬝ᵥ deriv p t) = 0 :=
  planarTrace_closed_action_zero hG hU hp hmap (by simpa using hperiod 0)

end
end TightVer401
