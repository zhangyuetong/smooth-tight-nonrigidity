import TightVer401.PlanarTrace

/-! Explicit local ruled connector coordinates. The source and gradient
formulas are actual functions. This file does not grant an annular inverse,
visible-angle lift or descended potential. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency true

/-- Quarter-turn with the same positive complex orientation as `I`. -/
def visibleConnectorJ (v : Coord) : Coord := ![-v 1, v 0]

def visibleConnectorDet (v w : Coord) : ℝ := v 0 * w 1 - v 1 * w 0

def visibleConnectorSource (p w : ℝ → Coord) (q : Coord) : Coord :=
  p (q 0) + q 1 • w (q 0)

def visibleConnectorHeight (g : ℝ → ℝ) (gamma w : ℝ → Coord) (q : Coord) : ℝ :=
  g (q 0) + q 1 * (gamma (q 0) ⬝ᵥ w (q 0))

def visibleConnectorA (p w : ℝ → Coord) (s : ℝ) : ℝ :=
  -visibleConnectorDet (deriv p s) (w s)

def visibleConnectorB (gamma w : ℝ → Coord) (s : ℝ) : ℝ :=
  deriv gamma s ⬝ᵥ w s

def visibleConnectorC (gamma w : ℝ → Coord) (s : ℝ) : ℝ :=
  visibleConnectorB gamma w s + visibleConnectorDet (deriv w s) (w s)

def visibleConnectorDelta (p gamma w : ℝ → Coord) (q : Coord) : ℝ :=
  visibleConnectorA p w (q 0) +
    q 1 * (visibleConnectorB gamma w (q 0) - visibleConnectorC gamma w (q 0))

def visibleConnectorGradient (p gamma w : ℝ → Coord) (q : Coord) : Coord :=
  gamma (q 0) +
    (q 1 * visibleConnectorB gamma w (q 0) / visibleConnectorDelta p gamma w q) •
      visibleConnectorJ (w (q 0))

@[simp] theorem visibleConnectorJ_dot_self (w : Coord) :
    visibleConnectorJ w ⬝ᵥ w = 0 := by
  simp [visibleConnectorJ, dotProduct, Fin.sum_univ_two]
  ring

theorem visibleConnectorJ_dot (w v : Coord) :
    visibleConnectorJ w ⬝ᵥ v = -visibleConnectorDet v w := by
  simp [visibleConnectorJ, visibleConnectorDet, dotProduct, Fin.sum_univ_two]
  ring

theorem visibleConnectorDet_add_smul (a b w : Coord) (u : ℝ) :
    visibleConnectorDet (a + u • b) w =
      visibleConnectorDet a w + u * visibleConnectorDet b w := by
  simp [visibleConnectorDet]
  ring

theorem visibleConnector_source_determinant (p gamma w : ℝ → Coord) (q : Coord) :
    visibleConnectorDet (deriv p (q 0) + q 1 • deriv w (q 0)) (w (q 0)) =
      -visibleConnectorDelta p gamma w q := by
  rw [visibleConnectorDet_add_smul]
  simp [visibleConnectorDelta, visibleConnectorA, visibleConnectorC]
  ring

/-- The actual candidate gradient satisfies both directional first-jet
identities when the explicit source determinant is nonzero. -/
theorem visibleConnector_gradient_equations (p gamma w : ℝ → Coord) (q : Coord)
    (hDelta : visibleConnectorDelta p gamma w q ≠ 0) :
    visibleConnectorGradient p gamma w q ⬝ᵥ w (q 0) =
        gamma (q 0) ⬝ᵥ w (q 0) ∧
      visibleConnectorGradient p gamma w q ⬝ᵥ
          (deriv p (q 0) + q 1 • deriv w (q 0)) =
        gamma (q 0) ⬝ᵥ deriv p (q 0) +
          q 1 * (deriv gamma (q 0) ⬝ᵥ w (q 0) +
            gamma (q 0) ⬝ᵥ deriv w (q 0)) := by
  have hJ := visibleConnectorJ_dot (w (q 0))
    (deriv p (q 0) + q 1 • deriv w (q 0))
  rw [visibleConnector_source_determinant p gamma w q, neg_neg] at hJ
  constructor
  · rw [visibleConnectorGradient, add_dotProduct, smul_dotProduct, visibleConnectorJ_dot_self]
    simp
  · rw [visibleConnectorGradient, add_dotProduct, smul_dotProduct, hJ]
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
    unfold visibleConnectorB
    field_simp [hDelta]
    <;> ring

/-- Actual coordinate derivatives of the ruled source, with no derivative
witness supplied independently of the two curves. -/
theorem visibleConnectorSource_partials {p w : ℝ → Coord}
    (hp : ContDiff ℝ ∞ p) (hw : ContDiff ℝ ∞ w) (q : Coord) :
    coordPartial 0 (visibleConnectorSource p w) q =
        deriv p (q 0) + q 1 • deriv w (q 0) ∧
      coordPartial 1 (visibleConnectorSource p w) q = w (q 0) := by
  have hpp := ((hp.differentiable (by simp) (q 0)).hasDerivAt.hasFDerivAt).comp q
    (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)).hasFDerivAt
  have hww := ((hw.differentiable (by simp) (q 0)).hasDerivAt.hasFDerivAt).comp q
    (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)).hasFDerivAt
  have hu := (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2)).hasFDerivAt (x := q)
  have hd := hpp.add (hu.smul hww)
  change HasFDerivAt (visibleConnectorSource p w) _ q at hd
  constructor <;> rw [coordPartial, hd.fderiv] <;> simp

/-- The determinant sign is for the actual source derivative. -/
theorem visibleConnectorSource_actual_determinant {p w : ℝ → Coord}
    (hp : ContDiff ℝ ∞ p) (hw : ContDiff ℝ ∞ w)
    (gamma : ℝ → Coord) (q : Coord) :
    visibleConnectorDet (coordPartial 0 (visibleConnectorSource p w) q)
      (coordPartial 1 (visibleConnectorSource p w) q) =
        -visibleConnectorDelta p gamma w q := by
  rw [(visibleConnectorSource_partials hp hw q).1,
    (visibleConnectorSource_partials hp hw q).2]
  exact visibleConnector_source_determinant p gamma w q

theorem visibleConnectorHeight_partials {g : ℝ → ℝ} {gamma w : ℝ → Coord}
    (hg : ContDiff ℝ ∞ g) (hgamma : ContDiff ℝ ∞ gamma) (hw : ContDiff ℝ ∞ w)
    (q : Coord) :
    coordPartial 0 (visibleConnectorHeight g gamma w) q =
        deriv g (q 0) + q 1 *
          (deriv gamma (q 0) ⬝ᵥ w (q 0) + gamma (q 0) ⬝ᵥ deriv w (q 0)) ∧
      coordPartial 1 (visibleConnectorHeight g gamma w) q =
        gamma (q 0) ⬝ᵥ w (q 0) := by
  have hgam := (hgamma.differentiable (by simp) (q 0)).hasDerivAt
  have hwr := (hw.differentiable (by simp) (q 0)).hasDerivAt
  have hgi (i : Fin 2) : HasDerivAt (fun s : ℝ => gamma s i)
      (deriv gamma (q 0) i) (q 0) := by
    simpa [Function.comp_def] using
      (ContinuousLinearMap.proj (R := ℝ) i).hasFDerivAt.comp_hasDerivAt (q 0) hgam
  have hwi (i : Fin 2) : HasDerivAt (fun s : ℝ => w s i)
      (deriv w (q 0) i) (q 0) := by
    simpa [Function.comp_def] using
      (ContinuousLinearMap.proj (R := ℝ) i).hasFDerivAt.comp_hasDerivAt (q 0) hwr
  have hdot : HasDerivAt (fun s => gamma s ⬝ᵥ w s)
      (deriv gamma (q 0) ⬝ᵥ w (q 0) + gamma (q 0) ⬝ᵥ deriv w (q 0)) (q 0) := by
    convert! ((hgi 0).mul (hwi 0)).add ((hgi 1).mul (hwi 1)) using 1 <;>
      (try simp only [dotProduct, Fin.sum_univ_two, Pi.add_apply, Pi.mul_apply]) <;>
      first | rfl | ring
  have hgg := ((hg.differentiable (by simp) (q 0)).hasDerivAt.hasFDerivAt).comp q
    (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)).hasFDerivAt
  have hdd := hdot.hasFDerivAt.comp q
    (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)).hasFDerivAt
  have hu := (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2)).hasFDerivAt (x := q)
  have hd := hgg.add (hu.mul hdd)
  change HasFDerivAt (visibleConnectorHeight g gamma w) _ q at hd
  constructor <;> rw [coordPartial, hd.fderiv] <;> simp

/-- Both candidate-gradient equations are the actual height partials when
`g` is the incoming potential value trace. -/
theorem visibleConnector_actual_first_jets {g : ℝ → ℝ} {p gamma w : ℝ → Coord}
    (hg : ContDiff ℝ ∞ g) (hp : ContDiff ℝ ∞ p)
    (hgamma : ContDiff ℝ ∞ gamma) (hw : ContDiff ℝ ∞ w)
    (hvalue : ∀ s, deriv g s = gamma s ⬝ᵥ deriv p s)
    (q : Coord) (hDelta : visibleConnectorDelta p gamma w q ≠ 0) :
    ∀ i : Fin 2, visibleConnectorGradient p gamma w q ⬝ᵥ
      coordPartial i (visibleConnectorSource p w) q =
        coordPartial i (visibleConnectorHeight g gamma w) q := by
  have hP := visibleConnectorSource_partials hp hw q
  have hH := visibleConnectorHeight_partials hg hgamma hw q
  have hY := visibleConnector_gradient_equations p gamma w q hDelta
  intro i
  fin_cases i
  · change visibleConnectorGradient p gamma w q ⬝ᵥ
      coordPartial 0 (visibleConnectorSource p w) q =
        coordPartial 0 (visibleConnectorHeight g gamma w) q
    rw [hP.1, hH.1, hvalue]
    exact hY.2
  · change visibleConnectorGradient p gamma w q ⬝ᵥ
      coordPartial 1 (visibleConnectorSource p w) q =
        coordPartial 1 (visibleConnectorHeight g gamma w) q
    rw [hP.2, hH.2]
    exact hY.1

end
end TightVer401
