import TightVer401.VisibleConnectorIncomingTerminalMargins
import TightVer401.VisibleConnectorDisplacedSeamRebase

/-! The terminal of the literal ruling rebase is EXACTLY the old terminal
composed with the retained phase a. Consequently a positive phase derivative
transports the actual terminal determinant without a second C1 approximation
or an independently selected terminal. -/
namespace TightVer401
noncomputable section
open Set Function OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Literal terminal identity for the same d = tc(a)-b used by the rebase. -/
theorem visibleConnectorIncomingTerminal_rebase_eq
    (p w : ℝ → Coord) (a b d tc : ℝ → ℝ)
    (hd : ∀ s, d s = tc (a s) - b s) (s : ℝ) :
    visibleConnectorSource (visibleConnectorRebasedSource p w a b)
      (visibleConnectorRebasedRuling w a d) (![s, 1] : Coord) =
    visibleConnectorSource p w (![a s, tc (a s)] : Coord) := by
  rw [visibleConnector_rebase_source, hd s]
  congr 1
  ext i
  fin_cases i <;> simp <;> ring

/-- Actual first derivative of the terminal: the same old terminal derivative
is multiplied by the SAME selected phase derivative. -/
theorem visibleConnectorIncomingTerminal_rebase_deriv
    {p w : ℝ → Coord} {a b d tc : ℝ → ℝ}
    (hp : ContDiff ℝ ∞ p) (hw : ContDiff ℝ ∞ w)
    (ha : ContDiff ℝ ∞ a) (htc : ContDiff ℝ ∞ tc)
    (hd : ∀ s, d s = tc (a s) - b s) (s : ℝ) :
    deriv (fun t => visibleConnectorSource (visibleConnectorRebasedSource p w a b)
      (visibleConnectorRebasedRuling w a d) (![t, 1] : Coord)) s =
    deriv a s • deriv (fun t => visibleConnectorSource p w (![t, tc t] : Coord)) (a s) := by
  let T : ℝ → Coord := fun t => visibleConnectorSource p w (![t, tc t] : Coord)
  have hT : ContDiff ℝ ∞ T := hp.add (htc.smul hw)
  have he : (fun t => visibleConnectorSource (visibleConnectorRebasedSource p w a b)
      (visibleConnectorRebasedRuling w a d) (![t, 1] : Coord)) = T ∘ a := by
    funext t
    exact visibleConnectorIncomingTerminal_rebase_eq p w a b d tc hd t
  rw [he]
  exact (((hT.differentiable (by simp) (a s)).hasDerivAt).scomp s
    ((ha.differentiable (by simp) s).hasDerivAt)).deriv

/-- Positive determinant and arbitrarily large norm bounds of the original
terminal transport literally through the rebase; neither is a perturbed
terminal premise. Smoothness of b or d is not needed for this exact identity. -/
theorem visibleConnectorIncomingTerminal_rebase_geometry
    {p w : ℝ → Coord} {a b d tc : ℝ → ℝ} {M : ℝ}
    (hp : ContDiff ℝ ∞ p) (hw : ContDiff ℝ ∞ w)
    (ha : ContDiff ℝ ∞ a) (htc : ContDiff ℝ ∞ tc)
    (hd : ∀ s, d s = tc (a s) - b s)
    (hap : ∀ s, 0 < deriv a s)
    (hnorm : ∀ s, M < ‖positiveExitComplexPoint
      (visibleConnectorSource p w (![s, tc s] : Coord))‖)
    (hdet : ∀ s, 0 < visibleConnectorDet
      (visibleConnectorSource p w (![s, tc s] : Coord))
      (deriv (fun t => visibleConnectorSource p w (![t, tc t] : Coord)) s)) :
    let T := fun s => visibleConnectorSource (visibleConnectorRebasedSource p w a b)
      (visibleConnectorRebasedRuling w a d) (![s, 1] : Coord)
    ∀ s, M < ‖positiveExitComplexPoint (T s)‖ ∧
      0 < visibleConnectorDet (T s) (deriv T s) := by
  dsimp only
  intro s
  constructor
  · rw [visibleConnectorIncomingTerminal_rebase_eq p w a b d tc hd s]
    exact hnorm (a s)
  · rw [visibleConnectorIncomingTerminal_rebase_eq p w a b d tc hd s,
      visibleConnectorIncomingTerminal_rebase_deriv hp hw ha htc hd s]
    have he : visibleConnectorDet
        (visibleConnectorSource p w (![a s, tc (a s)] : Coord))
        (deriv a s • deriv (fun t => visibleConnectorSource p w (![t, tc t] : Coord)) (a s)) =
        deriv a s * visibleConnectorDet
          (visibleConnectorSource p w (![a s, tc (a s)] : Coord))
          (deriv (fun t => visibleConnectorSource p w (![t, tc t] : Coord)) (a s)) := by
      simp only [visibleConnectorDet, Pi.smul_apply, smul_eq_mul]
      ring
    rw [he]
    exact mul_pos (hap s) (hdet (a s))

end
end TightVer401

