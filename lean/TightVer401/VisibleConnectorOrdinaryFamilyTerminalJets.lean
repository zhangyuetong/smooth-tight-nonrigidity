import TightVer401.VisibleConnectorFinalSmoothingGerms
import TightVer401.VisibleConnectorTerminalPairing
import TightVer401.VisibleConnectorIncomingTerminalRebase

/-! The open terminal equality germ transfers the literal raw ruling jets to
one final scalar H. The actual circle and radial positivity are deduced from
ordinary ruling coefficients; no raw gradient inverse is used for H. -/
namespace TightVer401
noncomputable section
open Set Function OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix

/-- Retain the SAME actual terminal and final H. Its gradient is the explicit
radius-R terminal direction, and its actual radial pairing is positive. -/
theorem visibleConnectorOrdinaryFamilyTerminalJets_actual_ruling
    {R : ℝ} (hR : 0 < R) {p gamma e : ℝ → Coord}
    {H raw : Coord → ℝ} {Ot : Set Coord}
    (hOt : IsOpen Ot) (hEquality : EqOn H raw Ot)
    (hUnit : ∀ s, e s ⬝ᵥ e s = 1)
    (hA : ∀ s, 0 < visibleConnectorA p (visibleConnectorActualRuling R gamma e) s)
    (hB : ∀ s, 0 < visibleConnectorB gamma (visibleConnectorActualRuling R gamma e) s)
    (hC : ∀ s, 0 < visibleConnectorC gamma (visibleConnectorActualRuling R gamma e) s)
    (hTerminalDomain : ∀ s, visibleConnectorActualTerminalSource p gamma
      (visibleConnectorActualRuling R gamma e) s ∈ Ot)
    (hRawGradient : ∀ s, planarGradient raw (visibleConnectorActualTerminalSource p gamma
      (visibleConnectorActualRuling R gamma e) s) = visibleConnectorGradient p gamma
      (visibleConnectorActualRuling R gamma e)
      ![s, visibleConnectorActualTerminalHeight p gamma (visibleConnectorActualRuling R gamma e) s])
    (hRadial : ∀ s, 0 < visibleConnectorActualTerminalSource p gamma
      (visibleConnectorActualRuling R gamma e) s ⬝ᵥ (-visibleConnectorJ (e s))) :
    let T := visibleConnectorActualTerminalSource p gamma (visibleConnectorActualRuling R gamma e)
    (fun s => -R • visibleConnectorJ (e s)) = planarGradient H ∘ T ∧
      (∀ s, planarGradient H (T s) = visibleConnectorGradient p gamma
        (visibleConnectorActualRuling R gamma e)
        ![s, visibleConnectorActualTerminalHeight p gamma (visibleConnectorActualRuling R gamma e) s]) ∧
      (∀ s, 0 < T s ⬝ᵥ planarGradient H (T s)) ∧
      (∀ s, planarGradient H (T s) ⬝ᵥ planarGradient H (T s) = R ^ 2) := by
  dsimp only
  obtain ⟨hGradient, _⟩ := visibleConnectorFinalSmoothing_open_equality_derivatives hOt hEquality
  have hj (s : ℝ) : planarGradient H (visibleConnectorActualTerminalSource p gamma
      (visibleConnectorActualRuling R gamma e) s) = visibleConnectorGradient p gamma
      (visibleConnectorActualRuling R gamma e)
      ![s, visibleConnectorActualTerminalHeight p gamma (visibleConnectorActualRuling R gamma e) s] :=
    (hGradient (hTerminalDomain s)).trans (hRawGradient s)
  have hc (s : ℝ) := visibleConnector_actual_ruling_circle_terminal hR
    (p := p) (gamma := gamma) (e := e) (hUnit s) (hA s) (hB s) (hC s)
  have hCircle (s : ℝ) : planarGradient H (visibleConnectorActualTerminalSource p gamma
      (visibleConnectorActualRuling R gamma e) s) = -R • visibleConnectorJ (e s) := by
    rw [hj s]
    exact (hc s).2.2.1
  refine ⟨?_, hj, ?_, ?_⟩
  · funext s
    exact (hCircle s).symm
  · intro s
    rw [hCircle s]
    have he : -R • visibleConnectorJ (e s) = R • (-visibleConnectorJ (e s)) := by
      ext i
      simp
    rw [he, dotProduct_smul]
    exact mul_pos hR (hRadial s)
  · intro s
    rw [hj s]
    exact (hc s).2.2.2

/-- The raw producer's rebased endpoint jet is the SAME old terminal jet.
The terminal is retained through a, with d equal to the actual remaining
ruling height. No separate old-terminal raw gradient identity is assumed. -/
theorem visibleConnectorOrdinaryFamilyTerminalJets_rebased_endpoint
    {p gamma w : ℝ → Coord} {a b d : ℝ → ℝ} {raw : Coord → ℝ}
    (hp : ContDiff ℝ ∞ p) (hgamma : ContDiff ℝ ∞ gamma) (hw : ContDiff ℝ ∞ w)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hd : ContDiff ℝ ∞ d)
    (hDb : ∀ s, visibleConnectorDelta p gamma w ![a s, b s] ≠ 0)
    (hap : ∀ s, deriv a s ≠ 0) (hdp : ∀ s, d s ≠ 0)
    (hRemaining : ∀ s, d s = visibleConnectorActualTerminalHeight p gamma w (a s) - b s)
    (hDt : ∀ s, visibleConnectorDelta p gamma w
      ![a s, visibleConnectorActualTerminalHeight p gamma w (a s)] ≠ 0)
    (hRawEndpoint : ∀ s, planarGradient raw
      (visibleConnectorRebasedSource p w a b s + visibleConnectorRebasedRuling w a d s) =
      visibleConnectorGradient (visibleConnectorRebasedSource p w a b)
        (visibleConnectorRebasedGradient p gamma w a b)
        (visibleConnectorRebasedRuling w a d) ![s, 1]) :
    (∀ s, visibleConnectorRebasedSource p w a b s + visibleConnectorRebasedRuling w a d s =
      visibleConnectorActualTerminalSource p gamma w (a s)) ∧
    (∀ s, planarGradient raw (visibleConnectorActualTerminalSource p gamma w (a s)) =
      visibleConnectorGradient p gamma w
        ![a s, visibleConnectorActualTerminalHeight p gamma w (a s)]) := by
  have hSource (s : ℝ) :
      visibleConnectorRebasedSource p w a b s + visibleConnectorRebasedRuling w a d s =
      visibleConnectorActualTerminalSource p gamma w (a s) := by
    have he := visibleConnectorIncomingTerminal_rebase_eq p w a b d
      (visibleConnectorActualTerminalHeight p gamma w) hRemaining s
    simpa only [visibleConnectorSource, Matrix.cons_val_zero, Matrix.cons_val_one,
      one_smul, visibleConnectorActualTerminalSource] using he
  refine ⟨hSource, ?_⟩
  intro s
  have hHeight : b s + 1 * d s = visibleConnectorActualTerminalHeight p gamma w (a s) := by
    rw [hRemaining s]
    ring
  have hDt' : visibleConnectorDelta p gamma w ![a s, b s + 1 * d s] ≠ 0 := by
    rw [hHeight]
    exact hDt s
  rw [← hSource s, hRawEndpoint s]
  have he := visibleConnector_rebase_gradient hp hgamma hw ha hb hd hDb hap hdp s 1 hDt'
  rw [hHeight] at he
  exact he
end
end TightVer401


