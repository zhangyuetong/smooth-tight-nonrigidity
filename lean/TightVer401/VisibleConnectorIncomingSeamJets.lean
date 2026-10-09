import TightVer401.VisibleConnectorIncomingCollar
import TightVer401.VisibleConnectorDisplacedSeamRebase

/-! Actual scalar and gradient jets at the displaced incoming seam. The trace
and its gradient are evaluated from the SAME Gin; no matching jet is assumed.
The Cartesian inverse below is retained, rather than chosen independently. -/
namespace TightVer401
noncomputable section
open Set Function Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- Chain rule for the literal incoming scalar trace. -/
theorem visibleConnectorIncomingSeam_trace_deriv {Gin : Coord → ℝ} {U : Set Coord}
    {p : ℝ → Coord} (hU : IsOpen U) (hGin : ContDiffOn ℝ ∞ Gin U)
    (hp : ContDiff ℝ ∞ p) (hpU : ∀ s, p s ∈ U) (s : ℝ) :
    deriv (Gin ∘ p) s = planarGradient Gin (p s) ⬝ᵥ deriv p s := by
  have hd := ((hGin _ (hpU s)).contDiffAt (hU.mem_nhds (hpU s))).differentiableAt (by simp)
  have hc := hd.hasFDerivAt.comp_hasDerivAt s (hp.differentiable (by simp) s).hasDerivAt
  rw [hc.deriv]
  exact planarGradient_dot_fderiv Gin (p s) (deriv p s)

/-- Construct the actual local raw scalar from Gin at any incoming seam point.
Both value and gradient matching are conclusions, including the literal trace
identity on the whole open parameter neighborhood. -/
theorem visibleConnectorIncomingSeam_exists_local_matched_potential
    {Gin : Coord → ℝ} {U : Set Coord} {p w : ℝ → Coord}
    (hU : IsOpen U) (hGin : ContDiffOn ℝ ∞ Gin U)
    (hp : ContDiff ℝ ∞ p) (hw : ContDiff ℝ ∞ w) (hpU : ∀ s, p s ∈ U)
    (r : ℝ) (hdet : visibleConnectorDet (deriv p r) (w r) ≠ 0) :
    ∃ (E : OpenPartialHomeomorph Coord Coord) (raw : Coord → ℝ),
      (![r, 0] : Coord) ∈ E.source ∧
      (E : Coord → Coord) = visibleConnectorSource p w ∧
      ContDiffOn ℝ ∞ E.symm E.target ∧ ContDiffOn ℝ ∞ raw E.target ∧
      EqOn (raw ∘ visibleConnectorSource p w)
        (visibleConnectorHeight (Gin ∘ p) (planarGradient Gin ∘ p) w) E.source ∧
      EqOn (planarGradient raw ∘ visibleConnectorSource p w)
        (visibleConnectorGradient p (planarGradient Gin ∘ p) w) E.source ∧
      (∀ s, (![s, 0] : Coord) ∈ E.source →
        raw (p s) = Gin (p s) ∧ planarGradient raw (p s) = planarGradient Gin (p s)) := by
  have hg : ContDiff ℝ ∞ (Gin ∘ p) := contDiffOn_univ.mp
    (hGin.comp hp.contDiffOn (fun s _ => hpU s))
  have hgamma : ContDiff ℝ ∞ (planarGradient Gin ∘ p) := contDiffOn_univ.mp
    ((planarGradient_contDiffOn hGin hU).comp hp.contDiffOn (fun s _ => hpU s))
  have hvalue (s : ℝ) : deriv (Gin ∘ p) s =
      (planarGradient Gin ∘ p) s ⬝ᵥ deriv p s :=
    visibleConnectorIncomingSeam_trace_deriv hU hGin hp hpU s
  have hDelta : visibleConnectorDelta p (planarGradient Gin ∘ p) w (![r, 0] : Coord) ≠ 0 := by
    simpa [visibleConnectorDelta, visibleConnectorA] using neg_ne_zero.mpr hdet
  obtain ⟨E, raw, hr, hE, hi, hraw, hv, hj⟩ :=
    visibleConnector_exists_local_potential hg hp hgamma hw hvalue (![r, 0] : Coord) hDelta
  refine ⟨E, raw, hr, hE, hi, hraw, hv, hj, ?_⟩
  intro s hs
  constructor
  · simpa [visibleConnectorSource, visibleConnectorHeight, Function.comp_apply] using hv hs
  · simpa [visibleConnectorSource, visibleConnectorGradient, Function.comp_apply] using hj hs

end
end TightVer401
