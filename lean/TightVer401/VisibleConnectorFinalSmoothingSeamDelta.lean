import TightVer401.VisibleConnectorFinalSmoothingHeight
import TightVer401.VisibleConnectorDisplacedSeamRebase

/-! Recover the displaced seam coefficient from the actual full rebased-band
source determinant. The raw gradient parameter is arbitrary: this determinant
is geometric, and no gradient identification is assumed. -/
namespace TightVer401
noncomputable section
open Set Function Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

private theorem finalSmoothing_Delta_gradient_independent
    (p w gamma₁ gamma₂ : ℝ → Coord) (q : Coord) :
    visibleConnectorDelta p gamma₁ w q = visibleConnectorDelta p gamma₂ w q := by
  simp only [visibleConnectorDelta, visibleConnectorC]
  ring

/-- The old coefficient belongs to the displaced zero seam `pc`, rather than
its original lower graph. Full rebased positivity includes that interior seam. -/
theorem visibleConnectorFinalSmoothing_old_coefficient_of_rebased_Delta
    {pc wc rawGamma : ℝ → Coord} {a b d : ℝ → ℝ}
    (hp : ContDiff ℝ ∞ pc) (hw : ContDiff ℝ ∞ wc)
    (ha : ContDiff ℝ ∞ a) (hbSmooth : ContDiff ℝ ∞ b) (hdSmooth : ContDiff ℝ ∞ d)
    (hphase : ∀ s, 0 < deriv a s) (hd : ∀ s, 0 < d s)
    (hb : ∀ s, b s < 0) (ht : ∀ s, 0 < b s + d s)
    (hDelta : ∀ q : Coord, 0 ≤ q 1 → q 1 ≤ 1 →
      0 < visibleConnectorDelta (visibleConnectorRebasedSource pc wc a b)
        rawGamma (visibleConnectorRebasedRuling wc a d) q) :
    ∀ s, 0 < visibleConnectorA pc wc (a s) := by
  intro s
  let u0 : ℝ := -b s / d s
  have hu0 : 0 < u0 := div_pos (neg_pos.mpr (hb s)) (hd s)
  have hu1 : u0 < 1 := (div_lt_one (hd s)).mpr (by linarith [ht s])
  have hz : b s + u0 * d s = 0 := by
    dsimp [u0]
    field_simp [(hd s).ne']
    ring
  have hpositive := hDelta (![s, u0] : Coord) hu0.le hu1.le
  have hchange := finalSmoothing_Delta_gradient_independent
    (visibleConnectorRebasedSource pc wc a b) (visibleConnectorRebasedRuling wc a d)
    rawGamma (visibleConnectorRebasedGradient pc pc wc a b) (![s, u0] : Coord)
  rw [hchange] at hpositive
  have hscale := (visibleConnector_rebase_determinants
    (gamma := pc) hp hw ha hbSmooth hdSmooth s u0).2
  rw [hscale] at hpositive
  have hseam : visibleConnectorDelta pc pc wc (![a s, b s + u0 * d s] : Coord) =
      visibleConnectorA pc wc (a s) := by
    simp only [visibleConnectorDelta, Matrix.cons_val_zero, Matrix.cons_val_one, hz,
      zero_mul, add_zero]
  rw [hseam] at hpositive
  have hfactor : 0 < deriv a s * d s := mul_pos (hphase s) (hd s)
  by_contra hnot
  have hnon : visibleConnectorA pc wc (a s) ≤ 0 := le_of_not_gt hnot
  have hbad := mul_nonpos_of_nonneg_of_nonpos hfactor.le hnon
  exact (not_lt_of_ge hbad) hpositive

end
end TightVer401