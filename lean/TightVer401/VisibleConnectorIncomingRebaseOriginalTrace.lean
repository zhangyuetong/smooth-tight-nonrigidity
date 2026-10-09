import TightVer401.VisibleConnectorDisplacedSeamPhaseSigns
import TightVer401.VisibleConnectorDisplacedSeamRebase

/-! The rebased lower source is literally the original incoming trace, from
ONE native inverse's right inverse and its retained real phase projection.
No original-source equality or independently chosen phase is assumed. -/
namespace TightVer401
noncomputable section
open Set Function OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem visibleConnectorIncomingRebase_original_trace
    {L : ℝ} [Fact (0 < L)] {p w0 : ℝ → Coord} {w : ℝ × ℝ → Coord}
    (hpL : Periodic p L) (hw0L : Periodic w0 L)
    (hwL : ∀ rho, Periodic (fun s => w (rho, s)) L)
    (e : OpenPartialHomeomorph (ℝ × (AddCircle L × ℝ)) (ℝ × Coord))
    (hef : (e : (ℝ × (AddCircle L × ℝ)) → ℝ × Coord) =
      visibleConnectorDisplacedNativePsi hpL hw0L hwL)
    (rho s : ℝ) (hz : (rho, s) ∈ visibleConnectorDisplacedRealPhaseDomain e p) :
    visibleConnectorRebasedSource (fun t => p t + rho • w0 t) (fun t => w (rho, t))
      (fun t => visibleConnectorDisplacedRealPhase e p (rho, t))
      (fun t => (visibleConnectorDisplacedNativeSolution e p (rho, t)).2) s = p s := by
  have hright := e.right_inv hz.1
  have hrho : (e.symm (rho, p s)).1 = rho := by
    have h := congrArg Prod.fst hright
    rw [hef] at h
    exact h
  have hi : e.symm (rho, p s) = (rho, visibleConnectorDisplacedNativeSolution e p (rho, s)) :=
    Prod.ext hrho rfl
  rw [hi, hef] at hright
  have hactual := congrArg Prod.snd hright
  have hproj := visibleConnectorDisplacedRealPhase_projection e p hz
  change hpL.lift (visibleConnectorDisplacedNativeSolution e p (rho, s)).1 +
    rho • hw0L.lift (visibleConnectorDisplacedNativeSolution e p (rho, s)).1 +
    (visibleConnectorDisplacedNativeSolution e p (rho, s)).2 •
      (hwL rho).lift (visibleConnectorDisplacedNativeSolution e p (rho, s)).1 = p s at hactual
  rw [← hproj, periodicLift_coe, periodicLift_coe, periodicLift_coe] at hactual
  simpa only [visibleConnectorRebasedSource, visibleConnectorSource,
    visibleConnectorRebaseParameter, Function.comp_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one] using hactual

end
end TightVer401
