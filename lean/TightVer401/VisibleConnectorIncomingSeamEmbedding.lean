import TightVer401.VisibleConnectorDisplacedSeamPhaseSigns
import TightVer401.VisibleConnectorIncomingCollar

/-! Embedding of the actual displaced seam through the SAME native inverse.
The new seam's injectivity is a conclusion of source membership and inverse
identities, rather than an independent geometry assumption. -/
namespace TightVer401
noncomputable section
open Set Function OAI.SmoothLocal.Geometry
open scoped Topology ContDiff Matrix
set_option backward.isDefEq.respectTransparency false

/-- Every source slice at zero height embeds the actual displaced central
circle. Retain this inverse when later selecting all rho-smallness bounds. -/
theorem visibleConnectorIncomingSeam_displaced_isClosedEmbedding
    {L : ℝ} [Fact (0 < L)] {p w0 : ℝ → Coord} {w : ℝ × ℝ → Coord}
    (hp : ContDiff ℝ ∞ p) (hw0 : ContDiff ℝ ∞ w0)
    (hpL : Periodic p L) (hw0L : Periodic w0 L)
    (hwL : ∀ rho, Periodic (fun s => w (rho, s)) L)
    (e : OpenPartialHomeomorph (ℝ × (AddCircle L × ℝ)) (ℝ × Coord))
    (hef : (e : (ℝ × (AddCircle L × ℝ)) → ℝ × Coord) =
      visibleConnectorDisplacedNativePsi hpL hw0L hwL)
    (rho : ℝ) (hsource : ∀ q : AddCircle L, (rho, (q, 0)) ∈ e.source) :
    Topology.IsClosedEmbedding (fun q : AddCircle L => hpL.lift q + rho • hw0L.lift q) := by
  have hforward (q : AddCircle L) :
      e (rho, (q, 0)) = (rho, hpL.lift q + rho • hw0L.lift q) := by
    rw [hef]
    simp [visibleConnectorDisplacedNativePsi]
  have hinj : Injective (fun q : AddCircle L => hpL.lift q + rho • hw0L.lift q) := by
    intro q r hqr
    have heq : e (rho, (q, 0)) = e (rho, (r, 0)) := by
      rw [hforward, hforward]
      exact Prod.ext rfl hqr
    have hnative := e.injOn (hsource q) (hsource r) heq
    exact congrArg (fun z : ℝ × (AddCircle L × ℝ) => z.2.1) hnative
  have hc : Continuous (fun q : AddCircle L => hpL.lift q + rho • hw0L.lift q) :=
    (periodicLift_contMDiff hp hpL).continuous.add
      ((continuous_const (y := rho)).smul (periodicLift_contMDiff hw0 hw0L).continuous)
  exact hc.isClosedEmbedding hinj

end
end TightVer401

