import TightVer401.DualRadialCompletionCircularDegree
import TightVer401.DualRadialCompletionEndGradients
import TightVer401.DualRadialCompletionExhaustion
import TightVer401.DualRadialCompletionGlobalInverse

/-! The literal radial ends feed the local degree specialization and then
actual compact-band exhaustion. This is a conditional producer consumer,
not a construction of the missing connector/filling pieces or degree proof.
-/
namespace TightVer401
noncomputable section
open Set Function OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

/-- From actual scalar end formulas, a local circular-degree producer proves
the exact global actual gradient annulus and a smooth inverse. No global
injection, global image or completed inverse is assumed. -/
theorem exists_dualRadialCompletion_gradient_inverse_of_circular_degree
    (hDegree : DualRadialCompletionCircularDegreeClaim)
    {G : Coord → ℝ} {A RN mu B d0 dInfinity epsilon0 L0 : ℝ}
    (hA : 0 < A) (hAR : A < RN) (hmu : 0 < mu) (hB : 0 < B)
    (hepsilon0 : 0 < epsilon0)
    (hG : ContDiffOn ℝ ∞ G {p | 0 < planarRadius p})
    (hneg : ∀ p, 0 < planarRadius p → (planarHessian G p).det < 0)
    (hInner : EqOn G (fun p => RN * planarRadius p - mu * planarRadius p ^ 2 / 2 + d0)
      {p | 0 < planarRadius p ∧ planarRadius p < epsilon0})
    (hOuter : EqOn G (fun p => A * planarRadius p - B / planarRadius p + dInfinity)
      {p | L0 < planarRadius p}) :
    ∃ e : OpenPartialHomeomorph Coord Coord,
      e.source = {p | 0 < planarRadius p} ∧
      e.target = {y | A < planarRadius y ∧ planarRadius y < RN} ∧
      (e : Coord → Coord) = planarGradient G ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  have hU : IsOpen {p : Coord | 0 < planarRadius p} :=
    isOpen_lt continuous_const quadraticFillerCartesianGradient_radius_continuous
  have hBands : ∀ epsilon L : ℝ, 0 < epsilon → epsilon < epsilon0 → L0 < L →
      epsilon < L → A + B / L ^ 2 < RN - mu * epsilon →
      BijOn (planarGradient G)
        {p : Coord | epsilon < planarRadius p ∧ planarRadius p < L}
        {y : Coord | A + B / L ^ 2 < planarRadius y ∧ planarRadius y < RN - mu * epsilon} := by
    intro epsilon L hepsilon hepsilon0' hL0 hepsilonL horder
    have hL : 0 < L := hepsilon.trans hepsilonL
    have hLower : 0 < A + B / L ^ 2 :=
      add_pos hA (div_pos hB (sq_pos_of_pos hL))
    apply hDegree G {p | 0 < planarRadius p} epsilon L
      (A + B / L ^ 2) (RN - mu * epsilon) hepsilon hepsilonL hLower horder hU hG
    · intro p hp
      exact hepsilon.trans_le hp.1
    · intro p hp _
      exact hneg p (hepsilon.trans hp)
    · exact dualRadialCompletionEndGradients_inner_circle hInner hepsilon hepsilon0'
    · exact dualRadialCompletionEndGradients_outer_circle hOuter hL hL0
  exact exists_dualRadialCompletion_gradient_inverse hG hneg
    (dualRadialCompletionExhaustion_bijOn hA hAR hmu hB hepsilon0 hBands)

end
end TightVer401
