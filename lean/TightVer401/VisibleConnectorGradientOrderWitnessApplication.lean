import TightVer401.VisibleConnectorGradientOrderPhysical
import TightVer401.VisibleConnectorWitnessAssemblyInputs

/-! The canonical incoming/terminal consumer of the frozen order proof.
The actual full incoming germ supplies its final-gradient boundary equation;
the two existing trace enclosure facts supply common point zero. -/
namespace TightVer401
noncomputable section
open Set Function OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

/-- Supply the canonical ordinary-data gradient nesting field without a
target-nesting or gradient-inverse premise. Retain the caller's SAME final G,
terminal trace, original incoming trace and already selected four fillings. -/
theorem visibleConnectorGradientOrder_retained_incoming_terminal
    {Gin G : Coord → ℝ} {Uin U N : Set Coord} {L R : ℝ} [Fact (0 < L)]
    (D : VisibleConnectorIncomingData Gin Uin L R)
    (T : PositiveExitTrace G U L) {Ho Hi To Ti : ℂ ≃ₜ ℂ}
    (hSourceOuter : PositiveJordanParametrization Ho
      (fun t => seamComplexCoord.symm (T.p (L*t))))
    (hSourceInner : PositiveJordanParametrization Hi
      (fun t => seamComplexCoord.symm (D.incoming.p (L*t))))
    (hTargetInner : PositiveJordanParametrization Ti
      (fun t => seamComplexCoord.symm (T.gamma (L*t))))
    (hTargetOuter : PositiveJordanParametrization To
      (fun t => seamComplexCoord.symm (D.incoming.gamma (L*t))))
    (hSourceNested : closure (positiveExitInside D.incoming.p) ⊆ positiveExitInside T.p)
    (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U)
    (hKU : closure (positiveExitInside T.p \ closure (positiveExitInside D.incoming.p)) ⊆ U)
    (hNeg : ∀ q ∈ positiveExitInside T.p \ closure (positiveExitInside D.incoming.p),
      (planarHessian G q).det < 0)
    (hN : IsOpen N) (hpN : range D.incoming.p ⊆ N) (hGerm : EqOn G Gin N)
    (hDisjoint : Disjoint (range D.incoming.gamma) (range T.gamma)) :
    closure (positiveExitInside T.gamma) ⊆ positiveExitInside D.incoming.gamma := by
  obtain ⟨hIncoming,_hIncomingPairing⟩ :=
    visibleConnectorWitnessAssembly_incoming_germ D hN hpN hGerm
  have hTerminal : ∀ s, planarGradient G (T.p s) = T.gamma s := by
    intro s
    rw [T.actual_gradient]
    rfl
  exact visibleConnectorGradientOrder_physical T.period_pos hSourceOuter hSourceInner
    hTargetInner hTargetOuter T.source_jordan D.incoming.source_jordan
    T.gradient_jordan D.incoming.gradient_jordan hSourceNested hU hG hKU hNeg
    hTerminal (fun s => (hIncoming s).2) hDisjoint.symm
    T.gradient_enclosure D.incoming.gradient_enclosure

end
end TightVer401
