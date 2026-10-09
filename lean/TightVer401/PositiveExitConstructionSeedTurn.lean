import TightVer401.PositiveExitConstructionBalancedTurn
import TightVer401.IdentityBandCentralSupport

/-! The actual turn tolerance is selected before the SAME correction speed.
The original actual tensor/support producer is called once with that smaller
scalar tolerance. No corrected seed is replaced after its potential is made. -/
open scoped Manifold
namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff Topology Matrix RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false

/-- Construct the original actual central potential with its SAME balanced
partner's proved origin turn, choosing the scalar tolerance before the seed. -/
theorem positiveExit_central_support_with_balanced_turn {N : ℕ} (hN : 10000 ≤ N)
    {η : ℝ} (hη : 0 < η) :
    let ell := corrugatedSeedArcCell (N : ℝ)
  let L := (N : ℝ) * ell
    ∃ e : ℝ ≃ₜ ℝ, (e : ℝ → ℝ) = corrugatedSeedArcMap (N : ℝ) ∧
      ContDiff ℝ ∞ e.symm ∧
      ∃ a : ℝ → ℝ, ContDiff ℝ ∞ a ∧ Function.Periodic a ell ∧ (∀ r, 0 < a r) ∧
        (∫ r in 0..ell, ‖a r - corrugatedSeedInitialSpeed (N : ℝ) e.symm r‖) < η ∧
        (∫ r in 0..L, a r • normalLoopTangent (corrugatedSeedSphere (N : ℝ) ∘ e.symm) r) = 0 ∧
        (∫ r in 0..L, deriv (normalLoopCurvature (corrugatedSeedSphere (N : ℝ) ∘ e.symm)) r /
          Real.sqrt (a r)) = 0 ∧
        HasPositiveArgumentTurn (corrugatedSeedBalancedPartner (N : ℝ) e.symm ell a) L ∧
        ComplexVisiblePair (1 / 4) (corrugatedSeedBeta (N : ℝ) ∘ e.symm)
          (corrugatedSeedBalancedPartner (N : ℝ) e.symm ell a) ∧
        ComplexVisiblePair (4 / 5)
          (corrugatedReverseReflect (corrugatedSeedBalancedPartner (N : ℝ) e.symm ell a))
          (corrugatedReverseReflect (corrugatedSeedBeta (N : ℝ) ∘ e.symm)) ∧
        ∃ S : ℝ ≃ₜ ℝ, (S : ℝ → ℝ) = rawPrimitive a ∧ ContDiff ℝ ∞ S.symm ∧
          ∃ d : PeriodicRuledFrame (rawPrimitive a L),
            d.γ = corrugatedSeedBalancedSpatial (N : ℝ) e.symm ell a ∘ S.symm ∧
            d.T = normalLoopTangent (corrugatedSeedSphere (N : ℝ) ∘ e.symm) ∘ S.symm ∧
            d.E = deriv (corrugatedSeedSphere (N : ℝ) ∘ e.symm) ∘ S.symm ∧
            d.n = (corrugatedSeedSphere (N : ℝ) ∘ e.symm) ∘ S.symm ∧
            d.k = normalLoopPhysicalK a
              (normalLoopCurvature (corrugatedSeedSphere (N : ℝ) ∘ e.symm)) S.symm ∧
            d.τ = normalLoopPhysicalTau a S.symm ∧ PrincipalNormalIdentityBand d ∧
            ∃ hT : 0 < rawPrimitive a L,
              letI : Fact (0 < rawPrimitive a L) := ⟨hT⟩
              ∃ w > 0, IdentityBandTwoSidedCollar d w ∧
                ProtectedIdentityBendingSubband d w ∧
                ∃ G : Coord → ℝ, ∃ U : Set Coord,
                  IdentityBandCentralSupportWithPotential d w a
                    (normalLoopCurvature (corrugatedSeedSphere (N : ℝ) ∘ e.symm)) S G U := by
  dsimp only
  let ell := corrugatedSeedArcCell (N : ℝ)
  let L := (N : ℝ) * ell
  obtain ⟨etaTurn, hetaTurn, hturn⟩ :=
    positiveExit_balancedPartner_positive_turn_uniform_threshold hN
  obtain ⟨e,he,hes,a,ha,hap,hapos,hsmall,hM,hB,hout,href,S,hS,hSs,
      d,hgamma,hTan,hE,hn,hk,htau,hidentity,hT,w,hw,hcollar,hprotected,G,U,hc⟩ :=
    identityBand_central_support_tensor hN (lt_min hη hetaTurn)
  have hsmallEta : (∫ r in 0..ell,
      ‖a r - corrugatedSeedInitialSpeed (N : ℝ) e.symm r‖) < η :=
    lt_of_lt_of_le hsmall (min_le_left _ _)
  have hsmallTurn : (∫ r in 0..ell,
      ‖a r - corrugatedSeedInitialSpeed (N : ℝ) e.symm r‖) < etaTurn :=
    lt_of_lt_of_le hsmall (min_le_right _ _)
  have ht := hturn e he a ha hap hsmallTurn
  exact ⟨e,he,hes,a,ha,hap,hapos,hsmallEta,hM,hB,ht,hout,href,S,hS,hSs,
    d,hgamma,hTan,hE,hn,hk,htau,hidentity,hT,w,hw,hcollar,hprotected,G,U,hc⟩

end
end TightVer401
