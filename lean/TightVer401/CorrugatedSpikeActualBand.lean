import TightVer401.CorrugatedSpikeBand
import TightVer401.RuledFrameTranslation

namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff Manifold Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

theorem corrugatedSeed_balanced_actual_band {N : ℕ} (hN : 10000 ≤ N)
    (e : ℝ ≃ₜ ℝ) (he : (e : ℝ → ℝ) = corrugatedSeedArcMap (N : ℝ))
    (hψ : ContDiff ℝ ∞ e.symm)
    (hi : ∀ r, HasDerivAt e.symm (corrugatedSeedSphericalSpeed (N : ℝ) (e.symm r))⁻¹ r)
    {a : ℝ → ℝ} (ha : ContDiff ℝ ∞ a)
    (haT : Function.Periodic a (corrugatedSeedArcCell (N : ℝ))) (hapos : ∀ r, 0 < a r)
    (hclose : (∫ r in 0..((N : ℝ) * corrugatedSeedArcCell (N : ℝ)),
      a r • normalLoopTangent (corrugatedSeedSphere (N : ℝ) ∘ e.symm) r) = 0)
    (hbalance : (∫ r in 0..((N : ℝ) * corrugatedSeedArcCell (N : ℝ)),
      deriv (normalLoopCurvature (corrugatedSeedSphere (N : ℝ) ∘ e.symm)) r / Real.sqrt (a r)) = 0)
    (hhinj : Set.InjOn (covariantSpeedCurve (corrugatedSeedArcCell (N : ℝ))
      (corrugatedSeedRotation (N : ℝ)) a (corrugatedSeedFrameHorizontal (N : ℝ) e.symm))
      (Ico 0 ((N : ℝ) * corrugatedSeedArcCell (N : ℝ)))) :
    let ell := corrugatedSeedArcCell (N : ℝ)
    let L := (N : ℝ) * ell
    let ζ := corrugatedSeedSphere (N : ℝ) ∘ e.symm
    ∃ S : ℝ ≃ₜ ℝ, (S : ℝ → ℝ) = rawPrimitive a ∧ ContDiff ℝ ∞ S.symm ∧
      ∃ d : PeriodicRuledFrame (rawPrimitive a L),
        d.γ = corrugatedSeedBalancedSpatial (N : ℝ) e.symm ell a ∘ S.symm ∧
        d.T = normalLoopTangent ζ ∘ S.symm ∧ d.E = deriv ζ ∘ S.symm ∧
        d.n = ζ ∘ S.symm ∧ d.k = normalLoopPhysicalK a (normalLoopCurvature ζ) S.symm ∧
        d.τ = normalLoopPhysicalTau a S.symm ∧ PrincipalNormalIdentityBand d ∧
        ∃ hT : 0 < rawPrimitive a L,
          letI : Fact (0 < rawPrimitive a L) := ⟨hT⟩
          ∃ δ > 0, Topology.IsEmbedding (d.bandMap (b := δ)) ∧
            Topology.IsEmbedding (corrugatedAmbientHorizontalCLM ∘ d.bandMap (b := δ)) ∧
            Function.Injective (fun p : AddCircle (rawPrimitive a L) × Ioo (0 : ℝ) δ =>
              d.fullGaussMap (p.1, (p.2 : ℝ))) ∧
            (∀ p : AddCircle (rawPrimitive a L) × Ioo (0 : ℝ) δ,
              0 < d.fullGaussMap (p.1, (p.2 : ℝ)) 2) := by
  dsimp only
  let ell := corrugatedSeedArcCell (N : ℝ)
  let L := (N : ℝ) * ell
  let ζ := corrugatedSeedSphere (N : ℝ) ∘ e.symm
  obtain ⟨S, hS, hSinfty, d, hγ, hT, hE, hn, hk, hτ, hidentity, hTpos,
    ⟨w, hw, hs, hp, hg⟩, ⟨v, hv, hnorth⟩⟩ :=
    corrugatedSeed_balanced_speed_band hN e he hψ hi ha haT hapos hclose hbalance hhinj
  letI : Fact (0 < rawPrimitive a L) := ⟨hTpos⟩
  let c := corrugatedHorizontal (speedCurve a (corrugatedSeedFrameHorizontal (N : ℝ) e.symm) ell /
    (corrugatedSeedRotation (N : ℝ) - 1))
  let D := d.translate c
  have hDγ : D.γ = corrugatedSeedBalancedSpatial (N : ℝ) e.symm ell a ∘ S.symm := by
    funext s
    change d.γ s + c = corrugatedSeedBalancedSpatial (N : ℝ) e.symm ell a (S.symm s)
    rw [hγ]
    rfl
  let δ := min w v
  have hδ : 0 < δ := lt_min hw hv
  have hsubset : Ioo (0 : ℝ) δ ⊆ Ioo 0 w := fun x hx =>
    ⟨hx.1, hx.2.trans_le (min_le_left w v)⟩
  let j : AddCircle (rawPrimitive a L) × Ioo (0 : ℝ) δ →
      AddCircle (rawPrimitive a L) × Ioo (0 : ℝ) w :=
    fun p => (p.1, Set.inclusion hsubset p.2)
  have hj : Topology.IsEmbedding j :=
    Topology.IsEmbedding.id.prodMap (Topology.IsEmbedding.inclusion hsubset)
  have hsδ : Topology.IsEmbedding (d.bandMap (b := w) ∘ j) := hs.comp hj
  have hpδ : Topology.IsEmbedding ((corrugatedAmbientHorizontalCLM ∘ d.bandMap (b := w)) ∘ j) :=
    hp.comp hj
  have hDspace : Topology.IsEmbedding (D.bandMap (b := δ)) :=
    periodicRuledFrame_translate_band_embedding d c hsδ
  have hDprojection : Topology.IsEmbedding (corrugatedAmbientHorizontalCLM ∘ D.bandMap (b := δ)) :=
    periodicRuledFrame_translate_horizontal_embedding d c hpδ
  refine ⟨S, hS, hSinfty, D, hDγ, hT, hE, hn, hk, hτ,
    periodicRuledFrame_translate_identity_band d c hidentity, hTpos,
    δ, hδ, hDspace, hDprojection, ?_, ?_⟩
  · intro p q heq
    have heq' : d.fullGaussMap ((j p).1, ((j p).2 : ℝ)) =
        d.fullGaussMap ((j q).1, ((j q).2 : ℝ)) := heq
    exact hj.injective (hg heq')
  · intro p
    apply hnorth
    refine ⟨mem_univ _, ?_, p.2.property.2.le.trans (min_le_right w v)⟩
    linarith [p.2.property.1]

end
end TightVer401
