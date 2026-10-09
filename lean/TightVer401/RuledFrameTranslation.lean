import TightVer401.NormalLoopCriterionGeometry
import TightVer401.ThinBandRuledGauss
import TightVer401.CorrugatedSeedFrameHorizontal

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

def PeriodicRuledFrame.translate {L : ℝ} (d : PeriodicRuledFrame L) (c : Ambient) :
    PeriodicRuledFrame L :=
  { d with
    γ := fun r => d.γ r + c
    smooth_γ := d.smooth_γ.add contDiff_const
    period_γ := by
      intro r
      change d.γ (r + L) + c = d.γ r + c
      rw [d.period_γ r]
    deriv_γ := fun r => (d.deriv_γ r).add_const c }

theorem periodicRuledFrame_translate_lift {L : ℝ} (d : PeriodicRuledFrame L) (c : Ambient)
    (q : AddCircle L) : (d.translate c).period_γ.lift q = d.period_γ.lift q + c := by
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective q
  simp only [Function.Periodic.lift_coe, PeriodicRuledFrame.translate]

theorem periodicRuledFrame_translate_bandMap {L b : ℝ} (d : PeriodicRuledFrame L)
    (c : Ambient) (p : AddCircle L × Ioo (0 : ℝ) b) :
    (d.translate c).bandMap p = d.bandMap p + c := by
  rw [PeriodicRuledFrame.bandMap, periodicRuledFrame_translate_lift]
  change (d.period_γ.lift p.1 + c) + (p.2 : ℝ) • d.period_E.lift p.1 =
    (d.period_γ.lift p.1 + (p.2 : ℝ) • d.period_E.lift p.1) + c
  abel

theorem periodicRuledFrame_translate_band_embedding {L b : ℝ} (d : PeriodicRuledFrame L)
    (c : Ambient) (hi : Topology.IsEmbedding (d.bandMap (b := b))) :
    Topology.IsEmbedding ((d.translate c).bandMap (b := b)) := by
  have h : Topology.IsEmbedding ((Homeomorph.addRight c) ∘ d.bandMap (b := b)) :=
    (Homeomorph.addRight c).isEmbedding.comp hi
  have he : (Homeomorph.addRight c) ∘ d.bandMap (b := b) = (d.translate c).bandMap (b := b) := by
    funext p
    exact (periodicRuledFrame_translate_bandMap d c p).symm
  rw [he] at h
  exact h

theorem periodicRuledFrame_translate_horizontal_embedding {L b : ℝ} (d : PeriodicRuledFrame L)
    (c : Ambient) (hi : Topology.IsEmbedding (corrugatedAmbientHorizontalCLM ∘ d.bandMap (b := b))) :
    Topology.IsEmbedding (corrugatedAmbientHorizontalCLM ∘ (d.translate c).bandMap (b := b)) := by
  have h : Topology.IsEmbedding ((Homeomorph.addRight (corrugatedAmbientHorizontalCLM c)) ∘
      (corrugatedAmbientHorizontalCLM ∘ d.bandMap (b := b))) :=
    (Homeomorph.addRight (corrugatedAmbientHorizontalCLM c)).isEmbedding.comp hi
  have he : (Homeomorph.addRight (corrugatedAmbientHorizontalCLM c)) ∘
      (corrugatedAmbientHorizontalCLM ∘ d.bandMap (b := b)) =
      corrugatedAmbientHorizontalCLM ∘ (d.translate c).bandMap (b := b) := by
    funext p
    change corrugatedAmbientHorizontalCLM (d.bandMap p) + corrugatedAmbientHorizontalCLM c =
      corrugatedAmbientHorizontalCLM ((d.translate c).bandMap p)
    rw [periodicRuledFrame_translate_bandMap, map_add]
  rw [he] at h
  exact h

theorem periodicRuledFrame_translate_fullGaussMap {L : ℝ} (d : PeriodicRuledFrame L) (c : Ambient) :
    (d.translate c).fullGaussMap = d.fullGaussMap := rfl

theorem periodicRuledFrame_translate_identity_band {L : ℝ} (d : PeriodicRuledFrame L)
    (c : Ambient) (hidentity : PrincipalNormalIdentityBand d) :
    PrincipalNormalIdentityBand (d.translate c) := by
  let D := d.translate c
  have hX : ContDiff ℝ ∞ (ruledMap D.γ D.E) :=
    (D.smooth_γ.comp (contDiff_apply ℝ ℝ 0)).add
      ((contDiff_apply ℝ ℝ 1).smul (D.smooth_E.comp (contDiff_apply ℝ ℝ 0)))
  refine ⟨hX, ?_, ?_, ?_, ?_⟩
  · intro s u
    change D.γ (s + L) + u • D.E (s + L) = D.γ s + u • D.E s
    rw [D.period_γ s, D.period_E s]
  · intro p
    exact ruled_differential_injective (D.deriv_γ (p 0)) (D.deriv_E (p 0))
      (D.orthonormal (p 0)) (D.torsion_ne_zero (p 0))
  · intro p
    exact ruled_gaussianCurvature_neg D.deriv_γ D.deriv_E hX.contDiffOn isOpen_univ
      (fun p _ => D.orthonormal (p 0)) (fun p _ => D.torsion_ne_zero (p 0)) (mem_univ p)
  · intro s
    obtain ⟨δ, hδ, hflow⟩ := hidentity.2.2.2.2 s
    refine ⟨δ, hδ, fun v hv => ?_⟩
    obtain ⟨hinit, hderiv, _, hreturn⟩ := hflow v hv
    refine ⟨hinit, hderiv, ?_, hreturn⟩
    intro t ht
    have hd := hderiv t ht
    let U : ℝ → ℝ := principalTrajectory (ruledRho D.τ) (ruledOmega D.k D.τ) s v
    change dotProduct (deriv (fun x => (![x, U x] : Coord)) t)
      ((secondFundamental (ruledMap D.γ D.E) (ruledNormal (D.T t) (D.n t) (D.k t) (D.τ t) (U t))
        (![t, U t] : Coord)).mulVec (deriv (fun x => (![x, U x] : Coord)) t)) = 0
    have hdD : HasDerivAt U (-(U t / 2) * (ruledLambda D.τ t + U t * ruledD D.k D.τ t)) t := hd
    rw [(ruled_graph_hasDerivAt hdD).deriv]
    apply (ruled_asymptotic_slope D.deriv_γ D.deriv_E (D.deriv_T t) (D.deriv_n t)
      (D.smooth_k.differentiable (by simp) t).hasDerivAt
      (D.smooth_τ.differentiable (by simp) t).hasDerivAt
      hX.contDiffOn isOpen_univ (mem_univ _) (D.orthonormal t) (D.torsion_ne_zero t)).mpr
    rfl

end
end TightVer401
