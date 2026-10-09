import OAI.Geometry.WeakMTW.Geodesics.HopfRinow

/-! Intrinsic-isometry rigidity on closed Riemannian manifolds, using the
OpenAI construction and uniqueness of actual minimizing geodesics. The general
noncompact and boundary extensions of manuscript lem:fixed-open are separate. -/
open Manifold Bundle Set Filter
open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
open OAI.WeakMTWGlobalSupport OAI.WeakMTWGlobalSupport.WeakMTW
open OAI.WeakMTWGlobalSupport.RiemannianLocal

theorem isometry_eq_id_of_fixed_open_compact
    {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
    [IsManifold (model n) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
    [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
      (fun x : M => TangentSpace (model n) x)]
    [IsRiemannianManifold (model n) M] [CompactSpace M] [ConnectedSpace M]
    {f : M → M} (hf : Isometry f) (hfs : ContMDiff (model n) (model n) ∞ f)
    {U : Set M} (hU : IsOpen U) (hne : U.Nonempty) (hfix : ∀ p ∈ U, f p = p) :
    f = id := by
  obtain ⟨p, hp⟩ := hne
  funext q
  by_cases hpq : p = q
  · subst q
    exact hfix p hp
  obtain ⟨b, hbp, _, hbq⟩ := exists_minimizing_unit_geodesic (n := n) hpq
  let γ : ℝ → M := geodesic b
  have hγ : ContMDiff 𝓘(ℝ, ℝ) (model n) ∞ γ := geodesic_smooth b
  have hγ0 : γ 0 = p := (geodesic_zero b).trans hbp
  have hγU : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ U :=
    hγ.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds (by rwa [hγ0]))
  have he : (f ∘ γ) =ᶠ[𝓝 0] γ := by
    filter_upwards [hγU] with t ht
    exact hfix (γ t) ht
  have hηdist : ∀ a, ∃ ε : ℝ, 0 < ε ∧
      ∀ s ∈ Metric.ball a ε, ∀ t ∈ Metric.ball a ε,
        dist ((f ∘ γ) s) ((f ∘ γ) t) = ‖b.2‖ * |s - t| := by
    intro a
    obtain ⟨ε, hε, hd⟩ := geodesic_dist b a
    refine ⟨ε, hε, ?_⟩
    intro s hs t ht
    rw [Function.comp_apply, Function.comp_apply, hf.dist_eq]
    exact hd s hs t ht
  have hη : ContMDiff 𝓘(ℝ, ℝ) (model n) ∞ (f ∘ γ) := hfs.comp hγ
  have hall : f ∘ γ = γ := intrinsic_global_unique hη hγ
    (norm_nonneg b.2) (norm_nonneg b.2) hηdist (geodesic_dist b) (curveState_congr he)
  have h := congrFun hall (dist p q)
  change f (geodesic b (dist p q)) = geodesic b (dist p q) at h
  simpa only [hbq, id_eq] using h

end
end TightVer401
