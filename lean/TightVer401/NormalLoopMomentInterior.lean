import TightVer401.NormalLoopMomentCone

namespace TightVer401
noncomputable section
open Set Filter MeasureTheory Metric
open scoped ContDiff Topology BigOperators

theorem circleMomentSpan_eq_top_of_origin_interior {m : ℕ} (L : ℝ)
    (f : AddCircle L → EuclideanSpace ℝ (Fin m))
    (h0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ interior (convexHull ℝ (Set.range f))) :
    circleMomentSpan L f = ⊤ := by
  have hsub : convexHull ℝ (Set.range f) ⊆ (circleMomentSpan L f : Set _) :=
    convexHull_min Submodule.subset_span (circleMomentSpan L f).convex
  exact (circleMomentSpan L f).eq_top_of_nonempty_interior'
    ⟨0, interior_mono hsub h0⟩

theorem nonnegativeSmoothPeriodMoments_interior_of_basis {m n : ℕ} (L : ℝ)
    {f : ℝ → EuclideanSpace ℝ (Fin m)} (hf : Continuous f)
    (ψ : Fin n → ℝ → ℝ) (hψ : ∀ j, ContDiff ℝ ∞ (ψ j))
    (hp : ∀ j, Function.Periodic (ψ j) L) (hn : ∀ j s, 0 ≤ ψ j s)
    (B : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin m)))
    (hB : ∀ j, B j = momentPathMoment L f (ψ j)) :
    (interior (nonnegativeSmoothPeriodMoments L f)).Nonempty := by
  let T := B.equivFunL
  let O : Set (EuclideanSpace ℝ (Fin m)) := {v | ∀ j, 0 < T v j}
  have hO : IsOpen O := by
    change IsOpen {v | ∀ j, 0 < T v j}
    simpa only [ofPred_forall, Function.comp_apply] using isOpen_iInter_of_finite
      (fun j : Fin n => isOpen_lt continuous_const ((continuous_apply j).comp T.continuous))
  have hsub : O ⊆ nonnegativeSmoothPeriodMoments L f := by
    intro v hv
    refine ⟨momentPathCorrection (T v) ψ, momentPathCorrection_contDiff _ hψ, ?_, ?_, ?_⟩
    · intro s
      simp [momentPathCorrection, fun j => hp j s]
    · intro s
      exact Finset.sum_nonneg (fun j _ => mul_nonneg (hv j).le (hn j s))
    · rw [momentPathMoment_correction L (T v) (fun j => (hψ j).continuous) hf]
      simp_rw [← hB]
      simpa only [T, Module.Basis.equivFunL_apply, Module.Basis.equivFun_apply] using B.sum_equivFun v
  let v := T.symm (fun _ => (1 : ℝ))
  have hv : v ∈ O := by
    intro j
    simp [v]
  exact ⟨v, interior_mono hsub (hO.interior_eq.symm ▸ hv)⟩

theorem nonnegativeSmoothPeriodMoments_interior_of_full_span {m : ℕ} (L : ℝ)
    [hL : Fact (0 < L)] {f : AddCircle L → EuclideanSpace ℝ (Fin m)}
    (hf : Continuous f) (hg : ContDiff ℝ ∞ (f ∘ periodProjection L))
    (hspan : circleMomentSpan L f = ⊤) :
    (interior (nonnegativeSmoothPeriodMoments L (f ∘ periodProjection L))).Nonempty := by
  letI := periodCircleChartedSpace L
  let g := f ∘ periodProjection L
  have ha : L / 2 ∈ Ioo 0 L := ⟨half_pos hL.out, half_lt_self hL.out⟩
  obtain ⟨r, Ψ, χ, hr, _, _, _, hΨsmooth, hΨnonneg, _, _, _, _, _, _, _, _, _, hLI, hΨspan⟩ :=
    exists_short_circle_moment_controls L f hf hg ha zero_lt_one
  let ψ := fun j => Ψ j ∘ periodProjection L
  have hψ (j) : ContDiff ℝ ∞ (ψ j) :=
    ((hΨsmooth j).comp (periodProjection_contMDiff L)).contDiff
  have hp (j) : Function.Periodic (ψ j) L := by
    intro s
    change Ψ j ((s + L : ℝ) : AddCircle L) = Ψ j (s : AddCircle L)
    rw [AddCircle.coe_add_period]
  have hm (j) : circleControlMoment L f (Ψ j) = momentPathMoment L g (ψ j) := rfl
  let B := Module.Basis.mk hLI (by rw [hΨspan, hspan])
  apply nonnegativeSmoothPeriodMoments_interior_of_basis L hg.continuous ψ hψ hp
    (fun j s => hΨnonneg j (periodProjection L s)) B
  intro j
  simp only [B, Module.Basis.mk_apply, hm, g]

theorem origin_interior_nonnegativeSmoothPeriodMoments {m : ℕ} (L : ℝ)
    [Fact (0 < L)] {f : AddCircle L → EuclideanSpace ℝ (Fin m)}
    (hf : Continuous f) (hg : ContDiff ℝ ∞ (f ∘ periodProjection L))
    (h0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ interior (convexHull ℝ (Set.range f))) :
    (0 : EuclideanSpace ℝ (Fin m)) ∈
      interior (nonnegativeSmoothPeriodMoments L (f ∘ periodProjection L)) := by
  have hi := nonnegativeSmoothPeriodMoments_interior_of_full_span L hf hg
    (circleMomentSpan_eq_top_of_origin_interior L f h0)
  have hc := nonnegativeSmoothPeriodMoments_convex L hg.continuous
  rw [← hc.interior_closure_eq_interior_of_nonempty_interior hi]
  exact interior_mono (circle_convexHull_subset_closure_nonnegativeSmoothPeriodMoments L hf) h0

end
end TightVer401
