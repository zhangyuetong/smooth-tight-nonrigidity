import TightVer401.MomentControlBump

namespace TightVer401
noncomputable section
open Set Filter MeasureTheory Metric
open scoped ContDiff Topology

def momentControlRadius (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)

theorem momentControlRadius_pos (k : ℕ) : 0 < momentControlRadius k := by
  unfold momentControlRadius
  positivity

theorem momentControlRadius_tendsto : Tendsto momentControlRadius atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

def momentControlSequence (c : ℝ) (k : ℕ) : ℝ → ℝ :=
  normalizedMomentControl c (momentControlRadius k) (momentControlRadius_pos k)

theorem momentControlSequence_moment_tendsto {m : ℕ} {f : ℝ → EuclideanSpace ℝ (Fin m)}
    (hf : Continuous f) (c : ℝ) :
    Tendsto (fun k => realControlMoment f (momentControlSequence c k)) atTop (𝓝 (f c)) :=
  normedBump_moment_tendsto hf (b := fun k => momentControlBump c (momentControlRadius k)
    (momentControlRadius_pos k)) momentControlRadius_tendsto

theorem momentControlSequence_eventually_independent {m n : ℕ}
    {f : ℝ → EuclideanSpace ℝ (Fin m)} (hf : Continuous f) (c : Fin n → ℝ)
    (hLI : LinearIndependent ℝ (fun j => f (c j))) :
    ∀ᶠ k : ℕ in atTop, LinearIndependent ℝ
      (fun j => realControlMoment f (momentControlSequence (c j) k)) := by
  have hT : Tendsto (fun k j => realControlMoment f (momentControlSequence (c j) k))
      atTop (𝓝 (fun j => f (c j))) :=
    tendsto_pi_nhds.mpr (fun j => momentControlSequence_moment_tendsto hf (c j))
  exact hT.eventually hLI.eventually

def momentSampleSpan {m : ℕ} (f : ℝ → EuclideanSpace ℝ (Fin m)) (S : Set ℝ) :=
  Submodule.span ℝ (f '' S)

theorem exists_independent_moment_samples {m : ℕ} (f : ℝ → EuclideanSpace ℝ (Fin m))
    (S : Set ℝ) :
    ∃ c : Fin (Module.finrank ℝ (momentSampleSpan f S)) → ℝ,
      (∀ j, c j ∈ S) ∧ LinearIndependent ℝ (fun j => f (c j)) ∧
      Submodule.span ℝ (Set.range (fun j => f (c j))) = momentSampleSpan f S := by
  classical
  obtain ⟨v, hv, hvspan, hvLI⟩ := Submodule.exists_fun_fin_finrank_span_eq ℝ (f '' S)
  choose c hc hfc using hv
  have hfun : (fun j => f (c j)) = v := funext hfc
  exact ⟨c, hc, hfun ▸ hvLI, hfun ▸ hvspan⟩

theorem realControlMoment_mem_span {m : ℕ} {f : ℝ → EuclideanSpace ℝ (Fin m)}
    {S : Set ℝ} {ψ : ℝ → ℝ} (hψ : Function.support ψ ⊆ S) :
    realControlMoment f ψ ∈ momentSampleSpan f S := by
  let V := momentSampleSpan f S
  have hmem (x : ℝ) : ψ x • f x ∈ V := by
    by_cases hx : ψ x = 0
    · simp [hx]
    · exact V.smul_mem _ (Submodule.subset_span ⟨x, hψ hx, rfl⟩)
  let F : ℝ → V := fun x => ⟨ψ x • f x, hmem x⟩
  have hI := V.subtypeₗᵢ.integral_comp_comm (μ := volume) F
  change realControlMoment f ψ = ((∫ x, F x : V) : EuclideanSpace ℝ (Fin m)) at hI
  rw [hI]
  exact (∫ x, F x : V).property

theorem independent_control_moments_span {m : ℕ} {f : ℝ → EuclideanSpace ℝ (Fin m)}
    {S : Set ℝ} (ψ : Fin (Module.finrank ℝ (momentSampleSpan f S)) → ℝ → ℝ)
    (hψ : ∀ j, Function.support (ψ j) ⊆ S)
    (hLI : LinearIndependent ℝ (fun j => realControlMoment f (ψ j))) :
    Submodule.span ℝ (Set.range (fun j => realControlMoment f (ψ j))) = momentSampleSpan f S := by
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact realControlMoment_mem_span (hψ j)
  · simpa only [Fintype.card_fin] using finrank_span_eq_card hLI

theorem momentControlSequence_eventually_contained {n : ℕ} (c : Fin n → ℝ) (L : ℝ)
    (hc : ∀ j, c j ∈ Ioo 0 L) :
    ∀ᶠ k : ℕ in atTop, ∀ j, tsupport (momentControlSequence (c j) k) ⊆ Ioo 0 L := by
  apply eventually_all.mpr
  intro j
  have hleft : ∀ᶠ k in atTop, momentControlRadius k < c j :=
    momentControlRadius_tendsto.eventually (gt_mem_nhds (hc j).1)
  have hright : ∀ᶠ k in atTop, momentControlRadius k < L - c j :=
    momentControlRadius_tendsto.eventually (gt_mem_nhds (sub_pos.mpr (hc j).2))
  filter_upwards [hleft, hright] with k hkl hkr
  rw [momentControlSequence, normalizedMomentControl_tsupport]
  intro x hx
  constructor <;> linarith [hx.1, hx.2]

theorem momentControlSequence_eventually_disjoint {n : ℕ} (c : Fin n → ℝ)
    (hc : Function.Injective c) :
    ∀ᶠ k : ℕ in atTop, Pairwise
      (fun i j => Disjoint (tsupport (momentControlSequence (c i) k))
        (tsupport (momentControlSequence (c j) k))) := by
  have hpair : ∀ i j : Fin n, ∀ᶠ k : ℕ in atTop, i ≠ j →
      momentControlRadius k + momentControlRadius k < dist (c i) (c j) := by
    intro i j
    by_cases hij : i = j
    · filter_upwards with k hk
      exact False.elim (hk hij)
    · have hdist : 0 < dist (c i) (c j) := dist_pos.mpr (fun h => hij (hc h))
      have hT : Tendsto (fun k => momentControlRadius k + momentControlRadius k) atTop (𝓝 0) := by
        simpa only [zero_add] using momentControlRadius_tendsto.add momentControlRadius_tendsto
      exact (hT.eventually (gt_mem_nhds hdist)).mono
        (fun k hk _ => hk)
  have hall : ∀ᶠ k in atTop, ∀ i j : Fin n, i ≠ j →
      momentControlRadius k + momentControlRadius k < dist (c i) (c j) :=
    eventually_all.mpr (fun i => eventually_all.mpr (hpair i))
  filter_upwards [hall] with k hk
  intro i j hij
  rw [momentControlSequence, momentControlSequence, normalizedMomentControl_tsupport,
    normalizedMomentControl_tsupport, ← Real.closedBall_eq_Icc, ← Real.closedBall_eq_Icc]
  exact closedBall_disjoint_closedBall (hk i j hij)

theorem momentControlSequence_eventually_avoids {n : ℕ} (c : Fin n → ℝ) (a : ℝ)
    (ha : ∀ j, c j ≠ a) :
    ∀ᶠ k : ℕ in atTop, ∀ j,
      Disjoint (tsupport (momentControlSequence (c j) k)) (closedBall a (momentControlRadius k)) := by
  apply eventually_all.mpr
  intro j
  have hT : Tendsto (fun k => momentControlRadius k + momentControlRadius k) atTop (𝓝 0) := by
    simpa only [zero_add] using momentControlRadius_tendsto.add momentControlRadius_tendsto
  have hdist : 0 < dist (c j) a := dist_pos.mpr (ha j)
  have hsmall : ∀ᶠ k in atTop,
      momentControlRadius k + momentControlRadius k < dist (c j) a := by
    simpa only [zero_add] using hT.eventually (gt_mem_nhds hdist)
  filter_upwards [hsmall] with k hk
  rw [momentControlSequence, normalizedMomentControl_tsupport, ← Real.closedBall_eq_Icc]
  exact closedBall_disjoint_closedBall hk

end
end TightVer401
