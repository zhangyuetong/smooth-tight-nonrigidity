import TightVer401.RelativeSaddlePiecewise

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

/-- The actual normal parameter obtained through the genuine inverse tube
charts. Its arbitrary extension outside the tube is never used as geometry. -/
def relativeSaddleNormalParameter {L : ℝ} (γ : ℝ → ℂ)
    (hL : Function.Periodic γ L) (r : ℝ) : Coord → ℝ :=
  seamNormalTubePotential γ hL r (fun p => p 1) (fun _ => rfl)

def relativeSaddleTubeSide {L : ℝ} (γ : ℝ → ℂ)
    (hL : Function.Periodic γ L) (r : ℝ) : Set Coord :=
  {x | 0 < relativeSaddleNormalParameter γ hL r x}

theorem relativeSaddleNormalParameter_coe {L : ℝ} {γ : ℝ → ℂ}
    (hL : Function.Periodic γ L) {r : ℝ}
    (hi : InjOn (seamNormalNative γ hL) (univ ×ˢ Icc (-r) r))
    (s t : ℝ) (ht : |t| ≤ r) :
    relativeSaddleNormalParameter γ hL r (seamNormalCoordinates γ (![s,t])) = t := by
  exact seamNormalTubePotential_coe hL (fun p => p 1) (fun _ => rfl) hi s t ht

/-- The canonical two-sided partition has no extra boundary in the actual tube.
This supplies the ordinary gluing premise, rather than assuming it. -/
theorem relativeSaddleTubeSide_boundary {L : ℝ} {γ : ℝ → ℂ}
    (hγ : ContDiff ℝ ∞ γ) (hL : Function.Periodic γ L) {r : ℝ}
    (hi : InjOn (seamNormalNative γ hL) (univ ×ˢ Icc (-r) r))
    (hJ : ∀ s t : ℝ, |t| ≤ r →
      (seamCoordinateJacobian (seamNormalCoordinates γ) (![s,t])).det ≠ 0) :
    seamNormalOpenTube γ hL r ∩ frontier (relativeSaddleTubeSide γ hL r) ⊆
      seamNormalSeam γ hL := by
  let T := relativeSaddleNormalParameter γ hL r
  let P := relativeSaddleTubeSide γ hL r
  have hOpen := seamNormalOpenTube_isOpen hγ hL hJ
  have hT : ContDiffOn ℝ ∞ T (seamNormalOpenTube γ hL r) :=
    seamNormalTubePotential_contDiffOn hγ hL hi hJ (by fun_prop) (fun _ => rfl)
  intro x hx
  have hc : ContinuousAt T x := (hT.continuousOn.continuousAt (hOpen.mem_nhds hx.1))
  have hz : T x = 0 := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hn | hn
    · have hmem : Pᶜ ∈ 𝓝 x := by
        filter_upwards [hc.eventually (gt_mem_nhds hn)] with y hy
        change ¬ 0 < T y
        exact not_lt.mpr hy.le
      have hnot : x ∈ (frontier P)ᶜ := by
        rw [compl_frontier_eq_union_interior]
        exact Or.inr (mem_interior_iff_mem_nhds.mpr hmem)
      exact hnot hx.2
    · have hmem : P ∈ 𝓝 x := hc.eventually (lt_mem_nhds hn)
      have hnot : x ∈ (frontier P)ᶜ := by
        rw [compl_frontier_eq_union_interior]
        exact Or.inl (mem_interior_iff_mem_nhds.mpr hmem)
      exact hnot hx.2
  rcases hx.1 with ⟨⟨q,t⟩,hq,rfl⟩
  obtain ⟨s,rfl⟩ := QuotientAddGroup.mk_surjective q
  change T (seamNormalNative γ hL (periodProjection L s,t)) = 0 at hz
  rw [seamNormalNative_coe] at hz
  change relativeSaddleNormalParameter γ hL r (seamNormalCoordinates γ (![s,t])) = 0 at hz
  rw [relativeSaddleNormalParameter_coe hL hi s t (abs_lt.mpr hq.2).le] at hz
  subst t
  exact ⟨periodProjection L s,rfl⟩

/-- A common branch domain yields a regular embedded open collar contained in
that domain. All tubular and openness premises are derived from the seam. -/
theorem relativeSaddleSeam_exists_collar {L : ℝ} [Fact (0 < L)] {γ : ℝ → ℂ}
    (hγ : ContDiff ℝ ∞ γ) (hL : Function.Periodic γ L)
    (hreg : ∀ s, deriv γ s ≠ 0) (hEmbed : Function.Injective hL.lift)
    {U : Set Coord} (hU : IsOpen U) (hSeamU : seamNormalSeam γ hL ⊆ U) :
    ∃ r > 0, InjOn (seamNormalNative γ hL) (univ ×ˢ Icc (-r) r) ∧
      (∀ s t : ℝ, |t| ≤ r →
        (seamCoordinateJacobian (seamNormalCoordinates γ) (![s,t])).det ≠ 0) ∧
      IsOpen (seamNormalOpenTube γ hL r) ∧ seamNormalOpenTube γ hL r ⊆ U := by
  obtain ⟨r₁,hr₁,hi₁,_,hJ₁⟩ := seamNormalNative_exists_regular_embedded_strip hγ hL hreg hEmbed
  obtain ⟨r₂,hr₂,hTube₂⟩ := seamNormalTube_exists_subset_open hγ hL hU hSeamU
  let r := min r₁ r₂
  have hr : 0 < r := lt_min hr₁ hr₂
  have hi : InjOn (seamNormalNative γ hL) (univ ×ˢ Icc (-r) r) := hi₁.mono
    (Set.prod_mono Subset.rfl (Icc_subset_Icc (neg_le_neg (min_le_left _ _)) (min_le_left _ _)))
  have hJ (s t : ℝ) (ht : |t| ≤ r) := hJ₁ s t (ht.trans (min_le_left _ _))
  refine ⟨r,hr,hi,hJ,seamNormalOpenTube_isOpen hγ hL hJ,?_⟩
  exact (image_mono (Set.prod_mono Subset.rfl
    (Ioo_subset_Ioo (neg_le_neg (min_le_right _ _)) (min_le_right _ _)))).trans hTube₂

end
end TightVer401
