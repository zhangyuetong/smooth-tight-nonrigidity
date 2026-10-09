import TightVer401.SeamNormalRegularTube
import TightVer401.SmoothingTubeTransfer

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

def seamNormalSeam {L : ℝ} (γ : ℝ → ℂ) (hL : Function.Periodic γ L) : Set Coord :=
  range (fun q : AddCircle L => seamNormalNative γ hL (q,0))

theorem seamNormalSeam_isClosed {L : ℝ} [Fact (0 < L)] {γ : ℝ → ℂ}
    (hγ : ContDiff ℝ ∞ γ) (hL : Function.Periodic γ L) :
    IsClosed (seamNormalSeam γ hL) := by
  apply IsCompact.isClosed
  exact isCompact_range ((seamNormalNative_continuous hγ hL).comp (continuous_id.prodMk continuous_const))

theorem seamNormalSeam_subset_openTube {L : ℝ} {γ : ℝ → ℂ}
    (hL : Function.Periodic γ L) {r : ℝ} (hr : 0 < r) :
    seamNormalSeam γ hL ⊆ seamNormalOpenTube γ hL r := by
  rintro _ ⟨q,rfl⟩
  exact ⟨(q,0),⟨mem_univ _,⟨neg_neg_of_pos hr,hr⟩⟩,rfl⟩

theorem seamNormalOpenTube_frontier_representative {L : ℝ} [Fact (0 < L)] {γ : ℝ → ℂ}
    (hγ : ContDiff ℝ ∞ γ) (hL : Function.Periodic γ L) {r : ℝ}
    (hOpen : IsOpen (seamNormalOpenTube γ hL r)) {x : Coord}
    (hx : x ∈ frontier (seamNormalOpenTube γ hL r)) :
    ∃ s t : ℝ, |t|=r ∧ x=seamNormalCoordinates γ (![s,t]) := by
  let C := seamNormalNative γ hL '' ((univ : Set (AddCircle L)) ×ˢ Icc (-r) r)
  have hC : IsClosed C := ((isCompact_univ.prod isCompact_Icc).image
    (seamNormalNative_continuous hγ hL)).isClosed
  have hTC : seamNormalOpenTube γ hL r ⊆ C :=
    image_mono (prod_mono Subset.rfl Ioo_subset_Icc_self)
  have hxC : x ∈ C := (closure_minimal hTC hC) (frontier_subset_closure hx)
  rcases hxC with ⟨⟨q,t⟩,hq,rfl⟩
  have ht : |t| ≤ r := abs_le.mpr hq.2
  have hn : ¬ |t| < r := by
    intro hlt
    have hxT : seamNormalNative γ hL (q,t) ∈ seamNormalOpenTube γ hL r :=
      ⟨(q,t),⟨mem_univ _,abs_lt.mp hlt⟩,rfl⟩
    rw [hOpen.frontier_eq] at hx
    exact hx.2 hxT
  obtain ⟨s,rfl⟩ := QuotientAddGroup.mk_surjective q
  exact ⟨s,t,le_antisymm ht (le_of_not_gt hn),seamNormalNative_coe hL s t⟩

/-- Every prescribed open seam neighborhood contains an actual uniform tube. -/
theorem seamNormalTube_exists_subset_open {L : ℝ} [hLpos : Fact (0 < L)] {γ : ℝ → ℂ}
    (hγ : ContDiff ℝ ∞ γ) (hL : Function.Periodic γ L) {N : Set Coord}
    (hN : IsOpen N) (hSeam : seamNormalSeam γ hL ⊆ N) :
    ∃ r > 0, seamNormalOpenTube γ hL r ⊆ N := by
  let U := (seamNormalCoordinates γ) ⁻¹' N
  have hU : IsOpen U := hN.preimage (seamNormalCoordinates_contDiff hγ).continuous
  have hAxis (s : ℝ) : (![s,0] : Coord) ∈ U := by
    apply hSeam
    exact ⟨periodProjection L s,(seamNormalNative_coe hL s 0).symm⟩
  obtain ⟨r,hr,hInside⟩ := seam_compact_axis_open_collar (isCompact_Icc : IsCompact (Icc (0 : ℝ) L))
    hU (fun s _ => hAxis s)
  refine ⟨r,hr,?_⟩
  rintro _ ⟨⟨q,t⟩,hq,rfl⟩
  obtain ⟨s,rfl⟩ := QuotientAddGroup.mk_surjective q
  change seamNormalNative γ hL (periodProjection L s,t) ∈ N
  rw [seamNormalNative_coe]
  have hp : Function.Periodic (fun v : ℝ => seamNormalCoordinates γ (![v,t])) L :=
    fun v => seamNormalCoordinates_periodic hL (![v,t])
  rw [seam_periodic_eq_representative hLpos.out hp s]
  exact hInside _ (Ico_subset_Icc_self (toIcoMod_mem_Ico' hLpos.out s)) t (abs_lt.mpr hq.2).le

end
end TightVer401
