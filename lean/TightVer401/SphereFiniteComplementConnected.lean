import TightVer401.SphereCharts
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Geometry.Manifold.Instances.Sphere

/-! A finite puncture set leaves the actual round sphere path connected.
Stereographic projection is taken from a puncture; only punctures in its source
are projected, so arbitrary outside-source values introduce no extra puncture. -/
namespace TightVer401
noncomputable section
open Set Metric OAI.SmoothLocal.Geometry
open scoped Topology
set_option backward.isDefEq.respectTransparency false

local instance sphereFiniteComplementDimension :
    Fact (Module.finrank ℝ Ambient = 2 + 1) := ⟨by simp [Ambient]⟩

/-- Removing any finite set from the actual round sphere leaves a nonempty
path-connected set. -/
theorem roundSphere_finite_complement_isPathConnected
    {E : Set RoundSphere} (hE : E.Finite) : IsPathConnected Eᶜ := by
  by_cases hEn : E.Nonempty
  · obtain ⟨v, hv⟩ := hEn
    let e : OpenPartialHomeomorph RoundSphere (EuclideanSpace ℝ (Fin 2)) :=
      stereographic' 2 v
    have hes : e.source = {v}ᶜ := stereographic'_source v
    have het : e.target = univ := stereographic'_target v
    let P : Set (EuclideanSpace ℝ (Fin 2)) := e '' (E ∩ e.source)
    have hP : P.Finite := (hE.subset inter_subset_left).image e
    have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 2)) := by
      rw [← Module.finrank_eq_rank]
      norm_num
    have hc : IsPathConnected Pᶜ :=
      hP.countable.isPathConnected_compl_of_one_lt_rank hrank
    have hcont : ContinuousOn e.symm Pᶜ := by
      apply e.symm.continuousOn.mono
      rw [e.symm_source, het]
      exact subset_univ _
    have himage : e.symm '' Pᶜ = Eᶜ := by
      ext q
      constructor
      · rintro ⟨z, hz, rfl⟩
        change e.symm z ∉ E
        intro hq
        have hzt : z ∈ e.target := by rw [het]; exact mem_univ _
        have hqs : e.symm z ∈ e.source := e.map_target hzt
        apply hz
        exact ⟨e.symm z, ⟨hq, hqs⟩, e.right_inv hzt⟩
      · intro hq
        have hqs : q ∈ e.source := by
          rw [hes]
          intro hqv
          have h : q = v := mem_singleton_iff.mp hqv
          exact hq (h.symm ▸ hv)
        refine ⟨e q, ?_, e.left_inv hqs⟩
        change e q ∉ P
        rintro ⟨r, ⟨hrE, hrs⟩, heq⟩
        have hrq : r = q := by
          have h := congrArg e.symm heq
          simpa only [e.left_inv hrs, e.left_inv hqs] using h
        exact hq (hrq ▸ hrE)
    rw [← himage]
    exact hc.image' hcont
  · have hempty : E = ∅ := Set.not_nonempty_iff_eq_empty.mp hEn
    have hrank : 1 < Module.rank ℝ Ambient := by
      rw [← Module.finrank_eq_rank]
      norm_num [Ambient]
    letI : PathConnectedSpace RoundSphere :=
      isPathConnected_iff_pathConnectedSpace.mp
        (isPathConnected_sphere hrank (0 : Ambient) (by norm_num : (0 : ℝ) ≤ 1))
    simpa only [hempty, compl_empty] using
      (isPathConnected_univ : IsPathConnected (univ : Set RoundSphere))

/-- The exact finite-complement connectedness needed for a one-sheeted positive
Gauss image. -/
theorem roundSphere_finite_complement_isConnected
    {E : Set RoundSphere} (hE : E.Finite) : IsConnected Eᶜ :=
  (roundSphere_finite_complement_isPathConnected hE).isConnected

theorem roundSphere_finite_complement_nonempty
    {E : Set RoundSphere} (hE : E.Finite) : Eᶜ.Nonempty :=
  (roundSphere_finite_complement_isPathConnected hE).nonempty

theorem roundSphere_univ_diff_finite_isConnected
    {E : Set RoundSphere} (hE : E.Finite) : IsConnected (univ \ E) := by
  simpa only [Set.compl_eq_univ_sdiff] using roundSphere_finite_complement_isConnected hE

end
end TightVer401

