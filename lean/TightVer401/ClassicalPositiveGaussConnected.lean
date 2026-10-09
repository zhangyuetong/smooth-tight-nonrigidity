import TightVer401.ClassicalExternal
import Mathlib.Analysis.Normed.Module.Connected

/-! Connectedness of the entire positive-curvature source of the actual Gauss chart.
The finite-punctured sphere result is proved by stereographic projection and the
pinned countable-complement path-connectedness theorem. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped Topology RealInnerProductSpace

local instance : Fact (Module.finrank ℝ Ambient = 2 + 1) := ⟨by simp [Ambient]⟩

/-- Removing finitely many points from the actual round two-sphere preserves
preconnectedness. -/
theorem roundSphere_finite_complement_isPreconnected
    (E : Set RoundSphere) (hE : E.Finite) : IsPreconnected (univ \ E) := by
  classical
  by_cases hempty : E = ∅
  · subst E
    have hs : IsPreconnected (Metric.sphere (0 : Ambient) 1) :=
      isPreconnected_sphere (by simp [← Module.finrank_eq_rank, Ambient]) 0 1
    letI : PreconnectedSpace RoundSphere := Subtype.preconnectedSpace hs
    simpa using (isPreconnected_univ : IsPreconnected (univ : Set RoundSphere))
  · obtain ⟨pole, hpole⟩ := Set.nonempty_iff_ne_empty.mpr hempty
    let c : OpenPartialHomeomorph RoundSphere (EuclideanSpace ℝ (Fin 2)) :=
      stereographic' 2 pole
    let F : Set (EuclideanSpace ℝ (Fin 2)) := c '' (E ∩ c.source)
    have hF : F.Finite := (hE.subset inter_subset_left).image c
    have hconn : IsPreconnected Fᶜ :=
      (hF.countable.isPathConnected_compl_of_one_lt_rank
        (by simp [← Module.finrank_eq_rank])).isConnected.isPreconnected
    have htarget : ∀ q, q ∈ c.target := by
      intro q
      simp [c]
    have himage : c.symm '' Fᶜ = univ \ E := by
      ext q
      constructor
      · rintro ⟨w, hw, rfl⟩
        refine ⟨mem_univ _, ?_⟩
        intro hmem
        apply hw
        refine ⟨c.symm w, ⟨hmem, c.map_target (htarget w)⟩, ?_⟩
        exact c.right_inv (htarget w)
      · intro hq
        have hqs : q ∈ c.source := by
          simp only [c, stereographic'_source, mem_compl_iff, mem_singleton_iff]
          intro heq
          exact hq.2 (heq.symm ▸ hpole)
        refine ⟨c q, ?_, c.left_inv hqs⟩
        rintro ⟨x, hx, heq⟩
        have hxq : x = q := by
          have hh := congrArg c.symm heq
          simpa only [c.left_inv hx.2, c.left_inv hqs] using hh
        exact hq.2 (hxq ▸ hx.1)
    rw [← himage]
    exact hconn.image c.symm (c.continuousOn_symm.mono (fun q _ => htarget q))

/-- Same-object interface for the orientation argument: the source of the given
Gauss homeomorphism is the ENTIRE actual native positive-curvature region. -/
theorem nativeTorusPositiveRegion_isPreconnected_of_gauss_chart
    (X : NonrigidTorusSource → Ambient)
    (E : Set RoundSphere) (hE : E.Finite)
    (e : OpenPartialHomeomorph NonrigidTorusSource RoundSphere)
    (hsource : e.source = nativeTorusPositiveRegion X)
    (htarget : e.target = univ \ E) :
    IsPreconnected (nativeTorusPositiveRegion X) := by
  have ht : IsPreconnected e.target := by
    rw [htarget]
    exact roundSphere_finite_complement_isPreconnected E hE
  rw [← hsource, ← e.symm_image_target_eq_source]
  exact ht.image e.symm e.continuousOn_symm

end
end TightVer401

