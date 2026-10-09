import Mathlib.Topology.OpenPartialHomeomorph.Continuity

namespace TightVer401
noncomputable section
open Set Filter
open scoped Topology

theorem local_injOn_transport_chart {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {e : OpenPartialHomeomorph X Y} {f : X → Z} {g : Y → Z} {x : X}
    (hx : x ∈ e.source) (hmatch : ∀ z ∈ e.source, g (e z) = f z)
    (hlocal : ∃ U ∈ 𝓝 x, Set.InjOn f U) :
    ∃ V ∈ 𝓝 (e x), Set.InjOn g V := by
  obtain ⟨U, hU, hi⟩ := hlocal
  have ht := e.map_source hx
  have hpre : e.symm ⁻¹' U ∈ 𝓝 (e x) := by
    have hc := e.continuousAt_symm ht
    exact hc.preimage_mem_nhds (by simpa only [e.left_inv hx] using hU)
  refine ⟨e.target ∩ e.symm ⁻¹' U,
    inter_mem (e.open_target.mem_nhds ht) hpre, ?_⟩
  intro y hy z hz he
  have hyf : g y = f (e.symm y) := by
    simpa only [e.right_inv hy.1] using hmatch (e.symm y) (e.map_target hy.1)
  have hzf : g z = f (e.symm z) := by
    simpa only [e.right_inv hz.1] using hmatch (e.symm z) (e.map_target hz.1)
  have hsame := hi hy.2 hz.2 (hyf.symm.trans (he.trans hzf))
  have hsame' := congrArg e hsame
  simpa only [e.right_inv hy.1, e.right_inv hz.1] using hsame'

end
end TightVer401
