import TightVer401.MomentControlSamples
import TightVer401.PeriodCircle

namespace TightVer401
noncomputable section
open Set Filter MeasureTheory Metric
open scoped ContDiff Topology Manifold

def circleMomentSpan {m : ℕ} (L : ℝ) (f : AddCircle L → EuclideanSpace ℝ (Fin m)) :=
  Submodule.span ℝ (Set.range f)

theorem circleMomentSpan_eq_representative {m : ℕ} (L : ℝ) [hL : Fact (0 < L)]
    {f : AddCircle L → EuclideanSpace ℝ (Fin m)} (hf : Continuous f) :
    circleMomentSpan L f = momentSampleSpan (f ∘ periodProjection L) (Ioo 0 L) := by
  let g := f ∘ periodProjection L
  let V := momentSampleSpan g (Ioo 0 L)
  have hg : Continuous g := hf.comp (AddCircle.continuous_mk' L)
  have hz : g 0 ∈ V := by
    have hT : Tendsto (fun k => g (momentControlRadius k)) atTop (𝓝 (g 0)) :=
      (hg.tendsto 0).comp momentControlRadius_tendsto
    have hsmall : ∀ᶠ k in atTop, momentControlRadius k < L :=
      momentControlRadius_tendsto.eventually (gt_mem_nhds hL.out)
    apply V.closed_of_finiteDimensional.mem_of_tendsto hT
    filter_upwards [hsmall] with k hk
    exact Submodule.subset_span ⟨momentControlRadius k,
      ⟨momentControlRadius_pos k, hk⟩, rfl⟩
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨q, rfl⟩
    let r := AddCircle.equivIco L 0 q
    have hr : (r : ℝ) ∈ Ico 0 L := by simpa only [zero_add] using r.property
    have hq : periodProjection L (r : ℝ) = q := AddCircle.coe_equivIco
    have hfg : f q = g (r : ℝ) := (congrArg f hq).symm
    rw [hfg]
    by_cases hpos : 0 < (r : ℝ)
    · exact Submodule.subset_span ⟨(r : ℝ), ⟨hpos, hr.2⟩, rfl⟩
    · have hr0 : (r : ℝ) = 0 := le_antisymm (not_lt.mp hpos) hr.1
      rw [hr0]
      exact hz
  · apply Submodule.span_le.mpr
    rintro _ ⟨r, _, rfl⟩
    exact Submodule.subset_span ⟨periodProjection L r, rfl⟩

end
end TightVer401
