import TightVer401.PeriodCircleInstances

namespace TightVer401
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology
set_option backward.isDefEq.respectTransparency false

theorem periodProjection_mfderiv_surjective (L : ℝ) [Fact (0 < L)] (s : ℝ) :
    Function.Surjective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (periodProjection L) s) := by
  let a := periodProjection L s
  let σ : AddCircle L → ℝ := fun x => s + extChartAt 𝓘(ℝ, ℝ) a x
  have hq0 : (periodChart L) (0 : ℝ) = 0 := rfl
  have hσa : σ a = s := by
    change s + (periodChart L).symm (-a + a) = s
    rw [neg_add_cancel, ← hq0, (periodChart L).left_inv (periodChart_zero_source L), add_zero]
  have hσ : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ σ a :=
    contMDiffAt_const.add (contMDiffAt_extChartAt (I := 𝓘(ℝ, ℝ)))
  have he : (periodProjection L ∘ σ) =ᶠ[𝓝 a] id := by
    filter_upwards [(chartAt ℝ a).open_source.mem_nhds (mem_chart_source ℝ a)] with x hx
    have hx' : x ∈ (OAI.RawQuotientLie.addLeftChart (periodChart L) a).source := hx
    rw [OAI.RawQuotientLie.addLeftChart_source] at hx'
    change periodProjection L (s + (periodChart L).symm (-a + x)) = x
    rw [map_add]
    change a + (periodChart L) ((periodChart L).symm (-a + x)) = x
    rw [(periodChart L).right_inv hx']
    rw [← add_assoc, add_neg_cancel, zero_add]
  have hd := mfderiv_comp_of_eq
    ((periodProjection_contMDiff L s).mdifferentiableAt (by simp))
    (hσ.mdifferentiableAt (by simp)) hσa
  have hid := he.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ))
  rw [mfderiv_id] at hid
  have hp := mfderiv_congr_point (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ))
    (f := periodProjection L) hσa
  change (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (periodProjection L) (σ a) : ℝ →L[ℝ] ℝ) =
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (periodProjection L) s at hp
  change (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (periodProjection L ∘ σ) a : ℝ →L[ℝ] ℝ) =
    (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (periodProjection L) (σ a)).comp
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) σ a) at hd
  rw [hp] at hd
  intro v
  refine ⟨mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) σ a v, ?_⟩
  have h := congrArg (fun A : ℝ →L[ℝ] ℝ => A v) (hd.symm.trans hid)
  exact h

end
end TightVer401
