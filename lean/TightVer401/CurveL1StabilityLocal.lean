import TightVer401.CurveL1StabilityBounds
import TightVer401.CurveL1StabilityTangent

namespace TightVer401
noncomputable section
open Set OAI.ClosedSurfaceR4.PeriodicPrimitive
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem speedCurve_projection_hasDerivAt {a : ℝ → ℝ} {P : ℝ → E}
    (ha : Continuous a) (hP : Continuous P) (v : E) (t : ℝ) :
    HasDerivAt (fun r => inner ℝ v (speedCurve a P r))
      (a t * inner ℝ v (P t)) t := by
  have hd := (innerSL ℝ v).hasFDerivAt.comp_hasDerivAt t
    (rawPrimitive_hasDerivAt (ha.smul hP) t)
  change HasDerivAt (fun r => inner ℝ v (speedCurve a P r))
    (inner ℝ v (a t • P t)) t at hd
  simpa only [real_inner_smul_right] using hd

theorem speedCurve_local_injective {a : ℝ → ℝ} {P : ℝ → E}
    (ha : Continuous a) (hP : Continuous P) (hapos : ∀ t, 0 < a t)
    {x δ : ℝ} (hdir : ∀ t ∈ Ioo (x - δ) (x + δ), 0 < inner ℝ (P x) (P t)) :
    Set.InjOn (speedCurve a P) (Ioo (x - δ) (x + δ)) := by
  have hc : Continuous (fun t => inner ℝ (P x) (speedCurve a P t)) :=
    (innerSL ℝ (P x)).continuous.comp (rawPrimitive_continuous (ha.smul hP))
  have hm := strictMonoOn_of_deriv_pos (convex_Ioo (x - δ) (x + δ)) hc.continuousOn
    (fun t ht => by
      rw [(speedCurve_projection_hasDerivAt ha hP (P x) t).deriv]
      exact mul_pos (hapos t) (hdir t (interior_subset ht)))
  intro y hy z hz he
  exact hm.injOn hy hz (congrArg (fun v => inner ℝ (P x) v) he)

end
end TightVer401
