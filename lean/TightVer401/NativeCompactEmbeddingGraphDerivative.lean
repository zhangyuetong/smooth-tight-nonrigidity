import TightVer401.ThinBandLocalCalculus
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-! Actual local differential of a perturbation parameter graph.
Its parameter coordinate prevents identification of different parameters.
The baseline immersion supplies the remaining injective coordinate derivative. -/
namespace TightVer401
noncomputable section
open Set Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The actual joint perturbation graph in local source coordinates. -/
def nativeCompactEmbeddingGraph (X Y : E → V) : E × ℝ → ℝ × V :=
  fun z => (z.2, X z.1 + z.2 • Y z.1)

/-- Actual smoothness of both local maps yields joint graph smoothness. -/
theorem nativeCompactEmbeddingGraph_contDiffAt {X Y : E → V} {x : E}
    (hX : ContDiffAt ℝ ∞ X x) (hY : ContDiffAt ℝ ∞ Y x) :
    ContDiffAt ℝ ∞ (nativeCompactEmbeddingGraph X Y) (x, (0 : ℝ)) := by
  have hx : ContDiffAt ℝ ∞ (fun z : E × ℝ => X z.1) (x, (0 : ℝ)) :=
    hX.comp (x, (0 : ℝ)) contDiffAt_fst
  have hy : ContDiffAt ℝ ∞ (fun z : E × ℝ => Y z.1) (x, (0 : ℝ)) :=
    hY.comp (x, (0 : ℝ)) contDiffAt_fst
  exact contDiffAt_snd.prodMk (hx.add (contDiffAt_snd.smul hy))

/-- Exact actual joint Frechet derivative at the zero parameter. -/
theorem nativeCompactEmbeddingGraph_fderiv_apply {X Y : E → V} {x : E}
    (hX : ContDiffAt ℝ ∞ X x) (hY : ContDiffAt ℝ ∞ Y x) (v : E) (a : ℝ) :
    fderiv ℝ (nativeCompactEmbeddingGraph X Y) (x, (0 : ℝ)) (v, a) =
      (a, fderiv ℝ X x v + a • Y x) := by
  unfold nativeCompactEmbeddingGraph
  have hx : HasFDerivAt (fun z : E × ℝ => X z.1)
      ((fderiv ℝ X x).comp (ContinuousLinearMap.fst ℝ E ℝ)) (x, (0 : ℝ)) := by
    simpa only [Function.comp_def] using
      (hX.differentiableAt (by simp)).hasFDerivAt.comp (x, (0 : ℝ)) hasFDerivAt_fst
  have hy : HasFDerivAt (fun z : E × ℝ => Y z.1)
      ((fderiv ℝ Y x).comp (ContinuousLinearMap.fst ℝ E ℝ)) (x, (0 : ℝ)) := by
    simpa only [Function.comp_def] using
      (hY.differentiableAt (by simp)).hasFDerivAt.comp (x, (0 : ℝ)) hasFDerivAt_fst
  have ha : HasFDerivAt (fun z : E × ℝ => z.2)
      (ContinuousLinearMap.snd ℝ E ℝ) (x, (0 : ℝ)) := hasFDerivAt_snd
  have hd := ha.prodMk (hx.add (ha.smul hy))
  have hdv := congrArg (fun D => D (v, a)) hd.fderiv
  simpa using hdv
/-- Actual baseline differential injectivity forces joint graph differential injectivity. -/
theorem nativeCompactEmbeddingGraph_fderiv_injective {X Y : E → V} {x : E}
    (hX : ContDiffAt ℝ ∞ X x) (hY : ContDiffAt ℝ ∞ Y x)
    (himm : Function.Injective (fderiv ℝ X x)) :
    Function.Injective (fderiv ℝ (nativeCompactEmbeddingGraph X Y) (x, (0 : ℝ))) := by
  intro v w he
  have hv := nativeCompactEmbeddingGraph_fderiv_apply hX hY v.1 v.2
  have hw := nativeCompactEmbeddingGraph_fderiv_apply hX hY w.1 w.2
  have he' : (v.2, fderiv ℝ X x v.1 + v.2 • Y x) =
      (w.2, fderiv ℝ X x w.1 + w.2 • Y x) := hv.symm.trans (he.trans hw)
  have ha : v.2 = w.2 := congrArg Prod.fst he'
  have hfirst : fderiv ℝ X x v.1 = fderiv ℝ X x w.1 := by
    apply add_right_cancel
    simpa only [ha] using congrArg Prod.snd he'
  exact Prod.ext (himm hfirst) ha

/-- The joint graph has an actual strict derivative, derived from its smoothness. -/
theorem nativeCompactEmbeddingGraph_hasStrictFDerivAt {X Y : E → V} {x : E}
    (hX : ContDiffAt ℝ ∞ X x) (hY : ContDiffAt ℝ ∞ Y x) :
    HasStrictFDerivAt (nativeCompactEmbeddingGraph X Y)
      (fderiv ℝ (nativeCompactEmbeddingGraph X Y) (x, (0 : ℝ))) (x, (0 : ℝ)) :=
  (nativeCompactEmbeddingGraph_contDiffAt hX hY).hasStrictFDerivAt (by simp)

/-- A real finite-dimensional baseline immersion yields actual graph local
injectivity; this conclusion is proved rather than supplied as an input. -/
theorem nativeCompactEmbeddingGraph_exists_local_injOn [FiniteDimensional ℝ E]
    {X Y : E → V} {x : E}
    (hX : ContDiffAt ℝ ∞ X x) (hY : ContDiffAt ℝ ∞ Y x)
    (himm : Function.Injective (fderiv ℝ X x)) :
    ∃ U ∈ 𝓝 (x, (0 : ℝ)), Set.InjOn (nativeCompactEmbeddingGraph X Y) U :=
  exists_local_injOn_of_injective_strictFDeriv
    (nativeCompactEmbeddingGraph_hasStrictFDerivAt hX hY)
    (nativeCompactEmbeddingGraph_fderiv_injective hX hY himm)

end
end TightVer401



