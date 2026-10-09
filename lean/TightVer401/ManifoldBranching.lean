import OAI.Geometry.SurfaceImmersion.Geometry.ManifoldMetricCalculus
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-! Global metric branching on actual charted surfaces, into three-space.
The imported OpenAI calculus is generic in the target despite its R4 namespace.
-/
open Manifold
open scoped ContDiff Manifold Topology BigOperators
namespace TightVer401.Manifold
noncomputable section
open OAI.ClosedSurfaceR4 Filter

abbrev ThreeSpace := EuclideanSpace ℝ (Fin 3)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

def IsBending (X y : M → ThreeSpace) : Prop :=
  ContMDiff planeModel 𝓘(ℝ, ThreeSpace) ∞ y ∧
  ∀ (p : M) (v w : TangentSpace planeModel p), linearMetricForm X y p v w = 0

theorem metric_quadratic {X y : M → ThreeSpace} {p : M}
    (hX : MDifferentiableAt planeModel 𝓘(ℝ, ThreeSpace) X p)
    (hy : MDifferentiableAt planeModel 𝓘(ℝ, ThreeSpace) y p)
    (v w : TangentSpace planeModel p) :
    inducedForm (X + y) p v w =
      inducedForm X p v w + linearMetricForm X y p v w + inducedForm y p v w := by
  have h := inducedForm_add hX hy v w
  linarith

theorem metric_sub_quadratic {X y : M → ThreeSpace} {p : M}
    (hX : MDifferentiableAt planeModel 𝓘(ℝ, ThreeSpace) X p)
    (hy : MDifferentiableAt planeModel 𝓘(ℝ, ThreeSpace) y p)
    (v w : TangentSpace planeModel p) :
    inducedForm (X - y) p v w =
      inducedForm X p v w - linearMetricForm X y p v w + inducedForm y p v w := by
  unfold inducedForm linearMetricForm surfaceDifferential
  rw [mfderiv_sub hX hy]
  simp only [sub_apply, inner_sub_left, inner_sub_right]
  ring

theorem exact_sign_pair {X y : M → ThreeSpace}
    (hX : ContMDiff planeModel 𝓘(ℝ, ThreeSpace) ∞ X) (hy : IsBending X y)
    (p : M) (v w : TangentSpace planeModel p) :
    inducedForm (X + y) p v w = inducedForm (X - y) p v w := by
  rw [metric_quadratic ((hX p).mdifferentiableAt (by simp))
      ((hy.1 p).mdifferentiableAt (by simp)),
    metric_sub_quadratic ((hX p).mdifferentiableAt (by simp))
      ((hy.1 p).mdifferentiableAt (by simp)), hy.2 p v w]
  simp

theorem differential_zero_off_support (y : M → ThreeSpace) {p : M}
    (hp : p ∉ tsupport y) : surfaceDifferential y p = 0 := by
  have hz : y =ᶠ[𝓝 p] (fun _ => (0 : ThreeSpace)) :=
    notMem_tsupport_iff_eventuallyEq.mp hp
  unfold surfaceDifferential
  rw [hz.mfderiv_eq]
  exact mfderiv_const

theorem cross_term_zero {y z : M → ThreeSpace}
    (h : Disjoint (tsupport y) (tsupport z)) (p : M)
    (v w : TangentSpace planeModel p) :
    inner ℝ (surfaceDifferential y p v) (surfaceDifferential z p w) = 0 := by
  by_cases hp : p ∈ tsupport y
  · have hz : p ∉ tsupport z := fun hz => Set.disjoint_left.mp h hp hz
    rw [differential_zero_off_support z hz]
    simp
  · rw [differential_zero_off_support y hp]
    simp

theorem differential_const_smul {y : M → ThreeSpace} {p : M}
    (hy : MDifferentiableAt planeModel 𝓘(ℝ, ThreeSpace) y p) (c : ℝ) :
    surfaceDifferential (c • y) p = c • surfaceDifferential y p :=
  const_smul_mfderiv hy c

theorem strain_const_smul {X y : M → ThreeSpace} {p : M}
    (hy : MDifferentiableAt planeModel 𝓘(ℝ, ThreeSpace) y p) (c : ℝ)
    (v w : TangentSpace planeModel p) :
    linearMetricForm X (c • y) p v w = c * linearMetricForm X y p v w := by
  simp only [linearMetricForm, differential_const_smul hy, smul_apply,
    real_inner_smul_left, real_inner_smul_right]
  ring

theorem metric_const_smul {y : M → ThreeSpace} {p : M}
    (hy : MDifferentiableAt planeModel 𝓘(ℝ, ThreeSpace) y p) (c : ℝ)
    (v w : TangentSpace planeModel p) :
    inducedForm (c • y) p v w = c^2 * inducedForm y p v w := by
  simp only [inducedForm, differential_const_smul hy, smul_apply,
    real_inner_smul_left, real_inner_smul_right]
  ring

/- The finite part of manuscript thm:branch, globally on the surface. -/
theorem finite_sign_metric {m : ℕ} {X : M → ThreeSpace} {Y : Fin m → M → ThreeSpace}
    (hX : ContMDiff planeModel 𝓘(ℝ, ThreeSpace) ∞ X)
    (hY : ∀ k, IsBending X (Y k))
    (hdisj : ∀ k l, k ≠ l → Disjoint (tsupport (Y k)) (tsupport (Y l)))
    (a ε : Fin m → ℝ) (hε : ∀ k, (ε k)^2 = 1)
    (p : M) (v w : TangentSpace planeModel p) :
    inducedForm (X + ∑ k, (ε k * a k) • Y k) p v w =
      inducedForm X p v w + ∑ k, (a k)^2 * inducedForm (Y k) p v w := by
  classical
  have hdY (k) : MDifferentiableAt planeModel 𝓘(ℝ, ThreeSpace) (Y k) p :=
    ((hY k).1 p).mdifferentiableAt (by simp)
  let f : Fin m → M → ThreeSpace := fun k => (ε k * a k) • Y k
  have hdf (k) : MDifferentiableAt planeModel 𝓘(ℝ, ThreeSpace) (f k) p :=
    (hdY k).const_smul (ε k * a k)
  have hdSum : MDifferentiableAt planeModel 𝓘(ℝ, ThreeSpace) (∑ k, f k) p :=
    MDifferentiableAt.sum fun k _ => hdf k
  change inducedForm (X + ∑ k, f k) p v w = _
  rw [metric_quadratic ((hX p).mdifferentiableAt (by simp)) hdSum,
    linearMetricForm_finite_sum X f hdf, inducedForm_finite_sum f hdf]
  have hs (k) : linearMetricForm X (f k) p v w = 0 := by
    rw [show f k = (ε k * a k) • Y k from rfl, strain_const_smul (hdY k), (hY k).2]
    simp
  have hm (k) : inducedForm (f k) p v w = (a k)^2 * inducedForm (Y k) p v w := by
    rw [show f k = (ε k * a k) • Y k from rfl, metric_const_smul (hdY k), mul_pow, hε k]
    simp
  have hc (k l) (hl : l ∈ Finset.univ.erase k) :
      inner ℝ (surfaceDifferential (f k) p v) (surfaceDifferential (f l) p w) = 0 := by
    have hkl : k ≠ l := Ne.symm (Finset.mem_erase.mp hl).1
    simp only [f, differential_const_smul (hdY _), smul_apply,
      real_inner_smul_left, real_inner_smul_right,
      cross_term_zero (hdisj k l hkl), mul_zero]
  have hcross : (∑ k, ∑ l ∈ Finset.univ.erase k,
      inner ℝ (surfaceDifferential (f k) p v) (surfaceDifferential (f l) p w)) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    apply Finset.sum_eq_zero
    intro l hl
    exact hc k l hl
  simp only [hs, hm, hcross, Finset.sum_const_zero, add_zero]

/- The countable formula needs only convergence of the actual first
   differentials, a consequence of convergence in the smooth topology. -/
theorem infinite_sign_metric_of_differential_limit
    {X Z : M → ThreeSpace} {Y : ℕ → M → ThreeSpace}
    (hX : ContMDiff planeModel 𝓘(ℝ, ThreeSpace) ∞ X)
    (hY : ∀ k, IsBending X (Y k))
    (hdisj : ∀ k l, k ≠ l → Disjoint (tsupport (Y k)) (tsupport (Y l)))
    (a ε : ℕ → ℝ) (hε : ∀ k, (ε k)^2 = 1)
    (p : M) (v w : TangentSpace planeModel p)
    (hlim : Tendsto (fun m : ℕ => surfaceDifferential
      (X + ∑ k : Fin m, (ε k * a k) • Y k) p) atTop
      (𝓝 (surfaceDifferential Z p))) :
    inducedForm Z p v w = inducedForm X p v w +
      ∑' k, (a k)^2 * inducedForm (Y k) p v w := by
  classical
  let b : ℕ → ℝ := fun k => (a k)^2 * inducedForm (Y k) p v w
  have hb : Summable b := by
    by_cases hex : ∃ k, p ∈ tsupport (Y k)
    · obtain ⟨k, hk⟩ := hex
      apply summable_of_ne_finset_zero (s := {k})
      intro l hl
      have hlk : l ≠ k := by simpa using hl
      have hn : p ∉ tsupport (Y l) := fun h =>
        Set.disjoint_left.mp (hdisj k l hlk.symm) hk h
      simp [b, inducedForm, differential_zero_off_support (Y l) hn]
    · have hn : ∀ k, p ∉ tsupport (Y k) := by simpa using hex
      have hz : b = 0 := by
        funext k
        simp [b, inducedForm, differential_zero_off_support (Y k) (hn k)]
      rw [hz]
      exact summable_zero
  have hmetric : Tendsto (fun m : ℕ => inducedForm
      (X + ∑ k : Fin m, (ε k * a k) • Y k) p v w) atTop
      (𝓝 (inducedForm Z p v w)) := by
    have hv := (continuous_eval_const v : Continuous
      (fun f : TangentSpace planeModel p →L[ℝ] ThreeSpace => f v)).tendsto
      (surfaceDifferential Z p) |>.comp hlim
    have hw := (continuous_eval_const w : Continuous
      (fun f : TangentSpace planeModel p →L[ℝ] ThreeSpace => f w)).tendsto
      (surfaceDifferential Z p) |>.comp hlim
    exact hv.inner hw
  have hformula (m : ℕ) : inducedForm
      (X + ∑ k : Fin m, (ε k * a k) • Y k) p v w =
      inducedForm X p v w + ∑ k ∈ Finset.range m, b k := by
    rw [finite_sign_metric hX (fun k => hY k)
      (fun k l h => hdisj k l (fun he => h (Fin.ext he)))
      (fun k => a k) (fun k => ε k) (fun k => hε k)]
    exact congrArg (fun r => inducedForm X p v w + r)
      (Fin.sum_univ_eq_sum_range b m)
  simp_rw [hformula] at hmetric
  exact tendsto_nhds_unique hmetric (tendsto_const_nhds.add hb.hasSum.tendsto_sum_nat)

end
end TightVer401.Manifold
