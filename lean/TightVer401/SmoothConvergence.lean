import TightVer401.ManifoldBranching
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-! Smooth convergence is expressed by locally uniform convergence of all
actual coordinate jets, including values and first Fréchet derivatives.
This avoids assuming the derivative-limit conclusion as a geometric grant. -/
open Filter Manifold
open scoped ContDiff Topology Manifold
namespace TightVer401
noncomputable section
set_option backward.isDefEq.respectTransparency false

def ConvergesSmoothlyOn {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : ℕ → E → V) (Z : E → V) (U : Set E) : Prop :=
  (∀ m, ContDiffOn ℝ ∞ (F m) U) ∧ ContDiffOn ℝ ∞ Z U ∧
  TendstoLocallyUniformlyOn F Z atTop U ∧
  TendstoLocallyUniformlyOn (fun m => fderiv ℝ (F m)) (fderiv ℝ Z) atTop U ∧
  ∀ k : ℕ, TendstoLocallyUniformlyOn
    (fun m => iteratedFDeriv ℝ (k + 2) (F m)) (iteratedFDeriv ℝ (k + 2) Z) atTop U

open OAI.ClosedSurfaceR4 in
theorem surfaceDifferential_eq_chart_fderiv
    {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
    {F : M → EuclideanSpace ℝ (Fin 3)} {p : M}
    (hF : MDifferentiableAt planeModel 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) F p) :
    surfaceDifferential F p = fderiv ℝ
      (F ∘ (extChartAt planeModel p).symm) ((extChartAt planeModel p) p) := by
  unfold surfaceDifferential mfderiv
  rw [if_pos hF]
  simp only [writtenInExtChartAt, mfld_simps, fderivWithin_univ]

namespace Manifold
open OAI.ClosedSurfaceR4
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

def ConvergesSmoothly (F : ℕ → M → ThreeSpace) (Z : M → ThreeSpace) : Prop :=
  (∀ m, ContMDiff planeModel 𝓘(ℝ, ThreeSpace) ∞ (F m)) ∧
  ContMDiff planeModel 𝓘(ℝ, ThreeSpace) ∞ Z ∧
  ∀ p : M, ConvergesSmoothlyOn
    (fun m => F m ∘ (extChartAt planeModel p).symm)
    (Z ∘ (extChartAt planeModel p).symm) (extChartAt planeModel p).target

theorem ConvergesSmoothly.differential_limit
    {F : ℕ → M → ThreeSpace} {Z : M → ThreeSpace}
    (h : ConvergesSmoothly F Z) (p : M) :
    Tendsto (fun m => surfaceDifferential (F m) p) atTop
      (𝓝 (surfaceDifferential Z p)) := by
  have hs (m) := surfaceDifferential_eq_chart_fderiv
    (((h.1 m) p).mdifferentiableAt (by simp))
  have hz := surfaceDifferential_eq_chart_fderiv
    ((h.2.1 p).mdifferentiableAt (by simp))
  simp_rw [hs, hz]
  exact (h.2.2 p).2.2.2.1.tendsto_at (by simp [mfld_simps])

theorem infinite_sign_metric
    {X Z : M → ThreeSpace} {Y : ℕ → M → ThreeSpace}
    (hX : ContMDiff planeModel 𝓘(ℝ, ThreeSpace) ∞ X)
    (hY : ∀ k, IsBending X (Y k))
    (hdisj : ∀ k l, k ≠ l → Disjoint (tsupport (Y k)) (tsupport (Y l)))
    (a ε : ℕ → ℝ) (hε : ∀ k, (ε k)^2 = 1)
    (hlim : ConvergesSmoothly
      (fun m => X + ∑ k : Fin m, (ε k * a k) • Y k) Z)
    (p : M) (v w : TangentSpace planeModel p) :
    inducedForm Z p v w = inducedForm X p v w +
      ∑' k, (a k)^2 * inducedForm (Y k) p v w :=
  infinite_sign_metric_of_differential_limit hX hY hdisj a ε hε p v w
    (hlim.differential_limit p)

end Manifold
end
end TightVer401
