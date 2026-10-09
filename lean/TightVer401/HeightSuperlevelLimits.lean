import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Connected strict superlevels pass to uniform approximations. This argument
uses only two points and their positive height margins; neither compactness nor
continuity is required once the uniform approximation is available. -/
namespace TightVer401
noncomputable section
open Set

/-- Uniform approximation by functions with preconnected strict superlevels
forces the same property for the limiting function. The ambient topological
space is arbitrary and empty superlevels are included. -/
theorem height_superlevel_isPreconnected_of_uniform_approximants
    {X : Type*} [TopologicalSpace X] {h : X → ℝ}
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ g : X → ℝ,
      (∀ x, |g x - h x| < ε) ∧
      (∀ b : ℝ, IsPreconnected {x : X | b < g x}))
    (a : ℝ) : IsPreconnected {x : X | a < h x} := by
  apply isPreconnected_of_forall_pair
  intro x hx y hy
  change a < h x at hx
  change a < h y at hy
  let ε : ℝ := min (h x - a) (h y - a) / 4
  have hε : 0 < ε := by
    dsimp [ε]
    exact div_pos (lt_min (sub_pos.mpr hx) (sub_pos.mpr hy)) (by norm_num)
  have hεx : 2 * ε < h x - a := by
    have hm := min_le_left (h x - a) (h y - a)
    dsimp [ε] at hε ⊢
    nlinarith
  have hεy : 2 * ε < h y - a := by
    have hm := min_le_right (h x - a) (h y - a)
    dsimp [ε] at hε ⊢
    nlinarith
  obtain ⟨g, hclose, hconnected⟩ := happrox ε hε
  refine ⟨{z : X | a + ε < g z}, ?_, ?_, ?_, hconnected (a + ε)⟩
  · intro z hz
    change a + ε < g z at hz
    change a < h z
    have hzclose := (abs_lt.mp (hclose z)).2
    linarith
  · change a + ε < g x
    have hxclose := (abs_lt.mp (hclose x)).1
    linarith
  · change a + ε < g y
    have hyclose := (abs_lt.mp (hclose y)).1
    linarith

end
end TightVer401
