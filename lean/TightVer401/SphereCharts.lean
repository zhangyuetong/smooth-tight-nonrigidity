import TightVer401.SphereHemisphere

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology RealInnerProductSpace Manifold
set_option backward.isDefEq.respectTransparency false

abbrev RoundSphere := Metric.sphere (0 : Ambient) 1

theorem roundSphere_norm (q : RoundSphere) : ‖q.val‖ = 1 := by simpa using q.property

theorem roundSphere_ne_zero (q : RoundSphere) : q.val ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [roundSphere_norm]
  exact one_ne_zero

local instance : Fact (Module.finrank ℝ Ambient = 2 + 1) := ⟨by simp [Ambient]⟩

def sphereHemispherePoint (w : Ambient) (hw : w ≠ 0) (hunit : ‖w‖ = 1)
    (p : Coord) : RoundSphere :=
  ⟨sphereHemisphere w hw p, by simpa using sphereHemisphere_norm w hw hunit p⟩

def sphereHemisphereChart (w : Ambient) (hw : w ≠ 0) (hunit : ‖w‖ = 1) :
    OpenPartialHomeomorph Coord RoundSphere where
  toFun := sphereHemispherePoint w hw hunit
  invFun := fun q => sphereHemisphereInverse w hw q.val
  source := univ
  target := {q | 0 < inner ℝ w q.val}
  map_source' := fun _ _ => sphereHemisphere_inner_pos w hw hunit _
  map_target' := fun _ _ => mem_univ _
  left_inv' := fun p _ => sphereHemisphere_left_inverse w hw hunit p
  right_inv' := by
    intro q hq
    apply Subtype.ext
    exact sphereHemisphere_right_inverse w hw hunit (by simpa using q.property) hq
  open_source := isOpen_univ
  open_target := isOpen_lt continuous_const (continuous_const.inner continuous_subtype_val)
  continuousOn_toFun :=
    ((sphereHemisphere_contDiff w hw hunit).continuous.subtype_mk _).continuousOn
  continuousOn_invFun := by
    have hi : ContinuousOn (sphereHemisphereInverse w hw) {u | 0 < inner ℝ w u} := by
      intro u hu
      exact (sphereHemisphereInverse_contDiffAt w hw hu).continuousAt.continuousWithinAt
    exact hi.comp continuous_subtype_val.continuousOn (fun q hq => hq)

theorem sphereHemispherePoint_contMDiff (w : Ambient) (hw : w ≠ 0) (hunit : ‖w‖ = 1) :
    ContMDiff 𝓘(ℝ, Coord) (𝓡 2) ∞ (sphereHemispherePoint w hw hunit) := by
  exact (sphereHemisphere_contDiff w hw hunit).contMDiff.codRestrict_sphere
    (fun p => by simpa using sphereHemisphere_norm w hw hunit p)

theorem sphereHemisphereChart_covers (q : RoundSphere) :
    q ∈ (sphereHemisphereChart q.val (by
      have hn : ‖q.val‖ = 1 := by simpa using q.property
      exact norm_ne_zero_iff.mp (by rw [hn]; exact one_ne_zero))
      (by simpa using q.property)).target := by
  change 0 < inner ℝ q.val q.val
  have hn : ‖q.val‖ = 1 := by simpa using q.property
  rw [real_inner_self_eq_norm_sq, hn]
  norm_num

theorem sphereHemisphere_transition_contDiffOn (w₁ w₂ : Ambient)
    (hw₁ : w₁ ≠ 0) (hw₂ : w₂ ≠ 0) (hu₁ : ‖w₁‖ = 1) :
    ContDiffOn ℝ ∞ (fun p => sphereHemisphereInverse w₂ hw₂ (sphereHemisphere w₁ hw₁ p))
      {p | 0 < inner ℝ w₂ (sphereHemisphere w₁ hw₁ p)} := by
  intro p hp
  exact ((sphereHemisphereInverse_contDiffAt w₂ hw₂ hp).comp p
    (sphereHemisphere_contDiff w₁ hw₁ hu₁).contDiffAt).contDiffWithinAt

theorem sphereHemisphere_transition_eq (w₁ w₂ : Ambient)
    (hw₁ : w₁ ≠ 0) (hw₂ : w₂ ≠ 0) (hu₁ : ‖w₁‖ = 1) (hu₂ : ‖w₂‖ = 1)
    {p : Coord} (hp : 0 < inner ℝ w₂ (sphereHemisphere w₁ hw₁ p)) :
    sphereHemisphere w₂ hw₂
      (sphereHemisphereInverse w₂ hw₂ (sphereHemisphere w₁ hw₁ p)) = sphereHemisphere w₁ hw₁ p :=
  sphereHemisphere_right_inverse w₂ hw₂ hu₂ (sphereHemisphere_norm w₁ hw₁ hu₁ p) hp

end
end TightVer401
