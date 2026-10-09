import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Connected.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import TightVer401.SphereCharts
import TightVer401.TorusGoalObjects
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.Normalize

/-! Dense good sphere directions imply the exact open-halfspace image predicate.
The good-direction hypothesis here is purely topological and remains an actual
producer obligation of the geometric Gauss argument.
-/

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
local instance heightTightnessSphereDirectionsPeriod : Fact (0 < 2 * Real.pi) :=
  ⟨Real.two_pi_pos⟩

variable {M : Type*} [TopologicalSpace M] [CompactSpace M]

/-- Compactness extends connected strict height superlevels from a dense set
of unit directions to every unit direction. -/
theorem heightSuperlevel_isPreconnected_of_dense_sphere_directions
    (X : M → Ambient) (hX : Continuous X) (G : Set RoundSphere) (hG : Dense G)
    (hgood : ∀ w ∈ G, ∀ a : ℝ,
      IsPreconnected {p : M | a < inner ℝ (w : Ambient) (X p)})
    (v : RoundSphere) (a : ℝ) :
    IsPreconnected {p : M | a < inner ℝ (v : Ambient) (X p)} := by
  obtain ⟨R, hR, hbound⟩ := (isCompact_univ.image hX).isBounded.exists_pos_norm_le
  have hnorm : ∀ p : M, ‖X p‖ ≤ R := fun p =>
    hbound (X p) (mem_image_of_mem X (mem_univ p))
  apply isPreconnected_of_forall_pair
  intro x hx y hy
  change a < inner ℝ (v : Ambient) (X x) at hx
  change a < inner ℝ (v : Ambient) (X y) at hy
  let δ : ℝ := min (inner ℝ (v : Ambient) (X x) - a)
    (inner ℝ (v : Ambient) (X y) - a) / 3
  have hδ : 0 < δ := by
    dsimp [δ]
    exact div_pos (lt_min (sub_pos.mpr hx) (sub_pos.mpr hy)) (by norm_num)
  have hδx : 3 * δ ≤ inner ℝ (v : Ambient) (X x) - a := by
    dsimp [δ]
    linarith [min_le_left (inner ℝ (v : Ambient) (X x) - a)
      (inner ℝ (v : Ambient) (X y) - a)]
  have hδy : 3 * δ ≤ inner ℝ (v : Ambient) (X y) - a := by
    dsimp [δ]
    linarith [min_le_right (inner ℝ (v : Ambient) (X x) - a)
      (inner ℝ (v : Ambient) (X y) - a)]
  obtain ⟨w, hwG, hw⟩ := hG.exists_dist_lt v (div_pos hδ hR)
  have hwNorm : ‖(v : Ambient) - (w : Ambient)‖ < δ / R := by
    simpa only [Subtype.dist_eq, dist_eq_norm] using hw
  have herror : ∀ p : M,
      |inner ℝ (v : Ambient) (X p) - inner ℝ (w : Ambient) (X p)| < δ := by
    intro p
    calc
      |inner ℝ (v : Ambient) (X p) - inner ℝ (w : Ambient) (X p)| =
          |inner ℝ ((v : Ambient) - (w : Ambient)) (X p)| := by rw [inner_sub_left]
      _ ≤ ‖(v : Ambient) - (w : Ambient)‖ * ‖X p‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖(v : Ambient) - (w : Ambient)‖ * R :=
        mul_le_mul_of_nonneg_left (hnorm p) (norm_nonneg _)
      _ < (δ / R) * R := mul_lt_mul_of_pos_right hwNorm hR
      _ = δ := div_mul_cancel₀ δ (ne_of_gt hR)
  refine ⟨{p : M | a + δ < inner ℝ (w : Ambient) (X p)}, ?_, ?_, ?_,
    hgood w hwG (a + δ)⟩
  · intro p hp
    change a + δ < inner ℝ (w : Ambient) (X p) at hp
    change a < inner ℝ (v : Ambient) (X p)
    have herr := (abs_lt.mp (herror p)).1
    linarith
  · change a + δ < inner ℝ (w : Ambient) (X x)
    have herr := (abs_lt.mp (herror x)).2
    linarith
  · change a + δ < inner ℝ (w : Ambient) (X y)
    have herr := (abs_lt.mp (herror y)).2
    linarith

/-- Dense good unit directions imply the SAME actual image's two-piece
property.  The connected source also handles the zero linear functional. -/
theorem isTightImage_of_dense_sphere_heightSuperlevels [PreconnectedSpace M]
    (X : M → Ambient) (hX : Continuous X) (G : Set RoundSphere) (hG : Dense G)
    (hgood : ∀ w ∈ G, ∀ a : ℝ,
      IsPreconnected {p : M | a < inner ℝ (w : Ambient) (X p)}) :
    IsTightImage X := by
  intro ell a
  let v : Ambient := (InnerProductSpace.toDual ℝ Ambient).symm ell
  have hrep : ∀ z : Ambient, ell z = inner ℝ v z := fun z =>
    (InnerProductSpace.toDual_symm_apply (x := z) (y := ell)).symm
  have hsource : IsPreconnected {p : M | a < ell (X p)} := by
    by_cases hv : v = 0
    · by_cases ha : a < 0
      · simpa only [hrep, hv, inner_zero_left, ha, setOf_true] using
          (isPreconnected_univ : IsPreconnected (univ : Set M))
      · simpa only [hrep, hv, inner_zero_left, ha, setOf_false] using
          (isPreconnected_empty : IsPreconnected (∅ : Set M))
    · let q : RoundSphere := ⟨NormedSpace.normalize v, by
        simpa using NormedSpace.norm_normalize hv⟩
      have hr : 0 < ‖v‖ := norm_pos_iff.mpr hv
      have hscale (z : Ambient) : inner ℝ v z = ‖v‖ * inner ℝ (q : Ambient) z := by
        calc
          inner ℝ v z = inner ℝ (‖v‖ • NormedSpace.normalize v) z := by
            rw [NormedSpace.norm_smul_normalize]
          _ = ‖v‖ * inner ℝ (q : Ambient) z := by rw [real_inner_smul_left]
      have heq : {p : M | a < ell (X p)} =
          {p : M | a / ‖v‖ < inner ℝ (q : Ambient) (X p)} := by
        ext p
        simp only [mem_setOf_eq, hrep, hscale]
        have hdiv : a / ‖v‖ < inner ℝ (q : Ambient) (X p) ↔
            a < inner ℝ (q : Ambient) (X p) * ‖v‖ := div_lt_iff₀ hr
        simpa only [mul_comm] using hdiv.symm
      rw [heq]
      exact heightSuperlevel_isPreconnected_of_dense_sphere_directions
        X hX G hG hgood q (a / ‖v‖)
  have himage : X '' {p : M | a < ell (X p)} = range X ∩ ell ⁻¹' Ioi a := by
    ext z
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p, rfl⟩, hp⟩
    · rintro ⟨⟨p, rfl⟩, hp⟩
      exact ⟨p, hp, rfl⟩
  rw [← himage]
  exact hsource.image X hX.continuousOn

/-- The actual native compact connected torus is an instance of the preceding
general approximation theorem. -/
theorem nativeTorus_isTightImage_of_dense_sphere_heightSuperlevels
    (X : NonrigidTorusSource → Ambient) (hX : Continuous X)
    (G : Set RoundSphere) (hG : Dense G)
    (hgood : ∀ w ∈ G, ∀ a : ℝ,
      IsPreconnected {p : NonrigidTorusSource | a < inner ℝ (w : Ambient) (X p)}) :
    IsTightImage X :=
  isTightImage_of_dense_sphere_heightSuperlevels X hX G hG hgood

end
end TightVer401
