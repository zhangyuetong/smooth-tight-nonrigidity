import TightVer401.QuadraticRadialFillingGradientNesting
import TightVer401.QuadraticRadialFillingBoundary

/-! Exact actual round source annuli, their closures, boundaries and Cartesian images.
This source geometry does not assume a gradient image or a degree conclusion. -/
namespace TightVer401
noncomputable section
open Set Metric Function OAI.SmoothLocal.Geometry
open scoped Topology

theorem quadraticRadialFillingRoundFilling_closedBall (r : ℝ) (hr : 0 < r) :
    quadraticRadialFillingRoundFilling r hr '' closedBall (0 : ℂ) 1 =
      closedBall (0 : ℂ) r := by
  calc
    _ = quadraticRadialFillingRoundFilling r hr '' closure (ball (0 : ℂ) 1) := by
      rw [closure_ball _ one_ne_zero]
    _ = closure (quadraticRadialFillingRoundFilling r hr '' ball (0 : ℂ) 1) :=
      (quadraticRadialFillingRoundFilling r hr).image_closure _
    _ = closedBall (0 : ℂ) r := by
      rw [quadraticRadialFillingRoundFilling_ball, closure_ball _ hr.ne']

theorem quadraticRadialFillingRoundFilling_closure_ball (r : ℝ) (hr : 0 < r) :
    closure (quadraticRadialFillingRoundFilling r hr '' ball (0 : ℂ) 1) =
      quadraticRadialFillingRoundFilling r hr '' closedBall (0 : ℂ) 1 := by
  rw [← (quadraticRadialFillingRoundFilling r hr).image_closure,
    closure_ball _ one_ne_zero]

theorem quadraticRadialFillingRoundFilling_frontier_ball (r : ℝ) (hr : 0 < r) :
    frontier (quadraticRadialFillingRoundFilling r hr '' ball (0 : ℂ) 1) =
      quadraticRadialFillingRoundFilling r hr '' sphere (0 : ℂ) 1 := by
  rw [← (quadraticRadialFillingRoundFilling r hr).image_frontier,
    frontier_ball _ one_ne_zero]

theorem quadraticRadialFillingRoundFilling_sphere_coord (r : ℝ) (hr : 0 < r) :
    seamComplexCoord '' (quadraticRadialFillingRoundFilling r hr '' sphere (0 : ℂ) 1) =
      quadraticRadialFillingRadiusLevel r := by
  rw [quadraticRadialFillingRoundFilling_sphere]
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    change planarRadius (seamComplexCoord z) = r
    rw [quadraticRadialFillingRadius_complex]
    simpa only [mem_sphere, dist_zero_right] using hz
  · intro hx
    change planarRadius x = r at hx
    refine ⟨angularDescentComplex x, ?_, quadraticRadialFillingCoord_complex x⟩
    simpa only [mem_sphere, dist_zero_right, angularDescentComplex_norm] using hx

theorem quadraticRadialFillingRoundAnnulus_open_eq
    {ρ S : ℝ} (hρ : 0 < ρ) (hS : 0 < S) :
    (quadraticRadialFillingRoundFilling S hS '' ball (0 : ℂ) 1) \
      closure (quadraticRadialFillingRoundFilling ρ hρ '' ball (0 : ℂ) 1) =
      {z : ℂ | ρ < ‖z‖ ∧ ‖z‖ < S} := by
  rw [quadraticRadialFillingRoundFilling_closure_ball,
    quadraticRadialFillingRoundFilling_ball, quadraticRadialFillingRoundFilling_closedBall]
  ext z
  simp only [mem_diff, mem_ball, mem_closedBall, dist_zero_right, not_le, mem_setOf_eq]
  exact and_comm

theorem quadraticRadialFillingRoundAnnulus_closed_eq
    {ρ S : ℝ} (hρ : 0 < ρ) (hS : 0 < S) :
    (quadraticRadialFillingRoundFilling S hS '' closedBall (0 : ℂ) 1) \
      (quadraticRadialFillingRoundFilling ρ hρ '' ball (0 : ℂ) 1) =
      {z : ℂ | ρ ≤ ‖z‖ ∧ ‖z‖ ≤ S} := by
  rw [quadraticRadialFillingRoundFilling_closedBall, quadraticRadialFillingRoundFilling_ball]
  ext z
  simp only [mem_diff, mem_ball, mem_closedBall, dist_zero_right, not_lt, mem_setOf_eq]
  exact and_comm

theorem quadraticRadialFillingRoundAnnulus_nested
    {ρ S : ℝ} (hρ : 0 < ρ) (hS : 0 < S) (hρS : ρ < S) :
    quadraticRadialFillingRoundFilling ρ hρ '' closedBall (0 : ℂ) 1 ⊆
      quadraticRadialFillingRoundFilling S hS '' ball (0 : ℂ) 1 := by
  rw [quadraticRadialFillingRoundFilling_closedBall, quadraticRadialFillingRoundFilling_ball]
  exact closedBall_subset_ball hρS

/-- Both edges of a nondegenerate actual round annulus are approached from its interior. -/
theorem quadraticRadialFilling_complexAnnulus_closure
    {ρ S : ℝ} (hρ : 0 < ρ) (hρS : ρ < S) :
    closure (ball (0 : ℂ) S \ closedBall (0 : ℂ) ρ) =
      closedBall (0 : ℂ) S \ ball (0 : ℂ) ρ := by
  have hS : 0 < S := hρ.trans hρS
  apply Subset.antisymm
  · apply closure_minimal
    · intro z hz
      exact ⟨ball_subset_closedBall hz.1,
        fun hb => hz.2 (ball_subset_closedBall hb)⟩
    · exact isClosed_closedBall.sdiff isOpen_ball
  · intro z hz
    by_cases hzS : ‖z‖ < S
    · have hinner : z ∈ closure ((closedBall (0 : ℂ) ρ)ᶜ) := by
        rw [closure_compl, interior_closedBall _ hρ.ne']
        exact hz.2
      exact isOpen_ball.inter_closure
        ⟨(by simpa only [mem_ball, dist_zero_right] using hzS), hinner⟩
    · have hzn : ‖z‖ = S :=
        le_antisymm (by simpa only [mem_closedBall, dist_zero_right] using hz.1)
          (not_lt.mp hzS)
      have hinner : z ∈ (closedBall (0 : ℂ) ρ)ᶜ := by
        simpa only [mem_compl_iff, mem_closedBall, dist_zero_right, hzn, not_le] using hρS
      have houter : z ∈ closure (ball (0 : ℂ) S) := by
        rw [closure_ball _ hS.ne']
        exact hz.1
      exact isClosed_closedBall.isOpen_compl.closure_inter ⟨houter,hinner⟩

theorem quadraticRadialFillingRoundAnnulus_closure
    {ρ S : ℝ} (hρ : 0 < ρ) (hS : 0 < S) (hρS : ρ < S) :
    closure ((quadraticRadialFillingRoundFilling S hS '' ball (0 : ℂ) 1) \
      closure (quadraticRadialFillingRoundFilling ρ hρ '' ball (0 : ℂ) 1)) =
      (quadraticRadialFillingRoundFilling S hS '' closedBall (0 : ℂ) 1) \
        (quadraticRadialFillingRoundFilling ρ hρ '' ball (0 : ℂ) 1) := by
  rw [quadraticRadialFillingRoundFilling_closure_ball,
    quadraticRadialFillingRoundFilling_closedBall,
    quadraticRadialFillingRoundFilling_closedBall,
    quadraticRadialFillingRoundFilling_ball,
    quadraticRadialFillingRoundFilling_ball]
  exact quadraticRadialFilling_complexAnnulus_closure hρ hρS

theorem quadraticRadialFillingRoundAnnulus_open_coord
    {ρ S : ℝ} (hρ : 0 < ρ) (hS : 0 < S) :
    seamComplexCoord '' ((quadraticRadialFillingRoundFilling S hS '' ball (0 : ℂ) 1) \
      closure (quadraticRadialFillingRoundFilling ρ hρ '' ball (0 : ℂ) 1)) =
      quadraticRadialFillingOpenAnnulus ρ S := by
  rw [quadraticRadialFillingRoundAnnulus_open_eq hρ hS]
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    change ρ < planarRadius (seamComplexCoord z) ∧ planarRadius (seamComplexCoord z) < S
    rwa [quadraticRadialFillingRadius_complex]
  · intro hx
    refine ⟨angularDescentComplex x, ?_, quadraticRadialFillingCoord_complex x⟩
    change ρ < ‖angularDescentComplex x‖ ∧ ‖angularDescentComplex x‖ < S
    rwa [angularDescentComplex_norm]

theorem quadraticRadialFillingRoundAnnulus_closed_coord
    {ρ S : ℝ} (hρ : 0 < ρ) (hS : 0 < S) :
    seamComplexCoord '' ((quadraticRadialFillingRoundFilling S hS '' closedBall (0 : ℂ) 1) \
      (quadraticRadialFillingRoundFilling ρ hρ '' ball (0 : ℂ) 1)) =
      quadraticRadialFillingClosedAnnulus ρ S := by
  rw [quadraticRadialFillingRoundAnnulus_closed_eq hρ hS]
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    change ρ ≤ planarRadius (seamComplexCoord z) ∧ planarRadius (seamComplexCoord z) ≤ S
    rwa [quadraticRadialFillingRadius_complex]
  · intro hx
    refine ⟨angularDescentComplex x, ?_, quadraticRadialFillingCoord_complex x⟩
    change ρ ≤ ‖angularDescentComplex x‖ ∧ ‖angularDescentComplex x‖ ≤ S
    rwa [angularDescentComplex_norm]

theorem quadraticRadialFilling_openAnnulus_closure_eq
    {ρ S : ℝ} (hρ : 0 < ρ) (hS : 0 < S) (hρS : ρ < S) :
    closure (quadraticRadialFillingOpenAnnulus ρ S) =
      quadraticRadialFillingClosedAnnulus ρ S := by
  let A := (quadraticRadialFillingRoundFilling S hS '' ball (0 : ℂ) 1) \
    closure (quadraticRadialFillingRoundFilling ρ hρ '' ball (0 : ℂ) 1)
  have he : seamComplexCoord '' closure A = closure (seamComplexCoord '' A) :=
    seamComplexCoord.toHomeomorph.image_closure A
  dsimp [A] at he
  rw [quadraticRadialFillingRoundAnnulus_closure hρ hS hρS,
    quadraticRadialFillingRoundAnnulus_closed_coord hρ hS,
    quadraticRadialFillingRoundAnnulus_open_coord hρ hS] at he
  exact he.symm

theorem quadraticRadialFilling_complexAnnulus_frontier
    {ρ S : ℝ} (hρ : 0 < ρ) (hρS : ρ < S) :
    frontier (ball (0 : ℂ) S \ closedBall (0 : ℂ) ρ) =
      sphere (0 : ℂ) ρ ∪ sphere (0 : ℂ) S := by
  rw [(isOpen_ball.sdiff isClosed_closedBall).frontier_eq,
    quadraticRadialFilling_complexAnnulus_closure hρ hρS]
  ext z
  simp only [mem_diff, mem_ball, mem_closedBall, mem_sphere,
    dist_zero_right, not_lt, not_le, mem_union]
  constructor
  · rintro ⟨hc,hn⟩
    by_cases he : ‖z‖ = ρ
    · exact Or.inl he
    · right
      have hl : ρ < ‖z‖ := lt_of_le_of_ne hc.2 (Ne.symm he)
      have hu : ¬ ‖z‖ < S := fun hs => hn ⟨hs,hl⟩
      exact le_antisymm hc.1 (not_lt.mp hu)
  · rintro (he | he)
    · exact ⟨⟨he.le.trans hρS.le, he.ge⟩, fun h => not_lt_of_ge he.le h.2⟩
    · exact ⟨⟨he.le, hρS.le.trans he.ge⟩, fun h => not_lt_of_ge he.ge h.1⟩

theorem quadraticRadialFillingRoundAnnulus_frontier
    {ρ S : ℝ} (hρ : 0 < ρ) (hS : 0 < S) (hρS : ρ < S) :
    frontier ((quadraticRadialFillingRoundFilling S hS '' ball (0 : ℂ) 1) \
      closure (quadraticRadialFillingRoundFilling ρ hρ '' ball (0 : ℂ) 1)) =
      (quadraticRadialFillingRoundFilling ρ hρ '' sphere (0 : ℂ) 1) ∪
        (quadraticRadialFillingRoundFilling S hS '' sphere (0 : ℂ) 1) := by
  rw [quadraticRadialFillingRoundFilling_closure_ball,
    quadraticRadialFillingRoundFilling_closedBall,
    quadraticRadialFillingRoundFilling_ball,
    quadraticRadialFillingRoundFilling_sphere,
    quadraticRadialFillingRoundFilling_sphere]
  exact quadraticRadialFilling_complexAnnulus_frontier hρ hρS

theorem quadraticRadialFilling_openAnnulus_frontier_eq
    {ρ S : ℝ} (hρ : 0 < ρ) (hS : 0 < S) (hρS : ρ < S) :
    frontier (quadraticRadialFillingOpenAnnulus ρ S) =
      quadraticRadialFillingRadiusLevel ρ ∪ quadraticRadialFillingRadiusLevel S := by
  let A := (quadraticRadialFillingRoundFilling S hS '' ball (0 : ℂ) 1) \
    closure (quadraticRadialFillingRoundFilling ρ hρ '' ball (0 : ℂ) 1)
  have he : seamComplexCoord '' frontier A = frontier (seamComplexCoord '' A) :=
    seamComplexCoord.toHomeomorph.image_frontier A
  dsimp [A] at he
  rw [quadraticRadialFillingRoundAnnulus_frontier hρ hS hρS, image_union,
    quadraticRadialFillingRoundFilling_sphere_coord,
    quadraticRadialFillingRoundFilling_sphere_coord,
    quadraticRadialFillingRoundAnnulus_open_coord hρ hS] at he
  exact he.symm

end
end TightVer401

