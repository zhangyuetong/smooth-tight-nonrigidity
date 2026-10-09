import TightVer401.QuadraticRadialFillingExteriorCollar
import Mathlib.Topology.Homeomorph.Lemmas

/-! Actual boundary injectivity and the homeomorphism to its actual image. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped Topology

def quadraticRadialFillingBoundary (ε S : ℝ) : Set Coord :=
  quadraticRadialFillingRadiusLevel ε ∪ quadraticRadialFillingRadiusLevel S

theorem quadraticRadialFilling_boundary_isCompact (ε S : ℝ) :
    IsCompact (quadraticRadialFillingBoundary ε S) :=
  (quadraticRadialFilling_radiusLevel_isCompact ε).union
    (quadraticRadialFilling_radiusLevel_isCompact S)

/-- The supplied actual inner-circle formula has exactly physical image
radius `C`; this is an adapter for the separately proved inner formula. -/
theorem quadraticRadialFilling_boundary_inner_radius
    {G : Coord → Coord} {ε C : ℝ} (hε : 0 < ε) (hC : 0 < C)
    (hInner : ∀ x ∈ quadraticRadialFillingRadiusLevel ε, G x = (C / ε) • x)
    {x : Coord} (hx : x ∈ quadraticRadialFillingRadiusLevel ε) :
    planarRadius (G x) = C := by
  rw [hInner x hx, quadraticRadialFilling_radius_smul, abs_of_pos (div_pos hC hε)]
  change planarRadius x = ε at hx
  rw [hx]
  exact div_mul_cancel₀ C hε.ne'

/-- The two actual boundary restrictions are jointly injective: scalar
cancellation handles the inner side, ordinary incoming injectivity handles
the outer side, and physical radius separates their two images. -/
theorem quadraticRadialFilling_boundary_injOn
    {G : Coord → Coord} {ε S C : ℝ} (hε : 0 < ε) (_hεS : ε < S) (hC : 0 < C)
    (hInner : ∀ x ∈ quadraticRadialFillingRadiusLevel ε, G x = (C / ε) • x)
    (hOuter : InjOn G (quadraticRadialFillingRadiusLevel S))
    (hBound : ∀ x ∈ quadraticRadialFillingRadiusLevel S, planarRadius (G x) < C) :
    InjOn G (quadraticRadialFillingBoundary ε S) := by
  intro x hx y hy hxy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · have hscale : (C / ε) • x = (C / ε) • y := by
      rw [← hInner x hx, ← hInner y hy]
      exact hxy
    ext i
    have hi := congrFun hscale i
    change (C / ε) * x i = (C / ε) * y i at hi
    exact mul_left_cancel₀ (div_ne_zero hC.ne' hε.ne') hi
  · have hb := hBound y hy
    rw [← hxy, quadraticRadialFilling_boundary_inner_radius hε hC hInner hx] at hb
    exact False.elim (lt_irrefl C hb)
  · have hb := hBound x hx
    rw [hxy, quadraticRadialFilling_boundary_inner_radius hε hC hInner hy] at hb
    exact False.elim (lt_irrefl C hb)
  · exact hOuter hx hy hxy

/-- Construct the actual boundary homeomorphism to the actual map image from
compactness, continuity and the proved joint boundary injectivity. -/
def quadraticRadialFillingBoundaryHomeomorph
    {G : Coord → Coord} {ε S C : ℝ} (hε : 0 < ε) (hεS : ε < S) (hC : 0 < C)
    (hG : ContinuousOn G (quadraticRadialFillingBoundary ε S))
    (hInner : ∀ x ∈ quadraticRadialFillingRadiusLevel ε, G x = (C / ε) • x)
    (hOuter : InjOn G (quadraticRadialFillingRadiusLevel S))
    (hBound : ∀ x ∈ quadraticRadialFillingRadiusLevel S, planarRadius (G x) < C) :
    quadraticRadialFillingBoundary ε S ≃ₜ G '' quadraticRadialFillingBoundary ε S := by
  letI : CompactSpace (quadraticRadialFillingBoundary ε S) :=
    isCompact_iff_compactSpace.mp (quadraticRadialFilling_boundary_isCompact ε S)
  let e : quadraticRadialFillingBoundary ε S ≃ G '' quadraticRadialFillingBoundary ε S :=
    Equiv.Set.imageOfInjOn G (quadraticRadialFillingBoundary ε S)
      (quadraticRadialFilling_boundary_injOn hε hεS hC hInner hOuter hBound)
  have he : Continuous e := hG.domRestrict.subtype_mk
    (fun x => mem_image_of_mem G x.property)
  exact e.toHomeomorphOfContinuousClosed he he.isClosedMap

theorem quadraticRadialFillingBoundaryHomeomorph_apply
    {G : Coord → Coord} {ε S C : ℝ} (hε : 0 < ε) (hεS : ε < S) (hC : 0 < C)
    (hG : ContinuousOn G (quadraticRadialFillingBoundary ε S))
    (hInner : ∀ x ∈ quadraticRadialFillingRadiusLevel ε, G x = (C / ε) • x)
    (hOuter : InjOn G (quadraticRadialFillingRadiusLevel S))
    (hBound : ∀ x ∈ quadraticRadialFillingRadiusLevel S, planarRadius (G x) < C)
    (x : quadraticRadialFillingBoundary ε S) :
    (quadraticRadialFillingBoundaryHomeomorph hε hεS hC hG hInner hOuter hBound x : Coord) =
      G x := rfl

theorem quadraticRadialFilling_exists_boundary_homeomorph
    {G : Coord → Coord} {ε S C : ℝ} (hε : 0 < ε) (hεS : ε < S) (hC : 0 < C)
    (hG : ContinuousOn G (quadraticRadialFillingBoundary ε S))
    (hInner : ∀ x ∈ quadraticRadialFillingRadiusLevel ε, G x = (C / ε) • x)
    (hOuter : InjOn G (quadraticRadialFillingRadiusLevel S))
    (hBound : ∀ x ∈ quadraticRadialFillingRadiusLevel S, planarRadius (G x) < C) :
    ∃ Φ : quadraticRadialFillingBoundary ε S ≃ₜ G '' quadraticRadialFillingBoundary ε S,
      ∀ x : quadraticRadialFillingBoundary ε S, (Φ x : Coord) = G x :=
  ⟨quadraticRadialFillingBoundaryHomeomorph hε hεS hC hG hInner hOuter hBound,
    quadraticRadialFillingBoundaryHomeomorph_apply hε hεS hC hG hInner hOuter hBound⟩

end
end TightVer401
