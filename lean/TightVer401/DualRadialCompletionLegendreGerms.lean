import TightVer401.PlanarLegendre

/-! Exact scalar Legendre overlap recovery from an actual partial inverse.
These algebraic identities do not assume smoothness or any continued image.
The caller separately identifies the forward map with its actual gradient.
-/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped Topology Matrix

/-- The actual scalar double transform returns the original potential on
its source, using only the inverse identity and the symmetric pairing. -/
theorem dualRadialCompletionLegendre_involutive
    (G : Coord → ℝ) (e : OpenPartialHomeomorph Coord Coord) :
    EqOn (planarLegendre (planarLegendre G e) e.symm) G e.source := by
  intro p hp
  change e p ⬝ᵥ p -
    (e.symm (e p) ⬝ᵥ e p - G (e.symm (e p))) = G p
  rw [e.left_inv hp, dotProduct_comm (e p) p]
  ring

/-- Double-transform recovery is an actual ambient germ at every source
point, because the ordinary partial-homeomorphism source is open. -/
theorem dualRadialCompletionLegendre_involutive_germ
    (G : Coord → ℝ) (e : OpenPartialHomeomorph Coord Coord)
    {p : Coord} (hp : p ∈ e.source) :
    planarLegendre (planarLegendre G e) e.symm =ᶠ[𝓝 p] G := by
  filter_upwards [e.open_source.mem_nhds hp] with q hq
  exact dualRadialCompletionLegendre_involutive G e hq

/-- Replacing the first transform by a scalar potential equal to it on the
actual target preserves the original potential after the inverse transform. -/
theorem dualRadialCompletionLegendre_recovery
    (G H : Coord → ℝ) (e : OpenPartialHomeomorph Coord Coord)
    (hH : EqOn H (planarLegendre G e) e.target) :
    EqOn (planarLegendre H e.symm) G e.source := by
  intro p hp
  change e p ⬝ᵥ p - H (e p) = G p
  rw [hH (e.map_source hp)]
  exact dualRadialCompletionLegendre_involutive G e hp

/-- An unchanged scalar dual overlap gives actual ambient recovery germs;
no derivative or inverse-gradient conclusion is supplied as a premise. -/
theorem dualRadialCompletionLegendre_recovery_germ
    (G H : Coord → ℝ) (e : OpenPartialHomeomorph Coord Coord)
    (hH : EqOn H (planarLegendre G e) e.target)
    {p : Coord} (hp : p ∈ e.source) :
    planarLegendre H e.symm =ᶠ[𝓝 p] G := by
  filter_upwards [e.open_source.mem_nhds hp] with q hq
  exact dualRadialCompletionLegendre_recovery G H e hH hq

end
end TightVer401
