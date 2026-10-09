import TightVer401.FermiSupportSeam
import OAI.Geometry.WeakMTW.Analysis.IntegralEquation

namespace TightVer401
noncomputable section
open Set Filter Function OAI.SmoothLocal.Geometry
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

theorem exists_smooth_coordinate_germ_extension {H : Coord → ℝ} {U : Set Coord}
    (hU : IsOpen U) (hH : ContDiffOn ℝ ∞ H U) {p : Coord} (hp : p ∈ U) :
    ∃ G : Coord → ℝ, ContDiff ℝ ∞ G ∧ G =ᶠ[𝓝 p] H :=
  OAI.WeakMTWGlobalSupport.SmoothODE.exists_smooth_extension hU hH hp

theorem fermiCoordinatePartial_eventuallyEq {F G : Coord → ℝ} {p : Coord}
    (h : F =ᶠ[𝓝 p] G) (i : Fin 2) : coordPartial i F =ᶠ[𝓝 p] coordPartial i G := by
  filter_upwards [h.fderiv (𝕜 := ℝ)] with q hq
  exact congrArg (fun L : Coord →L[ℝ] ℝ => L (Pi.single i 1)) hq

theorem fermiSupport_eventuallyEq {F G : Coord → ℝ} {p : Coord}
    (h : F =ᶠ[𝓝 p] G) (κ : ℝ → ℝ) :
    fermiSupportL κ F =ᶠ[𝓝 p] fermiSupportL κ G ∧
    fermiSupportM κ F =ᶠ[𝓝 p] fermiSupportM κ G ∧
    fermiSupportN F =ᶠ[𝓝 p] fermiSupportN G := by
  have h0 := fermiCoordinatePartial_eventuallyEq h 0
  have h1 := fermiCoordinatePartial_eventuallyEq h 1
  have h00 := fermiCoordinatePartial_eventuallyEq h0 0
  have h01 := fermiCoordinatePartial_eventuallyEq h1 0
  have h11 := fermiCoordinatePartial_eventuallyEq h1 1
  constructor
  · filter_upwards [h, h0, h1, h00] with q hq h0q h1q h00q
    simp only [fermiSupportL, hq, h0q, h1q, h00q]
  · constructor
    · filter_upwards [h0, h01] with q h0q h01q
      simp only [fermiSupportM, h0q, h01q]
    · filter_upwards [h, h11] with q hq h11q
      simp only [fermiSupportN, hq, h11q]

theorem fermiSupport_local_seam_codazzi {κ : ℝ → ℝ} {H : Coord → ℝ} {U : Set Coord}
    (hκ : ContDiff ℝ ∞ κ) (hU : IsOpen U) (hH : ContDiffOn ℝ ∞ H U)
    {r : ℝ} (hr : (![r,0] : Coord) ∈ U) :
    coordPartial 1 (fermiSupportL κ H) ![r,0] =
      coordPartial 0 (fermiSupportM κ H) ![r,0] +
        κ r * fermiSupportN H ![r,0] + κ r * fermiSupportL κ H ![r,0] := by
  obtain ⟨G, hG, he⟩ := exists_smooth_coordinate_germ_extension hU hH hr
  have hcoeff := fermiSupport_eventuallyEq he κ
  have hLt := fermiCoordinatePartial_eventuallyEq hcoeff.1 1
  have hMr := fermiCoordinatePartial_eventuallyEq hcoeff.2.1 0
  rw [← hLt.eq_of_nhds, ← hMr.eq_of_nhds,
    ← hcoeff.2.2.eq_of_nhds, ← hcoeff.1.eq_of_nhds]
  exact fermiSupport_seam_codazzi hκ hG r

end
end TightVer401
