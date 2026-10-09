import TightVer401.BandCoordinateLift

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped Manifold ContDiff
set_option backward.isDefEq.respectTransparency false

def openCoordinateDifferential {U : TopologicalSpace.Opens Coord}
    (f : U → Ambient) (p : U) : Coord →L[ℝ] Ambient := mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) f p

def openCoordinateInclusionDifferential (U : TopologicalSpace.Opens Coord) (p : U) :
    Coord →L[ℝ] Coord := mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Coord) (Subtype.val : U → Coord) p

theorem openCoordinate_inclusion_derivative (U : TopologicalSpace.Opens Coord) (p : U) :
    openCoordinateInclusionDifferential U p =
      ContinuousLinearMap.id ℝ Coord := by
  exact mfderiv_extChartAt_self (I := 𝓘(ℝ, Coord)) (x := p)

theorem openCoordinate_restriction_derivative {U : TopologicalSpace.Opens Coord}
    {f : Coord → Ambient} (p : U) (hf : DifferentiableAt ℝ f p.val) :
    openCoordinateDifferential (fun q : U => f q.val) p = fderiv ℝ f p.val := by
  have hv := (contMDiff_subtype_val (I := 𝓘(ℝ, Coord)) (n := ∞) p).mdifferentiableAt (by simp)
  have hd : openCoordinateDifferential (fun q : U => f q.val) p =
      (fderiv ℝ f p.val).comp
        (openCoordinateInclusionDifferential U p) :=
    (hf.hasFDerivAt.hasMFDerivAt.comp p hv.hasMFDerivAt).mfderiv
  rw [openCoordinate_inclusion_derivative, ContinuousLinearMap.comp_id] at hd
  exact hd

def bandFromCoordinatesDifferential (L b : ℝ) [Fact (0 < L)] (p : coordinateBandOpen b) :
    Coord →L[ℝ] (ℝ × ℝ) :=
  mfderiv 𝓘(ℝ, Coord) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (bandFromCoordinates L b) p

end
end TightVer401
