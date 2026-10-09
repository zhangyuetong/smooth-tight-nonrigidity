import TightVer401.IdentityBandPlanarSupportImage
import TightVer401.PlanarSupportConverse

/-! Uniqueness of the actual Cartesian support height, and equality of its
full local derivative germ on overlaps of reconstructed support maps. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology RealInnerProductSpace

/-- A reconstructed Cartesian support map determines its scalar potential. -/
theorem identityBand_planar_potential_eq_height (G : Coord → ℝ) (p : Coord) :
    G p = planarPotential (planarSupportMap G) p := by
  rw [planarPotential_eq_weight_height, planarSupportMap_height]
  field_simp [(planarWeight_pos p).ne']

/-- Potential values cannot depend on a choice of reconstructed branch. -/
theorem identityBand_planar_potential_unique {G H : Coord → ℝ} {U : Set Coord}
    (hmap : EqOn (planarSupportMap G) (planarSupportMap H) U) : EqOn G H U := by
  intro p hp
  rw [identityBand_planar_potential_eq_height G p,
    identityBand_planar_potential_eq_height H p]
  exact congrArg (fun x : Ambient => inner ℝ x (planarNormalNumerator p)) (hmap hp)

/-- On an open overlap the actual potential germs, hence both Cartesian
first and second derivatives, agree. Smoothness is supplied by the already
constructed local/global potentials and is not needed for germ equality. -/
theorem identityBand_planar_potential_overlap {G H : Coord → ℝ} {U : Set Coord}
    (hU : IsOpen U) (hmap : EqOn (planarSupportMap G) (planarSupportMap H) U)
    {p : Coord} (hp : p ∈ U) :
    G =ᶠ[𝓝 p] H ∧ fderiv ℝ G p = fderiv ℝ H p ∧
      planarHessian G p = planarHessian H p := by
  have heq : G =ᶠ[𝓝 p] H :=
    (identityBand_planar_potential_unique hmap).eventuallyEq_of_mem (hU.mem_nhds hp)
  refine ⟨heq, heq.fderiv_eq, ?_⟩
  ext i j
  unfold planarHessian coordPartial
  have hd : (fun q => fderiv ℝ G q (Pi.single j 1)) =ᶠ[𝓝 p]
      (fun q => fderiv ℝ H q (Pi.single j 1)) := by
    filter_upwards [heq.eventuallyEq_nhds] with q hq
    exact congrArg (fun d : Coord →L[ℝ] ℝ => d (Pi.single j 1)) hq.fderiv_eq
  exact congrArg (fun d : Coord →L[ℝ] ℝ => d (Pi.single i 1)) hd.fderiv_eq

end
end TightVer401