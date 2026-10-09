import TightVer401.RuledCentralGaussDerivative
import TightVer401.AmbientCross

/-! Actual orientation of the SAME original central Gauss trace. The signed
cross product is produced from the checked central Gauss derivatives and the
actual frame orientation. This does not yet prove a Cartesian Jacobian sign
on the entire selected flow annulus. -/
namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped Matrix RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false

/-- The original Gauss map reverses the oriented (phase,height) plane at
height zero. Both actual derivative columns are retained. -/
theorem positiveExit_selectedSourceGeometry_central_gauss_cross
    {T : ℝ} (d : PeriodicRuledFrame T) (r : ℝ)
    (horient : ambientCross (d.T r) (d.E r) = d.n r) :
    ambientCross (coordPartial 0 d.rawGaussMap (![r, 0] : Coord))
      (coordPartial 1 d.rawGaussMap (![r, 0] : Coord)) =
        (-(d.τ r)^2) • d.n r := by
  rw [periodicRuledFrame_rawGaussMap_central_partial_s,
    periodicRuledFrame_rawGaussMap_central_partial_u]
  calc
    ambientCross (-d.τ r • d.E r) (-d.τ r • d.T r) =
        (-(d.τ r)^2) • ambientCross (d.T r) (d.E r) := by
      ext i
      fin_cases i <;> simp [ambientCross, cross_apply] <;> ring
    _ = (-(d.τ r)^2) • d.n r := by rw [horient]

/-- The signed central Gauss area is the actual negative square of torsion;
nonzero torsion and the SAME unit normal give a strict orientation sign. -/
theorem positiveExit_selectedSourceGeometry_central_gauss_orientation
    {T : ℝ} (d : PeriodicRuledFrame T) (r : ℝ)
    (horient : ambientCross (d.T r) (d.E r) = d.n r) :
    inner ℝ (d.n r)
      (ambientCross (coordPartial 0 d.rawGaussMap (![r, 0] : Coord))
        (coordPartial 1 d.rawGaussMap (![r, 0] : Coord))) = -(d.τ r)^2 ∧
    inner ℝ (d.n r)
      (ambientCross (coordPartial 0 d.rawGaussMap (![r, 0] : Coord))
        (coordPartial 1 d.rawGaussMap (![r, 0] : Coord))) < 0 := by
  have heq : inner ℝ (d.n r)
      (ambientCross (coordPartial 0 d.rawGaussMap (![r, 0] : Coord))
        (coordPartial 1 d.rawGaussMap (![r, 0] : Coord))) = -(d.τ r)^2 := by
    rw [positiveExit_selectedSourceGeometry_central_gauss_cross d r horient,
      real_inner_smul_right, (d.orthonormal r).2.2.1, mul_one]
  exact ⟨heq, by rw [heq]; exact neg_neg_of_pos (sq_pos_of_ne_zero (d.torsion_ne_zero r))⟩

end
end TightVer401
