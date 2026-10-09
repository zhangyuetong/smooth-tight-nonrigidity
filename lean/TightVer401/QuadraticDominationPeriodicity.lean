import TightVer401.QuadraticDominationCalculus
import TightVer401.RuledPrimitives

/-! Angular periodicity of the explicit filler and its actual cylinder derivatives. -/
namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff

/-- Angular translation preserves the filler, for any common period of its traces. -/
theorem dualQuadraticFiller_angular_shift (R M L : ℝ) {chi h b : ℝ → ℝ}
    (hhper : Function.Periodic h L) (hbper : Function.Periodic b L) (p : Coord) :
    dualQuadraticFiller R M chi h b ![p 0, p 1 + L] =
      dualQuadraticFiller R M chi h b p := by
  simp [dualQuadraticFiller, hhper (p 1), hbper (p 1)]

/-- The fixed-radius angular profile is periodic without any smoothness hypothesis. -/
theorem dualQuadraticFiller_angular_periodic (R M L : ℝ) {chi h b : ℝ → ℝ}
    (hhper : Function.Periodic h L) (hbper : Function.Periodic b L) (r : ℝ) :
    Function.Periodic (fun theta => dualQuadraticFiller R M chi h b ![r, theta]) L := by
  intro theta
  simpa using dualQuadraticFiller_angular_shift R M L hhper hbper ![r, theta]

/-- Both actual first coordinate derivatives retain the angular period. -/
theorem dualQuadraticFiller_coordPartial_angular_shift (R M L : ℝ)
    {chi h b : ℝ → ℝ} (hchi : ContDiff ℝ ∞ chi)
    (hh : ContDiff ℝ ∞ h) (hb : ContDiff ℝ ∞ b)
    (hhper : Function.Periodic h L) (hbper : Function.Periodic b L)
    (p : Coord) (i : Fin 2) :
    coordPartial i (dualQuadraticFiller R M chi h b) ![p 0, p 1 + L] =
      coordPartial i (dualQuadraticFiller R M chi h b) p := by
  rw [dualQuadraticFiller_coordPartial R M hchi hh hb,
    dualQuadraticFiller_coordPartial R M hchi hh hb]
  simp [hhper (p 1), hbper (p 1), deriv_periodic hhper (p 1),
    deriv_periodic hbper (p 1)]

/-- The actual radial second derivative retains the angular period. -/
theorem dualQuadraticFiller_radial_second_angular_shift (R M L : ℝ)
    {chi h b : ℝ → ℝ} (hchi : ContDiff ℝ ∞ chi)
    (hh : ContDiff ℝ ∞ h) (hb : ContDiff ℝ ∞ b)
    (hhper : Function.Periodic h L) (hbper : Function.Periodic b L) (p : Coord) :
    coordPartial 0 (coordPartial 0 (dualQuadraticFiller R M chi h b))
        ![p 0, p 1 + L] =
      coordPartial 0 (coordPartial 0 (dualQuadraticFiller R M chi h b)) p := by
  rw [dualQuadraticFiller_radial_second R M hchi hh hb,
    dualQuadraticFiller_radial_second R M hchi hh hb]
  simp [hhper (p 1), hbper (p 1)]

/-- The actual angular second derivative retains the angular period. -/
theorem dualQuadraticFiller_angular_second_angular_shift (R M L : ℝ)
    {chi h b : ℝ → ℝ} (hchi : ContDiff ℝ ∞ chi)
    (hh : ContDiff ℝ ∞ h) (hb : ContDiff ℝ ∞ b)
    (hhper : Function.Periodic h L) (hbper : Function.Periodic b L) (p : Coord) :
    coordPartial 1 (coordPartial 1 (dualQuadraticFiller R M chi h b))
        ![p 0, p 1 + L] =
      coordPartial 1 (coordPartial 1 (dualQuadraticFiller R M chi h b)) p := by
  rw [dualQuadraticFiller_angular_second R M hchi hh hb,
    dualQuadraticFiller_angular_second R M hchi hh hb]
  simp [deriv_periodic (deriv_periodic hhper) (p 1),
    deriv_periodic (deriv_periodic hbper) (p 1)]

end
end TightVer401
