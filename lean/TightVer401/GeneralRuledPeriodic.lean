import TightVer401.GeneralRuledReturn
import TightVer401.GeneralRuledCurvature

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff

theorem curve_deriv_periodic {c : ℝ → Ambient} {L : ℝ} (hc : Function.Periodic c L) :
    Function.Periodic (deriv c) L := by
  intro s
  have he : (fun t => c (t + L)) = c := funext hc
  have hd := congrArg (fun f : ℝ → Ambient => deriv f s) he
  simpa only [deriv_comp_add_const] using hd

theorem general_ruled_periodic_coefficients {c e : ℝ → Ambient} {L : ℝ}
    (hc : Function.Periodic c L) (he : Function.Periodic e L) :
    Function.Periodic (generalRuledLinearCoefficient c e) L ∧
      Function.Periodic (generalRuledQuadraticCoefficient c e) L := by
  have hc₁ := curve_deriv_periodic hc
  have he₁ := curve_deriv_periodic he
  have hc₂ := curve_deriv_periodic hc₁
  have he₂ := curve_deriv_periodic he₁
  constructor <;> intro s <;>
    simp only [generalRuledLinearCoefficient, generalRuledQuadraticCoefficient,
      generalRuledQ₁, generalRuledQ₂, generalRuledDelta, hc₁ s, he₁ s, hc₂ s, he₂ s, he s]

theorem general_ruled_periodic_map {c e : ℝ → Ambient} {L : ℝ}
    (hc : Function.Periodic c L) (he : Function.Periodic e L) (t u : ℝ) :
    ruledMap c e (![t + L, u] : Coord) = ruledMap c e (![t, u] : Coord) := by
  simp only [ruledMap, Matrix.cons_val_zero, Matrix.cons_val_one, hc t, he t]

end
end TightVer401
