import TightVer401.CovariantSpeedCellBounds
import TightVer401.CovariantSpeedEmbedding
import TightVer401.CurveL1StabilityProjection

namespace TightVer401
noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem covariantSpeed_horizontal_full_moment_zero {T : ℝ} {ξ : ℂ}
    {a : ℝ → ℝ} {P : ℝ → E} (π : E →L[ℝ] ℂ)
    (ha : Continuous a) (hP : Continuous P) (haT : Function.Periodic a T)
    (hPcell : ∀ t, π (P (t + T)) = ξ * π (P t)) (hξ : ξ ≠ 1)
    (N : ℕ) (hN : ξ ^ N = 1) :
    (∫ r in 0..(N : ℝ) * T, a r • π (P r)) = 0 := by
  have hp := covariantSpeedCurve_periodic ha (π.continuous.comp hP) haT hPcell hξ N hN
  have hraw := covariantSpeedCurve_raw_periodic hp
  have he := hraw 0
  simpa only [speedCurve, OAI.ClosedSurfaceR4.PeriodicPrimitive.rawPrimitive,
    Function.comp_apply, zero_add, intervalIntegral.integral_same] using he

/-- Horizontal cell covariance and the actual scalar closing moment imply
the complete spatial closing moment, by ordinary jointly injective coordinates. -/
theorem covariantSpeed_full_moment_zero {T : ℝ} {ξ : ℂ} {a : ℝ → ℝ} {P : ℝ → E}
    (π : E →L[ℝ] ℂ) (σ : E →L[ℝ] ℝ)
    (hjoint : Function.Injective (fun v : E => (π v, σ v)))
    (ha : Continuous a) (hP : Continuous P) (haT : Function.Periodic a T)
    (hPcell : ∀ t, π (P (t + T)) = ξ * π (P t))
    (hσT : Function.Periodic (σ ∘ P) T) (hξ : ξ ≠ 1) (N : ℕ) (hN : ξ ^ N = 1)
    (hscalar : (∫ r in 0..T, a r * σ (P r)) = 0) :
    (∫ r in 0..(N : ℝ) * T, a r • P r) = 0 := by
  have hhorizontal := covariantSpeed_horizontal_full_moment_zero π ha hP haT hPcell hξ N hN
  have hp : Function.Periodic (fun r => a r * σ (P r)) T := by
    intro r
    change a (r + T) * σ (P (r + T)) = a r * σ (P r)
    rw [haT r, show σ (P (r + T)) = σ (P r) from hσT r]
  have hvertical : (∫ r in 0..(N : ℝ) * T, a r * σ (P r)) = 0 := by
    have hf : Continuous (fun r => a r * σ (P r)) := ha.mul (σ.continuous.comp hP)
    rw [periodic_cellIntegral_nat_mul hf hp N,
      hscalar, smul_zero]
  apply hjoint
  apply Prod.ext
  · have he := speedCurve_linear_projection π ha hP ((N : ℝ) * T)
    change (∫ r in 0..(N : ℝ) * T, a r • π (P r)) = π (∫ r in 0..(N : ℝ) * T, a r • P r) at he
    simpa only [map_zero] using he.symm.trans hhorizontal
  · have he := speedCurve_linear_projection σ ha hP ((N : ℝ) * T)
    change (∫ r in 0..(N : ℝ) * T, a r * σ (P r)) = σ (∫ r in 0..(N : ℝ) * T, a r • P r) at he
    simpa only [map_zero] using he.symm.trans hvertical

theorem covariantSpeed_full_tangent_periodic {T : ℝ} {ξ : ℂ} {P : ℝ → E}
    (π : E →L[ℝ] ℂ) (σ : E →L[ℝ] ℝ)
    (hjoint : Function.Injective (fun v : E => (π v, σ v)))
    (hPcell : ∀ t, π (P (t + T)) = ξ * π (P t))
    (hσT : Function.Periodic (σ ∘ P) T) (N : ℕ) (hN : ξ ^ N = 1) :
    Function.Periodic P ((N : ℝ) * T) := by
  intro t
  apply hjoint
  apply Prod.ext
  · simpa only [Function.comp_apply, hN, one_mul] using
      corrugated_covariant_iterate (f := π ∘ P) (T := T) (ξ := ξ) hPcell N t
  · exact hσT.nat_mul N t

end
end TightVer401
