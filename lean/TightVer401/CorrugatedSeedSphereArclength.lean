import TightVer401.CorrugatedSeedSphereCurvature
import TightVer401.CorrugatedSeedSphereReparam
import TightVer401.NormalLoopEmbeddingArclength

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff RealInnerProductSpace

theorem normalLoopCurvature_arclength_comp {ζ : ℝ → Ambient} {ψ : ℝ → ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (hψ : ContDiff ℝ ∞ ψ)
    (hi : ∀ s, HasDerivAt ψ (‖deriv ζ (ψ s)‖)⁻¹ s) (s : ℝ) :
    normalLoopCurvature (ζ ∘ ψ) s = sphericalCurveGeodesicCurvature ζ (ψ s) := by
  rw [normalLoopCurvature_comp hζ hψ, (hi s).deriv, sphericalCurveGeodesicCurvature,
    inv_pow, div_eq_mul_inv]
  ring

theorem corrugatedSeedSphere_exists_arclength {N : ℕ} (hN : 2 ≤ N) :
    ∃ (e : ℝ ≃ₜ ℝ) (L : ℝ),
      0 < L ∧ e 0 = 0 ∧
      (e : ℝ → ℝ) = rawPrimitive (fun t => ‖deriv (corrugatedSeedSphere (N : ℝ)) t‖) ∧
      ContDiff ℝ ∞ e.symm ∧
      (∀ s, HasDerivAt e.symm (‖deriv (corrugatedSeedSphere (N : ℝ)) (e.symm s)‖)⁻¹ s) ∧
      (∀ s, e.symm (s + L) = e.symm s + 2 * Real.pi) ∧
      ContDiff ℝ ∞ (corrugatedSeedSphere (N : ℝ) ∘ e.symm) ∧
      Function.Periodic (corrugatedSeedSphere (N : ℝ) ∘ e.symm) L ∧
      InjOn (corrugatedSeedSphere (N : ℝ) ∘ e.symm) (Ico 0 L) ∧
      (∀ s, ‖corrugatedSeedSphere (N : ℝ) (e.symm s)‖ = 1) ∧
      (∀ s, 0 < corrugatedSeedSphere (N : ℝ) (e.symm s) 2) ∧
      (∀ s, ‖deriv (corrugatedSeedSphere (N : ℝ) ∘ e.symm) s‖ = 1) ∧
      0 < normalLoopCurvature (corrugatedSeedSphere (N : ℝ) ∘ e.symm) 0 ∧
      normalLoopCurvature (corrugatedSeedSphere (N : ℝ) ∘ e.symm) (e (Real.pi / N)) < 0 := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  let ζ := corrugatedSeedSphere (N : ℝ)
  let a : ℝ → ℝ := fun t => ‖deriv ζ t‖
  have hζ : ContDiff ℝ ∞ ζ := corrugatedSeedSphere_contDiff _
  have hζp : Function.Periodic ζ (2 * Real.pi) := corrugatedSeedSphere_periodic hN
  have hζ' := (contDiff_infty_iff_deriv.mp hζ).2
  have hapos : ∀ t, 0 < a t := fun t => norm_pos_iff.mpr (corrugatedSeedSphere_deriv_ne_zero hNr t)
  have ha : ContDiff ℝ ∞ a := hζ'.norm ℝ
    (fun t => corrugatedSeedSphere_deriv_ne_zero hNr t)
  have hp' : Function.Periodic (deriv ζ) (2 * Real.pi) :=
    normalLoop_derivative_periodic hζp
      (fun t => (hζ.differentiable (by simp) t).hasDerivAt)
  have hap : Function.Periodic a (2 * Real.pi) := by intro t; dsimp [a]; rw [hp' t]
  obtain ⟨e, he, hψ, hi, hshift⟩ := normalLoop_exists_global_arclength_inverse ha hapos hap Real.two_pi_pos
  let L := rawPrimitive a (2 * Real.pi)
  have hL : 0 < L := normalLoop_arclength_period_pos ha.continuous hapos Real.two_pi_pos
  have hz : e 0 = 0 := by rw [he]; simp [rawPrimitive]
  have hsz : e.symm 0 = 0 :=
    (congrArg e.symm hz.symm).trans (e.symm_apply_apply 0)
  refine ⟨e, L, hL, hz, he, hψ, hi, hshift, hζ.comp hψ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s
    change ζ (e.symm (s + L)) = ζ (e.symm s)
    rw [hshift s, hζp]
  · exact normalLoop_arclength_reparameterized_injective ha.continuous hapos e he
      (corrugatedSeedSphere_injOn hNr)
  · intro s; exact corrugatedSeedSphere_unit _ _
  · intro s; exact corrugatedSeedSphere_north _ _
  · intro s
    rw [sphericalCurve_comp_deriv (hζ.differentiable (by simp)) (hψ.differentiable (by simp)),
      (hi s).deriv, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hapos _)),
      inv_mul_cancel₀ (ne_of_gt (hapos _))]
  · rw [normalLoopCurvature_arclength_comp hζ hψ hi, hsz]
    exact corrugatedSeedSphere_curvature_positive hNr
  · rw [normalLoopCurvature_arclength_comp hζ hψ hi, e.symm_apply_apply]
    exact corrugatedSeedSphere_curvature_negative hNr

end
end TightVer401
