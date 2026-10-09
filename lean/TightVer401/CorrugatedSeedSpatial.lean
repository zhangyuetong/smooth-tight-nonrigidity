import TightVer401.CorrugatedSeedSphereCurvature

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff

def corrugatedSeedVerticalDensity (N t : ℝ) : ℝ :=
  -corrugatedSeedPlaneDet (corrugatedSeedBeta N t) (deriv (corrugatedSeedPartner N) t)
def corrugatedSeedVertical (N : ℝ) : ℝ → ℝ := rawPrimitive (corrugatedSeedVerticalDensity N)
def corrugatedSeedSpatial (N t : ℝ) : Ambient := WithLp.toLp 2
  ![(-Complex.I * corrugatedSeedPartner N t).re,
    (-Complex.I * corrugatedSeedPartner N t).im, corrugatedSeedVertical N t]
def corrugatedAmbientHorizontal (u : Ambient) : ℂ := ⟨u 0, u 1⟩

theorem corrugatedSeedVerticalDensity_contDiff (N : ℝ) :
    ContDiff ℝ ∞ (corrugatedSeedVerticalDensity N) := by
  have hb := corrugatedSeedBeta_contDiff N
  have hd := (contDiff_infty_iff_deriv.mp (corrugatedSeedPartner_contDiff N)).2
  unfold corrugatedSeedVerticalDensity corrugatedSeedPlaneDet
  change ContDiff ℝ ∞ (fun t => -(Complex.reCLM (corrugatedSeedBeta N t) *
    Complex.imCLM (deriv (corrugatedSeedPartner N) t) -
    Complex.imCLM (corrugatedSeedBeta N t) * Complex.reCLM (deriv (corrugatedSeedPartner N) t)))
  fun_prop

theorem corrugatedSeedVertical_contDiff (N : ℝ) : ContDiff ℝ ∞ (corrugatedSeedVertical N) :=
  rawPrimitive_contDiff (corrugatedSeedVerticalDensity_contDiff N)

theorem corrugatedSeedVertical_hasDerivAt (N t : ℝ) :
    HasDerivAt (corrugatedSeedVertical N) (corrugatedSeedVerticalDensity N t) t :=
  rawPrimitive_hasDerivAt (corrugatedSeedVerticalDensity_contDiff N).continuous t

theorem corrugatedSeedPartner_deriv_cell {N : ℝ} (hN : N ≠ 0) (t : ℝ) :
    deriv (corrugatedSeedPartner N) (t + corrugatedSeedCell N) =
      corrugatedSeedRotation N * deriv (corrugatedSeedPartner N) t := by
  change deriv (corrugatedSeedDelta (corrugatedSeedRoot N) N) _ =
    corrugatedSeedRotation N * deriv (corrugatedSeedDelta (corrugatedSeedRoot N) N) t
  rw [corrugatedSeedDelta_deriv, corrugatedSeedDelta_deriv,
    corrugatedSeedDeltaVelocity_cell hN]

theorem corrugatedSeedVerticalDensity_periodic {N : ℝ} (hN : N ≠ 0) :
    Function.Periodic (corrugatedSeedVerticalDensity N) (corrugatedSeedCell N) := by
  intro t
  unfold corrugatedSeedVerticalDensity
  rw [corrugatedSeedBeta_cell hN, corrugatedSeedPartner_deriv_cell hN]
  exact congrArg Neg.neg (corrugatedSeedPlaneDet_rotate (corrugatedSeedCell N) _ _)

theorem corrugatedSeedVertical_periodic {N : ℝ} (hN : 1 < N) :
    Function.Periodic (corrugatedSeedVertical N) (corrugatedSeedCell N) := by
  intro t
  unfold corrugatedSeedVertical rawPrimitive
  rw [(corrugatedSeedVerticalDensity_periodic (ne_of_gt (by linarith : 0 < N))).intervalIntegral_add_eq_add
    0 t (fun a b => (corrugatedSeedVerticalDensity_contDiff N).continuous.intervalIntegrable a b), zero_add]
  have hz : (∫ s in 0..corrugatedSeedCell N, corrugatedSeedVerticalDensity N s) = 0 := by
    simp only [corrugatedSeedVerticalDensity, intervalIntegral.integral_neg,
      corrugatedSeedPartner_action_cell hN, neg_zero]
  rw [hz, add_zero]

theorem corrugatedSeedSpatial_contDiff (N : ℝ) : ContDiff ℝ ∞ (corrugatedSeedSpatial N) := by
  have hh : ContDiff ℝ ∞ (fun t => -Complex.I * corrugatedSeedPartner N t) :=
    contDiff_const.mul (corrugatedSeedPartner_contDiff N)
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · exact Complex.reCLM.contDiff.comp hh
  · exact Complex.imCLM.contDiff.comp hh
  · exact corrugatedSeedVertical_contDiff N

theorem corrugatedSeedSpatial_hasDerivAt (N t : ℝ) :
    HasDerivAt (corrugatedSeedSpatial N)
      (WithLp.toLp 2 ![(-Complex.I * deriv (corrugatedSeedPartner N) t).re,
        (-Complex.I * deriv (corrugatedSeedPartner N) t).im, corrugatedSeedVerticalDensity N t]) t := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
  have hh := ((corrugatedSeedPartner_contDiff N).differentiable (by simp) t).hasDerivAt.const_mul (-Complex.I)
  have hp : HasDerivAt (fun s =>
      ![(-Complex.I * corrugatedSeedPartner N s).re,
        (-Complex.I * corrugatedSeedPartner N s).im, corrugatedSeedVertical N s])
      ![(-Complex.I * deriv (corrugatedSeedPartner N) t).re,
        (-Complex.I * deriv (corrugatedSeedPartner N) t).im, corrugatedSeedVerticalDensity N t] t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hh
    · exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hh
    · exact corrugatedSeedVertical_hasDerivAt N t
  exact e.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hp

theorem corrugatedSeedSpatial_horizontal (N t : ℝ) :
    corrugatedAmbientHorizontal (corrugatedSeedSpatial N t) = -Complex.I * corrugatedSeedPartner N t := by
  apply Complex.ext <;> rfl

theorem corrugatedSeedSpatial_vertical (N t : ℝ) :
    corrugatedSeedSpatial N t 2 = corrugatedSeedVertical N t := rfl

theorem corrugatedSeedSpatial_injOn_of_partner {N : ℝ} {S : Set ℝ}
    (hi : InjOn (corrugatedSeedPartner N) S) : InjOn (corrugatedSeedSpatial N) S := by
  intro s hs t ht he
  apply hi hs ht
  have hh := congrArg corrugatedAmbientHorizontal he
  rw [corrugatedSeedSpatial_horizontal, corrugatedSeedSpatial_horizontal] at hh
  exact mul_left_cancel₀ (neg_ne_zero.mpr Complex.I_ne_zero) hh

end
end TightVer401
