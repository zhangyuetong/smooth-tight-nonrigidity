import TightVer401.PeriodicPlanarSchoenflies
import TightVer401.ComplexCircleDirection
import TightVer401.CorrugatedSeedPartnerJordan

namespace TightVer401
noncomputable section
open Set Function Metric
open scoped ContDiff Topology
local instance seedFillingPositivePeriod : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

theorem corrugatedSeedBetaPhase_continuous (N : ℝ) : Continuous (corrugatedSeedPhase N) := by
  unfold corrugatedSeedPhase
  fun_prop

theorem corrugatedSeedBetaPhase_turn (N : ℕ) :
    corrugatedSeedPhase (N : ℝ) (2 * Real.pi) - corrugatedSeedPhase (N : ℝ) 0 =
      2 * Real.pi := by
  unfold corrugatedSeedPhase
  rw [mul_zero, Real.sin_zero, mul_zero, add_zero]
  have hs : Real.sin ((N : ℝ) * (2 * Real.pi)) = 0 := by
    have he : (N : ℝ) * (2 * Real.pi) = ((2 * N : ℕ) : ℝ) * Real.pi := by
      push_cast
      ring
    rw [he, Real.sin_nat_mul_pi]
  rw [hs]
  ring

theorem corrugatedSeedPartnerAngle_turn {N : ℕ} (hN : 2 ≤ N) :
    corrugatedSeedPartnerAngle (N : ℝ) (2 * Real.pi) -
      corrugatedSeedPartnerAngle (N : ℝ) 0 = 2 * Real.pi := by
  unfold corrugatedSeedPartnerAngle
  have hp := corrugatedSeedPartnerRatio_periodic hN 0
  rw [zero_add] at hp
  rw [hp]
  ring

theorem corrugatedSeedBeta_ne_zero {N : ℝ} (hN : 1 < N) (t : ℝ) :
    corrugatedSeedBeta N t ≠ 0 := by
  apply norm_pos_iff.mp
  rw [corrugatedSeedBeta_norm hN]
  exact corrugatedSeedRadius_pos hN t

theorem corrugatedSeedBeta_direction {N : ℝ} (hN : 1 < N) (t : ℝ) :
    complexCircleDirection (corrugatedSeedBeta N t) = Circle.exp (corrugatedSeedPhase N t) := by
  apply complexCircleDirection_eq_of_exp (corrugatedSeedBeta_ne_zero hN t)
  rw [corrugatedSeedBeta_norm hN, Complex.real_smul]
  unfold corrugatedSeedBeta
  have hr : corrugatedSeedRadius N t ≠ 0 := ne_of_gt (corrugatedSeedRadius_pos hN t)
  have hrc : (corrugatedSeedRadius N t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  push_cast
  field_simp [hrc]

theorem corrugatedSeedBeta_exists_origin_filling {N : ℕ} (hN : 2 ≤ N) :
    ∃ H : ℂ ≃ₜ ℂ, range (corrugatedSeedBeta (N : ℝ)) = H '' sphere (0 : ℂ) 1 ∧
      (0 : ℂ) ∈ H '' ball (0 : ℂ) 1 := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  obtain ⟨H, hH⟩ := periodicComplexCurve_exists_filling (corrugatedSeedBeta_contDiff _)
    (corrugatedSeedBeta_periodic hN) (corrugatedSeedBeta_injOn hNr)
  refine ⟨H, hH, winding_origin_inside (L := 2 * Real.pi) complexCircleDirection_continuousOn
    (corrugatedSeedBeta_contDiff _).continuous (corrugatedSeedBetaPhase_continuous _) hH
    (corrugatedSeedBeta_ne_zero hNr) ?_ (corrugatedSeedBeta_direction hNr) ?_⟩
  · simpa only [zero_add] using corrugatedSeedBeta_periodic hN 0
  · have ht := corrugatedSeedBetaPhase_turn N
    intro he
    rw [he, sub_self] at ht
    exact (ne_of_gt Real.two_pi_pos) ht.symm

theorem corrugatedSeedPartner_exists_origin_filling {N : ℕ} (hN : 10000 ≤ N) :
    ∃ H : ℂ ≃ₜ ℂ, range (corrugatedSeedPartner (N : ℝ)) = H '' sphere (0 : ℂ) 1 ∧
      (0 : ℂ) ∈ H '' ball (0 : ℂ) 1 := by
  have hNr : (10000 : ℝ) ≤ N := by exact_mod_cast hN
  have hN2 : 2 ≤ N := by omega
  have hn : ∀ t, corrugatedSeedPartner (N : ℝ) t ≠ 0 := fun t => norm_pos_iff.mp (by
    linarith [(corrugatedSeedPartner_radius_bounds hNr t).1])
  obtain ⟨H, hH⟩ := periodicComplexCurve_exists_filling (corrugatedSeedPartner_contDiff _)
    (corrugatedSeedPartner_periodic hN2) (corrugatedSeedPartner_injOn hN)
  refine ⟨H, hH, winding_origin_inside (L := 2 * Real.pi) complexCircleDirection_continuousOn
    (corrugatedSeedPartner_contDiff _).continuous
    (corrugatedSeedPartnerAngle_contDiff hNr).continuous hH hn ?_ ?_ ?_⟩
  · simpa only [zero_add] using corrugatedSeedPartner_periodic hN2 0
  · intro t
    exact complexCircleDirection_eq_of_exp (hn t) (corrugatedSeedPartnerAngle_exp hNr t)
  · have ht := corrugatedSeedPartnerAngle_turn hN2
    intro he
    rw [he, sub_self] at ht
    exact (ne_of_gt Real.two_pi_pos) ht.symm
end
end TightVer401
