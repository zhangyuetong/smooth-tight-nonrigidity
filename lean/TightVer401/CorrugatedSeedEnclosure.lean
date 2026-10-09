import TightVer401.CorrugatedSeedFilling
import TightVer401.HomeomorphicJordanInside

namespace TightVer401
noncomputable section
open Set

theorem corrugatedSeed_origin_inside {N : ℕ} (hN : 10000 ≤ N) :
    (0 : Schoenflies.Plane) ∈ Schoenflies.inside
      (range (jordanComplexCoordinates.symm ∘ corrugatedSeedBeta (N : ℝ))) ∧
    (0 : Schoenflies.Plane) ∈ Schoenflies.inside
      (range (jordanComplexCoordinates.symm ∘ corrugatedSeedPartner (N : ℝ))) := by
  obtain ⟨Hβ, hβ, hβ0⟩ := corrugatedSeedBeta_exists_origin_filling (show 2 ≤ N by omega)
  obtain ⟨Hδ, hδ, hδ0⟩ := corrugatedSeedPartner_exists_origin_filling hN
  constructor
  · simpa only [map_zero] using homeomorphic_filling_mem_inside hβ hβ0
  · simpa only [map_zero] using homeomorphic_filling_mem_inside hδ hδ0

/-- An actual continuous argument lift with one positive turn. -/
def HasPositiveArgumentTurn (f : ℝ → ℂ) (L : ℝ) : Prop :=
  ∃ φ : ℝ → ℝ, Continuous φ ∧
    (∀ t, complexCircleDirection (f t) = Circle.exp (φ t)) ∧
    φ L - φ 0 = 2 * Real.pi

theorem corrugatedSeed_positive_argument_turns {N : ℕ} (hN : 10000 ≤ N) :
    HasPositiveArgumentTurn (corrugatedSeedBeta (N : ℝ)) (2 * Real.pi) ∧
    HasPositiveArgumentTurn (corrugatedSeedPartner (N : ℝ)) (2 * Real.pi) := by
  have hNr : (10000 : ℝ) ≤ N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) < N := by linarith
  constructor
  · exact ⟨corrugatedSeedPhase (N : ℝ), corrugatedSeedBetaPhase_continuous _,
      corrugatedSeedBeta_direction hN1, corrugatedSeedBetaPhase_turn N⟩
  · refine ⟨corrugatedSeedPartnerAngle (N : ℝ),
      (corrugatedSeedPartnerAngle_contDiff hNr).continuous, ?_,
      corrugatedSeedPartnerAngle_turn (show 2 ≤ N by omega)⟩
    intro t
    have hn : corrugatedSeedPartner (N : ℝ) t ≠ 0 := norm_pos_iff.mp (by
      linarith [(corrugatedSeedPartner_radius_bounds hNr t).1])
    exact complexCircleDirection_eq_of_exp hn (corrugatedSeedPartnerAngle_exp hNr t)
end
end TightVer401
