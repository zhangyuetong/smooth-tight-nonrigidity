import TightVer401.FermiSeamPerturbation
import TightVer401.FermiPerturbationBounds
import TightVer401.MomentControlBump

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry Set Metric
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

def fermiExitCutoff (ρ : ℝ) (hρ : 0 < ρ) : ℝ → ℝ := momentControlBump 0 ρ hρ

theorem fermiExitCutoff_contDiff (ρ : ℝ) (hρ : 0 < ρ) :
    ContDiff ℝ ∞ (fermiExitCutoff ρ hρ) := (momentControlBump 0 ρ hρ).contDiff

theorem fermiExitCutoff_zero (ρ : ℝ) (hρ : 0 < ρ) : fermiExitCutoff ρ hρ 0 = 1 :=
  (momentControlBump 0 ρ hρ).one_of_mem_closedBall (mem_closedBall_self (half_pos hρ).le)

theorem fermiExitCutoff_eq_one (ρ : ℝ) (hρ : 0 < ρ) {t : ℝ} (ht : |t| ≤ ρ / 2) :
    fermiExitCutoff ρ hρ t = 1 := by
  apply (momentControlBump 0 ρ hρ).one_of_mem_closedBall
  simpa [mem_closedBall, Real.dist_eq, momentControlBump] using ht

theorem fermiExitCutoff_eq_zero (ρ : ℝ) (hρ : 0 < ρ) {t : ℝ} (ht : ρ ≤ |t|) :
    fermiExitCutoff ρ hρ t = 0 := by
  apply (momentControlBump 0 ρ hρ).zero_of_le_dist
  simpa [Real.dist_eq, momentControlBump] using ht

theorem fermiSeamPerturbation_outside_collar (a κ : ℝ → ℝ) (ε ρ : ℝ)
    (hρ : 0 < ρ) {p : Coord} (hp : ρ ≤ |p 1|) :
    fermiSeamPerturbation ε a κ (fermiExitCutoff ρ hρ) p = 0 := by
  simp [fermiSeamPerturbation, fermiProduct, fermiQuadraticCutoff,
    fermiExitCutoff_eq_zero ρ hρ hp]

theorem fermiSeamPerturbation_const_mul (a κ χ : ℝ → ℝ) (ε : ℝ) :
    fermiSeamPerturbation ε a κ χ = (fun p => ε * fermiSeamPerturbation 1 a κ χ p) := by
  funext p
  simp only [fermiSeamPerturbation, fermiProduct]
  ring

theorem exists_fermiSeamPerturbation_C2_threshold {a κ : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hκ : ContDiff ℝ ∞ κ) (ρ : ℝ) (hρ : 0 < ρ)
    {K : Set Coord} (hK : IsCompact K) {η : ℝ} (hη : 0 < η) :
    ∃ e > 0, ∀ ε : ℝ, |ε| < e → ∀ p ∈ K,
      fermiCoordinateC2Size (fermiSeamPerturbation ε a κ (fermiExitCutoff ρ hρ)) p < η := by
  have hJ := fermiSeamPerturbation_contDiff ha hκ (fermiExitCutoff_contDiff ρ hρ) 1
  obtain ⟨e, he, hbound⟩ := exists_fermiPerturbation_C2_threshold hJ hK hη
  refine ⟨e, he, ?_⟩
  intro ε hε p hp
  rw [fermiSeamPerturbation_const_mul]
  exact hbound ε hε p hp

end
end TightVer401
