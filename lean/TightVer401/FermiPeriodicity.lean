import TightVer401.FermiSeamPerturbation

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

def FermiPeriodic (L : ℝ) (H : Coord → ℝ) : Prop :=
  ∀ p, H (p + Pi.single 0 L) = H p

theorem fermiPeriodic_coordPartial {L : ℝ} {H : Coord → ℝ} (hp : FermiPeriodic L H)
    (i : Fin 2) : FermiPeriodic L (coordPartial i H) := by
  have he : (fun p => H (p + Pi.single 0 L)) = H := funext hp
  intro p
  unfold coordPartial
  have hd := fderiv_comp_add_right (𝕜 := ℝ) (f := H) (x := p) (Pi.single 0 L)
  rw [he] at hd
  exact congrArg (fun D : Coord →L[ℝ] ℝ => D (Pi.single i 1)) hd.symm

theorem fermiPeriodic_iff_slices (L : ℝ) (H : Coord → ℝ) :
    FermiPeriodic L H ↔ ∀ t, Function.Periodic (fun r => H ![r,t]) L := by
  have hs (r t : ℝ) : (![r,t] : Coord) + Pi.single 0 L = ![r+L,t] := by
    ext i
    fin_cases i <;> simp
  constructor
  · intro hp t r
    simpa only [hs] using hp (![r,t] : Coord)
  · intro hp p
    have he : p = ![p 0,p 1] := by ext i; fin_cases i <;> simp
    rw [he, hs]
    exact hp (p 1) (p 0)

theorem fermiNormalScale_periodic {L : ℝ} {κ : ℝ → ℝ} (hκ : Function.Periodic κ L) :
    FermiPeriodic L (fermiNormalScale κ) := by
  intro p
  simp [fermiNormalScale, hκ (p 0)]

theorem fermiSupport_periodic {L : ℝ} {κ : ℝ → ℝ} {H : Coord → ℝ}
    (hκ : Function.Periodic κ L) (hH : FermiPeriodic L H) :
    FermiPeriodic L (fermiSupportL κ H) ∧ FermiPeriodic L (fermiSupportM κ H) ∧
      FermiPeriodic L (fermiSupportN H) := by
  have hh := fermiNormalScale_periodic hκ
  have hh0 := fermiPeriodic_coordPartial hh 0
  have hh1 := fermiPeriodic_coordPartial hh 1
  have hH0 := fermiPeriodic_coordPartial hH 0
  have hH1 := fermiPeriodic_coordPartial hH 1
  have hH00 := fermiPeriodic_coordPartial hH0 0
  have hH01 := fermiPeriodic_coordPartial hH1 0
  have hH11 := fermiPeriodic_coordPartial hH1 1
  constructor
  · intro p
    simp only [fermiSupportL, hh p, hh0 p, hh1 p, hH p, hH0 p, hH1 p, hH00 p]
  · constructor
    · intro p
      simp only [fermiSupportM, hh p, hh1 p, hH0 p, hH01 p]
    · intro p
      simp only [fermiSupportN, hH p, hH11 p]

theorem fermiSeamPerturbation_periodic {L : ℝ} {a κ χ : ℝ → ℝ}
    (ha : Function.Periodic a L) (hκ : Function.Periodic κ L) (ε : ℝ) :
    FermiPeriodic L (fermiSeamPerturbation ε a κ χ) := by
  intro p
  simp [fermiSeamPerturbation, fermiProduct, fermiQuadraticCutoff, ha (p 0), hκ (p 0)]

end
end TightVer401
