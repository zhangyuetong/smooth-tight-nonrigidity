import TightVer401.GnomonicMetric
import TightVer401.RadialCapInverse

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

def planarRadius (p : Coord) : ℝ := Real.sqrt (p 0 ^ 2 + p 1 ^ 2)
def polarSupportPotential (R a C : ℝ) (p : Coord) : ℝ :=
  R * planarRadius p - a * planarWeight p - C

theorem planarRadius_contDiffOn :
    ContDiffOn ℝ ∞ planarRadius {p | 0 < p 0 ^ 2 + p 1 ^ 2} := by
  apply ((contDiff_apply ℝ ℝ 0).pow 2 |>.add ((contDiff_apply ℝ ℝ 1).pow 2)).contDiffOn.sqrt
  intro p hp
  exact ne_of_gt hp

theorem planarRadius_coordPartial {p : Coord} (hp : 0 < p 0 ^ 2 + p 1 ^ 2) (i : Fin 2) :
    coordPartial i planarRadius p = p i / planarRadius p := by
  let P₀ : Coord →L[ℝ] ℝ := ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)
  let P₁ : Coord →L[ℝ] ℝ := ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2)
  have hf := ((P₀.hasFDerivAt (x := p)).pow 2).add ((P₁.hasFDerivAt (x := p)).pow 2)
  have hs := hf.sqrt (ne_of_gt hp)
  change HasFDerivAt planarRadius _ p at hs
  unfold coordPartial
  rw [hs.fderiv]
  simp only [smul_apply, add_apply, smul_eq_mul,
    show (2 : ℕ) - 1 = 1 from rfl, pow_one, nsmul_eq_mul]
  simp only [Pi.add_apply, P₀, P₁, ContinuousLinearMap.proj_apply]
  change (1 / (2 * planarRadius p)) *
    (2 * p 0 * (Pi.single i (1 : ℝ) : Coord) 0 +
      2 * p 1 * (Pi.single i (1 : ℝ) : Coord) 1) = p i / planarRadius p
  fin_cases i <;> simp <;> ring

theorem polarSupportPotential_coordPartial (R a C : ℝ) {p : Coord}
    (hp : 0 < p 0 ^ 2 + p 1 ^ 2) (i : Fin 2) :
    coordPartial i (polarSupportPotential R a C) p =
      R * p i / planarRadius p - a * p i / planarWeight p := by
  have hU : IsOpen {p : Coord | 0 < p 0 ^ 2 + p 1 ^ 2} :=
    isOpen_lt continuous_const (((continuous_apply 0).pow 2).add ((continuous_apply 1).pow 2))
  have hr : DifferentiableAt ℝ planarRadius p :=
    (planarRadius_contDiffOn.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hw : DifferentiableAt ℝ planarWeight p := gnomonicWeight_contDiff.differentiable (by simp) p
  have hR : DifferentiableAt ℝ (fun q => R * planarRadius q) p :=
    (differentiableAt_const R).mul hr
  have ha : DifferentiableAt ℝ (fun q => a * planarWeight q) p :=
    (differentiableAt_const a).mul hw
  have hd : DifferentiableAt ℝ (fun q => R * planarRadius q - a * planarWeight q) p := hR.sub ha
  change coordPartial i (fun q => R * planarRadius q - a * planarWeight q - C) p = _
  rw [coordPartial_scalar_sub hd (differentiableAt_const C),
    coordPartial_scalar_sub hR ha,
    coordPartial_scalar_mul (differentiableAt_const R) hr,
    coordPartial_scalar_mul (differentiableAt_const a) hw,
    coordPartial_scalar_const, coordPartial_scalar_const, coordPartial_scalar_const,
    planarRadius_coordPartial hp, gnomonicWeight_coordPartial]
  ring

theorem polarSupportPotential_supportMap (R a C : ℝ) {p : Coord}
    (hp : 0 < p 0 ^ 2 + p 1 ^ 2) :
    planarSupportMap (polarSupportPotential R a C) p = WithLp.toLp 2
      ![R * p 0 / planarRadius p - a * p 0 / planarWeight p,
        R * p 1 / planarRadius p - a * p 1 / planarWeight p,
        -a / planarWeight p - C] := by
  have hr : planarRadius p ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  have hw : planarWeight p ≠ 0 := (planarWeight_pos p).ne'
  have hr₂ : planarRadius p ^ 2 = p 0 ^ 2 + p 1 ^ 2 := Real.sq_sqrt hp.le
  have hw₂ : planarWeight p ^ 2 = 1 + p 0 ^ 2 + p 1 ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hthird : polarSupportPotential R a C p -
      p 0 * (R * p 0 / planarRadius p - a * p 0 / planarWeight p) -
      p 1 * (R * p 1 / planarRadius p - a * p 1 / planarWeight p) = -a / planarWeight p - C := by
    dsimp [polarSupportPotential]
    field_simp
    have hR := congrArg (fun x : ℝ => R * planarWeight p * x) hr₂
    have ha := congrArg (fun x : ℝ => a * planarRadius p * x) hw₂
    nlinarith [hR, ha]
  rw [planarSupportMap, polarSupportPotential_coordPartial R a C hp 0,
    polarSupportPotential_coordPartial R a C hp 1, hthird]

end
end TightVer401
