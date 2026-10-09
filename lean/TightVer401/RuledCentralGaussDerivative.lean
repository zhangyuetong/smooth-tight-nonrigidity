import TightVer401.ThinBandRuledGauss
import Mathlib.Analysis.Calculus.Deriv.Pi

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

theorem ruledNormal_zero (T n : Ambient) (k τ : ℝ) : ruledNormal T n k τ 0 = n := by
  simp [ruledNormal, ruledEnergy]

theorem ruledNormal_hasDerivAt_zero (T n : Ambient) (k τ : ℝ) :
    HasDerivAt (ruledNormal T n k τ) (-τ • T) 0 := by
  have henergy : HasDerivAt (ruledEnergy k τ) (-2 * k) 0 := by
    have h := (((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub
      ((hasDerivAt_id (0 : ℝ)).const_mul k)).pow 2).add
      (((hasDerivAt_id (0 : ℝ)).const_mul τ).pow 2)
    convert! h using 1
    · funext u
      change (1 - k * u)^2 + τ^2 * u^2 = (1 - k * u)^2 + (τ * u)^2
      ring
    · norm_num
  have hroot : HasDerivAt (fun u => Real.sqrt (ruledEnergy k τ u)) (-k) 0 := by
    convert! henergy.sqrt (by simp [ruledEnergy]) using 1
    simp [ruledEnergy]
    ring
  have ha : HasDerivAt (fun u => -τ * u / Real.sqrt (ruledEnergy k τ u)) (-τ) 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).const_mul (-τ)).div hroot
      (by simp [ruledEnergy]) using 1 <;> simp [ruledEnergy]
  have hb : HasDerivAt (fun u => (1 - k * u) / Real.sqrt (ruledEnergy k τ u)) 0 0 := by
    convert! ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub
      ((hasDerivAt_id (0 : ℝ)).const_mul k)).div hroot
      (by simp [ruledEnergy]) using 1 <;> simp [ruledEnergy]
  have h := (ha.smul (hasDerivAt_const (0 : ℝ) T)).add
    (hb.smul (hasDerivAt_const (0 : ℝ) n))
  have hf : (((fun u => -τ * u / Real.sqrt (ruledEnergy k τ u)) • fun _ => T) +
      (fun u => (1 - k * u) / Real.sqrt (ruledEnergy k τ u)) • fun _ => n) = ruledNormal T n k τ := rfl
  rw [hf] at h
  simpa only [smul_zero, zero_smul, add_zero, zero_add] using h

theorem periodicRuledFrame_rawGaussMap_central_partial_s {L : ℝ}
    (d : PeriodicRuledFrame L) (r : ℝ) :
    coordPartial 0 d.rawGaussMap (![r, 0] : Coord) = -d.τ r • d.E r := by
  have hpath : HasDerivAt (fun s => (![s, 0] : Coord)) (Pi.single 0 (1 : ℝ) : Coord) r := by
    have he : (fun s => (![s, 0] : Coord)) = Function.update (![0, 0] : Coord) 0 := by
      funext s i
      fin_cases i <;> simp
    rw [he]
    exact hasDerivAt_update _ _ _
  have hs := ((periodicRuledFrame_rawGaussMap_contDiff d).differentiable (by simp)
    (![r, 0] : Coord)).hasFDerivAt.comp_hasDerivAt r hpath
  have he : (fun s => d.rawGaussMap (![s, 0] : Coord)) = d.n := by
    funext s
    exact ruledNormal_zero (d.T s) (d.n s) (d.k s) (d.τ s)
  change HasDerivAt (fun s => d.rawGaussMap (![s, 0] : Coord))
    (coordPartial 0 d.rawGaussMap (![r, 0] : Coord)) r at hs
  rw [he] at hs
  exact hs.unique (d.deriv_n r)

theorem periodicRuledFrame_rawGaussMap_central_partial_u {L : ℝ}
    (d : PeriodicRuledFrame L) (r : ℝ) :
    coordPartial 1 d.rawGaussMap (![r, 0] : Coord) = -d.τ r • d.T r := by
  have hpath : HasDerivAt (fun u => (![r, u] : Coord)) (Pi.single 1 (1 : ℝ) : Coord) 0 := by
    have he : (fun u => (![r, u] : Coord)) = Function.update (![r, 0] : Coord) 1 := by
      funext u i
      fin_cases i <;> simp
    rw [he]
    exact hasDerivAt_update _ _ _
  have hs := ((periodicRuledFrame_rawGaussMap_contDiff d).differentiable (by simp)
    (![r, 0] : Coord)).hasFDerivAt.comp_hasDerivAt 0 hpath
  change HasDerivAt (fun u => ruledNormal (d.T r) (d.n r) (d.k r) (d.τ r) u)
    (coordPartial 1 d.rawGaussMap (![r, 0] : Coord)) 0 at hs
  exact hs.unique (ruledNormal_hasDerivAt_zero (d.T r) (d.n r) (d.k r) (d.τ r))

theorem periodicRuledFrame_ruledMap_central_partials {L : ℝ}
    (d : PeriodicRuledFrame L) (r : ℝ) :
    coordPartial 0 (ruledMap d.γ d.E) (![r, 0] : Coord) = d.T r ∧
      coordPartial 1 (ruledMap d.γ d.E) (![r, 0] : Coord) = d.E r := by
  constructor
  · simpa using ruled_partial_s (p := (![r, 0] : Coord)) (d.deriv_γ r) (d.deriv_E r)
  · exact ruled_partial_u (p := (![r, 0] : Coord)) (d.deriv_γ r) (d.deriv_E r)

end
end TightVer401
