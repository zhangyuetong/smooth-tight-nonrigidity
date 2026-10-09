import TightVer401.FermiMetricSupport
import TightVer401.FermiScaleCalculus

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry Set Filter
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

def fermiSupportL (κ : ℝ → ℝ) (H : Coord → ℝ) (p : Coord) : ℝ :=
  coordPartial 0 (coordPartial 0 H) p -
    coordPartial 0 (fermiNormalScale κ) p / fermiNormalScale κ p * coordPartial 0 H p +
    fermiNormalScale κ p * coordPartial 1 (fermiNormalScale κ) p * coordPartial 1 H p +
    H p * (fermiNormalScale κ p)^2

def fermiSupportM (κ : ℝ → ℝ) (H : Coord → ℝ) (p : Coord) : ℝ :=
  coordPartial 0 (coordPartial 1 H) p -
    coordPartial 1 (fermiNormalScale κ) p / fermiNormalScale κ p * coordPartial 0 H p

def fermiSupportN (H : Coord → ℝ) (p : Coord) : ℝ :=
  coordPartial 1 (coordPartial 1 H) p + H p

theorem fermiCoordinatePartial_contDiff {H : Coord → ℝ} (hH : ContDiff ℝ ∞ H)
    (i : Fin 2) : ContDiff ℝ ∞ (coordPartial i H) :=
  contDiffOn_univ.mp (partial_contDiffOn hH.contDiffOn isOpen_univ i)

theorem fermiSupport_actual_entries {κ : ℝ → ℝ} (hκ : ContDiff ℝ ∞ κ)
    (H : Coord → ℝ) {p : Coord} (hp : fermiNormalScale κ p ≠ 0) :
    sphereSupportTensor (fermiMetric (fermiNormalScale κ)) H p 0 0 = fermiSupportL κ H p ∧
    sphereSupportTensor (fermiMetric (fermiNormalScale κ)) H p 0 1 = fermiSupportM κ H p ∧
    sphereSupportTensor (fermiMetric (fermiNormalScale κ)) H p 1 1 = fermiSupportN H p :=
  fermiMetric_support_entries ((fermiNormalScale_contDiff hκ).differentiable (by simp) p) hp

theorem fermiSupport_seam_values {κ : ℝ → ℝ} (hκ : ContDiff ℝ ∞ κ)
    (H : Coord → ℝ) (r : ℝ) :
    fermiSupportL κ H ![r,0] = coordPartial 0 (coordPartial 0 H) ![r,0] +
      κ r * coordPartial 1 H ![r,0] + H ![r,0] ∧
    fermiSupportM κ H ![r,0] = coordPartial 0 (coordPartial 1 H) ![r,0] -
      κ r * coordPartial 0 H ![r,0] := by
  have hs := fermiNormalScale_seam hκ r
  simp [fermiSupportL, fermiSupportM, hs.1, hs.2.1, hs.2.2.1]

theorem fermiSupport_transverse_seam {κ : ℝ → ℝ} {H : Coord → ℝ}
    (hκ : ContDiff ℝ ∞ κ) (hH : ContDiff ℝ ∞ H) (r : ℝ) :
    coordPartial 1 (fermiSupportL κ H) ![r,0] =
      coordPartial 1 (coordPartial 0 (coordPartial 0 H)) ![r,0] -
        deriv κ r * coordPartial 0 H ![r,0] +
        (κ r)^2 * coordPartial 1 H ![r,0] +
        κ r * coordPartial 1 (coordPartial 1 H) ![r,0] + 2 * κ r * H ![r,0] := by
  let p : Coord := ![r,0]
  let h := fermiNormalScale κ
  have sh : ContDiff ℝ ∞ h := fermiNormalScale_contDiff hκ
  have sp (i : Fin 2) := fermiCoordinatePartial_contDiff sh i
  have sH (i : Fin 2) := fermiCoordinatePartial_contDiff hH i
  have sHH := fermiCoordinatePartial_contDiff (sH 0) 0
  have dh := sh.differentiable (by simp) p
  have dp (i : Fin 2) := (sp i).differentiable (by simp) p
  have dH := hH.differentiable (by simp) p
  have dHi (i : Fin 2) := (sH i).differentiable (by simp) p
  have hs := fermiNormalScale_seam hκ r
  have hn : h p ≠ 0 := by change fermiNormalScale κ ![r,0] ≠ 0; rw [hs.1]; norm_num
  have h10 : coordPartial 1 (coordPartial 0 h) p = deriv κ r := by
    rw [coordPartial_comm sh.contDiffOn isOpen_univ (mem_univ p) 1 0]
    exact hs.2.2.2.2
  have dq : DifferentiableAt ℝ (fun q => coordPartial 0 h q / h q) p :=
    scalar_coord_div_differentiableAt (dp 0) dh hn
  have dqv : coordPartial 1 (fun q => coordPartial 0 h q / h q) p = deriv κ r := by
    rw [coordPartial_scalar_div (dp 0) dh hn]
    simp [h, p, hs.1, hs.2.1, hs.2.2.1, h10]
  have dprod : DifferentiableAt ℝ (fun q => h q * coordPartial 1 h q) p := dh.mul (dp 1)
  have dprodv : coordPartial 1 (fun q => h q * coordPartial 1 h q) p = (κ r)^2 - 1 := by
    rw [coordPartial_scalar_mul dh (dp 1)]
    simp only [h, p, hs.1, hs.2.2.1, hs.2.2.2.1, one_mul]
    ring
  have dsq : DifferentiableAt ℝ (fun q => h q ^ 2) p := dh.pow 2
  have dsqv : coordPartial 1 (fun q => h q ^ 2) p = 2 * κ r := by
    have he : (fun q => h q ^ 2) = (fun q => h q * h q) := by funext q; ring
    rw [he, coordPartial_scalar_mul dh dh]
    simp [h, p, hs.1, hs.2.2.1]
    ring
  change coordPartial 1 (fun q =>
    (coordPartial 0 (coordPartial 0 H) q - (coordPartial 0 h q / h q) * coordPartial 0 H q) +
      (h q * coordPartial 1 h q) * coordPartial 1 H q + H q * h q ^ 2) p = _
  rw [coordPartial_scalar_add
    (f := fun q => coordPartial 0 (coordPartial 0 H) q -
      (coordPartial 0 h q / h q) * coordPartial 0 H q +
      (h q * coordPartial 1 h q) * coordPartial 1 H q)
    (g := fun q => H q * h q ^ 2)
    (((sHH.differentiable (by simp) p).sub (dq.mul (dHi 0))).add (dprod.mul (dHi 1)))
      (dH.mul dsq),
    coordPartial_scalar_add
      (f := fun q => coordPartial 0 (coordPartial 0 H) q -
        (coordPartial 0 h q / h q) * coordPartial 0 H q)
      (g := fun q => (h q * coordPartial 1 h q) * coordPartial 1 H q)
      ((sHH.differentiable (by simp) p).sub (dq.mul (dHi 0)))
      (dprod.mul (dHi 1)),
    coordPartial_scalar_sub (f := fun q => coordPartial 0 (coordPartial 0 H) q)
      (g := fun q => (coordPartial 0 h q / h q) * coordPartial 0 H q)
      (sHH.differentiable (by simp) p) (dq.mul (dHi 0)),
    coordPartial_scalar_mul (f := fun q => coordPartial 0 h q / h q)
      (g := fun q => coordPartial 0 H q) dq (dHi 0),
    coordPartial_scalar_mul (f := fun q => h q * coordPartial 1 h q)
      (g := fun q => coordPartial 1 H q) dprod (dHi 1),
    coordPartial_scalar_mul (f := fun q => H q) (g := fun q => h q ^ 2) dH dsq,
    dqv, dprodv, dsqv]
  simp only [h, p, hs.1, hs.2.1, hs.2.2.1, zero_div, zero_mul, one_mul, one_pow]
  ring

theorem fermiSupport_tangent_seam {κ : ℝ → ℝ} {H : Coord → ℝ}
    (hκ : ContDiff ℝ ∞ κ) (hH : ContDiff ℝ ∞ H) (r : ℝ) :
    coordPartial 0 (fermiSupportM κ H) ![r,0] =
      coordPartial 0 (coordPartial 0 (coordPartial 1 H)) ![r,0] -
        deriv κ r * coordPartial 0 H ![r,0] -
        κ r * coordPartial 0 (coordPartial 0 H) ![r,0] := by
  let p : Coord := ![r,0]
  let h := fermiNormalScale κ
  have sh : ContDiff ℝ ∞ h := fermiNormalScale_contDiff hκ
  have dh := sh.differentiable (by simp) p
  have dht := (fermiCoordinatePartial_contDiff sh 1).differentiable (by simp) p
  have dHr := (fermiCoordinatePartial_contDiff hH 0).differentiable (by simp) p
  have dHrt := (fermiCoordinatePartial_contDiff (fermiCoordinatePartial_contDiff hH 1) 0).differentiable (by simp) p
  have hs := fermiNormalScale_seam hκ r
  have hn : h p ≠ 0 := by change fermiNormalScale κ ![r,0] ≠ 0; rw [hs.1]; norm_num
  have dq := scalar_coord_div_differentiableAt dht dh hn
  have dqv : coordPartial 0 (fun q => coordPartial 1 h q / h q) p = deriv κ r := by
    rw [coordPartial_scalar_div dht dh hn]
    simp [h, p, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.2]
  change coordPartial 0 (fun q => coordPartial 0 (coordPartial 1 H) q -
    (coordPartial 1 h q / h q) * coordPartial 0 H q) p = _
  rw [coordPartial_scalar_sub (f := fun q => coordPartial 0 (coordPartial 1 H) q)
    (g := fun q => (coordPartial 1 h q / h q) * coordPartial 0 H q) dHrt (dq.mul dHr),
    coordPartial_scalar_mul (f := fun q => coordPartial 1 h q / h q)
      (g := fun q => coordPartial 0 H q) dq dHr, dqv]
  simp only [h, p, hs.1, hs.2.2.1, div_one]
  ring

theorem fermiSupport_seam_codazzi {κ : ℝ → ℝ} {H : Coord → ℝ}
    (hκ : ContDiff ℝ ∞ κ) (hH : ContDiff ℝ ∞ H) (r : ℝ) :
    coordPartial 1 (fermiSupportL κ H) ![r,0] =
      coordPartial 0 (fermiSupportM κ H) ![r,0] +
        κ r * fermiSupportN H ![r,0] + κ r * fermiSupportL κ H ![r,0] := by
  have hm : coordPartial 1 (coordPartial 0 H) = coordPartial 0 (coordPartial 1 H) :=
    funext fun p => coordPartial_comm hH.contDiffOn isOpen_univ (mem_univ p) 1 0
  have ht := coordPartial_comm (fermiCoordinatePartial_contDiff hH 0).contDiffOn
    isOpen_univ (mem_univ (![r,0] : Coord)) 1 0
  rw [hm] at ht
  rw [fermiSupport_transverse_seam hκ hH, fermiSupport_tangent_seam hκ hH,
    (fermiSupport_seam_values hκ H r).1, ht]
  simp only [fermiSupportN]
  ring

end
end TightVer401
