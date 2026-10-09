import TightVer401.IdentityBandCentralSupportCartesian
import TightVer401.IdentityBandCentralSupportCoordinates

/-! The actual Cartesian Hessian at the reconstructed central ruled seam.
The transported frame vectors come from the derivative of the actual source
coordinates; the tensor and positive directions are derived from reconstruction. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false

/-- The actual weighted Cartesian Hessian pulls back to the central mixed
tensor on arbitrary physical Gauss-frame directions. -/
theorem identityBand_central_cartesian_pairing {L : ℝ}
    (d : PeriodicRuledFrame L) (s : ℝ) {G : Coord → ℝ} {U V : Set Coord}
    {P : Coord → Coord}
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U) (hV : IsOpen V)
    (hP : ContDiffOn ℝ ∞ P V) (hPU : MapsTo P V U)
    (hrec : EqOn (planarSupportMap G ∘ P) (ruledMap d.γ d.E) V)
    (hnorm : EqOn (planarUnitNormal ∘ P) d.rawGaussMap V)
    (hp : (![s, 0] : Coord) ∈ V) {a : ℝ} (ha : 0 < a)
    (hτ : d.τ s = -a⁻¹) (v w : Coord) :
    dotProduct (fderiv ℝ P (![s, 0] : Coord) (a • v))
      ((planarHessian G (P (![s, 0] : Coord))).mulVec
        (fderiv ℝ P (![s, 0] : Coord) (a • w))) /
      planarWeight (P (![s, 0] : Coord)) =
        a * (v 0 * w 1 + v 1 * w 0) := by
  have hpull := identityBand_cartesian_pullback_pairing hG hU hV hP hPU hrec hnorm hp
    (a • v) (a • w)
  exact hpull.symm.trans (identityBand_central_differential_pairing d s ha.ne' hτ v w)

/-- In the actual transported frame vectors the weighted Cartesian Hessian
has precisely the matrix [[0,a],[a,0]]. The chart reconstruction, rather than
an assumed tensor package, identifies these vectors and entries. -/
theorem identityBand_central_cartesian_tensor {L : ℝ}
    (d : PeriodicRuledFrame L) (s : ℝ) {G : Coord → ℝ} {U V : Set Coord}
    {P : Coord → Coord}
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U) (hV : IsOpen V)
    (hP : ContDiffOn ℝ ∞ P V) (hPU : MapsTo P V U)
    (hrec : EqOn (planarSupportMap G ∘ P) (ruledMap d.γ d.E) V)
    (hnorm : EqOn (planarUnitNormal ∘ P) d.rawGaussMap V)
    (hp : (![s, 0] : Coord) ∈ V) {a : ℝ} (ha : 0 < a)
    (hτ : d.τ s = -a⁻¹) :
    let Q : Fin 2 → Coord := fun i =>
      fderiv ℝ P (![s, 0] : Coord) (a • (Pi.single i 1 : Coord))
    (fun i j => dotProduct (Q i)
      ((planarHessian G (P (![s, 0] : Coord))).mulVec (Q j)) /
        planarWeight (P (![s, 0] : Coord))) = (!![0, a; a, 0] : Matrix (Fin 2) (Fin 2) ℝ) := by
  dsimp only
  ext i j
  rw [identityBand_central_cartesian_pairing d s hG hU hV hP hPU hrec hnorm hp ha hτ]
  fin_cases i <;> fin_cases j <;> simp

/-- Every positive transverse tilt gives an actual positive Cartesian Hessian
direction at the reconstructed central point. Both its weighted value and its
unweighted strict positivity are proved. -/
theorem identityBand_central_cartesian_positive_transverse {L : ℝ}
    (d : PeriodicRuledFrame L) (s : ℝ) {G : Coord → ℝ} {U V : Set Coord}
    {P : Coord → Coord}
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U) (hV : IsOpen V)
    (hP : ContDiffOn ℝ ∞ P V) (hPU : MapsTo P V U)
    (hrec : EqOn (planarSupportMap G ∘ P) (ruledMap d.γ d.E) V)
    (hnorm : EqOn (planarUnitNormal ∘ P) d.rawGaussMap V)
    (hp : (![s, 0] : Coord) ∈ V) {a t : ℝ} (ha : 0 < a)
    (hτ : d.τ s = -a⁻¹) (ht : 0 < t) :
    let v := fderiv ℝ P (![s, 0] : Coord) (a • (![1, t] : Coord))
    let b := dotProduct v ((planarHessian G (P (![s, 0] : Coord))).mulVec v)
    b / planarWeight (P (![s, 0] : Coord)) = 2 * a * t ∧
      0 < b / planarWeight (P (![s, 0] : Coord)) ∧ 0 < b := by
  dsimp only
  have heq : dotProduct (fderiv ℝ P (![s, 0] : Coord) (a • (![1, t] : Coord)))
      ((planarHessian G (P (![s, 0] : Coord))).mulVec
        (fderiv ℝ P (![s, 0] : Coord) (a • (![1, t] : Coord)))) /
      planarWeight (P (![s, 0] : Coord)) = 2 * a * t := by
    rw [identityBand_central_cartesian_pairing d s hG hU hV hP hPU hrec hnorm hp ha hτ]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_mul, mul_one]
    ring
  have hpos : 0 < dotProduct
      (fderiv ℝ P (![s, 0] : Coord) (a • (![1, t] : Coord)))
      ((planarHessian G (P (![s, 0] : Coord))).mulVec
        (fderiv ℝ P (![s, 0] : Coord) (a • (![1, t] : Coord)))) /
      planarWeight (P (![s, 0] : Coord)) := by
    rw [heq]
    exact mul_pos (mul_pos (by norm_num) ha) ht
  refine ⟨heq, hpos, ?_⟩
  have hraw := mul_pos hpos (planarWeight_pos (P (![s, 0] : Coord)))
  rwa [div_mul_cancel₀ _ (planarWeight_pos (P (![s, 0] : Coord))).ne'] at hraw

end
end TightVer401
