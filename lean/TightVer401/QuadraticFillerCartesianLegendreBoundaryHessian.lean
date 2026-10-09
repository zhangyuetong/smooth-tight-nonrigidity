import TightVer401.QuadraticFillerCartesianLegendreBoundaryDefinitions

/-! Ambient Hessian data of the actual smooth radial continuation J. Boundary
claims never use the totalized Legendre transform outside its open target. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Actual Cartesian Hessian entries of the existing smooth radial continuation. -/
theorem quadraticFillerCartesianLegendreBoundary_hessian_entries {R M : ℝ}
    (hM : 0 < M) {p : Coord} (hp : 0 < planarRadius p) (i j : Fin 2) :
    planarHessian (quadraticFillerCartesianLegendreRadialPotential R M) p i j =
      (R - planarRadius p / M) / planarRadius p * (if i = j then 1 else 0) +
        ((-1 / M) / planarRadius p ^ 2 -
          (R - planarRadius p / M) / planarRadius p ^ 3) * p i * p j := by
  have hdom : p ∈ radialPlanarDomain univ := ⟨Real.sqrt_pos.mp hp, mem_univ _⟩
  change planarHessian (radialPlanarPotential
    (quadraticFillerCartesianLegendreRadialProfile R M)) p i j = _
  rw [radialPlanarPotential_hessian
    (quadraticFillerCartesianLegendreRadialProfile_contDiff R M).contDiffOn isOpen_univ hdom,
    quadraticFillerCartesianLegendreRadialProfile_second_deriv R M,
    quadraticFillerCartesianLegendreRadialProfile_deriv hM]

/-- Actual matrix action separates the identity and the radial rank-one part. -/
theorem quadraticFillerCartesianLegendreBoundary_hessian_action {R M : ℝ}
    (hM : 0 < M) {p : Coord} (hp : 0 < planarRadius p) (w : Coord) :
    planarHessian (quadraticFillerCartesianLegendreRadialPotential R M) p *ᵥ w =
      ((R - planarRadius p / M) / planarRadius p) • w +
        (((-1 / M) / planarRadius p ^ 2 -
          (R - planarRadius p / M) / planarRadius p ^ 3) * (p ⬝ᵥ w)) • p := by
  have hentry (i j : Fin 2) :=
    quadraticFillerCartesianLegendreBoundary_hessian_entries (R := R) hM hp i j
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hentry,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> ring

/-- Radial and tangential unit vectors are actual Hessian eigenvectors at every
positive polar radius, for the smooth radial continuation J. -/
theorem quadraticFillerCartesianLegendreBoundary_hessian_frame {R M s : ℝ}
    (hM : 0 < M) (hs : 0 < s) (theta : ℝ) :
    let u : Coord := ![Real.cos theta, Real.sin theta]
    let v : Coord := ![-Real.sin theta, Real.cos theta]
    let H := planarHessian (quadraticFillerCartesianLegendreRadialPotential R M)
      (saddlePolarChart ![s, theta])
    H *ᵥ u = (-1 / M) • u ∧ H *ᵥ v = ((R - s / M) / s) • v := by
  let u : Coord := ![Real.cos theta, Real.sin theta]
  let v : Coord := ![-Real.sin theta, Real.cos theta]
  let p : Coord := saddlePolarChart ![s, theta]
  let H := planarHessian (quadraticFillerCartesianLegendreRadialPotential R M) p
  let a := (R - s / M) / s
  let k := (-1 / M) / s ^ 2 - (R - s / M) / s ^ 3
  change H *ᵥ u = (-1 / M) • u ∧ H *ᵥ v = a • v
  have hradius : planarRadius p = s := angularDescent_radius_polar (by simpa using hs)
  have hp : 0 < planarRadius p := by rw [hradius]; exact hs
  have hpu : p = s • u := by ext i; fin_cases i <;> simp [p, u, saddlePolarChart, smul_eq_mul]
  have hdotu : p ⬝ᵥ u = s := by
    dsimp [p, u]
    simp only [saddlePolarChart, dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination s * Real.sin_sq_add_cos_sq theta
  have hdotv : p ⬝ᵥ v = 0 := by
    simp [p, v, saddlePolarChart, dotProduct, Fin.sum_univ_two]
    ring
  have hcoef : a + k * s * s = -1 / M := by
    dsimp [a, k]
    field_simp [hs.ne', hM.ne'] <;> ring
  constructor
  · have hu := quadraticFillerCartesianLegendreBoundary_hessian_action (R := R) hM hp u
    rw [hradius, hdotu] at hu
    change H *ᵥ u = a • u + (k * s) • p at hu
    calc
      H *ᵥ u = a • u + (k * s) • p := hu
      _ = (a + k * s * s) • u := by rw [hpu, smul_smul, ← add_smul]
      _ = (-1 / M) • u := by rw [hcoef]
  · have hv := quadraticFillerCartesianLegendreBoundary_hessian_action (R := R) hM hp v
    rw [hradius, hdotv] at hv
    simpa [H, a, k] using hv

/-- The actual bilinear radial/tangential Hessian data, including both mixed entries. -/
theorem quadraticFillerCartesianLegendreBoundary_hessian_frame_bilinear {R M s : ℝ}
    (hM : 0 < M) (hs : 0 < s) (theta : ℝ) :
    let u : Coord := ![Real.cos theta, Real.sin theta]
    let v : Coord := ![-Real.sin theta, Real.cos theta]
    let H := planarHessian (quadraticFillerCartesianLegendreRadialPotential R M)
      (saddlePolarChart ![s, theta])
    u ⬝ᵥ (H *ᵥ u) = -1 / M ∧ v ⬝ᵥ (H *ᵥ v) = (R - s / M) / s ∧
      u ⬝ᵥ (H *ᵥ v) = 0 ∧ v ⬝ᵥ (H *ᵥ u) = 0 := by
  let u : Coord := ![Real.cos theta, Real.sin theta]
  let v : Coord := ![-Real.sin theta, Real.cos theta]
  let H := planarHessian (quadraticFillerCartesianLegendreRadialPotential R M)
    (saddlePolarChart ![s, theta])
  change u ⬝ᵥ (H *ᵥ u) = -1 / M ∧ v ⬝ᵥ (H *ᵥ v) = (R - s / M) / s ∧
    u ⬝ᵥ (H *ᵥ v) = 0 ∧ v ⬝ᵥ (H *ᵥ u) = 0
  obtain ⟨hu, hv⟩ := quadraticFillerCartesianLegendreBoundary_hessian_frame
    (R := R) hM hs theta
  change H *ᵥ u = (-1 / M) • u at hu
  change H *ᵥ v = ((R - s / M) / s) • v at hv
  have huu : u ⬝ᵥ u = 1 := by
    simp only [u, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    nlinarith [Real.sin_sq_add_cos_sq theta]
  have hvv : v ⬝ᵥ v = 1 := by
    simp only [v, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    nlinarith [Real.sin_sq_add_cos_sq theta]
  have huv : u ⬝ᵥ v = 0 := by simp [u, v, dotProduct, Fin.sum_univ_two] <;> ring
  have hvu : v ⬝ᵥ u = 0 := by simp [u, v, dotProduct, Fin.sum_univ_two] <;> ring
  rw [hu, hv]
  simp only [dotProduct_smul, smul_eq_mul, huu, hvv, huv, hvu, mul_one, mul_zero,
    and_self]

/-- At the inner boundary MR/2 the radial and tangential eigenvalues are -1/M
and 1/M, respectively; all actual mixed frame entries vanish. -/
theorem quadraticFillerCartesianLegendreBoundary_inner_hessian_frame {R M : ℝ}
    (hR : 0 < R) (hM : 0 < M) (theta : ℝ) :
    let u : Coord := ![Real.cos theta, Real.sin theta]
    let v : Coord := ![-Real.sin theta, Real.cos theta]
    let H := planarHessian (quadraticFillerCartesianLegendreRadialPotential R M)
      (saddlePolarChart ![M * R / 2, theta])
    H *ᵥ u = (-1 / M) • u ∧ H *ᵥ v = (1 / M) • v ∧
      u ⬝ᵥ (H *ᵥ u) = -1 / M ∧ v ⬝ᵥ (H *ᵥ v) = 1 / M ∧
      u ⬝ᵥ (H *ᵥ v) = 0 ∧ v ⬝ᵥ (H *ᵥ u) = 0 := by
  have hs : 0 < M * R / 2 := by positivity
  have htan : (R - (M * R / 2) / M) / (M * R / 2) = 1 / M := by
    field_simp [hR.ne', hM.ne'] <;> ring
  obtain ⟨hu, hv⟩ := quadraticFillerCartesianLegendreBoundary_hessian_frame
    (R := R) hM hs theta
  obtain ⟨hrr, htt, hrt, htr⟩ := quadraticFillerCartesianLegendreBoundary_hessian_frame_bilinear
    (R := R) hM hs theta
  rw [htan] at hv htt
  exact ⟨hu, hv, hrr, htt, hrt, htr⟩

/-- At the outer boundary MR the actual radial eigenvalue is -1/M and the
actual tangential eigenvalue is zero: this continuation is degenerate there. -/
theorem quadraticFillerCartesianLegendreBoundary_outer_hessian_frame {R M : ℝ}
    (hR : 0 < R) (hM : 0 < M) (theta : ℝ) :
    let u : Coord := ![Real.cos theta, Real.sin theta]
    let v : Coord := ![-Real.sin theta, Real.cos theta]
    let H := planarHessian (quadraticFillerCartesianLegendreRadialPotential R M)
      (saddlePolarChart ![M * R, theta])
    H *ᵥ u = (-1 / M) • u ∧ H *ᵥ v = 0 ∧
      u ⬝ᵥ (H *ᵥ u) = -1 / M ∧ v ⬝ᵥ (H *ᵥ v) = 0 ∧
      u ⬝ᵥ (H *ᵥ v) = 0 ∧ v ⬝ᵥ (H *ᵥ u) = 0 := by
  have hs : 0 < M * R := mul_pos hM hR
  have htan : (R - (M * R) / M) / (M * R) = 0 := by
    field_simp [hR.ne', hM.ne'] <;> ring
  obtain ⟨hu, hv⟩ := quadraticFillerCartesianLegendreBoundary_hessian_frame
    (R := R) hM hs theta
  obtain ⟨hrr, htt, hrt, htr⟩ := quadraticFillerCartesianLegendreBoundary_hessian_frame_bilinear
    (R := R) hM hs theta
  rw [htan] at hv htt
  simp only [zero_smul] at hv
  exact ⟨hu, hv, hrr, htt, hrt, htr⟩

end
end TightVer401

