import TightVer401.QuadraticFillerCartesianGradientAnnulusSmooth
import TightVer401.DualRadialQuadraticGerm
import TightVer401.DualRadialNeckGeometry

/-! Actual end gradients derived from literal scalar equality on open regions.
No derivative formula, sign or continued inverse is supplied as a premise.
-/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

theorem dualRadialCompletionEndGradients_inner_gradient
    {G : Coord → ℝ} {RN mu d0 epsilon0 : ℝ}
    (hInner : EqOn G (fun p => RN * planarRadius p - mu * planarRadius p ^ 2 / 2 + d0)
      {p | 0 < planarRadius p ∧ planarRadius p < epsilon0})
    {p : Coord} (hp : 0 < planarRadius p) (hpInner : planarRadius p < epsilon0) :
    planarGradient G p = ((RN - mu * planarRadius p) / planarRadius p) • p := by
  let f : ℝ → ℝ := fun r => RN * r - mu * r ^ 2 / 2 + d0
  have hfeq : f = fun r => dualRadialQuadraticProfile 0 mu d0 r + RN * r := by
    funext r
    dsimp only [f, dualRadialQuadraticProfile]
    ring
  have hf : ContDiff ℝ ∞ f := by
    rw [hfeq]
    exact (dualRadialQuadraticProfile_contDiff 0 mu d0).add
      (contDiff_const.mul contDiff_id)
  have hfd : deriv f (planarRadius p) = RN - mu * planarRadius p := by
    calc
      deriv f (planarRadius p) = mu * 0 - mu * planarRadius p + RN * 1 := by
        rw [hfeq]
        exact ((dualRadialQuadraticProfile_hasDerivAt 0 mu d0 (planarRadius p)).add
          ((hasDerivAt_id (planarRadius p)).const_mul RN)).deriv
      _ = RN - mu * planarRadius p := by ring
  have hOpen : IsOpen {q : Coord | 0 < planarRadius q ∧ planarRadius q < epsilon0} :=
    (isOpen_lt continuous_const quadraticFillerCartesianGradient_radius_continuous).inter
      (isOpen_lt quadraticFillerCartesianGradient_radius_continuous continuous_const)
  have he : G =ᶠ[𝓝 p] radialPlanarPotential f := by
    filter_upwards [hOpen.mem_nhds ⟨hp, hpInner⟩] with q hq
    exact hInner hq
  have hpdom : p ∈ radialPlanarDomain univ := ⟨Real.sqrt_pos.mp hp, mem_univ _⟩
  ext i
  change fderiv ℝ G p (Pi.single i 1) = ((RN - mu * planarRadius p) / planarRadius p) * p i
  rw [he.fderiv_eq]
  change coordPartial i (radialPlanarPotential f) p = _
  rw [radialPlanarPotential_coordPartial hf.contDiffOn isOpen_univ hpdom, hfd]
  ring

theorem dualRadialCompletionEndGradients_outer_gradient
    {G : Coord → ℝ} {A B dInfinity L0 : ℝ}
    (hOuter : EqOn G (fun p => A * planarRadius p - B / planarRadius p + dInfinity)
      {p | L0 < planarRadius p})
    {p : Coord} (hp : 0 < planarRadius p) (hpOuter : L0 < planarRadius p) :
    planarGradient G p = ((A + B / planarRadius p ^ 2) / planarRadius p) • p := by
  let f := dualRadialNeckLegendreGerm A B (-dInfinity)
  have hOpen : IsOpen {q : Coord | L0 < planarRadius q} :=
    isOpen_lt continuous_const quadraticFillerCartesianGradient_radius_continuous
  have he : G =ᶠ[𝓝 p] radialPlanarPotential f := by
    filter_upwards [hOpen.mem_nhds hpOuter] with q hq
    simpa only [f, radialPlanarPotential, dualRadialNeckLegendreGerm, sub_neg_eq_add] using hOuter hq
  have hpdom : p ∈ radialPlanarDomain (Ioi 0) := ⟨Real.sqrt_pos.mp hp, hp⟩
  ext i
  change fderiv ℝ G p (Pi.single i 1) = ((A + B / planarRadius p ^ 2) / planarRadius p) * p i
  rw [he.fderiv_eq]
  change coordPartial i (radialPlanarPotential f) p = _
  rw [radialPlanarPotential_coordPartial (dualRadialNeckLegendreGerm_contDiffOn A B (-dInfinity))
    isOpen_Ioi hpdom, dualRadialNeckLegendreGerm_deriv A B (-dInfinity) hp]
  ring

theorem dualRadialCompletionEndGradients_inner_circle
    {G : Coord → ℝ} {RN mu d0 epsilon0 epsilon : ℝ}
    (hInner : EqOn G (fun p => RN * planarRadius p - mu * planarRadius p ^ 2 / 2 + d0)
      {p | 0 < planarRadius p ∧ planarRadius p < epsilon0})
    (hepsilon : 0 < epsilon) (hepsilon0 : epsilon < epsilon0) (theta : ℝ) :
    planarGradient G (saddlePolarChart ![epsilon, theta]) =
      (RN - mu * epsilon) • ![Real.cos theta, Real.sin theta] := by
  have hradius : planarRadius (saddlePolarChart ![epsilon, theta]) = epsilon := by
    simpa using angularDescent_radius_polar
      (show (0 : ℝ) < (![epsilon, theta] : Coord) 0 from hepsilon)
  have hg := dualRadialCompletionEndGradients_inner_gradient hInner
    (p := saddlePolarChart ![epsilon, theta])
    (by simpa only [hradius] using hepsilon) (by simpa only [hradius] using hepsilon0)
  rw [hg, hradius]
  ext i
  fin_cases i
  · change ((RN - mu * epsilon) / epsilon) * (epsilon * Real.cos theta) =
      (RN - mu * epsilon) * Real.cos theta
    field_simp [hepsilon.ne']
  · change ((RN - mu * epsilon) / epsilon) * (epsilon * Real.sin theta) =
      (RN - mu * epsilon) * Real.sin theta
    field_simp [hepsilon.ne']

theorem dualRadialCompletionEndGradients_outer_circle
    {G : Coord → ℝ} {A B dInfinity L0 L : ℝ}
    (hOuter : EqOn G (fun p => A * planarRadius p - B / planarRadius p + dInfinity)
      {p | L0 < planarRadius p})
    (hL : 0 < L) (hL0 : L0 < L) (theta : ℝ) :
    planarGradient G (saddlePolarChart ![L, theta]) =
      (A + B / L ^ 2) • ![Real.cos theta, Real.sin theta] := by
  have hradius : planarRadius (saddlePolarChart ![L, theta]) = L := by
    simpa using angularDescent_radius_polar
      (show (0 : ℝ) < (![L, theta] : Coord) 0 from hL)
  have hg := dualRadialCompletionEndGradients_outer_gradient hOuter
    (p := saddlePolarChart ![L, theta])
    (by simpa only [hradius] using hL) (by simpa only [hradius] using hL0)
  rw [hg, hradius]
  ext i
  fin_cases i
  · change ((A + B / L ^ 2) / L) * (L * Real.cos theta) =
      (A + B / L ^ 2) * Real.cos theta
    field_simp [hL.ne']
  · change ((A + B / L ^ 2) / L) * (L * Real.sin theta) =
      (A + B / L ^ 2) * Real.sin theta
    field_simp [hL.ne']

end
end TightVer401
