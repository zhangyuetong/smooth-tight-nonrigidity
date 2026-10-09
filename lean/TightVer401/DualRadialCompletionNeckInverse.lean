import TightVer401.DualRadialNeckGradientEscape
import TightVer401.QuadraticFillerCartesianGradientAnnulusSmooth
import TightVer401.QuadraticFillerCartesianGradientAnnulusAlgebra
import TightVer401.SeamNormalCoordinates
import TightVer401.AngularDescentCharts
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue

/-! The actual radial neck paste inherits a global exterior gradient inverse
from the actual filling inverse and its retained quadratic collar. -/
namespace TightVer401
noncomputable section
open Set Filter Function Metric OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

private theorem neck_gradient_eq_on {F H : Coord → ℝ} {U : Set Coord}
    (hU : IsOpen U) (hEq : EqOn F H U) {x : Coord} (hx : x ∈ U) :
    planarGradient F x = planarGradient H x := by
  have he : F =ᶠ[𝓝 x] H := by
    filter_upwards [hU.mem_nhds hx] with p hp
    exact hEq hp
  ext i
  change fderiv ℝ F x (Pi.single i 1) = fderiv ℝ H x (Pi.single i 1)
  rw [he.fderiv_eq]

private theorem neck_radial_gradient {g : ℝ → ℝ} {a b : ℝ}
    (hg : ContDiffOn ℝ ∞ g (Ioo a b)) {x : Coord}
    (hx0 : 0 < planarRadius x) (hx : planarRadius x ∈ Ioo a b) :
    planarGradient (radialPlanarPotential g) x =
      (deriv g (planarRadius x) / planarRadius x) • x := by
  have hD : x ∈ radialPlanarDomain (Ioo a b) := ⟨Real.sqrt_pos.mp hx0, hx⟩
  ext i
  change coordPartial i (radialPlanarPotential g) x =
    (deriv g (planarRadius x) / planarRadius x) * x i
  rw [radialPlanarPotential_coordPartial hg isOpen_Ioo hD]
  ring

private theorem neck_complex_coord (p : Coord) : seamComplexCoord (angularDescentComplex p) = p := by
  ext i
  fin_cases i <;> simp [seamComplexCoord_apply, angularDescentComplex]

private theorem neck_coord_complex (z : ℂ) : angularDescentComplex (seamComplexCoord z) = z := by
  apply Complex.ext <;> simp [seamComplexCoord_apply,angularDescentComplex]

private theorem neck_exterior_iff (Gamma : ℂ ≃ₜ ℂ) (y : Coord) :
    y ∈ seamComplexCoord '' (univ \ Gamma '' closedBall (0 : ℂ) 1) ↔
      angularDescentComplex y ∉ Gamma '' closedBall (0 : ℂ) 1 := by
  constructor
  · rintro ⟨z, ⟨_, hz⟩, rfl⟩
    rwa [neck_coord_complex]
  · intro hy
    exact ⟨angularDescentComplex y, ⟨mem_univ _, hy⟩, neck_complex_coord y⟩

private theorem neck_filling_target_iff (Gamma : ℂ ≃ₜ ℂ) (Q : ℝ) (y : Coord) :
    y ∈ seamComplexCoord '' (ball (0 : ℂ) Q \ Gamma '' closedBall (0 : ℂ) 1) ↔
      planarRadius y < Q ∧ angularDescentComplex y ∉ Gamma '' closedBall (0 : ℂ) 1 := by
  constructor
  · rintro ⟨z, ⟨hz, hnot⟩, rfl⟩
    rw [neck_coord_complex]
    constructor
    · rw [← angularDescentComplex_norm, neck_coord_complex]
      simpa only [mem_ball, dist_zero_right] using hz
    · exact hnot
  · rintro ⟨hr, hn⟩
    refine ⟨angularDescentComplex y, ⟨?_, hn⟩, neck_complex_coord y⟩
    simpa only [mem_ball, dist_zero_right, angularDescentComplex_norm] using hr

private theorem neck_slope_preimage {g : ℝ → ℝ} {a b t s : ℝ}
    (hcont : ContinuousOn (deriv g) (Ioo a b)) (ht : t ∈ Ioo a b)
    (hEscape : Tendsto (deriv g) (𝓝[>] a) atTop) (hs : deriv g t < s) :
    ∃ r ∈ Ioo a t, deriv g r = s := by
  have hhigh : ∀ᶠ r in 𝓝[>] a, s < deriv g r :=
    hEscape.eventually (eventually_gt_atTop s)
  obtain ⟨q, hqhigh, hq⟩ := (hhigh.and (Ioo_mem_nhdsGT ht.1)).exists
  have hI : Icc q t ⊆ Ioo a b := by
    intro r hr
    exact ⟨hq.1.trans_le hr.1, hr.2.trans_lt ht.2⟩
  obtain ⟨r, hr, he⟩ := intermediate_value_Icc' hq.2.le (hcont.mono hI) ⟨hs.le, hqhigh.le⟩
  refine ⟨r, ⟨hq.1.trans_le hr.1, ?_⟩, he⟩
  by_contra hrt
  have heq : r = t := le_antisymm hr.2 (le_of_not_gt hrt)
  rw [heq] at he
  exact (ne_of_lt hs) he

/-- The actual pasted neck gradient is bijective onto the entire exterior
of the same filling disk. Strictly decreasing actual scalar slope and the
retained quadratic collar separate the neck and old-filling branches. -/
theorem dualRadialCompletionNeck_gradient_bijOn
    {R M a d b S : ℝ} (hR : 0 < R) (hM : 0 < M) (ha : 0 < a)
    (had : a < d) (hdb : d < b) (hbR : b < R/2) (hRS : R/2 < S)
    {g : ℝ → ℝ} (hg : ContDiffOn ℝ ∞ g (Ioo a b))
    (hgpos : ∀ r ∈ Ioo a b, 0 < deriv g r)
    (hgneg : ∀ r ∈ Ioo a b, deriv (deriv g) r < 0)
    (hEscape : Tendsto (deriv g) (𝓝[>] a) atTop)
    (hgQuad : EqOn g (dualRadialQuadraticProfile R M (-M*R^2/2)) (Ioo d b))
    {F H : Coord → ℝ}
    (hFNeck : EqOn F (radialPlanarPotential g) {x | a < planarRadius x ∧ planarRadius x < b})
    (hFOld : EqOn F H {x | d < planarRadius x ∧ planarRadius x < S})
    (hHQuad : EqOn H (dualRadialQuadraticPotential R M (-M*R^2/2))
      {x | 0 < planarRadius x ∧ planarRadius x < R/2})
    (Gamma : ℂ ≃ₜ ℂ) (hGamma0 : (0 : ℂ) ∈ Gamma '' closedBall (0 : ℂ) 1)
    (hGammaBound : ∀ z ∈ Gamma '' closedBall (0 : ℂ) 1, ‖z‖ < M * (R-b))
    (e : OpenPartialHomeomorph Coord Coord)
    (heSource : e.source = {x | 0 < planarRadius x ∧ planarRadius x < S})
    (heTarget : e.target = seamComplexCoord '' (ball (0 : ℂ) (M*R) \ Gamma '' closedBall (0 : ℂ) 1))
    (heGradient : ∀ x ∈ e.source, e x = planarGradient H x) :
    BijOn (planarGradient F) {x | a < planarRadius x ∧ planarRadius x < S}
      (seamComplexCoord '' (univ \ Gamma '' closedBall (0 : ℂ) 1)) := by
  let t : ℝ := (d+b)/2
  let T : ℝ := M * (R-t)
  have hdt : d < t := by dsimp [t]; linarith
  have htb : t < b := by dsimp [t]; linarith
  have hat : a < t := had.trans hdt
  have ht0 : 0 < t := ha.trans hat
  have htR : t < R/2 := htb.trans hbR
  have htS : t < S := htR.trans hRS
  have htDomain : t ∈ Ioo a b := ⟨hat, htb⟩
  have hT0 : 0 < T := by dsimp [T]; exact mul_pos hM (by linarith)
  have hTMR : T < M*R := by dsimp [T]; nlinarith [mul_pos hM ht0]
  have hBoundT : ∀ z ∈ Gamma '' closedBall (0 : ℂ) 1, ‖z‖ < T := by
    intro z hz
    exact (hGammaBound z hz).trans (by dsimp [T]; nlinarith [mul_pos hM (sub_pos.mpr htb)])
  have hD := (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioo).mp hg |>.2
  have hAnti : StrictAntiOn (deriv g) (Ioo a b) :=
    strictAntiOn_of_deriv_neg (convex_Ioo a b) hD.continuousOn
      (fun r hr => hgneg r (interior_subset hr))
  have htSlope : deriv g t = T := by
    have heq : g =ᶠ[𝓝 t] dualRadialQuadraticProfile R M (-M*R^2/2) := by
      filter_upwards [isOpen_Ioo.mem_nhds (show t ∈ Ioo d b from ⟨hdt,htb⟩)] with r hr
      exact hgQuad hr
    rw [heq.deriv_eq, dualRadialQuadraticProfile_deriv]
    dsimp [T]
    ring
  have hRadialOpen (u v : ℝ) : IsOpen {x : Coord | u < planarRadius x ∧ planarRadius x < v} :=
    isOpen_Ioo.preimage quadraticFillerCartesianGradient_radius_continuous
  have hFInner {x : Coord} (hx : a < planarRadius x ∧ planarRadius x < t) :
      planarGradient F x = (deriv g (planarRadius x) / planarRadius x) • x := by
    rw [neck_gradient_eq_on (hRadialOpen a b) hFNeck ⟨hx.1,hx.2.trans htb⟩]
    exact neck_radial_gradient hg (ha.trans hx.1) ⟨hx.1,hx.2.trans htb⟩
  have hFInnerRadius {x : Coord} (hx : a < planarRadius x ∧ planarRadius x < t) :
      planarRadius (planarGradient F x) = deriv g (planarRadius x) := by
    rw [hFInner hx, quadraticFillerCartesianGradient_radius_smul
      (div_nonneg (hgpos _ ⟨hx.1,hx.2.trans htb⟩).le (ha.trans hx.1).le)]
    exact div_mul_cancel₀ _ (ha.trans hx.1).ne'
  have hFInnerHigh {x : Coord} (hx : a < planarRadius x ∧ planarRadius x < t) :
      T < planarRadius (planarGradient F x) := by
    rw [hFInnerRadius hx, ← htSlope]
    exact hAnti ⟨hx.1,hx.2.trans htb⟩ htDomain hx.2
  have hQuadGradient {x : Coord} (hx : 0 < planarRadius x ∧ planarRadius x < R/2) :
      planarGradient H x = (M * (R-planarRadius x) / planarRadius x) • x := by
    rw [neck_gradient_eq_on (hRadialOpen 0 (R/2)) hHQuad hx]
    change planarGradient (radialPlanarPotential (dualRadialQuadraticProfile R M (-M*R^2/2))) x = _
    rw [neck_radial_gradient (dualRadialQuadraticProfile_contDiff R M (-M*R^2/2)).contDiffOn hx.1 hx,
      dualRadialQuadraticProfile_deriv]
    congr 1
    ring
  have hQuadRadius {x : Coord} (hx : 0 < planarRadius x ∧ planarRadius x < R/2) :
      planarRadius (planarGradient H x) = M * (R-planarRadius x) := by
    rw [hQuadGradient hx, quadraticFillerCartesianGradient_radius_smul
      (div_nonneg (mul_nonneg hM.le (by linarith [hx.2])) hx.1.le)]
    exact div_mul_cancel₀ _ hx.1.ne'
  have hFOldGradient {x : Coord} (hx : t ≤ planarRadius x ∧ planarRadius x < S) :
      planarGradient F x = e x := by
    have hxE : x ∈ e.source := by rw [heSource]; exact ⟨ht0.trans_le hx.1,hx.2⟩
    rw [neck_gradient_eq_on (hRadialOpen d S) hFOld ⟨hdt.trans_le hx.1,hx.2⟩,
      ← heGradient x hxE]
  have hQuadPreimage {y : Coord} (hy : T < planarRadius y ∧ planarRadius y < M*R) :
      ∃ x : Coord, 0 < planarRadius x ∧ planarRadius x < t ∧
        x ∈ e.source ∧ e x = y := by
    let s := planarRadius y
    let r := R-s/M
    have hs0 : 0 < s := hT0.trans hy.1
    have hr0 : 0 < r := by
      dsimp [r]
      exact sub_pos.mpr ((div_lt_iff₀ hM).mpr (by dsimp [s]; nlinarith [hy.2]))
    have hrt : r < t := by
      have hd : R-t < s/M := (lt_div_iff₀ hM).mpr (by dsimp [s]; dsimp [T] at hy; nlinarith [hy.1])
      dsimp [r]
      linarith
    let x : Coord := (r/s) • y
    have hxRadius : planarRadius x = r := by
      rw [show x = (r/s) • y from rfl,
        quadraticFillerCartesianGradient_radius_smul (div_nonneg hr0.le hs0.le)]
      exact div_mul_cancel₀ r hs0.ne'
    have hxE : x ∈ e.source := by
      rw [heSource]
      change 0 < planarRadius x ∧ planarRadius x < S
      rw [hxRadius]
      exact ⟨hr0,hrt.trans htS⟩
    refine ⟨x, by rwa [hxRadius], by rwa [hxRadius], hxE, ?_⟩
    rw [heGradient x hxE, hQuadGradient ⟨by rwa [hxRadius], by rw [hxRadius]; exact hrt.trans htR⟩,
      hxRadius, show x = (r/s) • y from rfl, smul_smul]
    have hSlope : M * (R-r) = s := by
      dsimp [r]
      field_simp [hM.ne'] <;> ring
    have hc : (M*(R-r)/r)*(r/s) = 1 := by
      rw [hSlope]
      field_simp [hs0.ne', hr0.ne'] <;> ring
    rw [hc, one_smul]
  have hOldLow {x : Coord} (hx : t ≤ planarRadius x ∧ planarRadius x < S) :
      planarRadius (planarGradient F x) ≤ T := by
    rw [hFOldGradient hx]
    have hxE : x ∈ e.source := by rw [heSource]; exact ⟨ht0.trans_le hx.1,hx.2⟩
    have hyE := e.map_source hxE
    rw [heTarget, neck_filling_target_iff] at hyE
    by_contra hhigh
    obtain ⟨q,hq0,hqt,hqE,hqeq⟩ := hQuadPreimage ⟨lt_of_not_ge hhigh,hyE.1⟩
    have hqx : q = x := e.injOn hqE hxE hqeq
    rw [hqx] at hqt
    exact (not_lt_of_ge hx.1) hqt
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    by_cases hxt : planarRadius x < t
    · apply (neck_exterior_iff Gamma _).mpr
      intro hGamma
      have hlow := hBoundT _ hGamma
      rw [angularDescentComplex_norm] at hlow
      exact (not_lt_of_gt (hFInnerHigh ⟨hx.1,hxt⟩)) hlow
    · rw [hFOldGradient ⟨le_of_not_gt hxt,hx.2⟩]
      have hxE : x ∈ e.source := by rw [heSource]; exact ⟨ha.trans hx.1,hx.2⟩
      have hyE := e.map_source hxE
      rw [heTarget,neck_filling_target_iff] at hyE
      exact (neck_exterior_iff Gamma _).mpr hyE.2
  · intro x hx y hy he
    by_cases hxt : planarRadius x < t
    · by_cases hyt : planarRadius y < t
      · have hRadius : planarRadius x = planarRadius y := hAnti.injOn
          ⟨hx.1,hxt.trans htb⟩ ⟨hy.1,hyt.trans htb⟩ (by
            rw [← hFInnerRadius ⟨hx.1,hxt⟩, ← hFInnerRadius ⟨hy.1,hyt⟩, he])
        rw [hFInner ⟨hx.1,hxt⟩, hFInner ⟨hy.1,hyt⟩, ← hRadius] at he
        have hc : deriv g (planarRadius x) / planarRadius x ≠ 0 :=
          (div_pos (hgpos _ ⟨hx.1,hxt.trans htb⟩) (ha.trans hx.1)).ne'
        ext i
        exact mul_left_cancel₀ hc (congrFun he i)
      · have hl := hOldLow ⟨le_of_not_gt hyt,hy.2⟩
        rw [← he] at hl
        exact False.elim ((not_lt_of_ge hl) (hFInnerHigh ⟨hx.1,hxt⟩))
    · by_cases hyt : planarRadius y < t
      · have hl := hOldLow ⟨le_of_not_gt hxt,hx.2⟩
        rw [he] at hl
        exact False.elim ((not_lt_of_ge hl) (hFInnerHigh ⟨hy.1,hyt⟩))
      · apply e.injOn
          (by rw [heSource]; exact ⟨ha.trans hx.1,hx.2⟩)
          (by rw [heSource]; exact ⟨ha.trans hy.1,hy.2⟩)
        rw [← hFOldGradient ⟨le_of_not_gt hxt,hx.2⟩,
          ← hFOldGradient ⟨le_of_not_gt hyt,hy.2⟩]
        exact he
  · intro y hy
    have hyOut := (neck_exterior_iff Gamma y).mp hy
    have hs0 : 0 < planarRadius y := by
      rw [← angularDescentComplex_norm]
      apply norm_pos_iff.mpr
      intro hz
      exact hyOut (hz ▸ hGamma0)
    by_cases hsT : T < planarRadius y
    · obtain ⟨r,hr,hslope⟩ := neck_slope_preimage hD.continuousOn htDomain hEscape (by rwa [htSlope])
      let x : Coord := (r/planarRadius y) • y
      have hr0 : 0 < r := ha.trans hr.1
      have hxRadius : planarRadius x = r := by
        rw [show x = (r/planarRadius y) • y from rfl,
          quadraticFillerCartesianGradient_radius_smul (div_nonneg hr0.le hs0.le)]
        exact div_mul_cancel₀ r hs0.ne'
      have hxInner : a < planarRadius x ∧ planarRadius x < t := by rwa [hxRadius]
      refine ⟨x, ⟨hxInner.1,hxInner.2.trans htS⟩, ?_⟩
      rw [hFInner hxInner,hxRadius,hslope,show x = (r/planarRadius y) • y from rfl,smul_smul]
      have hc : (planarRadius y/r)*(r/planarRadius y) = 1 := by field_simp [hr0.ne',hs0.ne'] <;> ring
      rw [hc,one_smul]
    · have hyE : y ∈ e.target := by
        rw [heTarget,neck_filling_target_iff]
        exact ⟨(le_of_not_gt hsT).trans_lt hTMR,hyOut⟩
      have hxE := e.map_target hyE
      rw [heSource] at hxE
      have hxt : t ≤ planarRadius (e.symm y) := by
        by_contra hsmall
        have hquad := hQuadRadius ⟨hxE.1,(lt_of_not_ge hsmall).trans htR⟩
        have hfwd : planarGradient H (e.symm y) = y :=
          (heGradient _ (e.map_target hyE)).symm.trans (e.right_inv hyE)
        rw [hfwd] at hquad
        have hlarge : T < planarRadius y := by
          rw [hquad]
          dsimp [T]
          nlinarith [mul_pos hM (sub_pos.mpr (lt_of_not_ge hsmall))]
        exact hsT hlarge
      refine ⟨e.symm y, ⟨hat.trans_le hxt,hxE.2⟩, ?_⟩
      rw [hFOldGradient ⟨hxt,hxE.2⟩]
      exact e.right_inv hyE

end
end TightVer401
