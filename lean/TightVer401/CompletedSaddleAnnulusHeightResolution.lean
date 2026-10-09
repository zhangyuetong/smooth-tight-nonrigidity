import TightVer401.CompletedSaddleAnnulusHeight

/-! Resolve an actual interior scalar height at both radial boundaries.
Continuity is constructed from literal collars; no boundary inverse or closed
smoothness package is supplied. This is not completed support existence. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

/-- Actual total extension with explicitly resolved boundary values. -/
def completedSaddleAnnulusHeightResolved (A RN d0 dInfinity : ℝ)
    (Z : Coord → ℝ) (x : Coord) : ℝ :=
  if planarRadius x ≤ A then dInfinity
  else if RN ≤ planarRadius x then d0 else Z x

theorem completedSaddleAnnulusHeightResolved_eq_interior
    {A RN d0 dInfinity : ℝ} {Z : Coord → ℝ} {x : Coord}
    (hx : x ∈ quadraticRadialFillingOpenAnnulus A RN) :
    completedSaddleAnnulusHeightResolved A RN d0 dInfinity Z x = Z x := by
  simp only [completedSaddleAnnulusHeightResolved,
    if_neg (not_le_of_gt hx.1), if_neg (not_le_of_gt hx.2)]

theorem completedSaddleAnnulusHeightResolved_inner_boundary
    {A RN d0 dInfinity : ℝ} {Z : Coord → ℝ} {x : Coord}
    (hx : planarRadius x = A) :
    completedSaddleAnnulusHeightResolved A RN d0 dInfinity Z x = dInfinity := by
  simp [completedSaddleAnnulusHeightResolved, hx]

theorem completedSaddleAnnulusHeightResolved_outer_boundary
    {A RN d0 dInfinity : ℝ} {Z : Coord → ℝ} (hARN : A < RN) {x : Coord}
    (hx : planarRadius x = RN) :
    completedSaddleAnnulusHeightResolved A RN d0 dInfinity Z x = d0 := by
  simp [completedSaddleAnnulusHeightResolved, hx, not_le_of_gt hARN]

/-- Interior agreement is an actual neighborhood germ, so all actual derivatives transfer. -/
theorem completedSaddleAnnulusHeightResolved_germ
    {A RN d0 dInfinity : ℝ} {Z : Coord → ℝ} {x : Coord}
    (hx : x ∈ quadraticRadialFillingOpenAnnulus A RN) :
    completedSaddleAnnulusHeightResolved A RN d0 dInfinity Z =ᶠ[𝓝 x] Z := by
  filter_upwards [(quadraticRadialFilling_openAnnulus_isOpen A RN).mem_nhds hx] with y hy
  exact completedSaddleAnnulusHeightResolved_eq_interior hy

theorem completedSaddleAnnulusHeightResolved_fderiv
    {A RN d0 dInfinity : ℝ} {Z : Coord → ℝ} {x : Coord}
    (hx : x ∈ quadraticRadialFillingOpenAnnulus A RN) :
    fderiv ℝ (completedSaddleAnnulusHeightResolved A RN d0 dInfinity Z) x =
      fderiv ℝ Z x :=
  (completedSaddleAnnulusHeightResolved_germ hx).fderiv_eq

theorem completedSaddleAnnulusHeightResolved_regular
    {A RN d0 dInfinity : ℝ} {Z : Coord → ℝ}
    (hZ : ∀ x ∈ quadraticRadialFillingOpenAnnulus A RN, fderiv ℝ Z x ≠ 0) :
    ∀ x ∈ quadraticRadialFillingOpenAnnulus A RN,
      fderiv ℝ (completedSaddleAnnulusHeightResolved A RN d0 dInfinity Z) x ≠ 0 := by
  intro x hx
  rw [completedSaddleAnnulusHeightResolved_fderiv hx]
  exact hZ x hx

/-- The literal inner model already equals the resolved constant below the inner boundary. -/
theorem completedSaddleAnnulusHeightResolved_inner_model
    {A RN d0 dInfinity B ε : ℝ} {Z : Coord → ℝ}
    (hB : 0 < B) (hεgap : ε < RN - A)
    (hInner : ∀ x : Coord, A < planarRadius x → planarRadius x < A + ε →
      Z x = dInfinity - 2 * Real.sqrt (B * (planarRadius x - A)))
    {x : Coord} (hx : planarRadius x < A + ε) :
    completedSaddleAnnulusHeightResolved A RN d0 dInfinity Z x =
      dInfinity - 2 * Real.sqrt (B * (planarRadius x - A)) := by
  by_cases hi : planarRadius x ≤ A
  · rw [completedSaddleAnnulusHeightResolved, if_pos hi]
    rw [Real.sqrt_eq_zero_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hB.le (sub_nonpos.mpr hi))]
    ring
  · have ho : ¬ RN ≤ planarRadius x := by linarith
    rw [completedSaddleAnnulusHeightResolved, if_neg hi, if_neg ho]
    exact hInner x (lt_of_not_ge hi) hx

/-- The outer continuous max model includes the explicitly resolved outside constant. -/
theorem completedSaddleAnnulusHeightResolved_outer_model
    {A RN d0 dInfinity μ ε : ℝ} {Z : Coord → ℝ}
    (hεgap : ε < RN - A)
    (hOuter : ∀ x : Coord, RN - ε < planarRadius x → planarRadius x < RN →
      Z x = d0 + (RN - planarRadius x)^2 / (2 * μ))
    {x : Coord} (hx : RN - ε < planarRadius x) :
    completedSaddleAnnulusHeightResolved A RN d0 dInfinity Z x =
      d0 + (max (RN - planarRadius x) 0)^2 / (2 * μ) := by
  have hi : ¬ planarRadius x ≤ A := by linarith
  by_cases ho : RN ≤ planarRadius x
  · rw [completedSaddleAnnulusHeightResolved, if_neg hi, if_pos ho,
      max_eq_right (sub_nonpos.mpr ho)]
    simp
  · have hr : planarRadius x < RN := lt_of_not_ge ho
    rw [completedSaddleAnnulusHeightResolved, if_neg hi, if_neg ho,
      max_eq_left (sub_nonneg.mpr hr.le)]
    exact hOuter x hx hr

/-- The complete open outer collar needed by the compact height-separation theorem. -/
theorem completedSaddleAnnulusHeightResolved_outer_collar
    {A RN d0 dInfinity μ ε : ℝ} {Z : Coord → ℝ}
    (hεgap : ε < RN - A)
    (hOuter : ∀ x : Coord, RN - ε < planarRadius x → planarRadius x < RN →
      Z x = d0 + (RN - planarRadius x)^2 / (2 * μ))
    {x : Coord} (hx : RN - ε < planarRadius x) (hRN : planarRadius x < RN) :
    completedSaddleAnnulusHeightResolved A RN d0 dInfinity Z x =
      d0 + (RN - planarRadius x)^2 / (2 * μ) := by
  rw [completedSaddleAnnulusHeightResolved_outer_model hεgap hOuter hx,
    max_eq_left (sub_nonneg.mpr hRN.le)]

/-- Closed-band continuity is proved from actual interior continuity and literal scalar collars. -/
theorem completedSaddleAnnulusHeightResolved_continuousOn
    {A RN d0 dInfinity B μ ε : ℝ} {Z : Coord → ℝ}
    (hARN : A < RN) (hB : 0 < B) (hε : 0 < ε) (hεgap : ε < RN - A)
    (hZ : ContinuousOn Z (quadraticRadialFillingOpenAnnulus A RN))
    (hInner : ∀ x : Coord, A < planarRadius x → planarRadius x < A + ε →
      Z x = dInfinity - 2 * Real.sqrt (B * (planarRadius x - A)))
    (hOuter : ∀ x : Coord, RN - ε < planarRadius x → planarRadius x < RN →
      Z x = d0 + (RN - planarRadius x)^2 / (2 * μ)) :
    ContinuousOn (completedSaddleAnnulusHeightResolved A RN d0 dInfinity Z)
      (quadraticRadialFillingClosedAnnulus A RN) := by
  have hcInner : Continuous (fun x : Coord =>
      dInfinity - 2 * Real.sqrt (B * (planarRadius x - A))) :=
    continuous_const.sub (continuous_const.mul
      (continuous_const.mul (quadraticRadialFilling_radius_continuous.sub continuous_const)).sqrt)
  have hcOuter : Continuous (fun x : Coord =>
      d0 + (max (RN - planarRadius x) 0)^2 / (2 * μ)) :=
    continuous_const.add
      ((((continuous_const.sub quadraticRadialFilling_radius_continuous).max
        continuous_const).pow 2).div_const (2 * μ))
  intro x hx
  by_cases hi : planarRadius x = A
  · have hg : completedSaddleAnnulusHeightResolved A RN d0 dInfinity Z =ᶠ[𝓝 x]
        (fun y => dInfinity - 2 * Real.sqrt (B * (planarRadius y - A))) := by
      have hx' : planarRadius x < A + ε := by rw [hi]; linarith
      filter_upwards [(isOpen_lt quadraticRadialFilling_radius_continuous continuous_const).mem_nhds hx']
        with y hy
      exact completedSaddleAnnulusHeightResolved_inner_model hB hεgap hInner hy
    exact (hcInner.continuousAt.congr_of_eventuallyEq hg).continuousWithinAt
  by_cases ho : planarRadius x = RN
  · have hg : completedSaddleAnnulusHeightResolved A RN d0 dInfinity Z =ᶠ[𝓝 x]
        (fun y => d0 + (max (RN - planarRadius y) 0)^2 / (2 * μ)) := by
      have hx' : RN - ε < planarRadius x := by rw [ho]; linarith
      filter_upwards [(isOpen_lt continuous_const quadraticRadialFilling_radius_continuous).mem_nhds hx']
        with y hy
      exact completedSaddleAnnulusHeightResolved_outer_model hεgap hOuter hy
    exact (hcOuter.continuousAt.congr_of_eventuallyEq hg).continuousWithinAt
  have hxOpen : x ∈ quadraticRadialFillingOpenAnnulus A RN :=
    ⟨lt_of_le_of_ne hx.1 (Ne.symm hi), lt_of_le_of_ne hx.2 ho⟩
  have hcZ : ContinuousAt Z x :=
    (hZ x hxOpen).continuousAt ((quadraticRadialFilling_openAnnulus_isOpen A RN).mem_nhds hxOpen)
  exact (hcZ.congr_of_eventuallyEq
    (completedSaddleAnnulusHeightResolved_germ hxOpen)).continuousWithinAt

/-- Resolve the actual height, then derive the positive completed height gap. -/
theorem completedSaddleAnnulusHeightResolved_separation
    {A RN d0 dInfinity B μ ε : ℝ} {Z : Coord → ℝ}
    (hA : 0 < A) (hARN : A < RN) (hB : 0 < B) (hμ : 0 < μ)
    (hε : 0 < ε) (hεgap : ε < RN - A)
    (hZ : ContinuousOn Z (quadraticRadialFillingOpenAnnulus A RN))
    (hRegular : ∀ x ∈ quadraticRadialFillingOpenAnnulus A RN, fderiv ℝ Z x ≠ 0)
    (hInner : ∀ x : Coord, A < planarRadius x → planarRadius x < A + ε →
      Z x = dInfinity - 2 * Real.sqrt (B * (planarRadius x - A)))
    (hOuter : ∀ x : Coord, RN - ε < planarRadius x → planarRadius x < RN →
      Z x = d0 + (RN - planarRadius x)^2 / (2 * μ)) : d0 < dInfinity := by
  apply completedSaddleAnnulusHeight_separation hA hARN hμ hε
    (completedSaddleAnnulusHeightResolved_continuousOn hARN hB hε hεgap hZ hInner hOuter)
    (completedSaddleAnnulusHeightResolved_regular hRegular)
    (fun x hx => completedSaddleAnnulusHeightResolved_inner_boundary hx)
    (fun x hx => completedSaddleAnnulusHeightResolved_outer_boundary hARN hx)
  intro x hx hRN
  exact completedSaddleAnnulusHeightResolved_outer_collar hεgap hOuter hx hRN

end
end TightVer401
