import TightVer401.DualRadialCompletionQuadraticNeck
import TightVer401.DualRadialCompletionPatch

/-! Attach the retained neck to the same actual filling, choosing its puncture
radius below an independently prescribed positive inner slope. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

/-- The neck scalar is constructed and pasted to the given actual filling on
an open quadratic overlap. Its radius is chosen here, rather than granted by
a completed-potential package. -/
theorem exists_dualRadialCompletion_neck_filling_data {R M S RN rho : ℝ}
    (hR : 0 < R) (hM : 0 < M) (hrho : 0 < rho) (hrhoR : rho ≤ R / 2)
    (hRS : rho < S) (hRN : 0 < RN)
    {H : Coord → ℝ}
    (hH : ContDiffOn ℝ ∞ H {p | 0 < planarRadius p ∧ planarRadius p < S})
    (hn : ∀ p, 0 < planarRadius p → planarRadius p < S →
      (planarHessian H p).det < 0)
    (hquad : EqOn H (dualRadialQuadraticPotential R M (-M * R ^ 2 / 2))
      {p | 0 < planarRadius p ∧ planarRadius p < R / 2}) :
    ∃ (a B C b c d : ℝ) (g : ℝ → ℝ) (F : Coord → ℝ),
      0 < a ∧ a < RN ∧ a < c ∧ c < d ∧ d < b ∧ b < rho ∧ 0 < B ∧
      ContDiffOn ℝ ∞ g (Ioo a b) ∧
      (∀ r ∈ Ioo a b, 0 < deriv g r ∧ deriv (deriv g) r < 0) ∧
      Tendsto (deriv g) (𝓝[>] a) atTop ∧
      EqOn g (dualRadialQuadraticProfile R M (-M * R ^ 2 / 2)) (Ioo d b) ∧
      EqOn F (radialPlanarPotential g) {p | a < planarRadius p ∧ planarRadius p < b} ∧
      ContDiffOn ℝ ∞ F {p | a < planarRadius p ∧ planarRadius p < S} ∧
      (∀ p, a < planarRadius p → planarRadius p < S → (planarHessian F p).det < 0) ∧
      EqOn F (radialPlanarPotential (dualRadialNeck C B a))
        {p | a < planarRadius p ∧ planarRadius p < c} ∧
      EqOn F H {p | d < planarRadius p} := by
  let a := min (rho / 4) (RN / 2)
  let j := rho / 2
  have ha : 0 < a := lt_min (by positivity) (by positivity)
  have haRN : a < RN := (min_le_right _ _).trans_lt (by linarith)
  have haj : a < j := (min_le_left _ _).trans_lt (by dsimp [j]; linarith)
  have hjrho : j < rho := by dsimp [j]; linarith
  have hjR : j < R / 2 := hjrho.trans_le hrhoR
  let f := dualRadialQuadraticProfile R M (-M * R ^ 2 / 2)
  let B := dualRadialNeckCoefficient (deriv f j) j a
  let C := dualRadialNeckConstant (f j) (deriv f j) j a
  have hB : 0 < B := dualRadialNeckCoefficient_pos
    (dualRadialQuadraticProfile_signs (R := R) (r := j) hM (by linarith)).1 haj
  obtain ⟨b, c, d, g, hjb, hb, hc, hd, hcollar, hg, hsign, hneck, hin,
      hescape, _, hgeom, _⟩ := exists_dualRadialNeck_gradient_adapter isOpen_Ioo
    (dualRadialQuadraticProfile_contDiff R M (-M * R ^ 2 / 2)).contDiffOn
    ha haj ⟨ha.trans haj, hjrho⟩
    (dualRadialQuadraticProfile_signs (R := R) (r := j) hM (by linarith)).1
    (fun r hr => (dualRadialQuadraticProfile_signs (R := R) (r := r) hM
      (by linarith [hr.2])).2)
  let U0 := radialPlanarDomain (Ioo a b)
  let U1 := {p : Coord | d < planarRadius p ∧ planarRadius p < S}
  let F := dualRadialCompletionPatch U0 U1 (radialPlanarPotential g) H H
  have hU0 : IsOpen U0 := radialPlanarDomain_isOpen isOpen_Ioo
  have hU1 : IsOpen U1 :=
    (isOpen_lt continuous_const quadraticFillerCartesianGradient_radius_continuous).inter
      (isOpen_lt quadraticFillerCartesianGradient_radius_continuous continuous_const)
  have h01 : EqOn (radialPlanarPotential g) H (U0 ∩ U1) := by
    intro p hp
    have hpdb : planarRadius p ∈ Ioo d b := ⟨hp.2.1, hp.1.2.2⟩
    have hpR := hcollar hpdb
    have hpSmall : planarRadius p < R / 2 := hpR.2.trans_le hrhoR
    calc
      radialPlanarPotential g p = radialPlanarPotential f p := hin hpdb
      _ = H p := (hquad ⟨hpR.1, hpSmall⟩).symm
  have h02 : EqOn (radialPlanarPotential g) H (U0 ∩ (∅ : Set Coord)) := by simp
  have h12 : EqOn H H (U1 ∩ (∅ : Set Coord)) := fun _ _ => rfl
  have hsub : U1 ⊆ {p | 0 < planarRadius p ∧ planarRadius p < S} := by
    intro p hp
    exact ⟨(ha.trans haj |>.trans hd.1).trans hp.1, hp.2⟩
  have hcover : {p : Coord | a < planarRadius p ∧ planarRadius p < S} ⊆
      U0 ∪ U1 ∪ (∅ : Set Coord) := by
    intro p hp
    by_cases hpb : planarRadius p < b
    · exact Or.inl (Or.inl ⟨Real.sqrt_pos.mp (ha.trans hp.1), hp.1, hpb⟩)
    · exact Or.inl (Or.inr ⟨hd.2.trans_le (le_of_not_gt hpb), hp.2⟩)
  obtain ⟨he0, he1, _⟩ := dualRadialCompletionPatch_eqOn h01 h02 h12
  refine ⟨a, B, C, b, c, d, g, F, ha, haRN, hc.1, hc.2.trans hd.1,
    hd.2, hb.2, hB, hg, hsign, hescape, hin, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    exact he0 ⟨Real.sqrt_pos.mp (ha.trans hp.1), hp⟩
  · exact (dualRadialCompletionPatch_contDiffOn hU0 hU1 isOpen_empty h01 h02 h12
      (radialPlanarPotential_contDiffOn hg) (hH.mono hsub) (by simp)).mono hcover
  · intro p hp hps
    exact dualRadialCompletionPatch_saddle hU0 hU1 isOpen_empty h01 h02 h12
      (fun p hp => (hgeom p hp).1) (fun p hp => hn p (hsub hp).1 hp.2)
      (by simp) p (hcover ⟨hp, hps⟩)
  · intro p hp
    have hp0 : p ∈ U0 := ⟨Real.sqrt_pos.mp (ha.trans hp.1), hp.1, hp.2.trans (hc.2.trans hjb)⟩
    exact (he0 hp0).trans (hneck hp)
  · intro p hp
    by_cases hpb : planarRadius p < b
    · exact he1 ⟨hp, hpb.trans (hb.2.trans hRS)⟩
    · have hp0 : p ∉ U0 := fun h => hpb h.2.2
      simp [F, dualRadialCompletionPatch, hp0]

/-- Construct the scalar attachment with a controlled radius. -/
theorem exists_dualRadialCompletion_neck_filling_with_radius {R M S RN rho : ℝ}
    (hR : 0 < R) (hM : 0 < M) (hrho : 0 < rho) (hrhoR : rho ≤ R / 2)
    (hRS : rho < S) (hRN : 0 < RN)
    {H : Coord → ℝ}
    (hH : ContDiffOn ℝ ∞ H {p | 0 < planarRadius p ∧ planarRadius p < S})
    (hn : ∀ p, 0 < planarRadius p → planarRadius p < S →
      (planarHessian H p).det < 0)
    (hquad : EqOn H (dualRadialQuadraticPotential R M (-M * R ^ 2 / 2))
      {p | 0 < planarRadius p ∧ planarRadius p < R / 2}) :
    ∃ (a B C c d : ℝ) (F : Coord → ℝ),
      0 < a ∧ a < RN ∧ a < c ∧ c < d ∧ d < rho ∧ 0 < B ∧
      ContDiffOn ℝ ∞ F {p | a < planarRadius p ∧ planarRadius p < S} ∧
      (∀ p, a < planarRadius p → planarRadius p < S → (planarHessian F p).det < 0) ∧
      EqOn F (radialPlanarPotential (dualRadialNeck C B a))
        {p | a < planarRadius p ∧ planarRadius p < c} ∧
      EqOn F H {p | d < planarRadius p ∧ planarRadius p < S} := by
  obtain ⟨a, B, C, b, c, d, g, F, ha, haRN, hac, hcd, hdb, hbrho, hB,
    _hg, _hsg, _hescape, _hmatch, _hFg, hF, hnF, hInner, hOuter⟩ :=
    exists_dualRadialCompletion_neck_filling_data hR hM hrho hrhoR hRS hRN hH hn hquad
  exact ⟨a, B, C, c, d, F, ha, haRN, hac, hcd, hdb.trans hbrho, hB,
    hF, hnF, hInner, fun _ hp => hOuter hp.1⟩

/-- The standard half-radius attachment, with the same scalar witness. -/
theorem exists_dualRadialCompletion_neck_filling {R M S RN : ℝ}
    (hR : 0 < R) (hM : 0 < M) (hRS : R / 2 < S) (hRN : 0 < RN)
    {H : Coord → ℝ}
    (hH : ContDiffOn ℝ ∞ H {p | 0 < planarRadius p ∧ planarRadius p < S})
    (hn : ∀ p, 0 < planarRadius p → planarRadius p < S →
      (planarHessian H p).det < 0)
    (hquad : EqOn H (dualRadialQuadraticPotential R M (-M * R ^ 2 / 2))
      {p | 0 < planarRadius p ∧ planarRadius p < R / 2}) :
    ∃ (a B C c d : ℝ) (F : Coord → ℝ),
      0 < a ∧ a < RN ∧ a < c ∧ c < d ∧ d < R / 2 ∧ 0 < B ∧
      ContDiffOn ℝ ∞ F {p | a < planarRadius p ∧ planarRadius p < S} ∧
      (∀ p, a < planarRadius p → planarRadius p < S → (planarHessian F p).det < 0) ∧
      EqOn F (radialPlanarPotential (dualRadialNeck C B a))
        {p | a < planarRadius p ∧ planarRadius p < c} ∧
      EqOn F H {p | d < planarRadius p ∧ planarRadius p < S} := by
  exact exists_dualRadialCompletion_neck_filling_with_radius hR hM (half_pos hR)
    le_rfl hRS hRN hH hn hquad

end
end TightVer401
