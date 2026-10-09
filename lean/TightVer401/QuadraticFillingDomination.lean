import TightVer401.QuadraticDominationBounds
import TightVer401.QuadraticDominationGerms
import TightVer401.QuadraticDominationPeriodicity

/-! The ver500 angular filler coefficient, independent of Cartesian descent. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

/-- The actual tangential boundary trace has a uniform positive margin on the circle. -/
theorem quadraticDomination_trace_margin {R : ℝ} {h b : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (hb : ContDiff ℝ ∞ b)
    (hhper : Function.Periodic h (2 * Real.pi))
    (hbper : Function.Periodic b (2 * Real.pi))
    (htrace : ∀ t, 0 < deriv (deriv h) t + R * b t) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ t, μ ≤ deriv (deriv h) t + R * b t := by
  have : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  have hh2 := (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hh).2).2
  exact momentSlowdown_periodic_min (2 * Real.pi)
    (hh2.add (contDiff_const.mul hb))
    (by intro t; dsimp; rw [deriv_periodic (deriv_periodic hhper) t, hbper t]) htrace
theorem dualQuadraticFiller_angular_expression (R M : ℝ) {chi h b : ℝ → ℝ}
    (hchi : ContDiff ℝ ∞ chi) (hh : ContDiff ℝ ∞ h) (hb : ContDiff ℝ ∞ b) (p : Coord) :
    coordPartial 1 (coordPartial 1 (dualQuadraticFiller R M chi h b)) p +
      p 0 * coordPartial 0 (dualQuadraticFiller R M chi h b) p =
    M * (p 0 * (R - p 0)) + dualQuadraticAngularError R chi h b (p 0) (p 1) := by
  rw [dualQuadraticFiller_angular_second R M hchi hh hb,
    dualQuadraticFiller_coordPartial R M hchi hh hb]
  simp only [ite_true, dualQuadraticAngularError]
  ring

/-- A single derived threshold works for every larger coefficient. -/
theorem exists_quadratic_filler_threshold {R : ℝ} (hR : 0 < R)
    {chi h b : ℝ → ℝ} (hchi : ContDiff ℝ ∞ chi)
    (hh : ContDiff ℝ ∞ h) (hb : ContDiff ℝ ∞ b)
    (hhper : Function.Periodic h (2 * Real.pi))
    (hbper : Function.Periodic b (2 * Real.pi))
    (hchi0 : ∀ r, r ≤ R / 2 → chi r = 0)
    (hchi1 : ∀ r, 3 * R / 4 ≤ r → chi r = 1)
    (htrace : ∀ t, 0 < deriv (deriv h) t + R * b t) :
    ∃ T : ℝ, 0 < T ∧ ∀ M : ℝ, T < M → ∀ p : Coord, 0 < p 0 → p 0 ≤ R →
      coordPartial 0 (coordPartial 0 (dualQuadraticFiller R M chi h b)) p < 0 ∧
      0 < coordPartial 1 (coordPartial 1 (dualQuadraticFiller R M chi h b)) p +
        p 0 * coordPartial 0 (dualQuadraticFiller R M chi h b) p := by
  obtain ⟨A, D, C, hA, hD, hC, hrr, hang, hbb⟩ :=
    quadraticDomination_uniform_estimates hR hchi hh hb hhper hbper
  let T := max A (max (8 * D / R^2) (2 * C / R))
  have hAT : A ≤ T := le_max_left _ _
  have hDT : 8 * D / R^2 ≤ T := (le_max_left _ _).trans (le_max_right _ _)
  have hCT : 2 * C / R ≤ T := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨T, hA.trans_le hAT, ?_⟩
  intro M hM p hr hrR
  have hMA : A < M := hAT.trans_lt hM
  have hMD : 8 * D < M * R^2 := (div_lt_iff₀ (sq_pos_of_pos hR)).mp (hDT.trans_lt hM)
  have hMC : 2 * C < M * R := (div_lt_iff₀ hR).mp (hCT.trans_lt hM)
  have hMpos : 0 < M := hA.trans hMA
  have hp : p 0 ∈ Icc 0 R := ⟨hr.le, hrR⟩
  constructor
  · rw [dualQuadraticFiller_radial_second R M hchi hh hb]
    have he := (le_abs_self (dualQuadraticRadialError R chi h b (p 0) (p 1))).trans (hrr _ hp _)
    dsimp [dualQuadraticRadialError] at he
    linarith
  · rw [dualQuadraticFiller_angular_expression R M hchi hh hb]
    by_cases hinner : p 0 < R / 2
    · have hc : chi (p 0) = 0 := hchi0 _ hinner.le
      have hd : deriv chi (p 0) = 0 := (quadraticDomination_inner_derivatives
        (fun r hr => hchi0 r hr.le) hinner).1
      have he : dualQuadraticAngularError R chi h b (p 0) (p 1) = 0 := by
        simp [dualQuadraticAngularError, hc, hd]
      rw [he, add_zero]
      exact mul_pos hMpos (mul_pos hr (by linarith))
    · have hrhalf : R / 2 ≤ p 0 := le_of_not_gt hinner
      by_cases hmiddle : p 0 ≤ 3 * R / 4
      · have hq : R^2 / 8 ≤ p 0 * (R - p 0) := by
          have hprod := mul_le_mul hrhalf (show R / 4 ≤ R - p 0 by linarith)
            (by positivity : 0 ≤ R / 4) hr.le
          nlinarith
        have hMq := mul_le_mul_of_nonneg_left hq hMpos.le
        have he := (neg_abs_le (dualQuadraticAngularError R chi h b (p 0) (p 1)))
        have hbound := hang _ hp (p 1)
        nlinarith
      · have houter : 3 * R / 4 < p 0 := lt_of_not_ge hmiddle
        have hc : chi (p 0) = 1 := hchi1 _ houter.le
        have hd : deriv chi (p 0) = 0 := (quadraticDomination_plateau_derivatives
          (fun r hr => hchi1 r hr.le) houter).1
        have he : M * (p 0 * (R - p 0)) + dualQuadraticAngularError R chi h b (p 0) (p 1) =
            (deriv (deriv h) (p 1) + R * b (p 1)) +
              (R - p 0) * (M * p 0 - (b (p 1) + deriv (deriv b) (p 1))) := by
          simp only [dualQuadraticAngularError, hc, hd, zero_mul, one_mul, zero_add]
          ring
        rw [he]
        have hMr : C < M * p 0 := by
          have hmul := mul_le_mul_of_nonneg_left hrhalf hMpos.le
          nlinarith
        have hbound := (le_abs_self (b (p 1) + deriv (deriv b) (p 1))).trans (hbb (p 1))
        have hnonneg : 0 ≤ (R - p 0) * (M * p 0 - (b (p 1) + deriv (deriv b) (p 1))) :=
          mul_nonneg (sub_nonneg.mpr hrR) (by linarith)
        linarith [htrace (p 1)]

/-- Exact proposed blueprint interface. The threshold in fact needs only the positive tangential
trace; positivity of b is retained here for the incoming boundary first jet. -/
theorem exists_quadratic_filler_coefficient {R : ℝ} (hR : 0 < R)
    {chi h b : ℝ → ℝ} (hchi : ContDiff ℝ ∞ chi)
    (hh : ContDiff ℝ ∞ h) (hb : ContDiff ℝ ∞ b)
    (hhper : Function.Periodic h (2 * Real.pi))
    (hbper : Function.Periodic b (2 * Real.pi))
    (hchi0 : ∀ r, r ≤ R / 2 → chi r = 0)
    (hchi1 : ∀ r, 3 * R / 4 ≤ r → chi r = 1)
    (_hbpos : ∀ t, 0 < b t)
    (htrace : ∀ t, 0 < deriv (deriv h) t + R * b t)
    (M0 : ℝ) :
    ∃ M : ℝ, M0 < M ∧ 0 < M ∧ ∀ p : Coord, 0 < p 0 → p 0 ≤ R →
      coordPartial 0 (coordPartial 0 (dualQuadraticFiller R M chi h b)) p < 0 ∧
      0 < coordPartial 1 (coordPartial 1 (dualQuadraticFiller R M chi h b)) p +
        p 0 * coordPartial 0 (dualQuadraticFiller R M chi h b) p := by
  obtain ⟨T, hT, hsign⟩ := exists_quadratic_filler_threshold hR hchi hh hb hhper hbper hchi0 hchi1 htrace
  let M := max T M0 + 1
  have hTM : T < M := by dsimp [M]; linarith [le_max_left T M0]
  exact ⟨M, by dsimp [M]; linarith [le_max_right T M0], hT.trans hTM, hsign M hTM⟩

/-- Usable construction with a specified smooth cutoff and arbitrarily large coefficient. -/
theorem exists_quadratic_filler_coefficient_with_cutoff {R : ℝ} (hR : 0 < R)
    {h b : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (hb : ContDiff ℝ ∞ b)
    (hhper : Function.Periodic h (2 * Real.pi))
    (hbper : Function.Periodic b (2 * Real.pi))
    (hbpos : ∀ t, 0 < b t) (htrace : ∀ t, 0 < deriv (deriv h) t + R * b t) (M0 : ℝ) :
    ∃ M : ℝ, M0 < M ∧ 0 < M ∧
      ContDiff ℝ ∞ (dualQuadraticFiller R M (quadraticDominationCutoff R) h b) ∧
      (∀ t, dualQuadraticFiller R M (quadraticDominationCutoff R) h b ![R,t] = h t ∧
        coordPartial 0 (dualQuadraticFiller R M (quadraticDominationCutoff R) h b) ![R,t] = b t ∧
        coordPartial 1 (dualQuadraticFiller R M (quadraticDominationCutoff R) h b) ![R,t] = deriv h t) ∧
      (∀ p : Coord, p 0 ≤ R / 2 →
        dualQuadraticFiller R M (quadraticDominationCutoff R) h b p =
          dualRadialQuadraticProfile R M (-M * R^2 / 2) (p 0)) ∧
      (∀ p : Coord, 0 < p 0 → p 0 ≤ R →
        coordPartial 0 (coordPartial 0 (dualQuadraticFiller R M (quadraticDominationCutoff R) h b)) p < 0 ∧
        0 < coordPartial 1 (coordPartial 1 (dualQuadraticFiller R M (quadraticDominationCutoff R) h b)) p +
          p 0 * coordPartial 0 (dualQuadraticFiller R M (quadraticDominationCutoff R) h b) p) := by
  obtain ⟨hchi, hc0, hc1, _⟩ := quadraticDominationCutoff_properties hR
  obtain ⟨M, hM0, hM, hsign⟩ := exists_quadratic_filler_coefficient hR hchi hh hb hhper hbper hc0 hc1 hbpos htrace M0
  exact ⟨M, hM0, hM, dualQuadraticFiller_contDiff R M hchi hh hb,
    dualQuadraticFiller_boundary_first_jet hR M hchi hh hb hc1,
    fun p hp => dualQuadraticFiller_inner_germ R M hc0 hp, hsign⟩

end
end TightVer401
