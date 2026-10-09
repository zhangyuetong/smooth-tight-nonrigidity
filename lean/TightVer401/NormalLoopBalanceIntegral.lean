import TightVer401.NormalLoopBalance

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

theorem normalLoop_balance_integral_on_chart {a κ : ℝ → ℝ} {r₀ r₁ : ℝ}
    (ha : ContDiff ℝ ∞ a) (hκ : ContDiff ℝ ∞ κ) (hpos : ∀ r, 0 < a r)
    (e : OpenPartialHomeomorph ℝ ℝ) (hefun : (e : ℝ → ℝ) = rawPrimitive a)
    (hsource : Set.uIcc r₀ r₁ ⊆ e.source) :
    (∫ s in rawPrimitive a r₀..rawPrimitive a r₁,
      ruledPeriodCoefficient (normalLoopPhysicalK a κ e.symm)
        (normalLoopPhysicalTau a e.symm) s) =
    (1 / 2 : ℝ) * (∫ r in r₀..r₁, deriv κ r / Real.sqrt (a r)) := by
  let g := ruledPeriodCoefficient (normalLoopPhysicalK a κ e.symm)
    (normalLoopPhysicalTau a e.symm)
  have haderiv (r) : HasDerivAt a (deriv a r) r :=
    ((contDiff_infty_iff_deriv.mp ha).1 r).hasDerivAt
  have hκderiv (r) : HasDerivAt κ (deriv κ r) r :=
    ((contDiff_infty_iff_deriv.mp hκ).1 r).hasDerivAt
  have hψderiv (s) (hs : s ∈ e.target) : HasDerivAt e.symm (a (e.symm s))⁻¹ s :=
    e.hasDerivAt_symm hs (ne_of_gt (hpos _))
      (by rw [hefun]; exact rawPrimitive_hasDerivAt ha.continuous _)
  have hdensity (s) (hs : s ∈ e.target) :
      g s = deriv κ (e.symm s) / (2 * a (e.symm s) * Real.sqrt (a (e.symm s))) := by
    have hd := normalLoop_balance_density (haderiv _) (hκderiv _)
      (hpos _) (hψderiv s hs)
    change g s * a (e.symm s) = _ at hd
    calc
      g s = (deriv κ (e.symm s) / (2 * Real.sqrt (a (e.symm s)))) / a (e.symm s) :=
        (eq_div_iff (ne_of_gt (hpos _))).mpr hd
      _ = _ := by ring
  have haψ : ContinuousOn (fun s => a (e.symm s)) e.target :=
    ha.continuous.comp_continuousOn e.symm.continuousOn
  have hκψ : ContinuousOn (fun s => deriv κ (e.symm s)) e.target :=
    (contDiff_infty_iff_deriv.mp hκ).2.continuous.comp_continuousOn e.symm.continuousOn
  have hden : ContinuousOn (fun s => 2 * a (e.symm s) * Real.sqrt (a (e.symm s))) e.target :=
    (continuousOn_const.mul haψ).mul (Real.continuous_sqrt.comp_continuousOn haψ)
  have hg : ContinuousOn g e.target :=
    (hκψ.div hden (fun s _ => by
      exact mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt (hpos _)))
        (ne_of_gt (Real.sqrt_pos.mpr (hpos _))))).congr (fun s hs => hdensity s hs)
  have himage : rawPrimitive a '' Set.uIcc r₀ r₁ ⊆ e.target := by
    rintro s ⟨r, hr, rfl⟩
    rw [← hefun]
    exact e.map_source (hsource hr)
  have hsub := intervalIntegral.integral_comp_mul_deriv'
    (fun r (_ : r ∈ Set.uIcc r₀ r₁) => rawPrimitive_hasDerivAt ha.continuous r)
    ha.continuous.continuousOn (hg.mono himage)
  rw [← hsub]
  calc
    (∫ r in r₀..r₁, (g ∘ rawPrimitive a) r * a r) =
        ∫ r in r₀..r₁, (1 / 2 : ℝ) * (deriv κ r / Real.sqrt (a r)) := by
      apply intervalIntegral.integral_congr
      intro r hr
      have hrsource := hsource hr
      have hs : rawPrimitive a r ∈ e.target := by
        rw [← hefun]
        exact e.map_source hrsource
      have hinv : e.symm (rawPrimitive a r) = r := by
        rw [← hefun]
        exact e.left_inv hrsource
      have hd := normalLoop_balance_density (haderiv _) (hκderiv _)
        (hpos _) (hψderiv _ hs)
      rw [hinv] at hd
      change g (rawPrimitive a r) * a r = _ at hd
      dsimp [Function.comp_def]
      rw [hd]
      ring
    _ = (1 / 2 : ℝ) * (∫ r in r₀..r₁, deriv κ r / Real.sqrt (a r)) :=
      intervalIntegral.integral_const_mul _ _

end
end TightVer401
