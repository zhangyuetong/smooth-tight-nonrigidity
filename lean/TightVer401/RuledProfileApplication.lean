import TightVer401.RuledProfileUniqueness

/-! Application with the actual torsion, integrating factor and derivatives
of a smooth profile, without independent coefficient or derivative grants. -/
namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

theorem ruled_profile_smoothOn
    {k τ ρ W F : ℝ → ℝ} {T n : ℝ → Ambient}
    (hk : ContDiff ℝ ∞ k) (hτ : ContDiff ℝ ∞ τ) (hρ : ContDiff ℝ ∞ ρ)
    (hW : ContDiff ℝ ∞ W) (hF : ContDiff ℝ ∞ F)
    (hT : ContDiff ℝ ∞ T) (hn : ContDiff ℝ ∞ n) (hρ0 : ∀ s, ρ s ≠ 0) :
    ContDiffOn ℝ ∞ (ruledProfileField k τ ρ W F T n) {p : Coord | p 1 ≠ 0} := by
  have hs : ContDiff ℝ ∞ (fun p : Coord => p 0) :=
    contDiff_apply ℝ ℝ 0
  have hu : ContDiff ℝ ∞ (fun p : Coord => p 1) :=
    contDiff_apply ℝ ℝ 1
  have hkc := hk.comp hs
  have hτc := hτ.comp hs
  have hρc := hρ.comp hs
  have hWc := hW.comp hs
  have hd : ContDiff ℝ ∞ (fun p : Coord => 2 * ρ (p 0)) := contDiff_const.mul hρc
  have hd0 (p : Coord) : 2 * ρ (p 0) ≠ 0 := mul_ne_zero (by norm_num) (hρ0 (p 0))
  have hA : ContDiff ℝ ∞ (ruledAlphaFactor τ ρ) := (hτc.mul hu).div hd hd0
  have hB : ContDiff ℝ ∞ (ruledBetaFactor k ρ) :=
    (contDiff_const.sub (hkc.mul hu)).div hd hd0
  have hV : ContDiffOn ℝ ∞ (ruledFirstIntegral ρ W) {p : Coord | p 1 ≠ 0} :=
    (contDiffOn_const.div (hρc.contDiffOn.mul hu.contDiffOn)
      (fun p hp => mul_ne_zero (hρ0 (p 0)) hp)).sub hWc.contDiffOn
  have hFc := hF.comp_contDiffOn hV
  have hF'c := (contDiff_infty_iff_deriv.mp hF).2.comp_contDiffOn hV
  have hα : ContDiffOn ℝ ∞ (ruledProfileAlpha τ ρ W F) {p : Coord | p 1 ≠ 0} :=
    hA.contDiffOn.mul hF'c
  have hβ : ContDiffOn ℝ ∞ (ruledProfileBeta k ρ W F) {p : Coord | p 1 ≠ 0} :=
    (hu.contDiffOn.mul hFc).sub (hB.contDiffOn.mul hF'c)
  exact (hα.smul (hT.comp hs).contDiffOn).add (hβ.smul (hn.comp hs).contDiffOn)

theorem ruled_actual_profile_zero_strain
    {γ T E n : ℝ → Ambient} {k τ W F : ℝ → ℝ}
    (hγ : ∀ s, HasDerivAt γ (T s) s)
    (hE : ∀ s, HasDerivAt E (-k s • T s + τ s • n s) s)
    (hT : ∀ s, HasDerivAt T (k s • E s) s)
    (hn : ∀ s, HasDerivAt n (-τ s • E s) s)
    (hk : ContDiff ℝ ∞ k) (hτ : ContDiff ℝ ∞ τ) (hτ0 : ∀ s, τ s ≠ 0)
    (hW : ∀ s, HasDerivAt W (ruledPeriodCoefficient k τ s) s)
    (hF : ContDiff ℝ ∞ F)
    (hf : ∀ s, IsOrthonormalFrame (T s) (E s) (n s))
    {p : Coord} (hu : p 1 ≠ 0) :
    ∀ i j : Fin 2, strain (ruledMap γ E)
      (ruledProfileField k τ (ruledRho τ) W F T n) p i j = 0 := by
  have hkd := (hk.differentiable (by simp) (p 0)).hasDerivAt
  have hτd := (hτ.differentiable (by simp) (p 0)).hasDerivAt
  have hτeq : HasDerivAt τ (ruledLambda τ (p 0) * τ (p 0)) (p 0) := by
    convert! hτd using 1
    dsimp only [ruledLambda]
    field_simp [hτ0 (p 0)]
  have hρeq := ruledRho_hasDerivAt hτd (hτ0 (p 0))
  have hFp := (hF.differentiable (by simp) (ruledFirstIntegral (ruledRho τ) W p)).hasDerivAt
  have hF'd := (contDiff_infty_iff_deriv.mp hF).2
  have hF'p := (hF'd.differentiable (by simp) (ruledFirstIntegral (ruledRho τ) W p)).hasDerivAt
  exact ruled_profile_zero_strain (hγ (p 0)) (hE (p 0)) (hT (p 0)) (hn (p 0))
    hkd hτeq hρeq (hW (p 0)) (ne_of_gt (ruledRho_pos (hτ0 (p 0)))) hu hFp hF'p (hf (p 0))

theorem ruled_actual_profile_isInfinitesimalBending
    {γ T E n : ℝ → Ambient} {k τ W F : ℝ → ℝ}
    (hγ : ∀ s, HasDerivAt γ (T s) s)
    (hE : ∀ s, HasDerivAt E (-k s • T s + τ s • n s) s)
    (hT : ∀ s, HasDerivAt T (k s • E s) s)
    (hn : ∀ s, HasDerivAt n (-τ s • E s) s)
    (hk : ContDiff ℝ ∞ k) (hτ : ContDiff ℝ ∞ τ) (hτ0 : ∀ s, τ s ≠ 0)
    (hTs : ContDiff ℝ ∞ T) (hns : ContDiff ℝ ∞ n)
    (hWs : ContDiff ℝ ∞ W) (hW : ∀ s, HasDerivAt W (ruledPeriodCoefficient k τ s) s)
    (hF : ContDiff ℝ ∞ F) (hf : ∀ s, IsOrthonormalFrame (T s) (E s) (n s)) :
    IsInfinitesimalBendingOn (ruledMap γ E)
      (ruledProfileField k τ (ruledRho τ) W F T n) {p : Coord | p 1 ≠ 0} := by
  refine ⟨ruled_profile_smoothOn hk hτ (ruledRho_contDiff hτ hτ0) hWs hF hTs hns
    (fun s => ne_of_gt (ruledRho_pos (hτ0 s))), ?_⟩
  intro p hp
  exact ruled_actual_profile_zero_strain hγ hE hT hn hk hτ hτ0 hW hF hf hp

end
end TightVer401
