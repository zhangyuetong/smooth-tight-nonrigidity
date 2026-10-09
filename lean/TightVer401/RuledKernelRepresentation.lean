import TightVer401.RuledBendingNecessity
import TightVer401.RuledProfileRecovery
import TightVer401.ProfileCutoffSupport

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

theorem supported_ruled_bending_has_profile
    {γ T E n : ℝ → Ambient} {k τ W : ℝ → ℝ} {α β : Coord → ℝ} {lower upper : ℝ}
    (hγ : ∀ s, HasDerivAt γ (T s) s)
    (hE : ∀ s, HasDerivAt E (-k s • T s + τ s • n s) s)
    (hT : ∀ s, HasDerivAt T (k s • E s) s)
    (hn : ∀ s, HasDerivAt n (-τ s • E s) s)
    (hk : ContDiff ℝ ∞ k) (hτ : ContDiff ℝ ∞ τ) (hτ0 : ∀ s, τ s ≠ 0)
    (hα : ∀ p : Coord, 0 < p 1 → ContDiffAt ℝ ∞ α p)
    (hβ : ∀ p : Coord, 0 < p 1 → ContDiffAt ℝ ∞ β p)
    (hf : ∀ s, IsOrthonormalFrame (T s) (E s) (n s))
    (hstrain : ∀ p : Coord, 0 < p 1 → ∀ i j : Fin 2,
      strain (ruledMap γ E) (ruledBending α β T n) p i j = 0)
    (hlower : 0 < lower) (hupper : 0 < upper)
    (hsupportLower : ∀ p : Coord, p 1 < lower → ruledBending α β T n p = 0)
    (hsupportUpper : ∀ p : Coord, upper < p 1 → ruledBending α β T n p = 0)
    (hW : ∀ s, HasDerivAt W (ruledPeriodCoefficient k τ s) s) (hW0 : W 0 = 0) :
    ∃ F : ℝ → ℝ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
      (∀ s : ℝ, tsupport F ⊆ Set.Icc (1 / (ruledRho τ s * upper) - W s)
        (1 / (ruledRho τ s * lower) - W s)) ∧
      ∀ p : Coord, 0 < p 1 →
        ruledBending α β T n p = ruledProfileField k τ (ruledRho τ) W F T n p := by
  let P := ruledPotential k τ α β
  let f := ruledTransportWeight τ P
  have hPc (p : Coord) (hp : 0 < p 1) : ContDiffAt ℝ ∞ P p := by
    have hs : ContDiffAt ℝ ∞ (fun q : Coord => q 0) p := (contDiff_apply ℝ ℝ 0).contDiffAt
    have hu : ContDiffAt ℝ ∞ (fun q : Coord => q 1) p := (contDiff_apply ℝ ℝ 1).contDiffAt
    exact ((contDiffAt_const.sub ((hk.contDiffAt.comp p hs).mul hu)).mul (hα p hp)).add
      (((hτ.contDiffAt.comp p hs).mul hu).mul (hβ p hp))
  have hfc (p : Coord) (hp : 0 < p 1) : ContDiffAt ℝ ∞ f p := by
    have hs : ContDiffAt ℝ ∞ (fun q : Coord => q 0) p := (contDiff_apply ℝ ℝ 0).contDiffAt
    have hu : ContDiffAt ℝ ∞ (fun q : Coord => q 1) p := (contDiff_apply ℝ ℝ 1).contDiffAt
    exact (hPc p hp).div (((hτ.contDiffAt.comp p hs).mul hu).mul hu)
      (mul_ne_zero (mul_ne_zero (hτ0 _) (ne_of_gt hp)) (ne_of_gt hp))
  have hfl (p : Coord) (hp : p 1 < lower) : f p = 0 := by
    have hz : P p = 0 := ruledPotential_zero_of_bending_zero (hf _) (hsupportLower p hp)
    simp [f, ruledTransportWeight, hz]
  have hfu (p : Coord) (hp : upper < p 1) : f p = 0 := by
    have hz : P p = 0 := ruledPotential_zero_of_bending_zero (hf _) (hsupportUpper p hp)
    simp [f, ruledTransportWeight, hz]
  have hρpos : ∀ s, 0 < ruledRho τ s := fun s => ruledRho_pos (hτ0 s)
  have hρd : ∀ s, HasDerivAt (ruledRho τ) (ruledLambda τ s * ruledRho τ s / 2) s :=
    fun s => ruledRho_hasDerivAt (hτ.differentiable (by simp) s).hasDerivAt (hτ0 s)
  have hmix (p : Coord) (hp : 0 < p 1) :
      (1 - k (p 0) * p 1) * coordPartial 1 α p + τ (p 0) * p 1 * coordPartial 1 β p +
        k (p 0) * α p - τ (p 0) * β p = 0 := by
    obtain ⟨_, hm, _⟩ := ruled_strain_equations (hγ _) (hE _) (hT _) (hn _)
      ((hα p hp).differentiableAt (by simp)) ((hβ p hp).differentiableAt (by simp)) (hf _)
    exact hm.symm.trans (hstrain p hp 0 1)
  have hfpde (p : Coord) (hp : 0 < p 1) : coordPartial 0 f p -
      p 1 / 2 * (ruledLambda τ (p 0) + p 1 * ruledD k τ (p 0)) * coordPartial 1 f p = 0 := by
    have hτeq : HasDerivAt τ (ruledLambda τ (p 0) * τ (p 0)) (p 0) := by
      convert! (hτ.differentiable (by simp) (p 0)).hasDerivAt using 1
      dsimp only [ruledLambda]
      field_simp [hτ0 (p 0)]
    apply ruledTransportWeight_transport hτeq ((hPc p hp).differentiableAt (by simp))
      (hτ0 _) (ne_of_gt hp)
    exact ruledPotential_transport_of_zero_strain (hγ _) (hE _) (hT _) (hn _)
      (hk.differentiable (by simp) (p 0)).hasDerivAt
      (hτ.differentiable (by simp) (p 0)).hasDerivAt (hτ0 _)
      ((hα p hp).differentiableAt (by simp)) ((hβ p hp).differentiableAt (by simp))
      (hf _) (hstrain p hp 0 0) (hstrain p hp 0 1)
  let F := reciprocalProfile (ruledRho τ) f
  have hFs : ContDiff ℝ ∞ F := reciprocalProfile_contDiff (ruledRho_contDiff hτ hτ0)
    hρpos hupper hfc hfu
  refine ⟨F, hFs, reciprocalProfile_hasCompactSupport hρpos hlower hfl,
    fun s => reciprocalProfile_support_bounds hρd hρpos hlower hupper
      (fun q hq => (hfc q hq).differentiableAt (by simp)) hfl hfu hfpde hW hW0 s, ?_⟩
  have hrep (p : Coord) (hp : 0 < p 1) : P p =
      τ (p 0) * (p 1)^2 * F (ruledFirstIntegral (ruledRho τ) W p) := by
    have he := reciprocalProfile_reconstruction hρd hρpos hupper
      (fun q hq => (hfc q hq).differentiableAt (by simp)) hfu hfpde hW hW0 hp
    change P p / (τ (p 0) * p 1 * p 1) = F (ruledFirstIntegral (ruledRho τ) W p) at he
    have hx := (div_eq_iff (mul_ne_zero (mul_ne_zero (hτ0 _) (ne_of_gt hp)) (ne_of_gt hp))).mp he
    convert! hx using 1 <;> ring
  intro p hp
  exact ruled_profile_recovery_from_potential
    (hk.differentiable (by simp) (p 0)).hasDerivAt
    (hτ.differentiable (by simp) (p 0)).hasDerivAt (hτ0 _) (ne_of_gt (hρpos _)) hp hFs
    ((hα p hp).differentiableAt (by simp)) ((hβ p hp).differentiableAt (by simp)) (hmix p hp) hrep

end
end TightVer401
