import TightVer401.MomentControlBump
import TightVer401.ConcaveJetJoinPrimitive
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! An actual globally smooth radial parameter with literal endpoint germs,
constructed from ordinary positive endpoint derivative data and prescribed
total mass. No cylinder reparametrization or completion package is assumed. -/
namespace TightVer401
noncomputable section
open Set Filter MeasureTheory Metric
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

private theorem completedSaddleAnnulusRadialParameter_bump_mass
    {a b c r : ℝ} (hab : a ≤ b) (hr : 0 < r) :
    (∫ x in a..b, momentControlBump c r hr x) ≤ 2*r := by
  let χ := momentControlBump c r hr
  have hsub : (∫ x in a..b, χ x) ≤ ∫ x : ℝ, χ x := by
    rw [intervalIntegral.integral_of_le hab]
    exact MeasureTheory.setIntegral_le_integral (χ.integrable (μ := volume))
      (Eventually.of_forall fun x => χ.nonneg)
  have htotal : (∫ x : ℝ, χ x) ≤ 2*r := by
    have hm := χ.integral_le_measure_closedBall volume
    rw [Real.volume_real_closedBall χ.rOut_pos.le] at hm
    exact hm
  exact hsub.trans htotal

private theorem completedSaddleAnnulusRadialParameter_weighted_mass
    {a b c r K : ℝ} (hab : a ≤ b) (hr : 0 < r) (hK : 0 ≤ K)
    {f : ℝ → ℝ} (hf : Continuous f)
    (hbound : ∀ x ∈ Icc a b, ‖f x‖ ≤ K) :
    (∫ x in a..b, momentControlBump c r hr x * f x) ≤ 2*K*r := by
  let χ := momentControlBump c r hr
  have hcomp := intervalIntegral.integral_mono_on hab
    ((χ.continuous.mul hf).intervalIntegrable (μ := volume) a b)
    ((χ.continuous.const_mul K).intervalIntegrable (μ := volume) a b)
    (fun x hx => by
      simpa only [Pi.mul_apply, mul_comm K] using mul_le_mul_of_nonneg_left
        ((le_abs_self (f x)).trans (by simpa only [Real.norm_eq_abs] using hbound x hx))
        χ.nonneg)
  have hcomp' : (∫ x in a..b, χ x * f x) ≤ K * (∫ x in a..b, χ x) := by
    simpa only [Pi.mul_apply, intervalIntegral.integral_mul_const, mul_comm K] using hcomp
  exact hcomp'.trans ((mul_le_mul_of_nonneg_left
    (completedSaddleAnnulusRadialParameter_bump_mass hab hr) hK).trans_eq (by ring))

/-- Positive smooth derivative with prescribed mass and actual endpoint
derivative germs. The endpoint derivative functions need be positive only
on the open interval, so the left derivative may vanish at its endpoint. -/
theorem completedSaddleAnnulusRadialParameter_exists_derivative
    {a b T : ℝ} (hab : a < b) (hT : 0 < T) {f₀ f₁ : ℝ → ℝ}
    (hf₀ : ContDiff ℝ ∞ f₀) (hf₁ : ContDiff ℝ ∞ f₁)
    (hpos₀ : ∀ x ∈ Ioo a b, 0 < f₀ x)
    (hpos₁ : ∀ x ∈ Ioo a b, 0 < f₁ x) :
    ∃ v : ℝ → ℝ, ContDiff ℝ ∞ v ∧
      (∀ x ∈ Ioo a b, 0 < v x) ∧ (∫ x in a..b, v x) = T ∧
      (∃ ε > 0, EqOn v f₀ (Ioo (a-ε) (a+ε))) ∧
      (∃ ε > 0, EqOn v f₁ (Ioo (b-ε) (b+ε))) := by
  obtain ⟨K₀, hK₀⟩ := (isCompact_Icc : IsCompact (Icc a b)).exists_bound_of_continuousOn
    hf₀.continuous.continuousOn
  obtain ⟨K₁, hK₁⟩ := (isCompact_Icc : IsCompact (Icc a b)).exists_bound_of_continuousOn
    hf₁.continuous.continuousOn
  let K := max (max K₀ K₁) 1
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hbound₀ : ∀ x ∈ Icc a b, ‖f₀ x‖ ≤ K :=
    fun x hx => (hK₀ x hx).trans ((le_max_left K₀ K₁).trans (le_max_left _ _))
  have hbound₁ : ∀ x ∈ Icc a b, ‖f₁ x‖ ≤ K :=
    fun x hx => (hK₁ x hx).trans ((le_max_right K₀ K₁).trans (le_max_left _ _))
  let D := 4*K+(b-a)
  have hD : 0 < D := by dsimp [D]; linarith
  let δ := min ((b-a)/8) (T/(2*D))
  have hδ : 0 < δ := lt_min (by linarith) (div_pos hT (by positivity))
  have hδGap : δ < (b-a)/4 := by
    have h := min_le_left ((b-a)/8) (T/(2*D))
    dsimp [δ]
    linarith
  have hδMass : D*δ < T := by
    have h := min_le_right ((b-a)/8) (T/(2*D))
    have hmul := mul_le_mul_of_nonneg_left h hD.le
    have hcancel : D*(T/(2*D)) = T/2 := by field_simp [hD.ne']
    change D*δ ≤ D*(T/(2*D)) at hmul
    rw [hcancel] at hmul
    linarith
  let χ₀ := momentControlBump a δ hδ
  let χ₁ := momentControlBump b δ hδ
  let floor : ℝ → ℝ := fun x => (1-χ₀ x)*(1-χ₁ x)
  let v₀ : ℝ → ℝ := fun x => χ₀ x*f₀ x + χ₁ x*f₁ x + δ*floor x
  have hfloor : ContDiff ℝ ∞ floor :=
    (contDiff_const.sub χ₀.contDiff).mul (contDiff_const.sub χ₁.contDiff)
  have hv₀ : ContDiff ℝ ∞ v₀ :=
    ((χ₀.contDiff.mul hf₀).add (χ₁.contDiff.mul hf₁)).add (contDiff_const.mul hfloor)
  have hfloor01 (x : ℝ) : 0 ≤ floor x ∧ floor x ≤ 1 := by
    have h₀ : 0 ≤ 1-χ₀ x := sub_nonneg.mpr χ₀.le_one
    have h₁ : 0 ≤ 1-χ₁ x := sub_nonneg.mpr χ₁.le_one
    constructor
    · exact mul_nonneg h₀ h₁
    · dsimp [floor]
      calc
        (1-χ₀ x)*(1-χ₁ x) ≤ 1*(1-χ₁ x) :=
          mul_le_mul_of_nonneg_right (by linarith [χ₀.nonneg (x := x)]) h₁
        _ ≤ 1 := by linarith [χ₁.nonneg (x := x)]
  have hv₀pos : ∀ x ∈ Ioo a b, 0 < v₀ x := by
    intro x hx
    have hf0 := hpos₀ x hx
    have hf1 := hpos₁ x hx
    have hterm0 : 0 ≤ χ₀ x*f₀ x := mul_nonneg χ₀.nonneg hf0.le
    have hterm1 : 0 ≤ χ₁ x*f₁ x := mul_nonneg χ₁.nonneg hf1.le
    have hterm2 : 0 ≤ δ*floor x := mul_nonneg hδ.le (hfloor01 x).1
    by_cases hzero0 : χ₀ x = 0
    · by_cases hzero1 : χ₁ x = 0
      · simp [v₀, floor, hzero0, hzero1, hδ]
      · have hstrict := mul_pos (lt_of_le_of_ne χ₁.nonneg (Ne.symm hzero1)) hf1
        dsimp [v₀]
        linarith
    · have hstrict := mul_pos (lt_of_le_of_ne χ₀.nonneg (Ne.symm hzero0)) hf0
      dsimp [v₀]
      linarith
  have hmass₀ : (∫ x in a..b, v₀ x) < T := by
    have hb₀ := completedSaddleAnnulusRadialParameter_weighted_mass hab.le hδ hK.le
      hf₀.continuous hbound₀ (c := a)
    have hb₁ := completedSaddleAnnulusRadialParameter_weighted_mass hab.le hδ hK.le
      hf₁.continuous hbound₁ (c := b)
    have hbFloor := intervalIntegral.integral_mono_on hab.le
      (hfloor.continuous.intervalIntegrable (μ := volume) a b) intervalIntegrable_const
      (fun x _ => (hfloor01 x).2)
    have hbFloor' : (∫ x in a..b, floor x) ≤ b-a := by
      simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_one] using hbFloor
    have hfloorMul := mul_le_mul_of_nonneg_left hbFloor' hδ.le
    have hexpand : (∫ x in a..b, v₀ x) =
        (∫ x in a..b, χ₀ x*f₀ x) + (∫ x in a..b, χ₁ x*f₁ x) +
          δ*(∫ x in a..b, floor x) := by
      have he1 := intervalIntegral.integral_add
        (((χ₀.continuous.mul hf₀.continuous).add
          (χ₁.continuous.mul hf₁.continuous)).intervalIntegrable (μ := volume) a b)
        ((hfloor.continuous.const_mul δ).intervalIntegrable (μ := volume) a b)
      have he2 := intervalIntegral.integral_add
        ((χ₀.continuous.mul hf₀.continuous).intervalIntegrable (μ := volume) a b)
        ((χ₁.continuous.mul hf₁.continuous).intervalIntegrable (μ := volume) a b)
      simp only [Pi.add_apply, Pi.mul_apply] at he1 he2
      dsimp [v₀]
      rw [he1, he2, intervalIntegral.integral_const_mul]
    rw [hexpand]
    change D*δ < T at hδMass
    dsimp [D] at hδMass
    change (∫ x in a..b, χ₀ x*f₀ x) ≤ 2*K*δ at hb₀
    change (∫ x in a..b, χ₁ x*f₁ x) ≤ 2*K*δ at hb₁
    nlinarith
  let c := (a+b)/2
  let r := (b-a)/4
  have hr : 0 < r := by dsimp [r]; linarith
  let ψ := normalizedMomentControl c r hr
  have hψ : ContDiff ℝ ∞ ψ := normalizedMomentControl_contDiff c r hr
  have hψMass : (∫ x in a..b, ψ x) = 1 := by
    have hSupport : Function.support ψ ⊆ Ioc a b := by
      intro x hx
      rw [normalizedMomentControl_support] at hx
      dsimp [c,r] at hx
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    rw [intervalIntegral.integral_eq_integral_of_support_subset hSupport]
    exact normalizedMomentControl_integral c r hr
  let κ := T-(∫ x in a..b, v₀ x)
  have hk : 0 < κ := sub_pos.mpr hmass₀
  let v : ℝ → ℝ := fun x => v₀ x + κ*ψ x
  have hv : ContDiff ℝ ∞ v := hv₀.add (contDiff_const.mul hψ)
  have hvpos : ∀ x ∈ Ioo a b, 0 < v x := by
    intro x hx
    exact add_pos_of_pos_of_nonneg (hv₀pos x hx)
      (mul_nonneg hk.le (normalizedMomentControl_nonneg c r hr x))
  have hvMass : (∫ x in a..b, v x) = T := by
    rw [show (∫ x in a..b, v x) =
      (∫ x in a..b, v₀ x) + κ*(∫ x in a..b, ψ x) by
        dsimp [v]
        rw [intervalIntegral.integral_add
          (hv₀.continuous.intervalIntegrable (μ := volume) a b)
          ((hψ.continuous.const_mul κ).intervalIntegrable (μ := volume) a b),
          intervalIntegral.integral_const_mul], hψMass]
    dsimp [κ]
    ring
  have hleft : EqOn v f₀ (Ioo (a-δ/2) (a+δ/2)) := by
    intro x hx
    have hχ₀ : χ₀ x = 1 := by
      apply χ₀.one_of_mem_closedBall
      change dist x a ≤ δ/2
      rw [Real.dist_eq]
      exact abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hχ₁ : χ₁ x = 0 := by
      apply χ₁.zero_of_le_dist
      change δ ≤ dist x b
      rw [Real.dist_eq, abs_of_neg (by linarith [hx.2])]
      linarith [hx.2]
    have hψZero : ψ x = 0 := by
      apply Function.notMem_support.mp
      intro hs
      rw [normalizedMomentControl_support] at hs
      dsimp [c,r] at hs
      linarith [hs.1, hx.2]
    simp [v,v₀,floor,hχ₀,hχ₁,hψZero]
  have hright : EqOn v f₁ (Ioo (b-δ/2) (b+δ/2)) := by
    intro x hx
    have hχ₁ : χ₁ x = 1 := by
      apply χ₁.one_of_mem_closedBall
      change dist x b ≤ δ/2
      rw [Real.dist_eq]
      exact abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hχ₀ : χ₀ x = 0 := by
      apply χ₀.zero_of_le_dist
      change δ ≤ dist x a
      rw [Real.dist_eq, abs_of_pos (by linarith [hx.1])]
      linarith [hx.1]
    have hψZero : ψ x = 0 := by
      apply Function.notMem_support.mp
      intro hs
      rw [normalizedMomentControl_support] at hs
      dsimp [c,r] at hs
      linarith [hs.2, hx.1]
    simp [v,v₀,floor,hχ₀,hχ₁,hψZero]
  exact ⟨v,hv,hvpos,hvMass,⟨δ/2,half_pos hδ,hleft⟩,
    ⟨δ/2,half_pos hδ,hright⟩⟩

/-- Construct a literal smooth monotone interpolation from ordinary smooth
endpoint models whose derivatives are positive on the open interval. -/
theorem completedSaddleAnnulusRadialParameter_exists_from_models
    {a b A RN : ℝ} (hab : a < b) (hAR : A < RN)
    {q₀ q₁ : ℝ → ℝ} (hq₀ : ContDiff ℝ ∞ q₀) (hq₁ : ContDiff ℝ ∞ q₁)
    (hq₀a : q₀ a = A) (hq₁b : q₁ b = RN)
    (hpos₀ : ∀ x ∈ Ioo a b, 0 < deriv q₀ x)
    (hpos₁ : ∀ x ∈ Ioo a b, 0 < deriv q₁ x) :
    ∃ β : ℝ → ℝ, ContDiff ℝ ∞ β ∧ StrictMonoOn β (Icc a b) ∧
      β a = A ∧ β b = RN ∧ (∀ x ∈ Ioo a b, 0 < deriv β x) ∧
      β =ᶠ[𝓝 a] q₀ ∧ β =ᶠ[𝓝 b] q₁ := by
  obtain ⟨v,hv,hvpos,hMass,⟨ε₀,hε₀,he₀⟩,⟨ε₁,hε₁,he₁⟩⟩ :=
    completedSaddleAnnulusRadialParameter_exists_derivative hab (sub_pos.mpr hAR)
      (contDiff_infty_iff_deriv.mp hq₀).2 (contDiff_infty_iff_deriv.mp hq₁).2 hpos₀ hpos₁
  let β : ℝ → ℝ := fun x => A+jetPrimitive a v x
  have hβ : ContDiff ℝ ∞ β := contDiff_const.add (jetPrimitive_contDiff hv a)
  have hd (x : ℝ) : HasDerivAt β (v x) x :=
    (jetPrimitive_hasDerivAt hv.continuous a x).const_add A
  have hβa : β a = A := by simp [β,jetPrimitive]
  have hβb : β b = RN := by
    dsimp [β]
    rw [jetPrimitive_eq_interval hv.continuous,hMass]
    ring
  have hβpos : ∀ x ∈ Ioo a b, 0 < deriv β x := by
    intro x hx
    rw [(hd x).deriv]
    exact hvpos x hx
  have hmono : StrictMonoOn β (Icc a b) :=
    strictMonoOn_of_deriv_pos (convex_Icc a b) hβ.continuous.continuousOn
      (by simpa only [interior_Icc] using hβpos)
  have hleftEq : EqOn β q₀ (Ioo (a-ε₀) (a+ε₀)) := by
    apply isOpen_Ioo.eqOn_of_deriv_eq (convex_Ioo _ _).isPreconnected
      (hβ.differentiable (by simp)).differentiableOn
      (hq₀.differentiable (by simp)).differentiableOn
      (fun x hx => (hd x).deriv.trans (he₀ hx))
      (show a ∈ Ioo (a-ε₀) (a+ε₀) from ⟨by linarith,by linarith⟩)
    exact hβa.trans hq₀a.symm
  have hrightEq : EqOn β q₁ (Ioo (b-ε₁) (b+ε₁)) := by
    apply isOpen_Ioo.eqOn_of_deriv_eq (convex_Ioo _ _).isPreconnected
      (hβ.differentiable (by simp)).differentiableOn
      (hq₁.differentiable (by simp)).differentiableOn
      (fun x hx => (hd x).deriv.trans (he₁ hx))
      (show b ∈ Ioo (b-ε₁) (b+ε₁) from ⟨by linarith,by linarith⟩)
    exact hβb.trans hq₁b.symm
  exact ⟨β,hβ,hmono,hβa,hβb,hβpos,
    Filter.mem_of_superset (isOpen_Ioo.mem_nhds
      (show a ∈ Ioo (a-ε₀) (a+ε₀) from ⟨by linarith,by linarith⟩)) hleftEq,
    Filter.mem_of_superset (isOpen_Ioo.mem_nhds
      (show b ∈ Ioo (b-ε₁) (b+ε₁) from ⟨by linarith,by linarith⟩)) hrightEq⟩

/-- The actual cylinder radial parameter, with coefficient `B` unchanged
in its square germ and the exact normalized cosine germ at the north end. -/
theorem exists_completedSaddleAnnulusRadialParameter
    {A RN B μ h : ℝ} (hA : 0 < A) (hAR : A < RN)
    (hB : 0 < B) (hμ : 0 < μ) (hh : 0 < h) :
    ∃ β : ℝ → ℝ, ContDiff ℝ ∞ β ∧
      StrictMonoOn β (Icc (Real.pi/2) Real.pi) ∧
      β (Real.pi/2) = A ∧ β Real.pi = RN ∧
      (∀ u ∈ Ioo (Real.pi/2) Real.pi, 0 < deriv β u) ∧
      β =ᶠ[𝓝 (Real.pi/2)] (fun u => A+B*(u-Real.pi/2)^2) ∧
      β =ᶠ[𝓝 Real.pi] (fun u => RN-2*Real.sqrt (μ*h)*Real.cos (u/2)) := by
  let q₀ : ℝ → ℝ := fun u => A+B*(u-Real.pi/2)^2
  let q₁ : ℝ → ℝ := fun u => RN-2*Real.sqrt (μ*h)*Real.cos (u/2)
  have hq₀ : ContDiff ℝ ∞ q₀ :=
    contDiff_const.add (contDiff_const.mul ((contDiff_id.sub contDiff_const).pow 2))
  have hq₁ : ContDiff ℝ ∞ q₁ :=
    contDiff_const.sub (contDiff_const.mul (Real.contDiff_cos.comp (contDiff_id.div_const 2)))
  have hd₀ (u : ℝ) : HasDerivAt q₀ (2*B*(u-Real.pi/2)) u := by
    have hd := ((((hasDerivAt_id u).sub_const (Real.pi/2)).pow 2).const_mul B).const_add A
    convert! hd using 1 <;> simp [q₀] <;> ring
  have hd₁ (u : ℝ) : HasDerivAt q₁ (Real.sqrt (μ*h)*Real.sin (u/2)) u := by
    have hd := (((hasDerivAt_id u).div_const 2).cos.const_mul
      (2*Real.sqrt (μ*h))).const_sub RN
    convert! hd using 1 <;> simp [q₁] <;> ring
  apply completedSaddleAnnulusRadialParameter_exists_from_models
    (by linarith [Real.pi_pos] : Real.pi/2 < Real.pi) hAR hq₀ hq₁
  · simp [q₀]
  · simp [q₁]
  · intro u hu
    rw [(hd₀ u).deriv]
    exact mul_pos (mul_pos (by norm_num) hB) (sub_pos.mpr hu.1)
  · intro u hu
    rw [(hd₁ u).deriv]
    exact mul_pos (Real.sqrt_pos.mpr (mul_pos hμ hh))
      (Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos,hu.1]) (by linarith [hu.2,Real.pi_pos]))

end
end TightVer401
