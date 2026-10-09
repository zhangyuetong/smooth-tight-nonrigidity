import TightVer401.AnnularDegreeLocalSign
import TightVer401.PeriodicPlanarSchoenflies
import TightVer401.AnnularDegreeLifts
import OAI.Analysis.CircleDomains.Topology.CircleFormBoundary

/-! A single orientation sign for the actual Green and argument formulas.
The sign is selected by the proved finite-circle Green theorem and used
for both area and winding, so independent existential choices cannot be
confused. Only interior source disks will require derivative regularity. -/
namespace TightVer401
noncomputable section
open Set Function Filter MeasureTheory Metric
open OAI.CircleDomainRigidity OAI.CircleDomainRigidity.FiniteTransfer
open scoped Topology ContDiff BigOperators

/-- Ordinary Green and actual real argument increments share one sign.
Every classical formula used here is proved by the pinned foundation. -/
theorem annular_jordan_green_and_argument
    (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) (hγ : RegularJordanParametrization H γ) :
    ∃ ε : ℝ, |ε| = 1 ∧
      (∀ P Q : ℂ → ℝ, ContDiff ℝ ∞ P → ContDiff ℝ ∞ Q →
        ε * planarFormIntegral P Q γ =
          ∫ z in jordanInterior H, (fderiv ℝ Q z) 1 - (fderiv ℝ P z) Complex.I) ∧
      ∀ z ∈ jordanInterior H,
        ∃ v : ℝ → ℝ, ContDiff ℝ ∞ v ∧
          (∀ t, (v t : UnitAddCircle) = normalizedArgument (γ t - z)) ∧
          v 1 - v 0 = ε := by
  classical
  obtain ⟨ε, hε, hG⟩ := unorientedFiniteCircleGreenFormula H γ hγ
  refine ⟨ε, hε, ?_, ?_⟩
  · intro P Q hP hQ
    simpa using hG 0 (Fin.elim0) (Fin.elim0)
      (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
      (fun i => Fin.elim0 i) univ isOpen_univ (subset_univ _)
      P Q hP.contDiffOn hQ.contDiffOn
  · intro z hz
    let O : Set ℂ := {w | w ≠ z}
    have hO : IsOpen O := isOpen_ne_fun continuous_id continuous_const
    have hu : SmoothCircleOn (centeredArgument z) O := smoothCircleOn_centeredArgument z
    have hγO : ∀ t, γ t ∈ O := by
      intro t heq
      have ht := hγ.mem_frontier t
      rw [frontier, (jordanInterior_isOpen H).interior_eq] at ht
      exact ht.2 (heq ▸ hz)
    obtain ⟨v, hv, hproj⟩ := annular_exists_smooth_real_circuit_lift hO hu hγ.smooth hγO
    refine ⟨v, hv, hproj, ?_⟩
    obtain ⟨r, hr, hrH⟩ := nhds_basis_closedBall.mem_iff.mp
      ((jordanInterior_isOpen H).mem_nhds hz)
    have hcover : closure (jordanInterior H) \ ⋃ _i : Fin 1, ball z r ⊆ O := by
      intro w hw heq
      subst w
      exact hw.2 (mem_iUnion.mpr ⟨0, mem_ball_self hr⟩)
    have hc := contDiffOn_circleFDeriv hO hu
    have hformula := hG 1 (fun _ => z) (fun _ => r) (fun _ => hr)
      (fun i j hij => (hij (Subsingleton.elim _ _)).elim) (fun _ => hrH) O hO hcover
      (fun w => circleFDeriv (centeredArgument z) w 1)
      (fun w => circleFDeriv (centeredArgument z) w Complex.I)
      (hc.clm_apply contDiffOn_const) (hc.clm_apply contDiffOn_const)
    have hzero : (∫ w in jordanInterior H \ ⋃ _i : Fin 1, closedBall z r,
        fderiv ℝ (fun w => circleFDeriv (centeredArgument z) w Complex.I) w 1 -
          fderiv ℝ (fun w => circleFDeriv (centeredArgument z) w 1) w Complex.I) = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro w hw
      have hwO : w ∈ O := hcover ⟨subset_closure hw.1, fun h => hw.2 (by
        obtain ⟨i, hi⟩ := mem_iUnion.mp h
        exact mem_iUnion.mpr ⟨i, ball_subset_closedBall hi⟩)⟩
      exact sub_eq_zero.mpr (circleFDeriv_closed_complex hO hu hwO)
    have hinner : planarFormIntegral (fun w => circleFDeriv (centeredArgument z) w 1)
        (fun w => circleFDeriv (centeredArgument z) w Complex.I) (unitCircleParam z r) = 1 := by
      simpa only [circleFormIntegral, show (fun _ : ℂ => (1 : ℝ)) = 1 from rfl, one_mul]
        using centeredArgument_round_integral z hr
    have houter : planarFormIntegral (fun w => circleFDeriv (centeredArgument z) w 1)
        (fun w => circleFDeriv (centeredArgument z) w Complex.I) γ = v 1 - v 0 := by
      simpa only [circleFormIntegral, show (fun _ : ℂ => (1 : ℝ)) = 1 from rfl, one_mul]
        using circleFormIntegral_constant_weight hO hu (fun _ => 1) γ hγ.smooth hγO v
          hv.continuous hproj 1 (fun _ _ => rfl)
    simp only [Fin.sum_univ_one, hinner, houter, hzero] at hformula
    rcases le_total 0 ε with hp | hn
    · rw [abs_of_nonneg hp] at hε
      rw [hε] at hformula ⊢
      linarith
    · rw [abs_of_nonpos hn] at hε
      have hε' : ε = -1 := by linarith
      rw [hε'] at hformula ⊢
      linarith

theorem annular_positive_ball_integral {q : ℂ → ℝ} (c : ℂ) {r : ℝ}
    (hr : 0 < r) (hq : ContinuousOn q (closedBall c r))
    (hpos : ∀ z ∈ ball c r, 0 < q z) : 0 < ∫ z in ball c r, q z := by
  have hi : IntegrableOn q (ball c r) :=
    (hq.integrableOn_compact (isCompact_closedBall c r)).mono_set ball_subset_closedBall
  have hnonneg : 0 ≤ᵐ[volume.restrict (ball c r)] q := by
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with z hz
    exact (hpos z hz).le
  apply (setIntegral_pos_iff_support_of_nonneg_ae hnonneg hi).2
  have hs : support q ∩ ball c r = ball c r := by
    apply Set.inter_eq_self_of_subset_right
    intro z hz
    exact (hpos z hz).ne'
  rw [hs]
  exact measure_ball_pos volume c hr

/-- Actual derivative determinants are continuous on an open smoothness
domain. The proof uses the actual real/imaginary derivative columns. -/
theorem annular_complexJacobian_continuousOn {F : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) :
    ContinuousOn (fun z => (fderiv ℝ F z).det) U := by
  have hd : ContDiffOn ℝ ∞ (fderiv ℝ F) U := hF.fderiv_of_isOpen hU (by simp)
  have hOne := hd.clm_apply (contDiffOn_const (c := (1 : ℂ)))
  have hI := hd.clm_apply (contDiffOn_const (c := Complex.I))
  have hOneRe := (Complex.reCLM.contDiff.comp_contDiffOn hOne).continuousOn
  have hOneIm := (Complex.imCLM.contDiff.comp_contDiffOn hOne).continuousOn
  have hIRe := (Complex.reCLM.contDiff.comp_contDiffOn hI).continuousOn
  have hIIm := (Complex.imCLM.contDiff.comp_contDiffOn hI).continuousOn
  apply ((hOneRe.mul hIIm).sub (hIRe.mul hOneIm)).congr
  intro z _
  change (fderiv ℝ F z).det =
    (fderiv ℝ F z 1).re * (fderiv ℝ F z Complex.I).im -
      (fderiv ℝ F z Complex.I).re * (fderiv ℝ F z 1).im
  exact complex_real_det_columns (fderiv ℝ F z)

/-- For a regular image of a local source circle, the argument turn is
the actual derivative sign. The regular image and local filling will be
constructed from the inverse chart in the subsequent application. -/
theorem annular_regular_image_circle_argument_sign
    {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (c : ℂ) {r : ℝ} (hr : 0 < r) (hsource : closedBall c r ⊆ U)
    (s : ℝ) (hs : |s| = 1)
    (hJ : ∀ z ∈ closedBall c r, 0 < s * (fderiv ℝ F z).det)
    (H : ℂ ≃ₜ ℂ)
    (hγ : RegularJordanParametrization H (F ∘ unitCircleParam c r)) :
    ∀ y ∈ jordanInterior H,
      ∃ v : ℝ → ℝ, ContDiff ℝ ∞ v ∧
        (∀ t, (v t : UnitAddCircle) = normalizedArgument (F (unitCircleParam c r t) - y)) ∧
        v 1 - v 0 = s := by
  obtain ⟨ε, hε, hgreen, hargument⟩ := annular_jordan_green_and_argument H _ hγ
  have htargetInt : IntegrableOn (fun _ : ℂ => (1 : ℝ)) (jordanInterior H) :=
    ((continuous_const.continuousOn).integrableOn_compact
      (isCompact_closure_jordanInterior H)).mono_set subset_closure
  have htargetPos : 0 < ∫ z in jordanInterior H, (1 : ℝ) := by
    apply (setIntegral_pos_iff_support_of_nonneg_ae
      (Eventually.of_forall fun _ => zero_le_one) htargetInt).2
    have hsupp : support (fun _ : ℂ => (1 : ℝ)) = univ := by
      ext z
      simp [Function.support]
    rw [hsupp, univ_inter]
    exact (jordanInterior_isOpen H).measure_pos volume
      (isConnected_jordanInterior H).nonempty
  have harea := hgreen (fun _ => 0) Complex.re contDiff_const Complex.reCLM.contDiff
  have hcurl : (fun z : ℂ => (fderiv ℝ Complex.re z) 1 -
      (fderiv ℝ (fun _ : ℂ => (0 : ℝ)) z) Complex.I) = (fun _ => (1 : ℝ)) := by
    funext z
    change (fderiv ℝ (Complex.reCLM : ℂ → ℝ) z) 1 -
      (fderiv ℝ (Function.const ℂ (0 : ℝ)) z) Complex.I = 1
    rw [Complex.reCLM.hasFDerivAt.fderiv, fderiv_const]
    simp
  rw [hcurl] at harea
  have hεArea : 0 < ε * planarFormIntegral (fun _ => 0) Complex.re
      (F ∘ unitCircleParam c r) := harea.symm ▸ htargetPos
  have hsArea : 0 < s * planarFormIntegral (fun _ => 0) Complex.re
      (F ∘ unitCircleParam c r) := by
    rw [annular_local_area_integral_eq_jacobian hU hF c hr hsource,
      ← integral_const_mul]
    apply annular_positive_ball_integral c hr
    · exact continuousOn_const.mul ((annular_complexJacobian_continuousOn hU hF).mono hsource)
    · exact fun z hz => hJ z (ball_subset_closedBall hz)
  have hεCases : ε = 1 ∨ ε = -1 := by
    rcases le_total 0 ε with h | h
    · left; simpa only [abs_of_nonneg h] using hε
    · right; rw [abs_of_nonpos h] at hε; linarith
  have hsCases : s = 1 ∨ s = -1 := by
    rcases le_total 0 s with h | h
    · left; simpa only [abs_of_nonneg h] using hs
    · right; rw [abs_of_nonpos h] at hs; linarith
  have hεs : ε = s := by
    rcases hεCases with hε | hε <;> rcases hsCases with hs | hs <;>
      simp only [hε, hs, one_mul, neg_one_mul] at hεArea hsArea ⊢ <;> linarith
  intro y hy
  obtain ⟨v, hv, hproj, hturn⟩ := hargument y hy
  exact ⟨v, hv, hproj, hturn.trans hεs⟩

theorem annular_unitCircleParam_range (c : ℂ) {r : ℝ} (hr : 0 < r) :
    range (unitCircleParam c r) = sphere c r := by
  have hscale : range (unitCircleParam c r) = range (circleMap c r) := by
    ext z
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨2 * Real.pi * t, ht⟩
    · rintro ⟨t, ht⟩
      refine ⟨t / (2 * Real.pi), ?_⟩
      change circleMap c r (2 * Real.pi * (t / (2 * Real.pi))) = z
      rw [mul_div_cancel₀ t (by positivity : (2 * Real.pi : ℝ) ≠ 0)]
      exact ht
  rw [hscale, range_circleMap, abs_of_pos hr]

/-- An actual local inverse chart and nonzero actual derivatives construct
the regular image circuit, its Schoenflies filling, and the local disk image.
No image regularity or filling-side conclusion is assumed. -/
theorem annular_local_circle_exists_regular_filling
    {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (e : OpenPartialHomeomorph ℂ ℂ) (heF : (e : ℂ → ℂ) = F)
    (c : ℂ) {r : ℝ} (hr : 0 < r)
    (hsourceE : closedBall c r ⊆ e.source) (hsourceU : closedBall c r ⊆ U)
    (hJ : ∀ z ∈ closedBall c r, (fderiv ℝ F z).det ≠ 0) :
    ∃ H : ℂ ≃ₜ ℂ, RegularJordanParametrization H (F ∘ unitCircleParam c r) ∧
      F '' sphere c r = frontier (jordanInterior H) ∧
      F '' ball c r = jordanInterior H := by
  classical
  let γ : ℝ → ℂ := F ∘ unitCircleParam c r
  have hcircle (t : ℝ) : unitCircleParam c r t ∈ closedBall c r := by
    apply sphere_subset_closedBall
    exact annular_unitCircleParam_range c hr ▸ mem_range_self t
  have hsrc : ContDiff ℝ ∞ (unitCircleParam c r) :=
    (contDiff_circleMap c r).comp (contDiff_const.mul contDiff_id)
  have hγ : ContDiff ℝ ∞ γ := by
    apply contDiff_iff_contDiffAt.mpr
    intro t
    exact (hF.contDiffAt (hU.mem_nhds (hsourceU (hcircle t)))).comp t hsrc.contDiffAt
  have hperiod : Periodic γ 1 := by
    intro t
    change F (circleMap c r (2 * Real.pi * (t + 1))) =
      F (circleMap c r (2 * Real.pi * t))
    rw [show 2 * Real.pi * (t + 1) = 2 * Real.pi * t + 2 * Real.pi by ring,
      periodic_circleMap c r]
  have hinj : InjOn γ (Ico 0 1) := by
    intro a ha b hb hab
    change F (unitCircleParam c r a) = F (unitCircleParam c r b) at hab
    have hlocal : unitCircleParam c r a = unitCircleParam c r b :=
      e.injOn (hsourceE (hcircle a)) (hsourceE (hcircle b)) (by
        simpa only [heF] using hab)
    have hzero : unitCircleParam 0 r a = unitCircleParam 0 r b := by
      rw [unitCircleParam_translate c r a, unitCircleParam_translate c r b] at hlocal
      exact add_left_cancel hlocal
    exact (unitCircleParam_regular r hr).injective ha hb hzero
  letI : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  obtain ⟨H, hfill⟩ := periodicComplexCurve_exists_filling hγ hperiod hinj
  have hfront : frontier (jordanInterior H) = range γ := by
    rw [frontier_jordanInterior, ← hfill]
  have hclosed : γ '' Icc 0 1 = range γ := by
    apply Subset.antisymm
    · rintro z ⟨t, _, ht⟩
      exact ⟨t, ht⟩
    · rintro z ⟨t, rfl⟩
      refine ⟨Int.fract t, ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩, ?_⟩
      simpa only [Int.fract, mul_one] using hperiod.sub_int_mul_eq (x := t) ⌊t⌋
  have hregular : ∀ t, deriv γ t ≠ 0 := by
    intro t
    have hFt := (hF.contDiffAt (hU.mem_nhds (hsourceU (hcircle t)))).differentiableAt
      (by simp)
    have hder : deriv γ t = (fderiv ℝ F (unitCircleParam c r t))
        (deriv (unitCircleParam c r) t) :=
      (hFt.hasFDerivAt.comp_hasDerivAt t (hsrc.differentiable (by simp) t).hasDerivAt).deriv
    have hD : Injective (fderiv ℝ F (unitCircleParam c r t)) := by
      apply LinearMap.ker_eq_bot.mp
      by_contra hker
      exact hJ _ (hcircle t) (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hker)
    have hsrcDer : deriv (unitCircleParam c r) t ≠ 0 := by
      have he : unitCircleParam c r = fun t => c + unitCircleParam 0 r t :=
        funext (unitCircleParam_translate c r)
      rw [he, deriv_const_add]
      exact (unitCircleParam_regular r hr).regular t
    intro hz
    apply hsrcDer
    apply hD
    simpa only [hder, map_zero] using hz
  have hJordan : RegularJordanParametrization H γ :=
    ⟨hγ, hperiod, hinj, hregular, hclosed.trans hfront.symm⟩
  have hboundary : F '' sphere c r = frontier (jordanInterior H) := by
    rw [hfront]
    change _ = range (F ∘ unitCircleParam c r)
    rw [range_comp, annular_unitCircleParam_range c hr]
  have hboundaryE : e '' sphere c r = frontier (jordanInterior H) := by
    simpa only [heF] using hboundary
  have himage := annular_local_image_ball_eq_jordanInterior e H c hr hsourceE hboundaryE
  refine ⟨H, hJordan, hboundary, ?_⟩
  simpa only [heF] using himage

/-- The local contribution at an actual preimage: the argument of the
actual image circle around `F(c)` turns by the sign of the actual Jacobian.
The sole injectivity object is the local inverse chart; the regular image
circuit and its filling are constructed above. -/
theorem annular_local_circle_argument_sign
    {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (e : OpenPartialHomeomorph ℂ ℂ) (heF : (e : ℂ → ℂ) = F)
    (c : ℂ) {r : ℝ} (hr : 0 < r)
    (hsourceE : closedBall c r ⊆ e.source) (hsourceU : closedBall c r ⊆ U)
    (s : ℝ) (hs : |s| = 1)
    (hJ : ∀ z ∈ closedBall c r, 0 < s * (fderiv ℝ F z).det) :
    ∃ v : ℝ → ℝ, ContDiff ℝ ∞ v ∧
      (∀ t, (v t : UnitAddCircle) =
        normalizedArgument (F (unitCircleParam c r t) - F c)) ∧
      v 1 - v 0 = s ∧
      circleFormIntegral (fun _ => 1) (centeredArgument (F c))
        (F ∘ unitCircleParam c r) = s := by
  have hJne : ∀ z ∈ closedBall c r, (fderiv ℝ F z).det ≠ 0 := by
    intro z hz heq
    have h := hJ z hz
    rw [heq, mul_zero] at h
    exact (lt_irrefl 0) h
  obtain ⟨H, hγ, _, himage⟩ :=
    annular_local_circle_exists_regular_filling hU hF e heF c hr hsourceE hsourceU hJne
  have hcenter : F c ∈ jordanInterior H := himage ▸ ⟨c, mem_ball_self hr, rfl⟩
  obtain ⟨v, hv, hproj, hturn⟩ := annular_regular_image_circle_argument_sign
    hU hF c hr hsourceU s hs hJ H hγ (F c) hcenter
  refine ⟨v, hv, hproj, hturn, ?_⟩
  have havoid : ∀ t, (F ∘ unitCircleParam c r) t ∈ {z : ℂ | z ≠ F c} := by
    intro t heq
    have ht := hγ.mem_frontier t
    rw [frontier, (jordanInterior_isOpen H).interior_eq] at ht
    exact ht.2 (heq ▸ hcenter)
  have hform := circleFormIntegral_constant_weight
    (isOpen_ne_fun continuous_id continuous_const) (smoothCircleOn_centeredArgument (F c))
    (fun _ => 1) (F ∘ unitCircleParam c r) hγ.smooth havoid
    v hv.continuous hproj 1 (fun _ _ => rfl)
  simpa only [one_mul, hturn] using hform

end
end TightVer401
