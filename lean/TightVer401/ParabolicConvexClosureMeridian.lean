import TightVer401.ParabolicConvexClosureMeridianGerms
import TightVer401.ConcaveJetJoinRelative
import TightVer401.RadialCapSmoothingGlue
import Mathlib.Analysis.Convex.Deriv

/-! Construct the even meridian of ver500 convex closure from ordinary positive
parameters. Matching first jets are proved for an actual central quadratic and
the retained square-root germ; the relative concave join preserves their full
outside germs. Endpoint smoothness in height coordinates is not asserted. -/
namespace TightVer401
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

/-- The even central quadratic tangent to the upper germ at h/2. -/
def parabolicClosureCentralQuadratic (RN mu h : ℝ) : ℝ → ℝ :=
  let g := parabolicClosureUpperRadius RN mu h
  parabolicClosureJetQuadratic (h / 2) (g (h / 2)) (-deriv g (h / 2) / (h / 2))

 theorem parabolicClosureCentralQuadratic_contDiff (RN mu h : ℝ) :
    ContDiff ℝ ∞ (parabolicClosureCentralQuadratic RN mu h) :=
  parabolicClosureJetQuadratic_contDiff _ _ _

@[simp] theorem parabolicClosureCentralQuadratic_even (RN mu h z : ℝ) :
    parabolicClosureCentralQuadratic RN mu h (-z) =
      parabolicClosureCentralQuadratic RN mu h z :=
  parabolicClosureJetQuadratic_even _ _ _ _

 theorem parabolicClosureCentralQuadratic_second_neg (RN mu h : ℝ)
    (hmu : 0 < mu) (hh : 0 < h) (z : ℝ) :
    deriv (deriv (parabolicClosureCentralQuadratic RN mu h)) z < 0 := by
  change deriv (deriv (parabolicClosureJetQuadratic _ _ _)) z < 0
  rw [parabolicClosureJetQuadratic_second]
  exact neg_neg_of_pos (div_pos
    (neg_pos.mpr (parabolicClosureUpperRadius_deriv_neg RN mu h hmu (by linarith)))
    (half_pos hh))

/-- A genuine smooth upper-half meridian, quadratic near zero and exactly
square-root near the upper endpoint. The endpoint itself remains in its germ. -/
theorem exists_parabolicClosure_half_meridian (RN mu h : ℝ)
    (hmu : 0 < mu) (hh : 0 < h) :
    ∃ f : ℝ → ℝ, ContDiffOn ℝ ∞ f (Iio h) ∧
      (∀ z ∈ Iio h, deriv (deriv f) z < 0) ∧
      EqOn f (parabolicClosureCentralQuadratic RN mu h) (Iio (3 * h / 8)) ∧
      EqOn f (parabolicClosureUpperRadius RN mu h) (Ici (5 * h / 8)) := by
  let j := h / 2
  let η := h / 4
  let A := 3 * h / 8
  let B := 5 * h / 8
  let R := 11 * h / 16
  let Q := parabolicClosureCentralQuadratic RN mu h
  let g := parabolicClosureUpperRadius RN mu h
  have hη : 0 < η := by dsimp [η]; positivity
  have hj : 0 < j := by dsimp [j]; positivity
  have hjh : j < h := by dsimp [j]; linarith
  have hA : 0 < A := by dsimp [A]; positivity
  have hAB : A < B := by dsimp [A, B]; linarith
  have hBR : B < R := by dsimp [B, R]; linarith
  have hBh : B < h := by dsimp [B]; linarith
  have hballh : ball j η ⊆ Iio h := by
    intro x hx
    rw [Real.ball_eq_Ioo] at hx
    dsimp [j, η] at hx
    change x < h
    linarith [hx.2]
  have hQ : ContDiff ℝ ∞ Q := parabolicClosureCentralQuadratic_contDiff RN mu h
  have hg : ContDiffOn ℝ ∞ g (Iio h) := parabolicClosureUpperRadius_contDiffOn RN mu h hmu
  have hQneg : ∀ x : ℝ, deriv (deriv Q) x < 0 :=
    parabolicClosureCentralQuadratic_second_neg RN mu h hmu hh
  have hgneg : ∀ x ∈ Iio h, deriv (deriv g) x < 0 :=
    fun x hx => parabolicClosureUpperRadius_second_neg RN mu h hmu hx
  have hjet : Q j = g j ∧ deriv Q j = deriv g j :=
    parabolicClosure_quadratic_firstJet (RN := RN) (mu := mu) (h := h) hj
  have hjball : j ∈ ball j η := mem_ball_self hη
  have hjV : j ∈ ball j (η / 4) := mem_ball_self (by positivity)
  obtain ⟨q, hq, heLeft, heRight, hqneg⟩ := exists_concave_first_jet_join
    isOpen_ball isOpen_ball hjball hjV hQ.contDiffOn (hg.mono hballh)
    hjet.1 hjet.2 (fun x _ => hQneg x) (fun x hx => hgneg x (hballh hx))
  have hAq : Q =ᶠ[𝓝 A] q := by
    have hAI : A ∈ Ioo (j - 3 * η / 4) (j - η / 4) := by
      dsimp [A, j, η]; constructor <;> linarith
    filter_upwards [isOpen_Ioo.mem_nhds hAI] with x hx
    symm
    apply heLeft
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [Real.ball_eq_Ioo]; constructor <;> linarith [hx.1, hx.2]
    · change x ≤ j; linarith [hx.2]
    · rw [Real.ball_eq_Ioo]
      intro hv
      linarith [hv.1, hx.2]
  let p := radialCapSmoothingGlue A Q q
  have hleft (x : ℝ) (_hx : x ∈ Iio R) (_hxa : x ≤ A) : x ∈ (univ : Set ℝ) := mem_univ x
  have hright (x : ℝ) (hx : x ∈ Iio R) (hax : A ≤ x) : x ∈ ball j η := by
    rw [Real.ball_eq_Ioo]
    change x < R at hx
    dsimp [A, R, j, η] at hax hx ⊢
    constructor <;> linarith
  have hp : ContDiffOn ℝ ∞ p (Iio R) :=
    radialCapSmoothingGlue_contDiffOn isOpen_univ isOpen_ball Q q hQ.contDiffOn hq hAq hleft hright
  have hpneg : ∀ x ∈ Iio R, deriv (deriv p) x < 0 :=
    radialCapSmoothingGlue_second_negative Q q hAq hleft hright
      (fun x _ => hQneg x) hqneg
  have hBg : p =ᶠ[𝓝 B] g := by
    have hBI : B ∈ Ioo (j + η / 4) (j + 3 * η / 4) := by
      dsimp [B, j, η]; constructor <;> linarith
    filter_upwards [isOpen_Ioo.mem_nhds hBI] with x hx
    have hAx : A < x := by dsimp [A, j, η] at hx ⊢; linarith [hx.1]
    change (if x < A then Q x else q x) = g x
    rw [if_neg (not_lt.mpr hAx.le)]
    apply heRight
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [Real.ball_eq_Ioo]; constructor <;> linarith [hx.1, hx.2]
    · change j ≤ x; linarith [hx.1]
    · rw [Real.ball_eq_Ioo]
      intro hv
      linarith [hv.2, hx.1]
  let f := radialCapSmoothingGlue B p g
  have hleft' (x : ℝ) (_hx : x ∈ Iio h) (hxb : x ≤ B) : x ∈ Iio R :=
    hxb.trans_lt hBR
  have hright' (x : ℝ) (hx : x ∈ Iio h) (_hbx : B ≤ x) : x ∈ Iio h := hx
  refine ⟨f,
    radialCapSmoothingGlue_contDiffOn isOpen_Iio isOpen_Iio p g hp hg hBg hleft' hright',
    radialCapSmoothingGlue_second_negative p g hBg hleft' hright' hpneg hgneg, ?_, ?_⟩
  · intro x hx
    have hxA : x < A := hx
    have hxB : x < B := hxA.trans hAB
    simp [f, p, radialCapSmoothingGlue, hxA, hxB, Q]
  · intro x hx
    have hxB : B ≤ x := hx
    simp [f, radialCapSmoothingGlue, not_lt.mpr hxB, g]

/-- Even reflection; the central quadratic supplies the actual smooth zero germ. -/
def parabolicClosureEvenReflect (f : ℝ → ℝ) (z : ℝ) : ℝ :=
  if z < 0 then f (-z) else f z

@[simp] theorem parabolicClosureEvenReflect_even (f : ℝ → ℝ) (z : ℝ) :
    parabolicClosureEvenReflect f (-z) = parabolicClosureEvenReflect f z := by
  by_cases hz : z < 0
  · have hn : ¬ -z < 0 := by linarith
    simp [parabolicClosureEvenReflect, hz, hn]
  · by_cases hzero : z = 0
    · simp [hzero]
    · have hzpos : 0 < z := lt_of_le_of_ne (not_lt.mp hz) (Ne.symm hzero)
      have hn : -z < 0 := by linarith
      simp [parabolicClosureEvenReflect, hz, hn]

 theorem parabolicClosureEvenReflect_zero_germ {RN mu h : ℝ} (hh : 0 < h)
    {f : ℝ → ℝ}
    (hf : EqOn f (parabolicClosureCentralQuadratic RN mu h) (Iio (3 * h / 8))) :
    parabolicClosureEvenReflect f =ᶠ[𝓝 0] parabolicClosureCentralQuadratic RN mu h := by
  have hA : 0 < 3 * h / 8 := by positivity
  have hzero : (0 : ℝ) ∈ Ioo (-(3 * h / 8)) (3 * h / 8) := ⟨by linarith, hA⟩
  filter_upwards [isOpen_Ioo.mem_nhds hzero] with z hz
  by_cases hneg : z < 0
  · rw [parabolicClosureEvenReflect, if_pos hneg, hf (show -z < 3 * h / 8 by linarith [hz.1])]
    exact parabolicClosureCentralQuadratic_even RN mu h z
  · rw [parabolicClosureEvenReflect, if_neg hneg, hf hz.2]

/-- Construct the even radius solely from RN, mu, h > 0, with literal closed
endpoint collars. Positivity and closed strict concavity are derived. -/
theorem exists_even_parabolic_convex_meridian (RN mu h : ℝ)
    (_hRN : 0 < RN) (hmu : 0 < mu) (hh : 0 < h) :
    ∃ r0 : ℝ → ℝ,
      ContinuousOn r0 (Icc (-h) h) ∧
      ContDiffOn ℝ ∞ r0 (Ioo (-h) h) ∧
      (∀ z ∈ Ioo (-h) h, deriv (deriv r0) z < 0) ∧
      StrictConcaveOn ℝ (Icc (-h) h) r0 ∧
      r0 (-h) = RN ∧ r0 h = RN ∧
      (∀ z ∈ Ioo (-h) h, RN < r0 z) ∧
      (∃ δ ∈ Ioo 0 h,
        EqOn r0 (fun z => RN + Real.sqrt (2 * mu * (h + z))) (Icc (-h) (-h + δ)) ∧
        EqOn r0 (fun z => RN + Real.sqrt (2 * mu * (h - z))) (Icc (h - δ) h)) ∧
      (∀ z ∈ Icc (-h) h, r0 (-z) = r0 z) := by
  obtain ⟨f, hf, hfneg, hfQ, hfg⟩ := exists_parabolicClosure_half_meridian RN mu h hmu hh
  let r0 := parabolicClosureEvenReflect f
  have hzero : r0 =ᶠ[𝓝 0] parabolicClosureCentralQuadratic RN mu h :=
    parabolicClosureEvenReflect_zero_germ hh hfQ
  have hlocal_pos {z : ℝ} (hz : 0 < z) : r0 =ᶠ[𝓝 z] f := by
    filter_upwards [eventually_gt_nhds hz] with x hx
    exact if_neg (not_lt.mpr hx.le)
  have hlocal_neg {z : ℝ} (hz : z < 0) : r0 =ᶠ[𝓝 z] (fun x => f (-x)) := by
    filter_upwards [eventually_lt_nhds hz] with x hx
    exact if_pos hx
  have hrAt {z : ℝ} (hz : z ∈ Ioo (-h) h) : ContDiffAt ℝ ∞ r0 z := by
    rcases lt_trichotomy z 0 with hn | he | hp
    · have hnf : ContDiffAt ℝ ∞ f (-z) :=
        (hf (-z) (show -z < h by linarith [hz.1])).contDiffAt
          (isOpen_Iio.mem_nhds (show -z < h by linarith [hz.1]))
      exact (hnf.comp z contDiffAt_id.neg).congr_of_eventuallyEq (hlocal_neg hn)
    · subst z
      exact (parabolicClosureCentralQuadratic_contDiff RN mu h).contDiffAt.congr_of_eventuallyEq hzero
    · exact ((hf z hz.2).contDiffAt (isOpen_Iio.mem_nhds hz.2)).congr_of_eventuallyEq (hlocal_pos hp)
  have hr : ContDiffOn ℝ ∞ r0 (Ioo (-h) h) := fun z hz => (hrAt hz).contDiffWithinAt
  have hrneg : ∀ z ∈ Ioo (-h) h, deriv (deriv r0) z < 0 := by
    intro z hz
    rcases lt_trichotomy z 0 with hn | he | hp
    · rw [(hlocal_neg hn).deriv.deriv_eq, parabolicClosure_secondDeriv_reflect]
      exact hfneg (-z) (show -z < h by linarith [hz.1])
    · subst z
      rw [hzero.deriv.deriv_eq]
      exact parabolicClosureCentralQuadratic_second_neg RN mu h hmu hh 0
    · rw [(hlocal_pos hp).deriv.deriv_eq]
      exact hfneg z hz.2
  have hrupper : EqOn r0 (parabolicClosureUpperRadius RN mu h) (Icc (h - h / 4) h) := by
    intro z hz
    have hzpos : 0 < z := by linarith [hz.1]
    have hzB : 5 * h / 8 ≤ z := by linarith [hz.1]
    change (if z < 0 then f (-z) else f z) = _
    rw [if_neg (not_lt.mpr hzpos.le)]
    exact hfg hzB
  have hrlower : EqOn r0 (fun z => RN + Real.sqrt (2 * mu * (h + z)))
      (Icc (-h) (-h + h / 4)) := by
    intro z hz
    have hnz : -z ∈ Icc (h - h / 4) h := ⟨by linarith [hz.2], by linarith [hz.1]⟩
    have he := hrupper hnz
    change parabolicClosureEvenReflect f (-z) = parabolicClosureUpperRadius RN mu h (-z) at he
    rw [parabolicClosureEvenReflect_even] at he
    simpa [parabolicClosureUpperRadius, r0] using he
  have hupperGerm : r0 =ᶠ[𝓝 h] parabolicClosureUpperRadius RN mu h := by
    filter_upwards [eventually_gt_nhds (show 5 * h / 8 < h by linarith)] with z hz
    have hzpos : 0 < z := by linarith
    change (if z < 0 then f (-z) else f z) = _
    rw [if_neg (not_lt.mpr hzpos.le)]
    exact hfg hz.le
  have hlowerGerm : r0 =ᶠ[𝓝 (-h)] (fun z => parabolicClosureUpperRadius RN mu h (-z)) := by
    filter_upwards [eventually_lt_nhds (show -h < -(5 * h / 8) by linarith)] with z hz
    have hzneg : z < 0 := by linarith
    change (if z < 0 then f (-z) else f z) = _
    rw [if_pos hzneg]
    exact hfg (show 5 * h / 8 ≤ -z by linarith)
  have hcont : ContinuousOn r0 (Icc (-h) h) := by
    intro z hz
    by_cases hl : z = -h
    · subst z
      have hc : ContinuousAt (fun x => parabolicClosureUpperRadius RN mu h (-x)) (-h) :=
        ((parabolicClosureUpperRadius_continuous RN mu h).comp continuous_neg).continuousAt
      exact (hc.congr_of_eventuallyEq hlowerGerm).continuousWithinAt
    by_cases hu : z = h
    · subst z
      have hc : ContinuousAt (parabolicClosureUpperRadius RN mu h) h :=
        (parabolicClosureUpperRadius_continuous RN mu h).continuousAt
      exact (hc.congr_of_eventuallyEq hupperGerm).continuousWithinAt
    · exact (hrAt ⟨lt_of_le_of_ne hz.1 (Ne.symm hl), lt_of_le_of_ne hz.2 hu⟩).continuousAt.continuousWithinAt
  have hendUpper : r0 h = RN := by
    rw [hupperGerm.self_of_nhds, parabolicClosureUpperRadius_endpoint]
  have hendLower : r0 (-h) = RN := by
    change parabolicClosureEvenReflect f (-h) = RN
    rw [parabolicClosureEvenReflect_even]
    exact hendUpper
  have hconc : StrictConcaveOn ℝ (Icc (-h) h) r0 :=
    strictConcaveOn_of_deriv2_neg (convex_Icc (-h) h) hcont (by
      simpa only [interior_Icc, Function.iterate_succ_apply, Function.iterate_zero_apply] using hrneg)
  have hpos : ∀ z ∈ Ioo (-h) h, RN < r0 z := by
    intro z hz
    have hends : -h < h := by linarith
    have hsegment : z ∈ openSegment ℝ (-h) h := by
      rw [openSegment_eq_Ioo hends]
      exact hz
    have ht := hconc.lt_on_openSegment ⟨le_rfl, hends.le⟩ ⟨hends.le, le_rfl⟩ hends.ne hsegment
    simpa only [hendLower, hendUpper, min_self] using ht
  refine ⟨r0, hcont, hr, hrneg, hconc, hendLower, hendUpper, hpos, ?_, ?_⟩
  · refine ⟨h / 4, ⟨by positivity, by linarith⟩, hrlower, ?_⟩
    exact hrupper
  · intro z _
    exact parabolicClosureEvenReflect_even f z

end
end TightVer401



