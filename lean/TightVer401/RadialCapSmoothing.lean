import TightVer401.ConcaveJetJoinRelative
import TightVer401.RadialCapSmoothingGlue
import TightVer401.RadialCapInverse

namespace TightVer401
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

theorem radialCap_disc_on_symmetric_interval {a R x : ℝ} (_ha : 0 < a)
    (hx : x ∈ Ioo (R - a) (R + a)) : 0 < a ^ 2 - (R - x) ^ 2 := by
  have h1 : 0 < a - (R - x) := by linarith [hx.1]
  have h2 : 0 < a + (R - x) := by linarith [hx.2]
  nlinarith [mul_pos h1 h2]

theorem radialCap_second_negative_on_disc {C R a : ℝ} (ha : 0 < a) :
    ∀ x ∈ {x : ℝ | 0 < a ^ 2 - (R - x) ^ 2},
      deriv (deriv (radialCap C R a)) x < 0 := by
  intro x hx
  rw [radialCap_second_deriv C R a hx]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (sq_pos_of_pos ha))
    (pow_pos (Real.sqrt_pos.mpr hx) 3)

/-- A finite actual cap with a relatively smoothed incoming seam. The incoming
representative is assumed smooth only on its given open neighborhood. -/
theorem exists_radialCap_smoothing {U : Set ℝ} (hU : IsOpen U)
    {k₀ : ℝ → ℝ} (hk₀ : ContDiffOn ℝ ∞ k₀ U) {j d : ℝ}
    (hj : 0 < j) (hjU : j ∈ U) (hd : 0 < d)
    (hs : 0 < deriv k₀ j) (hneg : ∀ x ∈ U, deriv (deriv k₀) x < 0) :
    let a := radialCapRadius d (deriv k₀ j)
    let C := k₀ j - d / deriv k₀ j
    let R := j + d
    ∃ (u e : ℝ) (k : ℝ → ℝ), 0 < u ∧ u < j ∧ 0 < e ∧
      ContDiffOn ℝ ∞ k (Ioo u (R + e)) ∧
      (∀ x ∈ Ioo u (R + e), deriv (deriv k) x < 0) ∧
      (∀ x ∈ Ioo u R, 0 < deriv k x) ∧
      deriv k R = 0 ∧ deriv (deriv k) R = -1 / a ∧
      (∃ v ∈ Ioo u j, EqOn k k₀ (Ioo u v)) ∧
      k =ᶠ[𝓝 R] radialCap C R a := by
  dsimp only
  let s := deriv k₀ j
  let a := radialCapRadius d s
  let C := k₀ j - d / s
  let R := j + d
  let cap := radialCap C R a
  let D : Set ℝ := {x | 0 < a ^ 2 - (R - x) ^ 2}
  have ha : 0 < a := radialCapRadius_pos hd hs
  have hD : IsOpen D := isOpen_lt continuous_const
    (continuous_const.sub ((continuous_const.sub continuous_id).pow 2))
  have hjD : j ∈ D := radialCap_disc_positive hd hs ⟨le_rfl, by linarith⟩
  have had : d < a := by
    have hb := hjD
    change 0 < a ^ 2 - (j + d - j) ^ 2 at hb
    nlinarith
  have hcap : ContDiffOn ℝ ∞ cap D := radialCap_contDiffOn C R a
  have hcapneg : ∀ x ∈ D, deriv (deriv cap) x < 0 := radialCap_second_negative_on_disc ha
  have hW : IsOpen (U ∩ D ∩ Iio R ∩ Ioi 0) :=
    ((hU.inter hD).inter isOpen_Iio).inter isOpen_Ioi
  have hjW : j ∈ U ∩ D ∩ Iio R ∩ Ioi 0 :=
    ⟨⟨⟨hjU, hjD⟩, by change j < j + d; linarith⟩, hj⟩
  obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hjW)
  have hballU : ball j η ⊆ U := fun _ hx => (hball hx).1.1.1
  have hballD : ball j η ⊆ D := fun _ hx => (hball hx).1.1.2
  have hjball : j ∈ ball j η := by simp [hη]
  have hjV : j ∈ ball j (η / 4) := by simp [show 0 < η / 4 by positivity]
  have hjet := radialCap_matches_first_jet (j := j) (value := k₀ j) hd hs
  obtain ⟨q, hq, heLeft, heRight, hqneg⟩ := exists_concave_first_jet_join
    isOpen_ball isOpen_ball hjball hjV (hk₀.mono hballU) (hcap.mono hballD)
    hjet.1.symm hjet.2.symm (fun x hx => hneg x (hballU hx))
    (fun x hx => hcapneg x (hballD hx))
  let u := j - η / 2
  let B := j + η / 2
  let e := a / 2
  have huBall : u ∈ ball j η := by rw [Real.ball_eq_Ioo]; dsimp [u]; constructor <;> linarith
  have hBBall : B ∈ ball j η := by rw [Real.ball_eq_Ioo]; dsimp [B]; constructor <;> linarith
  have hu : 0 < u := (hball huBall).2
  have huj : u < j := by dsimp [u]; linarith
  have hBR : B < R := (hball hBBall).1.2
  have he : 0 < e := half_pos ha
  have hBq : q =ᶠ[𝓝 B] cap := by
    have hBI : B ∈ Ioo (j + η / 4) (j + 3 * η / 4) := by dsimp [B]; constructor <;> linarith
    filter_upwards [isOpen_Ioo.mem_nhds hBI] with x hx
    apply heRight
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [Real.ball_eq_Ioo]; constructor <;> linarith [hx.1, hx.2]
    · change j ≤ x; linarith [hx.1]
    · rw [Real.ball_eq_Ioo]
      intro h
      linarith [h.2, hx.1]
  let k := radialCapSmoothingGlue B q cap
  have hleft (x) (hx : x ∈ Ioo u (R + e)) (hxB : x ≤ B) : x ∈ ball j η := by
    rw [Real.ball_eq_Ioo]
    dsimp [u, B] at hx hxB
    constructor <;> linarith [hx.1]
  have hright (x) (hx : x ∈ Ioo u (R + e)) (hBx : B ≤ x) : x ∈ D := by
    apply radialCap_disc_on_symmetric_interval ha
    dsimp [B, R, e] at hx hBx ⊢
    constructor <;> linarith [hx.2]
  have hk : ContDiffOn ℝ ∞ k (Ioo u (R + e)) :=
    radialCapSmoothingGlue_contDiffOn isOpen_ball hD q cap hq hcap hBq hleft hright
  have hkneg : ∀ x ∈ Ioo u (R + e), deriv (deriv k) x < 0 :=
    radialCapSmoothingGlue_second_negative q cap hBq hleft hright hqneg hcapneg
  have hkcap : k =ᶠ[𝓝 R] cap := (eventually_gt_nhds hBR).mono (fun x hx => by
    simp [k, radialCapSmoothingGlue, not_lt.mpr hx.le])
  have hend := radialCap_endpoint_derivatives (C := C) (R := R) ha
  have hkR : deriv k R = 0 := hkcap.deriv_eq.trans hend.1
  have hkR₂ : deriv (deriv k) R = -1 / a := hkcap.deriv.deriv_eq.trans hend.2
  refine ⟨u, e, k, hu, huj, he, hk, hkneg,
    radialCapSmoothing_deriv_positive_before_endpoint he (huj.trans (by change j < j + d; linarith)) hk hkneg hkR,
    hkR, hkR₂, ?_, hkcap⟩
  refine ⟨j - η / 4, ⟨by dsimp [u]; linarith, by linarith⟩, ?_⟩
  intro x hx
  have hxB : x < B := by dsimp [B]; linarith [hx.2]
  change (if x < B then q x else cap x) = k₀ x
  rw [if_pos hxB]
  apply heLeft
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [Real.ball_eq_Ioo]; dsimp [u] at hx; constructor <;> linarith [hx.1, hx.2]
  · change x ≤ j; linarith [hx.2]
  · rw [Real.ball_eq_Ioo]
    intro h
    linarith [h.1, hx.2]

end
end TightVer401
