import TightVer401.DualRadialNeckGeometry
import TightVer401.ConcaveJetJoinRelative
import TightVer401.RadialCapSmoothingGlue

namespace TightVer401
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

/-- Actual radial neck attachment for ver500. Both incoming and terminal
representatives survive on open collars. Positivity is derived from strict
concavity and an unchanged positive incoming derivative. -/
theorem exists_dualRadialNeck_adapter {U : Set ℝ} (hU : IsOpen U)
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f U) {j a : ℝ}
    (_ha : 0 < a) (haj : a < j) (hjU : j ∈ U)
    (hpos : 0 < deriv f j) (hneg : ∀ x ∈ U, deriv (deriv f) x < 0) :
    let B := dualRadialNeckCoefficient (deriv f j) j a
    let C := dualRadialNeckConstant (f j) (deriv f j) j a
    ∃ (b c d : ℝ) (F : ℝ → ℝ), j < b ∧ b ∈ U ∧ c ∈ Ioo a j ∧ d ∈ Ioo j b ∧
      Ioo d b ⊆ U ∧
      ContDiffOn ℝ ∞ F (Ioo a b) ∧
      (∀ r ∈ Ioo a b, 0 < deriv F r ∧ deriv (deriv F) r < 0) ∧
      EqOn F (dualRadialNeck C B a) (Ioo a c) ∧
      EqOn F f (Ioo d b) ∧ Tendsto (deriv F) (𝓝[>] a) atTop := by
  dsimp only
  let B := dualRadialNeckCoefficient (deriv f j) j a
  let C := dualRadialNeckConstant (f j) (deriv f j) j a
  let neck := dualRadialNeck C B a
  have hB : 0 < B := dualRadialNeckCoefficient_pos hpos haj
  have hn : ContDiffOn ℝ ∞ neck (Ioi a) := dualRadialNeck_contDiffOn C a hB
  have hnneg : ∀ x ∈ Ioi a, deriv (deriv neck) x < 0 :=
    fun x hx => (dualRadialNeck_strict_derivative_signs C a hB hx).2
  have hdf := (contDiffOn_infty_iff_deriv_of_isOpen hU).mp hf |>.2
  have hdfj : ContinuousAt (deriv f) j :=
    (hdf.contDiffAt (hU.mem_nhds hjU)).continuousAt
  have hnear : {x : ℝ | 0 < deriv f x} ∈ 𝓝 j :=
    hdfj.eventually (Ioi_mem_nhds hpos)
  obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem ((hU.inter isOpen_Ioi).mem_nhds ⟨hjU, haj⟩) hnear)
  have hballU : ball j η ⊆ U := fun _ hx => (hball hx).1.1
  have hballA : ball j η ⊆ Ioi a := fun _ hx => (hball hx).1.2
  have hballpos : ∀ x ∈ ball j η, 0 < deriv f x := fun _ hx => (hball hx).2
  have hjball : j ∈ ball j η := by simp [hη]
  have hjV : j ∈ ball j (η / 4) := by simp [show 0 < η / 4 by positivity]
  have hjet := dualRadialNeck_matches_first_jet (value := f j) hpos haj
  obtain ⟨q, hq, heLeft, heRight, hqneg⟩ := exists_concave_first_jet_join
    isOpen_ball isOpen_ball hjball hjV (hn.mono hballA) (hf.mono hballU)
    hjet.1 hjet.2 (fun x hx => hnneg x (hballA hx))
    (fun x hx => hneg x (hballU hx))
  let c := j - η / 2
  let b := j + η / 2
  let d := j + η / 4
  let R := j + 3 * η / 4
  have hcball : c ∈ ball j η := by
    rw [Real.ball_eq_Ioo]; dsimp [c]; constructor <;> linarith
  have hca : a < c := hballA hcball
  have hcj : c < j := by dsimp [c]; linarith
  have hjb : j < b := by dsimp [b]; linarith
  have hbR : b < R := by dsimp [b, R]; linarith
  have hdb : d ∈ Ioo j b := by dsimp [d, b]; constructor <;> linarith
  have hcq : neck =ᶠ[𝓝 c] q := by
    have hcI : c ∈ Ioo (j - 3 * η / 4) (j - η / 4) := by
      dsimp [c]; constructor <;> linarith
    filter_upwards [isOpen_Ioo.mem_nhds hcI] with x hx
    symm
    apply heLeft
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [Real.ball_eq_Ioo]; constructor <;> linarith [hx.1, hx.2]
    · change x ≤ j; linarith [hx.2]
    · rw [Real.ball_eq_Ioo]
      intro h
      linarith [h.1, hx.2]
  let F := radialCapSmoothingGlue c neck q
  have hleft (x) (hx : x ∈ Ioo a R) (_hxc : x ≤ c) : x ∈ Ioi a := hx.1
  have hright (x) (hx : x ∈ Ioo a R) (hcx : c ≤ x) : x ∈ ball j η := by
    rw [Real.ball_eq_Ioo]
    dsimp [c, R] at hx hcx
    constructor <;> linarith [hx.2]
  have hF : ContDiffOn ℝ ∞ F (Ioo a R) :=
    radialCapSmoothingGlue_contDiffOn isOpen_Ioi isOpen_ball neck q hn hq hcq hleft hright
  have hFneg : ∀ x ∈ Ioo a R, deriv (deriv F) x < 0 :=
    radialCapSmoothingGlue_second_negative neck q hcq hleft hright hnneg hqneg
  have hrightEq (x) (hx : x ∈ Ioo d R) : F x = f x := by
    have hcx : c < x := by dsimp [c, d] at hx ⊢; linarith [hx.1]
    change (if x < c then neck x else q x) = f x
    rw [if_neg (not_lt.mpr hcx.le)]
    apply heRight
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [Real.ball_eq_Ioo]; dsimp [d, R] at hx; constructor <;> linarith [hx.1, hx.2]
    · change j ≤ x; dsimp [d] at hx; linarith [hx.1]
    · rw [Real.ball_eq_Ioo]
      intro h
      dsimp [d] at hx
      linarith [h.2, hx.1]
  have hbI : b ∈ Ioo d R := ⟨hdb.2, hbR⟩
  have hbEq : F =ᶠ[𝓝 b] f := by
    filter_upwards [isOpen_Ioo.mem_nhds hbI] with x hx
    exact hrightEq x hx
  have hbball : b ∈ ball j η := by
    rw [Real.ball_eq_Ioo]; dsimp [b]; constructor <;> linarith
  have hFbpos : 0 < deriv F b := by
    rw [hbEq.deriv_eq]
    exact hballpos b hbball
  have hF₁ := (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioo).mp hF |>.2
  have hanti := strictAntiOn_of_deriv_neg (convex_Ioo a R) hF₁.continuousOn
    (fun x hx => hFneg x (interior_subset hx))
  have hFpos : ∀ x ∈ Ioo a b, 0 < deriv F x := by
    intro x hx
    have hbDomain : b ∈ Ioo a R := ⟨haj.trans hjb, hbR⟩
    have h := hanti ⟨hx.1, hx.2.trans hbR⟩ hbDomain hx.2
    exact hFbpos.trans h
  have hFneck : EqOn F neck (Ioo a c) := by
    intro x hx
    exact if_pos hx.2
  have hderivEq : deriv F =ᶠ[𝓝[>] a] deriv neck := by
    have hlow : ∀ᶠ x in 𝓝[>] a, x < c :=
      (eventually_lt_nhds hca).filter_mono nhdsWithin_le_nhds
    filter_upwards [hlow] with x hx
    have heq : F =ᶠ[𝓝 x] neck := by
      filter_upwards [eventually_lt_nhds hx] with y hy
      exact if_pos hy
    exact heq.deriv_eq
  have hcollarU : Ioo d b ⊆ U := by
    intro x hx
    apply hballU
    rw [Real.ball_eq_Ioo]
    dsimp [d, b] at hx
    constructor <;> linarith [hx.1, hx.2]
  refine ⟨b, c, d, F, hjb, hballU hbball, ⟨hca, hcj⟩, hdb, hcollarU,
    hF.mono (fun x hx => ⟨hx.1, hx.2.trans hbR⟩), ?_, hFneck, ?_, ?_⟩
  · intro x hx
    exact ⟨hFpos x hx, hFneg x ⟨hx.1, hx.2.trans hbR⟩⟩
  · intro x hx
    exact hrightEq x ⟨hx.1, hx.2.trans hbR⟩
  · exact (dualRadialNeck_deriv_tendsto_atTop C a hB).congr' hderivEq.symm

end
end TightVer401
