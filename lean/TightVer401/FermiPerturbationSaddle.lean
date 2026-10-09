import TightVer401.FermiSupportPositiveGraph
import TightVer401.FermiPerturbationCollar
import Mathlib.Topology.MetricSpace.Thickening

namespace TightVer401
noncomputable section
open Set Filter Metric OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

theorem fermiSupport_const_mul {J : Coord → ℝ} (hJ : ContDiff ℝ ∞ J)
    (ε : ℝ) (κ : ℝ → ℝ) (p : Coord) :
    fermiSupportL κ (fun q => ε * J q) p = ε * fermiSupportL κ J p ∧
    fermiSupportM κ (fun q => ε * J q) p = ε * fermiSupportM κ J p ∧
    fermiSupportN (fun q => ε * J q) p = ε * fermiSupportN J p := by
  have h1 (i : Fin 2) : coordPartial i (fun q => ε * J q) =
      (fun q => ε * coordPartial i J q) :=
    funext fun q => fermiCoordinatePartial_const_mul (hJ.differentiable (by simp) q) ε i
  have h2 (i j : Fin 2) : coordPartial i (coordPartial j (fun q => ε * J q)) p =
      ε * coordPartial i (coordPartial j J) p := by
    rw [h1 j]
    exact fermiCoordinatePartial_const_mul
      ((fermiCoordinatePartial_contDiff hJ j).differentiable (by simp) p) ε i
  simp only [fermiSupportL, fermiSupportM, fermiSupportN]
  rw [h2 0 0, h2 0 1, h2 1 1, h1 0, h1 1]
  constructor
  · ring
  · constructor <;> ring

theorem compact_uniform_negative_parameter {U K : Set Coord} {D : ℝ × Coord → ℝ}
    (hU : IsOpen U) (hD : ContinuousOn D (univ ×ˢ U))
    (hK : IsCompact K) (hKU : K ⊆ U) (hneg : ∀ p ∈ K, D (0, p) < 0) :
    ∃ e > 0, ∀ ε : ℝ, |ε| < e → ∀ p ∈ K, D (ε, p) < 0 := by
  let C := (fun p : Coord => ((0 : ℝ), p)) '' K
  have hC : IsCompact C := hK.image (continuous_const.prodMk continuous_id)
  let V := (univ ×ˢ U) ∩ D ⁻¹' Iio 0
  have hV : IsOpen V := hD.isOpen_inter_preimage (isOpen_univ.prod hU) isOpen_Iio
  have hCV : C ⊆ V := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨⟨mem_univ _, hKU hp⟩, hneg p hp⟩
  obtain ⟨e, he, hthick⟩ := hC.exists_cthickening_subset_open hV hCV
  refine ⟨e, he, fun ε hε p hp => ?_⟩
  have hm : (ε, p) ∈ V := by
    apply hthick
    apply mem_cthickening_of_dist_le (ε, p) (0, p) e C
    · exact ⟨p, hp, rfl⟩
    · simpa only [dist_prod_same_right, Real.dist_eq, sub_zero] using hε.le
  exact hm.2

theorem exists_fermiSupport_saddle_threshold {κ : ℝ → ℝ} {H J : Coord → ℝ}
    {U K : Set Coord} (hκ : ContDiff ℝ ∞ κ) (hU : IsOpen U)
    (hH : ContDiffOn ℝ ∞ H U) (hJ : ContDiff ℝ ∞ J)
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hscale : ∀ p ∈ U, fermiNormalScale κ p ≠ 0)
    (hdet : ∀ p ∈ K, (sphereSupportTensor (fermiMetric (fermiNormalScale κ)) H p).det < 0) :
    ∃ e > 0, ∀ ε : ℝ, |ε| < e → ∀ p ∈ K,
      (sphereSupportTensor (fermiMetric (fermiNormalScale κ))
        (fun q => H q + ε * J q) p).det < 0 := by
  have hHc := fermiSupport_contDiffOn hκ hU hH hscale
  have hJc := fermiSupport_contDiffOn hκ hU hJ.contDiffOn hscale
  let D : ℝ × Coord → ℝ := fun x =>
    (fermiSupportL κ H x.2 + x.1 * fermiSupportL κ J x.2) *
      (fermiSupportN H x.2 + x.1 * fermiSupportN J x.2) -
      (fermiSupportM κ H x.2 + x.1 * fermiSupportM κ J x.2)^2
  have hc (F : Coord → ℝ) (hF : ContDiffOn ℝ ∞ F U) :
      ContinuousOn (fun x : ℝ × Coord => F x.2) (univ ×ˢ U) :=
    hF.continuousOn.comp continuous_snd.continuousOn (fun _ hx => hx.2)
  have hD : ContinuousOn D (univ ×ˢ U) :=
    ((hc _ hHc.1).add (continuous_fst.continuousOn.mul (hc _ hJc.1))).mul
      ((hc _ hHc.2.2).add (continuous_fst.continuousOn.mul (hc _ hJc.2.2))) |>.sub
        (((hc _ hHc.2.1).add (continuous_fst.continuousOn.mul (hc _ hJc.2.1))).pow 2)
  have hactual (ε : ℝ) (p : Coord) (hp : p ∈ U) :
      (sphereSupportTensor (fermiMetric (fermiNormalScale κ))
        (fun q => H q + ε * J q) p).det = D (ε, p) := by
    have hεJ : ContDiff ℝ ∞ (fun q => ε * J q) := contDiff_const.mul hJ
    have hsum : ContDiffOn ℝ ∞ (fun q => H q + ε * J q) U := hH.add hεJ.contDiffOn
    rw [fermiSupport_actual_matrix hκ hU hsum hp (hscale p hp), Matrix.det_fin_two]
    have ha := fermiSupport_local_add hU hH hεJ κ hp
    have hm := fermiSupport_const_mul hJ ε κ p
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      ha.1, ha.2.1, ha.2.2, hm.1, hm.2.1, hm.2.2, D]
    ring
  have hn : ∀ p ∈ K, D (0, p) < 0 := by
    intro p hp
    rw [← hactual 0 p (hKU hp)]
    simpa only [zero_mul, add_zero] using hdet p hp
  obtain ⟨e, he, hbound⟩ := compact_uniform_negative_parameter hU hD hK hKU hn
  exact ⟨e, he, fun ε hε p hp => by rw [hactual ε p (hKU hp)]; exact hbound ε hε p hp⟩

theorem exists_fermiSeamPerturbation_saddle_threshold {a κ χ : ℝ → ℝ}
    {H : Coord → ℝ} {U K : Set Coord}
    (hκ : ContDiff ℝ ∞ κ) (hU : IsOpen U) (hH : ContDiffOn ℝ ∞ H U)
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hscale : ∀ p ∈ U, fermiNormalScale κ p ≠ 0)
    (hdet : ∀ p ∈ K, (sphereSupportTensor (fermiMetric (fermiNormalScale κ)) H p).det < 0)
    (ha : ContDiff ℝ ∞ a) (hχ : ContDiff ℝ ∞ χ) :
    ∃ e > 0, ∀ ε : ℝ, |ε| < e → ∀ p ∈ K,
      (sphereSupportTensor (fermiMetric (fermiNormalScale κ))
        (fun q => H q + fermiSeamPerturbation ε a κ χ q) p).det < 0 := by
  obtain ⟨e, he, hb⟩ := exists_fermiSupport_saddle_threshold hκ hU hH
    (fermiSeamPerturbation_contDiff ha hκ hχ 1) hK hKU hscale hdet
  refine ⟨e, he, fun ε hε p hp => ?_⟩
  rw [fermiSeamPerturbation_const_mul]
  exact hb ε hε p hp

end
end TightVer401
