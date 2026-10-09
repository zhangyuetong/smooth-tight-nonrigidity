import TightVer401.FermiSupportPositiveGraph

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Matrix
set_option backward.isDefEq.respectTransparency false

theorem fermiAsymptoticSlope_contDiffOn {L M N : Coord → ℝ} {W : Set Coord}
    (hL : ContDiffOn ℝ ∞ L W) (hM : ContDiffOn ℝ ∞ M W)
    (hN : ContDiffOn ℝ ∞ N W)
    (hD : ∀ p ∈ W, 0 < M p ^ 2 - L p * N p)
    (hMpos : ∀ p ∈ W, 0 < M p) :
    ContDiffOn ℝ ∞ (fermiAsymptoticSlope L M N) W := by
  have hdisc := (hM.pow 2).sub (hL.mul hN)
  have hs := hdisc.sqrt (fun p hp => (hD p hp).ne')
  exact hL.neg.div (hM.add hs) (fun p hp =>
    (add_pos_of_pos_of_nonneg (hMpos p hp) (Real.sqrt_nonneg _)).ne')

theorem exists_fermiSupport_asymptotic_domain {κ : ℝ → ℝ} {H : Coord → ℝ} {U : Set Coord}
    (hκ : ContDiff ℝ ∞ κ) (hU : IsOpen U) (hH : ContDiffOn ℝ ∞ H U)
    (hscale : ∀ p ∈ U, fermiNormalScale κ p ≠ 0)
    (hseam : ∀ r, (![r,0] : Coord) ∈ U)
    (hzero : ∀ r, fermiSupportL κ H ![r,0] = 0)
    (hpos : ∀ r, 0 < fermiSeamMixed κ H r) :
    ∃ W : Set Coord, IsOpen W ∧ W ⊆ U ∧
      (∀ r, (![r,0] : Coord) ∈ W) ∧
      ContDiffOn ℝ ∞ (fermiAsymptoticSlope (fermiSupportL κ H)
        (fermiSupportM κ H) (fermiSupportN H)) W ∧
      (∀ p ∈ W, (sphereSupportTensor (fermiMetric (fermiNormalScale κ)) H p).det < 0) ∧
      ∀ p ∈ W, fermiSupportL κ H p + 2 * fermiSupportM κ H p *
        fermiAsymptoticSlope (fermiSupportL κ H) (fermiSupportM κ H) (fermiSupportN H) p +
        fermiSupportN H p *
          (fermiAsymptoticSlope (fermiSupportL κ H) (fermiSupportM κ H) (fermiSupportN H) p)^2 = 0 := by
  let L := fermiSupportL κ H
  let M := fermiSupportM κ H
  let N := fermiSupportN H
  let D : Coord → ℝ := fun p => M p ^ 2 - L p * N p
  have hc := fermiSupport_contDiffOn hκ hU hH hscale
  have hD : ContDiffOn ℝ ∞ D U := (hc.2.1.pow 2).sub (hc.1.mul hc.2.2)
  let V := U ∩ M ⁻¹' Ioi 0
  have hV : IsOpen V := hc.2.1.continuousOn.isOpen_inter_preimage hU isOpen_Ioi
  let W := V ∩ D ⁻¹' Ioi 0
  have hW : IsOpen W := (hD.continuousOn.mono inter_subset_left).isOpen_inter_preimage hV isOpen_Ioi
  have hWU : W ⊆ U := inter_subset_left.trans inter_subset_left
  have hWM : ∀ p ∈ W, 0 < M p := fun p hp => hp.1.2
  have hWD : ∀ p ∈ W, 0 < D p := fun p hp => hp.2
  have hWseam (r : ℝ) : (![r,0] : Coord) ∈ W := by
    refine ⟨⟨hseam r, hpos r⟩, ?_⟩
    change 0 < M ![r,0] ^ 2 - L ![r,0] * N ![r,0]
    rw [show L ![r,0] = 0 from hzero r, zero_mul, sub_zero]
    exact sq_pos_of_pos (hpos r)
  refine ⟨W, hW, hWU, hWseam,
    fermiAsymptoticSlope_contDiffOn (hc.1.mono hWU) (hc.2.1.mono hWU)
      (hc.2.2.mono hWU) hWD hWM, ?_, ?_⟩
  · intro p hp
    rw [fermiSupport_actual_matrix hκ hU hH (hWU hp) (hscale p (hWU hp)), Matrix.det_fin_two]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    have hd := hWD p hp
    dsimp only [D, L, M, N] at hd
    nlinarith
  · intro p hp
    exact fermiAsymptoticSlope_quadratic (hWD p hp).le
      (add_pos_of_pos_of_nonneg (hWM p hp) (Real.sqrt_nonneg _)).ne'

end
end TightVer401
