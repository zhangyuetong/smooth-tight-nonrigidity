import TightVer401.ScalarCoordinateCalculus
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod

namespace TightVer401
noncomputable section
open Set Metric OAI.SmoothLocal.Geometry
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false

theorem exitGraph_slice_hasDerivAt {F : Coord → ℝ} {U : Set Coord}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) {r δ : ℝ} (hp : ![r, δ] ∈ U) :
    HasDerivAt (fun t => F ![r, t]) (coordPartial 1 F ![r, δ]) δ := by
  have hι : HasDerivAt (fun t : ℝ => (![r, t] : Coord)) (Pi.single 1 1) δ := by
    have h := ((hasDerivAt_id δ).smul_const (Pi.single 1 1 : Coord)).const_add
      (Pi.single 0 r : Coord)
    convert! h using 1
    · funext t
      ext i
      fin_cases i <;> simp
    · simp
  exact ((hF _ hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
    |>.hasFDerivAt.comp_hasDerivAt δ hι

theorem exitGraph_uniform_derivative_positive {F : Coord → ℝ} {U : Set Coord} {P : ℝ}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (hseam : ∀ r ∈ Icc (0 : ℝ) P, (![r, 0] : Coord) ∈ U)
    (hd : ∀ r ∈ Icc (0 : ℝ) P, 0 < coordPartial 1 F ![r, 0]) :
    ∃ ε > 0, ∀ r ∈ Icc (0 : ℝ) P, ∀ δ, |δ| ≤ ε →
      (![r, δ] : Coord) ∈ U ∧ 0 < coordPartial 1 F ![r, δ] := by
  let K := (fun r : ℝ => (![r, 0] : Coord)) '' Icc (0 : ℝ) P
  have hι : Continuous (fun r : ℝ => (![r, 0] : Coord)) := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_id
    · exact continuous_const
  have hK : IsCompact K := isCompact_Icc.image hι
  let V := U ∩ (coordPartial 1 F) ⁻¹' Ioi 0
  have hV : IsOpen V := (partial_contDiffOn hF hU 1).continuousOn.isOpen_inter_preimage hU isOpen_Ioi
  have hKV : K ⊆ V := by
    rintro p ⟨r, hr, rfl⟩
    exact ⟨hseam r hr, hd r hr⟩
  obtain ⟨ε, hε, hthick⟩ := hK.exists_cthickening_subset_open hV hKV
  refine ⟨ε, hε, ?_⟩
  intro r hr δ hδ
  apply hthick
  apply mem_cthickening_of_dist_le ![r, δ] ![r, 0] ε K
  · exact ⟨r, hr, rfl⟩
  · apply (dist_pi_le_iff hε.le).mpr
    intro i
    fin_cases i
    · simpa using hε.le
    · simpa [Real.dist_eq] using hδ

theorem exitGraph_uniform_positive_side {F : Coord → ℝ} {U : Set Coord} {P : ℝ}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (hseam : ∀ r ∈ Icc (0 : ℝ) P, (![r, 0] : Coord) ∈ U)
    (hz : ∀ r ∈ Icc (0 : ℝ) P, F ![r, 0] = 0)
    (hd : ∀ r ∈ Icc (0 : ℝ) P, 0 < coordPartial 1 F ![r, 0]) :
    ∃ ε > 0, ∀ r ∈ Icc (0 : ℝ) P, ∀ δ, 0 < δ → δ < ε → 0 < F ![r, δ] := by
  obtain ⟨ε, hε, hεd⟩ := exitGraph_uniform_derivative_positive hU hF hseam hd
  refine ⟨ε, hε, ?_⟩
  intro r hr δ hδ hδε
  have hmem (t : ℝ) (ht : t ∈ Ioo (-ε) ε) :
      (![r, t] : Coord) ∈ U ∧ 0 < coordPartial 1 F ![r, t] :=
    hεd r hr t ((abs_lt.mpr ⟨by linarith [ht.1], ht.2⟩).le)
  have hcont : ContinuousOn (fun t => F ![r, t]) (Ioo (-ε) ε) := by
    intro t ht
    exact (exitGraph_slice_hasDerivAt hU hF (hmem t ht).1).continuousAt.continuousWithinAt
  have hm : StrictMonoOn (fun t => F ![r, t]) (Ioo (-ε) ε) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo _ _) hcont
    intro t ht
    have ht' := interior_subset ht
    rw [(exitGraph_slice_hasDerivAt hU hF (hmem t ht').1).deriv]
    exact (hmem t ht').2
  have he := hm (by constructor <;> linarith : (0 : ℝ) ∈ Ioo (-ε) ε)
    ⟨by linarith, hδε⟩ hδ
  simpa only [hz r hr] using he

theorem exitGraph_uniform_negative_side {F : Coord → ℝ} {U : Set Coord} {P : ℝ}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (hseam : ∀ r ∈ Icc (0 : ℝ) P, (![r, 0] : Coord) ∈ U)
    (hz : ∀ r ∈ Icc (0 : ℝ) P, F ![r, 0] = 0)
    (hd : ∀ r ∈ Icc (0 : ℝ) P, coordPartial 1 F ![r, 0] < 0) :
    ∃ ε > 0, ∀ r ∈ Icc (0 : ℝ) P, ∀ δ, -ε < δ → δ < 0 → 0 < F ![r, δ] := by
  let G : Coord → ℝ := fun p => F ![p 0, -p 1]
  have hmap : ContDiff ℝ ∞ (fun p : Coord => (![p 0, -p 1] : Coord)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · exact contDiff_apply ℝ ℝ 0
    · exact (contDiff_apply ℝ ℝ 1).neg
  let V := (fun p : Coord => (![p 0, -p 1] : Coord)) ⁻¹' U
  have hV : IsOpen V := hU.preimage hmap.continuous
  have hG : ContDiffOn ℝ ∞ G V := hF.comp hmap.contDiffOn (fun _ h => h)
  have hgs : ∀ r ∈ Icc (0 : ℝ) P, (![r, 0] : Coord) ∈ V := by
    intro r hr
    simpa [V] using hseam r hr
  have hgz : ∀ r ∈ Icc (0 : ℝ) P, G ![r, 0] = 0 := by
    intro r hr
    simpa [G] using hz r hr
  have hgd : ∀ r ∈ Icc (0 : ℝ) P, 0 < coordPartial 1 G ![r, 0] := by
    intro r hr
    have hnegseam : (![r, -(0 : ℝ)] : Coord) ∈ U := by simpa using hseam r hr
    have h := (exitGraph_slice_hasDerivAt hU hF hnegseam).comp (0 : ℝ) (hasDerivAt_id (0 : ℝ)).neg
    have h' := exitGraph_slice_hasDerivAt hV hG (hgs r hr)
    have he : coordPartial 1 G ![r, 0] = -coordPartial 1 F ![r, 0] := by
      simpa [G] using h'.unique h
    rw [he]
    exact neg_pos.mpr (hd r hr)
  obtain ⟨ε, hε, he⟩ := exitGraph_uniform_positive_side hV hG hgs hgz hgd
  refine ⟨ε, hε, ?_⟩
  intro r hr δ hεδ hδ
  have h := he r hr (-δ) (by linarith) (by linarith)
  simpa [G] using h

end
end TightVer401
