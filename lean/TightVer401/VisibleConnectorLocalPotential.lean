import TightVer401.VisibleConnectorRuledCoordinates

/-! Actual local Cartesian connector potentials constructed through the
retained inverse function theorem. Global annular degree and gluing are
separate construction obligations. No inverse or potential is supplied. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency true

 theorem visibleConnectorSource_contDiff {p w : ℝ → Coord}
    (hp : ContDiff ℝ ∞ p) (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (visibleConnectorSource p w) :=
  (hp.comp (contDiff_apply ℝ ℝ 0)).add
    ((contDiff_apply ℝ ℝ 1).smul (hw.comp (contDiff_apply ℝ ℝ 0)))

 theorem visibleConnectorHeight_contDiff {g : ℝ → ℝ} {gamma w : ℝ → Coord}
    (hg : ContDiff ℝ ∞ g) (hgamma : ContDiff ℝ ∞ gamma) (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (visibleConnectorHeight g gamma w) := by
  have hi (i : Fin 2) : ContDiff ℝ ∞ (fun s => gamma s i * w s i) :=
    ((contDiff_apply ℝ ℝ i).comp hgamma).mul ((contDiff_apply ℝ ℝ i).comp hw)
  have hd : ContDiff ℝ ∞ (fun s => gamma s ⬝ᵥ w s) := by
    simpa only [dotProduct, Fin.sum_univ_two] using (hi 0).add (hi 1)
  exact (hg.comp (contDiff_apply ℝ ℝ 0)).add
    ((contDiff_apply ℝ ℝ 1).mul (hd.comp (contDiff_apply ℝ ℝ 0)))

 theorem visibleConnector_two_dots_unique {v w a b : Coord}
    (hdet : visibleConnectorDet v w ≠ 0)
    (hv : a ⬝ᵥ v = b ⬝ᵥ v) (hw : a ⬝ᵥ w = b ⬝ᵥ w) : a = b := by
  have hdv : (a 0 - b 0) * v 0 + (a 1 - b 1) * v 1 = 0 := by
    simp only [dotProduct, Fin.sum_univ_two] at hv
    linarith
  have hdw : (a 0 - b 0) * w 0 + (a 1 - b 1) * w 1 = 0 := by
    simp only [dotProduct, Fin.sum_univ_two] at hw
    linarith
  have h0 : (a 0 - b 0) * visibleConnectorDet v w = 0 := by
    unfold visibleConnectorDet
    linear_combination w 1 * hdv - v 1 * hdw
  have h1 : (a 1 - b 1) * visibleConnectorDet v w = 0 := by
    unfold visibleConnectorDet
    linear_combination v 0 * hdw - w 0 * hdv
  have ha0 := sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_right hdet)
  have ha1 := sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right hdet)
  ext i
  fin_cases i
  · exact ha0
  · exact ha1

 theorem visibleConnector_columns_injective {v w : Coord}
    (hdet : visibleConnectorDet v w ≠ 0) :
    Function.Injective (fun a : Coord => a 0 • v + a 1 • w) := by
  intro a b hab
  have h0 := congrFun hab 0
  have h1 := congrFun hab 1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h0 h1
  have ha0 : (a 0 - b 0) * visibleConnectorDet v w = 0 := by
    unfold visibleConnectorDet
    linear_combination w 1 * h0 - w 0 * h1
  have ha1 : (a 1 - b 1) * visibleConnectorDet v w = 0 := by
    unfold visibleConnectorDet
    linear_combination v 0 * h1 - v 1 * h0
  have hz0 := sub_eq_zero.mp ((mul_eq_zero.mp ha0).resolve_right hdet)
  have hz1 := sub_eq_zero.mp ((mul_eq_zero.mp ha1).resolve_right hdet)
  ext i
  fin_cases i
  · exact hz0
  · exact hz1

 theorem visibleConnectorSource_fderiv_injective {p gamma w : ℝ → Coord}
    (hp : ContDiff ℝ ∞ p) (hw : ContDiff ℝ ∞ w) (q : Coord)
    (hDelta : visibleConnectorDelta p gamma w q ≠ 0) :
    Function.Injective (fderiv ℝ (visibleConnectorSource p w) q) := by
  have hdet : visibleConnectorDet (coordPartial 0 (visibleConnectorSource p w) q)
      (coordPartial 1 (visibleConnectorSource p w) q) ≠ 0 := by
    rw [visibleConnectorSource_actual_determinant hp hw gamma q]
    exact neg_ne_zero.mpr hDelta
  have hf (v : Coord) : fderiv ℝ (visibleConnectorSource p w) q v =
      v 0 • coordPartial 0 (visibleConnectorSource p w) q +
      v 1 • coordPartial 1 (visibleConnectorSource p w) q := by
    have hv : v = v 0 • (Pi.single 0 1 : Coord) + v 1 • (Pi.single 1 1 : Coord) := by
      ext i
      fin_cases i <;> simp
    conv_lhs => rw [hv]
    simp [coordPartial]
  intro a b hab
  exact visibleConnector_columns_injective hdet (by simpa only [hf] using hab)

/-- Construct the actual local Cartesian inverse and potential. Its gradient
is the explicit ruled gradient on the entire local source neighborhood. -/
theorem visibleConnector_exists_local_potential {g : ℝ → ℝ} {p gamma w : ℝ → Coord}
    (hg : ContDiff ℝ ∞ g) (hp : ContDiff ℝ ∞ p)
    (hgamma : ContDiff ℝ ∞ gamma) (hw : ContDiff ℝ ∞ w)
    (hvalue : ∀ s, deriv g s = gamma s ⬝ᵥ deriv p s)
    (q : Coord) (hDelta : visibleConnectorDelta p gamma w q ≠ 0) :
    ∃ (e : OpenPartialHomeomorph Coord Coord) (G : Coord → ℝ),
      q ∈ e.source ∧
      (e : Coord → Coord) = visibleConnectorSource p w ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧ ContDiffOn ℝ ∞ G e.target ∧
      EqOn (G ∘ visibleConnectorSource p w) (visibleConnectorHeight g gamma w) e.source ∧
      EqOn (planarGradient G ∘ visibleConnectorSource p w)
        (visibleConnectorGradient p gamma w) e.source := by
  let V := {r : Coord | visibleConnectorDelta p gamma w r ≠ 0}
  have hDeltaSmooth : ContDiff ℝ ∞ (visibleConnectorDelta p gamma w) := by
    have hdp := (contDiff_infty_iff_deriv.mp hp).2
    have hdg := (contDiff_infty_iff_deriv.mp hgamma).2
    have hdw := (contDiff_infty_iff_deriv.mp hw).2
    unfold visibleConnectorDelta visibleConnectorA visibleConnectorC visibleConnectorB
      visibleConnectorDet dotProduct
    simp only [Fin.sum_univ_two]
    fun_prop
  have hV : IsOpen V := hDeltaSmooth.continuous.isOpen_preimage _ isClosed_singleton.isOpen_compl
  have hq : q ∈ V := hDelta
  obtain ⟨e, heq, heV, he, hei⟩ := exists_smooth_local_inverse hV
    (visibleConnectorSource_contDiff hp hw).contDiffOn
    (fun r hr => visibleConnectorSource_fderiv_injective hp hw r hr) hq
  let G : Coord → ℝ := visibleConnectorHeight g gamma w ∘ e.symm
  have hH := visibleConnectorHeight_contDiff hg hgamma hw
  have hG : ContDiffOn ℝ ∞ G e.target := hH.comp_contDiffOn hei
  have hrec : EqOn (G ∘ visibleConnectorSource p w) (visibleConnectorHeight g gamma w) e.source := by
    intro r hr
    change visibleConnectorHeight g gamma w (e.symm (visibleConnectorSource p w r)) = _
    rw [← he, e.left_inv hr]
  refine ⟨e, G, heq, he, hei, hG, hrec, ?_⟩
  intro r hr
  have hrV := heV hr
  have hPr : visibleConnectorSource p w r ∈ e.target := by rw [← he]; exact e.map_source hr
  have hPdiff := (visibleConnectorSource_contDiff hp hw).differentiable (by simp) r
  have hGdiff := ((hG _ hPr).contDiffAt (e.open_target.mem_nhds hPr)).differentiableAt (by simp)
  have hcomp := fderiv_comp r hGdiff hPdiff
  have hEq := (hrec.eventuallyEq_of_mem (e.open_source.mem_nhds hr)).fderiv_eq (𝕜 := ℝ)
  have hfirst := visibleConnector_actual_first_jets hg hp hgamma hw hvalue r hrV
  have hdir (i : Fin 2) : planarGradient G (visibleConnectorSource p w r) ⬝ᵥ
      coordPartial i (visibleConnectorSource p w) r =
        coordPartial i (visibleConnectorHeight g gamma w) r := by
    rw [← planarGradient_dot_fderiv]
    change fderiv ℝ G (visibleConnectorSource p w r)
      (fderiv ℝ (visibleConnectorSource p w) r (Pi.single i 1)) = _
    rw [← ContinuousLinearMap.comp_apply, ← hcomp, hEq]
    rfl
  apply visibleConnector_two_dots_unique
    (v := coordPartial 0 (visibleConnectorSource p w) r)
    (w := coordPartial 1 (visibleConnectorSource p w) r)
  · rw [visibleConnectorSource_actual_determinant hp hw gamma r]
    exact neg_ne_zero.mpr hrV
  · exact (hdir 0).trans (hfirst 0).symm
  · exact (hdir 1).trans (hfirst 1).symm

end
end TightVer401
