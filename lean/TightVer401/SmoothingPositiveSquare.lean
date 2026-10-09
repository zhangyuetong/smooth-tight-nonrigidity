import TightVer401.SmoothingFlatPatch

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

theorem smoothing_positive_square_hasDerivAt (t : ℝ) :
    HasDerivAt (fun x : ℝ => (max x 0)^2) (2*max t 0) t := by
  rcases lt_trichotomy t 0 with ht | ht | ht
  · have hg : (fun x : ℝ => (max x 0)^2) =ᶠ[𝓝 t] (fun _ => 0) := by
      filter_upwards [isOpen_Iio.mem_nhds ht] with x hx
      change x < 0 at hx
      simp [max_eq_right (le_of_lt hx)]
    simpa [max_eq_right ht.le] using (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq hg
  · subst t
    have hl : HasDerivWithinAt (fun x : ℝ => (max x 0)^2) 0 (Iic 0) 0 := by
      exact (hasDerivAt_const 0 (0 : ℝ)).hasDerivWithinAt.congr_of_mem
        (fun x hx => by change x ≤ 0 at hx; simp [max_eq_right hx]) (by simp)
    have hr : HasDerivWithinAt (fun x : ℝ => (max x 0)^2) 0 (Ici 0) 0 := by
      have hp : HasDerivAt (fun x : ℝ => x^2) 0 0 := by
        have hd := ((by fun_prop : ContDiff ℝ ∞ (fun x : ℝ => x^2)).differentiable (by simp) 0).hasDerivAt
        rw [smoothing_normal_square_deriv] at hd
        simpa only [mul_zero] using hd
      exact hp.hasDerivWithinAt.congr_of_mem (fun x hx => by change 0 ≤ x at hx; rw [max_eq_left hx]) (by simp)
    have hu : Iic (0 : ℝ) ∪ Ici 0=univ := by
      ext x
      simp only [mem_union,mem_Iic,mem_Ici,mem_univ,iff_true]
      exact le_total x 0
    have hd := hl.union hr
    rw [hu] at hd
    simpa using hasDerivWithinAt_univ.mp hd
  · have hg : (fun x : ℝ => (max x 0)^2) =ᶠ[𝓝 t] (fun x => x^2) := by
      filter_upwards [isOpen_Ioi.mem_nhds ht] with x hx
      change 0 < x at hx
      simp [max_eq_left (le_of_lt hx)]
    simpa [max_eq_left ht.le] using ((hasDerivAt_id t).pow 2).congr_of_eventuallyEq hg

theorem smoothing_positive_square_contDiff : ContDiff ℝ 1 (fun x : ℝ => (max x 0)^2) := by
  apply contDiff_one_iff_deriv.mpr
  constructor
  · exact fun t => (smoothing_positive_square_hasDerivAt t).differentiableAt
  · have he : deriv (fun x : ℝ => (max x 0)^2)=fun t => 2*max t 0 := by
      funext t
      exact (smoothing_positive_square_hasDerivAt t).deriv
    rw [he]
    fun_prop

theorem smoothingFlatOriginal_contDiff_one {F G : Coord → ℝ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hzero : ∀ s : ℝ, (F-G) (![s,0]) = 0)
    (hfirst : ∀ s : ℝ, coordPartial 1 (F-G) (![s,0]) = 0) :
    ContDiff ℝ 1 (smoothingFlatOriginal F G) := by
  have he : smoothingFlatOriginal F G = fun p => G p+
      (max (p 1) 0)^2*smoothingFlatRemainder (F-G) p := by
    funext p
    exact smoothingFlatOriginal_eq hF hG hzero hfirst p
  rw [he]
  exact (hG.of_le (by simp)).add
    ((smoothing_positive_square_contDiff.comp (contDiff_apply ℝ ℝ 1)).mul
      ((smoothingFlatRemainder_contDiff (hF.sub hG)).of_le (by simp)))

end
end TightVer401
