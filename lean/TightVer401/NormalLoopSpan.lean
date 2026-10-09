import TightVer401.NormalLoopNonconstant

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false in
theorem normalLoop_annihilator_eq_zero {ζ : ℝ → Ambient}
    (hζ : ContDiff ℝ ∞ ζ) (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1)
    (hκ : ∃ r, normalLoopCurvature ζ r ≠ 0) {v : Ambient}
    (hv : ∀ r, inner ℝ v (normalLoopTangent ζ r) = 0) : v = 0 := by
  obtain ⟨r, hr⟩ := hκ
  have hE := (contDiff_infty_iff_deriv.mp hζ).2
  have hEd := (contDiff_infty_iff_deriv.mp hE).1
  have hvE (s : ℝ) (hs : normalLoopCurvature ζ s ≠ 0) :
      inner ℝ v (deriv ζ s) = 0 := by
    have hd := (hasDerivAt_const s v).inner ℝ
      (normalLoop_actual_frame hζ hunit hspeed s).2.1
    rw [show (fun t => inner ℝ v (normalLoopTangent ζ t)) = fun _ => (0 : ℝ)
      from funext hv] at hd
    have he := hd.unique (hasDerivAt_const s (0 : ℝ))
    simp only [inner_zero_left, add_zero, real_inner_smul_right] at he
    exact (mul_eq_zero.mp he).resolve_left hs
  have hnear : ∀ᶠ s in 𝓝 r, normalLoopCurvature ζ s ≠ 0 :=
    ((normalLoop_actual_smooth hζ).2.continuous.tendsto r).eventually_ne hr
  have hgerm : (fun s => inner ℝ v (deriv ζ s)) =ᶠ[𝓝 r] fun _ => (0 : ℝ) := by
    filter_upwards [hnear] with s hs using hvE s hs
  have hd := (hasDerivAt_const r v).inner ℝ ((hEd r).hasDerivAt)
  have hzero := (hd.congr_of_eventuallyEq hgerm.symm).unique (hasDerivAt_const r (0 : ℝ))
  have hvζ : inner ℝ v (ζ r) = 0 := by
    simp only [inner_zero_left, add_zero] at hzero
    rw [(normalLoop_actual_frame hζ hunit hspeed r).2.2,
      inner_sub_right, inner_neg_right, real_inner_smul_right, hv r,
      mul_zero, sub_zero] at hzero
    linarith
  have he := orthonormal_frame_decomposition (normalLoop_actual_frame hζ hunit hspeed r).1 v
  simpa only [hv r, hvE r hr, hvζ, zero_smul, zero_add] using he

theorem normalLoop_closure_annihilator_eq_zero {ζ : ℝ → Ambient} {a : ℝ → ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (ha : Continuous a)
    (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1)
    (hpos : ∀ r, 0 < a r) {L : ℝ} (hL : 0 < L)
    (hmoment : normalLoopMoment a ζ (deriv ζ) L = 0) {v : Ambient}
    (hv : ∀ r, inner ℝ v (normalLoopTangent ζ r) = 0) : v = 0 := by
  obtain ⟨r, hr⟩ := normalLoop_closure_forces_nonconstant_curvature
    hζ ha hunit hspeed hpos hL hmoment
  apply normalLoop_annihilator_eq_zero hζ hunit hspeed ?_ hv
  by_cases hzero : normalLoopCurvature ζ 0 = 0
  · exact ⟨r, hzero ▸ hr⟩
  · exact ⟨0, hzero⟩

theorem normalLoop_closure_span_eq_top {ζ : ℝ → Ambient} {a : ℝ → ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (ha : Continuous a)
    (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1)
    (hpos : ∀ r, 0 < a r) {L : ℝ} (hL : 0 < L)
    (hmoment : normalLoopMoment a ζ (deriv ζ) L = 0) :
    Submodule.span ℝ (Set.range (normalLoopTangent ζ)) = ⊤ := by
  apply Submodule.orthogonal_eq_bot_iff.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro v hv
  apply normalLoop_closure_annihilator_eq_zero hζ ha hunit hspeed hpos hL hmoment
  intro r
  exact Submodule.inner_left_of_mem_orthogonal
    (Submodule.subset_span (Set.mem_range_self r)) hv

end
end TightVer401
