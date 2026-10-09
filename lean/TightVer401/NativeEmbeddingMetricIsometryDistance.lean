import Mathlib.Geometry.Manifold.Riemannian.Basic

/-! Smooth tangent isometries preserve the actual intrinsic path distance.
This leaf uses only the differential-norm path infimum; no ambient metric is used.
-/
open Manifold Bundle MeasureTheory
open scoped Manifold ContDiff Topology Bundle ENNReal
namespace TightVer401
noncomputable section
set_option backward.isDefEq.respectTransparency false

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]
  [RiemannianBundle (fun p : M => TangentSpace I p)]

attribute [local instance] Measure.Subtype.measureSpace

/-- A C1 map preserving actual tangent norms cannot increase intrinsic distance. -/
theorem riemannianEDist_map_le_of_tangent_enorm
    (f : M → M) (hf : ContMDiff I I 1 f)
    (hnorm : ∀ (p : M) (v : TangentSpace I p),
      ‖mfderiv I I f p v‖ₑ = ‖v‖ₑ) (x y : M) :
    Manifold.riemannianEDist I (f x) (f y) ≤ Manifold.riemannianEDist I x y := by
  conv_rhs => rw [Manifold.riemannianEDist]
  refine le_iInf fun γ => le_iInf fun hγ => ?_
  let η : Path (f x) (f y) := γ.map hf.continuous
  have hη : ContMDiff (𝓡∂ 1) I 1 (η : unitInterval → M) := by
    change ContMDiff (𝓡∂ 1) I 1 (f ∘ (γ : unitInterval → M))
    exact hf.comp hγ
  have hlen :
      (∫⁻ t : unitInterval, ‖mfderiv (𝓡∂ 1) I η t 1‖ₑ) =
      ∫⁻ t : unitInterval, ‖mfderiv (𝓡∂ 1) I γ t 1‖ₑ := by
    apply lintegral_congr
    intro t
    change ‖mfderiv (𝓡∂ 1) I (f ∘ (γ : unitInterval → M)) t 1‖ₑ = _
    rw [mfderiv_comp t (hf.mdifferentiableAt (by simp))
      (hγ.mdifferentiableAt (by simp))]
    exact hnorm (γ t) (mfderiv (𝓡∂ 1) I γ t 1)
  rw [Manifold.riemannianEDist]
  exact (iInf_le_of_le η (iInf_le_of_le hη le_rfl)).trans_eq hlen

/-- Equality of base points transports the actual fiber norm, including its instance. -/
theorem tangent_enorm_base_eq (q r : M) (h : q = r) (v : E) :
    ‖(show TangentSpace I q from v)‖ₑ = ‖(show TangentSpace I r from v)‖ₑ := by
  subst r
  rfl

/-- The inverse of a smooth tangent-norm-preserving homeomorphism also preserves
those same tangent norms, by differentiating the actual inverse identity. -/
theorem homeomorph_symm_tangent_enorm
    (e : M ≃ₜ M) (he : ContMDiff I I 1 (e : M → M))
    (hi : ContMDiff I I 1 (e.symm : M → M))
    (hnorm : ∀ (p : M) (v : TangentSpace I p),
      ‖mfderiv I I e p v‖ₑ = ‖v‖ₑ)
    (p : M) (v : TangentSpace I p) :
    ‖mfderiv I I e.symm p v‖ₑ = ‖v‖ₑ := by
  have hcomp := mfderiv_comp p (he.mdifferentiableAt (by simp))
    (hi.mdifferentiableAt (by simp))
  have hid : (e : M → M) ∘ (e.symm : M → M) = id := by
    funext q
    exact e.apply_symm_apply q
  rw [hid, mfderiv_id] at hcomp
  have hv := congrArg (fun L : TangentSpace I p →L[ℝ] TangentSpace I p => L v) hcomp
  have hn := hnorm (e.symm p) (mfderiv I I e.symm p v)
  have hv' : mfderiv I I e (e.symm p) (mfderiv I I e.symm p v) = v := by
    exact hv.symm
  have ht := tangent_enorm_base_eq (I := I) (e (e.symm p)) p
    (e.apply_symm_apply p) (mfderiv I I e (e.symm p) (mfderiv I I e.symm p v))
  exact hn.symm.trans (ht.trans (congrArg (fun z : TangentSpace I p => ‖z‖ₑ) hv'))

/-- A smooth diffeomorphism preserving the Riemannian tangent norms preserves
exactly the distance defined by the C1-path length infimum. -/
theorem riemannianEDist_homeomorph_eq_of_tangent_enorm
    (e : M ≃ₜ M) (he : ContMDiff I I 1 (e : M → M))
    (hi : ContMDiff I I 1 (e.symm : M → M))
    (hnorm : ∀ (p : M) (v : TangentSpace I p),
      ‖mfderiv I I e p v‖ₑ = ‖v‖ₑ) (x y : M) :
    Manifold.riemannianEDist I (e x) (e y) = Manifold.riemannianEDist I x y := by
  apply le_antisymm
  · exact riemannianEDist_map_le_of_tangent_enorm e he hnorm x y
  · have h := riemannianEDist_map_le_of_tangent_enorm e.symm hi
      (homeomorph_symm_tangent_enorm e he hi hnorm) (e x) (e y)
    simpa only [e.symm_apply_apply] using h

end
end
end TightVer401





