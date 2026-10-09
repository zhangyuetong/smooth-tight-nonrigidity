import TightVer401.ProtectedTorusBendingStrain

/-! Transfer the same protected band bending through actual source coordinates.
No completed torus or bending conclusion is assumed. -/
open Manifold
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false

/-- Literal extension of a nonzero supported band bending has zero actual
native strain everywhere, including the frontier of the protected chart. -/
theorem protectedTorus_compact_nonzero_bending {T w : ℝ} [Fact (0 < T)]
    {X Y : AddCircle T × Ioo (0 : ℝ) w → Ambient}
    (hX : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ X)
    (hY : IsBandBending X Y) (hcompact : HasCompactSupport Y)
    (hnonzero : ∃ p, Y p ≠ 0)
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) NonrigidTorusSource)
    (hsupport : tsupport Y ⊆ e.source)
    (he : ContMDiffOn nativeProductModel nativeProductModel ∞ e.symm e.target)
    (A : Ambient ≃ᵃⁱ[ℝ] Ambient) (F : NonrigidTorusSource → Ambient)
    (hplacement : ∀ p ∈ e.source, F (e p) = A (X p)) :
    let Z := protectedTorusBendingField e A Y
    ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ Z ∧
      (∀ p, ∀ v z : ℝ × ℝ, nativeProductLinearMetricForm F Z p v z = 0) ∧
      HasCompactSupport Z ∧ (∃ p, Z p ≠ 0) ∧ tsupport Z ⊆ e '' tsupport Y := by
  refine ⟨protectedTorusBendingField_contMDiff e A hY.1 hcompact hsupport he, ?_,
    protectedTorusBendingField_hasCompactSupport e A hcompact hsupport,
    protectedTorusBendingField_nonzero e A hsupport hnonzero,
    protectedTorusBendingField_tsupport e A hcompact hsupport⟩
  intro q v z
  by_cases hq : q ∈ e.target
  · have hF : F =ᶠ[𝓝 q] (fun x => A (X (e.symm x))) := by
      filter_upwards [e.open_target.mem_nhds hq] with x hx
      have hp := hplacement (e.symm x) (e.map_target hx)
      rwa [e.right_inv hx] at hp
    exact protectedTorus_affine_pullback_zero_strain hX hY e A he hq hF
      (protectedTorusBendingField_eventually_eq e A Y hq) v z
  · have hout : q ∉ e '' tsupport Y := by
      rintro ⟨p, hp, rfl⟩
      exact hq (e.map_source (hsupport hp))
    have hz := protectedTorusBendingField_eventually_zero e A hcompact hsupport hout
    unfold nativeProductLinearMetricForm
    rw [hz.mfderiv_eq, mfderiv_const]
    simp

end
end TightVer401
