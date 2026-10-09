import TightVer401.PeriodProjectionDifferential
import TightVer401.BandDifferential

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped Manifold ContDiff
set_option backward.isDefEq.respectTransparency false

def bandProjection (L b : ℝ) : ℝ × Set.Ioo (0 : ℝ) b → AddCircle L × Set.Ioo (0 : ℝ) b :=
  Prod.map (periodProjection L) id

def bandProjectionDifferential (L b : ℝ) [Fact (0 < L)]
    (p : ℝ × Set.Ioo (0 : ℝ) b) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (bandProjection L b) p

theorem bandProjection_contMDiff (L b : ℝ) [Fact (0 < L)] :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
      (bandProjection L b) := (periodProjection_contMDiff L).prodMap contMDiff_id

theorem bandProjection_mfderiv_surjective (L b : ℝ) [Fact (0 < L)]
    (p : ℝ × Set.Ioo (0 : ℝ) b) :
    Function.Surjective (bandProjectionDifferential L b p) := by
  unfold bandProjectionDifferential
  intro v
  obtain ⟨x, hx⟩ := periodProjection_mfderiv_surjective L p.1 v.1
  refine ⟨(x, v.2), ?_⟩
  rw [bandProjection, mfderiv_prodMap
    ((periodProjection_contMDiff L p.1).mdifferentiableAt (by simp)) mdifferentiableAt_id,
    mfderiv_id]
  change (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (periodProjection L) p.1 x, v.2) = v
  rw [hx]
  exact Prod.eta v

theorem band_zero_strain_descends {L b : ℝ} [Fact (0 < L)]
    {X Y : AddCircle L × Set.Ioo (0 : ℝ) b → Ambient}
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Ambient) ∞ X)
    (hY : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Ambient) ∞ Y)
    (hstrain : ∀ p : ℝ × Set.Ioo (0 : ℝ) b, ∀ v w : ℝ × ℝ,
      inner ℝ (bandDifferential (X ∘ bandProjection L b) p v)
        (bandDifferential (Y ∘ bandProjection L b) p w) +
      inner ℝ (bandDifferential (Y ∘ bandProjection L b) p v)
        (bandDifferential (X ∘ bandProjection L b) p w) = 0) :
    ∀ p : AddCircle L × Set.Ioo (0 : ℝ) b, ∀ v w : ℝ × ℝ,
      inner ℝ (bandDifferential X p v) (bandDifferential Y p w) +
      inner ℝ (bandDifferential Y p v) (bandDifferential X p w) = 0 := by
  intro p v w
  obtain ⟨s, hs⟩ := QuotientAddGroup.mk_surjective p.1
  let q : ℝ × Set.Ioo (0 : ℝ) b := (s, p.2)
  have hq : bandProjection L b q = p := by exact Prod.ext hs rfl
  obtain ⟨v', hv⟩ := bandProjection_mfderiv_surjective L b q v
  obtain ⟨w', hw⟩ := bandProjection_mfderiv_surjective L b q w
  have hπ := (bandProjection_contMDiff L b q).mdifferentiableAt (by simp)
  have hXd := (hX (bandProjection L b q)).mdifferentiableAt (by simp)
  have hYd := (hY (bandProjection L b q)).mdifferentiableAt (by simp)
  have hx : bandDifferential (X ∘ bandProjection L b) q =
      (bandDifferential X (bandProjection L b q)).comp
        (bandProjectionDifferential L b q) := mfderiv_comp q hXd hπ
  have hy : bandDifferential (Y ∘ bandProjection L b) q =
      (bandDifferential Y (bandProjection L b q)).comp
        (bandProjectionDifferential L b q) := mfderiv_comp q hYd hπ
  have h := hstrain q v' w'
  rw [hx, hy] at h
  simpa only [ContinuousLinearMap.comp_apply, hv, hw, hq] using h

end
end TightVer401
