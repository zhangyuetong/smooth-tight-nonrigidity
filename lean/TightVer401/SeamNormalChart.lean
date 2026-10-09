import TightVer401.SeamNormalCoordinates
import TightVer401.SeamNormalStripChart

namespace TightVer401
noncomputable section
open Set OAI.CircleDomainRigidity OAI.SmoothLocal.Geometry
open scoped ContDiff

/-- The actual OpenAI regular normal chart, transported to the coordinates used
by the checked planar Hessian and smoothing calculus. -/
theorem seamNormalCoordinates_exists_chart {γ : ℝ → ℂ} (hγ : ContDiff ℝ ∞ γ)
    (s : ℝ) (hs : deriv γ s ≠ 0) :
    ∃ e : OpenPartialHomeomorph Coord Coord,
      (![s,0] : Coord) ∈ e.source ∧
      (∀ p, e p=seamNormalCoordinates γ p) ∧
      ContDiff ℝ ∞ e ∧ ContDiffAt ℝ ∞ e.symm (seamComplexCoord (γ s)) := by
  obtain ⟨e,heS,he,hSmooth,hInv⟩ := seamCurveNormalStrip_exists_chart hγ s hs
  let A := seamCoordProd.toHomeomorph.toOpenPartialHomeomorph
  let B := seamComplexCoord.toHomeomorph.toOpenPartialHomeomorph
  let e' := (A.trans e).trans B
  have hf : ∀ p, e' p=seamNormalCoordinates γ p := by
    intro p
    change seamComplexCoord (e (seamCoordProd p))=seamNormalCoordinates γ p
    rw [he]
    rfl
  have hSource : (![s,0] : Coord) ∈ e'.source := by
    simp only [e',OpenPartialHomeomorph.trans_source,mem_inter_iff,mem_preimage]
    refine ⟨⟨?_,?_⟩,?_⟩
    · change (![s,0] : Coord) ∈ (Set.univ : Set Coord)
      trivial
    · change (s,0) ∈ e.source
      exact heS
    · change e (s,0) ∈ (Set.univ : Set ℂ)
      trivial
  have hCont : ContDiff ℝ ∞ e' := by
    have heq : (e' : Coord → Coord)=seamNormalCoordinates γ := funext hf
    rw [heq]
    exact seamNormalCoordinates_contDiff hγ
  have hInv' : ContDiffAt ℝ ∞ e'.symm (seamComplexCoord (γ s)) := by
    have hMiddle : ContDiffAt ℝ ∞ (fun p : Coord => e.symm (seamComplexCoord.symm p))
        (seamComplexCoord (γ s)) := by
      have hc := hInv.comp (seamComplexCoord (γ s)) seamComplexCoord.symm.contDiff.contDiffAt
      simpa only [ContinuousLinearEquiv.symm_apply_apply,Function.comp_def] using hc
    have hc := seamCoordProd.symm.contDiff.contDiffAt.comp (seamComplexCoord (γ s)) hMiddle
    change ContDiffAt ℝ ∞ (fun p : Coord => seamCoordProd.symm (e.symm (seamComplexCoord.symm p)))
      (seamComplexCoord (γ s))
    simpa only [Function.comp_def] using hc
  exact ⟨e',hSource,hf,hCont,hInv'⟩

end
end TightVer401
