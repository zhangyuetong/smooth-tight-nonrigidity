import TightVer401.QuadraticRadialFillingExteriorCollar
import TightVer401.QuadraticRadialFillingGlue
import TightVer401.QuadraticRadialFillingBoundaryRadial
import TightVer401.DualRadialCompletionPatch

/-! Paste the actual inner filling to its incoming dual on a derived open
radial collar. The scalar, overlap width and whole punctured domain are built
from actual outer germs and the returned circle's incoming-domain membership. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix

theorem exists_dualRadialCompletion_inner_filling_patch {R S : ℝ}
    (hR : 0 < R) (hRS : R < S) {F H : Coord → ℝ} {U V : Set Coord}
    (hU : IsOpen U) (hV : IsOpen V) (_hUV : U ⊆ V)
    (hF : ContDiffOn ℝ ∞ F V)
    (hnF : ∀ p ∈ V, (planarHessian F p).det < 0)
    (hH : ContDiffOn ℝ ∞ H (quadraticRadialFillingDomain R U))
    (hnH : ∀ p ∈ quadraticRadialFillingDomain R U, (planarHessian H p).det < 0)
    (hDisk : {p : Coord | 0 < planarRadius p ∧ planarRadius p < S} ⊆
      quadraticRadialFillingDomain R U)
    (hCircleU : ∀ theta, saddlePolarChart ![S, theta] ∈ U)
    (hGerm : ∀ theta, H =ᶠ[𝓝 (saddlePolarChart ![S, theta])] F) :
    ∃ (delta : ℝ) (P : Coord → ℝ),
      0 < delta ∧ delta < S - R ∧
      ContDiffOn ℝ ∞ P (quadraticRadialFillingDomain S V) ∧
      (∀ p ∈ quadraticRadialFillingDomain S V, (planarHessian P p).det < 0) ∧
      EqOn P H {p | 0 < planarRadius p ∧ planarRadius p < S + delta} ∧
      EqOn P F (V ∩ {p | S - delta < planarRadius p}) := by
  have hS : 0 < S := hR.trans hRS
  let N := U ∩ interior {p : Coord | H p = F p}
  have hN : IsOpen N := hU.inter isOpen_interior
  have hCircleN : quadraticRadialFillingRadiusLevel S ⊆ N := by
    intro p hp
    obtain ⟨theta, rfl⟩ := quadraticRadialFilling_radiusLevel_exists_polar hS hp
    refine ⟨hCircleU theta, ?_⟩
    exact mem_interior_iff_mem_nhds.mpr (hGerm theta)
  obtain ⟨delta0, hd0, _hd0S, hCollar⟩ :=
    quadraticRadialFilling_exists_radial_collar hS hN hCircleN
  let delta := min delta0 ((S - R) / 2)
  have hd : 0 < delta := lt_min hd0 (by linarith)
  have hdSR : delta < S - R := (min_le_right _ _).trans_lt (by linarith)
  have hd0le : delta ≤ delta0 := min_le_left _ _
  let U0 := {p : Coord | 0 < planarRadius p ∧ planarRadius p < S + delta}
  let U1 := V ∩ {p : Coord | S - delta < planarRadius p}
  let P := dualRadialCompletionPatch U0 U1 H F F
  have hU0 : IsOpen U0 :=
    (isOpen_lt continuous_const quadraticFillerCartesianGradient_radius_continuous).inter
      (isOpen_lt quadraticFillerCartesianGradient_radius_continuous continuous_const)
  have hU1 : IsOpen U1 := hV.inter
    (isOpen_lt continuous_const quadraticFillerCartesianGradient_radius_continuous)
  have hSub : U0 ⊆ quadraticRadialFillingDomain R U := by
    intro p hp
    by_cases hpS : planarRadius p < S
    · exact hDisk ⟨hp.1, hpS⟩
    · have hAbs : |planarRadius p - S| < delta := by
        rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_gt hpS))]
        linarith [hp.2]
      exact ⟨hp.1, Or.inr (hCollar p (hAbs.trans_le hd0le)).1⟩
  have h01 : EqOn H F (U0 ∩ U1) := by
    intro p hp
    change (0 < planarRadius p ∧ planarRadius p < S + delta) ∧
      (p ∈ V ∧ S - delta < planarRadius p) at hp
    have hAbs : |planarRadius p - S| < delta := by
      rw [abs_lt]
      constructor <;> linarith [hp.1.2, hp.2.2]
    exact interior_subset (s := {p : Coord | H p = F p}) (a := p)
      (hCollar p (hAbs.trans_le hd0le)).2
  have h02 : EqOn H F (U0 ∩ (∅ : Set Coord)) := by simp
  have h12 : EqOn F F (U1 ∩ (∅ : Set Coord)) := fun _ _ => rfl
  have hCover : quadraticRadialFillingDomain S V ⊆ U0 ∪ U1 ∪ (∅ : Set Coord) := by
    intro p hp
    rcases hp.2 with hpS | hpU
    · change planarRadius p < S at hpS
      exact Or.inl (Or.inl ⟨hp.1, by linarith [hd]⟩)
    · by_cases hp0 : planarRadius p < S + delta
      · exact Or.inl (Or.inl ⟨hp.1, hp0⟩)
      · have hRadius : S - delta < planarRadius p := by
          linarith [hd, le_of_not_gt hp0]
        exact Or.inl (Or.inr ⟨hpU,hRadius⟩)
  obtain ⟨he0, he1, _⟩ := dualRadialCompletionPatch_eqOn h01 h02 h12
  refine ⟨delta, P, hd, hdSR, ?_, ?_, he0, he1⟩
  · exact (dualRadialCompletionPatch_contDiffOn hU0 hU1 isOpen_empty h01 h02 h12
      (hH.mono hSub) (hF.mono inter_subset_left) (by simp)).mono hCover
  · intro p hp
    exact dualRadialCompletionPatch_saddle hU0 hU1 isOpen_empty h01 h02 h12
      (fun p hp => hnH p (hSub hp)) (fun p hp => hnF p hp.1)
      (by simp) p (hCover hp)

end
end TightVer401
