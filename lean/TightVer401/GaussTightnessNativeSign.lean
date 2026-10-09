import TightVer401.NativeProductPlaneTorusCoordinates
import TightVer401.GaussTightnessDefiniteSign
import Mathlib.Topology.Algebra.Group.Quotient

/-! The actual preferred native second fundamental form is a continuous matrix
family. Flat quotient charts differ by literal translations on their entire
coordinate domain, so no chosen germ or substituted matrix is used. -/
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false
local instance nativeSignPeriod : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- Every native representative at a covered point is exactly a translate of
one globally smooth quotient representative, on its ENTIRE domain. -/
theorem nativeProductCoordinateMap_at_cover_eq_translate
    (X : NonrigidTorusSource → Ambient) (s u : ℝ) (q : Coord) :
    nativeProductCoordinateMap X (nativeProductTorusCoordinateCover s u q) =
      fun r => (X ∘ nativeProductTorusCoordinateCover s u) (q + r) := by
  rw [nativeProductTorusCoordinateMap_eq_cover X
    (nativeProductTorusCoordinateCover s u q) (s + q 0) (u + q 1) rfl rfl]
  funext r
  simp only [Function.comp_def, nativeProductTorusCoordinateCover, Pi.add_apply, add_assoc]

/-- Actual coordinate derivatives commute with translation, without any
regularity premise because this is the total fderiv translation identity. -/
theorem gaussSign_coordPartial_comp_add_left
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (i : Fin 2) (F : Coord → V) (q : Coord) :
    coordPartial i (fun r => F (q + r)) = fun r => coordPartial i F (q + r) := by
  funext r
  simp only [coordPartial, fderiv_comp_add_left]

/-- Actual second fundamental forms of translated native representatives
agree at the matching physical coordinate. -/
theorem nativeProduct_secondFundamental_at_cover
    (X : NonrigidTorusSource → Ambient) (s u : ℝ) (q : Coord) (n : Ambient) :
    secondFundamental
      (nativeProductCoordinateMap X (nativeProductTorusCoordinateCover s u q)) n 0 =
    secondFundamental (X ∘ nativeProductTorusCoordinateCover s u) n q := by
  rw [nativeProductCoordinateMap_at_cover_eq_translate]
  ext i j
  simp only [secondFundamental, gaussSign_coordPartial_comp_add_left, add_zero]

/-- The actual zero-centered preferred native second fundamental form for the
SAME embedding and global normal. -/
def nativeTorusSecondFundamental (X : NonrigidTorusSource → Ambient)
    (N : NonrigidTorusSource → RoundSphere) (p : NonrigidTorusSource) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  secondFundamental (nativeProductCoordinateMap X p) (N p : Ambient) 0

/-- The zero-based quotient cover is an actual open surjection, hence a quotient
map. This is a topological statement about the registered native torus. -/
theorem nativeProductTorusCoordinateCover_zero_isQuotientMap :
    Topology.IsQuotientMap (nativeProductTorusCoordinateCover 0 0) := by
  have hP : IsOpenMap (periodProjection (2 * Real.pi)) :=
    QuotientAddGroup.isOpenMap_coe
  have hopen : IsOpenMap (nativeProductTorusCoordinateCover 0 0) := by
    have hprod := (hP.prodMap hP).comp
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).toHomeomorph.isOpenMap
    convert! hprod using 1
    funext q
    change (periodProjection (2 * Real.pi) (0 + q 0),
      periodProjection (2 * Real.pi) (0 + q 1)) =
      (periodProjection (2 * Real.pi) (q 0), periodProjection (2 * Real.pi) (q 1))
    simp only [zero_add]
  have hsurj : Function.Surjective (nativeProductTorusCoordinateCover 0 0) := by
    intro p
    obtain ⟨s, hs⟩ := QuotientAddGroup.mk_surjective p.1
    obtain ⟨u, hu⟩ := QuotientAddGroup.mk_surjective p.2
    change periodProjection (2 * Real.pi) s = p.1 at hs
    change periodProjection (2 * Real.pi) u = p.2 at hu
    refine ⟨![s, u], ?_⟩
    apply Prod.ext
    · change periodProjection (2 * Real.pi) (0 + s) = p.1
      simpa only [zero_add] using hs
    · change periodProjection (2 * Real.pi) (0 + u) = p.2
      simpa only [zero_add] using hu
  exact hopen.isQuotientMap
    (nativeProductTorusCoordinateCover_contMDiff 0 0).continuous hsurj

/-- Smoothness of the actual map and continuity of its actual normal give
continuity of the actual preferred native II matrix on the whole torus. -/
theorem nativeTorusSecondFundamental_continuous
    {X : NonrigidTorusSource → Ambient}
    (hX : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ X)
    {N : NonrigidTorusSource → RoundSphere} (hN : Continuous N) :
    Continuous (nativeTorusSecondFundamental X N) := by
  let F : Coord → Ambient := X ∘ nativeProductTorusCoordinateCover 0 0
  have hF : ContDiff ℝ ∞ F :=
    (hX.comp (nativeProductTorusCoordinateCover_contMDiff 0 0)).contDiff
  have hpartial (i : Fin 2) : ContDiff ℝ ∞ (coordPartial i F) :=
    contDiffOn_univ.mp (partial_contDiffOn hF.contDiffOn isOpen_univ i)
  have hsecond (i j : Fin 2) : ContDiff ℝ ∞ (coordPartial i (coordPartial j F)) :=
    contDiffOn_univ.mp (partial_contDiffOn (hpartial j).contDiffOn isOpen_univ i)
  have hnormal : Continuous (fun q : Coord =>
      (N (nativeProductTorusCoordinateCover 0 0 q) : Ambient)) :=
    continuous_subtype_val.comp (hN.comp
      (nativeProductTorusCoordinateCover_contMDiff 0 0).continuous)
  have hcoeff (i j : Fin 2) : Continuous (fun q : Coord =>
      nativeTorusSecondFundamental X N (nativeProductTorusCoordinateCover 0 0 q) i j) := by
    have heq : (fun q : Coord => nativeTorusSecondFundamental X N
        (nativeProductTorusCoordinateCover 0 0 q) i j) =
        (fun q => inner ℝ (coordPartial i (coordPartial j F) q)
          (N (nativeProductTorusCoordinateCover 0 0 q) : Ambient)) := by
      funext q
      rw [nativeTorusSecondFundamental, nativeProduct_secondFundamental_at_cover]
      rfl
    rw [heq]
    exact (hsecond i j).continuous.inner hnormal
  apply nativeProductTorusCoordinateCover_zero_isQuotientMap.continuous_iff.mpr
  exact continuous_pi fun i => continuous_pi fun j => hcoeff i j

/-- The ACTUAL trace classifier is continuous on the whole native torus. -/
theorem nativeTorusSecondFundamental_trace_continuous
    {X : NonrigidTorusSource → Ambient}
    (hX : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ X)
    {N : NonrigidTorusSource → RoundSphere}
    (hN : ContMDiff nativeProductModel (𝓡 2) ∞ N) :
    Continuous (fun p => (secondFundamental
      (nativeProductCoordinateMap X p) (N p : Ambient) 0).trace) := by
  apply continuousOn_univ.mp
  exact real_two_matrix_continuousOn_trace (nativeTorusSecondFundamental X N)
    (nativeTorusSecondFundamental_continuous hX hN.continuous).continuousOn

end
end TightVer401


