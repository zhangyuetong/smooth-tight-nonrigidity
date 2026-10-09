import TightVer401.BandBendingMetricFamily
import TightVer401.BandBendingCompactCurvature
import TightVer401.CoordinateBendingPullback
import TightVer401.SurfaceMetric
import TightVer401.CurvatureLocality

/-! Curvature stability for actual smooth infinitesimal bendings. The family is
formed from the perturbed maps themselves. Joint curvature continuity is proved
from their actual Frechet derivatives and the pinned intrinsic metric formula. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

/-- Joint smoothness of the actual induced metric, including parameter dependence. -/
theorem bandBending_inducedMetric_family_contDiffOn
    {X Y : Coord → Ambient} {U : Set Coord}
    (hX : ContDiffOn ℝ ∞ X U) (hY : ContDiffOn ℝ ∞ Y U)
    (hU : IsOpen U) (i j : Fin 2) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × Coord => inducedMetric (fun q => X q + z.1 • Y q) z.2 i j)
      (univ ×ˢ U) := by
  let F : ℝ × Coord → Ambient := fun z => X z.2 + z.1 • Y z.2
  have hx : ContDiffOn ℝ ∞ (fun z : ℝ × Coord => X z.2) (univ ×ˢ U) :=
    hX.comp contDiffOn_snd (fun _ hz => hz.2)
  have hy : ContDiffOn ℝ ∞ (fun z : ℝ × Coord => Y z.2) (univ ×ˢ U) :=
    hY.comp contDiffOn_snd (fun _ hz => hz.2)
  have hf : ContDiffOn ℝ ∞ F (univ ×ˢ U) := hx.add (contDiffOn_fst.smul hy)
  exact (bandBending_sliceCoordPartial_contDiffOn hf (isOpen_univ.prod hU) i).inner ℝ
    (bandBending_sliceCoordPartial_contDiffOn hf (isOpen_univ.prod hU) j)

/-- Zero strain prevents loss of immersion at every amplitude. -/
theorem bandBending_coordinate_branch_immersion
    {X Y : Coord → Ambient} {p : Coord}
    (hX : DifferentiableAt ℝ X p) (hY : DifferentiableAt ℝ Y p)
    (hstrain : ∀ i j, strain X Y p i j = 0)
    (himm : Function.Injective (fderiv ℝ X p)) (a : ℝ) :
    Function.Injective (fderiv ℝ (fun q => X q + a • Y q) p) := by
  intro v w he
  let z := v - w
  have hz : fderiv ℝ (fun q => X q + a • Y q) p z = 0 := by
    simp only [z, map_sub, he, sub_self]
  have hd : fderiv ℝ (fun q => X q + a • Y q) p z =
      fderiv ℝ X p z + a • fderiv ℝ Y p z := by
    rw [fderiv_fun_add hX (hY.fun_const_smul a), fderiv_fun_const_smul hY a]
    rfl
  have hs := zero_strain_all_vectors hstrain z z
  have hn : inner ℝ (fderiv ℝ X p z) (fderiv ℝ X p z) +
      a^2 * inner ℝ (fderiv ℝ Y p z) (fderiv ℝ Y p z) = 0 := by
    have hh := congrArg (fun t : Ambient => inner ℝ t t) (hd.symm.trans hz)
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, inner_zero_left] at hh
    nlinarith [congrArg (fun r : ℝ => a * r) hs]
  have hnonneg : 0 ≤ a^2 * inner ℝ (fderiv ℝ Y p z) (fderiv ℝ Y p z) :=
    mul_nonneg (sq_nonneg a) real_inner_self_nonneg
  have hxzero : inner ℝ (fderiv ℝ X p z) (fderiv ℝ X p z) = 0 := by
    linarith [real_inner_self_nonneg (x := fderiv ℝ X p z)]
  have hdz : fderiv ℝ X p z = 0 := inner_self_eq_zero.mp hxzero
  apply himm
  exact sub_eq_zero.mp (by simpa only [z, map_sub] using hdz)

/-- Joint intrinsic curvature smoothness derived for a genuine infinitesimal bending. -/
theorem bandBending_actual_curvature_family_contDiffOn
    {X Y : Coord → Ambient} {U : Set Coord}
    (hX : ContDiffOn ℝ ∞ X U) (hY : IsInfinitesimalBendingOn X Y U)
    (hU : IsOpen U) (himm : ∀ p ∈ U, Function.Injective (fderiv ℝ X p)) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Coord =>
      gaussianCurvature (inducedMetric (fun q => X q + z.1 • Y q)) z.2) (univ ×ˢ U) := by
  apply bandBending_metricFamily_curvature_contDiffOn
    (G := fun a => inducedMetric (fun q => X q + a • Y q))
    (bandBending_inducedMetric_family_contDiffOn hX hY.1 hU)
  · intro z hz
    apply inducedMetric_posDef
    exact bandBending_coordinate_branch_immersion
      (((hX z.2 hz.2).contDiffAt (hU.mem_nhds hz.2)).differentiableAt (by simp))
      (((hY.1 z.2 hz.2).contDiffAt (hU.mem_nhds hz.2)).differentiableAt (by simp))
      (hY.2 z.2 hz.2) (himm z.2 hz.2) z.1
  · exact isOpen_univ.prod hU

/-- One amplitude bound preserves actual negative intrinsic curvature on a compact region. -/
theorem bandBending_compact_actual_curvature_threshold
    {X Y : Coord → Ambient} {U K : Set Coord}
    (hX : ContDiffOn ℝ ∞ X U) (hY : IsInfinitesimalBendingOn X Y U)
    (hU : IsOpen U) (himm : ∀ p ∈ U, Function.Injective (fderiv ℝ X p))
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hneg : ∀ p ∈ K, gaussianCurvature (inducedMetric X) p < 0) :
    ∃ δ > 0, ∀ a : ℝ, |a| < δ → ∀ p ∈ K,
      gaussianCurvature (inducedMetric (fun q => X q + a • Y q)) p < 0 := by
  have hc := (bandBending_actual_curvature_family_contDiffOn hX hY hU himm).continuousOn
  apply bandBending_compact_uniform_negative_parameter
    (F := fun z : ℝ × Coord => gaussianCurvature (inducedMetric (fun q => X q + z.1 • Y q)) z.2) hK
  · intro p hp
    exact (hc (0,p) ⟨mem_univ _, hKU hp⟩).continuousAt
      ((isOpen_univ.prod hU).mem_nhds ⟨mem_univ _, hKU hp⟩)
  · intro p hp
    simpa only [zero_smul, add_zero] using hneg p hp

end
end TightVer401
