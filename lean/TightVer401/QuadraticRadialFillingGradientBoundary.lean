import TightVer401.QuadraticRadialFillingCircle
import TightVer401.PlanarGradientInverse
import Mathlib.Topology.Separation.Hausdorff

/-! Ordinary boundary data for the quadratic filling application.
Local inverses are derived from the actual Cartesian Hessian. Injectivity on
one compact circle then gives injectivity on an actual open neighborhood. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

/-- The actual gradient trace along the radius-R circle. -/
def quadraticRadialFillingGradientTrace (F : Coord → ℝ) (R : ℝ) : ℝ → Coord :=
  fun s => planarGradient F (saddlePolarChart ![R,s])

theorem quadraticRadialFillingCircle_isCompact {R : ℝ} (hR : 0 < R) :
    IsCompact {x : Coord | planarRadius x = R} := by
  letI : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
  rw [← quadraticRadialFillingCircle_seam hR]
  exact isCompact_range ((seamNormalNative_continuous
    (quadraticRadialFillingCircle_contDiff R)
    (quadraticRadialFillingCircle_periodic R)).comp
      (continuous_id.prodMk continuous_const))

/-- Boundary injectivity and the actual nonzero Hessian determinant imply
an injective open collar of the gradient; no inverse package is an input. -/
theorem quadraticRadialFillingGradient_exists_injective_neighborhood
    {F : Coord → ℝ} {R : ℝ} {U : Set Coord}
    (hR : 0 < R) (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (hCircleU : {x : Coord | planarRadius x = R} ⊆ U)
    (hdet : ∀ x, planarRadius x = R → (planarHessian F x).det < 0)
    (hinj : InjOn (planarGradient F) {x : Coord | planarRadius x = R}) :
    ∃ W : Set Coord, IsOpen W ∧ {x : Coord | planarRadius x = R} ⊆ W ∧
      W ⊆ U ∧ InjOn (planarGradient F) W := by
  have hcont : ∀ x ∈ {x : Coord | planarRadius x = R},
      ContinuousAt (planarGradient F) x := by
    intro x hx
    exact ((planarGradient_contDiffOn hF hU) x (hCircleU hx)).contDiffAt
      (hU.mem_nhds (hCircleU hx)) |>.continuousAt
  have hlocal : ∀ x ∈ {x : Coord | planarRadius x = R},
      ∃ W ∈ 𝓝 x, InjOn (planarGradient F) W := by
    intro x hx
    obtain ⟨e, he, heU, hef, hei⟩ := planarGradient_exists_smooth_local_inverse_at
      hF hU (hCircleU hx) (ne_of_lt (hdet x hx))
    refine ⟨e.source, e.open_source.mem_nhds he, ?_⟩
    rw [← hef]
    exact e.injOn
  obtain ⟨W, hW, hCircleW, hinjW⟩ := hinj.exists_isOpen_superset
    (quadraticRadialFillingCircle_isCompact hR) hcont hlocal
  exact ⟨W ∩ U, hW.inter hU, fun x hx => ⟨hCircleW hx, hCircleU hx⟩,
    inter_subset_right, hinjW.mono inter_subset_left⟩

theorem quadraticRadialFillingGradientTrace_periodic (F : Coord → ℝ) (R : ℝ) :
    Function.Periodic (quadraticRadialFillingGradientTrace F R) (2 * Real.pi) := by
  intro s
  change planarGradient F (saddlePolarChart ![R,s + 2 * Real.pi]) =
    planarGradient F (saddlePolarChart ![R,s])
  rw [← quadraticRadialFillingCircle_coord R (s + 2 * Real.pi),
    ← quadraticRadialFillingCircle_coord R s,
    quadraticRadialFillingCircle_periodic R s]

theorem quadraticRadialFillingGradientTrace_contDiff
    {F : Coord → ℝ} {R : ℝ} {U : Set Coord}
    (hR : 0 < R) (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (hCircleU : {x : Coord | planarRadius x = R} ⊆ U) :
    ContDiff ℝ ∞ (quadraticRadialFillingGradientTrace F R) := by
  have hc : ContDiff ℝ ∞ (fun s : ℝ => saddlePolarChart ![R,s]) := by
    simpa only [Function.comp_def, quadraticRadialFillingCircle_coord] using
      seamComplexCoord.contDiff.comp (quadraticRadialFillingCircle_contDiff R)
  apply contDiffOn_univ.mp
  apply (planarGradient_contDiffOn hF hU).comp hc.contDiffOn
  intro s hs
  apply hCircleU
  exact angularDescent_radius_polar (q := ![R,s]) hR

/-- The circle tangent is an actual nonzero Cartesian vector. -/
theorem quadraticRadialFillingCircle_tangent_ne_zero {R : ℝ} (hR : 0 < R) (s : ℝ) :
    seamComplexCoord (quadraticRadialFillingCircle R s * Complex.I) ≠ 0 := by
  intro h
  have he : quadraticRadialFillingCircle R s * Complex.I = 0 :=
    seamComplexCoord.injective (by simpa only [map_zero] using h)
  exact (mul_ne_zero (circleMap_ne_center hR.ne') Complex.I_ne_zero) he

/-- Differentiating the actual boundary gradient multiplies its nonzero
circle tangent by the Cartesian Hessian. -/
theorem quadraticRadialFillingGradientTrace_hasDerivAt
    {F : Coord → ℝ} {R : ℝ} {U : Set Coord}
    (hR : 0 < R) (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (hCircleU : {x : Coord | planarRadius x = R} ⊆ U) (s : ℝ) :
    HasDerivAt (quadraticRadialFillingGradientTrace F R)
      (planarHessian F (saddlePolarChart ![R,s]) *ᵥ
        seamComplexCoord (quadraticRadialFillingCircle R s * Complex.I)) s := by
  have hp : saddlePolarChart ![R,s] ∈ U :=
    hCircleU (angularDescent_radius_polar (q := ![R,s]) hR)
  have hc : HasDerivAt (fun t : ℝ => saddlePolarChart ![R,t])
      (seamComplexCoord (quadraticRadialFillingCircle R s * Complex.I)) s := by
    have hd : HasDerivAt
        (fun t : ℝ => seamComplexCoord (quadraticRadialFillingCircle R t))
        (seamComplexCoord (quadraticRadialFillingCircle R s * Complex.I)) s :=
      seamComplexCoord.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_circleMap 0 R s)
    simpa only [quadraticRadialFillingCircle_coord] using hd
  have hg := ((planarGradient_contDiffOn hF hU) _ hp).contDiffAt (hU.mem_nhds hp)
  have hd := (hg.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt s hc
  rw [planarGradient_fderiv_apply hF hU hp] at hd
  convert hd using 1 <;> rfl

/-- Negative determinant supplies boundary regularity, rather than requiring
regularity of the image circle as an additional hypothesis. -/
theorem quadraticRadialFillingGradientTrace_regular
    {F : Coord → ℝ} {R : ℝ} {U : Set Coord}
    (hR : 0 < R) (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (hCircleU : {x : Coord | planarRadius x = R} ⊆ U)
    (hdet : ∀ x, planarRadius x = R → (planarHessian F x).det < 0) (s : ℝ) :
    deriv (quadraticRadialFillingGradientTrace F R) s ≠ 0 := by
  have hp : saddlePolarChart ![R,s] ∈ U :=
    hCircleU (angularDescent_radius_polar (q := ![R,s]) hR)
  have hi := planarGradient_differential_injective hF hU hp
    (ne_of_lt (hdet _ (angularDescent_radius_polar (q := ![R,s]) hR)))
  rw [(quadraticRadialFillingGradientTrace_hasDerivAt hR hU hF hCircleU s).deriv]
  intro hz
  apply quadraticRadialFillingCircle_tangent_ne_zero hR s
  apply hi
  simpa only [planarGradient_fderiv_apply hF hU hp, Matrix.mulVec_zero] using hz

end
end TightVer401

