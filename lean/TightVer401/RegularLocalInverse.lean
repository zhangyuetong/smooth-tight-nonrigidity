import Mathlib
import TightVer401.SurfaceMetric

/-! The inverse function theorem supplies the inverse and its smoothness from
injectivity of the actual differential, rather than a prescribed inverse. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

def regularCoordinateEquiv (f : Coord → Coord) (p : Coord)
    (hi : Function.Injective (fderiv ℝ f p)) : Coord ≃L[ℝ] Coord :=
  ContinuousLinearEquiv.ofBijective (fderiv ℝ f p)
    (LinearMap.ker_eq_bot.mpr hi)
    (LinearMap.range_eq_top.mpr (LinearMap.injective_iff_surjective.mp hi))

theorem regularCoordinateEquiv_hasFDerivAt {f : Coord → Coord} {p : Coord}
    (hd : DifferentiableAt ℝ f p) (hi : Function.Injective (fderiv ℝ f p)) :
    HasFDerivAt f (regularCoordinateEquiv f p hi : Coord →L[ℝ] Coord) p := by
  simpa only [regularCoordinateEquiv, ContinuousLinearEquiv.coe_ofBijective] using hd.hasFDerivAt

theorem exists_smooth_local_inverse {f : Coord → Coord} {U : Set Coord}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (hi : ∀ p ∈ U, Function.Injective (fderiv ℝ f p)) {p : Coord} (hp : p ∈ U) :
    ∃ e : OpenPartialHomeomorph Coord Coord,
      p ∈ e.source ∧ e.source ⊆ U ∧ (e : Coord → Coord) = f ∧
      ContDiffOn ℝ ∞ e.symm e.target := by
  have hfp := (hf p hp).contDiffAt (hU.mem_nhds hp)
  have hdp := regularCoordinateEquiv_hasFDerivAt (hfp.differentiableAt (by simp)) (hi p hp)
  let e₀ := hfp.toOpenPartialHomeomorph f hdp (by simp)
  let e := e₀.restrOpen U hU
  have hefun : (e : Coord → Coord) = f := rfl
  refine ⟨e, ⟨hfp.mem_toOpenPartialHomeomorph_source hdp (by simp), hp⟩,
    (fun q hq => hq.2), hefun, ?_⟩
  intro y hy
  have hx : e.symm y ∈ U := (e.map_target hy).2
  have hfx := (hf _ hx).contDiffAt (hU.mem_nhds hx)
  have hdx := regularCoordinateEquiv_hasFDerivAt (hfx.differentiableAt (by simp)) (hi _ hx)
  apply (e.contDiffAt_symm hy (f₀' := regularCoordinateEquiv f (e.symm y) (hi _ hx))
    (by rw [hefun]; exact hdx) (by rw [hefun]; exact hfx)).contDiffWithinAt

end
end TightVer401
