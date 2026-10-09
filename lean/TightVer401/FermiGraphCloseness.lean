import TightVer401.ExitPositiveGraphDomain
import TightVer401.FermiNormalGeometry

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Matrix
set_option backward.isDefEq.respectTransparency false

theorem fermiGraph_exists_uniform_closeness_radius {ζ : ℝ → Ambient} {v : ℝ → ℝ}
    {P η : ℝ} (hP : 0 < P) (hη : 0 < η)
    (hζ : ContDiff ℝ ∞ ζ) (hζP : Function.Periodic ζ P)
    (hv : ContDiff ℝ ∞ v) (hvP : Function.Periodic v P) :
    ∃ e > 0, ∀ δ : ℝ, |δ| < e → ∀ r,
      ‖fermiNormalMap ζ (exitGraphCurve v δ r) - ζ r‖ < η := by
  let U : Set Coord := {p | ‖fermiNormalMap ζ p - ζ (p 0)‖ < η}
  have hcont : Continuous (fun p : Coord => ‖fermiNormalMap ζ p - ζ (p 0)‖) :=
    ((fermiNormalMap_contDiff hζ).continuous.sub
      (hζ.continuous.comp (continuous_apply 0))).norm
  have hU : IsOpen U := isOpen_lt hcont continuous_const
  have hc : ∀ r ∈ Icc (0 : ℝ) P, (![r,0] : Coord) ∈ U := by
    intro r _
    change ‖fermiNormalMap ζ ![r,0] - ζ r‖ < η
    simpa [fermiNormalMap] using hη
  obtain ⟨e, he, hb⟩ := exitGraphCurve_uniform_domain hv hU hc
  refine ⟨e, he, fun δ hδ r => ?_⟩
  have hp : Function.Periodic (fun r => ‖fermiNormalMap ζ (exitGraphCurve v δ r) - ζ r‖) P := by
    intro r
    simp only [fermiNormalMap, exitGraphCurve, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, hvP r, hζP r,
      (normalLoop_actual_periodic hζ hζP).1 r]
  let s := toIcoMod hP 0 r
  have hs : s ∈ Ico 0 P := toIcoMod_mem_Ico' hP r
  have hval : ‖fermiNormalMap ζ (exitGraphCurve v δ s) - ζ s‖ =
      ‖fermiNormalMap ζ (exitGraphCurve v δ r) - ζ r‖ :=
    hp.sub_zsmul_eq (toIcoDiv hP 0 r)
  rw [← hval]
  exact hb s ⟨hs.1, hs.2.le⟩ δ hδ.le

end
end TightVer401
