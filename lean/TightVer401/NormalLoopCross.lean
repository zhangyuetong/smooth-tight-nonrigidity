import TightVer401.AmbientCrossSmooth
import TightVer401.GeneralRuledCurvature
import TightVer401.FrameDecomposition
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Prod

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

theorem normalLoopCross_add_right (u v w : Ambient) :
    ambientCross u (v + w) = ambientCross u v + ambientCross u w := by
  ext i
  fin_cases i <;> simp [ambientCross, cross_apply] <;> ring

theorem normalLoopCross_smul_right (a : ℝ) (u v : Ambient) :
    ambientCross u (a • v) = a • ambientCross u v := by
  ext i
  fin_cases i <;> simp [ambientCross, cross_apply] <;> ring

theorem normalLoopCross_neg_right (u v : Ambient) :
    ambientCross u (-v) = -ambientCross u v := by
  simpa using normalLoopCross_smul_right (-1) u v

theorem normalLoopCross_double (u v w : Ambient) :
    ambientCross u (ambientCross v w) =
      (inner ℝ u w) • v - (inner ℝ v u) • w := by
  have h := cross_cross_eq_smul_sub_smul' (fun i => u i) (fun i => v i) (fun i => w i)
  rw [ambient_inner_dot, ambient_inner_dot]
  ext i
  exact congrFun h i

theorem normalLoopCross_hasDerivAt {f g : ℝ → Ambient} {f' g' : Ambient} {r : ℝ}
    (hf : HasDerivAt f f' r) (hg : HasDerivAt g g' r) :
    HasDerivAt (fun t => ambientCross (f t) (g t))
      (ambientCross f' (g r) + ambientCross (f r) g') r := by
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  have hfc : ∀ i : Fin 3, HasDerivAt (fun t => f t i) (f' i) r := by
    intro i
    exact (PiLp.proj 2 (fun _ : Fin 3 => ℝ) i).hasFDerivAt.comp_hasDerivAt r hf
  have hgc : ∀ i : Fin 3, HasDerivAt (fun t => g t i) (g' i) r := by
    intro i
    exact (PiLp.proj 2 (fun _ : Fin 3 => ℝ) i).hasFDerivAt.comp_hasDerivAt r hg
  have hh : HasDerivAt (fun t => e (ambientCross (f t) (g t)))
      (e (ambientCross f' (g r) + ambientCross (f r) g')) r := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · convert ((hfc 1).mul (hgc 2)).sub ((hfc 2).mul (hgc 1)) using 1 <;>
        simp [e, ambientCross, cross_apply, Pi.mul_def, Pi.sub_def] <;> ring
    · convert ((hfc 2).mul (hgc 0)).sub ((hfc 0).mul (hgc 2)) using 1 <;>
        simp [e, ambientCross, cross_apply, Pi.mul_def, Pi.sub_def] <;> ring
    · convert ((hfc 0).mul (hgc 1)).sub ((hfc 1).mul (hgc 0)) using 1 <;>
        simp [e, ambientCross, cross_apply, Pi.mul_def, Pi.sub_def] <;> ring
  have hback := e.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt r hh
  change HasDerivAt (fun t => e.symm (e (ambientCross (f t) (g t))))
    (e.symm (e (ambientCross f' (g r) + ambientCross (f r) g'))) r at hback
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using hback

end
end TightVer401
