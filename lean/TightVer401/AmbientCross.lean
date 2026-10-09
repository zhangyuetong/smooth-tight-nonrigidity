import TightVer401.RuledNormal
import Mathlib.LinearAlgebra.CrossProduct

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped Matrix

def ambientCross (v w : Ambient) : Ambient :=
  WithLp.toLp 2 (crossProduct (fun i => v i) (fun i => w i))

theorem ambient_inner_dot (v w : Ambient) :
    inner ℝ v w = dotProduct (fun i => v i) (fun i => w i) := by
  simp [PiLp.inner_apply, dotProduct, mul_comm]

theorem ambientCross_add_left (v w z : Ambient) :
    ambientCross (v + w) z = ambientCross v z + ambientCross w z := by
  ext i
  change (crossProduct (fun j => v j + w j) (fun j => z j)) i =
    (crossProduct (fun j => v j) (fun j => z j)) i +
      (crossProduct (fun j => w j) (fun j => z j)) i
  fin_cases i <;> simp [cross_apply] <;> ring

theorem ambientCross_smul_left (a : ℝ) (v w : Ambient) :
    ambientCross (a • v) w = a • ambientCross v w := by
  ext i
  change (crossProduct (fun j => a * v j) (fun j => w j)) i =
    a * (crossProduct (fun j => v j) (fun j => w j)) i
  fin_cases i <;> simp [cross_apply] <;> ring

theorem ambientCross_orthogonal_left (v w : Ambient) :
    inner ℝ v (ambientCross v w) = 0 := by
  rw [ambient_inner_dot]
  exact dot_self_cross (fun i => v i) (fun i => w i)

theorem ambientCross_orthogonal_right (v w : Ambient) :
    inner ℝ w (ambientCross v w) = 0 := by
  rw [ambient_inner_dot]
  exact dot_cross_self (fun i => v i) (fun i => w i)

theorem ambientCross_triple_det (a b c : Ambient) :
    inner ℝ c (ambientCross a b) = Matrix.det ![fun i => a i, fun i => b i, fun i => c i] := by
  rw [ambient_inner_dot]
  exact (triple_product_permutation (fun i => c i) (fun i => a i) (fun i => b i)).trans
    (triple_product_eq_det (fun i => a i) (fun i => b i) (fun i => c i))

theorem ambientCross_ne_zero_of_triple {a b c : Ambient}
    (h : inner ℝ c (ambientCross a b) ≠ 0) : ambientCross a b ≠ 0 := by
  intro hz
  exact h (by rw [hz, inner_zero_right])

end
end TightVer401
