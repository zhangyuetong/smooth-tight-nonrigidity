import TightVer401.RuledBand
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry

theorem orthonormal_frame_decomposition {T E n : Ambient}
    (hf : IsOrthonormalFrame T E n) (Y : Ambient) :
    Y = (inner ℝ Y T) • T + (inner ℝ Y E) • E + (inner ℝ Y n) • n := by
  rcases hf with ⟨hTT, hEE, hnn, hTE, hTn, hEn⟩
  have hET : inner ℝ E T = 0 := by rw [real_inner_comm, hTE]
  have hnT : inner ℝ n T = 0 := by rw [real_inner_comm, hTn]
  have hnE : inner ℝ n E = 0 := by rw [real_inner_comm, hEn]
  let v : Fin 3 → Ambient := ![T, E, n]
  have hv : Orthonormal ℝ v := orthonormal_iff_ite.mpr (by
    intro i j
    fin_cases i <;> fin_cases j
    · exact hTT
    · exact hTE
    · exact hTn
    · exact hET
    · exact hEE
    · exact hEn
    · exact hnT
    · exact hnE
    · exact hnn)
  let B := basisOfOrthonormalOfCardEqFinrank hv (by simp [Ambient])
  have hB : (B : Fin 3 → Ambient) = v := coe_basisOfOrthonormalOfCardEqFinrank hv _
  let e := B.toOrthonormalBasis (by simpa only [hB] using hv)
  have he : (e : Fin 3 → Ambient) = v := by
    rw [Module.Basis.coe_toOrthonormalBasis]
    exact hB
  have h := e.sum_repr' Y
  simp only [he, Fin.sum_univ_succ, v, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.sum_univ_zero, add_zero] at h
  simpa only [real_inner_comm, add_assoc] using h.symm

end
end TightVer401
