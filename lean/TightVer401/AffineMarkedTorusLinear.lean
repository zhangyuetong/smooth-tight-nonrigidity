import TightVer401.TorusAffineMarkerEllipseBasic
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Actual linear realization of the literal triangular torus marker.
The surface is acted on by B and its bending by the distinct inverse
transpose C. Both are genuine continuous linear equivalences. The exact
cross pairing is proved, and C is identified with the actual adjoint of
B inverse. No ambient isometry or preservation of the original metric is
claimed. All support statements concern the original parameter source.
-/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped Matrix Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false

/-- The literal marker is a continuous linear equivalence. -/
def torusAffineMarkerLinearEquiv : Ambient ≃L[ℝ] Ambient where
  toFun := torusAffineMarker
  invFun := torusAffineMarkerInverse
  left_inv := torusAffineMarker_inverse_marker
  right_inv := torusAffineMarker_marker_inverse
  map_add' v w := by
    ext i
    fin_cases i <;> simp [torusAffineMarker, torusAffineMarkerVec] <;> ring
  map_smul' c v := by
    ext i
    fin_cases i <;> simp [torusAffineMarker, torusAffineMarkerVec] <;> ring
  continuous_toFun := torusAffineMarker_continuous
  continuous_invFun := torusAffineMarkerInverse_continuous

@[simp] theorem torusAffineMarkerLinearEquiv_apply (v : Ambient) :
    torusAffineMarkerLinearEquiv v = torusAffineMarker v := rfl
@[simp] theorem torusAffineMarkerLinearEquiv_symm_apply (v : Ambient) :
    torusAffineMarkerLinearEquiv.symm v = torusAffineMarkerInverse v := rfl

/-- Literal B inverse transpose, distinct from B. -/
def torusAffineMarkerContra (v : Ambient) : Ambient :=
  torusAffineMarkerVec (v 0) (v 1 / 2) (v 2 - v 0 - v 1 / 2)

/-- Literal B transpose, the inverse of the contragredient map. -/
def torusAffineMarkerContraInverse (v : Ambient) : Ambient :=
  torusAffineMarkerVec (v 0) (2 * v 1) (v 0 + v 1 + v 2)

def torusAffineMarkerContraLinearEquiv : Ambient ≃L[ℝ] Ambient where
  toFun := torusAffineMarkerContra
  invFun := torusAffineMarkerContraInverse
  left_inv v := by
    ext i
    fin_cases i <;> simp [torusAffineMarkerContra, torusAffineMarkerContraInverse,
      torusAffineMarkerVec] <;> ring
  right_inv v := by
    ext i
    fin_cases i <;> simp [torusAffineMarkerContra, torusAffineMarkerContraInverse,
      torusAffineMarkerVec] <;> ring
  map_add' v w := by
    ext i
    fin_cases i <;> simp [torusAffineMarkerContra, torusAffineMarkerVec] <;> ring
  map_smul' c v := by
    ext i
    fin_cases i <;> simp [torusAffineMarkerContra, torusAffineMarkerVec] <;> ring
  continuous_toFun := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
    apply continuous_pi
    intro i
    fin_cases i <;> fun_prop
  continuous_invFun := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
    apply continuous_pi
    intro i
    fin_cases i <;> fun_prop

@[simp] theorem torusAffineMarkerContraLinearEquiv_apply (v : Ambient) :
    torusAffineMarkerContraLinearEquiv v = torusAffineMarkerContra v := rfl

/-- Exact cross pairing that transports the infinitesimal strain. -/
theorem torusAffineMarker_dual_pairing (v w : Ambient) :
    inner ℝ (torusAffineMarker v) (torusAffineMarkerContra w) = inner ℝ v w := by
  simp [torusAffineMarker, torusAffineMarkerContra, torusAffineMarkerVec,
    PiLp.inner_apply, Fin.sum_univ_succ]
  ring

/-- The literal contragredient equivalence is the actual inverse adjoint. -/
theorem torusAffineMarkerContra_eq_inverse_adjoint :
    torusAffineMarkerContraLinearEquiv.toContinuousLinearMap =
      torusAffineMarkerLinearEquiv.symm.toContinuousLinearMap.adjoint := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  change inner ℝ (torusAffineMarkerContra x) y =
    inner ℝ x (torusAffineMarkerInverse y)
  rw [real_inner_comm]
  calc
    inner ℝ y (torusAffineMarkerContra x) = inner ℝ (torusAffineMarkerInverse y) x := by
      simpa only [torusAffineMarker_marker_inverse] using
        torusAffineMarker_dual_pairing (torusAffineMarkerInverse y) x
    _ = inner ℝ x (torusAffineMarkerInverse y) := real_inner_comm _ _

theorem torusAffineMarker_strain_transport (xv xw yv yw : Ambient) :
    inner ℝ (torusAffineMarker xv) (torusAffineMarkerContra yw) +
        inner ℝ (torusAffineMarkerContra yv) (torusAffineMarker xw) =
      inner ℝ xv yw + inner ℝ yv xw := by
  rw [torusAffineMarker_dual_pairing xv yw]
  apply congrArg (fun t : ℝ => inner ℝ xv yw + t)
  calc
    inner ℝ (torusAffineMarkerContra yv) (torusAffineMarker xw) =
        inner ℝ (torusAffineMarker xw) (torusAffineMarkerContra yv) := real_inner_comm _ _
    _ = inner ℝ xw yv := torusAffineMarker_dual_pairing xw yv
    _ = inner ℝ yv xw := real_inner_comm _ _

@[simp] theorem torusAffineMarkerContra_eq_zero_iff (v : Ambient) :
    torusAffineMarkerContra v = 0 ↔ v = 0 := by
  change torusAffineMarkerContraLinearEquiv v = 0 ↔ v = 0
  constructor
  · intro hv
    exact torusAffineMarkerContraLinearEquiv.injective
      (hv.trans (map_zero torusAffineMarkerContraLinearEquiv).symm)
  · intro hv
    rw [hv, map_zero]

theorem torusAffineMarkerContra_support {M : Type*} (Y : M → Ambient) :
    Function.support (fun p => torusAffineMarkerContra (Y p)) = Function.support Y := by
  ext p
  change torusAffineMarkerContra (Y p) ≠ 0 ↔ Y p ≠ 0
  exact not_congr (torusAffineMarkerContra_eq_zero_iff (Y p))

theorem torusAffineMarkerContra_tsupport {M : Type*} [TopologicalSpace M]
    (Y : M → Ambient) : tsupport (fun p => torusAffineMarkerContra (Y p)) = tsupport Y := by
  change closure (Function.support (fun p => torusAffineMarkerContra (Y p))) =
    closure (Function.support Y)
  rw [torusAffineMarkerContra_support]

theorem torusAffineMarkerContra_nonzero_iff {M : Type*} (Y : M → Ambient) :
    (∃ p, torusAffineMarkerContra (Y p) ≠ 0) ↔ ∃ p, Y p ≠ 0 := by
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p, (not_congr (torusAffineMarkerContra_eq_zero_iff (Y p))).mp hp⟩
  · rintro ⟨p, hp⟩
    exact ⟨p, (not_congr (torusAffineMarkerContra_eq_zero_iff (Y p))).mpr hp⟩

end
end TightVer401
