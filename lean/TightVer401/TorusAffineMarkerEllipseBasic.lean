import TightVer401.ParabolicConvexClosureBodySupport
import Mathlib.Topology.MetricSpace.Isometry

/-! Literal ver104 affine marker and its ordinary single-ellipse recognition
interface, instantiated in the pinned Ambient. No legacy proof engine import
or stabilizer conclusion is a background premise. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped Matrix Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false

def torusAffineMarkerVec (x y z : ℝ) : Ambient := WithLp.toLp 2 ![x,y,z]
def torusAffineMarker (v : Ambient) : Ambient :=
  torusAffineMarkerVec (v 0 + v 2) (2 * v 1 + v 2) (v 2)
def torusAffineMarkerInverse (v : Ambient) : Ambient :=
  torusAffineMarkerVec (v 0 - v 2) ((v 1 - v 2) / 2) (v 2)

@[simp] theorem torusAffineMarker_inverse_marker (v : Ambient) :
    torusAffineMarkerInverse (torusAffineMarker v) = v := by
  ext i
  fin_cases i <;> simp [torusAffineMarkerInverse, torusAffineMarker, torusAffineMarkerVec] <;> ring
@[simp] theorem torusAffineMarker_marker_inverse (v : Ambient) :
    torusAffineMarker (torusAffineMarkerInverse v) = v := by
  ext i
  fin_cases i <;> simp [torusAffineMarkerInverse, torusAffineMarker, torusAffineMarkerVec] <;> ring

theorem torusAffineMarker_injective : Function.Injective torusAffineMarker :=
  Function.LeftInverse.injective torusAffineMarker_inverse_marker
@[simp] theorem torusAffineMarker_neg (v : Ambient) : torusAffineMarker (-v) = -torusAffineMarker v := by
  ext i
  fin_cases i <;> simp [torusAffineMarker, torusAffineMarkerVec] <;> ring

theorem torusAffineMarker_continuous : Continuous torusAffineMarker := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i <;> fun_prop

theorem torusAffineMarkerInverse_continuous : Continuous torusAffineMarkerInverse := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i <;> fun_prop

def torusAffineMarkerHomeomorph : Ambient ≃ₜ Ambient where
  toFun := torusAffineMarker
  invFun := torusAffineMarkerInverse
  left_inv := torusAffineMarker_inverse_marker
  right_inv := torusAffineMarker_marker_inverse
  continuous_toFun := torusAffineMarker_continuous
  continuous_invFun := torusAffineMarkerInverse_continuous

def torusAffineMarkerEllipse (c : Ambient) (a b : ℝ) : Set Ambient :=
  {p | p 2 = c 2 ∧ ((p 0-c 0)/a)^2+((p 1-c 1)/b)^2 = 1}

def torusAffineMarkerIsometry (L : Ambient ≃ₗᵢ[ℝ] Ambient) (b : Ambient) (p : Ambient) : Ambient := L p+b

/-- Generic classical theorem: an affine isometry carrying a noncircular
axis-aligned planar ellipse to its translate carries its center to the
new center and preserves each of its three principal-axis lines. No pair
of boundary curves or surface stabilizer is included in this premise. -/
def MarkerEllipseAxesRecognition : Prop :=
  ∀ (L : Ambient ≃ₗᵢ[ℝ] Ambient) (b c d : Ambient) (a e : ℝ), 0 < a → a < e →
    torusAffineMarkerIsometry L b '' torusAffineMarkerEllipse c a e = torusAffineMarkerEllipse d a e →
    torusAffineMarkerIsometry L b c = d ∧ ∃ σ : Fin 3 → ℝ,
      (∀ i, σ i = 1 ∨ σ i = -1) ∧ ∀ p i, L p i = σ i*p i

def torusAffineMarkerCenter (h : ℝ) : Ambient := torusAffineMarkerVec h h h

theorem torusAffineMarker_center_neg (h : ℝ) : torusAffineMarkerCenter (-h) = -torusAffineMarkerCenter h := by
  ext i; fin_cases i <;> simp [torusAffineMarkerCenter,torusAffineMarkerVec]

/-- Literal circles become exactly the manuscript's shifted ellipses. -/
theorem torusAffineMarker_circle_image (R h : ℝ) (hR : R ≠ 0) :
    torusAffineMarker '' {p : Ambient | p 2 = h ∧ (p 0)^2+(p 1)^2=R^2} =
      torusAffineMarkerEllipse (torusAffineMarkerCenter h) R (2*R) := by
  ext p
  constructor
  · rintro ⟨q,⟨hq,hcircle⟩,rfl⟩
    simp only [torusAffineMarkerEllipse,mem_ofPred_eq,torusAffineMarker,torusAffineMarkerCenter,torusAffineMarkerVec] at *
    refine ⟨hq,?_⟩
    rw [hq]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one] 
    field_simp
    nlinarith
  · intro hp
    simp [torusAffineMarkerEllipse,torusAffineMarkerCenter,torusAffineMarkerVec] at hp
    refine ⟨torusAffineMarkerInverse p,⟨?_,?_⟩,?_⟩
    · simpa [torusAffineMarkerInverse,torusAffineMarkerVec] using hp.1
    · have he := hp.2
      field_simp at he
      simp [torusAffineMarkerInverse,torusAffineMarkerVec]
      rw [hp.1]
      nlinarith
    · ext i; fin_cases i <;> simp [torusAffineMarker,torusAffineMarkerInverse,torusAffineMarkerVec] <;> ring

/-- Preserving or exchanging the two opposite centers removes translation. -/
theorem torusAffineMarker_translation_zero (L : Ambient ≃ₗᵢ[ℝ] Ambient) (b c d : Ambient)
    (hplus : torusAffineMarkerIsometry L b c = d) (hminus : torusAffineMarkerIsometry L b (-c) = -d) : b = 0 := by
  ext i
  have hi := congrArg (fun p : Ambient => p i) hplus
  have hj := congrArg (fun p : Ambient => p i) hminus
  simp [torusAffineMarkerIsometry] at hi hj
  change b i = 0
  linarith

/-- The explicit shifted centers force all three axis signs to agree. -/
theorem torusAffineMarker_diagonal_from_centers (L : Ambient ≃ₗᵢ[ℝ] Ambient) (h c : ℝ)
    (hh : h ≠ 0) (σ : Fin 3 → ℝ) (hσ : ∀ p i, L p i = σ i*p i)
    (hc : L (torusAffineMarkerCenter h) = c • torusAffineMarkerCenter h) : ∀ p, L p = c • p := by
  have hsign : ∀ i, σ i = c := by
    intro i
    have hi := congrArg (fun p : Ambient => p i) hc
    rw [hσ] at hi
    have hcval : torusAffineMarkerCenter h i = h := by fin_cases i <;> rfl
    simp only [PiLp.smul_apply,smul_eq_mul,hcval] at hi
    exact mul_right_cancel₀ hh hi
  intro p
  ext i
  simpa only [PiLp.smul_apply,smul_eq_mul,hsign] using hσ p i


end
end TightVer401

