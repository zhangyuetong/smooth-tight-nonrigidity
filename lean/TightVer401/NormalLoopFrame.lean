import TightVer401.NormalLoopCross

/-! Construct the frame used by the normal-loop criterion directly from an
arclength parametrized spherical curve and its actual first two derivatives. -/
namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff

def normalLoopP (ζ E : ℝ → Ambient) (r : ℝ) : Ambient :=
  -ambientCross (ζ r) (E r)

def normalLoopKappa (ζ E A : ℝ → Ambient) (r : ℝ) : ℝ :=
  -inner ℝ (A r) (normalLoopP ζ E r)

theorem normalLoop_unit_tangent_orthogonal {ζ E : ℝ → Ambient}
    (hζ : ∀ r, HasDerivAt ζ (E r) r) (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (r : ℝ) : inner ℝ (ζ r) (E r) = 0 := by
  have hd := (hζ r).inner ℝ (hζ r)
  have heq : (fun t => inner ℝ (ζ t) (ζ t)) = fun _ => (1 : ℝ) := funext hunit
  rw [heq] at hd
  have he := hd.unique (hasDerivAt_const r (1 : ℝ))
  rw [real_inner_comm (ζ r) (E r)] at he
  linarith

theorem normalLoop_frame {ζ E : ℝ → Ambient}
    (hζ : ∀ r, HasDerivAt ζ (E r) r) (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (E r) (E r) = 1) (r : ℝ) :
    IsOrthonormalFrame (normalLoopP ζ E r) (E r) (ζ r) := by
  have hζE := normalLoop_unit_tangent_orthogonal hζ hunit r
  have hPP : inner ℝ (normalLoopP ζ E r) (normalLoopP ζ E r) = 1 := by
    rw [normalLoopP, inner_neg_left, inner_neg_right]
    rw [real_inner_self_eq_norm_sq, ambientCross_norm_sq, hunit r, hspeed r, hζE]
    norm_num
  refine ⟨hPP, hspeed r, hunit r, ?_, ?_, ?_⟩
  · rw [normalLoopP, inner_neg_left, real_inner_comm]
    simp [ambientCross_orthogonal_right]
  · rw [normalLoopP, inner_neg_left, real_inner_comm]
    simp [ambientCross_orthogonal_left]
  · rw [real_inner_comm, hζE]

theorem normalLoop_second_derivative {ζ E A : ℝ → Ambient}
    (hζ : ∀ r, HasDerivAt ζ (E r) r) (hE : ∀ r, HasDerivAt E (A r) r)
    (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (E r) (E r) = 1) (r : ℝ) :
    A r = -ζ r - normalLoopKappa ζ E A r • normalLoopP ζ E r := by
  have hEA := normalLoop_unit_tangent_orthogonal hE hspeed r
  have hζE : ∀ t, inner ℝ (ζ t) (E t) = 0 := normalLoop_unit_tangent_orthogonal hζ hunit
  have hd := (hζ r).inner ℝ (hE r)
  rw [show (fun t => inner ℝ (ζ t) (E t)) = fun _ => (0 : ℝ) from funext hζE] at hd
  have he := hd.unique (hasDerivAt_const r (0 : ℝ))
  rw [hspeed r] at he
  have hAζ : inner ℝ (A r) (ζ r) = -1 := by rw [real_inner_comm]; linarith
  have hAE : inner ℝ (A r) (E r) = 0 := by rw [real_inner_comm, hEA]
  have hdcomp := orthonormal_frame_decomposition (normalLoop_frame hζ hunit hspeed r) (A r)
  rw [hAζ, hAE] at hdcomp
  calc
    A r = (inner ℝ (A r) (normalLoopP ζ E r)) • normalLoopP ζ E r +
      0 • E r + (-1 : ℝ) • ζ r := hdcomp
    _ = -ζ r - normalLoopKappa ζ E A r • normalLoopP ζ E r := by
      dsimp [normalLoopKappa]
      module

theorem normalLoop_derivative_P {ζ E A : ℝ → Ambient}
    (hζ : ∀ r, HasDerivAt ζ (E r) r) (hE : ∀ r, HasDerivAt E (A r) r)
    (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (E r) (E r) = 1) (r : ℝ) :
    HasDerivAt (normalLoopP ζ E) (normalLoopKappa ζ E A r • E r) r := by
  have hζE := normalLoop_unit_tangent_orthogonal hζ hunit r
  have hζP : ambientCross (ζ r) (normalLoopP ζ E r) = E r := by
    rw [normalLoopP, normalLoopCross_neg_right, normalLoopCross_double, hζE, hunit r]
    simp
  have hd := (normalLoopCross_hasDerivAt (hζ r) (hE r)).neg
  change HasDerivAt (normalLoopP ζ E) _ r at hd
  rw [ambientCross_self, zero_add, normalLoop_second_derivative hζ hE hunit hspeed r,
    sub_eq_add_neg, normalLoopCross_add_right, normalLoopCross_neg_right,
    ambientCross_self, neg_zero, zero_add, normalLoopCross_neg_right,
    normalLoopCross_smul_right, hζP, neg_neg] at hd
  exact hd

theorem normalLoopP_contDiff {ζ E : ℝ → Ambient}
    (hζ : ContDiff ℝ ∞ ζ) (hE : ContDiff ℝ ∞ E) : ContDiff ℝ ∞ (normalLoopP ζ E) :=
  (ambientCross_contDiff hζ hE).neg

theorem normalLoopKappa_contDiff {ζ E A : ℝ → Ambient}
    (hζ : ContDiff ℝ ∞ ζ) (hE : ContDiff ℝ ∞ E) (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ ∞ (normalLoopKappa ζ E A) :=
  (hA.inner ℝ (normalLoopP_contDiff hζ hE)).neg

end
end TightVer401
