import TightVer401.AnnularDegreeAngularForm
import TightVer401.AnnularDegreeLifts
import TightVer401.AnnularDegreeFormula
import Mathlib.Algebra.Order.Floor.Ring

/-!
Applicable integer annular degree from actual boundary angular integrals.
The integrals are proved integer-valued by the actual covering lifts before
the degree is identified with the actual Jacobian preimage count. The degree
is not defined by a preimage count and no degree identity is an input.
-/
namespace TightVer401
noncomputable section
open Set Function Filter
open OAI.CircleDomainRigidity OAI.CircleDomainRigidity.FiniteTransfer
open scoped ContDiff Topology

/-- Smoothness and target avoidance construct an actual smooth argument lift
along any smooth source path; a lift is not supplied as an input. -/
theorem annularAngularForm_exists_smooth_lift
    {F : ℂ → ℂ} {y : ℂ} {O : Set ℂ}
    (hO : IsOpen O) (hF : ContDiffOn ℝ ∞ F O)
    (hAvoid : ∀ z ∈ O, F z ≠ y)
    {γ : ℝ → ℂ} (hγ : ContDiff ℝ ∞ γ) (hγO : ∀ t, γ t ∈ O) :
    ∃ v : ℝ → ℝ, ContDiff ℝ ∞ v ∧
      (∀ t, (v t : UnitAddCircle) = normalizedArgument (F (γ t) - y)) ∧
      planarFormIntegral (annularAngularFormP F y) (annularAngularFormQ F y) γ =
        v 1 - v 0 := by
  obtain ⟨v, hv, hproj⟩ := annular_exists_smooth_real_circuit_lift hO
    (annularArgumentPullback_smoothCircleOn hO hF hAvoid) hγ hγO
  exact ⟨v, hv, hproj,
    annularAngularForm_integral_eq_lift hO hF hAvoid hγ hγO v hv.continuous hproj⟩

/-- The actual angular integral of a closed source loop is an integer,
without any supplied lift or image-boundary differential condition. -/
theorem annularAngularForm_loop_integral_exists_integer
    {F : ℂ → ℂ} {y : ℂ} {O : Set ℂ}
    (hO : IsOpen O) (hF : ContDiffOn ℝ ∞ F O)
    (hAvoid : ∀ z ∈ O, F z ≠ y)
    {γ : ℝ → ℂ} (hγ : ContDiff ℝ ∞ γ) (hγO : ∀ t, γ t ∈ O)
    (hClosed : γ 1 = γ 0) :
    ∃ k : ℤ,
      planarFormIntegral (annularAngularFormP F y) (annularAngularFormQ F y) γ = (k : ℝ) := by
  obtain ⟨v, hv, hproj, _⟩ := annularAngularForm_exists_smooth_lift hO hF hAvoid hγ hγO
  exact annularAngularForm_loop_integral_integer hO hF hAvoid hγ hγO hClosed v hv.continuous hproj

/-- Degree measured in actual boundary winding turns. On the applicable
avoiding domain the boundary sum is an integer, so floor loses no information. -/
def annularBoundaryDegree (F : ℂ → ℂ) (γouter γinner : ℝ → ℂ) (y : ℂ) : ℤ :=
  Int.floor (planarFormIntegral (annularAngularFormP F y) (annularAngularFormQ F y) γouter -
    planarFormIntegral (annularAngularFormP F y) (annularAngularFormQ F y) γinner)

/-- Justification of the integer degree by actual boundary lifts. -/
theorem annularBoundaryDegree_cast
    {F : ℂ → ℂ} {y : ℂ} {O : Set ℂ}
    (hO : IsOpen O) (hF : ContDiffOn ℝ ∞ F O)
    (hAvoid : ∀ z ∈ O, F z ≠ y)
    {γouter γinner : ℝ → ℂ}
    (houter : ContDiff ℝ ∞ γouter) (hinner : ContDiff ℝ ∞ γinner)
    (houterO : ∀ t, γouter t ∈ O) (hinnerO : ∀ t, γinner t ∈ O)
    (hClosedOuter : γouter 1 = γouter 0) (hClosedInner : γinner 1 = γinner 0) :
    (annularBoundaryDegree F γouter γinner y : ℝ) =
      planarFormIntegral (annularAngularFormP F y) (annularAngularFormQ F y) γouter -
        planarFormIntegral (annularAngularFormP F y) (annularAngularFormQ F y) γinner := by
  obtain ⟨ko, hko⟩ := annularAngularForm_loop_integral_exists_integer
    hO hF hAvoid houter houterO hClosedOuter
  obtain ⟨ki, hki⟩ := annularAngularForm_loop_integral_exists_integer
    hO hF hAvoid hinner hinnerO hClosedInner
  have hsum : planarFormIntegral (annularAngularFormP F y) (annularAngularFormQ F y) γouter -
      planarFormIntegral (annularAngularFormP F y) (annularAngularFormQ F y) γinner =
      ((ko - ki : ℤ) : ℝ) := by
    rw [hko, hki, Int.cast_sub]
  rw [annularBoundaryDegree, hsum, Int.floor_intCast]

/-- Every continuous actual argument lift has the same increment, because
all increments equal the actual pulled-back boundary integral. -/
theorem annularAngularForm_lift_increment_independent
    {F : ℂ → ℂ} {y : ℂ} {O : Set ℂ}
    (hO : IsOpen O) (hF : ContDiffOn ℝ ∞ F O)
    (hAvoid : ∀ z ∈ O, F z ≠ y)
    {γ : ℝ → ℂ} (hγ : ContDiff ℝ ∞ γ) (hγO : ∀ t, γ t ∈ O)
    (v w : ℝ → ℝ) (hv : Continuous v) (hw : Continuous w)
    (hprojv : ∀ t, (v t : UnitAddCircle) = normalizedArgument (F (γ t) - y))
    (hprojw : ∀ t, (w t : UnitAddCircle) = normalizedArgument (F (γ t) - y)) :
    v 1 - v 0 = w 1 - w 0 :=
  (annularAngularForm_integral_eq_lift hO hF hAvoid hγ hγO v hv hprojv).symm.trans
    (annularAngularForm_integral_eq_lift hO hF hAvoid hγ hγO w hw hprojw)

/-- Application on the actual source annulus: off its boundary images the
open avoiding domain is constructed from actual continuity of the map. -/
theorem annularBoundaryDegree_cast_off_jordan_boundary
    {Houter Hinner : ℂ ≃ₜ ℂ} {γouter γinner : ℝ → ℂ}
    (houter : RegularJordanParametrization Houter γouter)
    (hinner : RegularJordanParametrization Hinner γinner)
    (hnested : closure (jordanInterior Hinner) ⊆ jordanInterior Houter)
    (F : ℂ → ℂ) (O : Set ℂ) (hO : IsOpen O) (hF : ContDiffOn ℝ ∞ F O)
    (hKO : annularJordanClosure Houter Hinner ⊆ O) (y : ℂ)
    (hy : y ∉ F '' (frontier (jordanInterior Houter) ∪ frontier (jordanInterior Hinner))) :
    (annularBoundaryDegree F γouter γinner y : ℝ) =
      planarFormIntegral (annularAngularFormP F y) (annularAngularFormQ F y) γouter -
        planarFormIntegral (annularAngularFormP F y) (annularAngularFormQ F y) γinner := by
  let A : Set ℂ := O ∩ {z | F z ≠ y}
  have hA : IsOpen A := hF.continuousOn.isOpen_inter_preimage hO isClosed_singleton.isOpen_compl
  have hFA : ContDiffOn ℝ ∞ F A := hF.mono inter_subset_left
  have hAvoid : ∀ z ∈ A, F z ≠ y := fun _ hz => hz.2
  have houterA : ∀ t, γouter t ∈ A := by
    intro t
    have ht := houter.mem_frontier t
    have ht' := ht
    rw [(jordanInterior_isOpen Houter).frontier_eq] at ht'
    refine ⟨hKO ⟨ht'.1, fun hi => ht'.2 (hnested (subset_closure hi))⟩, ?_⟩
    intro heq
    exact hy ⟨γouter t, Or.inl ht, heq⟩
  have hinnerA : ∀ t, γinner t ∈ A := by
    intro t
    have ht := hinner.mem_frontier t
    have ht' := ht
    rw [(jordanInterior_isOpen Hinner).frontier_eq] at ht'
    refine ⟨hKO ⟨subset_closure (hnested ht'.1), ht'.2⟩, ?_⟩
    intro heq
    exact hy ⟨γinner t, Or.inr ht, heq⟩
  exact annularBoundaryDegree_cast hA hFA hAvoid houter.smooth hinner.smooth houterA hinnerA
    (by simpa using houter.periodic 0) (by simpa using hinner.periodic 0)

/-- The integer boundary-defined degree counts actual interior preimages
with the actual Jacobian sign. The counting identity is derived from Green
excision and the local inverse charts, never assumed. -/
theorem annularBoundaryDegree_eq_actual_sign_mul_ncard
    {Houter Hinner : ℂ ≃ₜ ℂ} {γouter γinner : ℝ → ℂ}
    (houter : RegularJordanParametrization Houter γouter)
    (hinner : RegularJordanParametrization Hinner γinner)
    (hnested : closure (jordanInterior Hinner) ⊆ jordanInterior Houter)
    (hpositiveOuter : circleFormIntegral (fun _ => 1) (centeredArgument (Houter 0)) γouter = 1)
    (hpositiveInner : circleFormIntegral (fun _ => 1) (centeredArgument (Hinner 0)) γinner = 1)
    (F : ℂ → ℂ) (O : Set ℂ) (hO : IsOpen O) (hF : ContDiffOn ℝ ∞ F O)
    (hKO : annularJordanClosure Houter Hinner ⊆ O)
    (s : ℤ) (hs : s = 1 ∨ s = -1)
    (hJ : ∀ z ∈ annularJordanInterior Houter Hinner, 0 < (s : ℝ) * (fderiv ℝ F z).det)
    (y : ℂ)
    (hy : y ∉ F '' (frontier (jordanInterior Houter) ∪ frontier (jordanInterior Hinner))) :
    annularBoundaryDegree F γouter γinner y =
      s * ({x | x ∈ annularJordanClosure Houter Hinner ∧ F x = y}.ncard : ℤ) := by
  have hsReal : |(s : ℝ)| = 1 := by
    rcases hs with rfl | rfl <;> norm_num
  have hcount := annular_complex_positive_boundary_preimage_formula
    houter hinner hnested hpositiveOuter hpositiveInner F O hO hF hKO (s : ℝ) hsReal hJ y hy
  have hdegree := annularBoundaryDegree_cast_off_jordan_boundary
    houter hinner hnested F O hO hF hKO y hy
  apply Int.cast_injective (α := ℝ)
  simpa only [Int.cast_mul, Int.cast_natCast] using hdegree.trans hcount

end
end TightVer401
