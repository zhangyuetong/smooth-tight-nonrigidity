import TightVer401.AnnularDegreeLocal

/-! Signed counts of actual regular fibers. The sum here is deliberately named
a preimage count: identifying it with boundary winding is a separate obligation.
-/
namespace TightVer401
noncomputable section
open Set Function OAI.SmoothLocal.Geometry
open scoped ContDiff Topology BigOperators

/-- Integer orientation sign of the actual derivative. -/
def annularJacobianSign (F : Coord → Coord) (x : Coord) : ℤ :=
  if annularJacobian F x < 0 then -1 else
    if 0 < annularJacobian F x then 1 else 0

/-- Sum of actual Jacobian signs at all actual preimages in the source.
Use only with a proved finite fiber; `finsum` alone does not certify finiteness. -/
def annularSignedPreimageCount (F : Coord → Coord) (K : Set Coord) (y : Coord) : ℤ :=
  ∑ᶠ x : annularFiber F K y, annularJacobianSign F x

theorem annularJacobianSign_eq {F : Coord → Coord} {x : Coord} {s : ℤ}
    (hs : s = 1 ∨ s = -1) (hJ : 0 < (s : ℝ) * annularJacobian F x) :
    annularJacobianSign F x = s := by
  rcases hs with rfl | rfl
  · have hp : 0 < annularJacobian F x := by simpa using hJ
    simp [annularJacobianSign, hp, not_lt_of_ge hp.le]
  · have hn : annularJacobian F x < 0 := by
      norm_num at hJ
      linarith
    simp [annularJacobianSign, hn]

theorem annularJacobian_ne_zero_of_sign {F : Coord → Coord} {x : Coord} {s : ℤ}
    (hJ : 0 < (s : ℝ) * annularJacobian F x) : annularJacobian F x ≠ 0 := by
  intro hz
  simp [hz] at hJ

/-- Constant orientation makes the signed count the sign times the actual
number of preimages. This does not assume or prove a boundary degree formula. -/
theorem annularSignedPreimageCount_eq_sign_mul_ncard
    {F : Coord → Coord} {K : Set Coord} {y : Coord} {s : ℤ}
    (hfin : (annularFiber F K y).Finite) (hs : s = 1 ∨ s = -1)
    (hJ : ∀ x ∈ annularFiber F K y, 0 < (s : ℝ) * annularJacobian F x) :
    annularSignedPreimageCount F K y = s * (annularFiber F K y).ncard := by
  let := hfin.fintype
  have he : (fun x : annularFiber F K y => annularJacobianSign F x) =
      (fun _ : annularFiber F K y => s) := by
    funext x
    exact annularJacobianSign_eq hs (hJ x x.property)
  simp [annularSignedPreimageCount, he, finsum_eq_sum_of_fintype,
    mul_comm, ← Nat.card_eq_fintype_card]

theorem annularSignedPreimageCount_off_boundary
    {F : Coord → Coord} {K : Set Coord} {y : Coord} {s : ℤ}
    (hK : IsCompact K) (hF : ContinuousOn F K)
    (hFs : ContDiffOn ℝ ∞ F (interior K)) (hs : s = 1 ∨ s = -1)
    (hJ : ∀ x ∈ interior K, 0 < (s : ℝ) * annularJacobian F x)
    (hy : y ∉ F '' frontier K) :
    annularSignedPreimageCount F K y = s * (annularFiber F K y).ncard := by
  apply annularSignedPreimageCount_eq_sign_mul_ncard
    (annularFiber_finite hK hF hFs
      (fun x hx => annularJacobian_ne_zero_of_sign (hJ x hx)) hy) hs
  intro x hx
  exact hJ x (annularFiber_subset_interior hy hx)

/-- Absolute signed count removes the need to guess the boundary orientation
relative to the actual Jacobian sign. -/
theorem annularSignedPreimageCount_natAbs
    {F : Coord → Coord} {K : Set Coord} {y : Coord} {s : ℤ}
    (hfin : (annularFiber F K y).Finite) (hs : s = 1 ∨ s = -1)
    (hJ : ∀ x ∈ annularFiber F K y, 0 < (s : ℝ) * annularJacobian F x) :
    (annularSignedPreimageCount F K y).natAbs = (annularFiber F K y).ncard := by
  rw [annularSignedPreimageCount_eq_sign_mul_ncard hfin hs hJ]
  rcases hs with rfl | rfl <;> simp

/-- A zero signed count excludes every actual preimage when all signs agree. -/
theorem annularFiber_empty_of_signedCount_zero
    {F : Coord → Coord} {K : Set Coord} {y : Coord} {s : ℤ}
    (hfin : (annularFiber F K y).Finite) (hs : s = 1 ∨ s = -1)
    (hJ : ∀ x ∈ annularFiber F K y, 0 < (s : ℝ) * annularJacobian F x)
    (hc : annularSignedPreimageCount F K y = 0) : annularFiber F K y = ∅ := by
  rw [annularSignedPreimageCount_eq_sign_mul_ncard hfin hs hJ] at hc
  have hn : (annularFiber F K y).ncard = 0 := by
    rcases hs with rfl | rfl <;> simpa using hc
  exact (Set.ncard_eq_zero hfin).mp hn

/-- Count equal to the common sign gives exactly one actual preimage. -/
theorem annularFiber_unique_of_signedCount_eq_sign
    {F : Coord → Coord} {K : Set Coord} {y : Coord} {s : ℤ}
    (hfin : (annularFiber F K y).Finite) (hs : s = 1 ∨ s = -1)
    (hJ : ∀ x ∈ annularFiber F K y, 0 < (s : ℝ) * annularJacobian F x)
    (hc : annularSignedPreimageCount F K y = s) :
    ∃! x, x ∈ K ∧ F x = y := by
  rw [annularSignedPreimageCount_eq_sign_mul_ncard hfin hs hJ] at hc
  have hn : (annularFiber F K y).ncard = 1 := by
    rcases hs with rfl | rfl <;> norm_num at hc ⊢ <;> omega
  obtain ⟨x, hx⟩ := Set.ncard_eq_one.mp hn
  refine ⟨x, ?_, ?_⟩
  · have := hx.symm ▸ (mem_singleton x)
    exact this
  · intro z hz
    have hm : z ∈ annularFiber F K y := hz
    rw [hx] at hm
    exact hm

theorem annularFiber_unique_of_signedCount_natAbs_one
    {F : Coord → Coord} {K : Set Coord} {y : Coord} {s : ℤ}
    (hfin : (annularFiber F K y).Finite) (hs : s = 1 ∨ s = -1)
    (hJ : ∀ x ∈ annularFiber F K y, 0 < (s : ℝ) * annularJacobian F x)
    (hc : (annularSignedPreimageCount F K y).natAbs = 1) :
    ∃! x, x ∈ K ∧ F x = y := by
  have hn : (annularFiber F K y).ncard = 1 := by
    rw [← annularSignedPreimageCount_natAbs hfin hs hJ]
    exact hc
  obtain ⟨x, hx⟩ := Set.ncard_eq_one.mp hn
  refine ⟨x, ?_, ?_⟩
  · have hm : x ∈ annularFiber F K y := by
      rw [hx]
      exact mem_singleton x
    exact hm
  · intro z hz
    have hm : z ∈ annularFiber F K y := hz
    rw [hx] at hm
    exact hm

end
end TightVer401
