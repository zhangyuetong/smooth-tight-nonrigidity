import TightVer401.ProtectedTorusBendingExtension

/-! Literal same-object connection for a linear transformation of the protected
field. The existing extension definition is reused with identity placement and
transformed band data. No native strain, metric, curvature or marker construction
is introduced here. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry

variable {T w : ℝ} [Fact (0 < T)]

/-- Linear transformation commutes with the literal protected zero extension.
No support or smoothness hypothesis is needed for this pointwise identity. -/
theorem protectedTorusBendingField_linear_connection
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) NonrigidTorusSource)
    (A : Ambient ≃ᵃⁱ[ℝ] Ambient) (Y : AddCircle T × Ioo (0 : ℝ) w → Ambient)
    (C : Ambient →L[ℝ] Ambient) (q : NonrigidTorusSource) :
    protectedTorusBendingField e (AffineIsometryEquiv.refl ℝ Ambient)
        (fun p => C (A.linearIsometryEquiv (Y p))) q =
      C (protectedTorusBendingField e A Y q) := by
  by_cases hq : q ∈ e.target
  · rw [protectedTorusBendingField_of_mem e _ _ hq,
      protectedTorusBendingField_of_mem e A Y hq]
    rfl
  · rw [protectedTorusBendingField_of_notMem e _ _ hq,
      protectedTorusBendingField_of_notMem e A Y hq, map_zero]

/-- Function equality for reusing the existing literal protected-field
consumers with transformed band data. -/
theorem protectedTorusBendingField_linear_connection_fun
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) NonrigidTorusSource)
    (A : Ambient ≃ᵃⁱ[ℝ] Ambient) (Y : AddCircle T × Ioo (0 : ℝ) w → Ambient)
    (C : Ambient →L[ℝ] Ambient) :
    protectedTorusBendingField e (AffineIsometryEquiv.refl ℝ Ambient)
        (fun p => C (A.linearIsometryEquiv (Y p))) =
      fun q => C (protectedTorusBendingField e A Y q) := by
  funext q
  exact protectedTorusBendingField_linear_connection e A Y C q

/-- The transformed literal field evaluates to the same transformed band
field at every actual source point of the placement chart. -/
theorem protectedTorusBendingField_linear_connection_source
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) NonrigidTorusSource)
    (A : Ambient ≃ᵃⁱ[ℝ] Ambient) (Y : AddCircle T × Ioo (0 : ℝ) w → Ambient)
    (C : Ambient →L[ℝ] Ambient)
    {p : AddCircle T × Ioo (0 : ℝ) w} (hp : p ∈ e.source) :
    protectedTorusBendingField e (AffineIsometryEquiv.refl ℝ Ambient)
        (fun z => C (A.linearIsometryEquiv (Y z))) (e p) =
      C (A.linearIsometryEquiv (Y p)) := by
  rw [protectedTorusBendingField_linear_connection e A Y C,
    protectedTorusBendingField_source e A Y hp]

/-- The same actual source placement gives both literal transformed branch
values. B acts on the baseline and C on its field; they need not agree. -/
theorem protectedTorus_linear_branches_source
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) NonrigidTorusSource)
    (A : Ambient ≃ᵃⁱ[ℝ] Ambient)
    (X Y : AddCircle T × Ioo (0 : ℝ) w → Ambient)
    (F : NonrigidTorusSource → Ambient) (B C : Ambient →L[ℝ] Ambient)
    (hplacement : ∀ p ∈ e.source, F (e p) = A (X p))
    (ε : ℝ) {p : AddCircle T × Ioo (0 : ℝ) w} (hp : p ∈ e.source) :
    (B (F (e p)) + ε • protectedTorusBendingField e
        (AffineIsometryEquiv.refl ℝ Ambient)
        (fun z => C (A.linearIsometryEquiv (Y z))) (e p) =
      B (A (X p)) + ε • C (A.linearIsometryEquiv (Y p))) ∧
    (B (F (e p)) - ε • protectedTorusBendingField e
        (AffineIsometryEquiv.refl ℝ Ambient)
        (fun z => C (A.linearIsometryEquiv (Y z))) (e p) =
      B (A (X p)) - ε • C (A.linearIsometryEquiv (Y p))) := by
  constructor <;>
    rw [hplacement p hp, protectedTorusBendingField_linear_connection_source e A Y C hp]

end
end TightVer401

