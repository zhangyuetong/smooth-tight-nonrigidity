import TightVer401.CompletedSaddleTorusBendingConnection

/-! Literal ver503 sign transport on the already retained completed-saddle
band chart. These identities consume the same output Q and field Y as the
compact nonzero bending application; they construct no new geometry. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry

variable {T w RN μ h : ℝ} [Fact (0 < T)]
variable {d : PeriodicRuledFrame T} {K : Set (AddCircle T × Ioo (0 : ℝ) w)}
variable (Q : CompletedSaddleAnnulusGeometryOutput d K RN μ h)

/-- The fixed normalization acts on vectors by negation; its translation
acts only on the immersion. -/
@[simp] theorem completedSaddleTorusBandAffine_linear_apply (x : Ambient) :
    (completedSaddleTorusBandAffine Q).linearIsometryEquiv x = -x := by
  have hlinear :
      (completedSaddleTorusBandAffine Q).linearIsometryEquiv x +
          Q.verticalOffset • revolutionAxis =
        -x + Q.verticalOffset • revolutionAxis := by
    simpa only [vadd_eq_add, add_zero, completedSaddleTorusBandAffine_apply,
      neg_zero, zero_add] using
      ((completedSaddleTorusBandAffine Q).map_vadd (0 : Ambient) x).symm
  exact add_right_cancel hlinear

/-- Under the SAME retained source identification the transported field is
literally minus the original field, as required by ver503 protected realization. -/
theorem completedSaddleTorusBendingField_source_eq_neg
    (Y : AddCircle T × Ioo (0 : ℝ) w → Ambient)
    {p : AddCircle T × Ioo (0 : ℝ) w}
    (hp : p ∈ (completedSaddleTorusBandChart Q).source) :
    protectedTorusBendingField (completedSaddleTorusBandChart Q)
        (completedSaddleTorusBandAffine Q) Y (completedSaddleTorusBandChart Q p) =
      -Y p := by
  rw [protectedTorusBendingField_source _ _ _ hp,
    completedSaddleTorusBandAffine_linear_apply]

end
end TightVer401
