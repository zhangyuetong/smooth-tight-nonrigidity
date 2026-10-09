import TightVer401.AnnularDegreeLocal

/-!
Assembly of the smooth inverse after the annular signed-preimage argument has
proved uniqueness. This is a conditional helper, not the annular degree
criterion: its uniqueness premise must be discharged by the degree proof.
No assumptions are made about boundary differentials.
-/
namespace TightVer401
noncomputable section
open Set Function Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

/-- A chosen actual preimage on the image, extended by zero elsewhere. -/
def annularImageInverse (F : Coord → Coord) (U : Set Coord) (y : Coord) : Coord := by
  classical
  exact if hy : y ∈ F '' U then Classical.choose hy else 0

theorem annularImageInverse_mem {F : Coord → Coord} {U : Set Coord} {y : Coord}
    (hy : y ∈ F '' U) : annularImageInverse F U y ∈ U := by
  simp only [annularImageInverse, dif_pos hy]
  exact (Classical.choose_spec hy).1

theorem annularImageInverse_right {F : Coord → Coord} {U : Set Coord} {y : Coord}
    (hy : y ∈ F '' U) : F (annularImageInverse F U y) = y := by
  simp only [annularImageInverse, dif_pos hy]
  exact (Classical.choose_spec hy).2

/-- Unique actual interior fibers imply injectivity on the open source. -/
theorem annular_injOn_of_unique_preimages {F : Coord → Coord} {U : Set Coord}
    (hUnique : ∀ y ∈ F '' U, ∃! x, x ∈ U ∧ F x = y) : InjOn F U := by
  intro x hx z hz hxz
  obtain ⟨p, _, hp⟩ := hUnique (F x) (mem_image_of_mem F hx)
  exact (hp x ⟨hx, rfl⟩).trans (hp z ⟨hz, hxz.symm⟩).symm

theorem annularImageInverse_left {F : Coord → Coord} {U : Set Coord}
    (hUnique : ∀ y ∈ F '' U, ∃! x, x ∈ U ∧ F x = y)
    {x : Coord} (hx : x ∈ U) : annularImageInverse F U (F x) = x :=
  annular_injOn_of_unique_preimages hUnique
    (annularImageInverse_mem (mem_image_of_mem F hx)) hx
    (annularImageInverse_right (mem_image_of_mem F hx))

/-- Openness of the actual image follows from the actual nonzero Jacobian. -/
theorem annular_image_isOpen {F : Coord → Coord} {U : Set Coord}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (hJ : ∀ x ∈ U, annularJacobian F x ≠ 0) : IsOpen (F '' U) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro y ⟨x, hx, rfl⟩
  exact annular_image_mem_nhds hU hF hJ hx

/-- The chosen inverse agrees locally with the inverses supplied by the actual
Frechet derivative; uniqueness is used only to identify those local inverses. -/
theorem annularImageInverse_contDiffOn {F : Coord → Coord} {U : Set Coord}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (hJ : ∀ x ∈ U, annularJacobian F x ≠ 0)
    (hUnique : ∀ y ∈ F '' U, ∃! x, x ∈ U ∧ F x = y) :
    ContDiffOn ℝ ∞ (annularImageInverse F U) (F '' U) := by
  intro y hy
  let x := annularImageInverse F U y
  have hx : x ∈ U := annularImageInverse_mem hy
  have hFy : F x = y := annularImageInverse_right hy
  obtain ⟨e, hex, heU, heF, he⟩ := annular_exists_smooth_local_inverse hU hF hJ hx
  have hyT : y ∈ e.target := by
    rw [← hFy, ← heF]
    exact e.map_source hex
  have heq : annularImageInverse F U =ᶠ[𝓝 y] e.symm := by
    filter_upwards [e.open_target.mem_nhds hyT] with z hz
    have hxz := e.map_target hz
    have hFz : F (e.symm z) = z := by
      rw [← heF]
      exact e.right_inv hz
    have hzU : z ∈ F '' U := ⟨e.symm z, heU hxz, hFz⟩
    exact annular_injOn_of_unique_preimages hUnique
      (annularImageInverse_mem hzU) (heU hxz)
      ((annularImageInverse_right hzU).trans hFz.symm)
  exact ((he.contDiffAt (e.open_target.mem_nhds hyT)).congr_of_eventuallyEq heq).contDiffWithinAt

/-- The actual map, with the inverse assembled from unique fibers. Its source
is exactly the given open source and its target is the actual image. -/
def annularImageHomeomorph {F : Coord → Coord} {U : Set Coord}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (hJ : ∀ x ∈ U, annularJacobian F x ≠ 0)
    (hUnique : ∀ y ∈ F '' U, ∃! x, x ∈ U ∧ F x = y) :
    OpenPartialHomeomorph Coord Coord where
  toFun := F
  invFun := annularImageInverse F U
  source := U
  target := F '' U
  map_source' := fun _ hx => mem_image_of_mem F hx
  map_target' := fun _ hy => annularImageInverse_mem hy
  left_inv' := fun _ hx => annularImageInverse_left hUnique hx
  right_inv' := fun _ hy => annularImageInverse_right hy
  continuousOn_toFun := hF.continuousOn
  continuousOn_invFun := (annularImageInverse_contDiffOn hU hF hJ hUnique).continuousOn
  open_source := hU
  open_target := annular_image_isOpen hU hF hJ

@[simp] theorem annularImageHomeomorph_source {F : Coord → Coord} {U : Set Coord}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (hJ : ∀ x ∈ U, annularJacobian F x ≠ 0)
    (hUnique : ∀ y ∈ F '' U, ∃! x, x ∈ U ∧ F x = y) :
    (annularImageHomeomorph hU hF hJ hUnique).source = U := rfl

@[simp] theorem annularImageHomeomorph_target {F : Coord → Coord} {U : Set Coord}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (hJ : ∀ x ∈ U, annularJacobian F x ≠ 0)
    (hUnique : ∀ y ∈ F '' U, ∃! x, x ∈ U ∧ F x = y) :
    (annularImageHomeomorph hU hF hJ hUnique).target = F '' U := rfl

@[simp] theorem annularImageHomeomorph_coe {F : Coord → Coord} {U : Set Coord}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (hJ : ∀ x ∈ U, annularJacobian F x ≠ 0)
    (hUnique : ∀ y ∈ F '' U, ∃! x, x ∈ U ∧ F x = y) :
    (annularImageHomeomorph hU hF hJ hUnique : Coord → Coord) = F := rfl

theorem annular_exists_smooth_image_inverse {F : Coord → Coord} {U : Set Coord}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (hJ : ∀ x ∈ U, annularJacobian F x ≠ 0)
    (hUnique : ∀ y ∈ F '' U, ∃! x, x ∈ U ∧ F x = y) :
    ∃ e : OpenPartialHomeomorph Coord Coord,
      e.source = U ∧ e.target = F '' U ∧ (e : Coord → Coord) = F ∧
      ContDiffOn ℝ ∞ e.symm e.target := by
  exact ⟨annularImageHomeomorph hU hF hJ hUnique, rfl, rfl, rfl,
    annularImageInverse_contDiffOn hU hF hJ hUnique⟩

/-- The derivative of the assembled inverse is the inverse of the actual
Frechet derivative, represented as a continuous linear equivalence. -/
theorem annularImageInverse_hasFDerivAt {F : Coord → Coord} {U : Set Coord}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (hJ : ∀ x ∈ U, annularJacobian F x ≠ 0)
    (hUnique : ∀ y ∈ F '' U, ∃! x, x ∈ U ∧ F x = y)
    {y : Coord} (hy : y ∈ F '' U) :
    HasFDerivAt (annularImageInverse F U)
      ((regularCoordinateEquiv F (annularImageInverse F U y)
        (annularJacobian_differential_injective
          (hJ _ (annularImageInverse_mem hy)))).symm : Coord →L[ℝ] Coord) y := by
  let e := annularImageHomeomorph hU hF hJ hUnique
  have hp := annularImageInverse_mem hy
  have hd := regularCoordinateEquiv_hasFDerivAt
    ((hF.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp))
    (annularJacobian_differential_injective (hJ _ hp))
  exact e.hasFDerivAt_symm hy hd

end
end TightVer401
