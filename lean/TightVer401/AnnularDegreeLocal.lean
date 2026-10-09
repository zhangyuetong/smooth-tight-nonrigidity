import TightVer401.RegularLocalInverse
import Mathlib.Topology.IsLocalHomeomorph

/-!
Actual derivative and compact-fiber prerequisites for ver500's annular degree
criterion. No boundary differential condition is imposed. These prerequisites
do not assert the boundary-winding/signed-preimage identity.
-/
namespace TightVer401
noncomputable section
open Set Function OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

/-- The actual Frechet derivative determinant, independent of a chosen basis. -/
def annularJacobian (F : Coord → Coord) (x : Coord) : ℝ :=
  (fderiv ℝ F x).toLinearMap.det

/-- Preimages in the actual closed source, rather than a supplied fiber list. -/
def annularFiber (F : Coord → Coord) (K : Set Coord) (y : Coord) : Set Coord :=
  {x | x ∈ K ∧ F x = y}

theorem annularJacobian_differential_injective {F : Coord → Coord} {x : Coord}
    (hJ : annularJacobian F x ≠ 0) : Injective (fderiv ℝ F x) := by
  apply LinearMap.ker_eq_bot.mp
  by_contra hker
  exact hJ (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hker)

theorem annular_exists_smooth_local_inverse {F : Coord → Coord} {U : Set Coord}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (hJ : ∀ x ∈ U, annularJacobian F x ≠ 0) {x : Coord} (hx : x ∈ U) :
    ∃ e : OpenPartialHomeomorph Coord Coord,
      x ∈ e.source ∧ e.source ⊆ U ∧ (e : Coord → Coord) = F ∧
      ContDiffOn ℝ ∞ e.symm e.target :=
  exists_smooth_local_inverse hU hF
    (fun p hp => annularJacobian_differential_injective (hJ p hp)) hx

theorem annular_isLocalHomeomorphOn {F : Coord → Coord} {U : Set Coord}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (hJ : ∀ x ∈ U, annularJacobian F x ≠ 0) : IsLocalHomeomorphOn F U := by
  intro x hx
  obtain ⟨e, he, -, heF, -⟩ := annular_exists_smooth_local_inverse hU hF hJ hx
  exact ⟨e, he, heF.symm⟩

/-- Local openness is obtained from the actual derivative even at a possible
interior preimage of a target boundary point. -/
theorem annular_image_mem_nhds {F : Coord → Coord} {U : Set Coord}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (hJ : ∀ x ∈ U, annularJacobian F x ≠ 0) {x : Coord} (hx : x ∈ U) :
    F '' U ∈ nhds (F x) := by
  obtain ⟨e, he, heU, heF, -⟩ := annular_exists_smooth_local_inverse hU hF hJ hx
  apply Filter.mem_of_superset (e.open_target.mem_nhds (heF ▸ e.map_source he))
  intro y hy
  refine ⟨e.symm y, heU (e.map_target hy), ?_⟩
  rw [← heF]
  exact e.right_inv hy

theorem annularFiber_subset_interior {F : Coord → Coord} {K : Set Coord} {y : Coord}
    (hy : y ∉ F '' frontier K) : annularFiber F K y ⊆ interior K := by
  intro x hx
  by_contra hi
  apply hy
  exact ⟨x, ⟨subset_closure hx.1, hi⟩, hx.2⟩

theorem annularFiber_isCompact {F : Coord → Coord} {K : Set Coord} {y : Coord}
    (hK : IsCompact K) (hF : ContinuousOn F K) : IsCompact (annularFiber F K y) := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hc : IsClosed ((K.domRestrict F) ⁻¹' {y}) :=
    isClosed_singleton.preimage hF.domRestrict
  have hi : IsCompact ((K.domRestrict F) ⁻¹' {y}) :=
    hc.isCompact
  convert hi.image continuous_subtype_val using 1
  ext x
  simp [annularFiber, and_comm]

/-- Compactness and local inversion give finite fibers off the boundary image.
No global injectivity or prescribed image is assumed. -/
theorem annularFiber_finite {F : Coord → Coord} {K : Set Coord} {y : Coord}
    (hK : IsCompact K) (hF : ContinuousOn F K)
    (hFs : ContDiffOn ℝ ∞ F (interior K))
    (hJ : ∀ x ∈ interior K, annularJacobian F x ≠ 0)
    (hy : y ∉ F '' frontier K) : (annularFiber F K y).Finite := by
  have hl := (annular_isLocalHomeomorphOn isOpen_interior hFs hJ).mono
    (annularFiber_subset_interior hy)
  have hd : IsDiscrete (F '' annularFiber F K y) :=
    ((finite_singleton y).subset (by
      rintro z ⟨x, hx, rfl⟩
      exact hx.2)).isDiscrete
  exact (annularFiber_isCompact hK hF).finite (hl.isDiscrete_of_image hd)

end
end TightVer401
