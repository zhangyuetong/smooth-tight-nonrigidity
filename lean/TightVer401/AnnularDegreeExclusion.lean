import TightVer401.AnnularDegreeCount

/-! The local-openness step in the annular degree criterion. The premise here
is an explicitly conditional signed-count calculation on a forbidden region;
it still has to be derived from boundary winding in the full theorem.
-/
namespace TightVer401
noncomputable section
open Set Function OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

/-- Once the signed count is zero on a region off the boundary image, even
its closure cannot be hit by an interior point. This is the boundary-rank-
independent step; it uses the actual interior derivative. -/
theorem annular_interior_avoids_closure_zero_count_region
    {F : Coord → Coord} {K E : Set Coord} {s : ℤ}
    (hK : IsCompact K) (hF : ContinuousOn F K)
    (hFs : ContDiffOn ℝ ∞ F (interior K)) (hs : s = 1 ∨ s = -1)
    (hJ : ∀ x ∈ interior K, 0 < (s : ℝ) * annularJacobian F x)
    (hE : ∀ y ∈ E, y ∉ F '' frontier K)
    (hzero : ∀ y ∈ E, annularSignedPreimageCount F K y = 0) :
    ∀ x ∈ interior K, F x ∉ closure E := by
  intro x hx hcl
  have hj : ∀ p ∈ interior K, annularJacobian F p ≠ 0 :=
    fun p hp => annularJacobian_ne_zero_of_sign (hJ p hp)
  obtain ⟨y, ⟨hyimage, hyE⟩⟩ :=
    (mem_closure_iff_nhds.mp hcl) _
      (annular_image_mem_nhds isOpen_interior hFs hj hx)
  have hempty := annularFiber_empty_of_signedCount_zero
    (annularFiber_finite hK hF hFs hj (hE y hyE)) hs
    (fun p hp => hJ p (annularFiber_subset_interior (hE y hyE) hp))
    (hzero y hyE)
  obtain ⟨p, hp, hpy⟩ := hyimage
  have hmem : p ∈ annularFiber F K y := ⟨interior_subset hp, hpy⟩
  rw [hempty] at hmem
  exact hmem

end
end TightVer401
