import TightVer401.VisibleConnectorDisplacedSeamPhaseSigns

/-! Actual height smallness for the SAME native displaced inverse.
This leaf uses neither a Cartesian inverse nor a Gin/raw matching assumption.
Its positive margins may be intersected only after eta and its ruling are fixed.
-/
namespace TightVer401
noncomputable section
open Set Function Filter Metric OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- Compactness gives arbitrarily small displaced heights on the whole real
period, retaining the supplied native inverse literally. -/
theorem visibleConnectorIncomingParameters_uniform_height_small
    {L : ℝ} [hL : Fact (0 < L)] {p : ℝ → Coord}
    (e : OpenPartialHomeomorph (ℝ × (AddCircle L × ℝ)) (ℝ × Coord))
    (hD : IsOpen (visibleConnectorDisplacedRealPhaseDomain e p))
    (hb : ContDiffOn ℝ ∞
      (fun z => (visibleConnectorDisplacedNativeSolution e p z).2)
      (visibleConnectorDisplacedRealPhaseDomain e p))
    (haxis : ∀ s, (0, s) ∈ visibleConnectorDisplacedRealPhaseDomain e p)
    (hb0 : ∀ s, (visibleConnectorDisplacedNativeSolution e p (0, s)).2 = 0)
    (hbL : ∀ rho, Periodic
      (fun s => (visibleConnectorDisplacedNativeSolution e p (rho, s)).2) L)
    {r : ℝ} (hr : 0 < r) :
    ∃ delta > 0, ∀ rho s, |rho| < delta →
      |(visibleConnectorDisplacedNativeSolution e p (rho, s)).2| < r := by
  let D := visibleConnectorDisplacedRealPhaseDomain e p
  let b := fun z : ℝ × ℝ => (visibleConnectorDisplacedNativeSolution e p z).2
  let V := D ∩ (fun z => |b z|) ⁻¹' Iio r
  have hV : IsOpen V :=
    hb.continuousOn.abs.isOpen_inter_preimage hD isOpen_Iio
  let K : Set (ℝ × ℝ) := ({0} : Set ℝ) ×ˢ Icc 0 L
  have hK : IsCompact K := isCompact_singleton.prod isCompact_Icc
  have hKV : K ⊆ V := by
    intro z hz
    have he : z = (0, z.2) := Prod.ext (mem_singleton_iff.mp hz.1) rfl
    rw [he]
    refine ⟨haxis z.2, ?_⟩
    change |(visibleConnectorDisplacedNativeSolution e p (0, z.2)).2| < r
    rw [hb0]
    simpa using hr
  obtain ⟨c, hc, hcV⟩ := hK.exists_cthickening_subset_open hV hKV
  refine ⟨c / 2, half_pos hc, ?_⟩
  intro rho s hρ
  let x := AddCircle.equivIco L 0 (periodProjection L s)
  have hx : (x : ℝ) ∈ Icc 0 L := Ico_subset_Icc_self (by
    simpa only [zero_add] using x.property)
  have hxq : periodProjection L (x : ℝ) = periodProjection L s := AddCircle.coe_equivIco
  have hzV : (rho, (x : ℝ)) ∈ V := by
    apply hcV
    apply Metric.thickening_subset_cthickening c K
    apply Metric.mem_thickening_iff.mpr
    refine ⟨(0, (x : ℝ)), ⟨mem_singleton _, hx⟩, ?_⟩
    rw [Prod.dist_eq, dist_self]
    simp only [Real.dist_eq, sub_zero]
    exact max_lt (hρ.trans (half_lt_self hc)) hc
  have heq := congrArg (hbL rho).lift hxq
  rw [periodicLift_coe, periodicLift_coe] at heq
  have hsmallX : |(visibleConnectorDisplacedNativeSolution e p (rho, (x : ℝ))).2| < r := hzV.2
  rw [heq] at hsmallX
  exact hsmallX

end
end TightVer401


