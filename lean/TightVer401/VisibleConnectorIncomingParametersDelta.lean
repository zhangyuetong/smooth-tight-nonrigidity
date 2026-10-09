import TightVer401.VisibleConnectorDisplacedSeamPhaseSigns

/-! Uniform lower old Jacobian along the SAME displaced phase and height.
The actual coefficient families are composed with a and b before compactness.
No phase-speed sign substitutes for old Delta positivity, and no Gin matching
or original construction package is assumed.
-/
namespace TightVer401
noncomputable section
open Set Function Filter Metric OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- Actual continuous old coefficients give one uniform rho margin on which
the old Delta at the SAME lower seam is positive. This is the expression
A(rho,a(rho,s))+b(rho,s)*(B(rho,a(rho,s))-C(rho,a(rho,s))). -/
theorem visibleConnectorIncomingParameters_uniform_lower_delta
    {L : ℝ} [hL : Fact (0 < L)] {p : ℝ → Coord}
    (e : OpenPartialHomeomorph (ℝ × (AddCircle L × ℝ)) (ℝ × Coord))
    {Omega D0 : Set (ℝ × ℝ)} {A B C : ℝ × ℝ → ℝ}
    (hD : IsOpen D0)
    (hDsub : D0 ⊆ visibleConnectorDisplacedRealPhaseDomain e p)
    (ha : ContDiffOn ℝ ∞ (visibleConnectorDisplacedRealPhase e p)
      (visibleConnectorDisplacedRealPhaseDomain e p))
    (hb : ContDiffOn ℝ ∞
      (fun z => (visibleConnectorDisplacedNativeSolution e p z).2)
      (visibleConnectorDisplacedRealPhaseDomain e p))
    (haxis : ∀ s, (0, s) ∈ D0)
    (ha0 : ∀ s, visibleConnectorDisplacedRealPhase e p (0, s) = s)
    (hb0 : ∀ s, (visibleConnectorDisplacedNativeSolution e p (0, s)).2 = 0)
    (hashift : ∀ rho s, visibleConnectorDisplacedRealPhase e p (rho, s + L) =
      visibleConnectorDisplacedRealPhase e p (rho, s) + L)
    (hbL : ∀ rho, Periodic
      (fun s => (visibleConnectorDisplacedNativeSolution e p (rho, s)).2) L)
    (hA : ContinuousOn A Omega) (hB : ContinuousOn B Omega) (hC : ContinuousOn C Omega)
    (hmap : MapsTo (fun z : ℝ × ℝ =>
      (z.1, visibleConnectorDisplacedRealPhase e p z))
      D0 Omega)
    (hAL : ∀ rho, Periodic (fun s => A (rho, s)) L)
    (hBL : ∀ rho, Periodic (fun s => B (rho, s)) L)
    (hCL : ∀ rho, Periodic (fun s => C (rho, s)) L)
    (hA0 : ∀ s, 0 < A (0, s)) :
    ∃ delta > 0, ∀ rho s, |rho| < delta →
      0 < A (rho, visibleConnectorDisplacedRealPhase e p (rho, s)) +
        (visibleConnectorDisplacedNativeSolution e p (rho, s)).2 *
          (B (rho, visibleConnectorDisplacedRealPhase e p (rho, s)) -
            C (rho, visibleConnectorDisplacedRealPhase e p (rho, s))) := by
  let D := D0
  let a := visibleConnectorDisplacedRealPhase e p
  let b := fun z : ℝ × ℝ => (visibleConnectorDisplacedNativeSolution e p z).2
  let f := fun z : ℝ × ℝ =>
    A (z.1, a z) + b z * (B (z.1, a z) - C (z.1, a z))
  have hc : ContinuousOn (fun z : ℝ × ℝ => (z.1, a z)) D :=
    continuous_fst.continuousOn.prodMk (ha.continuousOn.mono hDsub)
  have hf : ContinuousOn f D :=
    (hA.comp hc hmap).add ((hb.continuousOn.mono hDsub).mul ((hB.comp hc hmap).sub (hC.comp hc hmap)))
  let V := D ∩ f ⁻¹' Ioi 0
  have hV : IsOpen V := hf.isOpen_inter_preimage hD isOpen_Ioi
  let K : Set (ℝ × ℝ) := ({0} : Set ℝ) ×ˢ Icc 0 L
  have hK : IsCompact K := isCompact_singleton.prod isCompact_Icc
  have hKV : K ⊆ V := by
    intro z hz
    have he : z = (0, z.2) := Prod.ext (mem_singleton_iff.mp hz.1) rfl
    rw [he]
    refine ⟨haxis z.2, ?_⟩
    change 0 < A (0, visibleConnectorDisplacedRealPhase e p (0, z.2)) +
      (visibleConnectorDisplacedNativeSolution e p (0, z.2)).2 *
        (B (0, visibleConnectorDisplacedRealPhase e p (0, z.2)) -
          C (0, visibleConnectorDisplacedRealPhase e p (0, z.2)))
    simpa only [ha0, hb0, zero_mul, add_zero] using hA0 z.2
  have hfL (rho : ℝ) : Periodic (fun s => f (rho, s)) L := by
    intro s
    have hbPeriod : (visibleConnectorDisplacedNativeSolution e p (rho, s + L)).2 =
        (visibleConnectorDisplacedNativeSolution e p (rho, s)).2 := hbL rho s
    have hAPeriod : A (rho, visibleConnectorDisplacedRealPhase e p (rho, s) + L) =
        A (rho, visibleConnectorDisplacedRealPhase e p (rho, s)) :=
      hAL rho (visibleConnectorDisplacedRealPhase e p (rho, s))
    have hBPeriod : B (rho, visibleConnectorDisplacedRealPhase e p (rho, s) + L) =
        B (rho, visibleConnectorDisplacedRealPhase e p (rho, s)) :=
      hBL rho (visibleConnectorDisplacedRealPhase e p (rho, s))
    have hCPeriod : C (rho, visibleConnectorDisplacedRealPhase e p (rho, s) + L) =
        C (rho, visibleConnectorDisplacedRealPhase e p (rho, s)) :=
      hCL rho (visibleConnectorDisplacedRealPhase e p (rho, s))
    change A (rho, visibleConnectorDisplacedRealPhase e p (rho, s + L)) +
      (visibleConnectorDisplacedNativeSolution e p (rho, s + L)).2 *
        (B (rho, visibleConnectorDisplacedRealPhase e p (rho, s + L)) -
          C (rho, visibleConnectorDisplacedRealPhase e p (rho, s + L))) =
      A (rho, visibleConnectorDisplacedRealPhase e p (rho, s)) +
      (visibleConnectorDisplacedNativeSolution e p (rho, s)).2 *
        (B (rho, visibleConnectorDisplacedRealPhase e p (rho, s)) -
          C (rho, visibleConnectorDisplacedRealPhase e p (rho, s)))
    rw [hashift rho s, hbPeriod, hAPeriod, hBPeriod, hCPeriod]
  obtain ⟨c, hcpos, hcV⟩ := hK.exists_cthickening_subset_open hV hKV
  refine ⟨c / 2, half_pos hcpos, ?_⟩
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
    exact max_lt (hρ.trans (half_lt_self hcpos)) hcpos
  have heq := congrArg (hfL rho).lift hxq
  rw [periodicLift_coe, periodicLift_coe] at heq
  have hpositiveX : 0 < f (rho, (x : ℝ)) := hzV.2
  rw [heq] at hpositiveX
  exact hpositiveX

end
end TightVer401



