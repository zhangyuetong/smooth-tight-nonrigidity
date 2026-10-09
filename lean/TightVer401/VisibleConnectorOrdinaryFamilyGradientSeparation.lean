import TightVer401.VisibleConnectorWitnessAssemblyCircle
import TightVer401.VisibleConnectorWitnessAssemblyTopology

/-! Actual universal incoming-gradient separation. Visibility is ordinary input;
no terminal inverse, target nesting, or final scalar construction is assumed. -/
namespace TightVer401
noncomputable section
open Set Function Filter Metric OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

/-- Visibility places the SAME incoming gradient strictly outside radius R. -/
theorem visibleConnectorOrdinaryFamily_incoming_gradient_radius
    {Gin : Coord → ℝ} {Uin : Set Coord} {L R : ℝ} [Fact (0 < L)]
    (D : VisibleConnectorIncomingData Gin Uin L R) (s : ℝ) :
    R < planarRadius (D.incoming.gamma s) := by
  have h := (D.visibility s).1
  rw [D.actual_delta] at h
  simp only [norm_mul, Complex.norm_I, one_mul] at h
  change R < ‖positiveExitComplexPoint (D.incoming.gamma s)‖ at h
  rw [
    visibleConnectorWitnessAssemblyTopology_complex_point,
    ← quadraticRadialFillingRadius_complex,
    seamComplexCoord.apply_symm_apply] at h
  exact h

/-- The physical-period compactness strengthens pointwise visibility to ONE
strict positive margin, independently of eta and of the later final H. -/
theorem visibleConnectorOrdinaryFamily_incoming_gradient_uniform_margin
    {Gin : Coord → ℝ} {Uin : Set Coord} {L R : ℝ} [Fact (0 < L)]
    (D : VisibleConnectorIncomingData Gin Uin L R) :
    ∃ eps > 0, ∀ s, R + eps ≤ planarRadius (D.incoming.gamma s) := by
  have hL : 0 < L := Fact.out
  have hc : Continuous (fun s => planarRadius (D.incoming.gamma s)) := by
    have he : (fun s => planarRadius (D.incoming.gamma s)) =
        fun s => ‖seamComplexCoord.symm (D.incoming.gamma s)‖ := by
      funext s
      rw [← quadraticRadialFillingRadius_complex, seamComplexCoord.apply_symm_apply]
    rw [he]
    exact (seamComplexCoord.symm.continuous.comp D.incoming.gamma_smooth.continuous).norm
  obtain ⟨s0, hs0, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr hL.le) hc.continuousOn
  refine ⟨planarRadius (D.incoming.gamma s0) - R,
    sub_pos.mpr (visibleConnectorOrdinaryFamily_incoming_gradient_radius D s0), ?_⟩
  intro s
  have hp : D.incoming.gamma s = D.incoming.gamma (toIcoMod hL 0 s) := by
    conv_lhs => rw [← toIcoMod_add_toIcoDiv_zsmul hL 0 s]
    exact D.incoming.gamma_periodic.zsmul (toIcoDiv hL 0 s) _
  rw [hp]
  have hm := hmin (Ico_subset_Icc_self (toIcoMod_mem_Ico' hL s))
  dsimp [IsMinOn] at hm
  linarith

/-- Every actual radius-R terminal gradient is disjoint from the incoming
curve. The statement applies to the terminal of the final smoothed scalar. -/
theorem visibleConnectorOrdinaryFamily_gradient_boundaries_disjoint
    {Gin : Coord → ℝ} {Uin : Set Coord} {L R : ℝ} [Fact (0 < L)]
    (D : VisibleConnectorIncomingData Gin Uin L R)
    {gamma : ℝ → Coord} (hCircle : ∀ s, planarRadius (gamma s) = R) :
    Disjoint (range D.incoming.gamma) (range gamma) := by
  apply disjoint_left.mpr
  rintro q ⟨s, rfl⟩ ⟨t, ht⟩
  have hr := visibleConnectorOrdinaryFamily_incoming_gradient_radius D s
  have he := congrArg planarRadius ht
  rw [hCircle t] at he
  linarith

end
end TightVer401

