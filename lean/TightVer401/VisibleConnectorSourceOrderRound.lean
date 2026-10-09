import TightVer401.VisibleConnectorSourceOrder
import TightVer401.VisibleConnectorSourceInverseGlobal

/-! Fixed-round actual Cartesian source-order application. The only source
nesting used by signed count is the proved round radius-one/radius-two nesting;
desired terminal/incoming nesting is an output, not an inverse premise. -/
namespace TightVer401
noncomputable section
open Set Function Filter Metric OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

/-- Actual positive Cartesian Jacobian and ordinary positive disjoint boundary
traces force incoming fill strictly inside terminal fill for the SAME `F/O`. -/
theorem visibleConnectorSourceOrder_round
    {F : Coord → Coord} {O : Set Coord} {Ho Hi : ℂ ≃ₜ ℂ}
    {etaOuter etaInner : ℝ → ℂ}
    (hO : IsOpen O) (hF : ContDiffOn ℝ ∞ F O)
    (hKO : {p : Coord | 1 ≤ planarRadius p ∧ planarRadius p ≤ 2} ⊆ O)
    (hJ : ∀ p : Coord, 1 ≤ planarRadius p → planarRadius p ≤ 2 →
      0 < annularJacobian F p)
    (hOuter : PositiveJordanParametrization Ho etaOuter)
    (hInner : PositiveJordanParametrization Hi etaInner)
    (hTraceOuter : ∀ t, annularComplexConjugate F (unitCircleParam 0 2 t) = etaOuter t)
    (hTraceInner : ∀ t, annularComplexConjugate F (unitCircleParam 0 1 t) = etaInner t)
    (hDisjoint : Disjoint (frontier (jordanInterior Ho)) (frontier (jordanInterior Hi)))
    {c : ℂ} (hcOuter : c ∈ jordanInterior Ho) (hcInner : c ∈ jordanInterior Hi) :
    closure (jordanInterior Hi) ⊆ jordanInterior Ho := by
  let R2 := roundDiskChart 2 (by norm_num)
  let R1 := roundDiskChart 1 zero_lt_one
  have hClosed : annularCoordJordanClosure R2 R1 =
      {p : Coord | 1 ≤ planarRadius p ∧ planarRadius p ≤ 2} :=
    visibleConnectorSourceInverse_round_closed zero_lt_one (by norm_num)
  have hOpen : annularCoordJordanInterior R2 R1 =
      {p : Coord | 1 < planarRadius p ∧ planarRadius p < 2} :=
    visibleConnectorSourceInverse_round_open zero_lt_one (by norm_num)
  have hSourceNested : closure (jordanInterior R1) ⊆ jordanInterior R2 := by
    dsimp [R1,R2]
    rw [roundDiskChart_interior,roundDiskChart_interior,closure_ball _ (ne_of_gt zero_lt_one)]
    exact closedBall_subset_ball (by norm_num : (1:ℝ) < 2)
  have hRoundOuter := quadraticRadialFillingDegree_positive_round 2 (by norm_num)
  have hRoundInner := quadraticRadialFillingDegree_positive_round 1 zero_lt_one
  let Oc : Set ℂ := seamComplexCoord ⁻¹' O
  let Fc := annularComplexConjugate F
  have hOc : IsOpen Oc := hO.preimage seamComplexCoord.continuous
  have hFc : ContDiffOn ℝ ∞ Fc Oc :=
    seamComplexCoord.symm.contDiff.comp_contDiffOn
      (hF.comp seamComplexCoord.contDiff.contDiffOn (fun _ hz => hz))
  have hKOc : annularJordanClosure R2 R1 ⊆ Oc := by
    intro z hz
    change seamComplexCoord z ∈ O
    apply hKO
    rw [← hClosed]
    exact mem_image_of_mem seamComplexCoord hz
  have hPositive : ∀ z ∈ annularJordanInterior R2 R1, 0 < (fderiv ℝ Fc z).det := by
    intro z hz
    have hzCoord : seamComplexCoord z ∈ annularCoordJordanInterior R2 R1 :=
      mem_image_of_mem seamComplexCoord hz
    have hzRound : 1 < planarRadius (seamComplexCoord z) ∧ planarRadius (seamComplexCoord z) < 2 := by
      rw [hOpen] at hzCoord
      exact hzCoord
    have hzO : seamComplexCoord z ∈ O := hKO ⟨hzRound.1.le,hzRound.2.le⟩
    have hd : DifferentiableAt ℝ F (seamComplexCoord z) :=
      hF.contDiffAt (hO.mem_nhds hzO) |>.differentiableAt (by simp)
    have heq := annular_complex_conjugate_jacobian hd
    change annularJacobian F (seamComplexCoord z) = (fderiv ℝ Fc z).det at heq
    rw [← heq]
    exact hJ _ hzRound.1.le hzRound.2.le
  have hOuterFun : Fc ∘ unitCircleParam 0 2 = etaOuter := funext hTraceOuter
  have hInnerFun : Fc ∘ unitCircleParam 0 1 = etaInner := funext hTraceInner
  have hImageOuter : PositiveJordanParametrization Ho (Fc ∘ unitCircleParam 0 2) := by
    rw [hOuterFun]
    exact hOuter
  have hImageInner : PositiveJordanParametrization Hi (Fc ∘ unitCircleParam 0 1) := by
    rw [hInnerFun]
    exact hInner
  exact visibleConnector_actual_positive_map_preserves_positive_jordan_order
    hRoundOuter hRoundInner hSourceNested Fc Oc hOc hFc hKOc hPositive
    hImageOuter hImageInner hDisjoint hcOuter hcInner

end
end TightVer401
