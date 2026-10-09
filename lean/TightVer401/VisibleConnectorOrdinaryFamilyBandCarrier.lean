import TightVer401.VisibleConnectorCartesianDescent
import TightVer401.VisibleConnectorWitnessAssemblyTopology
import TightVer401.QuadraticRadialFillingBoundaryRadial
import TightVer401.VisibleConnectorFinalSmoothingCarrier

/-! The SAME raw Cartesian closed-annulus image is the entire physical closed
ruling band. This supplies the full-band carrier identification, rather than
assuming closure containment in a rebased strip or shrinking to a seam collar. -/
namespace TightVer401
noncomputable section
open Set Function Filter Metric OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

/-- All positive radial representatives, including both boundary circles,
represent exactly all physical coordinates 0 ≤ u ≤ 1 of the SAME ruling. -/
theorem visibleConnectorOrdinaryFamily_cartesian_image_eq_closed_physical_band
    {L : ℝ} (hL : 0 < L) {P W : ℝ → Coord}
    (hP : Periodic P L) (hW : Periodic W L) :
    visibleConnectorCartesianSource L P W (fun _ => 1) ''
        {z : Coord | 1 ≤ planarRadius z ∧ planarRadius z ≤ 2} =
      {x | ∃ s u : ℝ, u ∈ Icc (0 : ℝ) 1 ∧
        x = visibleConnectorSource P W (![s, u] : Coord)} := by
  have hh : Periodic (fun _ : ℝ => (1 : ℝ)) L := fun _ => rfl
  apply Subset.antisymm
  · rintro x ⟨z, hz, rfl⟩
    have hr : 0 < planarRadius z := lt_of_lt_of_le (by norm_num) hz.1
    obtain ⟨theta, htheta⟩ := quadraticRadialFilling_radiusLevel_exists_polar hr
      (show z ∈ quadraticRadialFillingRadiusLevel (planarRadius z) from rfl)
    refine ⟨visibleConnectorPhysicalParameter L theta, planarRadius z - 1,
      ⟨by linarith [hz.1], by linarith [hz.2]⟩, ?_⟩
    rw [← htheta, visibleConnectorCartesianSource_polar hP hW hh (by simpa using hr)]
    simp only [visibleConnectorPolarSource, visibleConnectorSource,
      Matrix.cons_val_zero, Matrix.cons_val_one, mul_one]
    rw [htheta]
  · rintro x ⟨s, u, hu, rfl⟩
    let z : Coord := saddlePolarChart (![1 + u, 2 * Real.pi * s / L] : Coord)
    have hr : 0 < 1 + u := by linarith [hu.1]
    have hrad : planarRadius z = 1 + u := angularDescent_radius_polar
      (q := ![1 + u, 2 * Real.pi * s / L]) (by simpa using hr)
    refine ⟨z, ⟨by rw [hrad]; linarith [hu.1], by rw [hrad]; linarith [hu.2]⟩, ?_⟩
    dsimp only [z]
    rw [visibleConnectorCartesianSource_polar hP hW hh (by simpa using hr)]
    have hclock : visibleConnectorPhysicalParameter L (2 * Real.pi * s / L) = s := by
      unfold visibleConnectorPhysicalParameter
      field_simp [hL.ne', Real.two_pi_pos.ne']
    simp only [visibleConnectorPolarSource, visibleConnectorSource,
      Matrix.cons_val_zero, Matrix.cons_val_one, hclock, mul_one, add_sub_cancel_left]

/-- The raw image identity proves the actual full source closure equals the
closed physical band, including its original and terminal boundaries. -/
theorem visibleConnectorOrdinaryFamily_source_closure_eq_closed_physical_band
    {L : ℝ} (hL : 0 < L) {P W : ℝ → Coord}
    (hP : Periodic P L) (hW : Periodic W L) {Ho Hi : ℂ ≃ₜ ℂ}
    (hImage : visibleConnectorCartesianSource L P W (fun _ => 1) ''
      {z : Coord | 1 ≤ planarRadius z ∧ planarRadius z ≤ 2} =
        annularCoordJordanClosure Ho Hi) :
    annularCoordJordanClosure Ho Hi =
      {x | ∃ s u : ℝ, u ∈ Icc (0 : ℝ) 1 ∧
        x = visibleConnectorSource P W (![s, u] : Coord)} :=
  hImage.symm.trans
    (visibleConnectorOrdinaryFamily_cartesian_image_eq_closed_physical_band hL hP hW)

/-- Specializing to the actual rebased P/W identifies the whole closure with
the exact worker3 closed rebased band, without an assumed band inclusion. -/
theorem visibleConnectorOrdinaryFamily_source_closure_eq_closed_rebased_band
    {L : ℝ} (hL : 0 < L) {p w : ℝ → Coord} {a b d : ℝ → ℝ}
    (hP : Periodic (visibleConnectorRebasedSource p w a b) L)
    (hW : Periodic (visibleConnectorRebasedRuling w a d) L) {Ho Hi : ℂ ≃ₜ ℂ}
    (hImage : visibleConnectorCartesianSource L
      (visibleConnectorRebasedSource p w a b) (visibleConnectorRebasedRuling w a d)
      (fun _ => 1) '' {z : Coord | 1 ≤ planarRadius z ∧ planarRadius z ≤ 2} =
        annularCoordJordanClosure Ho Hi) :
    annularCoordJordanClosure Ho Hi = visibleConnectorFinalSmoothingClosedRebasedBand p w a b d :=
  visibleConnectorOrdinaryFamily_source_closure_eq_closed_physical_band hL hP hW hImage

/-- SAME raw U contains the full old-coordinate strip, by actual round-image
geometry and rebase algebra. This is a deduction, not a raw-domain grant. -/
theorem visibleConnectorOrdinaryFamily_raw_contains_full_rebased_strip
    {L : ℝ} (hL : 0 < L) {p w : ℝ → Coord} {a b d : ℝ → ℝ}
    (hP : Periodic (visibleConnectorRebasedSource p w a b) L)
    (hW : Periodic (visibleConnectorRebasedRuling w a d) L) {Ho Hi : ℂ ≃ₜ ℂ}
    (hImage : visibleConnectorCartesianSource L
      (visibleConnectorRebasedSource p w a b) (visibleConnectorRebasedRuling w a d)
      (fun _ => 1) '' {z : Coord | 1 ≤ planarRadius z ∧ planarRadius z ≤ 2} =
        annularCoordJordanClosure Ho Hi)
    {U : Set Coord} (hU : annularCoordJordanClosure Ho Hi ⊆ U)
    (hd : ∀ s, 0 < d s) :
    ∀ s t : ℝ, b s ≤ t → t ≤ b s + d s →
      visibleConnectorSource p w (![a s, t] : Coord) ∈ U := by
  intro s t hlo hhi
  have hu : (t - b s) / d s ∈ Icc (0 : ℝ) 1 := by
    refine ⟨div_nonneg (sub_nonneg.mpr hlo) (hd s).le, ?_⟩
    apply (div_le_iff₀ (hd s)).mpr
    linarith
  have he : b s + ((t - b s) / d s) * d s = t := by
    field_simp [(hd s).ne']
    ring
  apply hU
  rw [visibleConnectorOrdinaryFamily_source_closure_eq_closed_rebased_band hL hP hW hImage]
  refine ⟨s, (t - b s) / d s, hu, ?_⟩
  rw [visibleConnector_rebase_source]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, he]

/-- Instantiate the fixed carrier using SAME raw U and exact full-band
representation. Only the real incoming nonpositive-side domain and literal
raw height obligations remain; raw full-band membership is constructed. -/
theorem visibleConnectorOrdinaryFamily_full_source_band_subset_final_carrier
    {L : ℝ} (hL : 0 < L) {p w : ℝ → Coord} {a b d : ℝ → ℝ}
    (hP : Periodic (visibleConnectorRebasedSource p w a b) L)
    (hW : Periodic (visibleConnectorRebasedRuling w a d) L) {Ho Hi : ℂ ≃ₜ ℂ}
    (hImage : visibleConnectorCartesianSource L
      (visibleConnectorRebasedSource p w a b) (visibleConnectorRebasedRuling w a d)
      (fun _ => 1) '' {z : Coord | 1 ≤ planarRadius z ∧ planarRadius z ≤ 2} =
        annularCoordJordanClosure Ho Hi)
    {U GinU : Set Coord} {B : Coord → ℝ}
    (hU : annularCoordJordanClosure Ho Hi ⊆ U) (hd : ∀ s, 0 < d s)
    (hGin : ∀ s t : ℝ, b s ≤ t → t ≤ 0 →
      visibleConnectorSource p w (![a s, t] : Coord) ∈ GinU)
    (hHeight : ∀ s u : ℝ, u ∈ Icc (0 : ℝ) 1 →
      B (visibleConnectorSource (visibleConnectorRebasedSource p w a b)
        (visibleConnectorRebasedRuling w a d) (![s, u] : Coord)) = b s + u * d s) :
    annularCoordJordanClosure Ho Hi ⊆ visibleConnectorFinalSmoothingCarrier U GinU B := by
  apply visibleConnectorFinalSmoothingCarrier_closed_subset
    (show annularCoordJordanClosure Ho Hi ⊆
      visibleConnectorFinalSmoothingClosedRebasedBand p w a b d from
        (visibleConnectorOrdinaryFamily_source_closure_eq_closed_rebased_band hL hP hW hImage).subset)
    hd
    (visibleConnectorOrdinaryFamily_raw_contains_full_rebased_strip hL hP hW hImage hU hd)
    hGin hHeight

end
end TightVer401

