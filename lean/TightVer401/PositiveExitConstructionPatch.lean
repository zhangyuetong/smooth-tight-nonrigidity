import TightVer401.PositiveExitConstructionFermi
import TightVer401.FermiPerturbationCollar

/-! The explicit native Fermi change, multiplied by the true gnomonic weight,
has a smooth Cartesian zero extension. Compact support strictly inside the
constructed tube proves smoothness at every point of its chart boundary. -/
open scoped Manifold
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000

def positiveExitFermiNativeChange {P tube : ℝ} {a κ : ℝ → ℝ}
    (haP : Function.Periodic a P) (hκP : Function.Periodic κ P)
    (ε ρ : ℝ) (hρ : 0 < ρ) (p : AddCircle P × Ioo (-tube) tube) : ℝ :=
  ε / 2 * haP.lift p.1 * hκP.lift p.1 * (p.2 : ℝ)^2 * fermiExitCutoff ρ hρ p.2

theorem positiveExitFermiNativeChange_contMDiff {P tube ρ : ℝ} [Fact (0 < P)]
    {a κ : ℝ → ℝ} (haP : Function.Periodic a P) (hκP : Function.Periodic κ P)
    (ha : ContDiff ℝ ∞ a) (hκ : ContDiff ℝ ∞ κ) (ε : ℝ) (hρ : 0 < ρ) :
    ContMDiff nativeProductModel 𝓘(ℝ, ℝ) ∞
      (positiveExitFermiNativeChange (tube := tube) haP hκP ε ρ hρ) := by
  have ht : ContMDiff nativeProductModel 𝓘(ℝ, ℝ) ∞
      (fun p : AddCircle P × Ioo (-tube) tube => (p.2 : ℝ)) :=
    (contMDiff_subtype_val (U := identityBandTwoSidedOpen tube)).comp contMDiff_snd
  exact ((((contMDiff_const.mul ((periodicLift_contMDiff ha haP).comp contMDiff_fst)).mul
    ((periodicLift_contMDiff hκ hκP).comp contMDiff_fst)).mul (ht.pow 2)).mul
      ((fermiExitCutoff_contDiff ρ hρ).contMDiff.comp ht))

theorem positiveExitFermiNativeChange_raw {P tube : ℝ} {a κ : ℝ → ℝ}
    (haP : Function.Periodic a P) (hκP : Function.Periodic κ P)
    (ε ρ : ℝ) (hρ : 0 < ρ) (r : ℝ) (t : Ioo (-tube) tube) :
    positiveExitFermiNativeChange haP hκP ε ρ hρ (periodProjection P r, t) =
      fermiSeamPerturbation ε a κ (fermiExitCutoff ρ hρ) (![r, (t : ℝ)] : Coord) := by
  simp [positiveExitFermiNativeChange, fermiSeamPerturbation, fermiProduct,
    fermiQuadraticCutoff, periodProjection, Function.Periodic.lift_coe]
  ring

def positiveExitFermiClosedStripInclusion {P tube ρ : ℝ} (hρtube : ρ < tube) :
    AddCircle P × Icc (-ρ) ρ → AddCircle P × Ioo (-tube) tube :=
  fun p => (p.1, ⟨p.2, ⟨(neg_lt_neg hρtube).trans_le p.2.property.1,
    p.2.property.2.trans_lt hρtube⟩⟩)

theorem positiveExitFermiClosedStripInclusion_continuous {P tube ρ : ℝ}
    (hρtube : ρ < tube) : Continuous (positiveExitFermiClosedStripInclusion (P := P) hρtube) := by
  exact continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _)

/-- The actual compact change strip, including the cutoff endpoints, in the
Cartesian image of the constructed native chart. -/
def positiveExitFermiPatchStrip {P tube ρ : ℝ}
    (e : OpenPartialHomeomorph (AddCircle P × Ioo (-tube) tube) Coord)
    (hρtube : ρ < tube) : Set Coord :=
  range (e ∘ positiveExitFermiClosedStripInclusion (P := P) hρtube)

theorem positiveExitFermiPatchStrip_compact {P tube ρ : ℝ} [Fact (0 < P)]
    (e : OpenPartialHomeomorph (AddCircle P × Ioo (-tube) tube) Coord)
    (hρtube : ρ < tube) (he : ContMDiff nativeProductModel 𝓘(ℝ, Coord) ∞ e) :
    IsCompact (positiveExitFermiPatchStrip e hρtube) :=
  isCompact_range (he.continuous.comp (positiveExitFermiClosedStripInclusion_continuous hρtube))

theorem positiveExitFermiPatchStrip_subset_target {P tube ρ : ℝ}
    (e : OpenPartialHomeomorph (AddCircle P × Ioo (-tube) tube) Coord)
    (he : e.source = univ) (hρtube : ρ < tube) :
    positiveExitFermiPatchStrip e hρtube ⊆ e.target := by
  rintro y ⟨p, rfl⟩
  exact e.map_source (by rw [he]; exact mem_univ _)

def positiveExitFermiCartesianChange {P tube : ℝ} {a κ : ℝ → ℝ}
    (haP : Function.Periodic a P) (hκP : Function.Periodic κ P)
    (ε ρ : ℝ) (hρ : 0 < ρ)
    (e : OpenPartialHomeomorph (AddCircle P × Ioo (-tube) tube) Coord) (y : Coord) : ℝ := by
  classical
  exact if y ∈ e.target then
    planarWeight y * positiveExitFermiNativeChange haP hκP ε ρ hρ (e.symm y) else 0

theorem positiveExitFermiCartesianChange_on_target {P tube : ℝ} {a κ : ℝ → ℝ}
    (haP : Function.Periodic a P) (hκP : Function.Periodic κ P)
    (ε ρ : ℝ) (hρ : 0 < ρ)
    (e : OpenPartialHomeomorph (AddCircle P × Ioo (-tube) tube) Coord) :
    EqOn (positiveExitFermiCartesianChange haP hκP ε ρ hρ e)
      (fun y => planarWeight y * positiveExitFermiNativeChange haP hκP ε ρ hρ (e.symm y)) e.target := by
  intro y hy
  classical
  simp only [positiveExitFermiCartesianChange, hy, if_pos]

theorem positiveExitFermiCartesianChange_chart {P tube : ℝ} {a κ : ℝ → ℝ}
    (haP : Function.Periodic a P) (hκP : Function.Periodic κ P)
    (ε ρ : ℝ) (hρ : 0 < ρ)
    (e : OpenPartialHomeomorph (AddCircle P × Ioo (-tube) tube) Coord)
    (he : e.source = univ) (p : AddCircle P × Ioo (-tube) tube) :
    positiveExitFermiCartesianChange haP hκP ε ρ hρ e (e p) =
      planarWeight (e p) * positiveExitFermiNativeChange haP hκP ε ρ hρ p := by
  have hp : p ∈ e.source := by rw [he]; exact mem_univ _
  rw [positiveExitFermiCartesianChange_on_target haP hκP ε ρ hρ e (e.map_source hp)]
  change planarWeight (e p) * positiveExitFermiNativeChange haP hκP ε ρ hρ (e.symm (e p)) = _
  rw [e.left_inv hp]

/-- Dividing by the actual positive gnomonic weight recovers precisely the
retained spherical cutoff change, on every actual native tube point. -/
theorem positiveExitFermiCartesianChange_height {P tube : ℝ} {a κ : ℝ → ℝ}
    (haP : Function.Periodic a P) (hκP : Function.Periodic κ P)
    (ε ρ : ℝ) (hρ : 0 < ρ)
    (e : OpenPartialHomeomorph (AddCircle P × Ioo (-tube) tube) Coord)
    (he : e.source = univ) (p : AddCircle P × Ioo (-tube) tube) :
    positiveExitFermiCartesianChange haP hκP ε ρ hρ e (e p) / planarWeight (e p) =
      positiveExitFermiNativeChange haP hκP ε ρ hρ p := by
  rw [positiveExitFermiCartesianChange_chart haP hκP ε ρ hρ e he p]
  field_simp [(planarWeight_pos (e p)).ne']

theorem positiveExitFermiCartesianChange_zero_off_strip {P tube ρ : ℝ} {a κ : ℝ → ℝ}
    (haP : Function.Periodic a P) (hκP : Function.Periodic κ P)
    (ε : ℝ) (hρ : 0 < ρ)
    (e : OpenPartialHomeomorph (AddCircle P × Ioo (-tube) tube) Coord)
    (hρtube : ρ < tube) {y : Coord} (hy : y ∉ positiveExitFermiPatchStrip e hρtube) :
    positiveExitFermiCartesianChange haP hκP ε ρ hρ e y = 0 := by
  classical
  by_cases hyt : y ∈ e.target
  · have hout : ρ ≤ |((e.symm y).2 : ℝ)| := by
      by_contra hn
      have hab : |((e.symm y).2 : ℝ)| ≤ ρ := (lt_of_not_ge hn).le
      have hbounds := abs_le.mp hab
      let p : AddCircle P × Icc (-ρ) ρ :=
        ((e.symm y).1, ⟨(e.symm y).2, hbounds⟩)
      apply hy
      refine ⟨p, ?_⟩
      have hp : positiveExitFermiClosedStripInclusion hρtube p = e.symm y := by
        exact Prod.ext rfl (Subtype.ext rfl)
      change e (positiveExitFermiClosedStripInclusion hρtube p) = y
      rw [hp, e.right_inv hyt]
    simp [positiveExitFermiCartesianChange, hyt, positiveExitFermiNativeChange,
      fermiExitCutoff_eq_zero ρ hρ hout]
  · simp [positiveExitFermiCartesianChange, hyt]

theorem positiveExitFermiCartesianChange_tsupport {P tube ρ : ℝ} [Fact (0 < P)]
    {a κ : ℝ → ℝ} (haP : Function.Periodic a P) (hκP : Function.Periodic κ P)
    (ε : ℝ) (hρ : 0 < ρ)
    (e : OpenPartialHomeomorph (AddCircle P × Ioo (-tube) tube) Coord)
    (hρtube : ρ < tube) (he : ContMDiff nativeProductModel 𝓘(ℝ, Coord) ∞ e) :
    tsupport (positiveExitFermiCartesianChange haP hκP ε ρ hρ e) ⊆
      positiveExitFermiPatchStrip e hρtube := by
  apply closure_minimal _ (positiveExitFermiPatchStrip_compact e hρtube he).isClosed
  intro y hy
  by_contra hn
  exact hy (positiveExitFermiCartesianChange_zero_off_strip haP hκP ε hρ e hρtube hn)

/-- Actual global smoothness, including every point outside and on the chart
boundary, follows from the explicit compact cutoff and the actual inverse. -/
theorem positiveExitFermiCartesianChange_contDiff {P tube ρ : ℝ} [Fact (0 < P)]
    {a κ : ℝ → ℝ} (haP : Function.Periodic a P) (hκP : Function.Periodic κ P)
    (ha : ContDiff ℝ ∞ a) (hκ : ContDiff ℝ ∞ κ) (ε : ℝ) (hρ : 0 < ρ)
    (e : OpenPartialHomeomorph (AddCircle P × Ioo (-tube) tube) Coord)
    (heS : e.source = univ) (hρtube : ρ < tube)
    (he : ContMDiff nativeProductModel 𝓘(ℝ, Coord) ∞ e)
    (heI : ContMDiffOn 𝓘(ℝ, Coord) nativeProductModel ∞ e.symm e.target) :
    ContDiff ℝ ∞ (positiveExitFermiCartesianChange haP hκP ε ρ hρ e) := by
  have hn := positiveExitFermiNativeChange_contMDiff (tube := tube) haP hκP ha hκ ε hρ
  have hlocal : ContDiffOn ℝ ∞
      (fun y => planarWeight y * positiveExitFermiNativeChange haP hκP ε ρ hρ (e.symm y)) e.target :=
    gnomonicWeight_contDiff.contDiffOn.mul (hn.comp_contMDiffOn heI).contDiffOn
  have hK := positiveExitFermiPatchStrip_compact e hρtube he
  have hKt := positiveExitFermiPatchStrip_subset_target e heS hρtube
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hyt : y ∈ e.target
  · exact ((hlocal y hyt).contDiffAt (e.open_target.mem_nhds hyt)).congr_of_eventuallyEq
      ((positiveExitFermiCartesianChange_on_target haP hκP ε ρ hρ e).eventuallyEq_of_mem
        (e.open_target.mem_nhds hyt))
  · have hyK : y ∈ (positiveExitFermiPatchStrip e hρtube)ᶜ := fun hy => hyt (hKt hy)
    have hz : positiveExitFermiCartesianChange haP hκP ε ρ hρ e =ᶠ[𝓝 y] (fun _ => 0) := by
      filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hyK] with z hz
      exact positiveExitFermiCartesianChange_zero_off_strip haP hκP ε hρ e hρtube hz
    exact contDiffAt_const.congr_of_eventuallyEq hz

theorem positiveExitFermiCartesianChange_hasCompactSupport {P tube ρ : ℝ} [Fact (0 < P)]
    {a κ : ℝ → ℝ} (haP : Function.Periodic a P) (hκP : Function.Periodic κ P)
    (ε : ℝ) (hρ : 0 < ρ)
    (e : OpenPartialHomeomorph (AddCircle P × Ioo (-tube) tube) Coord)
    (hρtube : ρ < tube) (he : ContMDiff nativeProductModel 𝓘(ℝ, Coord) ∞ e) :
    HasCompactSupport (positiveExitFermiCartesianChange haP hκP ε ρ hρ e) :=
  (positiveExitFermiPatchStrip_compact e hρtube he).of_isClosed_subset (isClosed_tsupport _)
    (positiveExitFermiCartesianChange_tsupport haP hκP ε hρ e hρtube he)

/-- The protected equality holds on the entire open complement of the actual
compact change strip, so it retains full derivative germs there. -/
theorem positiveExitFermiCartesianChange_protected_germ {P tube ρ : ℝ} [Fact (0 < P)]
    {a κ : ℝ → ℝ} (haP : Function.Periodic a P) (hκP : Function.Periodic κ P)
    (ε : ℝ) (hρ : 0 < ρ)
    (e : OpenPartialHomeomorph (AddCircle P × Ioo (-tube) tube) Coord)
    (hρtube : ρ < tube) (he : ContMDiff nativeProductModel 𝓘(ℝ, Coord) ∞ e)
    (G : Coord → ℝ) :
    IsOpen (positiveExitFermiPatchStrip e hρtube)ᶜ ∧
      EqOn (fun y => G y + positiveExitFermiCartesianChange haP hκP ε ρ hρ e y) G
        (positiveExitFermiPatchStrip e hρtube)ᶜ ∧
      ∀ y ∉ positiveExitFermiPatchStrip e hρtube,
        (fun z => G z + positiveExitFermiCartesianChange haP hκP ε ρ hρ e z) =ᶠ[𝓝 y] G := by
  have hopen := (positiveExitFermiPatchStrip_compact e hρtube he).isClosed.isOpen_compl
  have heq : EqOn (fun y => G y + positiveExitFermiCartesianChange haP hκP ε ρ hρ e y) G
      (positiveExitFermiPatchStrip e hρtube)ᶜ := by
    intro y hy
    change G y + positiveExitFermiCartesianChange haP hκP ε ρ hρ e y = G y
    rw [positiveExitFermiCartesianChange_zero_off_strip haP hκP ε hρ e hρtube hy, add_zero]
  exact ⟨hopen, heq, fun y hy => heq.eventuallyEq_of_mem (hopen.mem_nhds hy)⟩

/-- Choose a genuine smaller cutoff and prove the explicit extension smooth
and compactly supported strictly inside the constructed chart target. -/
theorem positiveExitFermi_exists_cartesian_patch {P tube : ℝ} [Fact (0 < P)]
    {a κ : ℝ → ℝ} (haP : Function.Periodic a P) (hκP : Function.Periodic κ P)
    (ha : ContDiff ℝ ∞ a) (hκ : ContDiff ℝ ∞ κ) (ε : ℝ) (htube : 0 < tube)
    (e : OpenPartialHomeomorph (AddCircle P × Ioo (-tube) tube) Coord)
    (heS : e.source = univ) (he : ContMDiff nativeProductModel 𝓘(ℝ, Coord) ∞ e)
    (heI : ContMDiffOn 𝓘(ℝ, Coord) nativeProductModel ∞ e.symm e.target) :
    ∃ ρ : ℝ, ∃ hρ : 0 < ρ, ∃ hρtube : ρ < tube,
      ContDiff ℝ ∞ (positiveExitFermiCartesianChange haP hκP ε ρ hρ e) ∧
      HasCompactSupport (positiveExitFermiCartesianChange haP hκP ε ρ hρ e) ∧
      IsCompact (positiveExitFermiPatchStrip e hρtube) ∧
      positiveExitFermiPatchStrip e hρtube ⊆ e.target ∧
      tsupport (positiveExitFermiCartesianChange haP hκP ε ρ hρ e) ⊆
        positiveExitFermiPatchStrip e hρtube ∧
      (∀ p, positiveExitFermiCartesianChange haP hκP ε ρ hρ e (e p) =
        planarWeight (e p) * positiveExitFermiNativeChange haP hκP ε ρ hρ p) ∧
      (∀ y ∉ positiveExitFermiPatchStrip e hρtube,
        positiveExitFermiCartesianChange haP hκP ε ρ hρ e y = 0) := by
  let ρ := tube / 2
  have hρ : 0 < ρ := half_pos htube
  have hρtube : ρ < tube := half_lt_self htube
  exact ⟨ρ, hρ, hρtube,
    positiveExitFermiCartesianChange_contDiff haP hκP ha hκ ε hρ e heS hρtube he heI,
    positiveExitFermiCartesianChange_hasCompactSupport haP hκP ε hρ e hρtube he,
    positiveExitFermiPatchStrip_compact e hρtube he,
    positiveExitFermiPatchStrip_subset_target e heS hρtube,
    positiveExitFermiCartesianChange_tsupport haP hκP ε hρ e hρtube he,
    positiveExitFermiCartesianChange_chart haP hκP ε ρ hρ e heS,
    fun y hy => positiveExitFermiCartesianChange_zero_off_strip haP hκP ε hρ e hρtube hy⟩

end
end TightVer401
