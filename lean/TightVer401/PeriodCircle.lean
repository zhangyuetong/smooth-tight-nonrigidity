import TightVer401.AdditiveQuotientCharts

/-! The actual period quotient ℝ/(Lℤ) as a smooth manifold, using OpenAI's
quotient atlas and the actual local affine representatives of the quotient. -/
namespace TightVer401
noncomputable section
open Set Filter AddCommGroup OAI.RawQuotientLie
open scoped Manifold ContDiff Topology
set_option backward.isDefEq.respectTransparency false

def periodProjection (L : ℝ) : ℝ →+ AddCircle L := QuotientAddGroup.mk' _

def periodChart (L : ℝ) [Fact (0 < L)] : OpenPartialHomeomorph ℝ (AddCircle L) :=
  AddCircle.openPartialHomeomorphCoe L (-L / 2)

theorem periodChart_zero_source (L : ℝ) [hL : Fact (0 < L)] :
    (0 : ℝ) ∈ (periodChart L).source := by
  change 0 ∈ Ioo (-L / 2) (-L / 2 + L)
  constructor <;> linarith [hL.out]

theorem periodChart_zero_target (L : ℝ) [Fact (0 < L)] :
    (0 : AddCircle L) ∈ (periodChart L).target := by
  simpa [periodChart] using (periodChart L).map_source (periodChart_zero_source L)

theorem periodChart_coords_contDiff (L : ℝ) [hL : Fact (0 < L)] :
    ContDiffOn ℝ ∞ ((periodChart L).symm ∘ periodProjection L)
      (periodProjection L ⁻¹' (periodChart L).target) := by
  intro x hx
  have hn : (x : AddCircle L) ≠ ((-L / 2 : ℝ) : AddCircle L) := hx
  have hm : ¬ x ≡ (-L / 2) [PMOD L] := not_modEq_iff_ne_mod_zmultiples.mpr hn
  have he : ((periodChart L).symm ∘ periodProjection L) =ᶠ[𝓝 x]
      (fun y => y - toIcoDiv hL.out (-L / 2) x • L) := by
    filter_upwards [eventuallyEq_toIcoDiv_nhds hL.out (-L / 2) hm] with y hy
    change toIcoMod hL.out (-L / 2) y = y - toIcoDiv hL.out (-L / 2) x • L
    rw [toIcoMod, hy]
  exact ((contDiffAt_id.sub contDiffAt_const).congr_of_eventuallyEq he).contDiffWithinAt

@[instance_reducible]
def periodCircleChartedSpace (L : ℝ) [Fact (0 < L)] : ChartedSpace ℝ (AddCircle L) :=
  addQuotientChartedSpace (periodChart L) (periodChart_zero_target L)

theorem periodCircle_isManifold (L : ℝ) [Fact (0 < L)] :
    @IsManifold ℝ _ ℝ _ _ ℝ _ 𝓘(ℝ, ℝ) ∞ (AddCircle L) _ (periodCircleChartedSpace L) := by
  exact addQuotient_isManifold (periodProjection L) QuotientAddGroup.mk_surjective
    (fun x : ℝ => x) contMDiff_id (periodChart L) (periodChart_zero_target L) rfl
    (periodChart_coords_contDiff L).contMDiffOn

theorem periodProjection_contMDiff (L : ℝ) [Fact (0 < L)] :
    letI := periodCircleChartedSpace L
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (periodProjection L) := by
  exact addQuotient_projection_smooth (periodChart L) (periodChart_zero_target L)
    (periodProjection L) (AddCircle.continuous_mk' L) (periodChart_coords_contDiff L).contMDiffOn

theorem periodCircle_descend_smooth (L : ℝ) [Fact (0 < L)] {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (f : AddCircle L → V)
    (hf : ContDiff ℝ ∞ (f ∘ periodProjection L)) :
    letI := periodCircleChartedSpace L
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, V) ∞ f := by
  exact addQuotient_descend_smooth (periodChart L) (periodChart_zero_target L)
    (periodProjection L) QuotientAddGroup.mk_surjective (fun x : ℝ => x) contMDiff_id rfl f
    hf.contMDiff

end
end TightVer401
