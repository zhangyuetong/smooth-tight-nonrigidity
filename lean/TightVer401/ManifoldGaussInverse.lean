import TightVer401.GaussInverseCoordinates
import TightVer401.SphereSupportOpen

/-! Actual local inverses of a regular Gauss map on a smooth surface. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology RealInnerProductSpace Manifold

local instance : Fact (Module.finrank ℝ Ambient = 2 + 1) := ⟨by simp [Ambient]⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Coord M]
  [IsManifold 𝓘(ℝ, Coord) ∞ M]

theorem gaussManifold_exists_smooth_local_inverse {N : M → RoundSphere} {U : Set M}
    (hN : ContMDiffOn 𝓘(ℝ, Coord) (𝓡 2) ∞ N U) (hU : IsOpen U)
    (hi : ∀ q ∈ U, Function.Injective
      (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) (fun x => (N x).val) q))
    {p : M} (hp : p ∈ U) :
    ∃ e : OpenPartialHomeomorph M RoundSphere,
      p ∈ e.source ∧ e.source ⊆ U ∧ (∀ q ∈ e.source, e q = N q) ∧
      ContMDiffOn (𝓡 2) 𝓘(ℝ, Coord) ∞ e.symm e.target := by
  let c := chartAt Coord p
  let V := c.target ∩ c.symm ⁻¹' U
  have hV : IsOpen V := c.symm.continuousOn.isOpen_inter_preimage c.open_target hU
  have hpc : p ∈ c.source := mem_chart_source Coord p
  have hcp : c p ∈ V := ⟨c.map_source hpc, by change c.symm (c p) ∈ U; rwa [c.left_inv hpc]⟩
  have hcs : ContMDiffOn 𝓘(ℝ, Coord) 𝓘(ℝ, Coord) ∞ c.symm c.target :=
    contMDiffOn_chart_symm
  have hv : ContMDiffOn 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) ∞ (fun x => (N x).val) U :=
    (show ContMDiff (𝓡 2) 𝓘(ℝ, Ambient) ∞ (fun q : RoundSphere => q.val) from
      contMDiff_coe_sphere).comp_contMDiffOn hN
  have hNc : ContDiffOn ℝ ∞ (fun z => (N (c.symm z)).val) V :=
    (hv.comp (hcs.mono inter_subset_left) (fun _ hz => hz.2)).contDiffOn
  have hunit : ∀ z ∈ V, ‖(N (c.symm z)).val‖ = 1 := fun z _ => roundSphere_norm _
  have hic : ∀ z ∈ V, Function.Injective (fderiv ℝ (fun z => (N (c.symm z)).val) z) := by
    intro z hz
    have hdn := (hv.contMDiffAt (hU.mem_nhds hz.2)).mdifferentiableAt (by simp)
    have hdc := (hcs.contMDiffAt (c.open_target.mem_nhds hz.1)).mdifferentiableAt (by simp)
    have hci := (mdifferentiable_chart (I := 𝓘(ℝ, Coord)) p).symm.mfderiv_injective hz.1
    have hd := mfderiv_comp z hdn hdc
    rw [mfderiv_eq_fderiv] at hd
    change fderiv ℝ (fun z => (N (c.symm z)).val) z = _ at hd
    rw [hd]
    exact (hi _ hz.2).comp hci
  let w := (N p).val
  have hw : w ≠ 0 := roundSphere_ne_zero _
  have hu : ‖w‖ = 1 := roundSphere_norm _
  have hpos : 0 < inner ℝ w (N (c.symm (c p))).val := by
    rw [c.left_inv hpc]
    change 0 < inner ℝ w w
    rw [real_inner_self_eq_norm_sq, hu, one_pow]
    exact zero_lt_one
  obtain ⟨a, hap, haV, ha, haf, haN⟩ := gaussMap_exists_smooth_inverse_coordinates
    hNc hV hunit hic w hw hu hcp hpos
  let b := sphereHemisphereChart w hw hu
  let e := (c.trans a).trans b
  have hep : p ∈ e.source := by
    change (p ∈ c.source ∧ c p ∈ a.source) ∧ a (c p) ∈ b.source
    exact ⟨⟨hpc, hap⟩, mem_univ _⟩
  have heU : e.source ⊆ U := by
    intro x hx
    change (x ∈ c.source ∧ c x ∈ a.source) ∧ a (c x) ∈ b.source at hx
    have hvx := (haV hx.1.2).2
    change c.symm (c x) ∈ U at hvx
    rwa [c.left_inv hx.1.1] at hvx
  have heN : ∀ x ∈ e.source, e x = N x := by
    intro x hx
    change (x ∈ c.source ∧ c x ∈ a.source) ∧ a (c x) ∈ b.source at hx
    apply Subtype.ext
    change sphereHemisphere w hw (a (c x)) = (N x).val
    have heq := haN (c x) hx.1.2
    rw [c.left_inv hx.1.1] at heq
    exact heq.symm
  refine ⟨e, hep, heU, heN, ?_⟩
  intro y hy
  change (y ∈ b.target ∧ b.symm y ∈ (c.trans a).target) at hy
  have hay : b.symm y ∈ a.target := hy.2.1
  have hcy : a.symm (b.symm y) ∈ c.target := hy.2.2
  have hb : ContMDiffAt (𝓡 2) 𝓘(ℝ, Coord) ∞ b.symm y :=
    (sphereHemisphereInverse_contDiffAt w hw hy.1).contMDiffAt.comp y (contMDiff_coe_sphere y)
  have haa := (ha.contDiffAt (a.open_target.mem_nhds hay)).contMDiffAt.comp y hb
  have hcc := (hcs.contMDiffAt (c.open_target.mem_nhds hcy)).comp y haa
  exact hcc.contMDiffWithinAt

theorem gaussManifold_image_isOpen {N : M → RoundSphere} {U : Set M}
    (hN : ContMDiffOn 𝓘(ℝ, Coord) (𝓡 2) ∞ N U) (hU : IsOpen U)
    (hi : ∀ q ∈ U, Function.Injective
      (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) (fun x => (N x).val) q)) :
    IsOpen (N '' U) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨p, hp, rfl⟩
  obtain ⟨e, hep, heU, heN, _⟩ := gaussManifold_exists_smooth_local_inverse hN hU hi hp
  have htarget : e.target ⊆ N '' U := by
    intro z hz
    exact ⟨e.symm z, heU (e.map_target hz), (heN _ (e.map_target hz)).symm.trans (e.right_inv hz)⟩
  have hNp : N p ∈ e.target := by rw [← heN p hep]; exact e.map_source hep
  exact mem_of_superset (e.open_target.mem_nhds hNp) htarget

end
end TightVer401
