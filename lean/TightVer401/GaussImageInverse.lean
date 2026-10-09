import TightVer401.ManifoldGaussInverse
import TightVer401.SphereSupportOpenConverse

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology RealInnerProductSpace Manifold

local instance : Fact (Module.finrank ℝ Ambient = 2 + 1) := ⟨by simp [Ambient]⟩

variable {M : Type*} [Nonempty M]

def gaussImageInverse (N : M → RoundSphere) (U : Set M) (q : RoundSphere) : M := by
  classical
  exact if hq : q ∈ N '' U then Classical.choose hq else Classical.arbitrary M

theorem gaussImageInverse_mem {N : M → RoundSphere} {U : Set M} {q : RoundSphere}
    (hq : q ∈ N '' U) : gaussImageInverse N U q ∈ U := by
  simp only [gaussImageInverse, dif_pos hq]
  exact (Classical.choose_spec hq).1

theorem gaussImageInverse_right {N : M → RoundSphere} {U : Set M} {q : RoundSphere}
    (hq : q ∈ N '' U) : N (gaussImageInverse N U q) = q := by
  simp only [gaussImageInverse, dif_pos hq]
  exact (Classical.choose_spec hq).2

theorem gaussImageInverse_left {N : M → RoundSphere} {U : Set M}
    (hNi : InjOn N U) {p : M} (hp : p ∈ U) : gaussImageInverse N U (N p) = p :=
  hNi (gaussImageInverse_mem (mem_image_of_mem N hp)) hp
    (gaussImageInverse_right (mem_image_of_mem N hp))

variable [TopologicalSpace M] [ChartedSpace Coord M]
  [IsManifold 𝓘(ℝ, Coord) ∞ M]

theorem gaussImageInverse_contMDiffOn {N : M → RoundSphere} {U : Set M}
    (hN : ContMDiffOn 𝓘(ℝ, Coord) (𝓡 2) ∞ N U) (hU : IsOpen U)
    (hi : ∀ q ∈ U, Function.Injective
      (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) (fun x => (N x).val) q))
    (hNi : InjOn N U) :
    ContMDiffOn (𝓡 2) 𝓘(ℝ, Coord) ∞ (gaussImageInverse N U) (N '' U) := by
  intro q hq
  let p := gaussImageInverse N U q
  have hp : p ∈ U := gaussImageInverse_mem hq
  have hNq : N p = q := gaussImageInverse_right hq
  obtain ⟨e, hep, heU, heN, he⟩ := gaussManifold_exists_smooth_local_inverse hN hU hi hp
  have hqT : q ∈ e.target := by rw [← hNq, ← heN p hep]; exact e.map_source hep
  have heq : gaussImageInverse N U =ᶠ[𝓝 q] e.symm := by
    filter_upwards [e.open_target.mem_nhds hqT] with z hz
    have hx := e.map_target hz
    have hNz : N (e.symm z) = z := (heN _ hx).symm.trans (e.right_inv hz)
    have hzΩ : z ∈ N '' U := ⟨e.symm z, heU hx, hNz⟩
    exact hNi (gaussImageInverse_mem hzΩ) (heU hx) ((gaussImageInverse_right hzΩ).trans hNz.symm)
  exact ((he.contMDiffAt (e.open_target.mem_nhds hqT)).congr_of_eventuallyEq heq).contMDiffWithinAt

theorem gaussImage_inverse {N : M → RoundSphere} {U : Set M}
    (hN : ContMDiffOn 𝓘(ℝ, Coord) (𝓡 2) ∞ N U) (hU : IsOpen U)
    (hi : ∀ q ∈ U, Function.Injective
      (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) (fun x => (N x).val) q))
    (hNi : InjOn N U) :
    IsOpen (N '' U) ∧
      ContMDiffOn (𝓡 2) 𝓘(ℝ, Coord) ∞ (gaussImageInverse N U) (N '' U) ∧
      (∀ p ∈ U, gaussImageInverse N U (N p) = p) ∧
      (∀ q ∈ N '' U, gaussImageInverse N U q ∈ U ∧ N (gaussImageInverse N U q) = q) :=
  ⟨gaussManifold_image_isOpen hN hU hi, gaussImageInverse_contMDiffOn hN hU hi hNi,
    fun _ hp => gaussImageInverse_left hNi hp,
    fun _ hq => ⟨gaussImageInverse_mem hq, gaussImageInverse_right hq⟩⟩

theorem gaussImage_support_reconstruction {N : M → RoundSphere} {X : M → Ambient} {U : Set M}
    (hN : ContMDiffOn 𝓘(ℝ, Coord) (𝓡 2) ∞ N U) (hU : IsOpen U)
    (hi : ∀ q ∈ U, Function.Injective
      (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) (fun x => (N x).val) q))
    (hNi : InjOn N U) (hX : ContMDiffOn 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) ∞ X U)
    (hn : ∀ p ∈ U, ∀ v : TangentSpace 𝓘(ℝ, Coord) p,
      @inner ℝ Ambient _ (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) X p v) (N p).val = 0) :
    let F := fun q => X (gaussImageInverse N U q)
    let H := fun q => inner ℝ (F q) q.val
    IsOpen (N '' U) ∧ ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H (N '' U) ∧
      (∀ p ∈ U, X p = globalSphereSupport H (N p)) := by
  let F := fun q => X (gaussImageInverse N U q)
  let H := fun q => inner ℝ (F q) q.val
  have hΩ := gaussManifold_image_isOpen hN hU hi
  have hI := gaussImageInverse_contMDiffOn hN hU hi hNi
  have hF : ContMDiffOn (𝓡 2) 𝓘(ℝ, Ambient) ∞ F (N '' U) :=
    hX.comp hI (fun _ hq => gaussImageInverse_mem hq)
  have hH : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H (N '' U) :=
    contDiff_inner.contMDiff.comp_contMDiffOn (hF.prodMk_space
      (show ContMDiff (𝓡 2) 𝓘(ℝ, Ambient) ∞ (fun q : RoundSphere => q.val) from
        contMDiff_coe_sphere).contMDiffOn)
  have hnF : ∀ q ∈ N '' U, ∀ v : TangentSpace (𝓡 2) q,
      @inner ℝ Ambient _ (mfderiv (𝓡 2) 𝓘(ℝ, Ambient) F q v) q.val = 0 := by
    intro q hq v
    have hp := gaussImageInverse_mem hq
    have hdX := (hX.contMDiffAt (hU.mem_nhds hp)).mdifferentiableAt (by simp)
    have hdI := (hI.contMDiffAt (hΩ.mem_nhds hq)).mdifferentiableAt (by simp)
    have hd := mfderiv_comp q hdX hdI
    change mfderiv (𝓡 2) 𝓘(ℝ, Ambient) F q = _ at hd
    rw [hd]
    have hh := hn _ hp (mfderiv (𝓡 2) 𝓘(ℝ, Coord) (gaussImageInverse N U) q v)
    rwa [gaussImageInverse_right hq] at hh
  have he := globalSphereSupport_converseOn hF hΩ hnF
  refine ⟨hΩ, hH, ?_⟩
  intro p hp
  have hep := he (N p) (mem_image_of_mem N hp)
  change X (gaussImageInverse N U (N p)) = globalSphereSupport H (N p) at hep
  rwa [gaussImageInverse_left hNi hp] at hep

omit [Nonempty M] in
theorem gaussImage_support_exists {N : M → RoundSphere} {X : M → Ambient} {U : Set M}
    (hN : ContMDiffOn 𝓘(ℝ, Coord) (𝓡 2) ∞ N U) (hU : IsOpen U)
    (hi : ∀ q ∈ U, Function.Injective
      (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) (fun x => (N x).val) q))
    (hNi : InjOn N U) (hX : ContMDiffOn 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) ∞ X U)
    (hn : ∀ p ∈ U, ∀ v : TangentSpace 𝓘(ℝ, Coord) p,
      @inner ℝ Ambient _ (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) X p v) (N p).val = 0) :
    ∃ H : RoundSphere → ℝ, IsOpen (N '' U) ∧
      ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H (N '' U) ∧
      (∀ p ∈ U, X p = globalSphereSupport H (N p)) := by
  classical
  by_cases hM : Nonempty M
  · letI : Nonempty M := hM
    exact ⟨_, gaussImage_support_reconstruction hN hU hi hNi hX hn⟩
  · refine ⟨fun _ => 0, gaussManifold_image_isOpen hN hU hi, contMDiff_const.contMDiffOn, ?_⟩
    intro p _
    exact (hM ⟨p⟩).elim

end
end TightVer401
