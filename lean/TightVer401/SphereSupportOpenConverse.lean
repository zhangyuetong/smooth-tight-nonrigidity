import TightVer401.SphereSupportOpen

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology RealInnerProductSpace Manifold

local instance : Fact (Module.finrank ℝ Ambient = 2 + 1) := ⟨by simp [Ambient]⟩

theorem globalSphereSupport_converseOn {F : RoundSphere → Ambient} {Ω : Set RoundSphere}
    (hF : ContMDiffOn (𝓡 2) 𝓘(ℝ, Ambient) ∞ F Ω) (hΩ : IsOpen Ω)
    (hn : ∀ q ∈ Ω, ∀ v : TangentSpace (𝓡 2) q,
      @inner ℝ Ambient _ (mfderiv (𝓡 2) 𝓘(ℝ, Ambient) F q v) q.val = 0) :
    ∀ q ∈ Ω, F q = globalSphereSupport (fun x => inner ℝ (F x) x.val) q := by
  intro q hq
  let w := q.val
  have hw : w ≠ 0 := roundSphere_ne_zero q
  have hu : ‖w‖ = 1 := roundSphere_norm q
  let P := sphereHemispherePoint w hw hu
  let Q := sphereHemisphere w hw
  let V := hemisphereDomain w hw hu Ω
  have hV : IsOpen V := hemisphereDomain_isOpen w hw hu hΩ
  have hP : P 0 = q := by
    apply Subtype.ext
    exact sphereHemisphere_zero w hw hu
  have hzero : (0 : Coord) ∈ V := by change P 0 ∈ Ω; rwa [hP]
  have hFp : ContDiffOn ℝ ∞ (fun z => F (P z)) V :=
    (hF.comp (sphereHemispherePoint_contMDiff w hw hu).contMDiffOn (fun _ hz => hz)).contDiffOn
  have hnP : ∀ z ∈ V, IsUnitNormalAt (fun z => F (P z)) (Q z) z := by
    intro z hz
    constructor
    · rw [real_inner_self_eq_norm_sq, sphereHemisphere_norm w hw hu, one_pow]
    · intro v
      have hdf := (hF.contMDiffAt (hΩ.mem_nhds hz)).mdifferentiableAt (by simp)
      have hdp := ((sphereHemispherePoint_contMDiff w hw hu).contMDiffAt (x := z)).mdifferentiableAt (by simp)
      have hd := mfderiv_comp z hdf hdp
      rw [mfderiv_eq_fderiv] at hd
      change fderiv ℝ (fun z => F (P z)) z = _ at hd
      rw [hd]
      exact hn _ hz _
  have hg := sphereHemisphere_metric w hw hu
  have hgV : SmoothPositiveOn (inducedMetric Q) V :=
    ⟨fun i j => (hg.1.1 i j).mono (subset_univ _), fun z _ => hg.1.2 z (mem_univ z)⟩
  have hQV : IsometricOn (inducedMetric Q) Q V :=
    ⟨hg.2.1.mono (subset_univ _), fun z _ => hg.2.2 z (mem_univ z)⟩
  have he := sphereSupportMap_converse_local hgV hQV hFp hV hnP (x := 0) hzero
  change F (P 0) = hemisphereSupport w hw hu (fun x => inner ℝ (F x) x.val) 0 at he
  rwa [hP] at he

end
end TightVer401
