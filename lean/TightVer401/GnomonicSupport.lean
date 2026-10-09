import TightVer401.GnomonicCoordinates
import TightVer401.PlanarSupportSecondForm
import TightVer401.SphereSupportOpenConverse
import TightVer401.SupportLocality

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology RealInnerProductSpace Manifold
set_option backward.isDefEq.respectTransparency false

local instance : Fact (Module.finrank ℝ Ambient = 2 + 1) := ⟨by simp [Ambient]⟩

def gnomonicPotential (H : RoundSphere → ℝ) (p : Coord) : ℝ :=
  planarWeight p * H (gnomonicPoint p)

theorem planarSupportMap_height (G : Coord → ℝ) (p : Coord) :
    inner ℝ (planarSupportMap G p) (planarUnitNormal p) = G p / planarWeight p := by
  simp only [planarSupportMap, planarUnitNormal, EuclideanSpace.inner_toLp_toLp]
  simp [dotProduct, Fin.sum_univ_succ]
  ring

theorem gnomonicPotential_contDiffOn {H : RoundSphere → ℝ} {Ω : Set RoundSphere}
    (hH : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H Ω) :
    ContDiffOn ℝ ∞ (gnomonicPotential H) (gnomonicPoint ⁻¹' Ω) :=
  gnomonicWeight_contDiff.contDiffOn.mul
    (hH.comp gnomonicPoint_contMDiff.contMDiffOn (fun _ hx => hx)).contDiffOn

theorem gnomonicSupport_reconstruction {H : RoundSphere → ℝ} {Ω : Set RoundSphere}
    (hH : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H Ω) (hΩ : IsOpen Ω)
    (hnorth : ∀ q ∈ Ω, 0 < q.val 2) {p : Coord} (hp : gnomonicPoint p ∈ Ω) :
    planarSupportMap (gnomonicPotential H) p = globalSphereSupport H (gnomonicPoint p) := by
  let V := gnomonicPoint ⁻¹' Ω
  let G := gnomonicPotential H
  let I := fun q : RoundSphere => gnomonicInverse q.val
  let F := fun q : RoundSphere => planarSupportMap G (I q)
  have hV : IsOpen V := hΩ.preimage gnomonicPoint_contMDiff.continuous
  have hG : ContDiffOn ℝ ∞ G V := gnomonicPotential_contDiffOn hH
  have hX : ContDiffOn ℝ ∞ (planarSupportMap G) V := planarSupportMap_contDiffOn hG hV
  have hI : ContMDiffOn (𝓡 2) 𝓘(ℝ, Coord) ∞ I Ω := by
    intro q hq
    exact (gnomonicInverse_contMDiffAt (hnorth q hq)).contMDiffWithinAt
  have hi : ∀ q ∈ Ω, I q ∈ V := by
    intro q hq
    change gnomonicPoint (gnomonicInverse q.val) ∈ Ω
    rwa [gnomonic_right_inverse (hnorth q hq)]
  have hF : ContMDiffOn (𝓡 2) 𝓘(ℝ, Ambient) ∞ F Ω :=
    hX.contMDiffOn.comp hI hi
  have hn : ∀ q ∈ Ω, ∀ v : TangentSpace (𝓡 2) q,
      @inner ℝ Ambient _ (mfderiv (𝓡 2) 𝓘(ℝ, Ambient) F q v) q.val = 0 := by
    intro q hq v
    have hdf := (hX.contDiffAt (hV.mem_nhds (hi q hq))).contMDiffAt.mdifferentiableAt (by simp)
    have hdi := (hI.contMDiffAt (hΩ.mem_nhds hq)).mdifferentiableAt (by simp)
    have hd := mfderiv_comp q hdf hdi
    rw [mfderiv_eq_fderiv] at hd
    change mfderiv (𝓡 2) 𝓘(ℝ, Ambient) F q = _ at hd
    rw [hd]
    have hqval : planarUnitNormal (I q) = q.val :=
      congrArg Subtype.val (gnomonic_right_inverse (hnorth q hq))
    rw [← hqval]
    exact (planarSupportMap_isUnitNormal hG hV (hi q hq)).2 _
  have he := globalSphereSupport_converseOn hF hΩ hn
  have hheight : EqOn (fun q => inner ℝ (F q) q.val) H Ω := by
    intro q hq
    have hqval : planarUnitNormal (I q) = q.val :=
      congrArg Subtype.val (gnomonic_right_inverse (hnorth q hq))
    change inner ℝ (planarSupportMap G (I q)) q.val = H q
    rw [← hqval, planarSupportMap_height]
    change (planarWeight (I q) * H (gnomonicPoint (I q))) / planarWeight (I q) = H q
    rw [gnomonic_right_inverse (hnorth q hq)]
    exact mul_div_cancel_left₀ _ (ne_of_gt (planarWeight_pos (I q)))
  have hleft : I (gnomonicPoint p) = p := gnomonic_left_inverse p
  calc
    planarSupportMap G p = F (gnomonicPoint p) := by dsimp [F]; rw [hleft]
    _ = globalSphereSupport (fun q => inner ℝ (F q) q.val) (gnomonicPoint p) := he _ hp
    _ = globalSphereSupport H (gnomonicPoint p) := globalSphereSupport_congr_on_open hΩ hheight hp

end
end TightVer401
