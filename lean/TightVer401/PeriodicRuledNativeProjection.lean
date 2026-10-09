import TightVer401.PeriodicRuledNativeGauss
import TightVer401.ThinBandRuledHorizontal

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Manifold
set_option backward.isDefEq.respectTransparency false

/-- The actual horizontal projection is smooth on the very same native band. -/
theorem periodicRuledFrame_horizontal_band_contMDiff {L b : ℝ} [Fact (0 < L)]
    (d : PeriodicRuledFrame L) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℂ) ∞
      (corrugatedAmbientHorizontalCLM ∘ d.bandMap (b := b)) :=
  corrugatedAmbientHorizontalCLM.contDiff.contMDiff.comp d.bandMap_contMDiff

/-- A nonhorizontal actual normal makes projection regular at every band point,
not only at its central curve. -/
theorem periodicRuledFrame_horizontal_band_differential_injective {L b : ℝ} [Fact (0 < L)]
    (d : PeriodicRuledFrame L) (p : AddCircle L × Ioo (0 : ℝ) b)
    (hn : d.bandGaussMap p 2 ≠ 0) :
    Function.Injective (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℂ)
      (corrugatedAmbientHorizontalCLM ∘ d.bandMap (b := b)) p) := by
  have hchain : mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℂ)
      (corrugatedAmbientHorizontalCLM ∘ d.bandMap (b := b)) p =
      corrugatedAmbientHorizontalCLM.comp (bandDifferential d.bandMap p) :=
    (corrugatedAmbientHorizontalCLM.hasFDerivAt.hasMFDerivAt.comp p
      ((d.bandMap_contMDiff p).mdifferentiableAt (by simp)).hasMFDerivAt).mfderiv
  intro v w he
  have he' : corrugatedAmbientHorizontalCLM (bandDifferential d.bandMap p v) =
      corrugatedAmbientHorizontalCLM (bandDifferential d.bandMap p w) := by
    exact (congrArg (fun F => F v) hchain).symm.trans
      (he.trans (congrArg (fun F => F w) hchain))
  have hz : corrugatedAmbientHorizontalCLM (bandDifferential d.bandMap p (v - w)) = 0 := by
    rw [map_sub, map_sub, he', sub_self]
  have hzero := corrugatedAmbientHorizontal_plane_zero hz
    (periodicRuledFrame_bandGaussMap_orthogonal d p (v - w)) hn
  apply periodicRuledFrame_bandMap_immersion d p
  exact sub_eq_zero.mp (by simpa only [map_sub] using hzero)

/-- Northern normals give regular projection throughout any chosen band width. -/
theorem periodicRuledFrame_northern_band_projection_regular {L b : ℝ} [Fact (0 < L)]
    (d : PeriodicRuledFrame L)
    (hn : ∀ p : AddCircle L × Ioo (0 : ℝ) b, 0 < d.bandGaussMap p 2) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℂ) ∞
      (corrugatedAmbientHorizontalCLM ∘ d.bandMap (b := b)) ∧
    ∀ p : AddCircle L × Ioo (0 : ℝ) b,
      Function.Injective (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℂ)
        (corrugatedAmbientHorizontalCLM ∘ d.bandMap (b := b)) p) :=
  ⟨periodicRuledFrame_horizontal_band_contMDiff d,
    fun p => periodicRuledFrame_horizontal_band_differential_injective d p (hn p).ne'⟩

end
end TightVer401
