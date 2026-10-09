import TightVer401.PeriodCircleInstances
import TightVer401.PeriodicCircleFunctions
import TightVer401.RuledProfileSupport

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped Manifold ContDiff
set_option backward.isDefEq.respectTransparency false

def bandOpen (b : ℝ) : TopologicalSpace.Opens ℝ := ⟨Ioo 0 b, isOpen_Ioo⟩

instance bandInterval_chartedSpace (b : ℝ) : ChartedSpace ℝ (Ioo (0 : ℝ) b) :=
  inferInstanceAs (ChartedSpace ℝ (bandOpen b))

instance bandInterval_manifold (b : ℝ) : IsManifold 𝓘(ℝ, ℝ) ∞ (Ioo (0 : ℝ) b) :=
  inferInstanceAs (IsManifold 𝓘(ℝ, ℝ) ∞ (bandOpen b))

theorem bandProfile_contMDiff {L b : ℝ} [Fact (0 < L)]
    {k τ ρ W : AddCircle L → ℝ} {T n : AddCircle L → Ambient} {F : ℝ → ℝ}
    (hk : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ k)
    (hτ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ τ)
    (hρ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ ρ)
    (hW : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ W)
    (hT : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Ambient) ∞ T)
    (hn : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Ambient) ∞ n)
    (hρ0 : ∀ a, ρ a ≠ 0) (hF : ContDiff ℝ ∞ F) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Ambient) ∞ (bandProfile k τ ρ W F T n (b := b)) := by
  have hs : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : AddCircle L × Ioo (0 : ℝ) b => p.1) := contMDiff_fst
  have huv : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
      (fun u : Ioo (0 : ℝ) b => (u : ℝ)) :=
    contMDiff_subtype_val (U := bandOpen b)
  have hu : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : AddCircle L × Ioo (0 : ℝ) b => (p.2 : ℝ)) := huv.comp contMDiff_snd
  have hkc := hk.comp hs
  have hτc := hτ.comp hs
  have hρc := hρ.comp hs
  have hWc := hW.comp hs
  have hV : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : AddCircle L × Ioo (0 : ℝ) b => 1 / (ρ p.1 * (p.2 : ℝ)) - W p.1) :=
    (contMDiff_const.div₀ (hρc.mul hu)
      (fun p => mul_ne_zero (hρ0 _) (ne_of_gt p.2.property.1))).sub hWc
  have hd : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : AddCircle L × Ioo (0 : ℝ) b => 2 * ρ p.1) := contMDiff_const.mul hρc
  have hd0 (p : AddCircle L × Ioo (0 : ℝ) b) : 2 * ρ p.1 ≠ 0 :=
    mul_ne_zero (by norm_num) (hρ0 _)
  have hA := (hτc.mul hu).div₀ hd hd0
  have hB := ((contMDiff_const (c := (1 : ℝ))).sub (hkc.mul hu)).div₀ hd hd0
  have hFc := hF.contMDiff.comp hV
  have hF'c := (contDiff_infty_iff_deriv.mp hF).2.contMDiff.comp hV
  exact ((hA.mul hF'c).smul (hT.comp hs)).add
    (((hu.mul hFc).sub (hB.mul hF'c)).smul (hn.comp hs))

end
end TightVer401
