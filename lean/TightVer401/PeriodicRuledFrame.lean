import TightVer401.PeriodicBandProfile

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff Manifold
set_option backward.isDefEq.respectTransparency false

/- Ordinary curve and frame data. No immersion, curvature, characteristic,
   bending or supported-kernel conclusion is included in these inputs. -/
structure PeriodicRuledFrame (L : ℝ) where
  γ : ℝ → Ambient
  T : ℝ → Ambient
  E : ℝ → Ambient
  n : ℝ → Ambient
  k : ℝ → ℝ
  τ : ℝ → ℝ
  smooth_γ : ContDiff ℝ ∞ γ
  smooth_T : ContDiff ℝ ∞ T
  smooth_E : ContDiff ℝ ∞ E
  smooth_n : ContDiff ℝ ∞ n
  smooth_k : ContDiff ℝ ∞ k
  smooth_τ : ContDiff ℝ ∞ τ
  period_γ : Function.Periodic γ L
  period_T : Function.Periodic T L
  period_E : Function.Periodic E L
  period_n : Function.Periodic n L
  period_k : Function.Periodic k L
  period_τ : Function.Periodic τ L
  deriv_γ : ∀ s, HasDerivAt γ (T s) s
  deriv_T : ∀ s, HasDerivAt T (k s • E s) s
  deriv_E : ∀ s, HasDerivAt E (-k s • T s + τ s • n s) s
  deriv_n : ∀ s, HasDerivAt n (-τ s • E s) s
  orthonormal : ∀ s, IsOrthonormalFrame (T s) (E s) (n s)
  torsion_ne_zero : ∀ s, τ s ≠ 0

namespace PeriodicRuledFrame
variable {L b : ℝ} (d : PeriodicRuledFrame L)

def bandMap : AddCircle L × Set.Ioo (0 : ℝ) b → Ambient :=
  fun p => d.period_γ.lift p.1 + (p.2 : ℝ) • d.period_E.lift p.1

def profile {W F : ℝ → ℝ} (hW : Function.Periodic W L) :
    AddCircle L × Set.Ioo (0 : ℝ) b → Ambient :=
  bandProfile d.period_k.lift d.period_τ.lift (ruledRho_periodic d.period_τ).lift
    hW.lift F d.period_T.lift d.period_n.lift

theorem bandMap_contMDiff [Fact (0 < L)] :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Ambient) ∞ (d.bandMap (b := b)) := by
  have hs : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : AddCircle L × Set.Ioo (0 : ℝ) b => p.1) := contMDiff_fst
  have hγ := (periodicLift_contMDiff d.smooth_γ d.period_γ).comp hs
  have hE := (periodicLift_contMDiff d.smooth_E d.period_E).comp hs
  have hu : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : AddCircle L × Set.Ioo (0 : ℝ) b => (p.2 : ℝ)) :=
    (contMDiff_subtype_val (U := bandOpen b)).comp contMDiff_snd
  exact hγ.add (hu.smul hE)

theorem profile_contMDiff [Fact (0 < L)] {W F : ℝ → ℝ}
    (hWL : Function.Periodic W L) (hW : ContDiff ℝ ∞ W) (hF : ContDiff ℝ ∞ F) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Ambient) ∞ (d.profile (b := b) (F := F) hWL) :=
  periodic_bandProfile_contMDiff d.smooth_k d.smooth_τ
    (ruledRho_contDiff d.smooth_τ d.torsion_ne_zero) hW d.smooth_T d.smooth_n
    d.period_k d.period_τ (ruledRho_periodic d.period_τ) hWL d.period_T d.period_n
    (fun s => ne_of_gt (ruledRho_pos (d.torsion_ne_zero s))) hF

end PeriodicRuledFrame
end
end TightVer401
