import TightVer401.FermiGraphCloseness
import Mathlib.Analysis.Calculus.ContDiff.Comp

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Matrix
set_option backward.isDefEq.respectTransparency false

def graphTimeInclusion : ℝ →L[ℝ] Coord :=
  ContinuousLinearMap.single ℝ (fun _ : Fin 2 => ℝ) 0

def graphTimeJet (F : Coord → Ambient) (n : ℕ) (p : Coord) :=
  (iteratedFDeriv ℝ n F p).compContinuousLinearMap (fun _ : Fin n => graphTimeInclusion)

theorem graphTimeJet_continuous {F : Coord → Ambient} (hf : ContDiff ℝ ∞ F) (n : ℕ) :
    Continuous (graphTimeJet F n) := by
  exact (ContinuousMultilinearMap.compContinuousLinearMapL
    (F := Ambient) (fun _ : Fin n => graphTimeInclusion)).continuous.comp
      (hf.continuous_iteratedFDeriv (m := n) (by exact_mod_cast le_top))

theorem iteratedFDeriv_parameter_slice {F : Coord → Ambient} (hf : ContDiff ℝ ∞ F)
    (n : ℕ) (δ r : ℝ) :
    iteratedFDeriv ℝ n (fun s : ℝ => F ![s,δ]) r = graphTimeJet F n ![r,δ] := by
  let g : Coord → Ambient := fun q => F (q + ![0,δ])
  have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_id.add contDiff_const)
  have he (s : ℝ) : graphTimeInclusion s + (![0,δ] : Coord) = ![s,δ] := by
    ext i
    fin_cases i <;> simp [graphTimeInclusion]
  have hfun : (fun s : ℝ => F ![s,δ]) = g ∘ graphTimeInclusion := by
    funext s
    exact congrArg F (he s).symm
  rw [hfun,graphTimeInclusion.iteratedFDeriv_comp_right hg r (i := n) (by exact_mod_cast le_top)]
  dsimp only [g]
  rw [iteratedFDeriv_comp_add_right,he r]
  rfl

theorem exists_uniform_parameter_slice_jet_radius {F : Coord → Ambient}
    (hf : ContDiff ℝ ∞ F) (n : ℕ) {P η : ℝ} (hη : 0 < η) :
    ∃ e > 0, ∀ δ : ℝ, |δ| < e → ∀ r ∈ Icc (0 : ℝ) P,
      ‖iteratedFDeriv ℝ n (fun s : ℝ => F ![s,δ]) r -
        iteratedFDeriv ℝ n (fun s : ℝ => F ![s,0]) r‖ < η := by
  have hparam : ContDiff ℝ ∞ (fun p : Coord => (![p 0,0] : Coord)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · exact contDiff_apply ℝ ℝ 0
    · exact contDiff_const
  let U : Set Coord := {p | ‖graphTimeJet F n p - graphTimeJet F n ![p 0,0]‖ < η}
  have hU : IsOpen U := isOpen_lt
    (((graphTimeJet_continuous hf n).sub
      ((graphTimeJet_continuous hf n).comp hparam.continuous)).norm) continuous_const
  have hs : ∀ r ∈ Icc (0 : ℝ) P, (![r,0] : Coord) ∈ U := by
    intro r hr
    simpa only [U,mem_setOf_eq,Matrix.cons_val_zero,sub_self,norm_zero] using hη
  obtain ⟨e,he,hbound⟩ := exitGraphCurve_uniform_domain (v := fun _ => (1 : ℝ))
    contDiff_const hU hs
  refine ⟨e,he,fun δ hδ r hr => ?_⟩
  rw [iteratedFDeriv_parameter_slice hf,iteratedFDeriv_parameter_slice hf]
  simpa only [U,exitGraphCurve,mem_setOf_eq,mul_one,Matrix.cons_val_zero] using
    hbound r hr δ hδ.le

def fermiGraphParameter (ζ : ℝ → Ambient) (v : ℝ → ℝ) (p : Coord) : Ambient :=
  fermiNormalMap ζ ![p 0,p 1 * v (p 0)]

theorem fermiGraphParameter_contDiff {ζ : ℝ → Ambient} {v : ℝ → ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (hv : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (fermiGraphParameter ζ v) := by
  apply (fermiNormalMap_contDiff hζ).comp
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_apply ℝ ℝ 0
  · exact (contDiff_apply ℝ ℝ 1).mul (hv.comp (contDiff_apply ℝ ℝ 0))

theorem fermiGraph_uniform_smooth_convergence {ζ : ℝ → Ambient} {v : ℝ → ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (hv : ContDiff ℝ ∞ v) (n : ℕ) {P η : ℝ} (hη : 0 < η) :
    ∃ e > 0, ∀ δ : ℝ, |δ| < e → ∀ r ∈ Icc (0 : ℝ) P,
      ‖iteratedFDeriv ℝ n (fun s : ℝ => fermiNormalMap ζ (exitGraphCurve v δ s)) r -
        iteratedFDeriv ℝ n ζ r‖ < η := by
  have hbase : (fun s : ℝ => fermiGraphParameter ζ v ![s,0]) = ζ := by
    funext s
    simp [fermiGraphParameter,fermiNormalMap]
  obtain ⟨e,he,hbound⟩ := exists_uniform_parameter_slice_jet_radius
    (fermiGraphParameter_contDiff hζ hv) n (P := P) hη
  refine ⟨e,he,fun δ hδ r hr => ?_⟩
  have hb := hbound δ hδ r hr
  rw [hbase] at hb
  exact hb

end
end TightVer401

