import TightVer401.RevolutionEndCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Maps.Proper.Basic

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped Topology ContDiff

 def revolutionEndCircle (q : ℝ → ℝ) (H : ℝ)
    (p : AddCircle (2 * Real.pi) × Ici H) : Ambient :=
  WithLp.toLp 2 ![q p.2.val * Real.Angle.cos p.1,
    q p.2.val * Real.Angle.sin p.1, p.2.val]

 theorem revolutionEndCircle_height (q : ℝ → ℝ) (H : ℝ)
    (p : AddCircle (2 * Real.pi) × Ici H) : revolutionEndCircle q H p 2 = p.2.val := by
  simp [revolutionEndCircle]

 theorem revolutionEndCircle_representative (q : ℝ → ℝ) {H z : ℝ} (hz : H ≤ z) (θ : ℝ) :
    revolutionEndCircle q H ((θ : Real.Angle), ⟨z, hz⟩) =
      revolutionEnd q (![θ, z] : Coord) := by
  ext i
  fin_cases i <;> simp [revolutionEndCircle, revolutionEnd, revolutionRadial, revolutionAxis]

 theorem revolutionEndCircle_continuous {q : ℝ → ℝ} (hq : Continuous q) (H : ℝ) :
    Continuous (revolutionEndCircle q H) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i
  · exact (hq.comp (continuous_subtype_val.comp continuous_snd)).mul
      (Real.Angle.continuous_cos.comp continuous_fst)
  · exact (hq.comp (continuous_subtype_val.comp continuous_snd)).mul
      (Real.Angle.continuous_sin.comp continuous_fst)
  · exact continuous_subtype_val.comp continuous_snd

 theorem revolutionAngle_cos_sin_injective {θ φ : Real.Angle}
    (hc : Real.Angle.cos θ = Real.Angle.cos φ)
    (hs : Real.Angle.sin θ = Real.Angle.sin φ) : θ = φ := by
  induction θ using Real.Angle.induction_on
  induction φ using Real.Angle.induction_on
  exact Real.Angle.cos_sin_inj hc hs

 theorem revolutionEndCircle_injective {q : ℝ → ℝ} {H : ℝ}
    (hpos : ∀ z ∈ Ici H, 0 < q z) : Function.Injective (revolutionEndCircle q H) := by
  intro p s heq
  have hz : p.2.val = s.2.val := by
    simpa only [revolutionEndCircle_height] using congrArg (fun v : Ambient => v 2) heq
  have hq : q p.2.val ≠ 0 := ne_of_gt (hpos _ p.2.property)
  have hc := congrArg (fun v : Ambient => v 0) heq
  have hs := congrArg (fun v : Ambient => v 1) heq
  change q p.2.val * Real.Angle.cos p.1 = q s.2.val * Real.Angle.cos s.1 at hc
  change q p.2.val * Real.Angle.sin p.1 = q s.2.val * Real.Angle.sin s.1 at hs
  rw [← hz] at hc hs
  have ha := revolutionAngle_cos_sin_injective ((mul_left_cancel₀ hq) hc) ((mul_left_cancel₀ hq) hs)
  exact Prod.ext ha (Subtype.ext hz)

 theorem revolutionEndCircle_isProperMap {q : ℝ → ℝ} (hq : Continuous q) (H : ℝ) :
    IsProperMap (revolutionEndCircle q H) := by
  letI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  have hheight : IsProperMap (fun p : AddCircle (2 * Real.pi) × Ici H => p.2.val) :=
    isClosed_Ici.isProperMap_subtypeVal.comp isProperMap_snd_of_compactSpace
  apply isProperMap_of_comp_of_t2 (revolutionEndCircle_continuous hq H)
    (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous
  exact hheight

 theorem revolutionEndCircle_isClosedEmbedding {q : ℝ → ℝ} {H : ℝ}
    (hq : Continuous q) (hpos : ∀ z ∈ Ici H, 0 < q z) :
    Topology.IsClosedEmbedding (revolutionEndCircle q H) := by
  exact Topology.IsClosedEmbedding.isClosedEmbedding_iff_continuous_injective_isClosedMap.mpr
    ⟨revolutionEndCircle_continuous hq H, revolutionEndCircle_injective hpos,
      (revolutionEndCircle_isProperMap hq H).isClosedMap⟩

 theorem revolutionEndCircle_isEmbedding {q : ℝ → ℝ} {H : ℝ}
    (hq : Continuous q) (hpos : ∀ z ∈ Ici H, 0 < q z) :
    Topology.IsEmbedding (revolutionEndCircle q H) :=
  (revolutionEndCircle_isClosedEmbedding hq hpos).isEmbedding

end
end TightVer401

