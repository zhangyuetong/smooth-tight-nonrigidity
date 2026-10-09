import TightVer401.GaussTightnessRegularValues
import TightVer401.SphereCharts

/-! Actual regular height directions for a smooth spherical map on the global
two-dimensional covering space. Both normal signs are handled in the SAME
Sard application; intersection of arbitrary dense sets is never used. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false

private theorem sphereRegular_injective_of_det_ne_zero (L : Coord →L[ℝ] Coord)
    (hL : L.det ≠ 0) : Function.Injective L := by
  apply LinearMap.ker_eq_bot.mp
  by_contra hker
  exact hL (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hker)

/-- The unit directions whose two normal fibers consist entirely of actual
regular points are dense in the round sphere. -/
theorem gaussTightness_dense_both_regular_sphere_directions
    (N : Coord → Ambient) (hN : ContDiff ℝ ∞ N)
    (hunit : ∀ p, ‖N p‖ = 1) :
    Dense {q : RoundSphere | ∀ p, N p = (q : Ambient) ∨ N p = -(q : Ambient) →
      Function.Injective (fderiv ℝ N p)} := by
  classical
  apply dense_iff_inter_open.mpr
  intro U hU hUne
  obtain ⟨q, hq⟩ := hUne
  let w : Ambient := q.val
  have hw : w ≠ 0 := roundSphere_ne_zero q
  have hu : ‖w‖ = 1 := roundSphere_norm q
  let b := sphereHemisphereChart w hw hu
  let V : Set Coord := b ⁻¹' U
  have hb : Continuous b := by
    exact (sphereHemispherePoint_contMDiff w hw hu).continuous
  have hV : IsOpen V := hU.preimage hb
  have hb0 : b 0 = q := by
    apply Subtype.ext
    exact sphereHemisphere_zero w hw hu
  have hVne : V.Nonempty := ⟨0, by change b 0 ∈ U; rwa [hb0]⟩
  let Ns : Bool → Coord → Ambient := fun i => if i then (fun p => -N p) else N
  have hNs (i : Bool) : ContDiff ℝ ∞ (Ns i) := by
    cases i <;> simp only [Ns, Bool.false_eq_true, ↓reduceIte] <;> first | exact hN | exact hN.neg
  let f : Bool → Coord → Coord := fun i p => sphereHemisphereInverse w hw (Ns i p)
  let s : Bool → Set Coord := fun i => {p | 0 < inner ℝ w (Ns i p)}
  have hf : ∀ i p, p ∈ s i → DifferentiableAt ℝ (f i) p := by
    intro i p hp
    exact ((sphereHemisphereInverse_contDiffAt w hw hp).comp p
      (hNs i).contDiffAt).differentiableAt (by simp)
  have hdense := gaussTightness_dense_regular_values (volume : Measure Coord) f s hf
  obtain ⟨z, hzgood, hzV⟩ := hdense.exists_mem_open hV hVne
  refine ⟨b z, hzV, ?_⟩
  intro p hp
  obtain ⟨i, hip⟩ : ∃ i : Bool, Ns i p = (b z : Ambient) := by
    rcases hp with hp | hp
    · exact ⟨false, by simpa [Ns] using hp⟩
    · exact ⟨true, by simp only [Ns, ↓reduceIte, hp, neg_neg]⟩
  have hpos : p ∈ s i := by
    change 0 < inner ℝ w (Ns i p)
    rw [hip]
    exact sphereHemisphere_inner_pos w hw hu z
  have hfp : f i p = z := by
    change sphereHemisphereInverse w hw (Ns i p) = z
    rw [hip]
    exact sphereHemisphere_left_inverse w hw hu z
  have hiF : Function.Injective (fderiv ℝ (f i) p) :=
    sphereRegular_injective_of_det_ne_zero _ (hzgood i p hpos hfp)
  have hd : fderiv ℝ (f i) p =
      (fderiv ℝ (sphereHemisphereInverse w hw) (Ns i p)).comp
        (fderiv ℝ (Ns i) p) := by
    exact fderiv_comp p
      ((sphereHemisphereInverse_contDiffAt w hw hpos).differentiableAt (by simp))
      ((hNs i).differentiable (by simp) p)
  have hiNs : Function.Injective (fderiv ℝ (Ns i) p) := by
    intro v u hvu
    apply hiF
    rw [hd]
    simp only [ContinuousLinearMap.comp_apply, hvu]
  intro v u hvu
  apply hiNs
  cases i with
  | false => simpa only [Ns, Bool.false_eq_true, ↓reduceIte] using hvu
  | true =>
    change fderiv ℝ (fun p => -N p) p v = fderiv ℝ (fun p => -N p) p u
    rw [fderiv_fun_neg]
    simp only [ContinuousLinearMap.neg_apply, hvu]

end
end TightVer401
