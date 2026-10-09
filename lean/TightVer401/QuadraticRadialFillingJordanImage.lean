import TightVer401.QuadraticRadialFillingJordanImageModel
import TightVer401.QuadraticRadialFillingGradientLocalTrace
import TightVer401.QuadraticRadialFillingGradientWinding
import TightVer401.QuadraticRadialFillingCircleLifts
import TightVer401.QuadraticRadialFillingLocalOrder
import TightVer401.QuadraticRadialFillingLiftMultiplicity
import TightVer401.QuadraticRadialFillingBoundaryTraceInjection

/-! Multiplicity one from an ordinary Jordan image and an actual unit turn.
Both real lifts, both integer deck periods and global order are constructed. -/
namespace TightVer401
noncomputable section
open Set Function
open scoped ContDiff Topology

theorem quadraticRadialFillingJordanImage_injOn_of_direction_lift
    {γ : ℝ → ℂ} {φ : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hγ : Continuous γ) (hper : Function.Periodic γ L)
    (hlocal : IsLocallyInjective γ)
    (hJ : Schoenflies.IsJordanCurve (range (jordanComplexCoordinates.symm ∘ γ)))
    (hne : ∀ t, γ t ≠ 0) (hφ : Continuous φ)
    (hproj : ∀ t, complexCircleDirection (γ t) = Circle.exp (φ t))
    (hturn : φ L = φ 0 + 2 * Real.pi) : InjOn γ (Ico 0 L) := by
  obtain ⟨Γ,hΓ⟩ := quadraticRadialFillingJordanImage_exists_filling hJ
  have hmem (t : ℝ) : Γ.symm (γ t) ∈ Metric.sphere (0 : ℂ) 1 := by
    have ht : γ t ∈ Γ '' Metric.sphere (0 : ℂ) 1 := hΓ ▸ mem_range_self t
    obtain ⟨z,hz,he⟩ := ht
    simpa only [← he, Homeomorph.symm_apply_apply] using hz
  let c : ℝ → Circle := fun t => ⟨Γ.symm (γ t), hmem t⟩
  have hc : Continuous c := (Γ.symm.continuous.comp hγ).subtype_mk _
  obtain ⟨u,hu,hup⟩ := quadraticRadialFillingCircle_exists_real_lift hc
  have hfactor (t : ℝ) : γ t = Γ (Circle.exp (u t) : ℂ) := by
    rw [hup t]
    exact (Γ.apply_symm_apply (γ t)).symm
  have hcp : Function.Periodic c L := by
    intro t
    apply Subtype.ext
    change Γ.symm (γ (t + L)) = Γ.symm (γ t)
    rw [hper t]
  obtain ⟨k,hk⟩ := quadraticRadialFillingCircle_lift_integer_deck hu hup hcp
  have hulocal : IsLocallyInjective u := by
    intro t
    obtain ⟨W,hW,htW,hiW⟩ := hlocal t
    refine ⟨W,hW,htW,?_⟩
    intro s hs v hv he
    apply hiW hs hv
    rw [hfactor s, hfactor v, he]
  have hmono := quadraticRadialFilling_real_strictMono_or_strictAnti hu hulocal
  have hΓne (s : ℝ) : Γ (Circle.exp s : ℂ) ≠ 0 := by
    have hmem' : Γ (Circle.exp s : ℂ) ∈ range γ := by
      rw [hΓ]
      exact ⟨(Circle.exp s : ℂ), (Circle.exp s).property, rfl⟩
    obtain ⟨t,ht⟩ := hmem'
    exact ht ▸ hne t
  let a : ℝ → Circle := fun s => complexCircleDirection (Γ (Circle.exp s : ℂ))
  have ha : Continuous a := by
    apply continuous_iff_continuousAt.mpr
    intro s
    change ContinuousAt
      (fun t : ℝ => complexCircleDirection (Γ (Circle.exp t : ℂ))) s
    exact (complexCircleDirection_continuousOn.continuousAt
      (isOpen_ne_fun continuous_id continuous_const |>.mem_nhds (hΓne s))).comp
      (f := fun t : ℝ => Γ (Circle.exp t : ℂ))
      (Γ.continuous.comp (continuous_subtype_val.comp Circle.exp.continuous)).continuousAt
  obtain ⟨D,hD,hDp⟩ := quadraticRadialFillingCircle_exists_real_lift ha
  have hap : Function.Periodic a (2 * Real.pi) := by
    intro s
    exact congrArg (fun z : Circle => complexCircleDirection (Γ (z : ℂ)))
      (Circle.periodic_exp s)
  obtain ⟨d,hd⟩ := quadraticRadialFillingCircle_lift_integer_deck hD hDp hap
  have hsame (t : ℝ) : Circle.exp (φ t) = Circle.exp (D (u t)) := by
    rw [hDp]
    change Circle.exp (φ t) = complexCircleDirection (Γ (Circle.exp (u t) : ℂ))
    rw [← hfactor t, hproj t]
  obtain ⟨j,hj⟩ := Circle.exp_eq_exp.mp (hsame 0)
  have he : Circle.exp ∘ φ =
      Circle.exp ∘ (fun t => D (u t) + (j : ℝ) * (2 * Real.pi)) := by
    funext t
    simpa only [Function.comp_apply, Circle.exp_add,
      Circle.exp_int_mul_two_pi, mul_one] using hsame t
  have heq := Circle.isCoveringMap_exp.eq_of_comp_eq hφ
    ((hD.comp hu).add continuous_const) he 0 hj
  apply quadraticRadialFilling_trace_injOn_of_lift_composition hL hmono
    (fun t => by simpa only [mul_comm] using hk t)
    (fun s => by simpa only [mul_comm] using hd s)
    (fun t => congrFun heq t) hturn
    (Γ.injective.comp Subtype.val_injective) hfactor

theorem quadraticRadialFillingGradient_injOn_of_jordan_image
    {F : OAI.SmoothLocal.Geometry.Coord → ℝ} {R : ℝ}
    {U : Set OAI.SmoothLocal.Geometry.Coord}
    (hR : 0 < R) (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (hCircleU : {x | planarRadius x = R} ⊆ U)
    (hdet : ∀ x, planarRadius x = R → (planarHessian F x).det < 0)
    (hpos : ∀ t, 0 < quadraticRadialFillingGradientTrace F R t ⬝ᵥ
      ![Real.cos t,Real.sin t])
    (hJ : Schoenflies.IsJordanCurve (range (jordanComplexCoordinates.symm ∘
      quadraticRadialFillingGradientComplexTrace F R))) :
    InjOn (planarGradient F) (quadraticRadialFillingRadiusLevel R) := by
  letI : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
  have hinj := quadraticRadialFillingJordanImage_injOn_of_direction_lift
    Real.two_pi_pos
    (quadraticRadialFillingGradientComplexTrace_contDiff hR hU hF hCircleU).continuous
    (quadraticRadialFillingGradientComplexTrace_periodic F R)
    (quadraticRadialFillingGradientComplexTrace_locally_injective hR hU hF hCircleU hdet)
    hJ (quadraticRadialFillingGradientComplexTrace_ne_zero hpos)
    (quadraticRadialFillingGradientDirectionLift_continuous hR hU hF hCircleU hpos)
    (quadraticRadialFillingGradientDirectionLift_projects hpos)
    (quadraticRadialFillingGradientDirectionLift_turn F R)
  have hi : InjOn (quadraticRadialFillingGradientTrace F R) (Ico 0 (2 * Real.pi)) := by
    intro s hs t ht he
    exact hinj hs ht (congrArg angularDescentComplex he)
  exact quadraticRadialFillingGradient_injOn_of_trace_lift_injective hR
    (periodicComplexCurve_lift_injective (quadraticRadialFillingGradientTrace_periodic F R) hi)

end
end TightVer401
