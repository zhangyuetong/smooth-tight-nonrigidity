import TightVer401.RuledTransverse

/-! The actual uu strain equation gives zero derivative of the transverse
frame component. It can then be combined with the checked support argument. -/
namespace TightVer401
noncomputable section
set_option backward.isDefEq.respectTransparency false
open OAI.SmoothLocal.Geometry

def ruledFullBending (α χ β : Coord → ℝ) (T E n : ℝ → Ambient) : Coord → Ambient :=
  fun p => ruledBending α β T n p + χ p • E (p 0)

theorem ruled_transverse_strain
    {γ T E n : ℝ → Ambient} {k τ : ℝ → ℝ} {α χ β : Coord → ℝ} {p : Coord}
    (hγ : HasDerivAt γ (T (p 0)) (p 0))
    (hE : HasDerivAt E (-k (p 0) • T (p 0) + τ (p 0) • n (p 0)) (p 0))
    (hT : HasDerivAt T (k (p 0) • E (p 0)) (p 0))
    (hn : HasDerivAt n (-τ (p 0) • E (p 0)) (p 0))
    (hα : DifferentiableAt ℝ α p) (hχ : DifferentiableAt ℝ χ p)
    (hβ : DifferentiableAt ℝ β p)
    (hf : IsOrthonormalFrame (T (p 0)) (E (p 0)) (n (p 0))) :
    strain (ruledMap γ E) (ruledFullBending α χ β T E n) p 1 1 =
      2 * coordPartial 1 χ p := by
  have hdE : DifferentiableAt ℝ (fun q : Coord => E (q 0)) p :=
    (hE.hasFDerivAt.comp p (ContinuousLinearMap.proj (R := ℝ) 0).hasFDerivAt).differentiableAt
  have hdT : DifferentiableAt ℝ (fun q : Coord => T (q 0)) p :=
    (hT.hasFDerivAt.comp p (ContinuousLinearMap.proj (R := ℝ) 0).hasFDerivAt).differentiableAt
  have hdn : DifferentiableAt ℝ (fun q : Coord => n (q 0)) p :=
    (hn.hasFDerivAt.comp p (ContinuousLinearMap.proj (R := ℝ) 0).hasFDerivAt).differentiableAt
  have hdY : DifferentiableAt ℝ (ruledBending α β T n) p :=
    (hα.smul hdT).fun_add (hβ.smul hdn)
  have hdχE : DifferentiableAt ℝ (fun q : Coord => χ q • E (q 0)) p := hχ.smul hdE
  have hpart : coordPartial 1 (ruledFullBending α χ β T E n) p =
      coordPartial 1 (ruledBending α β T n) p + coordPartial 1 χ p • E (p 0) := by
    have hadd : coordPartial 1 (ruledFullBending α χ β T E n) p =
        coordPartial 1 (ruledBending α β T n) p +
          coordPartial 1 (fun q : Coord => χ q • E (q 0)) p := by
      change (fderiv ℝ (fun q => ruledBending α β T n q + χ q • E (q 0)) p)
        (Pi.single 1 1) = _
      rw [fderiv_fun_add hdY hdχE]
      rfl
    rw [hadd, coordPartial_scalar_vector hχ hdE, coordPartial_curve hE 1]
    simp
  rcases hf with ⟨_, hEE, _, hTE, _, hEn⟩
  have hET : inner ℝ (E (p 0)) (T (p 0)) = 0 := by rw [real_inner_comm, hTE]
  have hnE : inner ℝ (n (p 0)) (E (p 0)) = 0 := by rw [real_inner_comm, hEn]
  simp only [strain, hpart, ruled_partial_u hγ hE, ruledBending_partial hα hβ hT hn,
    Pi.single_eq_of_ne (show (0 : Fin 2) ≠ 1 by decide), zero_mul, zero_smul,
    add_zero, inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    hEE, hTE, hEn, hET, hnE, mul_zero, mul_one, zero_add]
  ring

theorem ruled_transverse_projection
    {α χ β : Coord → ℝ} {T E n : ℝ → Ambient} {p : Coord}
    (hf : IsOrthonormalFrame (T (p 0)) (E (p 0)) (n (p 0))) :
    inner ℝ (ruledFullBending α χ β T E n p) (E (p 0)) = χ p := by
  rcases hf with ⟨_, hEE, _, hTE, _, hEn⟩
  have hnE : inner ℝ (n (p 0)) (E (p 0)) = 0 := by rw [real_inner_comm, hEn]
  simp only [ruledFullBending, ruledBending, inner_add_left, real_inner_smul_left,
    hEE, hTE, hnE, mul_zero, mul_one, add_zero, zero_add]

theorem ruled_transverse_support_subset
    {α χ β : Coord → ℝ} {T E n : ℝ → Ambient}
    (hf : ∀ p : Coord, IsOrthonormalFrame (T (p 0)) (E (p 0)) (n (p 0))) :
    tsupport χ ⊆ tsupport (ruledFullBending α χ β T E n) := by
  apply closure_mono
  intro p hp
  change ruledFullBending α χ β T E n p ≠ 0
  intro hz
  have h := ruled_transverse_projection (α := α) (χ := χ) (β := β) (hf p)
  rw [hz, inner_zero_left] at h
  exact hp h.symm

theorem supported_ruled_transverse_component_zero
    {γ T E n : ℝ → Ambient} {k τ : ℝ → ℝ} {α χ β : Coord → ℝ}
    {b lower : ℝ} (hlower : 0 < lower) (hband : lower < b)
    (hγ : ∀ s, HasDerivAt γ (T s) s)
    (hE : ∀ s, HasDerivAt E (-k s • T s + τ s • n s) s)
    (hT : ∀ s, HasDerivAt T (k s • E s) s)
    (hn : ∀ s, HasDerivAt n (-τ s • E s) s)
    (hα : ∀ p : Coord, p 1 ∈ Set.Ioo 0 b → DifferentiableAt ℝ α p)
    (hχ : ∀ p : Coord, p 1 ∈ Set.Ioo 0 b → DifferentiableAt ℝ χ p)
    (hβ : ∀ p : Coord, p 1 ∈ Set.Ioo 0 b → DifferentiableAt ℝ β p)
    (hf : ∀ p : Coord, IsOrthonormalFrame (T (p 0)) (E (p 0)) (n (p 0)))
    (hstrain : ∀ p : Coord, p 1 ∈ Set.Ioo 0 b →
      strain (ruledMap γ E) (ruledFullBending α χ β T E n) p 1 1 = 0)
    (hsupp : ∀ p ∈ tsupport (ruledFullBending α χ β T E n), lower ≤ p 1)
    (s u : ℝ) (hu : u ∈ Set.Ioo 0 b) : χ (![s, u] : Coord) = 0 := by
  apply transverse_component_zero_of_support hlower hband hχ _ _ s u hu
  · intro p hp
    have he := ruled_transverse_strain (hγ (p 0)) (hE (p 0)) (hT (p 0))
      (hn (p 0)) (hα p hp) (hχ p hp) (hβ p hp) (hf p)
    rw [hstrain p hp] at he
    linarith
  · intro p hp
    exact hsupp p (ruled_transverse_support_subset hf hp)

end
end TightVer401
