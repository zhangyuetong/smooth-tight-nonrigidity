import TightVer401.TransportWeightPDE

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false

def ruledPotential (k τ : ℝ → ℝ) (α β : Coord → ℝ) : Coord → ℝ :=
  fun p => (1 - k (p 0) * p 1) * α p + τ (p 0) * p 1 * β p

theorem ruledPotential_differentiableAt {k τ : ℝ → ℝ} {α β : Coord → ℝ} {p : Coord}
    (hk : DifferentiableAt ℝ k (p 0)) (hτ : DifferentiableAt ℝ τ (p 0))
    (hα : DifferentiableAt ℝ α p) (hβ : DifferentiableAt ℝ β p) :
    DifferentiableAt ℝ (ruledPotential k τ α β) p := by
  have hs : DifferentiableAt ℝ (fun q : Coord => q 0) p :=
    ((ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)).hasFDerivAt (x := p)).differentiableAt
  have hu : DifferentiableAt ℝ (fun q : Coord => q 1) p :=
    ((ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2)).hasFDerivAt (x := p)).differentiableAt
  exact (((differentiableAt_const 1).sub ((hk.comp p hs).mul hu)).mul hα).add
    (((hτ.comp p hs).mul hu).mul hβ)

theorem ruledPotential_partial {k τ : ℝ → ℝ} {α β : Coord → ℝ} {p : Coord} {ks τs : ℝ}
    (hk : HasDerivAt k ks (p 0)) (hτ : HasDerivAt τ τs (p 0))
    (hα : DifferentiableAt ℝ α p) (hβ : DifferentiableAt ℝ β p) (i : Fin 2) :
    coordPartial i (ruledPotential k τ α β) p =
      (1 - k (p 0) * p 1) * coordPartial i α p + τ (p 0) * p 1 * coordPartial i β p +
      (Pi.single i (1 : ℝ) : Coord) 0 * (-ks * p 1 * α p + τs * p 1 * β p) +
      (Pi.single i (1 : ℝ) : Coord) 1 * (-k (p 0) * α p + τ (p 0) * β p) := by
  have hkc : DifferentiableAt ℝ (fun q : Coord => k (q 0)) p :=
    (hk.hasFDerivAt.comp p (ContinuousLinearMap.proj (R := ℝ) 0).hasFDerivAt).differentiableAt
  have hτc : DifferentiableAt ℝ (fun q : Coord => τ (q 0)) p :=
    (hτ.hasFDerivAt.comp p (ContinuousLinearMap.proj (R := ℝ) 0).hasFDerivAt).differentiableAt
  have hu : DifferentiableAt ℝ (fun q : Coord => q 1) p :=
    ((ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2)).hasFDerivAt (x := p)).differentiableAt
  have hku : DifferentiableAt ℝ (fun q : Coord => k (q 0) * q 1) p := hkc.mul hu
  have hτu : DifferentiableAt ℝ (fun q : Coord => τ (q 0) * q 1) p := hτc.mul hu
  have hA : DifferentiableAt ℝ (fun q : Coord => 1 - k (q 0) * q 1) p :=
    (differentiableAt_const 1).sub hku
  have hAa : DifferentiableAt ℝ (fun q : Coord => (1 - k (q 0) * q 1) * α q) p := hA.mul hα
  have hτb : DifferentiableAt ℝ (fun q : Coord => τ (q 0) * q 1 * β q) p := hτu.mul hβ
  change coordPartial i (fun q => (1 - k (q 0) * q 1) * α q +
    τ (q 0) * q 1 * β q) p = _
  rw [coordPartial_scalar_add hAa hτb,
    coordPartial_scalar_mul hA hα, coordPartial_scalar_mul hτu hβ,
    coordPartial_scalar_sub (differentiableAt_const 1) hku,
    coordPartial_scalar_mul hkc hu, coordPartial_scalar_mul hτc hu,
    coordPartial_curve hk, coordPartial_curve hτ, coordPartial_proj, coordPartial_scalar_const]
  simp only [smul_eq_mul]
  ring

theorem ruledPotential_transport_of_zero_strain
    {γ T E n : ℝ → Ambient} {k τ : ℝ → ℝ} {α β : Coord → ℝ} {p : Coord} {ks τs : ℝ}
    (hγ : HasDerivAt γ (T (p 0)) (p 0))
    (hE : HasDerivAt E (-k (p 0) • T (p 0) + τ (p 0) • n (p 0)) (p 0))
    (hT : HasDerivAt T (k (p 0) • E (p 0)) (p 0))
    (hn : HasDerivAt n (-τ (p 0) • E (p 0)) (p 0))
    (hk : HasDerivAt k ks (p 0)) (hτ : HasDerivAt τ τs (p 0)) (hτ0 : τ (p 0) ≠ 0)
    (hα : DifferentiableAt ℝ α p) (hβ : DifferentiableAt ℝ β p)
    (hf : IsOrthonormalFrame (T (p 0)) (E (p 0)) (n (p 0)))
    (hss : strain (ruledMap γ E) (ruledBending α β T n) p 0 0 = 0)
    (hsu : strain (ruledMap γ E) (ruledBending α β T n) p 0 1 = 0) :
    coordPartial 0 (ruledPotential k τ α β) p -
      p 1 / 2 * (τs / τ (p 0) + p 1 * (ks - k (p 0) * (τs / τ (p 0)))) *
        coordPartial 1 (ruledPotential k τ α β) p =
      -p 1 * (ks - k (p 0) * (τs / τ (p 0))) * ruledPotential k τ α β p := by
  obtain ⟨hs, hm, _⟩ := ruled_strain_equations hγ hE hT hn hα hβ hf
  have hs0 : (1 - k (p 0) * p 1) * coordPartial 0 α p +
      τ (p 0) * p 1 * coordPartial 0 β p = 0 := by rw [hss] at hs; linarith
  have hm0 := hm.symm.trans hsu
  rw [ruledPotential_partial hk hτ hα hβ 0, ruledPotential_partial hk hτ hα hβ 1]
  simp only [Pi.single_eq_same, Pi.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0),
    Pi.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1), zero_mul, one_mul, zero_add, add_zero]
  convert! ruled_transport_from_zero_strain (ks := ks) (τs := τs) hτ0 hs0 hm0 using 1
  · ring

end
end TightVer401
