import TightVer401.RuledIntegratingFactor

/-! Actual complete leaves when a periodic primitive exists. The band
inequality is the one whose maximum defines c_b in the manuscript. -/
namespace TightVer401
noncomputable section
set_option backward.isDefEq.respectTransparency false

def ruledLeaf (ρ ω : ℝ → ℝ) (c : ℝ) : ℝ → ℝ :=
  fun s => 1 / (ρ s * (c + ω s))

theorem ruledLeaf_first_integral {ρ ω : ℝ → ℝ} {c s : ℝ}
    (hρ : ρ s ≠ 0) (hc : c + ω s ≠ 0) :
    1 / (ρ s * ruledLeaf ρ ω c s) - ω s = c := by
  dsimp only [ruledLeaf]
  field_simp
  <;> ring

theorem ruledLeaf_periodic {ρ ω : ℝ → ℝ} {c L : ℝ}
    (hρ : Function.Periodic ρ L) (hω : Function.Periodic ω L) :
    Function.Periodic (ruledLeaf ρ ω c) L := by
  intro s
  simp only [ruledLeaf, hρ s, hω s]

theorem ruledLeaf_in_band {ρ ω : ℝ → ℝ} {c s b : ℝ}
    (hρ : 0 < ρ s) (hb : 0 < b) (hc : 1 / (ρ s * b) - ω s < c) :
    ruledLeaf ρ ω c s ∈ Set.Ioo 0 b := by
  have hcb : 1 / (ρ s * b) < c + ω s := by linarith
  have hcw : 0 < c + ω s := (one_div_pos.mpr (mul_pos hρ hb)).trans hcb
  constructor
  · exact one_div_pos.mpr (mul_pos hρ hcw)
  · dsimp only [ruledLeaf]
    apply (div_lt_iff₀ (mul_pos hρ hcw)).mpr
    have h := (div_lt_iff₀ (mul_pos hρ hb)).mp hcb
    nlinarith [h]

theorem ruledLeaf_hasDerivAt {ρ ω : ℝ → ℝ} {c s lam D : ℝ}
    (hρ : HasDerivAt ρ (lam * ρ s / 2) s)
    (hω : HasDerivAt ω (D / (2 * ρ s)) s)
    (hρ0 : ρ s ≠ 0) (hc : c + ω s ≠ 0) :
    HasDerivAt (ruledLeaf ρ ω c)
      (-(ruledLeaf ρ ω c s / 2) * (lam + ruledLeaf ρ ω c s * D)) s := by
  have hd := (hρ.mul (hω.const_add c)).inv (mul_ne_zero hρ0 hc)
  convert! hd using 1
  · funext t
    simp only [ruledLeaf, one_div, Pi.inv_apply, Pi.mul_apply]
  · dsimp only [ruledLeaf]
    simp only [Pi.mul_apply]
    field_simp
    <;> ring

end
end TightVer401
