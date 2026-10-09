import TightVer401.RuledLeaves
import Mathlib.Topology.Order.Compact

/-! Compact sets of complete leaf levels yield compact subannuli. This
topological step applies directly to a compact period circle. -/
namespace TightVer401
noncomputable section
open Set

theorem one_sided_level_in_band {r w c b : ℝ} (hr : 0 < r) (hb : 0 < b)
    (hc : 1 / (r * b) - w < c) : 1 / (r * (c + w)) ∈ Ioo 0 b := by
  exact ruledLeaf_in_band (ρ := fun _ => r) (ω := fun _ => w) (s := 0) hr hb hc

theorem compact_support_of_compact_leaf_levels
    {A V : Type*} [TopologicalSpace A] [CompactSpace A] [T2Space A] [Zero V]
    {ρ W : A → ℝ} {b : ℝ} {K : Set ℝ}
    (hρ : Continuous ρ) (hW : Continuous W) (hρpos : ∀ a, 0 < ρ a) (hb : 0 < b)
    (hK : IsCompact K) (hlevels : ∀ a, ∀ c ∈ K, 1 / (ρ a * b) - W a < c)
    {H : A × Ioo (0 : ℝ) b → V}
    (hzero : ∀ p, 1 / (ρ p.1 * (p.2 : ℝ)) - W p.1 ∉ K → H p = 0) :
    HasCompactSupport H := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hden (p : A × K) : 0 < (p.2 : ℝ) + W p.1 := by
    have hi := one_div_pos.mpr (mul_pos (hρpos p.1) hb)
    have hl := hlevels p.1 p.2 p.2.property
    linarith
  have hband (p : A × K) : 1 / (ρ p.1 * ((p.2 : ℝ) + W p.1)) ∈ Ioo 0 b :=
    one_sided_level_in_band (hρpos p.1) hb (hlevels p.1 p.2 p.2.property)
  let Ψ : A × K → A × Ioo (0 : ℝ) b := fun p =>
    (p.1, ⟨1 / (ρ p.1 * ((p.2 : ℝ) + W p.1)), hband p⟩)
  have hΨ : Continuous Ψ := by
    have hc : Continuous (fun p : A × K => (p.2 : ℝ)) :=
      continuous_subtype_val.comp continuous_snd
    have hd : Continuous (fun p : A × K => ρ p.1 * ((p.2 : ℝ) + W p.1)) :=
      (hρ.comp continuous_fst).mul (hc.add (hW.comp continuous_fst))
    have hu : Continuous (fun p : A × K => 1 / (ρ p.1 * ((p.2 : ℝ) + W p.1))) :=
      continuous_const.div hd (fun p => ne_of_gt (mul_pos (hρpos p.1) (hden p)))
    exact continuous_fst.prodMk (hu.subtype_mk hband)
  have hcompact : IsCompact (range Ψ) := isCompact_range hΨ
  have hs : Function.support H ⊆ range Ψ := by
    intro p hp
    have hv : 1 / (ρ p.1 * (p.2 : ℝ)) - W p.1 ∈ K := by
      by_contra hv
      exact hp (hzero p hv)
    refine ⟨(p.1, ⟨_, hv⟩), ?_⟩
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change 1 / (ρ p.1 * (1 / (ρ p.1 * (p.2 : ℝ)) - W p.1 + W p.1)) = (p.2 : ℝ)
      have hr0 := ne_of_gt (hρpos p.1)
      have hu0 := ne_of_gt p.2.property.1
      field_simp
      <;> ring
  exact hcompact.of_isClosed_subset (isClosed_tsupport H)
    (closure_minimal hs hcompact.isClosed)

end
end TightVer401
