import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.SeparatedMap
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Order.Real
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Tactic.Linarith

/-! A continuous locally injective real lift has one global order orientation. -/
namespace TightVer401
open Set Filter Function
open scoped Topology

private theorem quadraticRadialFilling_real_not_local_max
    {f : ℝ → ℝ} (hf : Continuous f) (hi : IsLocallyInjective f) (a : ℝ) :
    ¬ IsLocalMax f a := by
  intro hmax
  obtain ⟨U, hU, haU, hUi⟩ := hi a
  have hN : U ∩ {z | f z ≤ f a} ∈ 𝓝 a :=
    inter_mem (hU.mem_nhds haU) hmax
  obtain ⟨l, u, ha, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hN
  have hmono := hf.continuousOn.strictMonoOn_of_injOn_Ioo
    (lt_trans ha.1 ha.2) (hUi.mono (fun z hz => (hsub hz).1))
  rcases hmono with hmono | hanti
  · obtain ⟨z, haz, hzu⟩ := exists_between ha.2
    have hz : z ∈ Ioo l u := ⟨lt_trans ha.1 haz, hzu⟩
    exact (not_lt_of_ge (hsub hz).2) (hmono ha hz haz)
  · obtain ⟨z, hlz, hza⟩ := exists_between ha.1
    have hz : z ∈ Ioo l u := ⟨hlz, lt_trans hza ha.2⟩
    exact (not_lt_of_ge (hsub hz).2) (hanti hz ha hza)

private theorem quadraticRadialFilling_real_not_local_min
    {f : ℝ → ℝ} (hf : Continuous f) (hi : IsLocallyInjective f) (a : ℝ) :
    ¬ IsLocalMin f a := by
  intro hmin
  have hneg : IsLocallyInjective (fun z => -f z) :=
    hi.comp_left (fun _ _ h => neg_injective h)
  exact quadraticRadialFilling_real_not_local_max hf.neg hneg a hmin.neg

private theorem quadraticRadialFilling_real_no_repeated_endpoints
    {f : ℝ → ℝ} (hf : Continuous f) (hi : IsLocallyInjective f)
    {x y : ℝ} (hxy : x < y) (heq : f x = f y) : False := by
  have hedge : ∀ z ∈ Icc x y \ Ioo x y, f z = f x := by
    intro z hz
    by_cases hxz : x < z
    · have hzy : ¬ z < y := fun h => hz.2 ⟨hxz, h⟩
      have hzy' : z = y := by have := hz.1.2; linarith
      rw [hzy', ← heq]
    · have hzx : z = x := by have := hz.1.1; linarith
      rw [hzx]
  have hconst : ∀ z ∈ Icc x y, f z = f x := by
    intro z hz
    rcases lt_trichotomy (f z) (f x) with hlt | he | hgt
    · obtain ⟨a, _, hmin⟩ := isCompact_Icc.exists_isLocalMin_mem_open
        Ioo_subset_Icc_self hf.continuousOn hz
        (fun v hv => by rw [hedge v hv]; exact hlt) isOpen_Ioo
      exact False.elim (quadraticRadialFilling_real_not_local_min hf hi a hmin)
    · exact he
    · obtain ⟨a, _, hmax⟩ := isCompact_Icc.exists_isLocalMax_mem_open
        Ioo_subset_Icc_self hf.continuousOn hz
        (fun v hv => by rw [hedge v hv]; exact hgt) isOpen_Ioo
      exact False.elim (quadraticRadialFilling_real_not_local_max hf hi a hmax)
  obtain ⟨U, hU, hxU, hUi⟩ := hi x
  obtain ⟨l, u, hx, hsub⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hU.mem_nhds hxU)
  obtain ⟨z, hxz, hz⟩ := exists_between (lt_min hx.2 hxy)
  have hzu : z < u := lt_of_lt_of_le hz (min_le_left _ _)
  have hzy : z < y := lt_of_lt_of_le hz (min_le_right _ _)
  have hzU : z ∈ U := hsub ⟨lt_trans hx.1 hxz, hzu⟩
  have hzx : z = x := hUi hzU hxU (hconst z ⟨hxz.le, hzy.le⟩)
  exact (ne_of_gt hxz) hzx

/-- Ordinary continuity and local injectivity of an actual real function
already imply global injectivity; no global order premise is supplied. -/
theorem quadraticRadialFilling_real_injective_of_locally_injective
    {f : ℝ → ℝ} (hf : Continuous f) (hi : IsLocallyInjective f) :
    Function.Injective f := by
  intro x y heq
  rcases lt_trichotomy x y with hxy | hxy | hyx
  · exact False.elim (quadraticRadialFilling_real_no_repeated_endpoints hf hi hxy heq)
  · exact hxy
  · exact False.elim (quadraticRadialFilling_real_no_repeated_endpoints hf hi hyx heq.symm)

/-- A continuous locally injective real lift has a single strict order
orientation throughout its actual source. -/
theorem quadraticRadialFilling_real_strictMono_or_strictAnti
    {f : ℝ → ℝ} (hf : Continuous f) (hi : IsLocallyInjective f) :
    StrictMono f ∨ StrictAnti f :=
  hf.strictMono_of_inj (quadraticRadialFilling_real_injective_of_locally_injective hf hi)

end TightVer401
