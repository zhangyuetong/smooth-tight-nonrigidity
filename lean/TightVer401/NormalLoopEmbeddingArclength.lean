import TightVer401.NormalLoopEmbeddingPeriod
import TightVer401.NormalLoopGlobalArclength

namespace TightVer401
noncomputable section
open Set OAI.ClosedSurfaceR4.PeriodicPrimitive
set_option backward.isDefEq.respectTransparency false

theorem normalLoop_arclength_inverse_mem_Ico {a : ℝ → ℝ} {L s : ℝ}
    (ha : Continuous a) (hapos : ∀ r, 0 < a r) (e : ℝ ≃ₜ ℝ)
    (he : (e : ℝ → ℝ) = rawPrimitive a) (hs : s ∈ Ico 0 (rawPrimitive a L)) :
    e.symm s ∈ Ico 0 L := by
  have hm : StrictMono e := by
    intro x y hxy
    rw [he]
    exact normalLoop_arclength_strictMono ha hapos hxy
  have hz : e 0 = 0 := by rw [he]; simp [rawPrimitive]
  have hL : e L = rawPrimitive a L := congrFun he L
  constructor
  · by_contra h
    have hl := hm (lt_of_not_ge h)
    rw [e.apply_symm_apply, hz] at hl
    linarith [hs.1]
  · by_contra h
    have hl := hm.monotone (le_of_not_gt h)
    rw [hL, e.apply_symm_apply] at hl
    linarith [hs.2]

theorem normalLoop_arclength_reparameterized_injective {E : Type*}
    {c : ℝ → E} {a : ℝ → ℝ} {L : ℝ} (ha : Continuous a) (hapos : ∀ r, 0 < a r)
    (e : ℝ ≃ₜ ℝ) (he : (e : ℝ → ℝ) = rawPrimitive a)
    (hi : Set.InjOn c (Ico 0 L)) : Set.InjOn (c ∘ e.symm) (Ico 0 (rawPrimitive a L)) := by
  intro s hs t ht hst
  apply e.symm.injective
  exact hi (normalLoop_arclength_inverse_mem_Ico ha hapos e he hs)
    (normalLoop_arclength_inverse_mem_Ico ha hapos e he ht) hst

end
end TightVer401
