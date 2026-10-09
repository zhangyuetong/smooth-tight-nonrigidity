import TightVer401.MetricBranching
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-! Disjoint nonzero modes determine every coefficient from the actual map.
This proves separation of parametrized maps; image noncongruence additionally
requires the marked region and intrinsic-isometry rigidity arguments. -/
namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped BigOperators

def signedSeries {M : Type*} (Y : ℕ → M → Ambient) (a ε : ℕ → ℝ) (p : M) : Ambient :=
  ∑' k, (ε k * a k) • Y k p

theorem signedSeries_at_nonzero_mode
    {M : Type*} [TopologicalSpace M] {Y : ℕ → M → Ambient}
    (hdisj : ∀ k l, k ≠ l → Disjoint (tsupport (Y k)) (tsupport (Y l)))
    (a ε : ℕ → ℝ) {k : ℕ} {p : M} (hp : Y k p ≠ 0) :
    signedSeries Y a ε p = (ε k * a k) • Y k p := by
  have hk : p ∈ tsupport (Y k) := subset_closure hp
  apply tsum_eq_single k
  intro l hl
  have hn : p ∉ tsupport (Y l) := fun h =>
    Set.disjoint_left.mp (hdisj k l hl.symm) hk h
  rw [image_eq_zero_of_notMem_tsupport hn, smul_zero]

theorem signedSeries_coefficients_injective
    {M : Type*} [TopologicalSpace M] {Y : ℕ → M → Ambient}
    (hY : ∀ k, Y k ≠ 0)
    (hdisj : ∀ k l, k ≠ l → Disjoint (tsupport (Y k)) (tsupport (Y l)))
    (a : ℕ → ℝ) (ha : ∀ k, a k ≠ 0) (X : M → Ambient) :
    Function.Injective (fun ε : ℕ → ℝ => X + signedSeries Y a ε) := by
  intro ε δ h
  funext k
  have hex : ∃ p, Y k p ≠ 0 := by
    by_contra! hn
    apply hY k
    funext p
    exact hn p
  obtain ⟨p, hp⟩ := hex
  have he := congrFun h p
  simp only [Pi.add_apply] at he
  rw [signedSeries_at_nonzero_mode hdisj a ε hp,
    signedSeries_at_nonzero_mode hdisj a δ hp] at he
  have hc : ε k * a k = δ k * a k := smul_left_injective ℝ hp (add_left_cancel he)
  exact mul_right_cancel₀ (ha k) hc

end
end TightVer401
