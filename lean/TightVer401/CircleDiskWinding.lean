import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-! A nonzero actual argument increment forces the origin into a filling disk.
This uses the same actual covering-lift mechanism as OpenAI's CircleLifts. -/
namespace TightVer401
noncomputable section
open Set Function Metric
open scoped Topology

theorem winding_origin_inside {H : ℂ ≃ₜ ℂ} {f : ℝ → ℂ} {φ : ℝ → ℝ}
    {L : ℝ} {A : ℂ → Circle}
    (hA : ContinuousOn A {z | z ≠ 0}) (hf : Continuous f) (hφ : Continuous φ)
    (hboundary : range f = H '' sphere (0 : ℂ) 1)
    (hne : ∀ t, f t ≠ 0) (hp : f L = f 0)
    (hangle : ∀ t, A (f t) = Circle.exp (φ t)) (hturn : φ L ≠ φ 0) :
    (0 : ℂ) ∈ H '' ball (0 : ℂ) 1 := by
  classical
  by_contra hnot
  have hn : 1 ≤ ‖H.symm 0‖ := by
    by_contra hn
    apply hnot
    refine ⟨H.symm 0, ?_, by simp⟩
    simpa only [mem_ball, dist_zero_right] using lt_of_not_ge hn
  have hneq : ‖H.symm 0‖ ≠ 1 := by
    intro he
    have hb : (0 : ℂ) ∈ H '' sphere (0 : ℂ) 1 :=
      ⟨H.symm 0, by simpa only [mem_sphere, dist_zero_right] using he, by simp⟩
    rw [← hboundary] at hb
    obtain ⟨t, ht⟩ := hb
    exact hne t ht
  have hgt : 1 < ‖H.symm 0‖ := lt_of_le_of_ne hn hneq.symm
  let r := (‖H.symm 0‖ + 1) / 2
  have hr : 1 < r := by dsimp [r]; linarith
  have hrn : r < ‖H.symm 0‖ := by dsimp [r]; linarith
  let U : Set ℂ := H '' ball (0 : ℂ) r
  have hU : IsOpen U := H.isOpenMap _ isOpen_ball
  have hUnz : U ⊆ {z | z ≠ 0} := by
    rintro z ⟨w, hw, rfl⟩ he
    have hew : w = H.symm 0 := by simpa using congrArg H.symm he
    have hw' : ‖w‖ < r := by simpa only [mem_ball, dist_zero_right] using hw
    rw [hew] at hw'
    exact (not_lt_of_ge hrn.le) hw'
  have hfU : ∀ t, f t ∈ U := by
    intro t
    have ht : f t ∈ H '' sphere (0 : ℂ) 1 := hboundary ▸ mem_range_self t
    obtain ⟨z, hz, he⟩ := ht
    refine ⟨z, ?_, he⟩
    simp only [mem_ball, dist_zero_right, mem_sphere] at hz ⊢
    simpa only [hz] using hr
  letI : ContractibleSpace (ball (0 : ℂ) r) :=
    (convex_ball (0 : ℂ) r).contractibleSpace (nonempty_ball.mpr (by linarith))
  letI : SimplyConnectedSpace U := H.isSimplyConnected_image.mpr
    (show SimplyConnectedSpace (ball (0 : ℂ) r) from inferInstance)
  letI : LocallyPathConnectedSpace U := hU.locallyPathConnectedSpace
  let F : C(U, Circle) := ⟨fun x => A x, (hA.mono hUnz).domRestrict⟩
  obtain ⟨u, ⟨hu0, hulift⟩, _⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
    F ⟨f 0, hfU 0⟩ (φ 0) (hangle 0).symm
  let c : ℝ → U := fun t => ⟨f t, hfU t⟩
  have hc : Continuous c := hf.subtype_mk _
  have he : Circle.exp ∘ (u ∘ c) = Circle.exp ∘ φ := by
    funext t
    have ht := congrFun hulift (c t)
    exact ht.trans (hangle t)
  have heq : u ∘ c = φ := Circle.isCoveringMap_exp.eq_of_comp_eq
    (u.continuous.comp hc) hφ he 0 hu0
  apply hturn
  rw [← congrFun heq L, ← congrFun heq 0]
  have hcp : c L = c 0 := Subtype.ext hp
  change u (c L) = u (c 0)
  rw [hcp]
end
end TightVer401
