import TightVer401.ParabolicConvexClosure
import TightVer401.ProtectedTorusMapDefinitions

/-! Actual ordinary producer for the coordinator's literal cosine-height torus
assembly. Import only its admission-free definitions; no pending torus gates. -/
namespace TightVer401
noncomputable section
open Set
open scoped ContDiff

/-- Construct the exact protected meridian input, retaining its convex geometry
and asymmetry facts about the very same radius. No torus conclusion is assumed. -/
theorem exists_protectedParabolicMeridianInput_geometry (RN mu h : ℝ)
    (hRN : 0 < RN) (hmu : 0 < mu) (hh : 0 < h) :
    ∃ d : ProtectedParabolicMeridianInput RN mu h,
      (∀ z ∈ Ioo (-h) h, deriv (deriv d.meridian) z < 0) ∧
      StrictConcaveOn ℝ (Icc (-h) h) d.meridian ∧
      d.meridian (-h) = RN ∧ d.meridian h = RN ∧
      ∃ z ∈ Ioo 0 h, d.meridian (-z) ≠ d.meridian z := by
  obtain ⟨r, hc, hs, hn, hconc, hl, hu, hp, ⟨δ, hδ, hgl, hgu⟩, ha⟩ :=
    exists_parabolic_convex_meridian RN mu h hRN hmu hh
  let d : ProtectedParabolicMeridianInput RN mu h :=
    ⟨r, hc, hs, hp, ⟨δ, hδ.1, fun _ hz => hgu hz⟩,
      ⟨δ, hδ.1, fun _ hz => hgl hz⟩⟩
  exact ⟨d, hn, hconc, hl, hu, ha⟩

/-- Ordinary positive constants suffice for the actual assembly input. -/
theorem exists_protectedParabolicMeridianInput (RN mu h : ℝ)
    (hRN : 0 < RN) (hmu : 0 < mu) (hh : 0 < h) :
    Nonempty (ProtectedParabolicMeridianInput RN mu h) := by
  obtain ⟨d, _⟩ := exists_protectedParabolicMeridianInput_geometry RN mu h hRN hmu hh
  exact ⟨d⟩

end
end TightVer401
