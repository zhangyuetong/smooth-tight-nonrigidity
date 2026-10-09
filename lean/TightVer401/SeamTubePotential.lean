import TightVer401.SeamNormalTube
import TightVer401.SmoothingCylinderDescent

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

def seamNormalTubePotential {L : ℝ} (γ : ℝ → ℂ) (hL : Function.Periodic γ L)
    (r : ℝ) (H : Coord → ℝ) (hPeriod : ∀ p, H (smoothingSeamShift L p)=H p) : Coord → ℝ :=
  Function.extend
    (fun q : ↥((univ : Set (AddCircle L)) ×ˢ Icc (-r) r) => seamNormalNative γ hL q)
    (fun q => smoothingCylinderPotential L H hPeriod q) (fun _ => 0)

theorem seamNormalNative_coe {L : ℝ} {γ : ℝ → ℂ} (hL : Function.Periodic γ L) (s t : ℝ) :
    seamNormalNative γ hL (periodProjection L s,t)=seamNormalCoordinates γ (![s,t]) := by
  simp only [seamNormalNative,periodicLift_coe]
  rfl

theorem seamNormalTubePotential_native {L : ℝ} {γ : ℝ → ℂ}
    (hL : Function.Periodic γ L) {r : ℝ} (H : Coord → ℝ)
    (hPeriod : ∀ p, H (smoothingSeamShift L p)=H p)
    (hi : InjOn (seamNormalNative γ hL) (univ ×ˢ Icc (-r) r))
    (q : ↥((univ : Set (AddCircle L)) ×ˢ Icc (-r) r)) :
    seamNormalTubePotential γ hL r H hPeriod (seamNormalNative γ hL q)=
      smoothingCylinderPotential L H hPeriod q := by
  have hi' : Function.Injective
      (fun q : ↥((univ : Set (AddCircle L)) ×ˢ Icc (-r) r) => seamNormalNative γ hL q) := by
    intro p q hpq
    exact Subtype.ext (hi p.property q.property hpq)
  exact hi'.extend_apply _ _ q

theorem seamNormalTubePotential_coe {L : ℝ} {γ : ℝ → ℂ}
    (hL : Function.Periodic γ L) {r : ℝ} (H : Coord → ℝ)
    (hPeriod : ∀ p, H (smoothingSeamShift L p)=H p)
    (hi : InjOn (seamNormalNative γ hL) (univ ×ˢ Icc (-r) r))
    (s t : ℝ) (ht : |t| ≤ r) :
    seamNormalTubePotential γ hL r H hPeriod (seamNormalCoordinates γ (![s,t]))=H (![s,t]) := by
  let q : ↥((univ : Set (AddCircle L)) ×ˢ Icc (-r) r) :=
    ⟨(periodProjection L s,t),⟨mem_univ _,abs_le.mp ht⟩⟩
  have he := seamNormalTubePotential_native hL H hPeriod hi q
  change seamNormalTubePotential γ hL r H hPeriod (seamNormalNative γ hL (periodProjection L s,t))=
    smoothingCylinderPotential L H hPeriod (periodProjection L s,t) at he
  rw [seamNormalNative_coe,smoothingCylinderPotential_coe] at he
  exact he

theorem seamNormalTubePotential_chart_eq {L : ℝ} {γ : ℝ → ℂ}
    (hL : Function.Periodic γ L) {r : ℝ} (H : Coord → ℝ)
    (hPeriod : ∀ p, H (smoothingSeamShift L p)=H p)
    (hi : InjOn (seamNormalNative γ hL) (univ ×ˢ Icc (-r) r))
    (e : OpenPartialHomeomorph Coord Coord) (he : (e : Coord → Coord)=seamNormalCoordinates γ)
    (hS : e.source ⊆ {p : Coord | |p 1| < r}) {x : Coord} (hx : x ∈ e.target) :
    seamNormalTubePotential γ hL r H hPeriod x=H (e.symm x) := by
  let p := e.symm x
  have hp : |p 1| < r := hS (e.map_target hx)
  have hc := seamNormalTubePotential_coe hL H hPeriod hi (p 0) (p 1) hp.le
  have hpv : (![p 0,p 1] : Coord)=p := by ext i; fin_cases i <;> rfl
  rw [hpv,← he] at hc
  rw [e.right_inv hx] at hc
  exact hc

end
end TightVer401
