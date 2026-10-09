import TightVer401.QuadraticRadialFillingLargeGradient
import TightVer401.QuadraticFillerCartesianGradientAnnulus
import TightVer401.QuadraticRadialFillingBoundary

/-! Transfer the constructed explicit radial inverse through actual scalar germs.
The final union lemma is an assembly tool, not the pending degree theorem. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

theorem quadraticRadialFilling_inner_gradient_eq {R : ℝ} (hR : 0 < R)
    (M : ℝ) {H : Coord → ℝ}
    (hInner : ∀ x : Coord, 0 < planarRadius x → planarRadius x < R/2 →
      H =ᶠ[𝓝 x] dualRadialQuadraticPotential R M (-M*R^2/2))
    {x : Coord} (hx : x ∈ quadraticFillerCartesianGradientInner R) :
    planarGradient H x = quadraticFillerCartesianGradientRadialMap R M x := by
  rw [quadraticRadialFilling_gradient_eq_of_germ (hInner x hx.1 hx.2),
    ← quadraticFillerCartesian_inner_gradient hR M (fun _ => 0) (fun _ => 0) hx.2]
  exact quadraticFillerCartesianGradient_actual_eq hR M (fun _ => 0) (fun _ => 0) hx

theorem quadraticRadialFilling_inner_gradient_injOn {R M : ℝ}
    (hR : 0 < R) (hM : 0 < M) {H : Coord → ℝ}
    (hInner : ∀ x : Coord, 0 < planarRadius x → planarRadius x < R/2 →
      H =ᶠ[𝓝 x] dualRadialQuadraticPotential R M (-M*R^2/2)) :
    InjOn (planarGradient H) (quadraticFillerCartesianGradientInner R) := by
  intro x hx y hy he
  apply quadraticFillerCartesianGradient_injOn hR hM (fun _ => 0) (fun _ => 0) hx hy
  rw [quadraticFillerCartesianGradient_actual_eq hR M (fun _ => 0) (fun _ => 0) hx,
    quadraticFillerCartesianGradient_actual_eq hR M (fun _ => 0) (fun _ => 0) hy,
    ← quadraticRadialFilling_inner_gradient_eq hR M hInner hx,
    ← quadraticRadialFilling_inner_gradient_eq hR M hInner hy]
  exact he

theorem quadraticRadialFilling_inner_gradient_radius {R M : ℝ}
    (hR : 0 < R) (hM : 0 < M) {H : Coord → ℝ}
    (hInner : ∀ x : Coord, 0 < planarRadius x → planarRadius x < R/2 →
      H =ᶠ[𝓝 x] dualRadialQuadraticPotential R M (-M*R^2/2))
    {x : Coord} (hx : x ∈ quadraticFillerCartesianGradientInner R) :
    planarRadius (planarGradient H x) = M * (R - planarRadius x) := by
  rw [quadraticRadialFilling_inner_gradient_eq hR M hInner hx]
  exact quadraticFillerCartesianGradient_radial_radius hR hM hx

theorem quadraticRadialFilling_inner_subdisk_image {R M ρ : ℝ}
    (hR : 0 < R) (hM : 0 < M) (hρ : 0 < ρ) (hρR : ρ ≤ R/2)
    {H : Coord → ℝ}
    (hInner : ∀ x : Coord, 0 < planarRadius x → planarRadius x < R/2 →
      H =ᶠ[𝓝 x] dualRadialQuadraticPotential R M (-M*R^2/2)) :
    planarGradient H '' {x : Coord | 0 < planarRadius x ∧ planarRadius x < ρ} =
      {y : Coord | M*(R-ρ) < planarRadius y ∧ planarRadius y < M*R} := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    have hxInner : x ∈ quadraticFillerCartesianGradientInner R :=
      ⟨hx.1, hx.2.trans_le hρR⟩
    change M*(R-ρ) < planarRadius (planarGradient H x) ∧
      planarRadius (planarGradient H x) < M*R
    rw [quadraticRadialFilling_inner_gradient_radius hR hM hInner hxInner]
    constructor
    · exact mul_lt_mul_of_pos_left (by linarith [hx.2]) hM
    · exact mul_lt_mul_of_pos_left (by linarith [hx.1]) hM
  · intro hy
    have hyAnn : y ∈ quadraticFillerCartesianGradientAnnulus R M := by
      constructor
      · nlinarith [mul_nonneg hM.le (sub_nonneg.mpr hρR), hy.1]
      · exact hy.2
    let x := quadraticFillerCartesianGradientInverse R M y
    have hxInner : x ∈ quadraticFillerCartesianGradientInner R :=
      quadraticFillerCartesianGradient_inverse_mapsTo hR hM hyAnn
    have hxr : planarRadius x < ρ := by
      rw [quadraticFillerCartesianGradient_inverse_radius hR hM hyAnn]
      have hlower : R-ρ < planarRadius y / M :=
        (lt_div_iff₀ hM).mpr (by simpa only [mul_comm] using hy.1)
      linarith
    refine ⟨x, ⟨hxInner.1,hxr⟩, ?_⟩
    rw [quadraticRadialFilling_inner_gradient_eq hR M hInner hxInner]
    exact quadraticFillerCartesianGradient_right_inverse hR hM hyAnn

/-- A closed-band inverse and its actual radius bound combine with the derived
inner radial inverse. The separate degree construction must supply the band data. -/
theorem quadraticRadialFilling_puncturedDisk_injOn_of_closedBand
    {R M ρ S : ℝ} (hR : 0 < R) (hM : 0 < M) (hρ : 0 < ρ)
    (hρR : ρ ≤ R/2) {H : Coord → ℝ}
    (hInner : ∀ x : Coord, 0 < planarRadius x → planarRadius x < R/2 →
      H =ᶠ[𝓝 x] dualRadialQuadraticPotential R M (-M*R^2/2))
    (hBand : InjOn (planarGradient H) (quadraticRadialFillingClosedAnnulus ρ S))
    (hBound : ∀ x ∈ quadraticRadialFillingClosedAnnulus ρ S,
      planarRadius (planarGradient H x) ≤ M*(R-ρ)) :
    InjOn (planarGradient H) {x : Coord | 0 < planarRadius x ∧ planarRadius x < S} := by
  intro x hx y hy he
  by_cases hxr : planarRadius x < ρ
  · have hxInner : x ∈ quadraticFillerCartesianGradientInner R :=
      ⟨hx.1,hxr.trans_le hρR⟩
    by_cases hyr : planarRadius y < ρ
    · exact quadraticRadialFilling_inner_gradient_injOn hR hM hInner hxInner
        ⟨hy.1,hyr.trans_le hρR⟩ he
    · have hyBand : y ∈ quadraticRadialFillingClosedAnnulus ρ S :=
        ⟨le_of_not_gt hyr,hy.2.le⟩
      have hlarge : M*(R-ρ) < planarRadius (planarGradient H x) := by
        rw [quadraticRadialFilling_inner_gradient_radius hR hM hInner hxInner]
        exact mul_lt_mul_of_pos_left (by linarith) hM
      rw [he] at hlarge
      exact (not_lt_of_ge (hBound y hyBand) hlarge).elim
  · have hxBand : x ∈ quadraticRadialFillingClosedAnnulus ρ S :=
      ⟨le_of_not_gt hxr,hx.2.le⟩
    by_cases hyr : planarRadius y < ρ
    · have hyInner : y ∈ quadraticFillerCartesianGradientInner R :=
        ⟨hy.1,hyr.trans_le hρR⟩
      have hlarge : M*(R-ρ) < planarRadius (planarGradient H y) := by
        rw [quadraticRadialFilling_inner_gradient_radius hR hM hInner hyInner]
        exact mul_lt_mul_of_pos_left (by linarith) hM
      rw [← he] at hlarge
      exact (not_lt_of_ge (hBound x hxBand) hlarge).elim
    · exact hBand hxBand ⟨le_of_not_gt hyr,hy.2.le⟩ he

end
end TightVer401
