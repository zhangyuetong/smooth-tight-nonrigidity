import TightVer401.SeamNormalTube
import TightVer401.SeamPeriodicity
import TightVer401.SeamCoordinateInverse

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

theorem seamNormalCoordinates_periodic {γ : ℝ → ℂ} {L : ℝ}
    (hL : Function.Periodic γ L) (p : Coord) :
    seamNormalCoordinates γ (smoothingSeamShift L p)=seamNormalCoordinates γ p := by
  change seamComplexCoord (γ (p 0+L)+p 1 • (Complex.I*deriv γ (p 0+L)))=
    seamComplexCoord (γ (p 0)+p 1 • (Complex.I*deriv γ (p 0)))
  rw [hL,seam_complex_deriv_periodic hL]

/-- A closed embedded regular seam has an actual embedded normal tube whose
actual planar Jacobian is regular throughout the tube. -/
theorem seamNormalNative_exists_regular_embedded_strip {L : ℝ} [hLpos : Fact (0 < L)]
    {γ : ℝ → ℂ} (hγ : ContDiff ℝ ∞ γ) (hL : Function.Periodic γ L)
    (hreg : ∀ s, deriv γ s ≠ 0) (hi : Function.Injective hL.lift) :
    ∃ r > 0, InjOn (seamNormalNative γ hL) (univ ×ˢ Icc (-r) r) ∧
      Topology.IsEmbedding (fun p : ↥((univ : Set (AddCircle L)) ×ˢ Ioo (-r) r) =>
        seamNormalNative γ hL p) ∧
      ∀ s t : ℝ, |t| ≤ r → (seamCoordinateJacobian (seamNormalCoordinates γ) (![s,t])).det ≠ 0 := by
  obtain ⟨r₁,hr₁,hInj,hEmb⟩ := seamNormalNative_exists_embedded_strip hγ hL hreg hi
  obtain ⟨r₂,hr₂,hJ⟩ := seamCoordinateJacobian_periodic_regular_collar
    (seamNormalCoordinates_contDiff hγ) hLpos.out (seamNormalCoordinates_periodic hL)
    (fun s => seamNormalCoordinates_regular hγ s (hreg s))
  let r := min r₁ r₂
  have hr : 0 < r := lt_min hr₁ hr₂
  have hsmallClosed : (univ ×ˢ Icc (-r) r : Set (AddCircle L × ℝ)) ⊆ univ ×ˢ Icc (-r₁) r₁ := by
    intro p hp
    refine ⟨hp.1,?_⟩
    exact ⟨(neg_le_neg (min_le_left _ _)).trans hp.2.1,hp.2.2.trans (min_le_left _ _)⟩
  have hsmallOpen : (univ ×ˢ Ioo (-r) r : Set (AddCircle L × ℝ)) ⊆ univ ×ˢ Ioo (-r₁) r₁ := by
    intro p hp
    refine ⟨hp.1,?_⟩
    exact ⟨(neg_le_neg (min_le_left _ _)).trans_lt hp.2.1,hp.2.2.trans_le (min_le_left _ _)⟩
  exact ⟨r,hr,hInj.mono hsmallClosed,hEmb.comp (Topology.IsEmbedding.inclusion hsmallOpen),
    fun s t ht => hJ s t (ht.trans (min_le_right _ _))⟩

end
end TightVer401
