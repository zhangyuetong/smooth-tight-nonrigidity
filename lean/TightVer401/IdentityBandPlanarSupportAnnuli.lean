import TightVer401.IdentityBandPlanarSupportBand

/-! Explicit topological annuli and the actual gradient diffeomorphism
extracted from the constructed corrected-band support witness. -/
open scoped Manifold
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

/-- Both actual open images are homeomorphic to the original native cylinder,
and the actual gradient is a smooth bijection with smooth inverse between them. -/
theorem identityBandPlanarSupport_open_annuli {T w : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T) (hcore : IdentityBandPlanarSupportAnnulus d w) :
    ∃ U V : Set Coord, ∃ G : Coord → ℝ,
      IsOpen U ∧ IsOpen V ∧
      Nonempty ((AddCircle T × Ioo (0 : ℝ) w) ≃ₜ U) ∧
      Nonempty ((AddCircle T × Ioo (0 : ℝ) w) ≃ₜ V) ∧
      ContDiffOn ℝ ∞ G U ∧ Set.BijOn (planarGradient G) U V ∧
      ∃ g : OpenPartialHomeomorph Coord Coord,
        g.source = U ∧ g.target = V ∧ EqOn g (planarGradient G) U ∧
        ContDiffOn ℝ ∞ (planarGradient G) U ∧ ContDiffOn ℝ ∞ g.symm V := by
  obtain ⟨G, e, h, g, heS, _heT, _heF, _heD, _heI, hhS, _hhT, _hhF, _hhI,
    hG, _hrec, hgS, hgT, hgF, hgD, hgI, _hrest⟩ := hcore
  refine ⟨e.target, h.target, G, e.open_target, h.open_target,
    ⟨identityBandPlanarRegionHomeomorph e heS⟩,
    ⟨identityBandPlanarRegionHomeomorph h hhS⟩, hG, ?_,
    g, hgS, hgT, ?_, ?_, ?_⟩
  · simpa only [hgS, hgT] using g.bijOn.congr hgF
  · simpa only [hgS] using hgF
  · have hd := hgD.congr hgF.symm
    simpa only [hgS] using hd
  · simpa only [hgT] using hgI

end
end TightVer401