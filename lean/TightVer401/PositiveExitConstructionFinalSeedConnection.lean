import TightVer401.PositiveExitConstructionVisibleTurnSeed
import TightVer401.IdentityBandFlowOpenConnection

/-! Connect the FINAL field chosen after the common visible/turn margin to the
SAME original support potential and actual native Gauss chart. The old field
inside the potential package is deliberately discarded. The consumer is
positiveExit_exists_two_selected_visible_cartesian_patches. -/
open scoped Manifold
namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.SmoothLocal.Geometry
open scoped ContDiff Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

section
variable {T w : ℝ} [Fact (0 < T)]
local instance finalSeedCoordChartedSpace :
    ChartedSpace Coord (AddCircle T × Ioo (0 : ℝ) w) := nativeProductGaussChartedSpace _
local instance finalSeedCoordManifold :
    IsManifold 𝓘(ℝ, Coord) ∞ (AddCircle T × Ioo (0 : ℝ) w) := nativeProductGauss_isManifold _

/-- Transfer any final actual band bending through the retained native chart;
no existential field from an earlier support package is used. -/
theorem positiveExit_final_band_bending_transfer
    (d : PeriodicRuledFrame T) {G : Coord → ℝ}
    {Y : AddCircle T × Ioo (0 : ℝ) w → Ambient}
    (hY : IsBandBending (d.bandMap (b := w)) Y)
    (c0 : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) Coord)
    (hsource : c0.source = univ)
    (hci : ContMDiffOn 𝓘(ℝ, Coord) nativeProductModel ∞ c0.symm c0.target)
    (hrec : ∀ p, planarSupportMap G (c0 p) = d.bandMap p) :
    IsInfinitesimalBendingOn (planarSupportMap G) (Y ∘ c0.symm) c0.target := by
  let M := AddCircle T × Ioo (0 : ℝ) w
  have hX : ContMDiff 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) ∞ (d.bandMap (b := w)) :=
    d.bandMap_contMDiff.comp (nativeProductGauss_inverse_contMDiff M)
  have hYC : ContMDiff 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) ∞ Y :=
    hY.1.comp (nativeProductGauss_inverse_contMDiff M)
  have hciC : ContMDiffOn 𝓘(ℝ, Coord) 𝓘(ℝ, Coord) ∞ c0.symm c0.target :=
    (nativeProductGauss_identity_contMDiff M).comp_contMDiffOn hci
  have hstrain (p : M) (v z : TangentSpace 𝓘(ℝ, Coord) p) :
      @inner ℝ Ambient _ (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) d.bandMap p v)
        (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) Y p z) +
      @inner ℝ Ambient _ (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) Y p v)
        (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) d.bandMap p z) = 0 := by
    rw [nativeProductGauss_mfderiv M ((d.bandMap_contMDiff p).mdifferentiableAt (by simp)),
      nativeProductGauss_mfderiv M ((hY.1 p).mdifferentiableAt (by simp))]
    exact hY.2 p (nativeProductGaussCoordinateEquiv.symm v)
      (nativeProductGaussCoordinateEquiv.symm z)
  exact identityBandPlanarSupport_bending_transfer hX hYC hstrain c0 hsource hciC hrec

/-- Extract the actual native chart for the fixed scalar, then attach the SAME
final protected Y. The compact set is literally c0 '' tsupport Y. The final
margin, period balance and flow containment are supplied by the already proved
same-seed visible/turn producer; no selected exit geometry is assumed. -/
theorem positiveExit_final_seed_support_connection
    (d : PeriodicRuledFrame T) {a κ : ℝ → ℝ} {S : ℝ ≃ₜ ℝ}
    {G : Coord → ℝ} {U : Set Coord}
    (hc : IdentityBandCentralSupportWithPotential d w a κ S G U)
    {δ : ℝ}
    (hb : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0)
    (hinside : ∀ v ∈ Ioo (0 : ℝ) δ, ∀ s : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 v s ∈ Ioo 0 w)
    (Y : AddCircle T × Ioo (0 : ℝ) w → Ambient)
    (hY : IsBandBending (d.bandMap (b := w)) Y)
    (hcompact : HasCompactSupport Y) (hnonzero : ∃ p, Y p ≠ 0)
    (hsupport : tsupport Y ⊆ range (identityFlowBandInclusion d hb 0 hinside)) :
    ∃ c0 : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) Coord,
      c0.source = univ ∧
      c0.target = range (identityBandPlanarSource (d.bandSphereGauss (b := w))) ∧
      (∀ p, c0 p = gnomonicInverse (d.bandGaussMap p)) ∧
      ContMDiff nativeProductModel 𝓘(ℝ, Coord) ∞ c0 ∧
      ContMDiffOn 𝓘(ℝ, Coord) nativeProductModel ∞ c0.symm c0.target ∧
      ContDiffOn ℝ ∞ G c0.target ∧
      (∀ p, planarSupportMap G (c0 p) = d.bandMap p) ∧
      (∀ q ∈ c0.target, (planarHessian G q).det < 0) ∧
      Topology.IsEmbedding (fun q : c0.target => planarGradient G q.val) ∧
      IsInfinitesimalBendingOn (planarSupportMap G) (Y ∘ c0.symm) c0.target ∧
      ∃ C : Set Coord, C = c0 '' tsupport Y ∧ IsCompact C ∧ C.Nonempty ∧
        C ⊆ c0 '' range (identityFlowBandInclusion d hb 0 hinside) ∧
        c0 '' tsupport Y ⊆ C := by
  have hcore := hc.2.2.2.1
  have hdet := hc.2.2.2.2.2.2.2.2.1
  obtain ⟨c0, h, g, hcS, hcT, hcF, hcD, hcI, hhS, hhT, hhF, hhI,
    hG, hrec, hgS, hgT, hgF, hgD, hgI, _⟩ := hcore
  have hactual (p : AddCircle T × Ioo (0 : ℝ) w) :
      c0 p = gnomonicInverse (d.bandGaussMap p) := by
    rw [hcF]
    rfl
  have hdetTarget : ∀ q ∈ c0.target, (planarHessian G q).det < 0 := by
    rw [hcT]
    exact hdet
  have hgEmbed : Topology.IsEmbedding (fun q : c0.target => g q.val) := by
    rw [← hgS]
    change Topology.IsEmbedding (g.source.domRestrict (g : Coord → Coord))
    exact g.isEmbedding_restrict
  have hgradEmbed : Topology.IsEmbedding (fun q : c0.target => planarGradient G q.val) := by
    have heq : (fun q : c0.target => planarGradient G q.val) =
        (fun q : c0.target => g q.val) := by
      funext q
      exact (hgF (hgS.symm ▸ q.property)).symm
    rw [heq]
    exact hgEmbed
  have hbend := positiveExit_final_band_bending_transfer d hY c0 hcS hcI hrec
  have hcContinuous : Continuous c0 := continuousOn_univ.mp (by
    simpa only [hcS] using c0.continuousOn)
  have hC : IsCompact (c0 '' tsupport Y) := hcompact.image hcContinuous
  obtain ⟨p, hp⟩ := hnonzero
  have hCne : (c0 '' tsupport Y).Nonempty :=
    ⟨c0 p, ⟨p, subset_tsupport Y hp, rfl⟩⟩
  refine ⟨c0, hcS, hcT, hactual, hcD, hcI, hG, hrec, hdetTarget,
    hgradEmbed, hbend, c0 '' tsupport Y, rfl, hC, hCne, ?_, subset_rfl⟩
  exact image_mono hsupport

end
end
end TightVer401
