import TightVer401.IdentityBandCentralSupportRestriction
import TightVer401.IdentityBandCentralSupportSeedGeometry
import TightVer401.IdentityBandCentralSupportExtension
import TightVer401.IdentityBandCentralSupportTensor
import TightVer401.IdentityBandCentralSupportPhysical
import TightVer401.IdentityBandPlanarSupportPotential
import TightVer401.IdentityBandPlanarSupportSaddleImage

/-! One corrected seed, final collar, protected core and actual Cartesian
potential. The central tensor and signed tangential formula below belong to
that same potential, whose protected bending is selected after the final width. -/
open scoped Manifold
namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff Topology Matrix RealInnerProductSpace
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 300000

/-- Actual coupled Cartesian conclusions. This is an output predicate with
explicit derivatives of the same potential used by its retained core. -/
def IdentityBandCentralSupportWithPotential {T : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T) (w : ℝ) (a κ : ℝ → ℝ) (S : ℝ ≃ₜ ℝ)
    (G : Coord → ℝ) (U : Set Coord) : Prop :=
  IsOpen U ∧
    U = range (identityBandPlanarSource (identityBandTwoSidedSphereGauss (w := w) d)) ∧
    ContDiffOn ℝ ∞ G U ∧ IdentityBandPlanarSupportWithPotential d w G ∧
    ContDiffOn ℝ ∞ (identityBandCentralCoordinates d) (identityBandCentralRawDomain w) ∧
    MapsTo (identityBandCentralCoordinates d) (identityBandCentralRawDomain w) U ∧
    EqOn (planarSupportMap G ∘ identityBandCentralCoordinates d) (ruledMap d.γ d.E)
      (identityBandCentralRawDomain w) ∧
    EqOn (planarUnitNormal ∘ identityBandCentralCoordinates d) d.rawGaussMap
      (identityBandCentralRawDomain w) ∧
    (∀ q ∈ range (identityBandPlanarSource (d.bandSphereGauss (b := w))),
      (planarHessian G q).det < 0) ∧
    (∀ s : ℝ,
      let A := a (S.symm s)
      let Q : Fin 2 → Coord := fun i => fderiv ℝ (identityBandCentralCoordinates d)
        (![s, 0] : Coord) (A • (Pi.single i 1 : Coord))
      (fun i j => dotProduct (Q i)
        ((planarHessian G (identityBandCentralCoordinates d (![s, 0] : Coord))).mulVec (Q j)) /
        planarWeight (identityBandCentralCoordinates d (![s, 0] : Coord))) =
          (!![0, A; A, 0] : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    (∀ s t : ℝ, 0 < t →
      let A := a (S.symm s)
      let v := fderiv ℝ (identityBandCentralCoordinates d) (![s, 0] : Coord)
        (A • (![1, t] : Coord))
      let b := dotProduct v
        ((planarHessian G (identityBandCentralCoordinates d (![s, 0] : Coord))).mulVec v)
      b / planarWeight (identityBandCentralCoordinates d (![s, 0] : Coord)) = 2 * A * t ∧
        0 < b / planarWeight (identityBandCentralCoordinates d (![s, 0] : Coord)) ∧ 0 < b) ∧
    (∀ s u : ℝ, u ∈ Ioo (-w) w →
      let v := fderiv ℝ (identityBandCentralCoordinates d) (![s, u] : Coord)
        (Pi.single 0 1 : Coord)
      dotProduct v
        ((planarHessian G (identityBandCentralCoordinates d (![s, u] : Coord))).mulVec v) /
        planarWeight (identityBandCentralCoordinates d (![s, u] : Coord)) =
      u * (-deriv a (S.symm s) + u * deriv κ (S.symm s)) /
        ((a (S.symm s))^3 * Real.sqrt (ruledEnergy (d.k s) (d.τ s) u)))

/-- Starting only from the seed index and correction tolerance, construct one
corrected frame and final collar, select its genuine protected bending, and
prove its actual central Cartesian tensor and signed tangential entry for the
same smooth potential that retains that bending. -/
theorem identityBand_central_support_tensor {N : ℕ} (hN : 10000 ≤ N)
    {η : ℝ} (hη : 0 < η) :
    let ell := corrugatedSeedArcCell (N : ℝ)
  let L := (N : ℝ) * ell
    ∃ e : ℝ ≃ₜ ℝ, (e : ℝ → ℝ) = corrugatedSeedArcMap (N : ℝ) ∧
      ContDiff ℝ ∞ e.symm ∧
      ∃ a : ℝ → ℝ, ContDiff ℝ ∞ a ∧ Function.Periodic a ell ∧ (∀ r, 0 < a r) ∧
        (∫ r in 0..ell, ‖a r - corrugatedSeedInitialSpeed (N : ℝ) e.symm r‖) < η ∧
        (∫ r in 0..L, a r • normalLoopTangent (corrugatedSeedSphere (N : ℝ) ∘ e.symm) r) = 0 ∧
        (∫ r in 0..L, deriv (normalLoopCurvature (corrugatedSeedSphere (N : ℝ) ∘ e.symm)) r /
          Real.sqrt (a r)) = 0 ∧
        ComplexVisiblePair (1 / 4) (corrugatedSeedBeta (N : ℝ) ∘ e.symm)
          (corrugatedSeedBalancedPartner (N : ℝ) e.symm ell a) ∧
        ComplexVisiblePair (4 / 5)
          (corrugatedReverseReflect (corrugatedSeedBalancedPartner (N : ℝ) e.symm ell a))
          (corrugatedReverseReflect (corrugatedSeedBeta (N : ℝ) ∘ e.symm)) ∧
        ∃ S : ℝ ≃ₜ ℝ, (S : ℝ → ℝ) = rawPrimitive a ∧ ContDiff ℝ ∞ S.symm ∧
          ∃ d : PeriodicRuledFrame (rawPrimitive a L),
            d.γ = corrugatedSeedBalancedSpatial (N : ℝ) e.symm ell a ∘ S.symm ∧
            d.T = normalLoopTangent (corrugatedSeedSphere (N : ℝ) ∘ e.symm) ∘ S.symm ∧
            d.E = deriv (corrugatedSeedSphere (N : ℝ) ∘ e.symm) ∘ S.symm ∧
            d.n = (corrugatedSeedSphere (N : ℝ) ∘ e.symm) ∘ S.symm ∧
            d.k = normalLoopPhysicalK a
              (normalLoopCurvature (corrugatedSeedSphere (N : ℝ) ∘ e.symm)) S.symm ∧
            d.τ = normalLoopPhysicalTau a S.symm ∧ PrincipalNormalIdentityBand d ∧
            ∃ hT : 0 < rawPrimitive a L,
              letI : Fact (0 < rawPrimitive a L) := ⟨hT⟩
              ∃ w > 0, IdentityBandTwoSidedCollar d w ∧
                ProtectedIdentityBendingSubband d w ∧
                ∃ G : Coord → ℝ, ∃ U : Set Coord,
                  IdentityBandCentralSupportWithPotential d w a
                    (normalLoopCurvature (corrugatedSeedSphere (N : ℝ) ∘ e.symm)) S G U := by
  dsimp only
  obtain ⟨e, he, hψ, a, ha, haT, hapos, hsmall, hMfull, hBfull, hout, href, _hiCov,
    S, hS, hSsmooth, d, hγ, hT, hE, hn, hk, hτ, hidentity, hTpos,
    hninj, hnorthcentral, hhorizontal, oldw, holdw, hembold, hprojold⟩ :=
      identityBandCentralSupport_seed_geometry hN hη
  let L := (N : ℝ) * corrugatedSeedArcCell (N : ℝ)
  letI : Fact (0 < rawPrimitive a L) := ⟨hTpos⟩
  obtain ⟨w, hw, hwold, hcollar⟩ :=
    identityBand_exists_twoSided_collar d hninj hnorthcentral hhorizontal holdw
  obtain ⟨hembw, hprojw⟩ := identityBandCentralSupport_restrict_band_embeddings
    d hwold hembold hprojold
  have hmem (p : AddCircle (rawPrimitive a L) × Ioo (0 : ℝ) w) :
      (p.1, (p.2 : ℝ)) ∈ (univ ×ˢ Icc (-w) w : Set (AddCircle (rawPrimitive a L) × ℝ)) := by
    refine ⟨mem_univ _, ?_, p.2.property.2.le⟩
    linarith [p.2.property.1]
  have hgauss : Function.Injective
      (fun p : AddCircle (rawPrimitive a L) × Ioo (0 : ℝ) w => d.fullGaussMap (p.1, (p.2 : ℝ))) := by
    intro p q heq
    have hr := hcollar.1 (hmem p) (hmem q) heq
    have hfirst : p.1 = q.1 :=
      congrArg (fun z : AddCircle (rawPrimitive a L) × ℝ => z.1) hr
    have hsecond : (p.2 : ℝ) = (q.2 : ℝ) :=
      congrArg (fun z : AddCircle (rawPrimitive a L) × ℝ => z.2) hr
    exact Prod.ext hfirst (Subtype.ext hsecond)
  have hNi := periodicRuledFrame_bandSphereGauss_injective_of_actual d hgauss
  have hnorth (p : AddCircle (rawPrimitive a L) × Ioo (0 : ℝ) w) :
      0 < d.bandGaussMap p 2 := hcollar.2.1 _ (hmem p)
  have hprojection := periodicRuledFrame_northern_band_projection_regular d hnorth
  have hprotected : ProtectedIdentityBendingSubband d w :=
    periodicRuledFrame_protectedIdentityBendingSubband d hidentity hw hembw
  have hcore : IdentityBandPlanarSupportAnnulus d w :=
    identityBandPlanarSupport_actual_band d hw hNi hnorth hprojw
    hprojection.1 hprojection.2 hprotected
  obtain ⟨G, U, hU, hUr, hG, hrecTwo, hP, hPU, hrawrec, hrawnorm⟩ :=
    identityBandTwoSided_exists_cartesian_support d hw hcollar
  let jTwo : AddCircle (rawPrimitive a L) × Ioo (0 : ℝ) w →
      AddCircle (rawPrimitive a L) × Ioo (-w) w :=
    fun p => (p.1, ⟨p.2, ⟨by linarith [p.2.property.1], p.2.property.2⟩⟩)
  have hsrcTwo (p : AddCircle (rawPrimitive a L) × Ioo (0 : ℝ) w) :
      identityBandPlanarSource (identityBandTwoSidedSphereGauss d) (jTwo p) =
        identityBandPlanarSource (d.bandSphereGauss (b := w)) p := rfl
  have hxTwo (p : AddCircle (rawPrimitive a L) × Ioo (0 : ℝ) w) :
      identityBandTwoSidedMap d (jTwo p) = d.bandMap p := rfl
  have hsourceSubset : range (identityBandPlanarSource (d.bandSphereGauss (b := w))) ⊆ U := by
    rintro q ⟨p, rfl⟩
    rw [hUr]
    exact ⟨jTwo p, hsrcTwo p⟩
  have hGpositive : ContDiffOn ℝ ∞ G
      (range (identityBandPlanarSource (d.bandSphereGauss (b := w)))) := hG.mono hsourceSubset
  have hrecPositive (p : AddCircle (rawPrimitive a L) × Ioo (0 : ℝ) w) :
      planarSupportMap G (identityBandPlanarSource (d.bandSphereGauss (b := w)) p) = d.bandMap p := by
    simpa only [hsrcTwo p, hxTwo p] using hrecTwo (jTwo p)
  have hcoreG : IdentityBandPlanarSupportWithPotential d w G :=
    identityBandPlanarSupport_with_actual_potential d hcore hGpositive hrecPositive
  have hpositiveOpen : IsOpen (range (identityBandPlanarSource (d.bandSphereGauss (b := w)))) := by
    obtain ⟨_Gold, ecore, _h, _g, _heS, heT, _rest⟩ := hcore
    rw [← heT]
    exact ecore.open_target
  have hsign := identityBandPlanarSupport_hessian_det_neg_on_image d hGpositive
    hpositiveOpen rfl hnorth hrecPositive
  have hcentral (s : ℝ) : (![s, 0] : Coord) ∈ identityBandCentralRawDomain w := by
    change (0 : ℝ) ∈ Ioo (-w) w
    constructor <;> linarith
  have hτpoint (s : ℝ) : d.τ s = -(a (S.symm s))⁻¹ := by
    rw [hτ]
    rfl
  have hκ : ContDiff ℝ ∞ (normalLoopCurvature (corrugatedSeedSphere (N : ℝ) ∘ e.symm)) :=
    (normalLoop_actual_smooth ((corrugatedSeedSphere_contDiff (N : ℝ)).comp hψ)).2
  have hdata : IdentityBandCentralSupportWithPotential d w a
      (normalLoopCurvature (corrugatedSeedSphere (N : ℝ) ∘ e.symm)) S G U := by
    refine ⟨hU, hUr, hG, hcoreG, hP, hPU, hrawrec, hrawnorm, hsign, ?_, ?_, ?_⟩
    · intro s
      exact identityBand_central_cartesian_tensor d s
        (G := G) (U := U) (V := identityBandCentralRawDomain w)
        (P := identityBandCentralCoordinates d) hG hU
        (identityBandCentralRawDomain_isOpen w) hP hPU hrawrec hrawnorm (hcentral s)
        (hapos (S.symm s)) (hτpoint s)
    · intro s t ht
      exact identityBand_central_cartesian_positive_transverse d s
        (G := G) (U := U) (V := identityBandCentralRawDomain w)
        (P := identityBandCentralCoordinates d) hG hU
        (identityBandCentralRawDomain_isOpen w) hP hPU hrawrec hrawnorm (hcentral s)
        (hapos (S.symm s)) (hτpoint s) ht
    · intro s u hu
      have hp : (![s, u] : Coord) ∈ identityBandCentralRawDomain w := hu
      have hpull := identityBand_cartesian_pullback_pairing
        (G := G) (U := U) (V := identityBandCentralRawDomain w)
        (P := identityBandCentralCoordinates d) hG hU
        (identityBandCentralRawDomain_isOpen w) hP hPU hrawrec hrawnorm hp
        (Pi.single 0 1 : Coord) (Pi.single 0 1 : Coord)
      exact hpull.symm.trans
        (identityBand_corrected_frame_tangential_pairing d ha hκ hapos S hS hk hτ s u)
  exact ⟨e, he, hψ, a, ha, haT, hapos, hsmall, hMfull, hBfull, hout, href,
    S, hS, hSsmooth, d, hγ, hT, hE, hn, hk, hτ, hidentity, hTpos,
    w, hw, hcollar, hprotected, G, U, hdata⟩

end
end TightVer401
