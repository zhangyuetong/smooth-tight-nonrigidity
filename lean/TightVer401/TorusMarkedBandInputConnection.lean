import TightVer401.TorusMarkedBandCurvatureConnection
import TightVer401.BandLiftStrain
import TightVer401.GeneralRuledGeometry
import TightVer401.TorusRigidCurvatureConnection
import TightVer401.AffineMarkedTorusLinearCurvature

/-! Actual four physical-coordinate inputs for the literal marked threshold.
Ordinary ruled-frame data and actual band bending suffice. Smoothness, rank
and negative baseline curvature are global; the lifted field's smoothness
and zero strain are required only on the same open physical band. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false

/-- Discharge the four physical-coordinate hypotheses of the marked band
threshold from the SAME ruled frame, affine placement and actual bending.
No rank, normal, curvature or strain correspondence is an input. -/
theorem periodicRuledFrame_marked_coordinate_inputs
    {T w : ℝ} [Fact (0 < T)] (d : PeriodicRuledFrame T)
    (A : Ambient ≃ᵃⁱ[ℝ] Ambient)
    {Y : AddCircle T × Ioo (0 : ℝ) w → Ambient}
    (hY : IsBandBending (d.bandMap (b := w)) Y) :
    ContDiff ℝ ∞ (markedRuledBandCoordinateBase d A
      torusAffineMarkerLinearEquiv.toContinuousLinearMap) ∧
    IsInfinitesimalBendingOn (markedRuledBandCoordinateBase d A
      torusAffineMarkerLinearEquiv.toContinuousLinearMap)
      (markedRuledBandCoordinateField Y A
        torusAffineMarkerContraLinearEquiv.toContinuousLinearMap)
      (markedRuledBandCoordinateDomain w) ∧
    (∀ q ∈ markedRuledBandCoordinateDomain w, Function.Injective
      (fderiv ℝ (markedRuledBandCoordinateBase d A
        torusAffineMarkerLinearEquiv.toContinuousLinearMap) q)) ∧
    (∀ q ∈ markedRuledBandCoordinateDomain w, gaussianCurvature
      (inducedMetric (markedRuledBandCoordinateBase d A
        torusAffineMarkerLinearEquiv.toContinuousLinearMap)) q < 0) := by
  let X : Coord → Ambient := ruledMap d.γ d.E
  let XA : Coord → Ambient := A ∘ X
  let XB : Coord → Ambient := fun q => torusAffineMarker (XA q)
  let V : Coord → Ambient := bandCoordinateLift Y
  let VC : Coord → Ambient := fun q => torusAffineMarkerContra (A.linearIsometryEquiv (V q))
  let U : Set Coord := markedRuledBandCoordinateDomain w
  have hX : ContDiff ℝ ∞ X := general_ruled_contDiff d.smooth_γ d.smooth_E
  have hXA : ContDiff ℝ ∞ XA := by
    have he : XA = fun q => A.linearIsometryEquiv (X q) + A 0 := by
      funext q
      simpa only [XA, Function.comp_apply, vadd_eq_add, add_zero] using
        A.map_vadd (0 : Ambient) (X q)
    rw [he]
    exact (A.linearIsometryEquiv.contDiff.comp hX).add contDiff_const
  have hXB : ContDiff ℝ ∞ XB := torusAffineMarkerLinearEquiv.contDiff.comp hXA
  have hV : ContDiffOn ℝ ∞ V U := bandCoordinateLift_contDiffOn hY.1
  have hVC : ContDiffOn ℝ ∞ VC U :=
    torusAffineMarkerContraLinearEquiv.contDiff.comp_contDiffOn
      (A.linearIsometryEquiv.contDiff.comp_contDiffOn hV)
  have hiX (p : Coord) : Function.Injective (fderiv ℝ X p) :=
    ruled_differential_injective (d.deriv_γ (p 0)) (d.deriv_E (p 0))
      (d.orthonormal (p 0)) (d.torsion_ne_zero (p 0))
  have hiXA (p : Coord) : Function.Injective (fderiv ℝ XA p) := by
    intro v z he
    change fderiv ℝ (A ∘ X) p v = fderiv ℝ (A ∘ X) p z at he
    rw [torusRigid_coord_fderiv] at he
    change A.linearIsometryEquiv (fderiv ℝ X p v) =
      A.linearIsometryEquiv (fderiv ℝ X p z) at he
    exact hiX p (A.linearIsometryEquiv.injective he)
  have hiXB (p : Coord) : Function.Injective (fderiv ℝ XB p) := by
    intro v z he
    change fderiv ℝ (fun q => torusAffineMarker (XA q)) p v =
      fderiv ℝ (fun q => torusAffineMarker (XA q)) p z at he
    rw [affineMarkedTorusLinear_fderiv (hXA.differentiable (by simp) p)] at he
    change torusAffineMarker (fderiv ℝ XA p v) =
      torusAffineMarker (fderiv ℝ XA p z) at he
    exact hiXA p (torusAffineMarker_injective he)
  have hKX (p : Coord) : gaussianCurvature (inducedMetric X) p < 0 :=
    ruled_gaussianCurvature_neg d.deriv_γ d.deriv_E hX.contDiffOn isOpen_univ
      (fun q _ => d.orthonormal (q 0)) (fun q _ => d.torsion_ne_zero (q 0)) (mem_univ p)
  have hKXA (p : Coord) : gaussianCurvature (inducedMetric XA) p < 0 := by
    change gaussianCurvature (inducedMetric (A ∘ X)) p < 0
    rw [torusRigid_coord_inducedMetric]
    exact hKX p
  have hKXB (p : Coord) : gaussianCurvature (inducedMetric XB) p < 0 := by
    let n := ruledNormal (d.T (p 0)) (d.n (p 0)) (d.k (p 0)) (d.τ (p 0)) (p 1)
    have hn : IsUnitNormalAt X n p := ruled_isUnitNormal
      (d.deriv_γ (p 0)) (d.deriv_E (p 0))
      (d.orthonormal (p 0)) (d.torsion_ne_zero (p 0))
    have hnA : IsUnitNormalAt XA (A.linearIsometryEquiv n) p := by
      refine ⟨?_, ?_⟩
      · rw [A.linearIsometryEquiv.inner_map_map]
        exact hn.1
      · intro v
        change inner ℝ (fderiv ℝ (A ∘ X) p v) (A.linearIsometryEquiv n) = 0
        rw [torusRigid_coord_fderiv]
        change inner ℝ (A.linearIsometryEquiv (fderiv ℝ X p v))
          (A.linearIsometryEquiv n) = 0
        rw [A.linearIsometryEquiv.inner_map_map]
        exact hn.2 v
    exact (affineMarkedTorusLinear_gaussianCurvature_neg_iff isOpen_univ hXA.contDiffOn
      (fun q _ => hiXA q) (mem_univ p) hnA).mpr (hKXA p)
  change ContDiff ℝ ∞ XB ∧ IsInfinitesimalBendingOn XB VC U ∧
    (∀ q ∈ U, Function.Injective (fderiv ℝ XB q)) ∧
    (∀ q ∈ U, gaussianCurvature (inducedMetric XB) q < 0)
  refine ⟨hXB, ⟨hVC, ?_⟩, fun q _ => hiXB q, fun q _ => hKXB q⟩
  intro p hp i j
  have hBX (k : Fin 2) : coordPartial k XB p =
      torusAffineMarker (A.linearIsometryEquiv (coordPartial k X p)) := by
    change fderiv ℝ (fun q => torusAffineMarker ((A ∘ X) q)) p (Pi.single k 1) =
      torusAffineMarker (A.linearIsometryEquiv (fderiv ℝ X p (Pi.single k 1)))
    rw [affineMarkedTorusLinear_fderiv (hXA.differentiable (by simp) p),
      torusRigid_coord_fderiv]
    rfl
  have hCV (k : Fin 2) : coordPartial k VC p =
      torusAffineMarkerContra (A.linearIsometryEquiv (coordPartial k V p)) := by
    change fderiv ℝ (torusAffineMarkerContraLinearEquiv ∘ (A.linearIsometryEquiv ∘ V)) p
      (Pi.single k 1) =
        torusAffineMarkerContra (A.linearIsometryEquiv (fderiv ℝ V p (Pi.single k 1)))
    rw [torusAffineMarkerContraLinearEquiv.comp_fderiv, A.linearIsometryEquiv.comp_fderiv]
    rfl
  have hs := bandCoordinateLift_strain_in_band d hY hp i j
  change strain X V p i j = 0 at hs
  unfold strain
  rw [hBX i, hCV j, hCV i, hBX j, torusAffineMarker_strain_transport,
    A.linearIsometryEquiv.inner_map_map, A.linearIsometryEquiv.inner_map_map]
  exact hs

end
end TightVer401
