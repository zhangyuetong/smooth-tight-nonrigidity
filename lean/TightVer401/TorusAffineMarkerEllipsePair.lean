import TightVer401.TorusAffineMarkerEllipseGeometry

/-! Two actual boundary ellipses determine the entire ambient isometry.
The boundary permutation is proved from connectedness, and a swap forces
identical radii through the actual ellipse diameter theorem. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped Matrix Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
/-- The elementary, original part of the two-boundary-torusAffineMarkerEllipse argument. -/
theorem torusAffineMarker_sameRadius_pair_stabilizer (axes : MarkerEllipseAxesRecognition)
    (L : Ambient ≃ₗᵢ[ℝ] Ambient) (b : Ambient) (h R : ℝ) (hh : h ≠ 0) (hR : 0 < R)
    (hpair :
      (torusAffineMarkerIsometry L b '' torusAffineMarkerEllipse (torusAffineMarkerCenter h) R (2*R) = torusAffineMarkerEllipse (torusAffineMarkerCenter h) R (2*R) ∧
       torusAffineMarkerIsometry L b '' torusAffineMarkerEllipse (torusAffineMarkerCenter (-h)) R (2*R) = torusAffineMarkerEllipse (torusAffineMarkerCenter (-h)) R (2*R)) ∨
      (torusAffineMarkerIsometry L b '' torusAffineMarkerEllipse (torusAffineMarkerCenter h) R (2*R) = torusAffineMarkerEllipse (torusAffineMarkerCenter (-h)) R (2*R) ∧
       torusAffineMarkerIsometry L b '' torusAffineMarkerEllipse (torusAffineMarkerCenter (-h)) R (2*R) = torusAffineMarkerEllipse (torusAffineMarkerCenter h) R (2*R))) :
    (∀ p, torusAffineMarkerIsometry L b p = p) ∨ (∀ p, torusAffineMarkerIsometry L b p = -p) := by
  rcases hpair with ⟨hp,hm⟩ | ⟨hp,hm⟩
  · obtain ⟨hcp,σ,hsgn,hd⟩ := axes L b _ _ R (2*R) hR (by linarith) hp
    have hcm := (axes L b _ _ R (2*R) hR (by linarith) hm).1
    rw [torusAffineMarker_center_neg] at hcm
    have hb := torusAffineMarker_translation_zero L b _ _ hcp hcm
    subst b
    have hc : L (torusAffineMarkerCenter h) = (1:ℝ) • torusAffineMarkerCenter h := by simpa [torusAffineMarkerIsometry] using hcp
    have hf := torusAffineMarker_diagonal_from_centers L h 1 hh σ hd hc
    exact Or.inl (fun p => by simpa [torusAffineMarkerIsometry] using hf p)
  · obtain ⟨hcp,σ,hsgn,hd⟩ := axes L b _ _ R (2*R) hR (by linarith) hp
    have hcm := (axes L b _ _ R (2*R) hR (by linarith) hm).1
    rw [torusAffineMarker_center_neg] at hcp hcm
    have hcm' : torusAffineMarkerIsometry L b (-torusAffineMarkerCenter h) = -(-torusAffineMarkerCenter h) := by simpa using hcm
    have hb := torusAffineMarker_translation_zero L b _ _ hcp hcm'
    subst b
    have hc : L (torusAffineMarkerCenter h) = (-1:ℝ) • torusAffineMarkerCenter h := by simpa [torusAffineMarkerIsometry] using hcp
    have hf := torusAffineMarker_diagonal_from_centers L h (-1) hh σ hd hc
    exact Or.inr (fun p => by simpa [torusAffineMarkerIsometry] using hf p)


/-- Ordinary preservation of the pair DERIVES its boundary permutation. -/
theorem torusAffineMarkerEllipse_pair_permutation {RN RS h : ℝ}
    (hRN : 0 < RN) (hRS : 0 < RS) (hh : 0 < h)
    (L : Ambient ≃ₗᵢ[ℝ] Ambient) (b : Ambient)
    (hp : torusAffineMarkerIsometry L b ''
        (torusAffineMarkerEllipse (torusAffineMarkerCenter h) RN (2 * RN) ∪
          torusAffineMarkerEllipse (torusAffineMarkerCenter (-h)) RS (2 * RS)) =
      torusAffineMarkerEllipse (torusAffineMarkerCenter h) RN (2 * RN) ∪
        torusAffineMarkerEllipse (torusAffineMarkerCenter (-h)) RS (2 * RS)) :
    (torusAffineMarkerIsometry L b '' torusAffineMarkerEllipse (torusAffineMarkerCenter h) RN (2 * RN) =
        torusAffineMarkerEllipse (torusAffineMarkerCenter h) RN (2 * RN) ∧
      torusAffineMarkerIsometry L b '' torusAffineMarkerEllipse (torusAffineMarkerCenter (-h)) RS (2 * RS) =
        torusAffineMarkerEllipse (torusAffineMarkerCenter (-h)) RS (2 * RS)) ∨
    (torusAffineMarkerIsometry L b '' torusAffineMarkerEllipse (torusAffineMarkerCenter h) RN (2 * RN) =
        torusAffineMarkerEllipse (torusAffineMarkerCenter (-h)) RS (2 * RS) ∧
      torusAffineMarkerIsometry L b '' torusAffineMarkerEllipse (torusAffineMarkerCenter (-h)) RS (2 * RS) =
        torusAffineMarkerEllipse (torusAffineMarkerCenter h) RN (2 * RN)) := by
  have hc : Continuous (torusAffineMarkerIsometry L b) :=
    (torusAffineMarkerIsometryHomeomorph L b).continuous
  have hN := torusAffineMarkerEllipse_connected (torusAffineMarkerCenter h)
    hRN.ne' (show 2 * RN ≠ 0 by positivity)
  have hS := torusAffineMarkerEllipse_connected (torusAffineMarkerCenter (-h))
    hRS.ne' (show 2 * RS ≠ 0 by positivity)
  rw [image_union] at hp
  have hd : Disjoint (torusAffineMarkerEllipse (torusAffineMarkerCenter h) RN (2 * RN))
      (torusAffineMarkerEllipse (torusAffineMarkerCenter (-h)) RS (2 * RS)) := by
    apply disjoint_left.mpr
    intro p hN hS
    have hn : p 2 = h := hN.1
    have hs : p 2 = -h := hS.1
    linarith
  apply torusAffineMarker_split_pair _ _ _ _ hN.nonempty hS.nonempty hd hp
  · apply torusAffineMarker_connected_ellipse_side hh
      (hN.isPreconnected.image (torusAffineMarkerIsometry L b) hc.continuousOn)
    rw [← hp]
    exact subset_union_left
  · apply torusAffineMarker_connected_ellipse_side hh
      (hS.isPreconnected.image (torusAffineMarkerIsometry L b) hc.continuousOn)
    rw [← hp]
    exact subset_union_right

/-- Generic distinct-radius marker pair: inversion is possible only when RN=RS. -/
theorem torusAffineMarkerEllipse_pair_stabilizer (axes : MarkerEllipseAxesRecognition)
    {RN RS h : ℝ} (hRN : 0 < RN) (hRS : 0 < RS) (hh : 0 < h)
    (L : Ambient ≃ₗᵢ[ℝ] Ambient) (b : Ambient)
    (hp : torusAffineMarkerIsometry L b ''
        (torusAffineMarkerEllipse (torusAffineMarkerCenter h) RN (2 * RN) ∪
          torusAffineMarkerEllipse (torusAffineMarkerCenter (-h)) RS (2 * RS)) =
      torusAffineMarkerEllipse (torusAffineMarkerCenter h) RN (2 * RN) ∪
        torusAffineMarkerEllipse (torusAffineMarkerCenter (-h)) RS (2 * RS)) :
    (∀ p, torusAffineMarkerIsometry L b p = p) ∨
      (RN = RS ∧ ∀ p, torusAffineMarkerIsometry L b p = -p) := by
  rcases torusAffineMarkerEllipse_pair_permutation hRN hRS hh L b hp with ⟨hN,hS⟩ | ⟨hN,hS⟩
  · obtain ⟨hcN,σ,hσ,hd⟩ := axes L b _ _ RN (2 * RN) hRN (by linarith) hN
    have hcS := (axes L b _ _ RS (2 * RS) hRS (by linarith) hS).1
    rw [torusAffineMarker_center_neg] at hcS
    have hb := torusAffineMarker_translation_zero L b _ _ hcN hcS
    subst b
    have hc : L (torusAffineMarkerCenter h) = (1 : ℝ) • torusAffineMarkerCenter h := by
      simpa [torusAffineMarkerIsometry] using hcN
    have hi := torusAffineMarker_diagonal_from_centers L h 1 hh.ne' σ hd hc
    exact Or.inl (fun p => by simpa [torusAffineMarkerIsometry] using hi p)
  · have he : RN = RS := torusAffineMarkerEllipse_radius_eq_of_image hRN hRS _ _ L b hN
    subst RS
    rcases torusAffineMarker_sameRadius_pair_stabilizer axes L b h RN hh.ne' hRN
      (Or.inr ⟨hN,hS⟩) with hi | hi
    · exact Or.inl hi
    · exact Or.inr ⟨rfl,hi⟩

/-- Unequal actual radii exclude a swap without a meridian asymmetry hypothesis. -/
theorem torusAffineMarkerEllipse_distinctRadii_rigid (axes : MarkerEllipseAxesRecognition)
    {RN RS h : ℝ} (hRN : 0 < RN) (hRS : 0 < RS) (hh : 0 < h) (hne : RN ≠ RS)
    (L : Ambient ≃ₗᵢ[ℝ] Ambient) (b : Ambient)
    (hp : torusAffineMarkerIsometry L b ''
        (torusAffineMarkerEllipse (torusAffineMarkerCenter h) RN (2 * RN) ∪
          torusAffineMarkerEllipse (torusAffineMarkerCenter (-h)) RS (2 * RS)) =
      torusAffineMarkerEllipse (torusAffineMarkerCenter h) RN (2 * RN) ∪
        torusAffineMarkerEllipse (torusAffineMarkerCenter (-h)) RS (2 * RS)) :
    ∀ p, torusAffineMarkerIsometry L b p = p := by
  rcases torusAffineMarkerEllipse_pair_stabilizer axes hRN hRS hh L b hp with hi | ⟨he,hi⟩
  · exact hi
  · exact False.elim (hne he)

end
end TightVer401
