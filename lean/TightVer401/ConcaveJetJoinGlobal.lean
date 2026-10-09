import TightVer401.ConcaveJetJoinEndpoint
import TightVer401.ConcaveJetJoinOuterGerms

namespace TightVer401
noncomputable section
open Set
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

/-- Auxiliary globally smooth representatives are joined by correcting actual
acceleration moments and integrating twice. The originals are recovered on
open half-lines containing both endpoints. -/
theorem exists_concaveJetJoin_global {L c : ℝ} (hc : c ∈ Ioo 0 L)
    {qL qR : ℝ → ℝ} (hqL : ContDiff ℝ ∞ qL) (hqR : ContDiff ℝ ∞ qR)
    (hv : qL c = qR c) (hd : deriv qL c = deriv qR c)
    (hnegL : ∀ x ∈ Icc 0 L, deriv (deriv qL) x < 0)
    (hnegR : ∀ x ∈ Icc 0 L, deriv (deriv qR) x < 0) :
    ∃ Q : ℝ → ℝ, ContDiff ℝ ∞ Q ∧
      (∀ x ∈ Icc 0 L, deriv (deriv Q) x < 0) ∧
      (∃ α > 0, EqOn Q qL (Iio α)) ∧
      (∃ β < L, EqOn Q qR (Ioi β)) := by
  have hqL₂ := (contDiff_infty_iff_deriv.mp ((contDiff_infty_iff_deriv.mp hqL).2)).2
  have hqR₂ := (contDiff_infty_iff_deriv.mp ((contDiff_infty_iff_deriv.mp hqR).2)).2
  let hL := fun x => -deriv (deriv qL) x
  let hR := fun x => -deriv (deriv qR) x
  have hfL : ContDiff ℝ ∞ hL := hqL₂.neg
  have hfR : ContDiff ℝ ∞ hR := hqR₂.neg
  obtain ⟨μ, hμ, hμL, hμR⟩ := exists_jetAcceleration_positive_floor
    (show 0 ≤ L by linarith [hc.1, hc.2]) hfL.continuous hfR.continuous
    (fun x hx => neg_pos.mpr (hnegL x hx)) (fun x hx => neg_pos.mpr (hnegR x hx))
  obtain ⟨r, ψ, a, hr, _, hl, hu, _, hψS, ha, hapos, hmoment, hsupp⟩ :=
    exists_concaveJetJoin_acceleration hc jetAffineMomentVector
      jetAffineMomentVector_contDiff.continuous hfL hfR hμ hμL hμR
      (show 0 < (1 : ℝ) by norm_num)
  obtain ⟨⟨α, hα, _, heL⟩, ⟨β, hβ, _, heR⟩⟩ :=
    concaveJetJoin_corrected_outer_germs hr hl hu hL hR a ψ hψS hsupp
  let Q := concaveJetReconstruction 0 (qL 0) (deriv qL 0) a
  have hQ : ContDiff ℝ ∞ Q := concaveJetReconstruction_contDiff ha _ _ _
  have hjet0 := concaveJetReconstruction_first_jet ha 0 (qL 0) (deriv qL 0)
  have hjetL := concaveJetJoin_endpoint_of_affine_moment hc hqL hqR ha hv hd hmoment
  have heQL : EqOn qL Q (Iio α) := concaveJetJoin_germ_from_acceleration
    isOpen_Iio (convex_Iio α).isPreconnected hα hqL.contDiffOn ha _ _ _
    (fun x hx => by rw [heL hx]; simp [hL]) hjet0.1.symm hjet0.2.symm
  have heQR : EqOn qR Q (Ioi β) := concaveJetJoin_germ_from_acceleration
    isOpen_Ioi (convex_Ioi β).isPreconnected hβ hqR.contDiffOn ha _ _ _
    (fun x hx => by rw [heR hx]; simp [hR]) hjetL.1.symm hjetL.2.symm
  exact ⟨Q, hQ, concaveJetReconstruction_strict_concavity ha _ _ _ hapos,
    ⟨α, hα, heQL.symm⟩, ⟨β, hβ, heQR.symm⟩⟩

end
end TightVer401
