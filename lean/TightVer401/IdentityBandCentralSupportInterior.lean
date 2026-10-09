import TightVer401.IdentityBandCentralSupportCoordinates
import TightVer401.RuledSecondForm

/-! Actual interior differential pairings of the same ruled frame.
These are raw ruled-germ calculations; transport to a global Cartesian
potential and the construction of closed positive exits remain separate. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- The full actual interior pairing is the negative second fundamental form.
The coefficient formulas come from the retained ruled second-form calculus. -/
theorem identityBand_interior_differential_pairing {L : ℝ}
    (d : PeriodicRuledFrame L) (p v w : Coord) :
    inner ℝ (fderiv ℝ (ruledMap d.γ d.E) p v) (fderiv ℝ d.rawGaussMap p w) =
      -(p 1 * d.τ (p 0) *
          (ruledLambda d.τ (p 0) + p 1 * ruledD d.k d.τ (p 0)) * v 0 * w 0 +
        d.τ (p 0) * (v 0 * w 1 + v 1 * w 0)) /
        Real.sqrt (ruledEnergy (d.k (p 0)) (d.τ (p 0)) (p 1)) := by
  have hX : ContDiff ℝ ∞ (ruledMap d.γ d.E) :=
    (d.smooth_γ.comp (contDiff_apply ℝ ℝ 0)).add
      ((contDiff_apply ℝ ℝ 1).smul (d.smooth_E.comp (contDiff_apply ℝ ℝ 0)))
  have hN := periodicRuledFrame_rawGaussMap_contDiff d
  have hn : ∀ q ∈ (univ : Set Coord),
      IsUnitNormalAt (ruledMap d.γ d.E) (d.rawGaussMap q) q := by
    intro q _
    exact ruled_isUnitNormal (d.deriv_γ (q 0)) (d.deriv_E (q 0))
      (d.orthonormal (q 0)) (d.torsion_ne_zero (q 0))
  have hpairs (i j : Fin 2) :
      inner ℝ (coordPartial i (ruledMap d.γ d.E) p) (coordPartial j d.rawGaussMap p) =
        -secondFundamental (ruledMap d.γ d.E) (d.rawGaussMap p) p j i := by
    rw [real_inner_comm]
    exact gaussMap_partial_pairing hX.contDiffOn hN.contDiffOn isOpen_univ hn
      (mem_univ p) j i
  have h00 : secondFundamental (ruledMap d.γ d.E) (d.rawGaussMap p) p 0 0 =
      p 1 * d.τ (p 0) *
        (ruledLambda d.τ (p 0) + p 1 * ruledD d.k d.τ (p 0)) /
        Real.sqrt (ruledEnergy (d.k (p 0)) (d.τ (p 0)) (p 1)) := by
    simpa only [PeriodicRuledFrame.rawGaussMap, ruledLambda, ruledD] using
      ruled_second_form_ss d.deriv_γ d.deriv_E (d.deriv_T (p 0)) (d.deriv_n (p 0))
        ((d.smooth_k.differentiable (by simp) (p 0)).hasDerivAt)
        ((d.smooth_τ.differentiable (by simp) (p 0)).hasDerivAt)
        (d.orthonormal (p 0)) (d.torsion_ne_zero (p 0))
  have hmixed :
      secondFundamental (ruledMap d.γ d.E) (d.rawGaussMap p) p 0 1 =
        d.τ (p 0) / Real.sqrt (ruledEnergy (d.k (p 0)) (d.τ (p 0)) (p 1)) ∧
      secondFundamental (ruledMap d.γ d.E) (d.rawGaussMap p) p 1 1 = 0 :=
    ruled_mixed_and_ruling_second_form d.deriv_γ d.deriv_E (d.orthonormal (p 0))
  have h10 : secondFundamental (ruledMap d.γ d.E) (d.rawGaussMap p) p 1 0 =
      d.τ (p 0) / Real.sqrt (ruledEnergy (d.k (p 0)) (d.τ (p 0)) (p 1)) := by
    rw [secondFundamental, coordPartial_comm hX.contDiffOn isOpen_univ (mem_univ p) 1 0]
    exact hmixed.1
  rw [fderiv_two_coordinates, fderiv_two_coordinates,
    inner_add_left, inner_add_right, inner_add_right]
  simp only [real_inner_smul_left, real_inner_smul_right]
  rw [hpairs 0 0, hpairs 0 1, hpairs 1 0, hpairs 1 1,
    h00, hmixed.1, h10, hmixed.2]
  simp only [div_eq_mul_inv]
  ring

/-- Exact signed tangential entry in the actual interior ruled coordinates. -/
theorem identityBand_interior_tangential_pairing {L : ℝ}
    (d : PeriodicRuledFrame L) (p : Coord) :
    inner ℝ
      (fderiv ℝ (ruledMap d.γ d.E) p (Pi.single 0 1 : Coord))
      (fderiv ℝ d.rawGaussMap p (Pi.single 0 1 : Coord)) =
      -(p 1 * d.τ (p 0) *
        (ruledLambda d.τ (p 0) + p 1 * ruledD d.k d.τ (p 0))) /
        Real.sqrt (ruledEnergy (d.k (p 0)) (d.τ (p 0)) (p 1)) := by
  simpa using identityBand_interior_differential_pairing d p
    (Pi.single 0 1 : Coord) (Pi.single 0 1 : Coord)

/-- The actual speed derivative gives the physical lambda coefficient. -/
theorem identityBand_physical_lambda {a ψ : ℝ → ℝ} {s a' : ℝ}
    (ha : HasDerivAt a a' (ψ s)) (hpos : 0 < a (ψ s))
    (hψ : HasDerivAt ψ (a (ψ s))⁻¹ s) :
    ruledLambda (normalLoopPhysicalTau a ψ) s = -a' / (a (ψ s))^2 := by
  have hapsi := ha.comp s hψ
  have ht : HasDerivAt (normalLoopPhysicalTau a ψ)
      (-(-(a' * (a (ψ s))⁻¹) / (a (ψ s))^2)) s :=
    (hapsi.inv hpos.ne').neg
  rw [ruledLambda, ht.deriv]
  dsimp [normalLoopPhysicalTau]
  field_simp [hpos.ne'] <;> ring

/-- The signed tangential entry for the same corrected physical frame.
Its numerator is u*(-a_r+u*kappa_r), so no universal interior sign is claimed. -/
theorem identityBand_interior_tangential_pairing_physical {L : ℝ}
    (d : PeriodicRuledFrame L) {a κ ψ : ℝ → ℝ} {s u a' κ' : ℝ}
    (hk : d.k = normalLoopPhysicalK a κ ψ)
    (hτ : d.τ = normalLoopPhysicalTau a ψ)
    (ha : HasDerivAt a a' (ψ s)) (hκ : HasDerivAt κ κ' (ψ s))
    (hpos : 0 < a (ψ s)) (hψ : HasDerivAt ψ (a (ψ s))⁻¹ s) :
    inner ℝ
      (fderiv ℝ (ruledMap d.γ d.E) (![s, u] : Coord) (Pi.single 0 1 : Coord))
      (fderiv ℝ d.rawGaussMap (![s, u] : Coord) (Pi.single 0 1 : Coord)) =
      u * (-a' + u * κ') /
        ((a (ψ s))^3 * Real.sqrt (ruledEnergy (d.k s) (d.τ s) u)) := by
  have hLambda : ruledLambda d.τ s = -a' / (a (ψ s))^2 := by
    rw [hτ]
    exact identityBand_physical_lambda ha hpos hψ
  have hD : ruledD d.k d.τ s = κ' / (a (ψ s))^2 := by
    rw [hk, hτ]
    exact normalLoop_physical_D ha hκ hpos hψ
  have ht : d.τ s = -(a (ψ s))⁻¹ := by rw [hτ]; rfl
  have hnum : -(u * d.τ s * (ruledLambda d.τ s + u * ruledD d.k d.τ s)) =
      u * (-a' + u * κ') / (a (ψ s))^3 := by
    rw [ht, hLambda, hD]
    field_simp [hpos.ne'] <;> ring
  rw [identityBand_interior_tangential_pairing]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hnum, div_div]

/-- Every fixed positive central transverse direction stays positive on
an actual open neighborhood, by continuity of the actual first derivatives. -/
theorem identityBand_central_positive_transverse_neighborhood {L : ℝ}
    (d : PeriodicRuledFrame L) (s : ℝ) {a t : ℝ} (ha : 0 < a)
    (hτ : d.τ s = -a⁻¹) (ht : 0 < t) :
    ∃ U : Set Coord, IsOpen U ∧ (![s, 0] : Coord) ∈ U ∧
      ∀ p ∈ U, 0 < inner ℝ
        (fderiv ℝ (ruledMap d.γ d.E) p (a • ![1, t]))
        (fderiv ℝ d.rawGaussMap p (a • ![1, t])) := by
  have hX : ContDiff ℝ ∞ (ruledMap d.γ d.E) :=
    (d.smooth_γ.comp (contDiff_apply ℝ ℝ 0)).add
      ((contDiff_apply ℝ ℝ 1).smul (d.smooth_E.comp (contDiff_apply ℝ ℝ 0)))
  have hN := periodicRuledFrame_rawGaussMap_contDiff d
  let B : Coord → ℝ := fun p => inner ℝ
    (fderiv ℝ (ruledMap d.γ d.E) p (a • ![1, t]))
    (fderiv ℝ d.rawGaussMap p (a • ![1, t]))
  have hc : Continuous B :=
    ((hX.continuous_fderiv_apply (by simp)).comp
      (continuous_id.prodMk continuous_const)).inner
      ((hN.continuous_fderiv_apply (by simp)).comp
        (continuous_id.prodMk continuous_const))
  exact ⟨{p | 0 < B p}, isOpen_lt continuous_const hc,
    (identityBand_central_positive_transverse_pairing d s ha hτ ht).2,
    fun _ hp => hp⟩

end
end TightVer401

