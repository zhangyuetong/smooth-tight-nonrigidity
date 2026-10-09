import TightVer401.RuledCentralGaussDerivative
import TightVer401.CentralSupportInversePairing

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- Actual Gauss coordinates and the actual height reconstruct the ruled
surface. Evaluating its Hessian-plus-metric tensor in the spherical
orthonormal frame (E,T) gives the strictly positive mixed entry −1/τ. -/
theorem ruled_central_support_tensor {L : ℝ} (d : PeriodicRuledFrame L) (r : ℝ)
    (hτ : d.τ r < 0) :
    ∃ hw : d.n r ≠ 0, ∃ e : OpenPartialHomeomorph Coord Coord,
      (![r, 0] : Coord) ∈ e.source ∧ ContDiffOn ℝ ∞ e e.source ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ q ∈ e.source, d.rawGaussMap q = sphereHemisphere (d.n r) hw (e q)) ∧
      let Q := sphereHemisphere (d.n r) hw
      let g := inducedMetric Q
      let H : Coord → ℝ := fun y => inner ℝ (ruledMap d.γ d.E (e.symm y)) (Q y)
      let c := (-d.τ r)⁻¹
      let V : Fin 2 → Coord := ![
        fderiv ℝ e (![r, 0] : Coord) (c • (Pi.single 0 1 : Coord)),
        fderiv ℝ e (![r, 0] : Coord) (c • (Pi.single 1 1 : Coord))]
      (∀ y ∈ e.target, ruledMap d.γ d.E (e.symm y) = sphereSupportMap g Q H y) ∧
      (∀ i, fderiv ℝ Q (e (![r, 0] : Coord)) (V i) = (![d.E r, d.T r] : Fin 2 → Ambient) i) ∧
      (fun i j => sphereSupportTensorBilinear g H (e (![r, 0] : Coord)) (V i) (V j)) =
        !![0, c; c, 0] ∧ 0 < c := by
  let p : Coord := ![r, 0]
  let X := ruledMap d.γ d.E
  let N := d.rawGaussMap
  have hX : ContDiff ℝ ∞ X :=
    (d.smooth_γ.comp (contDiff_apply ℝ ℝ 0)).add
      ((contDiff_apply ℝ ℝ 1).smul (d.smooth_E.comp (contDiff_apply ℝ ℝ 0)))
  have hN := periodicRuledFrame_rawGaussMap_contDiff d
  have hn : ∀ q ∈ (univ : Set Coord), IsUnitNormalAt X (N q) q := by
    intro q _
    exact ruled_isUnitNormal (d.deriv_γ (q 0)) (d.deriv_E (q 0))
      (d.orthonormal (q 0)) (d.torsion_ne_zero (q 0))
  have hunit : ∀ q ∈ (univ : Set Coord), ‖N q‖ = 1 := by
    intro q hq
    have hh := (hn q hq).1
    rw [real_inner_self_eq_norm_sq] at hh
    nlinarith [norm_nonneg (N q)]
  have hzero : N p = d.n r := ruledNormal_zero (d.T r) (d.n r) (d.k r) (d.τ r)
  have hu : ‖d.n r‖ = 1 := by rw [← hzero]; exact hunit p (mem_univ p)
  have hw : d.n r ≠ 0 := norm_ne_zero_iff.mp (by rw [hu]; exact one_ne_zero)
  have hpos : 0 < inner ℝ (d.n r) (N p) := by
    rw [hzero, (d.orthonormal r).2.2.1]
    exact zero_lt_one
  obtain ⟨e, hep, heU, heI, hef, heN⟩ := gaussMap_exists_smooth_inverse_coordinates
    hN.contDiffOn isOpen_univ hunit
    (fun q _ => periodicRuledFrame_rawGaussMap_differential_injective d q)
    (d.n r) hw hu (p := p) (mem_univ p) hpos
  have heF : ContDiffOn ℝ ∞ e e.source := by
    intro q hq
    have hqpos : 0 < inner ℝ (d.n r) (N q) := by
      change 0 < inner ℝ (d.n r) (d.rawGaussMap q)
      rw [heN q hq]
      exact sphereHemisphere_inner_pos (d.n r) hw hu (e q)
    rw [hef]
    exact ((sphereHemisphereInverse_contDiffAt (d.n r) hw hqpos).comp q hN.contDiffAt).contDiffWithinAt
  have heD : DifferentiableAt ℝ e p :=
    ((heF p hep).contDiffAt (e.open_source.mem_nhds hep)).differentiableAt (by simp)
  let Q := sphereHemisphere (d.n r) hw
  let H : Coord → ℝ := fun y => inner ℝ (X (e.symm y)) (Q y)
  let c := (-d.τ r)⁻¹
  let v₀ : Coord := c • Pi.single 0 1
  let v₁ : Coord := c • Pi.single 1 1
  let V : Fin 2 → Coord := ![fderiv ℝ e p v₀, fderiv ℝ e p v₁]
  have hcn : -d.τ r ≠ 0 := neg_ne_zero.mpr (d.torsion_ne_zero r)
  have hc : c * (-d.τ r) = 1 := inv_mul_cancel₀ hcn
  have hN₀ : fderiv ℝ N p v₀ = d.E r := by
    rw [show v₀ = c • (Pi.single 0 1 : Coord) from rfl, map_smul]
    change c • coordPartial 0 d.rawGaussMap p = d.E r
    rw [periodicRuledFrame_rawGaussMap_central_partial_s, smul_smul, hc, one_smul]
  have hN₁ : fderiv ℝ N p v₁ = d.T r := by
    rw [show v₁ = c • (Pi.single 1 1 : Coord) from rfl, map_smul]
    change c • coordPartial 1 d.rawGaussMap p = d.T r
    rw [periodicRuledFrame_rawGaussMap_central_partial_u, smul_smul, hc, one_smul]
  have hX₀ : fderiv ℝ X p v₀ = c • d.T r := by
    rw [show v₀ = c • (Pi.single 0 1 : Coord) from rfl, map_smul]
    change c • coordPartial 0 (ruledMap d.γ d.E) p = _
    rw [(periodicRuledFrame_ruledMap_central_partials d r).1]
  have hX₁ : fderiv ℝ X p v₁ = c • d.E r := by
    rw [show v₁ = c • (Pi.single 1 1 : Coord) from rfl, map_smul]
    change c • coordPartial 1 (ruledMap d.γ d.E) p = _
    rw [(periodicRuledFrame_ruledMap_central_partials d r).2]
  have hNQ : N =ᶠ[𝓝 p] (Q ∘ e) := by
    filter_upwards [e.open_source.mem_nhds hep] with q hq
    exact heN q hq
  have hDN : fderiv ℝ N p = (fderiv ℝ Q (e p)).comp (fderiv ℝ e p) := by
    rw [hNQ.fderiv_eq]
    exact fderiv_comp p ((sphereHemisphere_contDiff (d.n r) hw hu).differentiable (by simp) _) heD
  have hframe : ∀ i, fderiv ℝ Q (e p) (V i) = (![d.E r, d.T r] : Fin 2 → Ambient) i := by
    intro i
    fin_cases i
    · exact (congrArg (fun D : Coord →L[ℝ] Ambient => D v₀) hDN).symm.trans hN₀
    · exact (congrArg (fun D : Coord →L[ℝ] Ambient => D v₁) hDN).symm.trans hN₁
  have hmatrix : (fun i j => sphereSupportTensorBilinear (inducedMetric Q) H (e p) (V i) (V j)) =
      !![0, c; c, 0] := by
    ext i j
    have hb (v z : Coord) : sphereSupportTensorBilinear (inducedMetric Q) H (e p)
        (fderiv ℝ e p v) (fderiv ℝ e p z) = inner ℝ (fderiv ℝ X p v) (fderiv ℝ N p z) :=
      supportInverse_bilinear_pairing hX.contDiffOn isOpen_univ hn
        (d.n r) hw hu e heU heI heN hep heD v z
    have hET : inner ℝ (d.E r) (d.T r) = 0 := by
      rw [real_inner_comm]
      exact (d.orthonormal r).2.2.2.1
    fin_cases i <;> fin_cases j
    · change sphereSupportTensorBilinear (inducedMetric Q) H (e p)
        (fderiv ℝ e p v₀) (fderiv ℝ e p v₀) = 0
      rw [hb v₀ v₀, hX₀, hN₀, real_inner_smul_left, (d.orthonormal r).2.2.2.1, mul_zero]
    · change sphereSupportTensorBilinear (inducedMetric Q) H (e p)
        (fderiv ℝ e p v₀) (fderiv ℝ e p v₁) = c
      rw [hb v₀ v₁, hX₀, hN₁, real_inner_smul_left, (d.orthonormal r).1, mul_one]
    · change sphereSupportTensorBilinear (inducedMetric Q) H (e p)
        (fderiv ℝ e p v₁) (fderiv ℝ e p v₀) = c
      rw [hb v₁ v₀, hX₁, hN₀, real_inner_smul_left, (d.orthonormal r).2.1, mul_one]
    · change sphereSupportTensorBilinear (inducedMetric Q) H (e p)
        (fderiv ℝ e p v₁) (fderiv ℝ e p v₁) = 0
      rw [hb v₁ v₁, hX₁, hN₁, real_inner_smul_left, hET, mul_zero]
  exact ⟨hw, e, hep, heF, heI, heN,
    support_reconstruction_from_inverse_coordinates hX.contDiffOn isOpen_univ hn
      (d.n r) hw hu e heU heI heN, hframe, hmatrix, inv_pos.mpr (neg_pos.mpr hτ)⟩

end
end TightVer401
