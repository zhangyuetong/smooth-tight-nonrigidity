import TightVer401.SmoothingTubeGradient
import TightVer401.SmoothingTubeC1
import TightVer401.SeamChartContinuity

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

theorem smoothing_compact_inverseJacobian_bound {Φ : Coord → Coord}
    (hΦ : ContDiff ℝ ∞ Φ) {S : Set Coord} (hS : IsCompact S)
    (hJ : ∀ p ∈ S, (seamCoordinateJacobian Φ p).det ≠ 0) :
    ∃ M : ℝ, 0 < M ∧ ∀ p ∈ S, ∀ i a : Fin 2,
      |((seamCoordinateJacobian Φ p).transpose)⁻¹ i a| ≤ M := by
  have hc : ContinuousOn (fun p => ((seamCoordinateJacobian Φ p).transpose)⁻¹) S := by
    intro p hp
    apply ContinuousAt.continuousWithinAt
    apply (continuousAt_matrix_inv (seamCoordinateJacobian Φ p).transpose ?_).comp
      (f := fun q : Coord => (seamCoordinateJacobian Φ q).transpose)
      (seamCoordinateJacobian_continuous hΦ |>.matrix_transpose).continuousAt
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ (by simpa only [Matrix.det_transpose] using hJ p hp)
  obtain ⟨C,hC⟩ := hS.exists_bound_of_continuousOn hc
  let M := max 1 C
  refine ⟨M,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro p hp i a
  let A : Matrix (Fin 2) (Fin 2) ℝ := ((seamCoordinateJacobian Φ p).transpose)⁻¹
  change |A i a| ≤ M
  exact (norm_le_pi_norm (A i) a).trans
    ((norm_le_pi_norm A i).trans
      ((hC p hp).trans (le_max_right 1 C)))

theorem smoothing_matrix_vector_bound {A : Matrix (Fin 2) (Fin 2) ℝ} {v : Coord}
    {M η : ℝ} (hM : 0 ≤ M) (hη : 0 ≤ η) (hA : ∀ i a, |A i a| ≤ M) (hv : ‖v‖ ≤ η) :
    ‖A *ᵥ v‖ ≤ 2*M*η := by
  have hb (a : Fin 2) : |v a| ≤ η := (norm_le_pi_norm v a).trans hv
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2*M*η)).mpr
  intro i
  simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_two,Real.norm_eq_abs]
  calc
    _ ≤ |A i 0*v 0|+|A i 1*v 1| := abs_add_le _ _
    _ ≤ M*η+M*η := by
      rw [abs_mul,abs_mul]
      exact add_le_add (mul_le_mul (hA i 0) (hb 0) (abs_nonneg _) hM)
        (mul_le_mul (hA i 1) (hb 1) (abs_nonneg _) hM)
    _ = 2*M*η := by ring

theorem seamNormalCoordinates_mem_openTube {L : ℝ} {γ : ℝ → ℂ}
    (hL : Function.Periodic γ L) {r : ℝ} {p : Coord} (hp : |p 1| < r) :
    seamNormalCoordinates γ p ∈ seamNormalOpenTube γ hL r := by
  refine ⟨(periodProjection L (p 0),p 1),⟨mem_univ _,abs_lt.mp hp⟩,?_⟩
  rw [seamNormalNative_coe]
  congr 1
  ext i
  fin_cases i <;> rfl

/-- A compactly obtained actual Jacobian bound uniformly transports C¹ errors
between the real periodic formulas and actual planar tube potentials. -/
theorem smoothing_tube_compact_gradient_error {L : ℝ} {γ : ℝ → ℂ}
    (hγ : ContDiff ℝ ∞ γ) (hL : Function.Periodic γ L) {r : ℝ}
    (hi : InjOn (seamNormalNative γ hL) (univ ×ˢ Icc (-r) r))
    (hJ : ∀ s t : ℝ, |t| ≤ r → (seamCoordinateJacobian (seamNormalCoordinates γ) (![s,t])).det ≠ 0)
    {S : Set Coord} (hS : IsCompact S) (hSr : ∀ p ∈ S, |p 1| < r) :
    ∃ M : ℝ, 0 < M ∧ ∀ H O : Coord → ℝ, ∀ hPH : ∀ p, H (smoothingSeamShift L p)=H p,
      ∀ hPO : ∀ p, O (smoothingSeamShift L p)=O p,
      ContDiff ℝ 1 H → ContDiff ℝ 1 O → ∀ η : ℝ, 0 ≤ η →
      (∀ p ∈ S, ‖planarGradient H p-planarGradient O p‖ ≤ η) → ∀ p ∈ S,
      ‖planarGradient (seamNormalTubePotential γ hL r H hPH) (seamNormalCoordinates γ p)-
        planarGradient (seamNormalTubePotential γ hL r O hPO) (seamNormalCoordinates γ p)‖ ≤ 2*M*η := by
  have hj (p : Coord) (hp : |p 1| < r) : (seamCoordinateJacobian (seamNormalCoordinates γ) p).det ≠ 0 := by
    have hv : (![p 0,p 1] : Coord)=p := by ext i; fin_cases i <;> rfl
    have he := hJ (p 0) (p 1) hp.le
    simpa only [hv] using he
  obtain ⟨M,hM,hB⟩ := smoothing_compact_inverseJacobian_bound (seamNormalCoordinates_contDiff hγ) hS
    (fun p hp => hj p (hSr p hp))
  refine ⟨M,hM,fun H O hPH hPO hH hO η hη hclose p hp => ?_⟩
  have hpTube := seamNormalCoordinates_mem_openTube hL (hSr p hp)
  have hTubeOpen := seamNormalOpenTube_isOpen hγ hL hJ
  have hdH := ((seamNormalTubePotential_contDiffOn_one hγ hL hi hJ hH hPH).contDiffAt
    (hTubeOpen.mem_nhds hpTube)).differentiableAt (by norm_num)
  have hdO := ((seamNormalTubePotential_contDiffOn_one hγ hL hi hJ hO hPO).contDiffAt
    (hTubeOpen.mem_nhds hpTube)).differentiableAt (by norm_num)
  rw [seamNormalTubePotential_gradient hγ hL H hPH hi (hSr p hp) (hj p (hSr p hp)) hdH,
    seamNormalTubePotential_gradient hγ hL O hPO hi (hSr p hp) (hj p (hSr p hp)) hdO,
    ← Matrix.mulVec_sub]
  exact smoothing_matrix_vector_bound hM.le hη (hB p hp) (hclose p hp)

end
end TightVer401
