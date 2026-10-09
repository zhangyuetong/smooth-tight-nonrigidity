import TightVer401.SphereSupportGradient

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

theorem support_height_partial {X Q : Coord → Ambient} {U : Set Coord}
    (hX : ContDiffOn ℝ ∞ X U) (hQ : ContDiffOn ℝ ∞ Q U) (hU : IsOpen U)
    {p : Coord} (hp : p ∈ U) (hn : IsUnitNormalAt X (Q p) p) (i : Fin 2) :
    coordPartial i (fun q => inner ℝ (X q) (Q q)) p = inner ℝ (X p) (coordPartial i Q p) := by
  have hdX := ((hX p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hdQ := ((hQ p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  change fderiv ℝ (fun q => inner ℝ (X q) (Q q)) p (Pi.single i 1) = _
  rw [fderiv_inner_apply ℝ hdX hdQ, hn.2 _, add_zero]
  rfl

theorem sphereSupportMap_converse_local {g : MetricField} {X Q : Coord → Ambient} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hQ : IsometricOn g Q U) (hX : ContDiffOn ℝ ∞ X U)
    (hU : IsOpen U) (hn : ∀ q ∈ U, IsUnitNormalAt X (Q q) q) :
    EqOn X (sphereSupportMap g Q (fun q => inner ℝ (X q) (Q q))) U := by
  intro p hp
  let H : Coord → ℝ := fun q => inner ℝ (X q) (Q q)
  let A := sphereSupportMap g Q H
  have hunit : ∀ q ∈ U, inner ℝ (Q q) (Q q) = 1 := fun q hq => (hn q hq).1
  have hQn := sphere_isUnitNormal hQ.1 hU hp hunit
  have hApair (i : Fin 2) : inner ℝ (A p) (coordPartial i Q p) = coordPartial i H p := by
    have horth : inner ℝ (Q p) (coordPartial i Q p) = 0 := by
      rw [real_inner_comm]
      exact hQn.2 _
    simp only [A, sphereSupportMap, inner_add_left, real_inner_smul_left, horth,
      mul_zero, add_zero, sphereGradient_pairing hg hQ hp]
  have hwt (i : Fin 2) : inner ℝ (coordPartial i Q p) (X p - A p) = 0 := by
    rw [real_inner_comm, inner_sub_left, hApair,
      support_height_partial hX hQ.1 hU hp (hn p hp)]
    exact sub_self _
  have hnormal : inner ℝ (Q p) (X p - A p) = 0 := by
    rw [inner_sub_right, real_inner_comm (X p) (Q p), real_inner_comm (A p) (Q p)]
    rw [sphereSupportMap_height hQ.1 hU hp hunit]
    exact sub_self _
  have heq := normal_eq_inner_smul_of_independent_tangents
    (fun i => coordPartial i Q p) (isometric_tangents_independent hg hQ hp)
    (Q p) (X p - A p) (hunit p hp) (fun i => hQn.2 _) hwt
  rw [hnormal, zero_smul] at heq
  exact sub_eq_zero.mp heq

end
end TightVer401
