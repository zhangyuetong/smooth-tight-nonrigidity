import TightVer401.RevolutionEndGaussImage

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false

def revolutionHeightInverse {q : ℝ → ℝ} {H : ℝ}
    (hq : ContDiff ℝ ∞ q) (hslope : Tendsto (deriv q) atTop atTop) (y : ℝ) : ℝ :=
  if hy : y ∈ Ico (revolutionNormalHeight q H) 1 then
    Classical.choose (revolutionNormalHeight_exists_preimage hq hslope hy)
  else H

theorem revolutionHeightInverse_spec {q : ℝ → ℝ} {H y : ℝ}
    (hq : ContDiff ℝ ∞ q) (hslope : Tendsto (deriv q) atTop atTop)
    (hy : y ∈ Ico (revolutionNormalHeight q H) 1) :
    H ≤ revolutionHeightInverse (H := H) hq hslope y ∧
      revolutionNormalHeight q (revolutionHeightInverse (H := H) hq hslope y) = y := by
  simp only [revolutionHeightInverse, dif_pos hy]
  exact Classical.choose_spec (revolutionNormalHeight_exists_preimage hq hslope hy)

theorem revolutionHeightInverse_left {q : ℝ → ℝ} {H z : ℝ}
    (hq : ContDiff ℝ ∞ q) (hc : ∀ z ∈ Ici H, 0 < deriv (deriv q) z)
    (hs : ∀ z ∈ Ici H, 0 < deriv q z)
    (hslope : Tendsto (deriv q) atTop atTop) (hz : H ≤ z) :
    revolutionHeightInverse (H := H) hq hslope (revolutionNormalHeight q z) = z := by
  have hy : revolutionNormalHeight q z ∈ Ico (revolutionNormalHeight q H) 1 := by
    exact ⟨(revolutionNormalHeight_strictMonoOn hq hc).monotoneOn
      (by simp) hz hz, (revolutionNormalHeight_mem_Ioo (hs z hz)).2⟩
  have he := revolutionHeightInverse_spec hq hslope hy
  exact (revolutionNormalHeight_strictMonoOn hq hc).injOn he.1 hz he.2

def revolutionEndGaussInverse {q : ℝ → ℝ} {H : ℝ}
    (hq : ContDiff ℝ ∞ q) (hslope : Tendsto (deriv q) atTop atTop)
    (n : revolutionEndGaussCap q H) : AddCircle (2 * Real.pi) × Ici H :=
  (revolutionGaussAngle n.val,
    ⟨revolutionHeightInverse (H := H) hq hslope (n.val.val 2),
      (revolutionHeightInverse_spec hq hslope n.property).1⟩)

theorem revolutionEndGaussInverse_right {q : ℝ → ℝ} {H : ℝ}
    (hq : ContDiff ℝ ∞ q) (hs : ∀ z ∈ Ici H, 0 < deriv q z)
    (hslope : Tendsto (deriv q) atTop atTop) (n : revolutionEndGaussCap q H) :
    revolutionEndGauss q H (revolutionEndGaussInverse hq hslope n) = n.val := by
  apply Subtype.ext
  exact revolutionEndCircleNormal_angle n.val _
    (hs _ (revolutionHeightInverse_spec hq hslope n.property).1)
    (revolutionHeightInverse_spec hq hslope n.property).2

theorem revolutionEndGaussInverse_left {q : ℝ → ℝ} {H : ℝ}
    (hq : ContDiff ℝ ∞ q) (hc : ∀ z ∈ Ici H, 0 < deriv (deriv q) z)
    (hs : ∀ z ∈ Ici H, 0 < deriv q z)
    (hslope : Tendsto (deriv q) atTop atTop) (p : AddCircle (2 * Real.pi) × Ici H) :
    revolutionEndGaussInverse hq hslope
      ⟨revolutionEndGauss q H p, revolutionEndGauss_mem_cap hq hc hs p⟩ = p := by
  apply revolutionEndGauss_injective hq hc
  exact revolutionEndGaussInverse_right hq hs hslope _

def revolutionEndGaussEquiv {q : ℝ → ℝ} {H : ℝ}
    (hq : ContDiff ℝ ∞ q) (hc : ∀ z ∈ Ici H, 0 < deriv (deriv q) z)
    (hs : ∀ z ∈ Ici H, 0 < deriv q z)
    (hslope : Tendsto (deriv q) atTop atTop) :
    (AddCircle (2 * Real.pi) × Ici H) ≃ revolutionEndGaussCap q H where
  toFun p := ⟨revolutionEndGauss q H p, revolutionEndGauss_mem_cap hq hc hs p⟩
  invFun := revolutionEndGaussInverse hq hslope
  left_inv := revolutionEndGaussInverse_left hq hc hs hslope
  right_inv n := Subtype.ext (revolutionEndGaussInverse_right hq hs hslope n)

theorem revolutionEndGaussInverse_boundary {q : ℝ → ℝ} {H : ℝ}
    (hq : ContDiff ℝ ∞ q) (hc : ∀ z ∈ Ici H, 0 < deriv (deriv q) z)
    (hs : ∀ z ∈ Ici H, 0 < deriv q z)
    (hslope : Tendsto (deriv q) atTop atTop) (n : revolutionEndGaussCap q H)
    (hn : n.val.val 2 = revolutionNormalHeight q H) :
    (revolutionEndGaussInverse hq hslope n).2.val = H := by
  change revolutionHeightInverse (H := H) hq hslope (n.val.val 2) = H
  rw [hn]
  exact revolutionHeightInverse_left hq hc hs hslope le_rfl

theorem revolutionEndGaussInverse_interior {q : ℝ → ℝ} {H : ℝ}
    (hq : ContDiff ℝ ∞ q) (hc : ∀ z ∈ Ici H, 0 < deriv (deriv q) z)
    (hslope : Tendsto (deriv q) atTop atTop) (n : revolutionEndGaussCap q H)
    (hn : revolutionNormalHeight q H < n.val.val 2) :
    H < (revolutionEndGaussInverse hq hslope n).2.val := by
  have he := revolutionHeightInverse_spec hq hslope n.property
  apply lt_of_le_of_ne he.1
  intro hh
  rw [← hh] at he
  exact (ne_of_lt hn) he.2

end
end TightVer401
