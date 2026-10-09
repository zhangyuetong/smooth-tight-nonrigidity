import TightVer401.ProtectedTorusPositiveGaussPhase

/-! The genuine cosine-height diffeomorphism on the open convex phase.
The inverse is explicit and smooth on the actual interior interval. -/
open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
open Set Filter _root_.Manifold OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false

def protectedTorusPositiveGaussHeight (h φ : ℝ) : ℝ := -h * Real.cos φ

def protectedTorusPositiveGaussHeightInverse (h z : ℝ) : ℝ :=
  2 * Real.pi - Real.arccos (-z / h)

theorem protectedTorusPositiveGaussHeight_mem {h φ : ℝ} (hh : 0 < h)
    (hφ : φ ∈ Ioo Real.pi (2 * Real.pi)) :
    protectedTorusPositiveGaussHeight h φ ∈ Ioo (-h) h := by
  have ht : 2 * Real.pi - φ ∈ Ioo (0 : ℝ) Real.pi :=
    ⟨by linarith [hφ.2], by linarith [hφ.1]⟩
  have hc := Real.cosPartialHomeomorph.map_source ht
  change Real.cos (2 * Real.pi - φ) ∈ Ioo (-1 : ℝ) 1 at hc
  rw [Real.cos_two_pi_sub] at hc
  change -h * Real.cos φ ∈ Ioo (-h) h
  constructor <;> nlinarith [hc.1, hc.2]

theorem protectedTorusPositiveGaussHeightInverse_ratio {h z : ℝ}
    (hh : 0 < h) (hz : z ∈ Ioo (-h) h) : -z / h ∈ Ioo (-1 : ℝ) 1 := by
  constructor
  · exact (lt_div_iff₀ hh).mpr (by linarith [hz.2])
  · exact (div_lt_iff₀ hh).mpr (by linarith [hz.1])

theorem protectedTorusPositiveGaussHeightInverse_mem {h z : ℝ}
    (hh : 0 < h) (hz : z ∈ Ioo (-h) h) :
    protectedTorusPositiveGaussHeightInverse h z ∈ Ioo Real.pi (2 * Real.pi) := by
  have hr := protectedTorusPositiveGaussHeightInverse_ratio hh hz
  have h0 := Real.arccos_pos.mpr hr.2
  have hpi := Real.arccos_lt_pi.mpr hr.1
  constructor <;> dsimp [protectedTorusPositiveGaussHeightInverse] <;> linarith

theorem protectedTorusPositiveGaussHeight_left {h φ : ℝ} (hh : 0 < h)
    (hφ : φ ∈ Ioo Real.pi (2 * Real.pi)) :
    protectedTorusPositiveGaussHeightInverse h
      (protectedTorusPositiveGaussHeight h φ) = φ := by
  have hr : -(-h * Real.cos φ) / h = Real.cos φ := by field_simp [hh.ne']
  dsimp [protectedTorusPositiveGaussHeightInverse, protectedTorusPositiveGaussHeight]
  rw [hr, ← Real.cos_two_pi_sub φ,
    Real.arccos_cos (by linarith [hφ.2]) (by linarith [hφ.1])]
  ring

theorem protectedTorusPositiveGaussHeight_right {h z : ℝ} (hh : 0 < h)
    (hz : z ∈ Ioo (-h) h) :
    protectedTorusPositiveGaussHeight h
      (protectedTorusPositiveGaussHeightInverse h z) = z := by
  have hr := protectedTorusPositiveGaussHeightInverse_ratio hh hz
  dsimp [protectedTorusPositiveGaussHeightInverse, protectedTorusPositiveGaussHeight]
  rw [Real.cos_two_pi_sub, Real.cos_arccos hr.1.le hr.2.le]
  field_simp [hh.ne']
  <;> ring

theorem protectedTorusPositiveGaussHeight_contDiff (h : ℝ) :
    ContDiff ℝ ∞ (protectedTorusPositiveGaussHeight h) :=
  contDiff_const.mul Real.contDiff_cos

theorem protectedTorusPositiveGaussHeightInverse_contDiffOn {h : ℝ} (hh : 0 < h) :
    ContDiffOn ℝ ∞ (protectedTorusPositiveGaussHeightInverse h) (Ioo (-h) h) := by
  intro z hz
  have hr := protectedTorusPositiveGaussHeightInverse_ratio hh hz
  exact (contDiffAt_const.sub
    ((Real.contDiffAt_arccos (ne_of_gt hr.1) (ne_of_lt hr.2)).comp z
      (contDiffAt_id.neg.div_const h))).contDiffWithinAt

/-- Both directions are actual smooth scalar maps on the precise open intervals. -/
def protectedTorusPositiveGaussHeightDiffeomorph {h : ℝ} (hh : 0 < h) :
    Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      protectedTorusPositiveGaussPhaseDomain (parabolicConvexClosureHeightDomain h) ∞ where
  toFun φ := ⟨protectedTorusPositiveGaussHeight h φ,
    protectedTorusPositiveGaussHeight_mem hh φ.property⟩
  invFun z := ⟨protectedTorusPositiveGaussHeightInverse h z,
    protectedTorusPositiveGaussHeightInverse_mem hh z.property⟩
  left_inv φ := Subtype.ext (protectedTorusPositiveGaussHeight_left hh φ.property)
  right_inv z := Subtype.ext (protectedTorusPositiveGaussHeight_right hh z.property)
  contMDiff_toFun := (ContMDiff.subtypeVal_comp_iff
    (parabolicConvexClosureHeightDomain h) _).mp
      ((protectedTorusPositiveGaussHeight_contDiff h).contMDiff.comp
        (contMDiff_subtype_val (I := 𝓘(ℝ, ℝ))
          (U := protectedTorusPositiveGaussPhaseDomain)))
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff protectedTorusPositiveGaussPhaseDomain _).mp
    intro z
    exact contMDiffAt_subtype_iff.mpr
      ((protectedTorusPositiveGaussHeightInverse_contDiffOn hh).contDiffAt
        (isOpen_Ioo.mem_nhds z.property)).contMDiffAt

end
end TightVer401
