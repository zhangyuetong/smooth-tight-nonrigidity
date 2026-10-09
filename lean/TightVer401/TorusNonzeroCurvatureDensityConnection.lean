import TightVer401.ClassicalExternal
import TightVer401.PeriodProjectionDifferential
import Mathlib.Topology.Perfect
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Order.Interval.Set.Infinite

/-! The literal native torus off its two phase seams is dense. This is only a
source-topology connection: actual surface curvature off those seams is an
explicit producer input, and the resulting dense nonzero-curvature set refers
to the SAME native preferred-chart curvature of the SAME actual map. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- Complement of the literal south (0) and north (pi) phase seams. -/
def protectedTorusOffPhaseSeams : Set NonrigidTorusSource :=
  {q | q.2 ≠ 0 ∧ q.2 ≠ periodProjection (2 * Real.pi) Real.pi}

/-- Removing those two phase points leaves a dense set in the actual quotient
circle, and hence in the second factor of the native product source. -/
theorem protectedTorusOffPhaseSeams_dense : Dense protectedTorusOffPhaseSeams := by
  letI : Infinite (Ico (0 : ℝ) (0 + 2 * Real.pi)) :=
    Set.Ico.infinite (by simpa using Real.two_pi_pos)
  letI : Infinite (AddCircle (2 * Real.pi)) :=
    (AddCircle.equivIco (2 * Real.pi) 0).infinite_iff.mpr inferInstance
  letI : PerfectSpace (AddCircle (2 * Real.pi)) := inferInstance
  have hcircle : Dense
      ({(0 : AddCircle (2 * Real.pi)), periodProjection (2 * Real.pi) Real.pi}ᶜ :
        Set (AddCircle (2 * Real.pi))) := by
    have hfinite :
        ({(0 : AddCircle (2 * Real.pi)), periodProjection (2 * Real.pi) Real.pi} :
          Set (AddCircle (2 * Real.pi))).Finite := by simp
    have hd : Dense ((univ : Set (AddCircle (2 * Real.pi))) \
        {(0 : AddCircle (2 * Real.pi)), periodProjection (2 * Real.pi) Real.pi}) :=
      dense_univ.sdiff_finite hfinite
    have hset :
        (univ : Set (AddCircle (2 * Real.pi))) \
            {(0 : AddCircle (2 * Real.pi)), periodProjection (2 * Real.pi) Real.pi} =
          ({(0 : AddCircle (2 * Real.pi)), periodProjection (2 * Real.pi) Real.pi}ᶜ :
            Set (AddCircle (2 * Real.pi))) := by
      ext q
      simp only [mem_diff, mem_univ, true_and, mem_compl_iff]
    rw [hset] at hd
    exact hd
  have hproduct := (dense_univ : Dense (univ : Set (AddCircle (2 * Real.pi)))).prod hcircle
  have heq :
      (univ : Set (AddCircle (2 * Real.pi))) ×ˢ
        ({(0 : AddCircle (2 * Real.pi)), periodProjection (2 * Real.pi) Real.pi}ᶜ :
          Set (AddCircle (2 * Real.pi))) = protectedTorusOffPhaseSeams := by
    ext q
    simp [protectedTorusOffPhaseSeams]
  exact heq ▸ hproduct

/-- The original geometric producer need only prove actual native K nonzero
away from its two literal seams. Density then follows from the source topology. -/
theorem nativeTorus_nonzero_curvature_dense_of_off_seams
    (F : NonrigidTorusSource → Ambient)
    (hK : ∀ q : NonrigidTorusSource, q.2 ≠ 0 →
      q.2 ≠ periodProjection (2 * Real.pi) Real.pi → nativeTorusChartCurvature F q ≠ 0) :
    Dense {q : NonrigidTorusSource | nativeTorusChartCurvature F q ≠ 0} := by
  apply protectedTorusOffPhaseSeams_dense.mono
  intro q hq
  exact hK q hq.1 hq.2

end
end TightVer401
