import TightVer401.SmoothingSeamPeriodicity
import TightVer401.PeriodicCircleFunctions

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry OAI.RawQuotientLie
open scoped ContDiff Manifold

theorem smoothingCylinderSlice_periodic (L : ℝ) (F : Coord → ℝ)
    (hperiod : ∀ p, F (smoothingSeamShift L p)=F p) (t : ℝ) :
    Function.Periodic (fun s : ℝ => F (![s,t])) L := by
  intro s
  exact hperiod (![s,t])

def smoothingCylinderPotential (L : ℝ) (F : Coord → ℝ)
    (hperiod : ∀ p, F (smoothingSeamShift L p)=F p) (q : AddCircle L × ℝ) : ℝ :=
  (smoothingCylinderSlice_periodic L F hperiod q.2).lift q.1

theorem smoothingCylinderPotential_coe (L : ℝ) (F : Coord → ℝ)
    (hperiod : ∀ p, F (smoothingSeamShift L p)=F p) (s t : ℝ) :
    smoothingCylinderPotential L F hperiod (periodProjection L s,t)=F (![s,t]) :=
  (smoothingCylinderSlice_periodic L F hperiod t).lift_coe s

/-- Joint native smoothness on the actual period circle times the normal line. -/
theorem smoothingCylinderPotential_contMDiff (L : ℝ) [Fact (0 < L)]
    {F : Coord → ℝ} (hF : ContDiff ℝ ∞ F)
    (hperiod : ∀ p, F (smoothingSeamShift L p)=F p) :
    letI smoothingCylinderPeriodCharted : ChartedSpace ℝ (AddCircle L) := periodCircleChartedSpace L
    ContMDiff (𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)) 𝓘(ℝ,ℝ) ∞ (smoothingCylinderPotential L F hperiod) := by
  letI smoothingCylinderPeriodCharted : ChartedSpace ℝ (AddCircle L) := periodCircleChartedSpace L
  intro q
  obtain ⟨s,hs⟩ := QuotientAddGroup.mk_surjective q.1
  have hs' : periodProjection L s=q.1 := hs
  rw [contMDiffAt_iff_source]
  have he : smoothingCylinderPotential L F hperiod ∘
      (extChartAt (𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)) q).symm =
      fun v : ℝ × ℝ => F (![s+v.1,v.2]) := by
    funext v
    rw [Function.comp_apply,extChartAt_prod]
    change smoothingCylinderPotential L F hperiod
      ((extChartAt 𝓘(ℝ,ℝ) q.1).symm v.1,v.2)=F (![s+v.1,v.2])
    rw [addQuotient_extChart_symm_apply (periodChart L) (periodChart_zero_target L)]
    have hc : (periodChart L) v.1=periodProjection L v.1 := rfl
    rw [hc,← hs',← map_add]
    exact smoothingCylinderPotential_coe L F hperiod _ _
  rw [he]
  have hc : ContDiff ℝ ∞ (fun v : ℝ × ℝ => F (![s+v.1,v.2])) := by
    apply hF.comp
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> simp <;> fun_prop
  exact hc.contMDiff.contMDiffAt.contMDiffWithinAt

end
end TightVer401
