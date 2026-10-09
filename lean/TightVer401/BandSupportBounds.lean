import TightVer401.PeriodicBandProfile

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry

theorem compact_band_support_uniform_bounds {A V : Type*} [TopologicalSpace A] [Zero V]
    {b : ℝ} {Y : A × Ioo (0 : ℝ) b → V} (hb : 0 < b) (hY : HasCompactSupport Y) :
    ∃ lower upper : ℝ, 0 < lower ∧ lower < upper ∧ upper < b ∧
      ∀ p ∈ tsupport Y, lower ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ upper := by
  have hc : Continuous (fun p : A × Ioo (0 : ℝ) b => (p.2 : ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  by_cases hne : (tsupport Y).Nonempty
  · obtain ⟨p, hp, hmin⟩ := hY.exists_isMinOn hne hc.continuousOn
    obtain ⟨q, hq, hmax⟩ := hY.exists_isMaxOn hne hc.continuousOn
    have hlo := p.2.property.1
    have hhi := q.2.property.2
    have hle : (p.2 : ℝ) ≤ (q.2 : ℝ) := hmin hq
    refine ⟨(p.2 : ℝ) / 2, ((q.2 : ℝ) + b) / 2, by linarith, by linarith,
      by linarith, ?_⟩
    intro r hr
    have hrlo : (p.2 : ℝ) ≤ (r.2 : ℝ) := hmin hr
    have hrhi : (r.2 : ℝ) ≤ (q.2 : ℝ) := hmax hr
    constructor <;> linarith
  · refine ⟨b / 3, 2 * b / 3, by linarith, by linarith, by linarith, ?_⟩
    intro p hp
    exact False.elim (hne ⟨p, hp⟩)

end
end TightVer401
