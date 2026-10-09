import TightVer401.ScalarFlowVariation
import OAI.Geometry.WeakMTW.Analysis.SmoothFlow

namespace TightVer401
noncomputable section
open Set Filter Metric OAI.SmoothLocal.Geometry
open OAI.WeakMTWGlobalSupport
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

def scalarFlowAutonomization (f : Coord → ℝ) (p : Coord) : Coord := ![1, f p]

theorem scalarFlowAutonomization_contDiffOn {f : Coord → ℝ} {W : Set Coord}
    (hf : ContDiffOn ℝ ∞ f W) : ContDiffOn ℝ ∞ (scalarFlowAutonomization f) W := by
  apply contDiffOn_pi.mpr
  intro i
  fin_cases i
  · exact contDiffOn_const
  · exact hf

theorem scalarFlowPeriod_exists_local_phase_flow {f : Coord → ℝ} {W : Set Coord}
    (hW : IsOpen W) (hf : ContDiffOn ℝ ∞ f W) {p : Coord} (hp : p ∈ W) :
    ∃ (D : Set (ℝ × Coord)) (Φ : ℝ × Coord → Coord),
      IsOpen D ∧ (0, p) ∈ D ∧ ContDiffOn ℝ ∞ Φ D ∧
      (∀ x, (0, x) ∈ D → Φ (0, x) = x) ∧
      ∀ q ∈ D, Φ q ∈ W ∧ HasDerivAt (fun t => Φ (t, q.2))
        (scalarFlowAutonomization f (Φ q)) q.1 :=
  SmoothFlow.exists_smooth_local_flow hW (scalarFlowAutonomization_contDiffOn hf) hp

theorem scalarFlowPeriod_finite_positive_bound {ι : Type*} (s : Finset ι) (e : ι → ℝ)
    (he : ∀ i ∈ s, 0 < e i) : ∃ δ > 0, ∀ i ∈ s, δ ≤ e i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨δ, hδ, hb⟩ := ih (fun j hj => he j (Finset.mem_insert_of_mem hj))
    refine ⟨min δ (e i), lt_min hδ (he i (Finset.mem_insert_self _ _)), ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hb j hj)

theorem scalarFlowPeriod_exists_uniform_finite_cells {f : Coord → ℝ} {W : Set Coord} {P : ℝ}
    (hP : 0 ≤ P) (hW : IsOpen W) (hf : ContDiffOn ℝ ∞ f W)
    (hseam : ∀ r ∈ Icc (0 : ℝ) P, (![r, 0] : Coord) ∈ W) :
    ∃ δ > 0, ∃ s : Finset (Icc (0 : ℝ) P),
      ∃ (D : Icc (0 : ℝ) P → Set (ℝ × Coord))
        (Φ : Icc (0 : ℝ) P → ℝ × Coord → Coord),
      (∀ c ∈ s, IsOpen (D c) ∧ ContDiffOn ℝ ∞ (Φ c) (D c) ∧
        (∀ x, (0, x) ∈ D c → Φ c (0, x) = x) ∧
        ∀ q ∈ D c, Φ c q ∈ W ∧ HasDerivAt (fun t => Φ c (t, q.2))
          (scalarFlowAutonomization f (Φ c q)) q.1) ∧
      ∀ r ∈ Icc (0 : ℝ) P, ∃ c ∈ s, ∀ t x : ℝ,
        |t| < δ → |x| < δ → (t, (![r, x] : Coord)) ∈ D c := by
  classical
  choose D Φ hD hmem hΦ hzero hode using fun c : Icc (0 : ℝ) P =>
    scalarFlowPeriod_exists_local_phase_flow hW hf (hseam c c.property)
  choose η hη hball using fun c : Icc (0 : ℝ) P =>
    Metric.mem_nhds_iff.mp ((hD c).mem_nhds (hmem c))
  let B : Icc (0 : ℝ) P → Set ℝ := fun c => Metric.ball c (η c / 2)
  have hcover : Icc (0 : ℝ) P ⊆ ⋃ c, B c := by
    intro r hr
    exact mem_iUnion.mpr ⟨⟨r, hr⟩, mem_ball_self (half_pos (hη ⟨r, hr⟩))⟩
  obtain ⟨s, hs⟩ := isCompact_Icc.elim_finite_subcover B (fun _ => isOpen_ball) hcover
  obtain ⟨δ, hδ, hb⟩ := scalarFlowPeriod_finite_positive_bound s (fun c => η c / 2)
    (fun c _ => half_pos (hη c))
  refine ⟨δ, hδ, s, D, Φ, fun c _ => ⟨hD c, hΦ c, hzero c, hode c⟩, ?_⟩
  intro r hr
  obtain ⟨c, hc, hrc⟩ := mem_iUnion₂.mp (hs hr)
  refine ⟨c, hc, fun t x ht hx => hball c ?_⟩
  have htη : |t| < η c := (ht.trans_le (hb c hc)).trans (half_lt_self (hη c))
  have hxη : |x| < η c := (hx.trans_le (hb c hc)).trans (half_lt_self (hη c))
  have hrη : dist r (c : ℝ) < η c := hrc.trans (half_lt_self (hη c))
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
  refine ⟨by simpa only [Real.dist_eq, sub_zero] using htη, ?_⟩
  apply (dist_pi_lt_iff (hη c)).mpr
  intro i
  fin_cases i
  · exact hrη
  · change dist x (0 : ℝ) < η c
    simpa only [Real.dist_eq, sub_zero] using hxη

end
end TightVer401
