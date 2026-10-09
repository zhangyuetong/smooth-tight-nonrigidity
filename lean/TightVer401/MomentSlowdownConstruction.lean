import TightVer401.MomentControlSmallness
import TightVer401.MomentSlowdownEstimates
import TightVer401.MomentPath

namespace TightVer401
noncomputable section
open Set Filter MeasureTheory Metric
open scoped ContDiff Topology BigOperators
set_option backward.isDefEq.respectTransparency false

def momentSlowdownChi (L : ℝ) [Fact (0 < L)] (a r : ℝ) (hr : 0 < r) : ℝ → ℝ :=
  momentPeriodicRepresentative L (momentControlBump a r hr)

structure MomentSlowdownData {m n : ℕ} (L : ℝ) [Fact (0 < L)]
    (a R ε η : ℝ) (b : ℝ → ℝ) (f : ℝ → EuclideanSpace ℝ (Fin m))
    (g : ℝ → ℝ) (ψ : Fin n → ℝ → ℝ) where
  r : ℝ
  hr : 0 < r
  rε : r < ε
  rR : r < R
  left : 0 < a - r
  right : a + r < L
  c : Fin n → ℝ
  δ : ℝ
  δpos : 0 < δ
  smooth : ContDiff ℝ ∞ (momentSlowdownChi L a r hr)
  periodic : Function.Periodic (momentSlowdownChi L a r hr) L
  bound : ∀ s, 0 ≤ momentSlowdownChi L a r hr s ∧ momentSlowdownChi L a r hr s ≤ 1
  controls_smooth : ∀ j, ContDiff ℝ ∞ (momentPeriodicRepresentative L (ψ j))
  controls_periodic : ∀ j, Function.Periodic (momentPeriodicRepresentative L (ψ j)) L
  controls_nonneg : ∀ j s, 0 ≤ momentPeriodicRepresentative L (ψ j) s
  controls_mass : ∀ j, (∫ s in 0..L, momentPeriodicRepresentative L (ψ j) s) = 1
  disjoint : ∀ s, momentSlowdownChi L a r hr s ≠ 0 → ∀ j,
    momentPeriodicRepresentative L (ψ j) s = 0
  control : ∀ s, momentSlowdownChi L a r hr s = 0 →
    δ ≤ b s - ∑ j, |c j| * |momentPeriodicRepresentative L (ψ j) s|
  balance : (∑ j, c j • momentPathMoment L f (momentPeriodicRepresentative L (ψ j))) =
    momentPathMoment L f (fun s => momentSlowdownChi L a r hr s * b s)
  small : (∫ s in 0..L, |momentSlowdownChi L a r hr s * b s|) +
    (∑ j, |c j| * (∫ s in 0..L, |momentPeriodicRepresentative L (ψ j) s|)) < η
  plateau : ∀ s ∈ Icc (a - r / 2) (a + r / 2), momentSlowdownChi L a r hr s = 1
  sign : ∀ s ∈ Icc 0 L, momentSlowdownChi L a r hr s ≠ 0 → 0 < g s
  plateau_sign : ∀ s ∈ Icc (a - r / 2) (a + r / 2), 0 < g s

theorem exists_momentSlowdown_data {m n : ℕ} (L : ℝ) [hL : Fact (0 < L)]
    {a R ε η : ℝ} {b g : ℝ → ℝ} {f : ℝ → EuclideanSpace ℝ (Fin m)}
    (ψ : Fin n → ℝ → ℝ) (ha : a ∈ Ioo 0 L) (hR : 0 < R)
    (hε : 0 < ε) (hη : 0 < η) (hb : ContDiff ℝ ∞ b)
    (hbL : Function.Periodic b L) (hbpos : ∀ s, 0 < b s)
    (hf : Continuous f) (hg : Continuous g) (hga : 0 < g a)
    (hψ : ∀ j, ContDiff ℝ ∞ (ψ j)) (hψcompact : ∀ j, HasCompactSupport (ψ j))
    (hψinside : ∀ j, tsupport (ψ j) ⊆ Ioo 0 L)
    (hψnonneg : ∀ j s, 0 ≤ ψ j s) (hψmass : ∀ j, (∫ s in 0..L, ψ j s) = 1)
    (hψaway : ∀ j, Disjoint (tsupport (ψ j)) (closedBall a R))
    (T : momentSampleSpan f (Ioo 0 L) ≃L[ℝ] (Fin n → ℝ))
    (hT : ∀ u : momentSampleSpan f (Ioo 0 L),
      (∑ j, T u j • (∫ s in 0..L, ψ j s • f s)) = (u : EuclideanSpace ℝ (Fin m))) :
    Nonempty (MomentSlowdownData L a R ε η b f g ψ) := by
  obtain ⟨μ, hμ, hμb⟩ := momentSlowdown_periodic_min L hb hbL hbpos
  obtain ⟨B, hB, hBb⟩ := momentSlowdown_periodic_bound L hb hbL
  let Ψ : Fin n → ℝ → ℝ := fun j => momentPeriodicRepresentative L (ψ j)
  have hΨ (j) : ContDiff ℝ ∞ (Ψ j) :=
    momentPeriodicRepresentative_contDiff L (hψ j) (hψcompact j) (hψinside j)
  have hΨL (j) : Function.Periodic (Ψ j) L := momentPeriodicRepresentative_periodic L (ψ j)
  obtain ⟨K, hK, hKΨ⟩ := momentSlowdown_control_bound L hΨ hΨL
  obtain ⟨M, hM, hMbf⟩ := exists_positive_baseline_moment_bound hf hb.continuous L
  obtain ⟨C, hC, hCT⟩ := momentSlowdown_coordinate_bound _ T
  have hge : ∀ᶠ s in 𝓝 a, 0 < g s := hg.continuousAt.eventually (Ioi_mem_nhds hga)
  obtain ⟨e, he, hge⟩ := Metric.eventually_nhds_iff.mp hge
  obtain ⟨r, hr, hrε, hrR, hre, hleft, hright, hcorr, hsmall⟩ :=
    momentSlowdown_choose_radius ha hR hε hμ hη hB hC hM hK he
  let β := momentControlBump a r hr
  have hβinside : tsupport (β : ℝ → ℝ) ⊆ Ioo 0 L := by
    rw [momentSlowdown_bump_tsupport hr]
    intro s hs
    exact ⟨hleft.trans_le hs.1, hs.2.trans_lt hright⟩
  have hβcompact : HasCompactSupport (β : ℝ → ℝ) := β.hasCompactSupport
  have hβsmooth : ContDiff ℝ ∞ (β : ℝ → ℝ) := β.contDiff
  have hβeq := momentPeriodicRepresentative_eqOn L hβinside
  let χ := momentSlowdownChi L a r hr
  let u : momentSampleSpan f (Ioo 0 L) :=
    ⟨slowdownVectorMoment L a r hr b f,
      slowdownVectorMoment_mem_span hr b hleft.le hright.le⟩
  let c : Fin n → ℝ := T u
  have hc : (∑ j, |c j|) ≤ 2 * C * M * r :=
    slowdown_coefficients_l1_le hr b hM.le hC.le hMbf hleft.le hright.le T hCT u rfl
  have herror (s) : (∑ j, |c j| * |Ψ j s|) < μ / 2 := by
    calc
      (∑ j, |c j| * |Ψ j s|) ≤ K * (∑ j, |c j|) := momentSlowdown_control_error_le c Ψ hKΨ s
      _ ≤ K * (2 * C * M * r) := mul_le_mul_of_nonneg_left hc hK.le
      _ < μ / 2 := by nlinarith [hcorr]
  have hplateau (s) (hs : s ∈ Icc (a - r / 2) (a + r / 2)) : χ s = 1 := by
    change momentPeriodicRepresentative L β s = 1
    rw [hβeq ⟨by linarith [hs.1], by linarith [hs.2]⟩]
    exact momentSlowdown_bump_plateau hr hs
  have hsign (s) (hs : s ∈ Icc 0 L) (hχs : χ s ≠ 0) : 0 < g s := by
    have hβs : β s ≠ 0 := by
      change momentPeriodicRepresentative L β s ≠ 0 at hχs
      rwa [hβeq hs] at hχs
    have hsball : s ∈ ball a r := by
      change s ∈ Function.support (β : ℝ → ℝ) at hβs
      rwa [β.support_eq] at hβs
    exact hge (lt_trans hsball hre)
  have hslow : (∫ s in 0..L, |χ s * b s|) ≤ 2 * B * r := by
    have heq : (∫ s in 0..L, |χ s * b s|) = ∫ s in 0..L, |β s * b s| := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le hL.out.le] at hs
      change |momentPeriodicRepresentative L β s * b s| = |β s * b s|
      rw [hβeq hs]
    rw [heq]
    exact momentSlowdown_bump_weight_l1_le hr b hleft.le hright.le (fun s _ => hBb s)
  have hmass (j) : (∫ s in 0..L, |Ψ j s|) = 1 := by
    have habs : (fun s => |Ψ j s|) = Ψ j := by
      ext s
      exact abs_of_nonneg (momentPeriodicRepresentative_nonneg L (hψnonneg j) s)
    rw [habs]
    exact momentPeriodicRepresentative_normalized L (hψinside j) (hψmass j)
  refine ⟨{
    r := r, hr := hr, rε := hrε, rR := hrR, left := hleft, right := hright,
    c := c, δ := μ / 2, δpos := by positivity,
    smooth := momentPeriodicRepresentative_contDiff L hβsmooth hβcompact hβinside,
    periodic := momentPeriodicRepresentative_periodic L β,
    bound := ?_, controls_smooth := hΨ, controls_periodic := hΨL,
    controls_nonneg := fun j => momentPeriodicRepresentative_nonneg L (hψnonneg j),
    controls_mass := fun j => momentPeriodicRepresentative_normalized L (hψinside j) (hψmass j),
    disjoint := ?_, control := ?_, balance := ?_, small := ?_, plateau := hplateau,
    sign := hsign, plateau_sign := ?_ }⟩
  · intro s
    change 0 ≤ momentPeriodicCircleControl L β (periodProjection L s) ∧
      momentPeriodicCircleControl L β (periodProjection L s) ≤ 1
    exact ⟨β.nonneg, β.le_one⟩
  · intro s hχs j
    apply momentPeriodicRepresentative_disjoint_zero L (hψcompact j) hβcompact (hψinside j) hβinside _ s hχs
    apply (hψaway j).mono_right
    rw [β.tsupport_eq]
    exact closedBall_subset_closedBall hrR.le
  · intro s _
    have hs := hμb s
    have he := herror s
    change μ / 2 ≤ b s - ∑ j, |c j| * |Ψ j s|
    linarith
  · have hrightmoment : momentPathMoment L f (fun s => χ s * b s) =
        slowdownVectorMoment L a r hr b f := by
      unfold momentPathMoment slowdownVectorMoment slowdownControl
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le hL.out.le] at hs
      change (momentPeriodicRepresentative L β s * b s) • f s = (β s * b s) • f s
      rw [hβeq hs]
    rw [hrightmoment]
    calc
      (∑ j, c j • momentPathMoment L f (Ψ j)) =
          ∑ j, T u j • (∫ s in 0..L, ψ j s • f s) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [momentPathMoment, momentPeriodicRepresentative_intervalMoment L (hψinside j)]
      _ = _ := hT u
  · change (∫ s in 0..L, |χ s * b s|) +
      (∑ j, |c j| * (∫ s in 0..L, |Ψ j s|)) < η
    simp only [hmass, mul_one]
    nlinarith [hslow, hc, hsmall]
  · intro s hs
    apply hsign s ⟨by linarith [hs.1], by linarith [hs.2]⟩
    rw [hplateau s hs]
    exact one_ne_zero

end
end TightVer401
