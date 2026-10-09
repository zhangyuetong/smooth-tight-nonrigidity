import TightVer401.PlanarGradientInverse
import TightVer401.RadialPlanarPotential

/-! Exhaustion after actual compact-band degree results.
The per-band premise is an intermediate degree output. It must be produced
from ordinary circular boundary data, not supplied to the public completion.
No pending degree source or completed global inverse is imported here.
-/
namespace TightVer401
noncomputable section
open Set Function OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

/-- Select a sufficiently small inner radius and sufficiently large outer
radius, simultaneously retaining source bounds and bracketing a target point. -/
theorem dualRadialCompletionExhaustion_parameters {A RN mu B epsilon0 L0 x q sigma : ℝ}
    (hAR : A < RN) (hmu : 0 < mu) (hepsilon0 : 0 < epsilon0) (hx : 0 < x)
    (hAsigma : A < sigma) (hsigmaRN : sigma < RN) :
    ∃ epsilon L : ℝ,
      0 < epsilon ∧ epsilon < epsilon0 ∧ epsilon < x ∧ L0 < L ∧ q < L ∧
      1 < L ∧ epsilon < L ∧ A + B / L ^ 2 < sigma ∧ sigma < RN - mu * epsilon := by
  let m := min epsilon0 (min x (min 1 ((RN - sigma) / mu)))
  have hm : 0 < m := by
    dsimp only [m]
    exact lt_min hepsilon0 (lt_min hx (lt_min zero_lt_one (div_pos (sub_pos.mpr hsigmaRN) hmu)))
  let epsilon := m / 2
  have hepsilon : 0 < epsilon := half_pos hm
  have hem : epsilon < m := half_lt_self hm
  have hm0 : m ≤ epsilon0 := min_le_left _ _
  have hmx : m ≤ x := (min_le_right _ _).trans (min_le_left _ _)
  have hm1 : m ≤ 1 := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hmd : m ≤ (RN - sigma) / mu := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  have hepsilon0' : epsilon < epsilon0 := hem.trans_le hm0
  have hepsilonx : epsilon < x := hem.trans_le hmx
  have hepsilon1 : epsilon < 1 := hem.trans_le hm1
  have hepsilond : epsilon < (RN - sigma) / mu := hem.trans_le hmd
  let T := max L0 (max q (max 1 (B / (sigma - A))))
  let L := T + 1
  have hTL : T < L := by dsimp only [L]; linarith
  have hL0 : L0 < L := (show L0 ≤ T from le_max_left _ _).trans_lt hTL
  have hqT : q ≤ T := (le_max_left _ _).trans (le_max_right _ _)
  have h1T : 1 ≤ T := (le_max_left _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hBT : B / (sigma - A) ≤ T := (le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hLq : q < L := hqT.trans_lt hTL
  have hL1 : 1 < L := h1T.trans_lt hTL
  have hLB : B / (sigma - A) < L := hBT.trans_lt hTL
  have hdelta : 0 < sigma - A := sub_pos.mpr hAsigma
  have hLpos : 0 < L := zero_lt_one.trans hL1
  have hLsq : L ≤ L ^ 2 := by
    simpa only [one_mul, pow_two] using mul_le_mul_of_nonneg_right hL1.le hLpos.le
  have hBdelta : B < L * (sigma - A) := (div_lt_iff₀ hdelta).mp hLB
  have hBdeltaSq : B < (sigma - A) * L ^ 2 := by
    calc
      B < L * (sigma - A) := hBdelta
      _ ≤ L ^ 2 * (sigma - A) := mul_le_mul_of_nonneg_right hLsq hdelta.le
      _ = (sigma - A) * L ^ 2 := mul_comm _ _
  have hFraction : B / L ^ 2 < sigma - A :=
    (div_lt_iff₀ (sq_pos_of_pos hLpos)).mpr hBdeltaSq
  have hUpper : sigma < RN - mu * epsilon := by
    have hproduct : epsilon * mu < RN - sigma := (lt_div_iff₀ hmu).mp hepsilond
    nlinarith
  exact ⟨epsilon, L, hepsilon, hepsilon0', hepsilonx, hL0, hLq, hL1,
    hepsilon1.trans hL1, by linarith, hUpper⟩

/-- Genuine exhaustion: a family of actual compact-band degree bijections
proves global injectivity and the exact punctured-plane gradient image.
It does not assume either global conclusion or an assembled inverse. -/
theorem dualRadialCompletionExhaustion_bijOn {G : Coord → ℝ}
    {A RN mu B epsilon0 L0 : ℝ} (hA : 0 < A) (hAR : A < RN)
    (hmu : 0 < mu) (hB : 0 < B) (hepsilon0 : 0 < epsilon0)
    (hBands : ∀ epsilon L : ℝ, 0 < epsilon → epsilon < epsilon0 → L0 < L →
      epsilon < L → A + B / L ^ 2 < RN - mu * epsilon →
      BijOn (planarGradient G)
        {p : Coord | epsilon < planarRadius p ∧ planarRadius p < L}
        {y : Coord | A + B / L ^ 2 < planarRadius y ∧ planarRadius y < RN - mu * epsilon}) :
    BijOn (planarGradient G) {p : Coord | 0 < planarRadius p}
      {y : Coord | A < planarRadius y ∧ planarRadius y < RN} := by
  have hAmid : A < (A + RN) / 2 := by linarith
  have hmidRN : (A + RN) / 2 < RN := by linarith
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨epsilon, L, hepsilon, hepsilon0', hepsilonp, hL0, hpL, hL1, hepsilonL,
      hLower, hUpper⟩ := dualRadialCompletionExhaustion_parameters
        (B := B) (L0 := L0) (x := planarRadius p) (q := planarRadius p)
        hAR hmu hepsilon0 hp hAmid hmidRN
    have hBij := hBands epsilon L hepsilon hepsilon0' hL0 hepsilonL (hLower.trans hUpper)
    have hy := hBij.mapsTo ⟨hepsilonp, hpL⟩
    have hFraction : 0 < B / L ^ 2 := div_pos hB (sq_pos_of_pos (zero_lt_one.trans hL1))
    have hProduct : 0 < mu * epsilon := mul_pos hmu hepsilon
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  · intro p hp z hz hpz
    have hx : 0 < min (planarRadius p) (planarRadius z) := lt_min hp hz
    obtain ⟨epsilon, L, hepsilon, hepsilon0', hepsilonx, hL0, hqL, _hL1, hepsilonL,
      hLower, hUpper⟩ := dualRadialCompletionExhaustion_parameters
        (B := B) (L0 := L0) (q := max (planarRadius p) (planarRadius z))
        hAR hmu hepsilon0 hx hAmid hmidRN
    have hBij := hBands epsilon L hepsilon hepsilon0' hL0 hepsilonL (hLower.trans hUpper)
    exact hBij.injOn
      ⟨hepsilonx.trans_le (min_le_left _ _), (le_max_left _ _).trans_lt hqL⟩
      ⟨hepsilonx.trans_le (min_le_right _ _), (le_max_right _ _).trans_lt hqL⟩ hpz
  · intro y hy
    obtain ⟨epsilon, L, hepsilon, hepsilon0', _hepsilonx, hL0, _hqL, _hL1, hepsilonL,
      hLower, hUpper⟩ := dualRadialCompletionExhaustion_parameters
        (B := B) (L0 := L0) (x := 1) (q := 1)
        hAR hmu hepsilon0 zero_lt_one hy.1 hy.2
    have hBij := hBands epsilon L hepsilon hepsilon0' hL0 hepsilonL (hLower.trans hUpper)
    obtain ⟨p, hp, hpy⟩ := hBij.surjOn ⟨hLower, hUpper⟩
    exact ⟨p, hepsilon.trans hp.1, hpy⟩

end
end TightVer401
