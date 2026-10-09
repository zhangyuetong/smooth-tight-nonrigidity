import TightVer401.PositiveExitConstructionLabel
import TightVer401.SeamCompactCollar
import Mathlib.Algebra.Order.ToIntervalMod

/-! Uniform label control around the SAME selected Fermi seam. Compactness
on one full period and actual label continuity produce the smallness threshold;
no source nesting or separation conclusion is assumed. -/
open scoped Manifold
namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

/-- A continuous periodic label constant on the seam has a genuine uniform
label tube. Only local continuity on its actual open domain is needed. -/
theorem positiveExitSelected_exists_periodic_label_tube
    {P c η : ℝ} (hP : 0 < P) (hη : 0 < η)
    {L : Coord → ℝ} {U : Set Coord} (hU : IsOpen U)
    (hL : ContinuousOn L U) (hLP : FermiPeriodic P L)
    (hseam : ∀ r : ℝ, (![r, 0] : Coord) ∈ U)
    (hzero : ∀ r : ℝ, L (![r, 0] : Coord) = c) :
    ∃ ρ > 0, ∀ r x : ℝ, |x| ≤ ρ → |L (![r, x] : Coord) - c| < η := by
  let V : Set Coord := U ∩ L ⁻¹' Ioo (c - η) (c + η)
  have hV : IsOpen V := hL.isOpen_inter_preimage hU isOpen_Ioo
  have haxis : ∀ r ∈ Icc (0 : ℝ) P, (![r, 0] : Coord) ∈ V := by
    intro r _
    refine ⟨hseam r, ?_⟩
    change c - η < L (![r, 0] : Coord) ∧ L (![r, 0] : Coord) < c + η
    rw [hzero r]
    constructor <;> linarith
  obtain ⟨ρ, hρ, htube⟩ := seam_compact_axis_open_collar isCompact_Icc hV haxis
  refine ⟨ρ, hρ, fun r x hx => ?_⟩
  let s := toIcoMod hP 0 r
  have hs : s ∈ Icc (0 : ℝ) P := Ico_subset_Icc_self (toIcoMod_mem_Ico' hP r)
  have hb := (htube s hs x hx).2
  have hp := ((fermiPeriodic_iff_slices P L).mp hLP) x
  have he := hp.sub_zsmul_eq (x := r) (toIcoDiv hP 0 r)
  change L (![s, x] : Coord) = L (![r, x] : Coord) at he
  change c - η < L (![s, x] : Coord) ∧ L (![s, x] : Coord) < c + η at hb
  rw [he] at hb
  apply abs_lt.mpr
  constructor <;> linarith [hb.1, hb.2]

/-- Specialize the compact periodic argument to the actual Cartesian label
pulled back through the SAME Fermi source and SAME native inverse. -/
theorem positiveExitFermiLabel_exists_uniform_tube
    {T w P c η : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T)
    (hb : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0)
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) Coord)
    {ζ : ℝ → Ambient} (hζ : ContDiff ℝ ∞ ζ)
    (hζP : Function.Periodic ζ P) (hP : 0 < P)
    (heI : ContMDiffOn 𝓘(ℝ, Coord) nativeProductModel ∞ e.symm e.target)
    (hseam : ∀ r : ℝ, (![r, 0] : Coord) ∈ positiveExitFermiLabelDomain e ζ)
    (hzero : ∀ r : ℝ, positiveExitFermiLabel d hb e ζ (![r, 0] : Coord) = c)
    (hη : 0 < η) :
    ∃ ρ > 0, ∀ r x : ℝ, |x| ≤ ρ →
      |positiveExitCartesianLabel d hb e (positiveExitFermiSource ζ ![r, x]) - c| < η := by
  exact positiveExitSelected_exists_periodic_label_tube hP hη
    (positiveExitFermiLabelDomain_isOpen e hζ)
    (positiveExitFermiLabel_contDiffOn d hb e hζ heI).continuousOn
    (positiveExitFermiLabel_periodic d hb e hζ hζP) hseam hzero

/-- The constant in the preceding tube is the actual first-integral value
of the selected raw leaf, rather than an independently chosen label. -/
theorem positiveExitFermiLabel_selected_exists_uniform_tube
    {T w P δ η : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T)
    (hb : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0)
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) Coord)
    (heS : e.source = univ)
    (heF : ∀ p, e p = gnomonicInverse (d.bandGaussMap p))
    (heI : ContMDiffOn 𝓘(ℝ, Coord) nativeProductModel ∞ e.symm e.target)
    (hinside : ∀ u ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 u t ∈ Ioo 0 w)
    (v : Ioo (0 : ℝ) δ) (ψ : ℝ → ℝ)
    {ζ : ℝ → Ambient} (hζ : ContDiff ℝ ∞ ζ)
    (hζP : Function.Periodic ζ P) (hP : 0 < P)
    (hζeq : ∀ r, ζ r = positiveExitRawLeaf d hb hinside v (ψ r))
    (hbandNorth : ∀ p : AddCircle T × Ioo (0 : ℝ) w, 0 < d.bandGaussMap p 2)
    (hη : 0 < η) :
    ∃ ρ > 0, ∀ r x : ℝ, |x| ≤ ρ →
      |positiveExitCartesianLabel d hb e (positiveExitFermiSource ζ ![r, x]) -
        (1 / (ruledRho d.τ 0 * (v : ℝ)) - ruledOmega d.k d.τ 0)| < η := by
  have hseam (r : ℝ) : (![r, 0] : Coord) ∈ positiveExitFermiLabelDomain e ζ := by
    let p := positiveExitLeaf d hb hinside v (periodProjection T (ψ r))
    have hn : 0 < ζ r 2 := by
      rw [hζeq r]
      exact hbandNorth p
    have hsrc : positiveExitFermiSource ζ (![r, 0] : Coord) = e p := by
      simp only [positiveExitFermiSource, fermiNormalMap, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Real.cos_zero, Real.sin_zero,
        one_smul, zero_smul, add_zero]
      rw [hζeq r, heF p]
      rfl
    refine ⟨?_, ?_⟩
    · simpa [fermiNormalMap] using hn
    · change positiveExitFermiSource ζ (![r, 0] : Coord) ∈ e.target
      rw [hsrc]
      exact e.map_source (by rw [heS]; exact mem_univ p)
  exact positiveExitFermiLabel_exists_uniform_tube d hb e hζ hζP hP heI hseam
    (positiveExitFermiLabel_selected_seam d hb e heS heF hinside v ψ hζeq) hη

/-- A continuous periodic profile admits one positive amplitude budget making
all of its graph heights lie in a prescribed tube, on the entire real axis. -/
theorem positiveExitSelected_exists_graph_amplitude_budget
    {P ρ : ℝ} (hP : 0 < P) (hρ : 0 < ρ)
    {v : ℝ → ℝ} (hv : Continuous v) (hvP : Function.Periodic v P) :
    ∃ ν > 0, ∀ δ : ℝ, |δ| < ν → ∀ r : ℝ, |δ * v r| < ρ := by
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) P)).exists_bound_of_continuousOn
    hv.continuousOn
  let B : ℝ := max M 1
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right M 1)
  have hvB (r : ℝ) : |v r| ≤ B := by
    let s := toIcoMod hP 0 r
    have hs : s ∈ Icc (0 : ℝ) P := Ico_subset_Icc_self (toIcoMod_mem_Ico' hP r)
    have he := hvP.sub_zsmul_eq (x := r) (toIcoDiv hP 0 r)
    change v s = v r at he
    have hb := hM s hs
    rw [he] at hb
    have hvM : |v r| ≤ M := by simpa only [Real.norm_eq_abs] using hb
    exact hvM.trans (le_max_left M 1)
  refine ⟨ρ / B, div_pos hρ hB, fun δ hδ r => ?_⟩
  rw [abs_mul]
  calc
    |δ| * |v r| ≤ |δ| * B := mul_le_mul_of_nonneg_left (hvB r) (abs_nonneg δ)
    _ < (ρ / B) * B := mul_lt_mul_of_pos_right hδ hB
    _ = ρ := div_mul_cancel₀ ρ hB.ne'
/-- A uniform tube supplies actual set separation of every small graph
from any protected set with a strict label gap. This gives boundary
separation for source-order consumers without presupposing nesting. -/
theorem positiveExitSelected_graph_disjoint_of_label_tube
    {L : Coord → ℝ} {Φ : Coord → Coord} {C : Set Coord} {c η ρ : ℝ}
    (htube : ∀ r x : ℝ, |x| ≤ ρ → |L (Φ ![r, x]) - c| < η)
    (hgap : ∀ q ∈ C, η ≤ |L q - c|)
    (u : ℝ → ℝ) (hu : ∀ r, |u r| ≤ ρ) :
    Disjoint ((fun r => Φ (![r, u r] : Coord)) '' univ) C := by
  apply Set.disjoint_left.mpr
  rintro q ⟨r, _, rfl⟩ hq
  exact (not_lt_of_ge (hgap _ hq)) (htube r (u r) (hu r))

/-- Distinct selected seam labels with disjoint label tubes give actual
separation of the two small Cartesian graph images. The Fermi sources and
profiles can differ; the Cartesian label remains the SAME function. -/
theorem positiveExitSelected_two_graphs_disjoint_of_label_tubes
    {L : Coord → ℝ} {Φ₁ Φ₂ : Coord → Coord}
    {c₁ c₂ η₁ η₂ ρ₁ ρ₂ : ℝ}
    (htube₁ : ∀ r x : ℝ, |x| ≤ ρ₁ → |L (Φ₁ ![r, x]) - c₁| < η₁)
    (htube₂ : ∀ r x : ℝ, |x| ≤ ρ₂ → |L (Φ₂ ![r, x]) - c₂| < η₂)
    (hgap : η₁ + η₂ < |c₁ - c₂|)
    (u₁ u₂ : ℝ → ℝ) (hu₁ : ∀ r, |u₁ r| ≤ ρ₁) (hu₂ : ∀ r, |u₂ r| ≤ ρ₂) :
    Disjoint ((fun r => Φ₁ (![r, u₁ r] : Coord)) '' univ)
      ((fun r => Φ₂ (![r, u₂ r] : Coord)) '' univ) := by
  apply Set.disjoint_left.mpr
  rintro q ⟨r, _, hr⟩ ⟨s, _, hs⟩
  have h₁ := htube₁ r (u₁ r) (hu₁ r)
  have h₂ := htube₂ s (u₂ s) (hu₂ s)
  change Φ₁ (![r, u₁ r] : Coord) = q at hr
  change Φ₂ (![s, u₂ s] : Coord) = q at hs
  rw [hr] at h₁
  rw [hs] at h₂
  have htri : |c₁ - c₂| ≤ |L q - c₁| + |L q - c₂| := by
    calc
      |c₁ - c₂| ≤ |c₁ - L q| + |L q - c₂| := abs_sub_le c₁ (L q) c₂
      _ = |L q - c₁| + |L q - c₂| := by rw [abs_sub_comm c₁ (L q)]
  exact (not_lt_of_ge htri) ((add_lt_add h₁ h₂).trans hgap)
end
end TightVer401






