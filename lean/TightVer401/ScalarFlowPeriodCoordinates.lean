import TightVer401.ScalarFlowPeriodCells
import TightVer401.ScalarFlowPeriodUniqueness

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

theorem scalarFlowPeriod_abs_le_of_mem_uIcc_zero {s t : ℝ} (hs : s ∈ uIcc 0 t) :
    |s| ≤ |t| := by
  have hl : -|t| ≤ min 0 t := le_min (by linarith [abs_nonneg t]) (neg_abs_le t)
  have hr : max 0 t ≤ |t| := max_le (abs_nonneg t) (le_abs_self t)
  exact abs_le.mpr ⟨hl.trans hs.1, hs.2.trans hr⟩

theorem scalarFlowPeriod_time_coordinate {f : Coord → ℝ}
    {D : Set (ℝ × Coord)} {Φ : ℝ × Coord → Coord} {δ r x t : ℝ}
    (hδ : 0 < δ) (hzero : ∀ y, (0, y) ∈ D → Φ (0, y) = y)
    (hode : ∀ q ∈ D, HasDerivAt (fun s => Φ (s, q.2))
      (scalarFlowAutonomization f (Φ q)) q.1)
    (hbox : ∀ s : ℝ, |s| < δ → (s, (![r, x] : Coord)) ∈ D) (ht : |t| < δ) :
    Φ (t, (![r, x] : Coord)) 0 = r + t := by
  have hd (s : ℝ) (hs : s ∈ uIcc 0 t) :
      HasDerivAt (fun a => Φ (a, (![r, x] : Coord)) 0) 1 s := by
    have hm := hbox s ((scalarFlowPeriod_abs_le_of_mem_uIcc_zero hs).trans_lt ht)
    have h := (hasDerivAt_pi.mp (hode (s, ![r, x]) hm)) (0 : Fin 2)
    simpa only [scalarFlowAutonomization, Matrix.cons_val_zero] using h
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd intervalIntegrable_const
  have h0 := hzero ![r, x] (hbox 0 (by simpa using hδ))
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one, h0,
    Matrix.cons_val_zero] at he
  linarith

theorem scalarFlowPeriod_central_orbit {f : Coord → ℝ} {W : Set Coord}
    {D : Set (ℝ × Coord)} {Φ : ℝ × Coord → Coord} {δ r : ℝ}
    (hδ : 0 < δ) (hW : IsOpen W) (hf : ContDiffOn ℝ ∞ f W)
    (hΦ : ContDiffOn ℝ ∞ Φ D)
    (hzero : ∀ y, (0, y) ∈ D → Φ (0, y) = y)
    (hode : ∀ q ∈ D, Φ q ∈ W ∧ HasDerivAt (fun s => Φ (s, q.2))
      (scalarFlowAutonomization f (Φ q)) q.1)
    (hseam : ∀ a : ℝ, (![a, 0] : Coord) ∈ W)
    (hfzero : ∀ a : ℝ, f ![a, 0] = 0)
    (hbox : ∀ s : ℝ, |s| < δ → (s, (![r, 0] : Coord)) ∈ D) :
    ∀ t : ℝ, |t| < δ / 2 → Φ (t, (![r, 0] : Coord)) = ![r + t, 0] := by
  let I := Icc (-δ / 2) (δ / 2)
  have hsmall (s : ℝ) (hs : s ∈ I) : |s| < δ := by
    have ha : |s| ≤ δ / 2 := abs_le.mpr ⟨by linarith [hs.1], hs.2⟩
    exact ha.trans_lt (half_lt_self hδ)
  let U : ℝ → Coord := fun s => Φ (s, ![r, 0])
  let Z : ℝ → Coord := fun s => ![r + s, 0]
  have hUc : ContinuousOn U I := hΦ.continuousOn.comp
    (continuous_id.prodMk continuous_const).continuousOn (fun s hs => hbox s (hsmall s hs))
  have hZc : Continuous Z := by fun_prop
  have hUd (s : ℝ) (hs : s ∈ Ioo (-δ / 2) (δ / 2)) :
      HasDerivAt U (scalarFlowAutonomization f (U s)) s :=
    (hode (s, ![r, 0]) (hbox s (hsmall s (Ioo_subset_Icc_self hs)))).2
  have hZd (s : ℝ) (hs : s ∈ Ioo (-δ / 2) (δ / 2)) :
      HasDerivAt Z (scalarFlowAutonomization f (Z s)) s := by
    have hd := ((hasDerivAt_id s).const_add r).smul_const (Pi.single 0 1 : Coord)
    convert! hd using 1
    · funext a
      ext i
      fin_cases i <;> simp [Z]
    · ext i
      fin_cases i <;> simp [Z, scalarFlowAutonomization, hfzero]
  have hUmem (s : ℝ) (hs : s ∈ I) : U s ∈ W :=
    (hode (s, ![r, 0]) (hbox s (hsmall s hs))).1
  have hZmem (s : ℝ) (hs : s ∈ I) : Z s ∈ W := hseam (r + s)
  have h0 : U 0 = Z 0 := by
    simpa only [U, Z, add_zero] using hzero ![r, 0] (hbox 0 (by simpa using hδ))
  have he := scalarFlowPeriod_unique_Icc_local hW (scalarFlowAutonomization_contDiffOn hf)
    (t₀ := (0 : ℝ)) (by constructor <;> linarith) hUc hZc.continuousOn
    hUd hZd hUmem hZmem h0
  intro t ht
  exact he (by
    have ha := abs_le.mp ht.le
    exact ⟨by linarith [ha.1], ha.2⟩)

end
end TightVer401
