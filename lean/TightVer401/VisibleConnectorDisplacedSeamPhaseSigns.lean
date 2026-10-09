import TightVer401.VisibleConnectorDisplacedSeamPhase
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! Actual compact sign selection for the already constructed displaced phase.
The joint derivatives are actual fderiv evaluations. No derivative sign,
negative original height or phase homeomorphism is supplied as an input. -/
namespace TightVer401
noncomputable section
open Set Function Filter Metric OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

private theorem displaced_phase_surjective {f : ℝ → ℝ} {L : ℝ}
    (hf : Continuous f) (hL : 0 < L) (hshift : ∀ s, f (s + L) = f s + L) :
    Surjective f := by
  have hnat : ∀ n : ℕ, ∀ s, f (s + (n : ℝ) * L) = f s + (n : ℝ) * L := by
    intro n
    induction n with
    | zero => intro s; simp
    | succ n ih =>
      intro s
      rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, ← add_assoc, hshift, ih]
      ring
  intro y
  obtain ⟨n, hn⟩ := exists_nat_gt (|y - f 0| / L)
  have habs : |y - f 0| < (n : ℝ) * L := (div_lt_iff₀ hL).mp hn
  have hupper : f ((n : ℝ) * L) = f 0 + (n : ℝ) * L := by
    simpa only [zero_add] using hnat n 0
  have hnegative := hnat n (-((n : ℝ) * L))
  rw [neg_add_cancel] at hnegative
  have hlower : f (-((n : ℝ) * L)) = f 0 - (n : ℝ) * L := by linarith
  apply intermediate_value_univ (-((n : ℝ) * L)) ((n : ℝ) * L) hf
  rw [hlower, hupper]
  exact ⟨by linarith [neg_abs_le (y - f 0)], by linarith [le_abs_self (y - f 0)]⟩

/-- A SINGLE actual small displacement works simultaneously at every original
parameter: phase speed is positive, height displacement speed is negative,
and every positive displacement places the original curve at negative height.
Each fixed small displacement has an actual smooth global real phase inverse,
with its full-period inverse shift. The scalar Gin gluing germ is not claimed. -/
theorem visibleConnectorDisplaced_exists_uniform_phase_signs {L : ℝ} [hL : Fact (0 < L)]
    {p w0 : ℝ → Coord} {w : ℝ × ℝ → Coord} {Omega : Set (ℝ × ℝ)}
    (hp : ContDiff ℝ ∞ p) (hw0 : ContDiff ℝ ∞ w0)
    (hpL : Periodic p L) (hw0L : Periodic w0 L)
    (hwL : ∀ rho, Periodic (fun s => w (rho, s)) L)
    (hip : Injective hpL.lift) (hOmega : IsOpen Omega) (hw : ContDiffOn ℝ ∞ w Omega)
    (haxis : ∀ s, (0, s) ∈ Omega) (hwzero : ∀ s, w (0, s) = w0 s)
    (hdet : ∀ s, visibleConnectorDet (deriv p s) (w0 s) ≠ 0) :
    ∃ e : OpenPartialHomeomorph (ℝ × (AddCircle L × ℝ)) (ℝ × Coord),
      (e : (ℝ × (AddCircle L × ℝ)) → ℝ × Coord) =
        visibleConnectorDisplacedNativePsi hpL hw0L hwL ∧
      (∀ y ∈ e.target, ∃ s : ℝ,
        ∃ a : OpenPartialHomeomorph (ℝ × Coord) (ℝ × Coord),
        ContDiffOn ℝ ∞ a.symm a.target ∧
        ∃ B : Set (ℝ × Coord), IsOpen B ∧ y ∈ B ∧
          B ⊆ e.target ∧ B ⊆ a.target ∧
          (∀ v ∈ B, e.symm v = visibleConnectorDisplacedNativeChart L s (a.symm v))) ∧
      (∀ s, (0, p s) ∈ e.target ∧
        visibleConnectorDisplacedNativeSolution e p (0, s) = (periodProjection L s, 0)) ∧
      (∀ q : AddCircle L, (0, (q, 0)) ∈ e.source) ∧
      IsOpen (visibleConnectorDisplacedRealPhaseDomain e p) ∧
      ContDiffOn ℝ ∞ (visibleConnectorDisplacedRealPhase e p)
        (visibleConnectorDisplacedRealPhaseDomain e p) ∧
      ContDiffOn ℝ ∞ (fun z => (visibleConnectorDisplacedNativeSolution e p z).2)
        (visibleConnectorDisplacedRealPhaseDomain e p) ∧
      (∀ rho s, visibleConnectorDisplacedRealPhase e p (rho, s + L) =
        visibleConnectorDisplacedRealPhase e p (rho, s) + L) ∧
      (∀ rho, Periodic (fun s => (visibleConnectorDisplacedNativeSolution e p (rho, s)).2) L) ∧
      (∀ s, visibleConnectorDisplacedRealPhase e p (0, s) = s) ∧
      (∀ s, (visibleConnectorDisplacedNativeSolution e p (0, s)).2 = 0) ∧
      ∃ eta > 0, ∃ eps > 0, eps ≤ eta ∧
        Icc (-eta) eta ×ˢ (univ : Set ℝ) ⊆ visibleConnectorDisplacedRealPhaseDomain e p ∧
        (∀ rho s, |rho| < eps →
          0 < deriv (fun t => visibleConnectorDisplacedRealPhase e p (rho, t)) s ∧
          deriv (fun r => (visibleConnectorDisplacedNativeSolution e p (r, s)).2) rho < 0) ∧
        (∀ rho s, 0 < rho → rho < eps →
          (visibleConnectorDisplacedNativeSolution e p (rho, s)).2 < 0) ∧
        (∀ rho, |rho| < eps → ∃ A : ℝ ≃ₜ ℝ,
          (A : ℝ → ℝ) = (fun s => visibleConnectorDisplacedRealPhase e p (rho, s)) ∧
          ContDiff ℝ ∞ A.symm ∧ (∀ s, A.symm (s + L) = A.symm s + L)) ∧
        (∀ rho s, |rho| < eps →
          visibleConnectorDisplacedPhi p w0 w rho
            (![visibleConnectorDisplacedRealPhase e p (rho, s),
              (visibleConnectorDisplacedNativeSolution e p (rho, s)).2] : Coord) = p s) := by
  obtain ⟨e, hef, hLocal, hD, ha, hb, hEquation, hShift, hPeriod, hA0, hB0,
    _, hAs0, hBr0, eta, heta, hstrip⟩ :=
    visibleConnectorDisplaced_exists_smooth_real_phase hp hw0 hpL hw0L hwL
      hip hOmega hw haxis hwzero hdet
  have hCentral (s : ℝ) : (0, p s) ∈ e.target ∧
      visibleConnectorDisplacedNativeSolution e p (0, s) = (periodProjection L s, 0) := by
    have hz : (0, s) ∈ visibleConnectorDisplacedRealPhaseDomain e p :=
      hstrip ⟨⟨by linarith, by linarith⟩, mem_univ _⟩
    refine ⟨hz.1, Prod.ext ?_ (hB0 s)⟩
    have hproj := visibleConnectorDisplacedRealPhase_projection e p hz
    rw [hA0 s] at hproj
    exact hproj.symm
  have hSource (q : AddCircle L) : (0, (q, 0)) ∈ e.source := by
    obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective q
    have ht := (hCentral s).1
    have hr := congrArg Prod.fst (e.right_inv ht)
    rw [hef] at hr
    change (e.symm (0, p s)).1 = 0 at hr
    have hi : e.symm (0, p s) = (0, (periodProjection L s, 0)) :=
      Prod.ext hr (hCentral s).2
    have hs := e.map_target ht
    rw [hi] at hs
    exact hs
  let D := visibleConnectorDisplacedRealPhaseDomain e p
  let a := visibleConnectorDisplacedRealPhase e p
  let b := fun z : ℝ × ℝ => (visibleConnectorDisplacedNativeSolution e p z).2
  let R := fun z : ℝ × ℝ => deriv (fun r => b (r, z.2)) z.1
  let S := fun z : ℝ × ℝ => deriv (fun s => a (z.1, s)) z.2
  have hRfd (z : ℝ × ℝ) (hz : z ∈ D) : R z = fderiv ℝ b z (1, 0) := by
    have hf : DifferentiableAt ℝ b z := ((hb _ hz).contDiffAt (hD.mem_nhds hz)).differentiableAt (by simp)
    have hpath : HasDerivAt (fun r : ℝ => (r, z.2)) ((1 : ℝ), (0 : ℝ)) z.1 :=
      (hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2)
    have hc := hf.hasFDerivAt.comp_hasDerivAt z.1 hpath
    simpa only [R, Function.comp_def] using hc.deriv
  have hSfd (z : ℝ × ℝ) (hz : z ∈ D) : S z = fderiv ℝ a z (0, 1) := by
    have hf : DifferentiableAt ℝ a z := ((ha _ hz).contDiffAt (hD.mem_nhds hz)).differentiableAt (by simp)
    have hpath : HasDerivAt (fun s : ℝ => (z.1, s)) ((0 : ℝ), (1 : ℝ)) z.2 :=
      (hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2)
    have hc := hf.hasFDerivAt.comp_hasDerivAt z.2 hpath
    simpa only [S, Function.comp_def] using hc.deriv
  have hRconst : ContinuousOn (fun _ : ℝ × ℝ => ((1 : ℝ), (0 : ℝ))) D :=
    continuous_const.continuousOn
  have hSconst : ContinuousOn (fun _ : ℝ × ℝ => ((0 : ℝ), (1 : ℝ))) D :=
    continuous_const.continuousOn
  have hRc : ContinuousOn R D :=
    (((hb.continuousOn_fderiv_of_isOpen hD (by simp)).clm_apply hRconst).congr
      (fun z hz => hRfd z hz))
  have hSc : ContinuousOn S D :=
    (((ha.continuousOn_fderiv_of_isOpen hD (by simp)).clm_apply hSconst).congr
      (fun z hz => hSfd z hz))
  have hD0 (s : ℝ) : (0, s) ∈ D := hstrip ⟨⟨by linarith, by linarith⟩, mem_univ _⟩
  have hR0 (s : ℝ) : R (0, s) = -1 := (hBr0 s).deriv
  have hS0 (s : ℝ) : S (0, s) = 1 := (hAs0 s).deriv
  let VR := D ∩ R ⁻¹' Iio 0
  have hVR : IsOpen VR := hRc.isOpen_inter_preimage hD isOpen_Iio
  let V := VR ∩ S ⁻¹' Ioi 0
  have hV : IsOpen V := (hSc.mono inter_subset_left).isOpen_inter_preimage hVR isOpen_Ioi
  have hV0 (s : ℝ) : (0, s) ∈ V := by
    refine ⟨⟨hD0 s, ?_⟩, ?_⟩
    · change R (0, s) < 0
      rw [hR0]
      norm_num
    · change 0 < S (0, s)
      rw [hS0]
      norm_num
  let K : Set (ℝ × ℝ) := ({0} : Set ℝ) ×ˢ Icc 0 L
  have hK : IsCompact K := (show IsCompact ({0} : Set ℝ) from isCompact_singleton).prod isCompact_Icc
  have hKV : K ⊆ V := by
    intro z hz
    have hz0 : z.1 = 0 := mem_singleton_iff.mp hz.1
    have he : z = (0, z.2) := Prod.ext hz0 rfl
    rw [he]
    exact hV0 z.2
  obtain ⟨r, hr, hrV⟩ := hK.exists_cthickening_subset_open hV hKV
  let eps := min eta (r / 2)
  have heps : 0 < eps := lt_min heta (half_pos hr)
  have hepsEta : eps ≤ eta := min_le_left _ _
  have hRp (rho : ℝ) : Periodic (fun s => R (rho, s)) L := by
    intro s
    have heq : (fun r => b (r, s + L)) = (fun r => b (r, s)) :=
      funext (fun r => hPeriod r s)
    change deriv (fun r => b (r, s + L)) rho = deriv (fun r => b (r, s)) rho
    rw [heq]
  have hSp (rho : ℝ) : Periodic (fun s => S (rho, s)) L := by
    intro s
    have heq : (fun t => a (rho, t + L)) = (fun t => a (rho, t) + L) :=
      funext (fun t => hShift rho t)
    change deriv (fun t => a (rho, t)) (s + L) = deriv (fun t => a (rho, t)) s
    rw [← deriv_comp_add_const (fun t => a (rho, t)) L s, heq, deriv_add_const]
  have hsign (rho s : ℝ) (hρ : |rho| < eps) : 0 < S (rho, s) ∧ R (rho, s) < 0 := by
    let x := AddCircle.equivIco L 0 (periodProjection L s)
    have hx : (x : ℝ) ∈ Icc 0 L := Ico_subset_Icc_self (by
      simpa only [zero_add] using x.property)
    have hxq : periodProjection L (x : ℝ) = periodProjection L s := AddCircle.coe_equivIco
    have hzV : (rho, (x : ℝ)) ∈ V := by
      apply hrV
      apply Metric.thickening_subset_cthickening r K
      apply Metric.mem_thickening_iff.mpr
      refine ⟨(0, (x : ℝ)), ⟨mem_singleton _, hx⟩, ?_⟩
      rw [Prod.dist_eq, dist_self]
      simp only [Real.dist_eq, sub_zero]
      exact max_lt (lt_trans (lt_of_lt_of_le hρ (min_le_right _ _)) (half_lt_self hr)) hr
    have hReq := congrArg (hRp rho).lift hxq
    have hSeq := congrArg (hSp rho).lift hxq
    rw [periodicLift_coe, periodicLift_coe] at hReq hSeq
    exact ⟨hSeq ▸ hzV.2, hReq ▸ hzV.1.2⟩
  have hnegative (rho s : ℝ) (hρ : 0 < rho) (hρeps : rho < eps) : b (rho, s) < 0 := by
    have hmap : MapsTo (fun t : ℝ => (t, s)) (Icc 0 rho) D := by
      intro t ht
      apply hstrip
      exact ⟨⟨(neg_nonpos.mpr heta.le).trans ht.1,
        ht.2.trans (hρeps.le.trans hepsEta)⟩, mem_univ _⟩
    have hc : ContinuousOn (fun t => b (t, s)) (Icc 0 rho) :=
      hb.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn hmap
    have hanti : StrictAntiOn (fun t => b (t, s)) (Icc 0 rho) :=
      strictAntiOn_of_deriv_neg (convex_Icc 0 rho) hc (by
        intro t ht
        have ht' := interior_subset ht
        have htAbs : |t| < eps := by
          rw [abs_of_nonneg ht'.1]
          exact lt_of_le_of_lt ht'.2 hρeps
        exact (hsign t s htAbs).2)
    have hlt := hanti ⟨le_rfl, hρ.le⟩ ⟨hρ.le, le_rfl⟩ hρ
    change b (rho, s) < b (0, s) at hlt
    have hb0 : b (0, s) = 0 := hB0 s
    rw [hb0] at hlt
    exact hlt
  have hHomeo (rho : ℝ) (hρ : |rho| < eps) : ∃ A : ℝ ≃ₜ ℝ,
      (A : ℝ → ℝ) = (fun s => a (rho, s)) ∧
      ContDiff ℝ ∞ A.symm ∧ (∀ s, A.symm (s + L) = A.symm s + L) := by
    have hsliceMap : MapsTo (fun s : ℝ => (rho, s)) univ D := by
      intro s _
      apply hstrip
      exact ⟨(abs_le.mp (le_trans hρ.le hepsEta)), mem_univ _⟩
    have hf : ContDiff ℝ ∞ (fun s => a (rho, s)) := contDiffOn_univ.mp
      (ha.comp (contDiff_const.prodMk contDiff_id).contDiffOn hsliceMap)
    have hpos (s : ℝ) : 0 < deriv (fun t => a (rho, t)) s := (hsign rho s hρ).1
    have hm : StrictMono (fun s => a (rho, s)) := strictMono_of_deriv_pos hpos
    have hsur := displaced_phase_surjective hf.continuous hL.out (hShift rho)
    let A := (StrictMono.orderIsoOfSurjective (fun s => a (rho, s)) hm hsur).toHomeomorph
    have hAf : (A : ℝ → ℝ) = (fun s => a (rho, s)) := rfl
    refine ⟨A, hAf, ?_, ?_⟩
    · apply contDiff_iff_contDiffAt.mpr
      intro s
      let F := A.toOpenPartialHomeomorph
      have hder := ((hf.differentiable (by simp) (A.symm s)).hasDerivAt).hasFDerivAt_equiv
        (ne_of_gt (hpos (A.symm s)))
      exact F.contDiffAt_symm (by simp [F])
        (f₀' := ContinuousLinearEquiv.unitsEquivAut ℝ
          (Units.mk0 (deriv (fun t => a (rho, t)) (A.symm s))
            (ne_of_gt (hpos (A.symm s)))))
        (by change HasFDerivAt A _ _; rw [hAf]; exact hder)
        (by change ContDiffAt ℝ ∞ A _; rw [hAf]; exact hf.contDiffAt)
    · intro s
      apply A.injective
      rw [A.apply_symm_apply]
      change s + L = a (rho, A.symm s + L)
      have hs : a (rho, A.symm s + L) = a (rho, A.symm s) + L := hShift rho (A.symm s)
      rw [hs]
      have hi : a (rho, A.symm s) = s := A.apply_symm_apply s
      rw [hi]
  refine ⟨e, hef, hLocal, hCentral, hSource, hD, ha, hb, hShift, hPeriod, hA0, hB0,
    eta, heta, eps, heps, hepsEta, hstrip, hsign, hnegative, hHomeo, ?_⟩
  intro rho s hρ
  apply hEquation
  apply hstrip
  exact ⟨abs_le.mp (le_trans hρ.le hepsEta), mem_univ _⟩

end
end TightVer401