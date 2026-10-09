import TightVer401.TorusAffineMarkerEllipseBasic

/-! Elementary recognition of the literal noncircular ellipse in actual Ambient.
The enclosing-ball center and longest axis are unique; orthogonality fixes the
remaining axes. No external recognition hypothesis is used. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped Matrix RealInnerProductSpace
set_option maxHeartbeats 1200000

@[simp] private theorem marker_fin20 : (2 : Fin 3) ≠ 0 := by decide
@[simp] private theorem marker_fin21 : (2 : Fin 3) ≠ 1 := by decide
@[simp] private theorem marker_fin10 : (1 : Fin 3) ≠ 0 := by decide
@[simp] private theorem marker_fin02 : (0 : Fin 3) ≠ 2 := by decide
@[simp] private theorem marker_fin12 : (1 : Fin 3) ≠ 2 := by decide
@[simp] private theorem marker_fin01 : (0 : Fin 3) ≠ 1 := by decide

private def markerAxis (i : Fin 3) : Ambient :=
  WithLp.toLp 2 (fun j => if j = i then 1 else 0)

@[simp] private theorem markerAxis_apply (i j : Fin 3) :
    markerAxis i j = if j = i then 1 else 0 := rfl

private theorem marker_norm_sq (p : Ambient) :
    ‖p‖ ^ 2 = (p 0)^2 + (p 1)^2 + (p 2)^2 := by
  simpa [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs, add_assoc] using
    PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ) p

private theorem marker_inner (p q : Ambient) :
    inner ℝ p q = p 0 * q 0 + p 1 * q 1 + p 2 * q 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three, mul_comm]

private theorem marker_ellipse_polynomial {p c : Ambient} {a e : ℝ}
    (ha : 0 < a) (he : 0 < e) (hp : p ∈ torusAffineMarkerEllipse c a e) :
    e^2 * (p 0-c 0)^2 + a^2 * (p 1-c 1)^2 = a^2*e^2 := by
  have h := hp.2
  field_simp [ha.ne', he.ne'] at h
  nlinarith [h]

private theorem marker_ellipse_bound {p c : Ambient} {a e : ℝ}
    (ha : 0 < a) (hae : a < e) (hp : p ∈ torusAffineMarkerEllipse c a e) :
    ‖p-c‖^2 ≤ e^2 := by
  have he : 0 < e := ha.trans hae
  have h := marker_ellipse_polynomial ha he hp
  have hz : p 2 = c 2 := hp.1
  rw [marker_norm_sq]
  simp only [PiLp.sub_apply, hz, sub_self, zero_pow (by decide : 2 ≠ 0), add_zero]
  have hgap : 0 < e^2-a^2 := by nlinarith
  have hn := mul_nonneg hgap.le (sq_nonneg (p 0-c 0))
  have hapos : 0 < a^2 := sq_pos_of_pos ha
  nlinarith

private theorem marker_ellipse_longest {p : Ambient} {a e : ℝ}
    (ha : 0 < a) (hae : a < e)
    (hp : p ∈ torusAffineMarkerEllipse 0 a e) (hn : ‖p‖^2 = e^2) :
    p = e • markerAxis 1 ∨ p = (-e) • markerAxis 1 := by
  have he : 0 < e := ha.trans hae
  have h := marker_ellipse_polynomial ha he hp
  have hz : p 2 = 0 := by simpa using hp.1
  have hns := marker_norm_sq p
  rw [hz] at hns
  simp only [zero_pow (by decide : 2 ≠ 0), add_zero] at hns
  have hgap : e^2-a^2 ≠ 0 := by nlinarith
  have hxprod : (e^2-a^2)*(p 0)^2 = 0 := by
    simp only [PiLp.zero_apply, sub_zero] at h
    nlinarith
  have hx2 : (p 0)^2 = 0 := (mul_eq_zero.mp hxprod).resolve_left hgap
  have hx : p 0 = 0 := by nlinarith [sq_nonneg (p 0)]
  have hy2 : (p 1)^2 = e^2 := by nlinarith
  rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hy2) with hy | hy
  · left; ext i; fin_cases i <;> simp [PiLp.smul_apply, hx, hy, hz]
  · right; ext i; fin_cases i <;> simp [PiLp.smul_apply, hx, hy, hz]

private theorem marker_ellipse_endpoint (c : Ambient) {a e : ℝ}
    (ha : 0 < a) (he : 0 < e) (sign : ℝ) (hsign : sign^2 = 1) :
    c + (sign*e) • markerAxis 1 ∈ torusAffineMarkerEllipse c a e := by
  constructor
  · simp [PiLp.add_apply, PiLp.smul_apply]
  · simpa [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, ha.ne', he.ne'] using hsign

/-- The exact classical interface is proved by elementary Euclidean algebra. -/
theorem markerEllipseAxesRecognition_proved : MarkerEllipseAxesRecognition := by
  intro L b c d a e ha hae himage
  have he : 0 < e := ha.trans hae
  let k : Ambient := L c+b
  have hball : ∀ q ∈ torusAffineMarkerEllipse d a e, ‖q-k‖^2 ≤ e^2 := by
    intro q hq
    rw [← himage] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    have heq : torusAffineMarkerIsometry L b p-k = L (p-c) := by
      rw [map_sub]
      dsimp [torusAffineMarkerIsometry, k]
      abel
    rw [heq, L.norm_map]
    exact marker_ellipse_bound ha hae hp
  have hplus := hball (d+e • markerAxis 1)
    (by simpa using marker_ellipse_endpoint d ha he 1 (by norm_num))
  have hminus := hball (d+(-e) • markerAxis 1)
    (by simpa using marker_ellipse_endpoint d ha he (-1) (by norm_num))
  rw [marker_norm_sq] at hplus hminus
  simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, markerAxis_apply] at hplus hminus
  simp at hplus hminus
  have hk0 : k 0 = d 0 := by nlinarith [sq_nonneg (d 0-k 0), sq_nonneg (d 1-k 1), sq_nonneg (d 2-k 2)]
  have hk1 : k 1 = d 1 := by nlinarith [sq_nonneg (d 0-k 0), sq_nonneg (d 1-k 1), sq_nonneg (d 2-k 2)]
  have hk2 : k 2 = d 2 := by nlinarith [sq_nonneg (d 0-k 0), sq_nonneg (d 1-k 1), sq_nonneg (d 2-k 2)]
  have hk : k = d := by ext i; fin_cases i <;> assumption
  refine ⟨hk, ?_⟩
  have hcentered : ∀ p ∈ torusAffineMarkerEllipse 0 a e,
      L p ∈ torusAffineMarkerEllipse 0 a e := by
    intro p hp
    have hpc : c+p ∈ torusAffineMarkerEllipse c a e := by
      constructor
      · have hz : p 2 = 0 := by simpa using hp.1
        simp [PiLp.add_apply, hz]
      · simpa [PiLp.add_apply] using hp.2
    have hq : torusAffineMarkerIsometry L b (c+p) ∈ torusAffineMarkerEllipse d a e := by
      rw [← himage]; exact mem_image_of_mem _ hpc
    have heq : torusAffineMarkerIsometry L b (c+p) = d+L p := by
      simp only [torusAffineMarkerIsometry, map_add]
      change L c+L p+b = d+L p
      rw [← hk]; dsimp [k]; abel
    rw [heq] at hq
    constructor
    · have hz := hq.1
      simpa [PiLp.add_apply] using hz
    · simpa [PiLp.add_apply] using hq.2
  have hAxisNorm (i : Fin 3) : ‖L (markerAxis i)‖^2 = 1 := by
    rw [L.norm_map, marker_norm_sq]
    fin_cases i <;> norm_num <;> decide
  have hp1 : e • markerAxis 1 ∈ torusAffineMarkerEllipse 0 a e := by
    simpa using marker_ellipse_endpoint (0 : Ambient) ha he 1 (by norm_num)
  have hl1 := hcentered _ hp1
  have hn1 : ‖L (e • markerAxis 1)‖^2 = e^2 := by
    rw [L.norm_map, marker_norm_sq]
    simp [PiLp.smul_apply]
  obtain ⟨s1, hs1, hcol1⟩ : ∃ s1 : ℝ, (s1 = 1 ∨ s1 = -1) ∧
      L (markerAxis 1) = s1 • markerAxis 1 := by
    rcases marker_ellipse_longest ha hae hl1 hn1 with h | h
    · refine ⟨1, Or.inl rfl, ?_⟩
      have hc : e • L (markerAxis 1) = e • markerAxis 1 := by simpa using h
      have hh : L (markerAxis 1) = markerAxis 1 := smul_right_injective Ambient he.ne' hc
      simpa only [one_smul] using hh
    · refine ⟨-1, Or.inr rfl, ?_⟩
      have hc : e • L (markerAxis 1) = e • ((-1 : ℝ) • markerAxis 1) := by
        simpa [smul_smul] using h
      exact smul_right_injective Ambient he.ne' hc
  have hs1ne : s1 ≠ 0 := by rcases hs1 with h | h <;> simp [h]
  have hp0 : a • markerAxis 0 ∈ torusAffineMarkerEllipse 0 a e := by
    constructor <;> simp [PiLp.smul_apply, ha.ne']
  have hl0 := hcentered _ hp0
  have h02 : L (markerAxis 0) 2 = 0 := by
    have hz := hl0.1
    simp only [map_smul, PiLp.smul_apply, PiLp.zero_apply] at hz
    exact (mul_eq_zero.mp hz).resolve_left ha.ne'
  have horth01 := L.inner_map_map (markerAxis 0) (markerAxis 1)
  rw [hcol1] at horth01
  have h01 : L (markerAxis 0) 1 = 0 := by
    simp [marker_inner, PiLp.smul_apply] at horth01
    exact horth01.resolve_right hs1ne
  have h00sq : (L (markerAxis 0) 0)^2 = 1 := by
    have hn := hAxisNorm 0
    rw [marker_norm_sq, h01, h02] at hn
    simpa using hn
  let s0 : ℝ := L (markerAxis 0) 0
  have hs0 : s0 = 1 ∨ s0 = -1 := sq_eq_one_iff.mp h00sq
  have hs0ne : s0 ≠ 0 := by rcases hs0 with h | h <;> simp [h]
  have hcol0 : L (markerAxis 0) = s0 • markerAxis 0 := by
    ext i; fin_cases i <;> simp [s0, PiLp.smul_apply, h01, h02]
  have horth20 := L.inner_map_map (markerAxis 2) (markerAxis 0)
  have horth21 := L.inner_map_map (markerAxis 2) (markerAxis 1)
  rw [hcol0] at horth20
  rw [hcol1] at horth21
  have h20 : L (markerAxis 2) 0 = 0 := by
    simp [marker_inner, PiLp.smul_apply] at horth20
    exact horth20.resolve_right hs0ne
  have h21 : L (markerAxis 2) 1 = 0 := by
    simp [marker_inner, PiLp.smul_apply] at horth21
    exact horth21.resolve_right hs1ne
  have h22sq : (L (markerAxis 2) 2)^2 = 1 := by
    have hn := hAxisNorm 2
    rw [marker_norm_sq, h20, h21] at hn
    simpa using hn
  let s2 : ℝ := L (markerAxis 2) 2
  have hs2 : s2 = 1 ∨ s2 = -1 := sq_eq_one_iff.mp h22sq
  have hcol2 : L (markerAxis 2) = s2 • markerAxis 2 := by
    ext i; fin_cases i <;> simp [s2, PiLp.smul_apply, h20, h21]
  refine ⟨![s0,s1,s2], ?_, ?_⟩
  · intro i
    fin_cases i
    · simpa using hs0
    · simpa using hs1
    · simpa using hs2
  · intro p i
    have hpdecomp : p = p 0 • markerAxis 0 + p 1 • markerAxis 1 + p 2 • markerAxis 2 := by
      ext j; fin_cases j <;> simp [PiLp.add_apply, PiLp.smul_apply]
    rw [hpdecomp, map_add, map_add, map_smul, map_smul, map_smul,
      hcol0, hcol1, hcol2]
    fin_cases i <;> simp [PiLp.add_apply, PiLp.smul_apply, smul_smul, mul_comm]

end
end TightVer401
