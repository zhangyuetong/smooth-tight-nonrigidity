import TightVer401.ScalarCellPaste
import TightVer401.ScalarFlowPeriodReparameter

namespace TightVer401
noncomputable section
open Set Filter Metric OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

def scalarCellFinitePaste (r : ℕ → ℝ) (w : ℕ → Coord → ℝ) : ℕ → Coord → ℝ
  | 0 => w 0
  | n+1 => scalarCellPaste (r (n+1)) (scalarCellFinitePaste r w n) (w (n+1))

def scalarCellFiniteDomain (r : ℕ → ℝ) (ε : ℝ) (V : Set ℝ) (n : ℕ) : Set Coord :=
  {q | -ε/4 < q 0 ∧ q 0 < r n + ε/4 ∧ q 1 ∈ V}

theorem scalarCellFiniteDomain_isOpen {r : ℕ → ℝ} {ε : ℝ} {V : Set ℝ}
    (hV : IsOpen V) (n : ℕ) : IsOpen (scalarCellFiniteDomain r ε V n) :=
  (isOpen_lt continuous_const (continuous_apply 0)).inter
    ((isOpen_lt (continuous_apply 0) continuous_const).inter
      (hV.preimage (continuous_apply 1)))

theorem scalarCellFinitePaste_tail_germ (r : ℕ → ℝ) (w : ℕ → Coord → ℝ)
    (n : ℕ) {q : Coord} (hq : r n < q 0) :
    scalarCellFinitePaste r w n =ᶠ[𝓝 q] w n := by
  cases n with
  | zero => exact Filter.EventuallyEq.rfl
  | succ n =>
    have hn : ∀ᶠ p : Coord in 𝓝 q, r (n+1) < p 0 :=
      ((continuous_apply 0) : Continuous (fun p : Coord => p 0)).continuousAt.eventually
        (lt_mem_nhds hq)
    filter_upwards [hn] with p hp
    exact if_neg (not_lt_of_ge hp.le)

theorem scalarCellFiniteDomain_step_subset {r : ℕ → ℝ} {ε : ℝ} {V : Set ℝ} {n : ℕ}
    (hε : 0 < ε) (hstep : 0 < r (n+1)-r n) (hsmall : r (n+1)-r n < ε/4) :
    scalarCellFiniteDomain r ε V (n+1) ⊆
      scalarCellPasteDomain (r (n+1)) (scalarCellFiniteDomain r ε V n)
        (scalarCellStrip (r (n+1)) ε V) := by
  intro q hq
  refine ⟨?_,?_⟩
  · intro ht
    exact ⟨hq.1,by linarith,hq.2.2⟩
  · intro ht
    refine ⟨?_,hq.2.2⟩
    rw [abs_of_nonneg (sub_nonneg.mpr ht)]
    linarith [hq.2.1]

theorem scalarCellFinitePaste_properties {r : ℕ → ℝ} {w : ℕ → Coord → ℝ}
    {ε : ℝ} {V : Set ℝ} {W : Set Coord} {f : Coord → ℝ} {N : ℕ}
    (hε : 0 < ε) (hr0 : r 0 = 0) (hV : IsOpen V)
    (hstep : ∀ j < N, 0 < r (j+1)-r j)
    (hsmall : ∀ j < N, r (j+1)-r j < ε/4)
    (hw : ∀ j ≤ N, ContDiffOn ℝ ∞ (w j) (scalarCellStrip (r j) ε V))
    (himage : ∀ j ≤ N, ∀ q ∈ scalarCellStrip (r j) ε V, (![q 0,w j q] : Coord) ∈ W)
    (hode : ∀ j ≤ N, ∀ q ∈ scalarCellStrip (r j) ε V,
      coordPartial 0 (w j) q = f ![q 0,w j q])
    (hag : ∀ j < N, ∀ x ∈ V,
      w j =ᶠ[𝓝 (![r (j+1),x] : Coord)] w (j+1)) :
    ∀ n ≤ N,
      ContDiffOn ℝ ∞ (scalarCellFinitePaste r w n) (scalarCellFiniteDomain r ε V n) ∧
      (∀ q ∈ scalarCellFiniteDomain r ε V n,
        (![q 0,scalarCellFinitePaste r w n q] : Coord) ∈ W) ∧
      ∀ q ∈ scalarCellFiniteDomain r ε V n,
        coordPartial 0 (scalarCellFinitePaste r w n) q =
          f ![q 0,scalarCellFinitePaste r w n q] := by
  intro n hn
  induction n with
  | zero =>
    have hs : scalarCellFiniteDomain r ε V 0 ⊆ scalarCellStrip (r 0) ε V := by
      intro q hq
      refine ⟨?_,hq.2.2⟩
      rw [hr0,sub_zero,abs_lt]
      constructor <;> linarith [hq.1,hq.2.1]
    exact ⟨(hw 0 (Nat.zero_le N)).mono hs,
      fun q hq => himage 0 (Nat.zero_le N) q (hs hq),
      fun q hq => hode 0 (Nat.zero_le N) q (hs hq)⟩
  | succ n ih =>
    have hnN : n < N := Nat.lt_of_succ_le hn
    obtain ⟨hs,hi,ho⟩ := ih (Nat.le_of_lt hnN)
    have hc : ∀ q ∈ scalarCellFiniteDomain r ε V n ∩ scalarCellStrip (r (n+1)) ε V,
        q 0 = r (n+1) → scalarCellFinitePaste r w n =ᶠ[𝓝 q] w (n+1) := by
      intro q hq hqt
      have he : (![r (n+1),q 1] : Coord) = q := by
        ext i
        fin_cases i
        · exact hqt.symm
        · rfl
      have hg := hag n hnN (q 1) hq.2.2
      rw [he] at hg
      exact (scalarCellFinitePaste_tail_germ r w n (by linarith [hstep n hnN])).trans hg
    have hm := scalarCellFiniteDomain_step_subset (V := V) hε (hstep n hnN) (hsmall n hnN)
    refine ⟨(scalarCellPaste_contDiffOn (scalarCellFiniteDomain_isOpen hV n)
      (scalarCellStrip_isOpen hV) hs (hw (n+1) hn) hc).mono hm,?_,?_⟩
    · exact fun q hq => scalarCellPaste_image hi (himage (n+1) hn) q (hm hq)
    · exact fun q hq => scalarCellPaste_ode hc ho (hode (n+1) hn) q (hm hq)

theorem scalarCellFiniteTime_nonneg {r : ℕ → ℝ} {N : ℕ} (hr0 : r 0 = 0)
    (hstep : ∀ j < N, 0 < r (j+1)-r j) : ∀ n ≤ N, 0 ≤ r n := by
  intro n hn
  induction n with
  | zero => rw [hr0]
  | succ n ih =>
    have ht := hstep n (Nat.lt_of_succ_le hn)
    have hp := ih (Nat.le_of_succ_le hn)
    linarith

theorem scalarCellFinitePaste_central {r : ℕ → ℝ} {w : ℕ → Coord → ℝ}
    {ε : ℝ} {V : Set ℝ} {N : ℕ}
    (hε : 0 < ε) (hr0 : r 0 = 0)
    (hstep : ∀ j < N, 0 < r (j+1)-r j)
    (hsmall : ∀ j < N, r (j+1)-r j < ε/4)
    (hcentral : ∀ j ≤ N, ∀ t, |t-r j| < ε → w j ![t,0] = 0) :
    ∀ n ≤ N, ∀ t, (![t,0] : Coord) ∈ scalarCellFiniteDomain r ε V n →
      scalarCellFinitePaste r w n ![t,0] = 0 := by
  intro n hn
  induction n with
  | zero =>
    intro t ht
    change -ε/4 < t ∧ t < r 0 + ε/4 ∧ (0 : ℝ) ∈ V at ht
    rw [hr0,zero_add] at ht
    exact hcentral 0 (Nat.zero_le N) t (by
      rw [hr0,sub_zero,abs_lt]
      constructor <;> linarith [ht.1,ht.2.1])
  | succ n ih =>
    intro t ht
    have hm := scalarCellFiniteDomain_step_subset (V := V) hε
      (hstep n (Nat.lt_of_succ_le hn)) (hsmall n (Nat.lt_of_succ_le hn)) ht
    change (if t < r (n+1) then scalarCellFinitePaste r w n ![t,0] else w (n+1) ![t,0]) = 0
    split
    · exact ih (Nat.le_of_succ_le hn) t (hm.1 ‹t < r (n+1)›.le)
    · exact hcentral (n+1) hn t (hm.2 (le_of_not_gt ‹¬t < r (n+1)›)).1

theorem scalarCellFinitePaste_initial {r : ℕ → ℝ} {w : ℕ → Coord → ℝ}
    {N : ℕ} (hr0 : r 0 = 0) (hstep : ∀ j < N, 0 < r (j+1)-r j) :
    ∀ n ≤ N, ∀ x : ℝ, scalarCellFinitePaste r w n ![0,x] = w 0 ![0,x] := by
  intro n hn
  induction n with
  | zero => intro x; rfl
  | succ n ih =>
    intro x
    have hp := scalarCellFiniteTime_nonneg hr0 hstep n (Nat.le_of_succ_le hn)
    have hs := hstep n (Nat.lt_of_succ_le hn)
    have ht : (0 : ℝ) < r (n+1) := by linarith
    change (if (0 : ℝ) < r (n+1) then scalarCellFinitePaste r w n ![0,x]
      else w (n+1) ![0,x]) = _
    rw [if_pos ht]
    exact ih (Nat.le_of_succ_le hn) x

theorem exists_scalarCellFinitePaste {r : ℕ → ℝ} {w : ℕ → Coord → ℝ}
    {ε : ℝ} {V : Set ℝ} {W : Set Coord} {f : Coord → ℝ} {N : ℕ}
    (hε : 0 < ε) (hr0 : r 0 = 0) (hV : IsOpen V) (h0V : (0 : ℝ) ∈ V)
    (hstep : ∀ j < N, 0 < r (j+1)-r j)
    (hsmall : ∀ j < N, r (j+1)-r j < ε/4)
    (hw : ∀ j ≤ N, ContDiffOn ℝ ∞ (w j) (scalarCellStrip (r j) ε V))
    (himage : ∀ j ≤ N, ∀ q ∈ scalarCellStrip (r j) ε V, (![q 0,w j q] : Coord) ∈ W)
    (hode : ∀ j ≤ N, ∀ q ∈ scalarCellStrip (r j) ε V,
      coordPartial 0 (w j) q = f ![q 0,w j q])
    (hag : ∀ j < N, ∀ x ∈ V,
      w j =ᶠ[𝓝 (![r (j+1),x] : Coord)] w (j+1))
    (hcentral : ∀ j ≤ N, ∀ t, |t-r j| < ε → w j ![t,0] = 0)
    (hinit : ∀ x ∈ V, w 0 ![0,x] = x) :
    ∃ (u : Coord → ℝ) (D : Set Coord), IsOpen D ∧ ContDiffOn ℝ ∞ u D ∧
      (∀ q ∈ D, (![q 0,u q] : Coord) ∈ W) ∧
      (∀ q ∈ D, coordPartial 0 u q = f ![q 0,u q]) ∧
      (∀ t ∈ Icc (0 : ℝ) (r N), (![t,0] : Coord) ∈ D ∧ u ![t,0] = 0) ∧
      (fun x : ℝ => u ![0,x]) =ᶠ[𝓝 (0 : ℝ)] id := by
  have hp := scalarCellFinitePaste_properties hε hr0 hV hstep hsmall hw himage hode hag N le_rfl
  refine ⟨scalarCellFinitePaste r w N,scalarCellFiniteDomain r ε V N,
    scalarCellFiniteDomain_isOpen hV N,hp.1,hp.2.1,hp.2.2,?_,?_⟩
  · intro t ht
    have hd : (![t,0] : Coord) ∈ scalarCellFiniteDomain r ε V N := by
      change -ε/4 < t ∧ t < r N + ε/4 ∧ (0 : ℝ) ∈ V
      exact ⟨by linarith [ht.1],by linarith [ht.2],h0V⟩
    exact ⟨hd,scalarCellFinitePaste_central hε hr0 hstep hsmall hcentral N le_rfl t hd⟩
  · filter_upwards [hV.mem_nhds h0V] with x hx
    exact (scalarCellFinitePaste_initial hr0 hstep N le_rfl x).trans (hinit x hx)

end
end TightVer401

