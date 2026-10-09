import TightVer401.TorusAffineMarkerEllipseBasic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-! Actual ellipse connectedness and diameter. Neither boundary permutation
nor radius recognition is assumed. The literal semiaxes R,2R give diameter 4R,
so an ambient isometry between two such ellipses forces equal positive radii. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped Matrix Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
def torusAffineMarkerIsometryHomeomorph (L : Ambient ≃ₗᵢ[ℝ] Ambient) (b : Ambient) : Ambient ≃ₜ Ambient where
  toFun := torusAffineMarkerIsometry L b
  invFun q := L.symm (q-b)
  left_inv q := by simp [torusAffineMarkerIsometry]
  right_inv q := by simp [torusAffineMarkerIsometry]
  continuous_toFun := L.continuous.add continuous_const
  continuous_invFun := L.symm.continuous.comp (continuous_id.sub continuous_const)

def torusAffineMarkerEllipseParam (c : Ambient) (a b : ℝ) (z : Circle) : Ambient :=
  torusAffineMarkerVec (c 0+a*(z : ℂ).re) (c 1+b*(z : ℂ).im) (c 2)

theorem torusAffineMarkerEllipseParam_continuous (c : Ambient) (a b : ℝ) : Continuous (torusAffineMarkerEllipseParam c a b) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i <;> fun_prop

theorem torusAffineMarkerEllipseParam_range (c : Ambient) {a b : ℝ} (ha : a≠0) (hb : b≠0) :
    range (torusAffineMarkerEllipseParam c a b)=torusAffineMarkerEllipse c a b := by
  ext q
  constructor
  · rintro ⟨z,rfl⟩
    refine ⟨rfl,?_⟩
    change ((c 0+a*(z : ℂ).re-c 0)/a)^2+((c 1+b*(z : ℂ).im-c 1)/b)^2=1
    have he := z.normSq_coe
    rw [Complex.normSq_apply] at he
    field_simp
    linear_combination a^2*b^2*he
  · intro hq
    let z : ℂ := ⟨(q 0-c 0)/a,(q 1-c 1)/b⟩
    have hz : ‖z‖=1 := by
      have he : ‖z‖^2=1 := by
        rw [Complex.sq_norm,Complex.normSq_apply]
        change ((q 0-c 0)/a)*((q 0-c 0)/a)+((q 1-c 1)/b)*((q 1-c 1)/b)=1
        nlinarith [hq.2]
      nlinarith [norm_nonneg z]
    let w : Circle := ⟨z,by change dist z 0=1; simpa only [dist_zero_right] using hz⟩
    refine ⟨w,?_⟩
    ext i
    fin_cases i
    · change c 0+a*((q 0-c 0)/a)=q 0
      field_simp
      ring
    · change c 1+b*((q 1-c 1)/b)=q 1
      field_simp
      ring
    · exact hq.1.symm

theorem torusAffineMarkerEllipse_connected (c : Ambient) {a b : ℝ} (ha : a≠0) (hb : b≠0) :
    IsConnected (torusAffineMarkerEllipse c a b) := by
  rw [←torusAffineMarkerEllipseParam_range c ha hb]
  exact isConnected_range (torusAffineMarkerEllipseParam_continuous c a b)

theorem torusAffineMarker_split_pair {X : Type*} (A B P Q : Set X) (hA : A.Nonempty) (hB : B.Nonempty)
    (hd : Disjoint A B) (hu : P ∪ Q=A ∪ B)
    (hP : P⊆A ∨ P⊆B) (hQ : Q⊆A ∨ Q⊆B) :
    (P=A ∧ Q=B) ∨ (P=B ∧ Q=A) := by
  have hsameA : ¬(P⊆A ∧ Q⊆A) := by
    rintro ⟨hp,hq⟩
    obtain ⟨x,hx⟩ := hB
    have hi : x∈P∪Q := hu.symm ▸ Or.inr hx
    exact Set.disjoint_left.mp hd (hi.elim (fun h => hp h) (fun h => hq h)) hx
  have hsameB : ¬(P⊆B ∧ Q⊆B) := by
    rintro ⟨hp,hq⟩
    obtain ⟨x,hx⟩ := hA
    have hi : x∈P∪Q := hu.symm ▸ Or.inl hx
    exact Set.disjoint_left.mp hd hx (hi.elim (fun h => hp h) (fun h => hq h))
  rcases hP with hp|hp <;> rcases hQ with hq|hq
  · exact False.elim (hsameA ⟨hp,hq⟩)
  · apply Or.inl
    constructor
    · apply Subset.antisymm hp
      intro x hx
      have hi : x∈P∪Q := hu.symm ▸ Or.inl hx
      exact hi.elim id (fun hi => False.elim (Set.disjoint_left.mp hd hx (hq hi)))
    · apply Subset.antisymm hq
      intro x hx
      have hi : x∈P∪Q := hu.symm ▸ Or.inr hx
      exact hi.elim (fun hi => False.elim (Set.disjoint_left.mp hd (hp hi) hx)) id
  · apply Or.inr
    constructor
    · apply Subset.antisymm hp
      intro x hx
      have hi : x∈P∪Q := hu.symm ▸ Or.inr hx
      exact hi.elim id (fun hi => False.elim (Set.disjoint_left.mp hd (hq hi) hx))
    · apply Subset.antisymm hq
      intro x hx
      have hi : x∈P∪Q := hu.symm ▸ Or.inl hx
      exact hi.elim (fun hi => False.elim (Set.disjoint_left.mp hd hx (hp hi))) id
  · exact False.elim (hsameB ⟨hp,hq⟩)

theorem torusAffineMarker_connected_ellipse_side {h RN RS : ℝ} (hh : 0<h) {S : Set Ambient}
    (hS : IsPreconnected S)
    (hs : S⊆torusAffineMarkerEllipse (torusAffineMarkerCenter h) RN (2*RN) ∪ torusAffineMarkerEllipse (torusAffineMarkerCenter (-h)) RS (2*RS)) :
    S⊆torusAffineMarkerEllipse (torusAffineMarkerCenter h) RN (2*RN) ∨ S⊆torusAffineMarkerEllipse (torusAffineMarkerCenter (-h)) RS (2*RS) := by
  have hc : Continuous (fun q : Ambient => q 2) :=
    (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 2 : Ambient →L[ℝ] ℝ).continuous
  have hn : ∀q∈S,q 2≠0 := by
    intro q hq
    rcases hs hq with hq|hq
    · have he : q 2=h := hq.1
      rw [he]
      exact hh.ne'
    · have he : q 2= -h := hq.1
      rw [he]
      exact neg_ne_zero.mpr hh.ne'
  rcases hS.mapsTo_Ioi_or_Iio hc.continuousOn hn with hp|hm
  · apply Or.inl
    intro q hq
    rcases hs hq with hn|hn
    · exact hn
    · exfalso
      have ht : 0<q 2 := hp hq
      have he : q 2= -h := hn.1
      linarith
  · apply Or.inr
    intro q hq
    rcases hs hq with hn|hn
    · exfalso
      have ht : q 2<0 := hm hq
      have he : q 2=h := hn.1
      linarith
    · exact hn



private theorem torusAffineMarker_ambient_norm_sq (p : Ambient) :
    ‖p‖ ^ 2 = (p 0) ^ 2 + (p 1) ^ 2 + (p 2) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [Fin.sum_univ_succ]
  ring

/-- Every point of the R,2R ellipse lies in the actual radius-2R center ball. -/
theorem torusAffineMarkerEllipse_dist_center_le (c : Ambient) {R : ℝ}
    (hR : 0 < R) {p : Ambient} (hp : p ∈ torusAffineMarkerEllipse c R (2 * R)) :
    dist p c ≤ 2 * R := by
  let x := (p 0 - c 0) / R
  let y := (p 1 - c 1) / (2 * R)
  have hx : R * x = p 0 - c 0 := by dsimp [x]; field_simp
  have hy : (2 * R) * y = p 1 - c 1 := by dsimp [y]; field_simp
  have hu : x ^ 2 + y ^ 2 = 1 := hp.2
  have hs : ‖p - c‖ ^ 2 = (R * x) ^ 2 + ((2 * R) * y) ^ 2 := by
    rw [torusAffineMarker_ambient_norm_sq]
    simp only [PiLp.sub_apply, hp.1, sub_self, zero_pow (by decide : 2 ≠ 0), add_zero]
    rw [hx, hy]
  rw [dist_eq_norm]
  have hmult := congrArg (fun a : ℝ => (2 * R) ^ 2 * a) hu
  nlinarith [sq_nonneg (R * x), norm_nonneg (p - c)]

/-- Actual diameter of the literal noncircular ellipse. -/
theorem torusAffineMarkerEllipse_diam (c : Ambient) {R : ℝ} (hR : 0 < R) :
    Metric.diam (torusAffineMarkerEllipse c R (2 * R)) = 4 * R := by
  have hbound : torusAffineMarkerEllipse c R (2 * R) ⊆ Metric.closedBall c (2 * R) :=
    fun _ hp => torusAffineMarkerEllipse_dist_center_le c hR hp
  have hb : Bornology.IsBounded (torusAffineMarkerEllipse c R (2 * R)) :=
    Metric.isBounded_closedBall.subset hbound
  apply le_antisymm
  · have ht := Metric.diam_le_of_subset_closedBall (by positivity : 0 ≤ 2 * R) hbound
    linarith
  · let p := torusAffineMarkerVec (c 0) (c 1 + 2 * R) (c 2)
    let q := torusAffineMarkerVec (c 0) (c 1 - 2 * R) (c 2)
    have hp : p ∈ torusAffineMarkerEllipse c R (2 * R) := by
      simp [p, torusAffineMarkerEllipse, torusAffineMarkerVec, hR.ne']
    have hq : q ∈ torusAffineMarkerEllipse c R (2 * R) := by
      simp [q, torusAffineMarkerEllipse, torusAffineMarkerVec, hR.ne']
    have hd : dist p q = 4 * R := by
      rw [dist_eq_norm]
      have hs : ‖p - q‖ ^ 2 = (4 * R) ^ 2 := by
        rw [torusAffineMarker_ambient_norm_sq]
        simp [p, q, torusAffineMarkerVec, PiLp.sub_apply]
        ring
      nlinarith [norm_nonneg (p - q)]
    rw [← hd]
    exact Metric.dist_le_diam_of_mem hb hp hq

/-- An actual ambient affine isometry between marked circles forces equal radii. -/
theorem torusAffineMarkerEllipse_radius_eq_of_image {RN RS : ℝ}
    (hRN : 0 < RN) (hRS : 0 < RS) (c d : Ambient)
    (L : Ambient ≃ₗᵢ[ℝ] Ambient) (b : Ambient)
    (he : torusAffineMarkerIsometry L b '' torusAffineMarkerEllipse c RN (2 * RN) =
      torusAffineMarkerEllipse d RS (2 * RS)) : RN = RS := by
  have hi : Isometry (torusAffineMarkerIsometry L b) := by
    intro p q
    simp only [torusAffineMarkerIsometry, edist_add_right]
    exact L.isometry p q
  have hd := hi.diam_image (torusAffineMarkerEllipse c RN (2 * RN))
  rw [he, torusAffineMarkerEllipse_diam d hRS, torusAffineMarkerEllipse_diam c hRN] at hd
  linarith

end
end TightVer401

