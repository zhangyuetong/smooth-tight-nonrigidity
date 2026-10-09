import TightVer401.VisibleConnectorDisplacedSeamRebase
import Mathlib.Topology.MetricSpace.Thickening

/-! Uniform positivity at the SAME lower inverse graph. The supplied phase
and height are never replaced. Continuity concerns actual ruling coefficients,
not a desired Delta-sign field; compactness produces that sign uniformly. -/
namespace TightVer401
noncomputable section
open Set Function Metric OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix

private theorem lowerDelta_deriv_periodic {f : ℝ → Coord} {L : ℝ}
    (hL : Periodic f L) : Periodic (deriv f) L := by
  intro s
  have he : (fun t => f (t + L)) = f := funext hL
  have hd := congrArg (fun F : ℝ → Coord => deriv F s) he
  simpa only [deriv_comp_add_const] using hd

/-- Actual Delta at a supplied inverse graph is independent of gamma. -/
theorem visibleConnectorOrdinaryFamilyLowerDelta_geometry
    (p gamma w : ℝ → Coord) (a b : ℝ) :
    visibleConnectorDelta p gamma w ![a, b] =
      visibleConnectorA p w a - b * visibleConnectorDet (deriv w a) (w a) := by
  simp only [visibleConnectorDelta, Matrix.cons_val_zero, Matrix.cons_val_one,
    visibleConnectorC]
  ring

/-- Positive central A and continuity of the actual source coefficients give
one two-sided displacement bound at every real period representative. Omega
is the actual coefficient domain and V is the SAME inverse phase domain.
The map (rho,s) ↦ (rho,a(rho,s)) must stay in Omega; this is an ordinary
same-object domain obligation. No lower Delta positivity is a premise. -/
theorem visibleConnectorOrdinaryFamilyLowerDelta_uniform
    {L : ℝ} (hL : 0 < L) {p gamma w : ℝ × ℝ → Coord}
    {a b : ℝ × ℝ → ℝ} {Omega V : Set (ℝ × ℝ)}
    (hV : IsOpen V) (haxis : ∀ s, (0, s) ∈ V)
    (ha : ContinuousOn a V) (hb : ContinuousOn b V)
    (hmap : ∀ z ∈ V, (z.1, a z) ∈ Omega)
    (hA : ContinuousOn (fun z : ℝ × ℝ =>
      visibleConnectorA (fun s => p (z.1, s)) (fun s => w (z.1, s)) z.2) Omega)
    (hDet : ContinuousOn (fun z : ℝ × ℝ =>
      visibleConnectorDet (deriv (fun s => w (z.1, s)) z.2) (w z)) Omega)
    (hpL : ∀ rho, Periodic (fun s => p (rho, s)) L)
    (hwL : ∀ rho, Periodic (fun s => w (rho, s)) L)
    (hshift : ∀ rho s, a (rho, s + L) = a (rho, s) + L)
    (hbL : ∀ rho, Periodic (fun s => b (rho, s)) L)
    (ha0 : ∀ s, a (0, s) = s) (hb0 : ∀ s, b (0, s) = 0)
    (hA0 : ∀ s, 0 < visibleConnectorA (fun t => p (0, t))
      (fun t => w (0, t)) s) :
    ∃ eps > 0, ∀ rho s, |rho| < eps →
      0 < visibleConnectorDelta (fun t => p (rho, t))
        (fun t => gamma (rho, t)) (fun t => w (rho, t))
        ![a (rho, s), b (rho, s)] := by
  let A : ℝ × ℝ → ℝ := fun z =>
    visibleConnectorA (fun s => p (z.1, s)) (fun s => w (z.1, s)) z.2
  let D : ℝ × ℝ → ℝ := fun z =>
    visibleConnectorDet (deriv (fun s => w (z.1, s)) z.2) (w z)
  let f : ℝ × ℝ → ℝ := fun z => A (z.1, a z) - b z * D (z.1, a z)
  have hphase : ContinuousOn (fun z : ℝ × ℝ => (z.1, a z)) V :=
    continuous_fst.continuousOn.prodMk ha
  have hf : ContinuousOn f V :=
    (hA.comp hphase hmap).sub (hb.mul (hDet.comp hphase hmap))
  let W : Set (ℝ × ℝ) := V ∩ f ⁻¹' Ioi (0 : ℝ)
  have hW : IsOpen W := hf.isOpen_inter_preimage hV isOpen_Ioi
  have hW0 (s : ℝ) : (0, s) ∈ W := by
    refine ⟨haxis s, ?_⟩
    change 0 < A (0, a (0, s)) - b (0, s) * D (0, a (0, s))
    rw [ha0 s, hb0 s, zero_mul, sub_zero]
    exact hA0 s
  let K : Set (ℝ × ℝ) := ({0} : Set ℝ) ×ˢ Icc 0 L
  have hK : IsCompact K := isCompact_singleton.prod isCompact_Icc
  have hKW : K ⊆ W := by
    intro z hz
    have hz0 : z.1 = 0 := mem_singleton_iff.mp hz.1
    have he : z = (0, z.2) := Prod.ext hz0 rfl
    rw [he]
    exact hW0 z.2
  obtain ⟨r, hr, hrW⟩ := hK.exists_cthickening_subset_open hW hKW
  have hAPer (rho : ℝ) : Periodic (fun s => A (rho, s)) L := by
    intro s
    dsimp [A]
    unfold visibleConnectorA
    rw [lowerDelta_deriv_periodic (hpL rho) s, hwL rho s]
  have hDPer (rho : ℝ) : Periodic (fun s => D (rho, s)) L := by
    intro s
    dsimp [D]
    rw [lowerDelta_deriv_periodic (hwL rho) s, (show w (rho, s + L) = w (rho, s) from hwL rho s)]
  have hfPer (rho : ℝ) : Periodic (fun s => f (rho, s)) L := by
    intro s
    dsimp [f]
    rw [hshift rho s, (show b (rho, s + L) = b (rho, s) from hbL rho s), (show A (rho, a (rho, s) + L) = A (rho, a (rho, s)) from hAPer rho (a (rho, s))), (show D (rho, a (rho, s) + L) = D (rho, a (rho, s)) from hDPer rho (a (rho, s)))]
  refine ⟨r / 2, half_pos hr, ?_⟩
  intro rho s hsmall
  obtain ⟨n, hn, _⟩ := existsUnique_sub_zsmul_mem_Ico hL s 0
  simp only [mem_Ico, zero_add] at hn
  have hzW : (rho, s - n • L) ∈ W := by
    apply hrW
    apply Metric.thickening_subset_cthickening r K
    apply Metric.mem_thickening_iff.mpr
    refine ⟨(0, s - n • L), ⟨mem_singleton _, hn.1, hn.2.le⟩, ?_⟩
    rw [Prod.dist_eq, dist_self]
    simp only [Real.dist_eq, sub_zero]
    exact max_lt (hsmall.trans (half_lt_self hr)) hr
  have hfpos : 0 < f (rho, s) := by
    have hh : 0 < f (rho, s - n • L) := hzW.2
    rw [(hfPer rho).sub_zsmul_eq n] at hh
    exact hh
  rw [visibleConnectorOrdinaryFamilyLowerDelta_geometry]
  exact hfpos

end
end TightVer401



