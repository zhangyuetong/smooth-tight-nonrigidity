import TightVer401.FermiSupportRegularity
import TightVer401.ExitPositiveGraphUniform

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

def scalarFlowJacobian (u : Coord → ℝ) (r : ℝ) : ℝ := coordPartial 1 u ![r, 0]
def scalarFlowLinearCoefficient (f : Coord → ℝ) (r : ℝ) : ℝ := coordPartial 1 f ![r, 0]

theorem scalarFlow_rhs_transverse {u f : Coord → ℝ} {V W : Set Coord}
    (hV : IsOpen V) (hW : IsOpen W) (hu : ContDiffOn ℝ ∞ u V)
    (hf : ContDiffOn ℝ ∞ f W)
    (himage : ∀ q ∈ V, (![q 0, u q] : Coord) ∈ W)
    {r : ℝ} (hr : (![r, 0] : Coord) ∈ V) (hzero : u ![r, 0] = 0) :
    coordPartial 1 (fun q => f ![q 0, u q]) ![r, 0] =
      scalarFlowLinearCoefficient f r * scalarFlowJacobian u r := by
  let p : Coord := ![r, 0]
  have du := ((hu p hr).contDiffAt (hV.mem_nhds hr)).differentiableAt (by simp)
  have df := ((hf _ (himage p hr)).contDiffAt (hW.mem_nhds (himage p hr))).differentiableAt (by simp)
  have hg := ((ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)).hasFDerivAt (x := p)).smul_const
    (Pi.single 0 1 : Coord) |>.add (du.hasFDerivAt.smul_const (Pi.single 1 1 : Coord))
  have hm : (fun q : Coord => q 0 • (Pi.single 0 1 : Coord) + u q • (Pi.single 1 1 : Coord)) =
      (fun q => (![q 0, u q] : Coord)) := by
    funext q
    ext i
    fin_cases i <;> simp
  change HasFDerivAt
    (fun q : Coord => q 0 • (Pi.single 0 1 : Coord) + u q • (Pi.single 1 1 : Coord))
    ((ContinuousLinearMap.proj (R := ℝ) 0).smulRight (Pi.single 0 1 : Coord) +
      (fderiv ℝ u p).smulRight (Pi.single 1 1 : Coord)) p at hg
  rw [hm] at hg
  have hd := df.hasFDerivAt.comp p hg
  change fderiv ℝ (f ∘ fun q => (![q 0, u q] : Coord)) p (Pi.single 1 1) = _
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply,
    Pi.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1), zero_smul, zero_add]
  rw [map_smul]
  simp only [p, hzero, Matrix.cons_val_zero, coordPartial, scalarFlowJacobian,
    scalarFlowLinearCoefficient, smul_eq_mul]
  ring

theorem scalarFlow_variation_hasDerivAt {u f : Coord → ℝ} {V W : Set Coord}
    (hV : IsOpen V) (hW : IsOpen W) (hu : ContDiffOn ℝ ∞ u V)
    (hf : ContDiffOn ℝ ∞ f W)
    (himage : ∀ q ∈ V, (![q 0, u q] : Coord) ∈ W)
    (hode : ∀ q ∈ V, coordPartial 0 u q = f ![q 0, u q])
    {r : ℝ} (hr : (![r, 0] : Coord) ∈ V) (hzero : u ![r, 0] = 0) :
    HasDerivAt (scalarFlowJacobian u)
      (scalarFlowLinearCoefficient f r * scalarFlowJacobian u r) r := by
  have hd := fermiSupport_seam_hasDerivAt hV (partial_contDiffOn hu hV 1) hr
  have he : coordPartial 0 u =ᶠ[𝓝 (![r, 0] : Coord)] (fun q => f ![q 0, u q]) := by
    filter_upwards [hV.mem_nhds hr] with q hq
    exact hode q hq
  have ht := (fermiCoordinatePartial_eventuallyEq he 1).eq_of_nhds
  rw [coordPartial_comm hu hV hr 0 1, ht,
    scalarFlow_rhs_transverse hV hW hu hf himage hr hzero] at hd
  exact hd

theorem scalarFlowJacobian_initial {u : Coord → ℝ} {V : Set Coord}
    (hV : IsOpen V) (hu : ContDiffOn ℝ ∞ u V) (h0 : (![0, 0] : Coord) ∈ V)
    (hinitial : (fun x : ℝ => u ![0, x]) =ᶠ[𝓝 (0 : ℝ)] id) :
    scalarFlowJacobian u 0 = 1 := by
  have hd := exitGraph_slice_hasDerivAt hV hu h0
  exact hd.unique ((hasDerivAt_id (0 : ℝ)).congr_of_eventuallyEq hinitial)

theorem scalarFlowLinearCoefficient_continuousOn {f : Coord → ℝ} {W : Set Coord}
    {P : ℝ} (hW : IsOpen W) (hf : ContDiffOn ℝ ∞ f W)
    (hseam : ∀ r ∈ Icc (0 : ℝ) P, (![r, 0] : Coord) ∈ W) :
    ContinuousOn (scalarFlowLinearCoefficient f) (Icc (0 : ℝ) P) := by
  have hc : Continuous (fun r : ℝ => (![r, 0] : Coord)) := by fun_prop
  exact (partial_contDiffOn hf hW 1).continuousOn.comp hc.continuousOn hseam

end
end TightVer401
