import TightVer401.VisibleConnectorLocalPotential
import TightVer401.RegularLocalInverse

/-! Actual local parametric inversion for the displaced incoming seam.
The original p is the target of the inverse. No global collar, exterior
ordering, or full scalar germ is inferred from the first derivatives. -/
namespace TightVer401
noncomputable section
open Set Function Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- The actual jointly parameterized displaced ruling. -/
def visibleConnectorDisplacedPhi (p w0 : ℝ → Coord) (w : ℝ × ℝ → Coord)
    (rho : ℝ) (q : Coord) : Coord :=
  p (q 0) + rho • w0 (q 0) + q 1 • w (rho, q 0)

def visibleConnectorDisplacedPsi (p w0 : ℝ → Coord) (w : ℝ × ℝ → Coord)
    (z : ℝ × Coord) : ℝ × Coord :=
  (z.1, visibleConnectorDisplacedPhi p w0 w z.1 z.2)

/-- The actual inverse solution for the ORIGINAL point p(s). -/
def visibleConnectorDisplacedSolution (e : OpenPartialHomeomorph (ℝ × Coord) (ℝ × Coord))
    (p : ℝ → Coord) (z : ℝ × ℝ) : Coord := (e.symm (z.1, p z.2)).2

def visibleConnectorDisplacedSolutionDomain
    (e : OpenPartialHomeomorph (ℝ × Coord) (ℝ × Coord)) (p : ℝ → Coord) : Set (ℝ × ℝ) :=
  (fun z : ℝ × ℝ => (z.1, p z.2)) ⁻¹' e.target

theorem visibleConnectorDisplacedPsi_contDiff {p w0 : ℝ → Coord} {w : ℝ × ℝ → Coord}
    (hp : ContDiff ℝ ∞ p) (hw0 : ContDiff ℝ ∞ w0) (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (visibleConnectorDisplacedPsi p w0 w) := by
  have hs : ContDiff ℝ ∞ (fun z : ℝ × Coord => z.2 0) :=
    (contDiff_apply ℝ ℝ 0).comp contDiff_snd
  have hu : ContDiff ℝ ∞ (fun z : ℝ × Coord => z.2 1) :=
    (contDiff_apply ℝ ℝ 1).comp contDiff_snd
  exact contDiff_fst.prodMk (((hp.comp hs).add
    (contDiff_fst.smul (hw0.comp hs))).add (hu.smul (hw.comp (contDiff_fst.prodMk hs))))

/-- Actual joint smoothness uses only the prescribed ruling domain. -/
theorem visibleConnectorDisplacedPsi_contDiffOn {p w0 : ℝ → Coord} {w : ℝ × ℝ → Coord}
    {Omega : Set (ℝ × ℝ)} (hp : ContDiff ℝ ∞ p) (hw0 : ContDiff ℝ ∞ w0)
    (hw : ContDiffOn ℝ ∞ w Omega) :
    ContDiffOn ℝ ∞ (visibleConnectorDisplacedPsi p w0 w)
      ((fun z : ℝ × Coord => (z.1, z.2 0)) ⁻¹' Omega) := by
  have hs : ContDiff ℝ ∞ (fun z : ℝ × Coord => z.2 0) :=
    (contDiff_apply ℝ ℝ 0).comp contDiff_snd
  have hu : ContDiff ℝ ∞ (fun z : ℝ × Coord => z.2 1) :=
    (contDiff_apply ℝ ℝ 1).comp contDiff_snd
  have hArg : ContDiff ℝ ∞ (fun z : ℝ × Coord => (z.1, z.2 0)) :=
    contDiff_fst.prodMk hs
  have hW := hw.comp hArg.contDiffOn (fun _ hz => hz)
  exact contDiff_fst.contDiffOn.prodMk (((hp.comp hs).contDiffOn.add
    (contDiff_fst.contDiffOn.smul (hw0.comp hs).contDiffOn)).add (hu.contDiffOn.smul hW))

/-- The actual central derivative is the old ruling derivative with its
actual displacement column. The derivative of the new w is multiplied by u=0. -/
theorem visibleConnectorDisplacedPsi_fderiv_central {p w0 : ℝ → Coord}
    {w : ℝ × ℝ → Coord} (hp : ContDiff ℝ ∞ p) (hw0 : ContDiff ℝ ∞ w0)
    (s : ℝ) (hw : ContDiffAt ℝ ∞ w (0, s))
    (hwzero : ∀ r, w (0, r) = w0 r) (v : ℝ × Coord) :
    fderiv ℝ (visibleConnectorDisplacedPsi p w0 w) (0, (![s, 0] : Coord)) v =
      (v.1, fderiv ℝ (visibleConnectorSource p w0) (![s, 0] : Coord) v.2 + v.1 • w0 s) := by
  let z0 : ℝ × Coord := (0, ![s, 0])
  let R : (ℝ × Coord) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ Coord
  let Q : (ℝ × Coord) →L[ℝ] Coord := ContinuousLinearMap.snd ℝ ℝ Coord
  let S : (ℝ × Coord) →L[ℝ] ℝ := (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)).comp Q
  let U : (ℝ × Coord) →L[ℝ] ℝ := (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2)).comp Q
  have hOld := ((visibleConnectorSource_contDiff hp hw0).differentiable (by simp)
    (![s, 0] : Coord)).hasFDerivAt.comp z0 (Q.hasFDerivAt (x := z0))
  have hW0 := ((hw0.differentiable (by simp) s).hasDerivAt.hasFDerivAt).comp z0
    (S.hasFDerivAt (x := z0))
  have hW := (hw.differentiableAt (by simp)).hasFDerivAt.comp z0
    ((R.hasFDerivAt (x := z0)).prodMk (S.hasFDerivAt (x := z0)))
  have hPhi := (hOld.add ((R.hasFDerivAt (x := z0)).smul hW0)).add
    ((U.hasFDerivAt (x := z0)).smul (hW.sub hW0))
  change HasFDerivAt (fun z : ℝ × Coord =>
    visibleConnectorSource p w0 (Q z) + R z • w0 (S z) +
    U z • (w (R z, S z) - w0 (S z))) _ z0 at hPhi
  have heq : (fun z : ℝ × Coord =>
    visibleConnectorSource p w0 (Q z) + R z • w0 (S z) +
    U z • (w (R z, S z) - w0 (S z))) =
    (fun z : ℝ × Coord => visibleConnectorDisplacedPhi p w0 w z.1 z.2) := by
    funext z
    change p (z.2 0) + z.2 1 • w0 (z.2 0) + z.1 • w0 (z.2 0) +
      z.2 1 • (w (z.1, z.2 0) - w0 (z.2 0)) =
      p (z.2 0) + z.1 • w0 (z.2 0) + z.2 1 • w (z.1, z.2 0)
    rw [smul_sub]
    abel
  rw [heq] at hPhi
  have hPsi := (R.hasFDerivAt (x := z0)).prodMk hPhi
  change HasFDerivAt (visibleConnectorDisplacedPsi p w0 w) _ z0 at hPsi
  rw [hPsi.fderiv]
  simp [z0, R, Q, S, U, hwzero, add_assoc, add_left_comm, add_comm]

set_option backward.isDefEq.respectTransparency true in
/-- Construct an actual smooth local parametric inverse. Its joint original-
point solution is smooth on the actual target preimage, solves the literal
ruling equation, and has displacement derivatives a_rho=0 and b_rho=-1. -/
theorem visibleConnectorDisplaced_exists_local_inverse {p w0 : ℝ → Coord}
    {w : ℝ × ℝ → Coord} {Omega : Set (ℝ × ℝ)}
    (hp : ContDiff ℝ ∞ p) (hw0 : ContDiff ℝ ∞ w0)
    (hOmega : IsOpen Omega) (hw : ContDiffOn ℝ ∞ w Omega)
    (hwzero : ∀ r, w (0, r) = w0 r)
    (s : ℝ) (hsOmega : (0, s) ∈ Omega)
    (hdet : visibleConnectorDet (deriv p s) (w0 s) ≠ 0) :
    ∃ e : OpenPartialHomeomorph (ℝ × Coord) (ℝ × Coord),
      (0, (![s, 0] : Coord)) ∈ e.source ∧
      (e : (ℝ × Coord) → ℝ × Coord) = visibleConnectorDisplacedPsi p w0 w ∧
      e.source ⊆ (fun z : ℝ × Coord => (z.1, z.2 0)) ⁻¹' Omega ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧
      IsOpen (visibleConnectorDisplacedSolutionDomain e p) ∧
      (0, s) ∈ visibleConnectorDisplacedSolutionDomain e p ∧
      ContDiffOn ℝ ∞ (visibleConnectorDisplacedSolution e p)
        (visibleConnectorDisplacedSolutionDomain e p) ∧
      (∀ z ∈ visibleConnectorDisplacedSolutionDomain e p,
        visibleConnectorDisplacedPhi p w0 w z.1 (visibleConnectorDisplacedSolution e p z) = p z.2) ∧
      visibleConnectorDisplacedSolution e p (0, s) = (![s, 0] : Coord) ∧
      HasDerivAt (fun rho => visibleConnectorDisplacedSolution e p (rho, s))
        (![0, -1] : Coord) 0 ∧
      HasDerivAt (fun rho => visibleConnectorDisplacedSolution e p (rho, s) 0) 0 0 ∧
      HasDerivAt (fun rho => visibleConnectorDisplacedSolution e p (rho, s) 1) (-1) 0 := by
  let z0 : ℝ × Coord := (0, ![s, 0])
  let t0 : ℝ × Coord := (0, p s)
  let f := visibleConnectorDisplacedPsi p w0 w
  let Z : Set (ℝ × Coord) := (fun z : ℝ × Coord => (z.1, z.2 0)) ⁻¹' Omega
  have hArg : Continuous (fun z : ℝ × Coord => (z.1, z.2 0)) :=
    continuous_fst.prodMk ((continuous_apply 0).comp continuous_snd)
  have hZ : IsOpen Z := hOmega.preimage hArg
  have hzZ : z0 ∈ Z := by
    change (0, s) ∈ Omega
    exact hsOmega
  have hf : ContDiffOn ℝ ∞ f Z := visibleConnectorDisplacedPsi_contDiffOn hp hw0 hw
  have hfAt : ContDiffAt ℝ ∞ f z0 := (hf z0 hzZ).contDiffAt (hZ.mem_nhds hzZ)
  have hwAt : ContDiffAt ℝ ∞ w (0, s) := (hw _ hsOmega).contDiffAt (hOmega.mem_nhds hsOmega)
  have hf0 : f z0 = t0 := by simp [f, z0, t0, visibleConnectorDisplacedPsi, visibleConnectorDisplacedPhi]
  have hDelta : visibleConnectorDelta p p w0 (![s, 0] : Coord) ≠ 0 := by
    simpa [visibleConnectorDelta, visibleConnectorA] using neg_ne_zero.mpr hdet
  let A : Coord ≃L[ℝ] Coord := regularCoordinateEquiv (visibleConnectorSource p w0)
    (![s, 0] : Coord) (visibleConnectorSource_fderiv_injective hp hw0 _ hDelta)
  let E : (ℝ × Coord) ≃L[ℝ] (ℝ × Coord) :=
    (ContinuousLinearEquiv.refl ℝ ℝ).skewProd A
      (ContinuousLinearMap.toSpanSingleton ℝ (w0 s))
  have hA (v : Coord) : A v = fderiv ℝ (visibleConnectorSource p w0) (![s, 0] : Coord) v := rfl
  have hDf : fderiv ℝ f z0 = (E : (ℝ × Coord) →L[ℝ] ℝ × Coord) := by
    apply ContinuousLinearMap.ext
    intro v
    change fderiv ℝ (visibleConnectorDisplacedPsi p w0 w)
      (0, (![s, 0] : Coord)) v = E v
    rw [visibleConnectorDisplacedPsi_fderiv_central hp hw0 s hwAt hwzero]
    simp only [E, ContinuousLinearEquiv.skewProd_apply, ContinuousLinearEquiv.refl_apply,
      ContinuousLinearMap.toSpanSingleton_apply, hA]
  have hFD : HasFDerivAt f (E : (ℝ × Coord) →L[ℝ] ℝ × Coord) z0 := by
    rw [← hDf]
    exact (hfAt.differentiableAt (by simp)).hasFDerivAt
  let W : Set (ℝ × Coord) := Z ∩ (fderiv ℝ f) ⁻¹'
    range ((↑) : ((ℝ × Coord) ≃L[ℝ] (ℝ × Coord)) → ((ℝ × Coord) →L[ℝ] ℝ × Coord))
  have hW : IsOpen W := (hf.continuousOn_fderiv_of_isOpen hZ (by simp)).isOpen_inter_preimage
    hZ ContinuousLinearEquiv.isOpen
  have hzW : z0 ∈ W := ⟨hzZ, E, hDf.symm⟩
  let e0 := hfAt.toOpenPartialHomeomorph f hFD (by simp)
  let e := e0.restrOpen W hW
  have hef : (e : (ℝ × Coord) → ℝ × Coord) = f := rfl
  have hez : z0 ∈ e.source := ⟨hfAt.mem_toOpenPartialHomeomorph_source hFD (by simp), hzW⟩
  have heZ : e.source ⊆ Z := fun _ hx => hx.2.1
  have het : t0 ∈ e.target := hf0 ▸ (show f z0 ∈ e.target from by rw [← hef]; exact e.map_source hez)
  have heinv : e.symm t0 = z0 := by
    rw [← hf0, ← hef]
    exact e.left_inv hez
  have hei : ContDiffOn ℝ ∞ e.symm e.target := by
    intro y hy
    have hxW : e.symm y ∈ W := (e.map_target hy).2
    obtain ⟨B, hB⟩ := hxW.2
    have hfx : ContDiffAt ℝ ∞ f (e.symm y) :=
      (hf _ hxW.1).contDiffAt (hZ.mem_nhds hxW.1)
    have hBd : HasFDerivAt e (B : (ℝ × Coord) →L[ℝ] ℝ × Coord) (e.symm y) := by
      rw [hef, hB]
      exact (hfx.differentiableAt (by simp)).hasFDerivAt
    exact (e.contDiffAt_symm hy hBd (by rw [hef]; exact hfx)).contDiffWithinAt
  let j : ℝ × ℝ → ℝ × Coord := fun z => (z.1, p z.2)
  have hj : ContDiff ℝ ∞ j := contDiff_fst.prodMk (hp.comp contDiff_snd)
  have hV : IsOpen (visibleConnectorDisplacedSolutionDomain e p) := e.open_target.preimage hj.continuous
  have hVs : (0, s) ∈ visibleConnectorDisplacedSolutionDomain e p := het
  have hQ : ContDiffOn ℝ ∞ (visibleConnectorDisplacedSolution e p)
      (visibleConnectorDisplacedSolutionDomain e p) :=
    (hei.comp hj.contDiffOn (fun _ hz => hz)).snd
  have hsolve (z : ℝ × ℝ) (hz : z ∈ visibleConnectorDisplacedSolutionDomain e p) :
      visibleConnectorDisplacedPhi p w0 w z.1 (visibleConnectorDisplacedSolution e p z) = p z.2 := by
    have heq := e.right_inv hz
    rw [hef] at heq
    have hrho := congrArg Prod.fst heq
    have hsource := congrArg Prod.snd heq
    change (e.symm (z.1, p z.2)).1 = z.1 at hrho
    change visibleConnectorDisplacedPhi p w0 w (e.symm (z.1, p z.2)).1
      (e.symm (z.1, p z.2)).2 = p z.2 at hsource
    rw [hrho] at hsource
    exact hsource
  have hQ0 : visibleConnectorDisplacedSolution e p (0, s) = (![s, 0] : Coord) :=
    congrArg Prod.snd heinv
  have hAw : A (![0, -1] : Coord) = -w0 s := by
    rw [hA]
    have hv : (![0, -1] : Coord) = (-1 : ℝ) • (Pi.single 1 1 : Coord) := by
      ext i
      fin_cases i <;> simp
    rw [hv, map_smul]
    change (-1 : ℝ) • coordPartial 1 (visibleConnectorSource p w0) (![s, 0] : Coord) = -w0 s
    rw [(visibleConnectorSource_partials hp hw0 (![s, 0] : Coord)).2]
    simp
  have hEneg : E (1, (![0, -1] : Coord)) = ((1 : ℝ), (0 : Coord)) := by
    simp [E, hAw, ContinuousLinearEquiv.skewProd_apply]
  have hEinv : E.symm ((1 : ℝ), (0 : Coord)) = (1, (![0, -1] : Coord)) := by
    apply E.injective
    rw [E.apply_symm_apply, hEneg]
  have hInv : HasFDerivAt e.symm (E.symm : (ℝ × Coord) →L[ℝ] ℝ × Coord) t0 :=
    e.hasFDerivAt_symm het (by rw [heinv, hef]; exact hFD)
  have hpath : HasDerivAt (fun rho : ℝ => (rho, p s)) ((1 : ℝ), (0 : Coord)) 0 :=
    (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 (p s))
  have hfull : HasDerivAt (fun rho : ℝ => e.symm (rho, p s))
      (1, (![0, -1] : Coord)) 0 := by
    have hh := hInv.comp_hasDerivAt 0 hpath
    change HasDerivAt (fun rho : ℝ => e.symm (rho, p s))
      (E.symm ((1 : ℝ), (0 : Coord))) 0 at hh
    rw [hEinv] at hh
    exact hh
  have hQr : HasDerivAt (fun rho => visibleConnectorDisplacedSolution e p (rho, s))
      (![0, -1] : Coord) 0 := hfull.snd
  have ha := (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)).hasFDerivAt.comp_hasDerivAt 0 hQr
  have hb := (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2)).hasFDerivAt.comp_hasDerivAt 0 hQr
  refine ⟨e, hez, hef, heZ, hei, hV, hVs, hQ, hsolve, hQ0, hQr, ?_, ?_⟩
  · simpa only [Function.comp_def, ContinuousLinearMap.proj_apply, Matrix.cons_val_zero] using ha
  · convert hb using 1 <;> rfl

end
end TightVer401