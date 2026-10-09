import TightVer401.PositiveExitConstructionPullback
import TightVer401.PositiveExitConstructionLeaf
import TightVer401.PositiveExitConstructionFirstIntegral
import TightVer401.IdentityBandCentralSupportPhysical
import TightVer401.NormalLoopOrientation

/-! Actual asymptotic and outward mixed coefficients on a selected complete
identity-flow leaf. The height is the pullback of the SAME Cartesian potential.
The handedness of the actual corrected frame is stated as an ordinary cross
identity: orthonormality alone does not fix the Fermi transverse sign. -/
open scoped Manifold
namespace TightVer401
noncomputable section
open Set Filter MeasureTheory OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff Topology Matrix RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

/-- The actual corrected normal-loop frame has the handedness needed by the
outward Fermi convention; this is not part of `PeriodicRuledFrame` itself. -/
theorem positiveExit_corrected_frame_orientation {T : ℝ} (d : PeriodicRuledFrame T)
    {ξ : ℝ → Ambient} {ψ : ℝ → ℝ} (hξ : ContDiff ℝ ∞ ξ)
    (hunit : ∀ r, inner ℝ (ξ r) (ξ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ξ r) (deriv ξ r) = 1)
    (hT : d.T = normalLoopTangent ξ ∘ ψ)
    (hE : d.E = deriv ξ ∘ ψ) (hn : d.n = ξ ∘ ψ) :
    ∀ s, ambientCross (d.T s) (d.E s) = d.n s := by
  intro s
  rw [hT, hE, hn]
  exact (normalLoop_orientation
    (fun r => (hξ.differentiable (by simp) r).hasDerivAt) hunit hspeed (ψ s)).1

theorem positiveExit_corrected_frame_torsion_negative {T : ℝ} (d : PeriodicRuledFrame T)
    {a ψ : ℝ → ℝ} (ha : ∀ r, 0 < a r)
    (hτ : d.τ = normalLoopPhysicalTau a ψ) : ∀ s, d.τ s < 0 := by
  intro s
  rw [hτ]
  exact neg_neg_of_pos (inv_pos.mpr (ha (ψ s)))

private theorem positiveExit_cross_self (x : Ambient) : ambientCross x x = 0 := by
  ext i
  fin_cases i <;> simp [ambientCross, cross_apply]

private theorem positiveExit_cross_pairing (x n y : Ambient) :
    inner ℝ x (-ambientCross n y) = -inner ℝ y (ambientCross x n) := by
  norm_num [inner_neg_right, ambient_inner_dot, dotProduct, Fin.sum_univ_succ,
    ambientCross, cross_apply]
  simp only [show (Fin.succ (0 : Fin 2)) = (1 : Fin 3) from rfl,
    show (Fin.succ (Fin.succ (0 : Fin 1))) = (2 : Fin 3) from rfl]
  <;> ring

/-- Exact outward pairing for the actual nonruling null tangent. It is
derived from the actual ruled derivatives and their retained second form. -/
theorem positiveExitRawNullDirection_outward_pairing {T : ℝ}
    (d : PeriodicRuledFrame T) (q : Coord)
    (horient : ambientCross (d.T (q 0)) (d.E (q 0)) = d.n (q 0)) :
    inner ℝ (fderiv ℝ (ruledMap d.γ d.E) q (positiveExitRawNullDirection d q))
      (-ambientCross (d.rawGaussMap q)
        (fderiv ℝ d.rawGaussMap q (positiveExitRawNullDirection d q))) =
      -d.τ (q 0) * (1 + (positiveExitRawNullDirection d q 1)^2 /
        ruledEnergy (d.k (q 0)) (d.τ (q 0)) (q 1)) := by
  let R := Real.sqrt (ruledEnergy (d.k (q 0)) (d.τ (q 0)) (q 1))
  let A := (1 - d.k (q 0) * q 1) • d.T (q 0) +
    (d.τ (q 0) * q 1) • d.n (q 0)
  let f := positiveExitRawNullDirection d q 1
  have hR : R ≠ 0 := (Real.sqrt_pos.mpr (ruledEnergy_pos (d.torsion_ne_zero (q 0)))).ne'
  have hRsq : R^2 = ruledEnergy (d.k (q 0)) (d.τ (q 0)) (q 1) :=
    Real.sq_sqrt (ruledEnergy_pos (d.torsion_ne_zero (q 0))).le
  rcases d.orthonormal (q 0) with ⟨hTT, hEE, hnn, hTE, hTn, hEn⟩
  have hET : inner ℝ (d.E (q 0)) (d.T (q 0)) = 0 := by rw [real_inner_comm, hTE]
  have hTnCross : ambientCross (d.T (q 0)) (d.n (q 0)) = -d.E (q 0) := by
    rw [← horient, normalLoopCross_double, hTE, hTT]
    simp
  have hnTCross : ambientCross (d.n (q 0)) (d.T (q 0)) = d.E (q 0) := by
    rw [normalLoopCross_swap, hTnCross, neg_neg]
  have hEnCross : ambientCross (d.E (q 0)) (d.n (q 0)) = d.T (q 0) := by
    rw [← horient, normalLoopCross_double, hEE, hTE]
    simp
  have hETCross : ambientCross (d.E (q 0)) (d.T (q 0)) = -d.n (q 0) := by
    rw [normalLoopCross_swap, horient]
  have hX : fderiv ℝ (ruledMap d.γ d.E) q (positiveExitRawNullDirection d q) =
      A + f • d.E (q 0) := by
    rw [fderiv_two_coordinates, ruled_partial_s (d.deriv_γ _) (d.deriv_E _),
      ruled_partial_u (d.deriv_γ _) (d.deriv_E _)]
    simp [A, f, positiveExitRawNullDirection]
  have hcross : ambientCross
      (fderiv ℝ (ruledMap d.γ d.E) q (positiveExitRawNullDirection d q)) (d.rawGaussMap q) =
      (-R) • d.E (q 0) + (f / R) • A := by
    rw [hX]
    simp only [PeriodicRuledFrame.rawGaussMap, ruledNormal, A, R,
      ambientCross_add_left, normalLoopCross_add_right, ambientCross_smul_left,
      normalLoopCross_smul_right, hTnCross, hnTCross, hEnCross, hETCross,
      positiveExit_cross_self, smul_zero, zero_add, add_zero]
    ext i
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
    dsimp only [R, A] at hR hRsq ⊢
    simp only [ruledEnergy, mul_comm] at hR hRsq ⊢
    field_simp [hR]
    linear_combination (d.E (q 0) i) * hRsq
  have hBE : inner ℝ (fderiv ℝ d.rawGaussMap q (positiveExitRawNullDirection d q))
      (d.E (q 0)) = -d.τ (q 0) / R := by
    have he := identityBand_interior_differential_pairing d q
      (Pi.single 1 1 : Coord) (positiveExitRawNullDirection d q)
    rw [show fderiv ℝ (ruledMap d.γ d.E) q (Pi.single 1 1 : Coord) = d.E (q 0) from
      ruled_partial_u (d.deriv_γ _) (d.deriv_E _), real_inner_comm] at he
    simpa [positiveExitRawNullDirection, R] using he
  have hBA : inner ℝ (fderiv ℝ d.rawGaussMap q (positiveExitRawNullDirection d q)) A =
      d.τ (q 0) * f / R := by
    have he := identityBand_interior_differential_pairing d q
      (Pi.single 0 1 : Coord) (positiveExitRawNullDirection d q)
    rw [show fderiv ℝ (ruledMap d.γ d.E) q (Pi.single 0 1 : Coord) = A from
      ruled_partial_s (d.deriv_γ _) (d.deriv_E _), real_inner_comm] at he
    rw [he]
    simp only [Pi.single_eq_same, Pi.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0),
      positiveExitRawNullDirection, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, mul_zero, zero_mul, add_zero, zero_add, mul_one, one_mul]
    dsimp [R, f, positiveExitRawNullDirection]
    ring
  rw [positiveExit_cross_pairing, hcross, inner_add_right, real_inner_smul_right,
    real_inner_smul_right, hBE, hBA]
  change -((-R) * (-d.τ (q 0) / R) + (f / R) * (d.τ (q 0) * f / R)) = _
  rw [← hRsq]
  field_simp [hR]
  ring

theorem positiveExitRawNullDirection_outward_positive {T : ℝ}
    (d : PeriodicRuledFrame T) (q : Coord)
    (horient : ambientCross (d.T (q 0)) (d.E (q 0)) = d.n (q 0))
    (hτ : d.τ (q 0) < 0) :
    0 < inner ℝ (fderiv ℝ (ruledMap d.γ d.E) q (positiveExitRawNullDirection d q))
      (-ambientCross (d.rawGaussMap q)
        (fderiv ℝ d.rawGaussMap q (positiveExitRawNullDirection d q))) := by
  rw [positiveExitRawNullDirection_outward_pairing d q horient]
  exact mul_pos (neg_pos.mpr hτ) (by
    have he : 0 ≤ (positiveExitRawNullDirection d q 1)^2 /
        ruledEnergy (d.k (q 0)) (d.τ (q 0)) (q 1) :=
      div_nonneg (sq_nonneg (positiveExitRawNullDirection d q 1))
        (ruledEnergy_pos (k := d.k (q 0)) (u := q 1) (d.torsion_ne_zero (q 0))).le
    linarith)

def positiveExitLeafRawCoordinates {T : ℝ} (d : PeriodicRuledFrame T) (v t : ℝ) : Coord :=
  ![t, principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 v t]

theorem positiveExitLeafRawCoordinates_hasDerivAt {T δ w : ℝ}
    (d : PeriodicRuledFrame T)
    (hinside : ∀ v ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 v t ∈ Ioo 0 w)
    {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) δ) (t : ℝ) :
    HasDerivAt (positiveExitLeafRawCoordinates d v)
      (positiveExitRawNullDirection d (positiveExitLeafRawCoordinates d v t)) t := by
  exact ruled_graph_hasDerivAt (principalTrajectory_hasDerivAt
    (ruledRho_hasDerivAt (d.smooth_τ.differentiable (by simp) t).hasDerivAt
      (d.torsion_ne_zero t))
    (ruledOmega_hasDerivAt d.smooth_k d.smooth_τ d.torsion_ne_zero t)
    (ruledRho_pos (d.torsion_ne_zero t)).ne'
    (positiveExit_trajectory_denominator_ne_zero d hinside hv t))

theorem positiveExitRawLeaf_eq_raw {T δ w : ℝ} (d : PeriodicRuledFrame T)
    (hb : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0)
    (hinside : ∀ u ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 u t ∈ Ioo 0 w)
    (v : Ioo (0 : ℝ) δ) :
    positiveExitRawLeaf d hb hinside v = d.rawGaussMap ∘ positiveExitLeafRawCoordinates d v := by
  rfl

/-- Actual coefficient identification along a reconstructed Cartesian seam.
Only the ordinary surface trace and its actual derivative appear as inputs. -/
theorem positiveExitFermi_seam_entries {ζ X : ℝ → Ambient} {G : Coord → ℝ}
    {U V : Set Coord} (hζ : ContDiff ℝ ∞ ζ)
    (hunit : ∀ s, inner ℝ (ζ s) (ζ s) = 1)
    (hspeed : ∀ s, inner ℝ (deriv ζ s) (deriv ζ s) = 1)
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U) (hV : IsOpen V)
    (hnorth : ∀ q ∈ V, 0 < fermiNormalMap ζ q 2)
    (hscale : ∀ q ∈ V, fermiNormalScale (normalLoopCurvature ζ) q ≠ 0)
    (hmap : MapsTo (positiveExitFermiSource ζ) V U)
    (hseam : ∀ s, (![s, 0] : Coord) ∈ V)
    (htrace : ∀ s, planarSupportMap G (positiveExitFermiSource ζ (![s, 0] : Coord)) = X s)
    (s : ℝ) :
    fermiSupportL (normalLoopCurvature ζ) (positiveExitFermiHeight G ζ) ![s, 0] =
        inner ℝ (deriv X s) (deriv ζ s) ∧
      fermiSupportM (normalLoopCurvature ζ) (positiveExitFermiHeight G ζ) ![s, 0] =
        inner ℝ (deriv X s) (normalLoopTangent ζ s) := by
  let P := positiveExitFermiSource ζ
  let F := planarSupportMap G ∘ P
  have hP := positiveExitFermiSource_contDiffOn hζ hnorth
  have hF : ContDiffOn ℝ ∞ F V := (planarSupportMap_contDiffOn hG hU).comp hP hmap
  have hs : HasDerivAt (fun r : ℝ => (![r, 0] : Coord)) (Pi.single 0 1 : Coord) s := by
    let L : ℝ →L[ℝ] Coord := ContinuousLinearMap.toSpanSingleton ℝ (Pi.single 0 1 : Coord)
    have heL : (fun r : ℝ => (![r, 0] : Coord)) = L := by
      ext r i
      fin_cases i <;> simp [L]
    rw [heL]
    have hdL : HasFDerivAt L L s := L.hasFDerivAt
    simpa only [L, ContinuousLinearMap.toSpanSingleton_apply, one_smul] using hdL.hasDerivAt
  have hd := ((hF _ (hseam s)).contDiffAt (hV.mem_nhds (hseam s))).differentiableAt (by simp)
  have ht := hd.hasFDerivAt.comp_hasDerivAt s hs
  have he : F ∘ (fun r : ℝ => (![r, 0] : Coord)) = X := funext htrace
  rw [he] at ht
  have hpartial : coordPartial 0 F (![s, 0] : Coord) = deriv X s := ht.deriv.symm
  have hnEq := positiveExitFermi_normal_eq hζ hunit hspeed hnorth
  have hpair (j : Fin 2) :
      sphereSupportTensor (inducedMetric (fermiNormalMap ζ)) (positiveExitFermiHeight G ζ)
        (![s, 0] : Coord) 0 j =
      inner ℝ (coordPartial 0 F (![s, 0] : Coord))
        (coordPartial j (fermiNormalMap ζ) (![s, 0] : Coord)) := by
    rw [positiveExitFermi_tensor_entry hζ hunit hspeed hG hU hV hnorth hscale hmap (hseam s)]
    exact (identityBand_cartesian_pullback_pairing hG hU hV hP hmap (fun _ _ => rfl)
      hnEq (hseam s) (Pi.single 0 1 : Coord) (Pi.single j 1 : Coord)).symm
  have hκ := (normalLoop_actual_smooth hζ).2
  have hentries := fermiSupport_actual_entries hκ (positiveExitFermiHeight G ζ) (hscale _ (hseam s))
  rw [← fermiNormalMap_inducedMetric hζ hunit hspeed] at hentries
  have hpartials := fermiNormalMap_partials hζ hunit hspeed (![s, 0] : Coord)
  constructor
  · rw [← hentries.1, hpair 0, hpartial, hpartials.1]
    simp [fermiNormalScale]
  · rw [← hentries.2.1, hpair 1, hpartial, hpartials.2]
    simp [fermiNormalTransverse]

/-- The same complete closed flow leaf, reparametrized by its constructed
arclength, has actual L=0 and actual outward M>0 for the SAME G. -/
theorem positiveExitFermi_closed_leaf_seam {T δ w : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T)
    (hb : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0)
    (hinside : ∀ u ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 u t ∈ Ioo 0 w)
    (v : Ioo (0 : ℝ) δ) (S : ℝ ≃ₜ ℝ)
    (hS : (S : ℝ → ℝ) = rawPrimitive (positiveExitLeafSpeed d hb hinside v))
    (horient : ∀ t, ambientCross (d.T t) (d.E t) = d.n t)
    (hτ : ∀ t, d.τ t < 0)
    {G : Coord → ℝ} {U V : Set Coord}
    (hζ : ContDiff ℝ ∞ (positiveExitRawLeaf d hb hinside v ∘ S.symm))
    (hunit : ∀ s, inner ℝ ((positiveExitRawLeaf d hb hinside v ∘ S.symm) s)
      ((positiveExitRawLeaf d hb hinside v ∘ S.symm) s) = 1)
    (hspeed : ∀ s, inner ℝ (deriv (positiveExitRawLeaf d hb hinside v ∘ S.symm) s)
      (deriv (positiveExitRawLeaf d hb hinside v ∘ S.symm) s) = 1)
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U) (hV : IsOpen V)
    (hnorth : ∀ q ∈ V, 0 < fermiNormalMap (positiveExitRawLeaf d hb hinside v ∘ S.symm) q 2)
    (hscale : ∀ q ∈ V, fermiNormalScale
      (normalLoopCurvature (positiveExitRawLeaf d hb hinside v ∘ S.symm)) q ≠ 0)
    (hmap : MapsTo (positiveExitFermiSource (positiveExitRawLeaf d hb hinside v ∘ S.symm)) V U)
    (hseam : ∀ s, (![s, 0] : Coord) ∈ V)
    (hrec : ∀ t, planarSupportMap G (gnomonicInverse (d.rawGaussMap
      (positiveExitLeafRawCoordinates d v t))) =
      ruledMap d.γ d.E (positiveExitLeafRawCoordinates d v t)) :
    ∀ s, fermiSupportL (normalLoopCurvature (positiveExitRawLeaf d hb hinside v ∘ S.symm))
        (positiveExitFermiHeight G (positiveExitRawLeaf d hb hinside v ∘ S.symm)) ![s, 0] = 0 ∧
      0 < fermiSupportM (normalLoopCurvature (positiveExitRawLeaf d hb hinside v ∘ S.symm))
        (positiveExitFermiHeight G (positiveExitRawLeaf d hb hinside v ∘ S.symm)) ![s, 0] := by
  let ζ := positiveExitRawLeaf d hb hinside v ∘ S.symm
  let X := ruledMap d.γ d.E ∘ positiveExitLeafRawCoordinates d v ∘ S.symm
  have htrace (s : ℝ) : planarSupportMap G (positiveExitFermiSource ζ (![s, 0] : Coord)) = X s := by
    simpa [ζ, X, positiveExitFermiSource, fermiNormalMap, positiveExitRawLeaf_eq_raw,
      Function.comp_apply] using hrec (S.symm s)
  have hXsmooth : ContDiff ℝ ∞ (ruledMap d.γ d.E) :=
    (d.smooth_γ.comp (contDiff_apply ℝ ℝ 0)).add
      ((contDiff_apply ℝ ℝ 1).smul (d.smooth_E.comp (contDiff_apply ℝ ℝ 0)))
  intro s
  let q := positiveExitLeafRawCoordinates d v (S.symm s)
  let a := (positiveExitLeafSpeed d hb hinside v (S.symm s))⁻¹
  let n := positiveExitRawNullDirection d q
  have ha : 0 < a := inv_pos.mpr (positiveExitLeafSpeed_pos d hb hinside v _)
  have hψ := identityBand_arclengthInverse_hasDerivAt
    (positiveExitLeafSpeed_contDiff d hb hinside v).continuous
    (positiveExitLeafSpeed_pos d hb hinside v) S hS s
  have hq := (positiveExitLeafRawCoordinates_hasDerivAt d hinside v.property (S.symm s)).scomp s hψ
  have hdX : deriv X s = a • fderiv ℝ (ruledMap d.γ d.E) q n := by
    have hx := (hXsmooth.differentiable (by simp) q).hasFDerivAt.comp_hasDerivAt s hq
    simpa [X, q, a, n] using hx.deriv
  have hdζ : deriv ζ s = a • fderiv ℝ d.rawGaussMap q n := by
    have hz := ((periodicRuledFrame_rawGaussMap_contDiff d).differentiable (by simp) q).hasFDerivAt.comp_hasDerivAt s hq
    simpa [ζ, positiveExitRawLeaf_eq_raw, q, a, n, Function.comp_assoc] using hz.deriv
  have hζq : ζ s = d.rawGaussMap q := by
    simp [ζ, q, positiveExitRawLeaf_eq_raw]
  have he := positiveExitFermi_seam_entries hζ hunit hspeed hG hU hV hnorth hscale hmap
    hseam htrace s
  constructor
  · rw [he.1, hdX, hdζ, real_inner_smul_left, real_inner_smul_right,
      positiveExitRawNullDirection_actual_pairing]
    simp
  · rw [he.2, hdX]
    have hP : normalLoopTangent ζ s =
        a • (-ambientCross (d.rawGaussMap q) (fderiv ℝ d.rawGaussMap q n)) := by
      rw [normalLoopTangent, normalLoopP, hζq, hdζ, normalLoopCross_smul_right]
      module
    rw [hP, real_inner_smul_left, real_inner_smul_right]
    exact mul_pos ha (mul_pos ha (positiveExitRawNullDirection_outward_positive d q
      (horient (q 0)) (hτ (q 0))))

end
end TightVer401
