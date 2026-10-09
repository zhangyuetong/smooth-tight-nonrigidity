import TightVer401.MomentControlBasis
import TightVer401.MomentControlCircleSpan
import TightVer401.MomentPeriodicControl

namespace TightVer401
noncomputable section
open Set Filter MeasureTheory Metric
open scoped ContDiff Topology Manifold

def circleControlMoment {m : ℕ} (L : ℝ) (f : AddCircle L → EuclideanSpace ℝ (Fin m))
    (ψ : AddCircle L → ℝ) : EuclideanSpace ℝ (Fin m) :=
  ∫ s in 0..L, ψ (periodProjection L s) • f (periodProjection L s)

theorem exists_short_circle_moment_controls {m : ℕ} (L : ℝ) [Fact (0 < L)]
    (f : AddCircle L → EuclideanSpace ℝ (Fin m)) (hf : Continuous f)
    (hg : ContDiff ℝ ∞ (f ∘ periodProjection L)) {a ε : ℝ}
    (ha : a ∈ Ioo 0 L) (hε : 0 < ε) :
    letI := periodCircleChartedSpace L
    ∃ (r : ℝ) (Ψ : Fin (Module.finrank ℝ (circleMomentSpan L f)) → AddCircle L → ℝ)
        (χ : AddCircle L → ℝ),
      0 < r ∧ r < ε ∧ 0 < a - r ∧ a + r < L ∧
      (∀ j, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (Ψ j)) ∧
      (∀ j q, 0 ≤ Ψ j q) ∧ (∀ j, (∫ s in 0..L, Ψ j (periodProjection L s)) = 1) ∧
      (∀ j, ∃ c : ℝ, tsupport (Ψ j) ⊆ periodProjection L '' Icc (c - r) (c + r)) ∧
      Pairwise (fun i j => Disjoint (tsupport (Ψ i)) (tsupport (Ψ j))) ∧
      ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ χ ∧
      (∀ q, χ q ∈ Icc 0 1) ∧
      tsupport χ ⊆ periodProjection L '' closedBall a r ∧
      (∀ s ∈ Icc (a - r / 2) (a + r / 2), χ (periodProjection L s) = 1) ∧
      (∀ j, Disjoint (tsupport (Ψ j)) (periodProjection L '' closedBall a r)) ∧
      (∀ j, Disjoint (tsupport (Ψ j)) (tsupport χ)) ∧
      LinearIndependent ℝ (fun j => circleControlMoment L f (Ψ j)) ∧
      Submodule.span ℝ (Set.range (fun j => circleControlMoment L f (Ψ j))) =
        circleMomentSpan L f := by
  letI := periodCircleChartedSpace L
  rw [circleMomentSpan_eq_representative L hf]
  let g := f ∘ periodProjection L
  obtain ⟨r, ψ, hr, hrε, har, haL, hψsmooth, hψnonneg, hψmass, hψinside,
    hψshape, hψpair, hψavoid, hψLI, hψspan⟩ :=
      exists_short_independent_interval_controls (f := g) hg.continuous ha hε
  let b := momentControlBump a r hr
  have hbr : b.rOut = r := rfl
  let χ := momentPeriodicCircleControl L b
  let Ψ := fun j => momentPeriodicCircleControl L (ψ j)
  have hψcompact (j) : HasCompactSupport (ψ j) := by
    obtain ⟨c, hc⟩ := hψshape j
    change IsCompact (tsupport (ψ j))
    rw [hc]
    exact isCompact_Icc
  have hbcompact : HasCompactSupport (b : ℝ → ℝ) := b.hasCompactSupport
  have hbinside : tsupport (b : ℝ → ℝ) ⊆ Ioo 0 L := by
    rw [b.tsupport_eq, Real.closedBall_eq_Icc]
    change Icc (a - r) (a + r) ⊆ Ioo 0 L
    intro s hs
    exact ⟨har.trans_le hs.1, hs.2.trans_lt haL⟩
  have hMoment (j) : circleControlMoment L f (Ψ j) = ∫ s in 0..L, ψ j s • g s :=
    momentPeriodicRepresentative_intervalMoment L (hψinside j) g
  have hχsmooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ χ :=
    momentPeriodicCircleControl_contMDiff L b.contDiff hbcompact hbinside
  have hχrange (q) : χ q ∈ Icc 0 1 := by
    change b ((AddCircle.equivIco L 0 q : Ico 0 (0 + L)) : ℝ) ∈ Icc 0 1
    exact ⟨b.nonneg, b.le_one⟩
  have hχsupport : tsupport χ ⊆ periodProjection L '' closedBall a r := by
    simpa only [χ, b.tsupport_eq, hbr] using momentPeriodicCircleControl_tsupport L hbcompact
  have hχplateau (s) (hs : s ∈ Icc (a - r / 2) (a + r / 2)) :
      χ (periodProjection L s) = 1 := by
    have hsI : s ∈ Icc 0 L := by
      constructor <;> linarith [hs.1, hs.2]
    rw [show χ (periodProjection L s) = momentPeriodicRepresentative L b s from rfl,
      momentPeriodicRepresentative_eqOn L hbinside hsI]
    apply b.one_of_mem_closedBall
    rw [Real.closedBall_eq_Icc]
    exact hs
  have hψχ (j) : Disjoint (tsupport (Ψ j)) (tsupport χ) := by
    apply momentPeriodicCircleControl_disjoint L (hψcompact j) hbcompact (hψinside j) hbinside
    simpa only [b.tsupport_eq, hbr] using hψavoid j
  have hψArc (j) : Disjoint (tsupport (Ψ j)) (periodProjection L '' closedBall a r) := by
    apply Set.disjoint_left.mpr
    intro q hq hqArc
    obtain ⟨s, hs, hsq⟩ := momentPeriodicCircleControl_tsupport L (hψcompact j) hq
    obtain ⟨t, ht, htq⟩ := hqArc
    have hsI : s ∈ Ico 0 (0 + L) := by
      exact ⟨(hψinside j hs).1.le, by simpa only [zero_add] using (hψinside j hs).2⟩
    have htI : t ∈ Ico 0 (0 + L) := by
      have htInside := hbinside (show t ∈ tsupport (b : ℝ → ℝ) by
        simpa only [b.tsupport_eq, hbr] using ht)
      exact ⟨htInside.1.le, by simpa only [zero_add] using htInside.2⟩
    have hst : s = t := (AddCircle.coe_eq_coe_iff_of_mem_Ico hsI htI).mp (hsq.trans htq.symm)
    subst t
    exact Set.disjoint_left.mp (hψavoid j) hs ht
  refine ⟨r, Ψ, χ, hr, hrε, har, haL,
    (fun j => momentPeriodicCircleControl_contMDiff L (hψsmooth j) (hψcompact j) (hψinside j)),
    (fun j q => momentPeriodicCircleControl_nonneg L (hψnonneg j) q),
    (fun j => momentPeriodicRepresentative_normalized L (hψinside j) (hψmass j)),
    ?_, ?_, hχsmooth, hχrange, hχsupport, hχplateau, hψArc, hψχ, ?_, ?_⟩
  · intro j
    obtain ⟨c, hc⟩ := hψshape j
    exact ⟨c, momentPeriodicCircleControl_arc L (hψcompact j) (hc ▸ subset_rfl)⟩
  · intro i j hij
    exact momentPeriodicCircleControl_disjoint L (hψcompact i) (hψcompact j)
      (hψinside i) (hψinside j) (hψpair hij)
  · simpa only [hMoment] using hψLI
  · simpa only [hMoment] using hψspan

end
end TightVer401
