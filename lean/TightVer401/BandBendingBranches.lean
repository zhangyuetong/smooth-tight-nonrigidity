import TightVer401.PeriodicRuledBending

/-! Exact metric branching for the actual native band model. The OpenAI
manifold induced-form API uses Plane charts; these identities use the existing
band differential on its product model and the same ambient inner product. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Manifold Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- The actual pullback metric of a map on the native band. -/
def bandInducedForm {L b : ℝ} [Fact (0 < L)] (φ : AddCircle L × Ioo (0 : ℝ) b → Ambient)
    (p : AddCircle L × Ioo (0 : ℝ) b) (v w : ℝ × ℝ) : ℝ :=
  inner ℝ (bandDifferential φ p v) (bandDifferential φ p w)

theorem bandInducedForm_quadratic {L b : ℝ} [Fact (0 < L)]
    {φ Y : AddCircle L × Ioo (0 : ℝ) b → Ambient}
    (hφ : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Ambient) ∞ φ)
    (hY : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Ambient) ∞ Y)
    (ε : ℝ) (p : AddCircle L × Ioo (0 : ℝ) b) (v w : ℝ × ℝ) :
    bandInducedForm (φ + ε • Y) p v w = bandInducedForm φ p v w +
      ε * (inner ℝ (bandDifferential φ p v) (bandDifferential Y p w) +
        inner ℝ (bandDifferential Y p v) (bandDifferential φ p w)) +
      ε^2 * bandInducedForm Y p v w := by
  have hdφ := (hφ p).mdifferentiableAt (by simp)
  have hdY := (hY p).mdifferentiableAt (by simp)
  unfold bandInducedForm bandDifferential
  rw [mfderiv_add hdφ (hdY.const_smul ε), const_smul_mfderiv hdY ε]
  simp only [add_apply, smul_apply, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right]
  ring

/-- A genuine infinitesimal bending has this exact common metric at every amplitude. -/
theorem bandBending_branch_common_metric {L b : ℝ} [Fact (0 < L)]
    {φ Y : AddCircle L × Ioo (0 : ℝ) b → Ambient}
    (hφ : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Ambient) ∞ φ)
    (hY : IsBandBending φ Y) (ε : ℝ) (p : AddCircle L × Ioo (0 : ℝ) b)
    (v w : ℝ × ℝ) :
    bandInducedForm (φ + ε • Y) p v w =
      bandInducedForm φ p v w + ε^2 * bandInducedForm Y p v w := by
  rw [bandInducedForm_quadratic hφ hY.1, hY.2 p v w]
  ring

/-- Opposite perturbations have exactly the same actual induced metric. -/
theorem bandBending_opposite_branches_metric {L b : ℝ} [Fact (0 < L)]
    {φ Y : AddCircle L × Ioo (0 : ℝ) b → Ambient}
    (hφ : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Ambient) ∞ φ)
    (hY : IsBandBending φ Y) (ε : ℝ) :
    bandInducedForm (φ + ε • Y) = bandInducedForm (φ - ε • Y) := by
  have he : φ - ε • Y = φ + (-ε) • Y := by
    funext p
    change φ p - ε • Y p = φ p + (-ε) • Y p
    rw [neg_smul, sub_eq_add_neg]
  rw [he]
  funext p v w
  rw [bandBending_branch_common_metric hφ hY, bandBending_branch_common_metric hφ hY]
  simp

/-- Both perturbed maps are smooth in the actual band manifold structure. -/
theorem bandBending_branches_contMDiff {L b : ℝ} [Fact (0 < L)]
    {φ Y : AddCircle L × Ioo (0 : ℝ) b → Ambient}
    (hφ : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Ambient) ∞ φ)
    (hY : IsBandBending φ Y) (ε : ℝ) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Ambient) ∞ (φ + ε • Y) ∧
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Ambient) ∞ (φ - ε • Y) :=
  by
    have hc : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun _ : AddCircle L × Ioo (0 : ℝ) b => ε) := contMDiff_const
    have hεY : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Ambient) ∞ (ε • Y) :=
      hc.smul hY.1
    exact ⟨hφ.add hεY, hφ.sub hεY⟩

/-- Off the topological support, the two branches agree with the original map as germs. -/
theorem bandBending_branches_agree_off_support {L b : ℝ}
    {φ Y : AddCircle L × Ioo (0 : ℝ) b → Ambient} (ε : ℝ)
    {p : AddCircle L × Ioo (0 : ℝ) b} (hp : p ∉ tsupport Y) :
    (φ + ε • Y) =ᶠ[𝓝 p] φ ∧ (φ - ε • Y) =ᶠ[𝓝 p] φ := by
  have hzero : Y =ᶠ[𝓝 p] (fun _ => (0 : Ambient)) :=
    notMem_tsupport_iff_eventuallyEq.mp hp
  constructor <;> filter_upwards [hzero] with q hq <;> simp [hq]

/-- In particular, both actual first differentials and pullback metrics are unchanged there. -/
theorem bandBending_branches_differential_off_support {L b : ℝ} [Fact (0 < L)]
    {φ Y : AddCircle L × Ioo (0 : ℝ) b → Ambient} (ε : ℝ)
    {p : AddCircle L × Ioo (0 : ℝ) b} (hp : p ∉ tsupport Y) :
    bandDifferential (φ + ε • Y) p = bandDifferential φ p ∧
    bandDifferential (φ - ε • Y) p = bandDifferential φ p := by
  obtain ⟨hplus, hminus⟩ := bandBending_branches_agree_off_support (φ := φ) ε hp
  exact ⟨hplus.mfderiv_eq, hminus.mfderiv_eq⟩


/-- The common metric is positive on every nonzero tangent whenever the original
map is immersive. Thus no amplitude restriction is needed for immersion. -/
theorem bandBending_branch_immersion {L b : ℝ} [Fact (0 < L)]
    {φ Y : AddCircle L × Ioo (0 : ℝ) b → Ambient}
    (hφ : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Ambient) ∞ φ)
    (hY : IsBandBending φ Y) (ε : ℝ) (p : AddCircle L × Ioo (0 : ℝ) b)
    (himm : Function.Injective (bandDifferential φ p)) :
    Function.Injective (bandDifferential (φ + ε • Y) p) := by
  intro v w he
  let z := v - w
  have hdz : bandDifferential (φ + ε • Y) p z = 0 := by
    simp only [z, map_sub, he, sub_self]
  have hmetric := bandBending_branch_common_metric hφ hY ε p z z
  have hmetriczero : bandInducedForm (φ + ε • Y) p z z = 0 := by
    simp only [bandInducedForm, hdz, inner_zero_left]
  rw [hmetriczero] at hmetric
  have hnonneg : 0 ≤ ε^2 * bandInducedForm Y p z z :=
    mul_nonneg (sq_nonneg ε) real_inner_self_nonneg
  have hbasenonneg : 0 ≤ bandInducedForm φ p z z := real_inner_self_nonneg
  have hbasezero : bandInducedForm φ p z z = 0 := by linarith
  have hdzφ : bandDifferential φ p z = 0 := inner_self_eq_zero.mp hbasezero
  apply himm
  exact sub_eq_zero.mp (by simpa only [z, map_sub] using hdzφ)

theorem bandBending_opposite_branches_immersion {L b : ℝ} [Fact (0 < L)]
    {φ Y : AddCircle L × Ioo (0 : ℝ) b → Ambient}
    (hφ : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Ambient) ∞ φ)
    (hY : IsBandBending φ Y) (ε : ℝ) (p : AddCircle L × Ioo (0 : ℝ) b)
    (himm : Function.Injective (bandDifferential φ p)) :
    Function.Injective (bandDifferential (φ + ε • Y) p) ∧
    Function.Injective (bandDifferential (φ - ε • Y) p) := by
  have he : φ - ε • Y = φ + (-ε) • Y := by
    funext q
    change φ q - ε • Y q = φ q + (-ε) • Y q
    rw [neg_smul, sub_eq_add_neg]
  exact ⟨bandBending_branch_immersion hφ hY ε p himm,
    he.symm ▸ bandBending_branch_immersion hφ hY (-ε) p himm⟩

/-- Nonzero opposite amplitudes give different parametrized maps. -/
theorem bandBending_opposite_branches_ne {L b : ℝ}
    {φ Y : AddCircle L × Ioo (0 : ℝ) b → Ambient}
    {ε : ℝ} (hε : ε ≠ 0) (hY : ∃ p, Y p ≠ 0) :
    φ + ε • Y ≠ φ - ε • Y := by
  intro he
  obtain ⟨p, hp⟩ := hY
  have he' : φ p + ε • Y p = φ p + -(ε • Y p) := by
    simpa only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, sub_eq_add_neg] using congrFun he p
  have ha : ε • Y p = -(ε • Y p) := add_left_cancel he'
  have hz : (ε + ε) • Y p = 0 := by
    rw [add_smul]
    exact (congrArg (fun u : Ambient => u + ε • Y p) ha).trans (neg_add_cancel _)
  have hscalar : ε + ε ≠ 0 := by intro h; apply hε; linarith
  exact hp ((smul_eq_zero.mp hz).resolve_left hscalar)

end
end TightVer401
