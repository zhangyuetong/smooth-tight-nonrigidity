import TightVer401.VisibleConnectorDisplacedSeamRebase
import TightVer401.RelativeSaddleSmoothing

/-! The full smoothing carrier is constructed from the SAME raw inverse target
and incoming branch domain. No branch extension, final scalar or pending incoming
interface is imported. Closed rebased rulings are retained by their literal old
height, including the original incoming endpoint and the positive terminal end. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix

/-- Full fixed domain for two-sided smoothing. -/
def visibleConnectorFinalSmoothingCarrier (Vraw GinU : Set Coord) (B : Coord → ℝ) :
    Set Coord := Vraw ∩ (GinU ∪ B ⁻¹' Ioi 0)

/-- Only continuity on the actual raw domain is needed. -/
theorem visibleConnectorFinalSmoothingCarrier_open
    {Vraw GinU : Set Coord} {B : Coord → ℝ}
    (hRaw : IsOpen Vraw) (hGin : IsOpen GinU) (hB : ContinuousOn B Vraw) :
    IsOpen (visibleConnectorFinalSmoothingCarrier Vraw GinU B) := by
  rw [visibleConnectorFinalSmoothingCarrier, inter_union_distrib_left]
  exact (hRaw.inter hGin).union (hB.isOpen_inter_preimage hRaw isOpen_Ioi)

theorem visibleConnectorFinalSmoothingCarrier_subset_raw
    (Vraw GinU : Set Coord) (B : Coord → ℝ) :
    visibleConnectorFinalSmoothingCarrier Vraw GinU B ⊆ Vraw := fun _ hx => hx.1

/-- Retain containment in the SAME Cartesian inverse target. -/
theorem visibleConnectorFinalSmoothingCarrier_subset_target
    {Vraw GinU T : Set Coord} {B : Coord → ℝ} (hRawTarget : Vraw ⊆ T) :
    visibleConnectorFinalSmoothingCarrier Vraw GinU B ⊆ T :=
  (visibleConnectorFinalSmoothingCarrier_subset_raw Vraw GinU B).trans hRawTarget

theorem visibleConnectorFinalSmoothingCarrier_incoming_subset
    (Vraw GinU : Set Coord) (B : Coord → ℝ) :
    Vraw ∩ GinU ⊆ visibleConnectorFinalSmoothingCarrier Vraw GinU B :=
  fun _ hx => ⟨hx.1, Or.inl hx.2⟩

theorem visibleConnectorFinalSmoothingCarrier_positive_subset
    (Vraw GinU : Set Coord) (B : Coord → ℝ) :
    Vraw ∩ B ⁻¹' Ioi 0 ⊆ visibleConnectorFinalSmoothingCarrier Vraw GinU B :=
  fun _ hx => ⟨hx.1, Or.inr hx.2⟩

theorem visibleConnectorFinalSmoothingCarrier_seam_subset
    {Vraw GinU S : Set Coord} {B : Coord → ℝ}
    (hRaw : S ⊆ Vraw) (hGin : S ⊆ GinU) :
    S ⊆ visibleConnectorFinalSmoothingCarrier Vraw GinU B :=
  fun _ hx => ⟨hRaw hx, Or.inl (hGin hx)⟩

/-- The entire positive side belongs to the actual raw branch domain. -/
theorem visibleConnectorFinalSmoothingCarrier_positive_domain
    (Vraw GinU : Set Coord) (B : Coord → ℝ) :
    visibleConnectorFinalSmoothingCarrier Vraw GinU B ∩
      interior (B ⁻¹' Ioi 0) ⊆ Vraw := fun _ hx => hx.1.1

/-- The entire negative side belongs to the actual incoming branch domain. -/
theorem visibleConnectorFinalSmoothingCarrier_negative_domain
    (Vraw GinU : Set Coord) (B : Coord → ℝ) :
    visibleConnectorFinalSmoothingCarrier Vraw GinU B ∩
      interior (B ⁻¹' Ioi 0)ᶜ ⊆ GinU := by
  intro x hx
  exact hx.1.2.resolve_right (interior_subset hx.2)

/-- A useful stronger form also includes height zero, hence seam points. -/
theorem visibleConnectorFinalSmoothingCarrier_nonpositive_domain
    {Vraw GinU : Set Coord} {B : Coord → ℝ} {x : Coord}
    (hx : x ∈ visibleConnectorFinalSmoothingCarrier Vraw GinU B)
    (hB : B x ≤ 0) : x ∈ GinU := by
  exact hx.2.resolve_right (not_lt.mpr hB)

/-- The actual closed rebased source strip; its parameter includes BOTH ends. -/
def visibleConnectorFinalSmoothingClosedRebasedBand
    (p w : ℝ → Coord) (a b d : ℝ → ℝ) : Set Coord :=
  {x | ∃ s u : ℝ, u ∈ Icc (0 : ℝ) 1 ∧
    x = visibleConnectorSource (visibleConnectorRebasedSource p w a b)
      (visibleConnectorRebasedRuling w a d) (![s, u] : Coord)}

/-- Every point of the closed strip belongs to the full carrier. The proof uses
literal height and positivity of the SAME ruling scale, rather than silently
replacing the final domain by a seam collar. The old nonpositive strip is the
precise remaining incoming-domain producer input. -/
theorem visibleConnectorFinalSmoothingCarrier_closed_rebased_band
    {Vraw GinU : Set Coord} {B : Coord → ℝ}
    {p w : ℝ → Coord} {a b d : ℝ → ℝ}
    (hd : ∀ s, 0 < d s)
    (hRaw : ∀ s t : ℝ, b s ≤ t → t ≤ b s + d s →
      visibleConnectorSource p w (![a s, t] : Coord) ∈ Vraw)
    (hGin : ∀ s t : ℝ, b s ≤ t → t ≤ 0 →
      visibleConnectorSource p w (![a s, t] : Coord) ∈ GinU)
    (hHeight : ∀ s u : ℝ, u ∈ Icc (0 : ℝ) 1 →
      B (visibleConnectorSource (visibleConnectorRebasedSource p w a b)
        (visibleConnectorRebasedRuling w a d) (![s, u] : Coord)) = b s + u * d s) :
    visibleConnectorFinalSmoothingClosedRebasedBand p w a b d ⊆
      visibleConnectorFinalSmoothingCarrier Vraw GinU B := by
  rintro x ⟨s, u, hu, rfl⟩
  have hlo : b s ≤ b s + u * d s := by
    have hmul := mul_nonneg hu.1 (hd s).le
    linarith
  have hhi : b s + u * d s ≤ b s + d s := by
    have hmul := mul_le_mul_of_nonneg_right hu.2 (hd s).le
    linarith
  refine ⟨?_, ?_⟩
  · rw [visibleConnector_rebase_source]
    exact hRaw s (b s + u * d s) hlo hhi
  · by_cases hpos : 0 < b s + u * d s
    · right
      change 0 < B _
      rw [hHeight s u hu]
      exact hpos
    · left
      rw [visibleConnector_rebase_source]
      exact hGin s (b s + u * d s) hlo (le_of_not_gt hpos)

/-- Transfer any independently proved physical closed-band identification into
the constructed carrier; this is the OrdinaryData source-closure consumer. -/
theorem visibleConnectorFinalSmoothingCarrier_closed_subset
    {Vraw GinU C : Set Coord} {B : Coord → ℝ}
    {p w : ℝ → Coord} {a b d : ℝ → ℝ}
    (hC : C ⊆ visibleConnectorFinalSmoothingClosedRebasedBand p w a b d)
    (hd : ∀ s, 0 < d s)
    (hRaw : ∀ s t : ℝ, b s ≤ t → t ≤ b s + d s →
      visibleConnectorSource p w (![a s, t] : Coord) ∈ Vraw)
    (hGin : ∀ s t : ℝ, b s ≤ t → t ≤ 0 →
      visibleConnectorSource p w (![a s, t] : Coord) ∈ GinU)
    (hHeight : ∀ s u : ℝ, u ∈ Icc (0 : ℝ) 1 →
      B (visibleConnectorSource (visibleConnectorRebasedSource p w a b)
        (visibleConnectorRebasedRuling w a d) (![s, u] : Coord)) = b s + u * d s) :
    C ⊆ visibleConnectorFinalSmoothingCarrier Vraw GinU B :=
  hC.trans (visibleConnectorFinalSmoothingCarrier_closed_rebased_band hd hRaw hGin hHeight)

end
end TightVer401
