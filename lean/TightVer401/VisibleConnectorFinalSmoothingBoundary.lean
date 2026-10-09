import TightVer401.RelativeSaddleSmoothing

/-!
Worker preflight: HEAD 68996b72a5a3be36982cb90600ccec06c194fb4d,
branch codex/ver503-final-smoothing. Exclusive sources: FinalSmoothing*.lean.
Examined checked exports: exists_relative_saddle_smoothing_on_sides,
relativeSaddlePiecewise_germ_interior/_compl, planarHessian_det_contDiffOn.
Exact consumer: VisibleConnectorWitnessAssemblyOrdinaryData G/U/G_smooth,
actual_saddle_closed and incoming_neighborhood/incoming_germ_retained.
SAME inputs: fixed full V, Gin on GinU, raw on Vraw contained in the same
Cartesian E.target, actual height B and original/terminal boundary sets.
Pending IncomingGin5176081 was read only and is never imported.
Remaining original inputs: compatible eta/rho and native e, actual seam
matching/embedding/classifier, raw-domain full-band coverage, and actual
branch Hessian signs. This leaf constructs separation and explicit open
boundary neighborhoods; it assumes neither a smoothing output nor an inverse.
-/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

/-- Choose a modification region with closure avoiding BOTH boundary sets.
The final full V is unchanged, including the positive terminal boundary. -/
theorem visibleConnectorFinalSmoothing_exists_modification
    {B : Coord → ℝ} {V C K T : Set Coord} (hV : IsOpen V)
    (hC : IsCompact C) (hK : IsCompact K) (hT : IsCompact T)
    (hCV : C ⊆ V) (hzero : ∀ x ∈ C, B x = 0)
    (hnegative : ∀ x ∈ K, B x < 0) (hpositive : ∀ x ∈ T, 0 < B x) :
    ∃ N : Set Coord, IsOpen N ∧ C ⊆ N ∧ closure N ⊆ V \ (K ∪ T) := by
  have hCW : C ⊆ V \ (K ∪ T) := by
    intro x hx
    refine ⟨hCV hx, ?_⟩
    rintro (hk | ht)
    · have hn := hnegative x hk
      rw [hzero x hx] at hn
      exact lt_irrefl 0 hn
    · have hp := hpositive x ht
      rw [hzero x hx] at hp
      exact lt_irrefl 0 hp
  obtain ⟨r, hr, hthick⟩ := hC.exists_cthickening_subset_open
    (hV.sdiff (hK.union hT).isClosed) hCW
  exact ⟨Metric.thickening r C, Metric.isOpen_thickening,
    Metric.self_subset_thickening hr C,
    (Metric.closure_thickening_subset_cthickening r C).trans hthick⟩

/-- Explicit protected incoming neighborhood, on the actual negative side. -/
def visibleConnectorFinalSmoothingIncomingOpen
    (V GinU N : Set Coord) (B : Coord → ℝ) : Set Coord :=
  ((V ∩ GinU) \ closure N) ∩ {x | B x < 0}

/-- Explicit protected terminal neighborhood, on the actual positive side. -/
def visibleConnectorFinalSmoothingTerminalOpen
    (V Vraw N : Set Coord) (B : Coord → ℝ) : Set Coord :=
  ((V ∩ Vraw) \ closure N) ∩ {x | 0 < B x}

/-- Construct the full open incoming equality neighborhood directly from the
relative theorem's outside equality. No first-jet inference is used. -/
theorem visibleConnectorFinalSmoothing_incoming_open
    {B Gin raw H : Coord → ℝ} {V GinU N K : Set Coord}
    (hV : IsOpen V) (hGinU : IsOpen GinU) (hB : ContinuousOn B V)
    (hKV : K ⊆ V) (hKGin : K ⊆ GinU) (hKN : Disjoint K (closure N))
    (hnegative : ∀ x ∈ K, B x < 0)
    (houtside : ∀ x ∈ V \ N,
      H =ᶠ[𝓝 x] relativeSaddlePiecewise {y | B y < 0} Gin raw) :
    let O := visibleConnectorFinalSmoothingIncomingOpen V GinU N B
    IsOpen O ∧ K ⊆ O ∧ O ⊆ V ∩ GinU ∧ EqOn H Gin O := by
  have hOpen : IsOpen (visibleConnectorFinalSmoothingIncomingOpen V GinU N B) := by
    have heq : visibleConnectorFinalSmoothingIncomingOpen V GinU N B =
        (V ∩ B ⁻¹' Iio 0) ∩ (GinU \ closure N) := by
      ext x
      simp only [visibleConnectorFinalSmoothingIncomingOpen, mem_inter_iff,
        Set.mem_sdiff, mem_ofPred_eq, mem_preimage, mem_Iio]
      tauto
    rw [heq]
    exact (hB.isOpen_inter_preimage hV isOpen_Iio).inter
      (hGinU.sdiff isClosed_closure)
  refine ⟨hOpen, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨⟨⟨hKV hx, hKGin hx⟩, fun hn => Set.disjoint_left.mp hKN hx hn⟩,
      hnegative x hx⟩
  · intro x hx
    exact hx.1.1
  · intro x hx
    have he := (houtside x ⟨hx.1.1.1, fun hn => hx.1.2 (subset_closure hn)⟩).self_of_nhds
    have hn : B x < 0 := hx.2
    simpa [relativeSaddlePiecewise, hn] using he

/-- Construct the full open raw-terminal equality neighborhood while keeping
V fixed. Positive height is used with its actual sign. -/
theorem visibleConnectorFinalSmoothing_terminal_open
    {B Gin raw H : Coord → ℝ} {V Vraw N T : Set Coord}
    (hV : IsOpen V) (hVraw : IsOpen Vraw) (hB : ContinuousOn B V)
    (hTV : T ⊆ V) (hTRaw : T ⊆ Vraw) (hTN : Disjoint T (closure N))
    (hpositive : ∀ x ∈ T, 0 < B x)
    (houtside : ∀ x ∈ V \ N,
      H =ᶠ[𝓝 x] relativeSaddlePiecewise {y | B y < 0} Gin raw) :
    let O := visibleConnectorFinalSmoothingTerminalOpen V Vraw N B
    IsOpen O ∧ T ⊆ O ∧ O ⊆ V ∩ Vraw ∧ EqOn H raw O := by
  have hOpen : IsOpen (visibleConnectorFinalSmoothingTerminalOpen V Vraw N B) := by
    have heq : visibleConnectorFinalSmoothingTerminalOpen V Vraw N B =
        (V ∩ B ⁻¹' Ioi 0) ∩ (Vraw \ closure N) := by
      ext x
      simp only [visibleConnectorFinalSmoothingTerminalOpen, mem_inter_iff,
        Set.mem_sdiff, mem_ofPred_eq, mem_preimage, mem_Ioi]
      tauto
    rw [heq]
    exact (hB.isOpen_inter_preimage hV isOpen_Ioi).inter
      (hVraw.sdiff isClosed_closure)
  refine ⟨hOpen, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨⟨⟨hTV hx, hTRaw hx⟩, fun hn => Set.disjoint_left.mp hTN hx hn⟩,
      hpositive x hx⟩
  · intro x hx
    exact hx.1.1
  · intro x hx
    have he := (houtside x ⟨hx.1.1.1, fun hn => hx.1.2 (subset_closure hn)⟩).self_of_nhds
    have hp : 0 < B x := hx.2
    simpa [relativeSaddlePiecewise, not_lt.mpr hp.le] using he

end
end TightVer401


