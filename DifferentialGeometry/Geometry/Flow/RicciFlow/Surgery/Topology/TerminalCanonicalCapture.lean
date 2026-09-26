import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingReciprocal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalScalarCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

theorem exists_compact_subset_terminalRegularRegion_containing_scalar_sublevels
    (G : P.IncomingSlab a s) {q : ℝ} {C : ℝ≥0} (hq : 0 < q)
    (hbound : ∀ x : P.Carrier, ∀ t ∈ Ioo a s, q < G.flow.scalar t x →
      |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤ C * G.flow.scalar t x ^ 2)
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (hpinch : PhiAlmostNonnegative G.flow (Ico a s) Phi) (A : ℝ) :
    ∃ K : Set P.Carrier, IsCompact K ∧ K ⊆ G.terminalRegularRegion ∧
      ∃ d ∈ Ico a s, ∀ t ∈ Ioo d s, ∀ x : P.Carrier,
        G.flow.scalar t x ≤ A → x ∈ K := by
  classical
  let S := G.terminalRegularRegionᶜ
  have hS : IsCompact S := G.terminalRegularRegion_isOpen.isClosed_compl.isCompact
  have hlocal (x : S) : ∃ U : Set P.Carrier, IsOpen U ∧ x.1 ∈ U ∧
      ∃ d ∈ Ico a s, ∀ t ∈ Ioo d s, ∀ y ∈ U, A < G.flow.scalar t y :=
    G.exists_nhds_scalar_lower_bound_of_not_mem_terminalRegularRegion
      hq hbound hPhi hpinch x.2 A
  choose U hU hxU d hd hscalar using hlocal
  have hcover : S ⊆ ⋃ x : S, U x := fun x hx =>
    mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩
  obtain ⟨F, hF⟩ := hS.elim_finite_subcover U hU hcover
  let O : Set P.Carrier := ⋃ x ∈ F, U x
  have hO : IsOpen O := isOpen_iUnion fun x => isOpen_iUnion fun _ => hU x
  have hSO : S ⊆ O := hF
  have hregular : Oᶜ ⊆ G.terminalRegularRegion := by
    intro x hx
    by_contra h
    exact hx (hSO h)
  let T : Finset (Option S) := insert none (F.image some)
  let time : Option S → ℝ := fun x => x.elim a d
  have htime (x : Option S) : time x ∈ Ico a s := by
    cases x with
    | none => exact ⟨le_rfl, G.lt⟩
    | some x => exact hd x
  obtain ⟨z, hz, hmax⟩ := T.exists_max_image time ⟨none, by simp [T]⟩
  refine ⟨Oᶜ, hO.isClosed_compl.isCompact, hregular, time z, htime z, ?_⟩
  intro t ht x hx hmem
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp hmem
  have hsome : some y ∈ T :=
    Finset.mem_insert_of_mem (Finset.mem_image_of_mem some hy)
  have hhigh := hscalar y t ⟨(hmax (some y) hsome).trans_lt ht.1, ht.2⟩ x hxy
  exact (not_lt_of_ge hx) hhigh

theorem TerminalLimitMetric.isCompact_scalar_sublevel_of_time_derivative_bound
    (L : G.TerminalLimitMetric) {q : ℝ} {C : ℝ≥0} (hq : 0 < q)
    (hbound : ∀ x : P.Carrier, ∀ t ∈ Ioo a s, q < G.flow.scalar t x →
      |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤ C * G.flow.scalar t x ^ 2)
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (hpinch : PhiAlmostNonnegative G.flow (Ico a s) Phi) (A : ℝ) :
    IsCompact {x : G.terminalRegularOpen | metricScalarAt L.metric x ≤ A} := by
  obtain ⟨K, hK, hKreg, d, hd, hcapture⟩ :=
    G.exists_compact_subset_terminalRegularRegion_containing_scalar_sublevels
      hq hbound hPhi hpinch (A + 1)
  let K' : Set G.terminalRegularOpen := Subtype.val ⁻¹' K
  have himage : Subtype.val '' K' = K := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hy
      exact ⟨⟨y, hKreg hy⟩, hy, rfl⟩
  have hK' : IsCompact K' := by
    rw [_root_.Topology.IsEmbedding.isCompact_iff
      (_root_.Topology.IsEmbedding.subtypeVal (p := fun y => y ∈ G.terminalRegularOpen))]
    exact himage ▸ hK
  apply hK'.of_isClosed_subset
    (isClosed_le (metricScalar_smooth L.metric).continuous continuous_const)
  intro x hx
  have hclose : ∀ᶠ t in 𝓝[<] s, G.flow.scalar t x.val < A + 1 :=
    (L.tendsto_metricScalarAt x).eventually_lt_const (hx.trans_lt (lt_add_one A))
  have hlate : ∀ᶠ t in 𝓝[<] s, t ∈ Ioo d s := Ioo_mem_nhdsLT hd.2
  obtain ⟨t, ht, hscalar⟩ := (hlate.and hclose).exists
  exact hcapture t ht x.val hscalar.le

theorem TerminalLimitMetric.exists_compact_containing_canonical_domains
    (L : G.TerminalLimitMetric) {q eps C1 C2 : ℝ} {Ctime : ℝ≥0} (hq : 0 < q)
    (hcanonical : ∀ x : P.Carrier, ∀ t ∈ Ioo a s, q < G.flow.scalar t x →
      Nonempty (CanonicalWitness G.flow eps C1 C2 x t))
    (hbound : ∀ y : P.Carrier, ∀ t ∈ Ioo a s, q < G.flow.scalar t y →
      |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ Ctime * G.flow.scalar t y ^ 2)
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (hpinch : PhiAlmostNonnegative G.flow (Ico a s) Phi)
    (x : G.terminalRegularOpen) (hx : q < metricScalarAt L.metric x) :
    ∃ K : Set G.terminalRegularOpen, IsCompact K ∧
      ∃ d ∈ Ico a s, ∀ t ∈ Ioo d s,
        Nonempty (CanonicalWitness G.flow eps C1 C2 x.1 t) ∧
          ∀ W : CanonicalWitness G.flow eps C1 C2 x.1 t,
            W.domain.carrier ⊆ Subtype.val '' K := by
  have hhigh : ∀ᶠ t in 𝓝[<] s, q < G.flow.scalar t x.1 :=
    (L.tendsto_metricScalarAt x).eventually (Ioi_mem_nhds hx)
  have hC2 : 0 ≤ C2 := by
    have htime : ∀ᶠ t in 𝓝[<] s, t ∈ Ioo a s := Ioo_mem_nhdsLT G.lt
    obtain ⟨t, ht, hqt⟩ := (htime.and hhigh).exists
    let W := (hcanonical x.1 t ht hqt).some
    have hcomparison := (W.scalar_bounds x.1 (interior_subset W.center_inside)).2
    have hpositive := W.Q_pos
    nlinarith
  let A := C2 * (metricScalarAt L.metric x + 1)
  obtain ⟨K, hK, hKregular, d, hd, hcapture⟩ :=
    G.exists_compact_subset_terminalRegularRegion_containing_scalar_sublevels
      hq hbound hPhi hpinch A
  let K' : Set G.terminalRegularOpen := Subtype.val ⁻¹' K
  have himage : Subtype.val '' K' = K := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hy
      exact ⟨⟨y, hKregular hy⟩, hy, rfl⟩
  have hK' : IsCompact K' := by
    rw [_root_.Topology.IsEmbedding.isCompact_iff
      (_root_.Topology.IsEmbedding.subtypeVal (p := fun y => y ∈ G.terminalRegularOpen))]
    exact himage ▸ hK
  have hcenter : ∀ᶠ t in 𝓝[<] s,
      G.flow.scalar t x.1 < metricScalarAt L.metric x + 1 :=
    (L.tendsto_metricScalarAt x).eventually_lt_const (lt_add_one _)
  obtain ⟨d', hd', hcenter'⟩ :=
    (mem_nhdsLT_iff_exists_mem_Ico_Ioo_subset G.lt).mp (hcenter.and hhigh)
  refine ⟨K', hK', max d d', ⟨hd.1.trans (le_max_left _ _), max_lt hd.2 hd'.2⟩, ?_⟩
  intro t ht
  have ht' : t ∈ Ioo d' s := ⟨(le_max_right _ _).trans_lt ht.1, ht.2⟩
  refine ⟨hcanonical x.1 t ⟨hd'.1.trans_lt ht'.1, ht.2⟩ (hcenter' ht').2, ?_⟩
  intro W y hy
  rw [himage]
  apply hcapture t ⟨(le_max_left _ _).trans_lt ht.1, ht.2⟩ y
  exact (W.scalar_bounds y hy).2.trans (mul_le_mul_of_nonneg_left
    (hcenter' ht').1.le hC2)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
