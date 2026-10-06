import DifferentialGeometry.Geometry.Fibration.ActualFirstGraphData
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortChartFamilyApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortChartFamilyBindings
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortChartFamilyEdgeApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortQuantitativeApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortPacketsResidualApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortActiveSupportPacket
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortBlockBudgets
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortCircleGram
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortCloudPackets
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortConstantComparison
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortEdgeComparisonList
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortEdgeConstantComparison
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortEdgeSupportLink
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortFirstComparisonList
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortFirstGraphAssembly
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortFirstGraphEdgeGroup
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortFirstGraphModel
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortFirstGraphTags
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortFirstGraphTagsScalar
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortGlobalBlockMapBridge
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortHeightComparison
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortRawAlignment
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortRetainedMarkerCloud
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortSupportRows
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortZeroConstantComparison
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortZeroMeeting
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortZeroMeetingTcp
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortZeroRawTcp
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortZeroAdaptedPhysicalTest
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAffineHeight
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryWholeSupportCount
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryReplacementStrictBCF2K

/-!
# Boundary port (lane B-PORT-A): ActualFirstGraphData (circle-stage closure)

GENERATED from `DifferentialGeometry/Geometry/Fibration/ActualFirstGraphData.lean` by
`build-logs/scratch/B-PORT-A/gen_circle.py` (engine `portlib2.py`); do
not edit by hand, re-run the script. Closed family → boundary family (`LocalPacketsOnB` /
`LocalPacketsOnBF`, complete σ-compact carrier, regional `…On` families, ACTIVE edge `edgeB`); every
ported declaration `x` ↦ `x_BAUGP` (namespaced `T.m` ↦ `TOn.m_BAUGP`). Substitution table and
failure points: `build-logs/resume/state-B-PORT-A.md`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Analysis DifferentialGeometry.Analysis.Calculus GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

section Card

end Card

section Listed

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}
  {Lmax τ γ vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- The listed tags of `D_i` other than edges: the own circle tag, and every circle / slim / zero
tag whose closed support meets `D_i = B(i, 10ρ(i))`. -/
def tcpListedPred_BAUGP (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc
    Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂) (i : X) : CGPTag_BAUGP L Z →
        Prop
  | .inl j => j.1 = i ∨ (tsupport (L.circle.cutoff j.1) ∩ ball i (10 * ρ i)).Nonempty
  | .inr (.inl j) => (tsupport (L.slim.cutoff_BCNT j.1) ∩ ball i (10 * ρ i)).Nonempty
  | .inr (.inr (.inl _)) => False
  | .inr (.inr (.inr (.inl k))) =>
      (tsupport (cgpCutoff_BAUGP L Z (.inr (.inr (.inr (.inl k))))) ∩ ball i (10 * ρ i)).Nonempty
  | .inr (.inr (.inr (.inr _))) => False

open Classical in
/-- **`S`**: the listed non-edge tags of `D_i` (see `tcpListedPred_BAUGP`). -/
def tcpListedTags_BAUGP (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc
    Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂) (i : X) : Finset
        (CGPTag_BAUGP L Z) :=
  Finset.univ.filter (tcpListedPred_BAUGP L Z i)

open Classical in
/-- **`S_e`**: the edge charts whose closed support meets `D_i`. -/
def tcpListedEdges_BAUGP (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc
    Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    (i : X) : Finset L.edgeB.finite_centres.toFinset :=
  Finset.univ.filter fun j => (tsupport (L.edgeB.cutoff_BAUGA j.1) ∩ ball i (10 * ρ i)).Nonempty

theorem mem_tcpListedTags_KA7_BAUGP
    {L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂}
    {Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂} {i : X} {t : CGPTag_BAUGP L
        Z} :
    t ∈ tcpListedTags_BAUGP L Z i ↔ tcpListedPred_BAUGP L Z i t := by
  classical
  simp [tcpListedTags_BAUGP]

theorem mem_tcpListedEdges_KA7_BAUGP
    {L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂} {i : X}
    {j : L.edgeB.finite_centres.toFinset} :
    j ∈ tcpListedEdges_BAUGP L i ↔ (tsupport (L.edgeB.cutoff_BAUGA j.1) ∩ ball i (10 * ρ
        i)).Nonempty := by
  classical
  simp [tcpListedEdges_BAUGP]

open Classical in
/-- **The count of the listed tags** (`N = fc07ActiveBound`): from TCP01's count of the circle,
slim, edge and zero supports meeting `D_i`, `#S + #S_e ≤ N + 1` (the `+1` is the own tag) and
`#S_e ≤ N`. -/
theorem tcpListed_card_KA7_BAUGP
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂) (i : X)
    (hcount : ({j | j ∈ L.circle.centres ∧
          (tsupport (L.circle.cutoff j) ∩ ball i (10 * ρ i)).Nonempty}.ncard : ℝ) +
        {j | j ∈ L.slim.centres ∧
          (tsupport (L.slim.cutoff_BCNT j) ∩ ball i (10 * ρ i)).Nonempty}.ncard +
        {j | j ∈ L.edgeB.centres ∧
          (tsupport (L.edgeB.cutoff_BAUGA j) ∩ ball i (10 * ρ i)).Nonempty}.ncard +
        (zeroMeetingList_BAUGP Z i 10).ncard ≤ fc07ActiveBound) :
    ((tcpListedTags_BAUGP L Z i).card : ℝ) + (tcpListedEdges_BAUGP L i).card ≤ fc07ActiveBound + 1 ∧
      ((tcpListedEdges_BAUGP L i).card : ℝ) ≤ fc07ActiveBound := by
  set Sown : Finset L.circle.finite_centres.toFinset := Finset.univ.filter (fun j => j.1 = i)
    with hSown
  set Sc : Finset L.circle.finite_centres.toFinset := Finset.univ.filter
    (fun j => (tsupport (L.circle.cutoff j.1) ∩ ball i (10 * ρ i)).Nonempty) with hSc
  set Ss : Finset L.slim.finite_centres.toFinset := Finset.univ.filter
    (fun j => (tsupport (L.slim.cutoff_BCNT j.1) ∩ ball i (10 * ρ i)).Nonempty) with hSs
  set Sz : Finset Z.finite_centres.toFinset := Finset.univ.filter
    (fun k => (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
      ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial y)) ∩
        ball i (10 * ρ i)).Nonempty) with hSz
  have hown : Sown.card ≤ 1 := Finset.card_le_one.mpr fun a ha b hb =>
    Subtype.ext ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
  have hcSc : (Sc.card : ℝ) = {j | j ∈ L.circle.centres ∧
      (tsupport (L.circle.cutoff j) ∩ ball i (10 * ρ i)).Nonempty}.ncard := by
    rw [hSc, card_filter_toFinset_eq_ncard'_KA7 L.circle.finite_centres
      (fun j => (tsupport (L.circle.cutoff j) ∩ ball i (10 * ρ i)).Nonempty)]
  have hcSs : (Ss.card : ℝ) = {j | j ∈ L.slim.centres ∧
      (tsupport (L.slim.cutoff_BCNT j) ∩ ball i (10 * ρ i)).Nonempty}.ncard := by
    rw [hSs, card_filter_toFinset_eq_ncard'_KA7 L.slim.finite_centres
      (fun j => (tsupport (L.slim.cutoff_BCNT j) ∩ ball i (10 * ρ i)).Nonempty)]
  have hcSe : ((tcpListedEdges_BAUGP L i).card : ℝ) = {j | j ∈ L.edgeB.centres ∧
      (tsupport (L.edgeB.cutoff_BAUGA j) ∩ ball i (10 * ρ i)).Nonempty}.ncard := by
    rw [tcpListedEdges_BAUGP, card_filter_toFinset_eq_ncard'_KA7 L.edgeB.finite_centres
      (fun j => (tsupport (L.edgeB.cutoff_BAUGA j) ∩ ball i (10 * ρ i)).Nonempty)]
  have hcSz : (Sz.card : ℝ) = (zeroMeetingList_BAUGP Z i 10).ncard := by
    rw [hSz, card_filter_toFinset_eq_ncard_KA7 Z.finite_centres
      (fun k hk => (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
        ((Z.zero k hk).radial y)) ∩ ball i (10 * ρ i)).Nonempty)]
    rfl
  have hsub : tcpListedTags_BAUGP L Z i ⊆
      ((Sown.image (fun j => (.inl j : CGPTag_BAUGP L Z)) ∪ Sc.image (fun j => (.inl j :
          CGPTag_BAUGP L Z))) ∪
        Ss.image (fun j => (.inr (.inl j) : CGPTag_BAUGP L Z))) ∪
        Sz.image (fun k => (.inr (.inr (.inr (.inl k))) : CGPTag_BAUGP L Z)) := by
    intro t ht
    rw [mem_tcpListedTags_KA7_BAUGP] at ht
    simp only [Finset.mem_union, Finset.mem_image]
    rcases t with j | j | j | k | q
    · rcases ht with h | h
      · exact Or.inl (Or.inl (Or.inl ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, rfl⟩))
      · exact Or.inl (Or.inl (Or.inr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, rfl⟩))
    · exact Or.inl (Or.inr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩, rfl⟩)
    · exact ht.elim
    · exact Or.inr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩, rfl⟩
    · exact ht.elim
  have hcard := Finset.card_le_card hsub
  have h1 := Finset.card_union_le
    ((Sown.image (fun j => (.inl j : CGPTag_BAUGP L Z)) ∪ Sc.image (fun j => (.inl j : CGPTag_BAUGP
        L Z))) ∪
      Ss.image (fun j => (.inr (.inl j) : CGPTag_BAUGP L Z)))
    (Sz.image (fun k => (.inr (.inr (.inr (.inl k))) : CGPTag_BAUGP L Z)))
  have h2 := Finset.card_union_le
    (Sown.image (fun j => (.inl j : CGPTag_BAUGP L Z)) ∪ Sc.image (fun j => (.inl j : CGPTag_BAUGP
        L Z)))
    (Ss.image (fun j => (.inr (.inl j) : CGPTag_BAUGP L Z)))
  have h3 := Finset.card_union_le (Sown.image (fun j => (.inl j : CGPTag_BAUGP L Z)))
    (Sc.image (fun j => (.inl j : CGPTag_BAUGP L Z)))
  have i1 := Finset.card_image_le (s := Sown) (f := fun j => (.inl j : CGPTag_BAUGP L Z))
  have i2 := Finset.card_image_le (s := Sc) (f := fun j => (.inl j : CGPTag_BAUGP L Z))
  have i3 := Finset.card_image_le (s := Ss) (f := fun j => (.inr (.inl j) : CGPTag_BAUGP L Z))
  have i4 := Finset.card_image_le (s := Sz)
    (f := fun k => (.inr (.inr (.inr (.inl k))) : CGPTag_BAUGP L Z))
  have htot : (tcpListedTags_BAUGP L Z i).card ≤ 1 + Sc.card + Ss.card + Sz.card := by omega
  have htotR : ((tcpListedTags_BAUGP L Z i).card : ℝ) ≤ 1 + Sc.card + Ss.card + Sz.card := by
    exact_mod_cast htot
  have h0 : (0 : ℝ) ≤ (zeroMeetingList_BAUGP Z i 10).ncard := Nat.cast_nonneg _
  have h0c : (0 : ℝ) ≤ {j | j ∈ L.circle.centres ∧
      (tsupport (L.circle.cutoff j) ∩ ball i (10 * ρ i)).Nonempty}.ncard := Nat.cast_nonneg _
  have h0s : (0 : ℝ) ≤ {j | j ∈ L.slim.centres ∧
      (tsupport (L.slim.cutoff_BCNT j) ∩ ball i (10 * ρ i)).Nonempty}.ncard := Nat.cast_nonneg _
  constructor
  · rw [hcSc, hcSs, hcSz] at htotR
    rw [hcSe]
    linarith
  · rw [hcSe]
    linarith

end Listed

section Rows

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}
  {vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricN_TCP05D_KA7_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedN_TCP05D_KA7_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricC_TCP05D_KA7_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- The circle rows `A_j` of the model from a coisometry family. -/
def tcpAcOf_BAUGP (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ
    δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
    [∀ a, MetricSpace (C a)] {o : ∀ a, C a}
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂)
    (Acf : X → ℝ² →L[ℝ] ℝ²) : CGPTag_BAUGP L Z → ℝ² →L[ℝ] ℝ²
  | .inl j => Acf j.1
  | .inr _ => 0

/-- The circle offsets `c_j = s_j u_j(p_i)` of the model. -/
def tcpCcOf_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (i : X) : CGPTag_BAUGP P P.zero → ℝ²
  | .inl j => (ρ j.1 / ρ i) • circleRaw_KA3_BAUGP P j.1 i
  | .inr _ => 0

/-- The scalar rows of the model: slim `e₀∘A_j`, edge `s_j⁻¹ e₀∘A_j`, zero `e₀∘A₀`. -/
def tcpA1Of_BAUGP (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ
    δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
    [∀ a, MetricSpace (C a)] {o : ∀ a, C a}
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂)
    (i : X) (Asf Aef Azf : X → ℝ² →L[ℝ] ℝ¹) : CGPTag_BAUGP L Z → ℝ² →L[ℝ] ℝ
  | .inl _ => 0
  | .inr (.inl j) => (EuclideanSpace.proj (0 : Fin 1)).comp (Asf j.1)
  | .inr (.inr (.inl j)) => (ρ j.1 / ρ i)⁻¹ • (EuclideanSpace.proj (0 : Fin 1)).comp (Aef j.1)
  | .inr (.inr (.inr (.inl k))) => (EuclideanSpace.proj (0 : Fin 1)).comp (Azf k.1)
  | .inr (.inr (.inr (.inr _))) => 0

/-- The scalar offsets of the model: slim `s_j u_j(p_i)`, edge `u_j(p_i)`, zero `s₀η₀(p_i)`. -/
def tcpC1Of_BAUGP (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ
    δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
    [∀ a, MetricSpace (C a)] {o : ∀ a, C a}
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂)
    (i : X) : CGPTag_BAUGP L Z → ℝ
  | .inl _ => 0
  | .inr (.inl j) => ρ j.1 / ρ i * slimRaw_KA3_BAUGP L j.1 i
  | .inr (.inr (.inl j)) => edgeRaw_KA3_BAUGP L j.1 i
  | .inr (.inr (.inr (.inl k))) =>
      (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / ρ i *
        (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial i
  | .inr (.inr (.inr (.inr _))) => 0

end Rows

section Height

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}
  {vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- **The height input of the edge network from TCP04** at a circle centre `i`: from TCP04's
conclusion at `i` (no edge support / low branch / high branch) there are `τ`, a row `Bτ` of norm
`≤ 1` and an offset `cτ` with, on `D_i`: the listed edge cutoffs are `f(η_k/Δ) g(τ/Δ)`; `τ = t` or
(`τ = 0` and the `E'` marker vanishes); `τ` is smooth with `|τ − (Bτη_i + cτ)| ≤ θ/2` and
`|dτ − Bτ dη_i| ≤ (θ/20)|·|`. -/
theorem tcp05_height_data_KA7_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (hΔ : 1 ≤ Δ) {i : X} (hi : i ∈ P.circle.centres) {θ : ℝ} (hθ : 0 ≤ θ)
    (hball : ∀ j ∈ P.edgeB.centres, (tsupport (P.edgeB.cutoff_BAUGA j) ∩ ball i (10 * ρ
        i)).Nonempty →
      ball i (10 * ρ i) ⊆ ball j (100 * Δ * ρ j))
    (hH : ((∀ j ∈ P.edgeB.centres, ¬ (tsupport (P.edgeB.cutoff_BAUGA j) ∩ ball i (10 * ρ
        i)).Nonempty) →
          ∀ j, ∀ x ∈ ball i (10 * ρ i), P.edgeB.cutoff_BAUGA j x = 0) ∧
        ((∃ j ∈ P.edgeB.centres, (tsupport (P.edgeB.cutoff_BAUGA j) ∩ ball i (10 * ρ i)).Nonempty) →
          (∀ x ∈ ball i (10 * ρ i), P.edgeB.smoothing x / ρ x < 3 * Δ / 20 ∧
            ∀ j ∈ P.edgeB.centres, x ∈ ball j (100 * Δ * ρ j) →
              P.edgeB.cutoff_BAUGA j x = edgeCoordinateProfile (P.edgeB.coord_BAUGA j x / Δ)) ∨
          ∃ B : ℝ² →L[ℝ] ℝ¹, B.comp (ContinuousLinearMap.adjoint B) = ContinuousLinearMap.id ℝ _ ∧
            ∀ x ∈ ball i (10 * ρ i),
              Δ / 10 ≤ P.edgeB.smoothing x / ρ x ∧ P.edgeB.smoothing x / ρ x ≤ 181 * Δ / 20 ∧
              ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (fun y => P.edgeB.smoothing y / ρ y) x ∧
              ‖EuclideanSpace.single 0 (P.edgeB.smoothing x / ρ x - P.edgeB.smoothing i / ρ i) -
                  B (cgpCircleCoord_BAUGP P i hi x -
                    cgpCircleCoord_BAUGP P i hi i)‖ ≤ θ / 2 ∧
              ∀ w : TangentSpace 𝓘(ℝ, E3) x,
                ‖EuclideanSpace.single 0
                      (mvfderiv 𝓘(ℝ, E3) (fun y => P.edgeB.smoothing y / ρ y) x w) -
                    B (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord_BAUGP P i hi) x w)‖ ≤
                  θ / 20 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) ∧
                |mvfderiv 𝓘(ℝ, E3) (fun y => P.edgeB.smoothing y / ρ y) x w| ≤
                  2 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w))) :
    ∃ τf : X → ℝ, ∃ Bτ : ℝ² →L[ℝ] ℝ, ∃ cτ : ℝ, ‖Bτ‖ ≤ 1 ∧
      (∀ y ∈ ball i (10 * ρ i), ∀ k ∈ tcpListedEdges_BAUGP P i,
        P.edgeB.cutoff_BAUGA k.1 y =
          edgeCoordinateProfile (P.edgeB.coord_BAUGA k.1 y / Δ) * edgeHeightProfile (τf y / Δ)) ∧
      (∀ y ∈ ball i (10 * ρ i), τf y = cgpHeight_BAUGP P y ∨
        (τf y = 0 ∧ cgpEdgeMarker_BAUGP P y = 0)) ∧
      ∀ x ∈ ball i (10 * ρ i), ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ τf x ∧
        |τf x - (Bτ (cgpCircleCoord_BAUGP P i hi x) + cτ)| ≤ θ / 2 ∧
        ∀ w : TangentSpace 𝓘(ℝ, E3) x, |mvfderiv 𝓘(ℝ, E3) τf x w -
          Bτ (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord_BAUGP P i hi) x w)| ≤
          θ / 20 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) := by
  have hΔ0 : 0 < Δ := by linarith
  have hg0 : edgeHeightProfile 0 = 1 := descendingIntervalProfile_one (by norm_num) (by norm_num)
  -- the constant input `τ = 0` (no edge support or the low branch)
  have hconst : ∀ x ∈ ball i (10 * ρ i), ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (fun _ : X => (0 : ℝ)) x ∧
      |(fun _ : X => (0 : ℝ)) x - ((0 : ℝ² →L[ℝ] ℝ) (cgpCircleCoord_BAUGP P i hi x) +
        0)| ≤ θ / 2 ∧
      ∀ w : TangentSpace 𝓘(ℝ, E3) x, |mvfderiv 𝓘(ℝ, E3) (fun _ : X => (0 : ℝ)) x w -
        (0 : ℝ² →L[ℝ] ℝ) (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord_BAUGP P i hi) x w)| ≤
        θ / 20 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) := by
    intro x _
    refine ⟨contMDiffAt_const, ?_, fun w => ?_⟩
    · simp only [zero_apply, add_zero, sub_zero, abs_zero]
      linarith
    · rw [mvfderiv_const]
      simp only [zero_apply, sub_zero, abs_zero]
      positivity
  by_cases hex : ∃ j ∈ P.edgeB.centres, (tsupport (P.edgeB.cutoff_BAUGA j) ∩ ball i (10 * ρ
      i)).Nonempty
  · rcases hH.2 hex with hlow | ⟨B, hB, hhigh⟩
    · refine ⟨fun _ => 0, 0, 0, by rw [norm_zero]; exact zero_le_one, ?_, ?_, hconst⟩
      · intro y hy k hk
        have hkl := (mem_tcpListedEdges_KA7_BAUGP (i := i)).mp hk
        have hkc := (Set.Finite.mem_toFinset _).mp k.2
        rw [(hlow y hy).2 k.1 hkc (hball k.1 hkc hkl hy), zero_div, hg0, mul_one]
      · intro y hy
        right
        refine ⟨rfl, ?_⟩
        rw [cgpEdgeMarker_BAUGP, cgpEdgeH_eq_zero_of_le, zero_mul]
        have h1 := (hlow y hy).1
        rw [cgpHeight_BAUGP, div_le_iff₀ hΔ0]
        linarith
    · refine ⟨fun y => P.edgeB.smoothing y / ρ y, (EuclideanSpace.proj (0 : Fin 1)).comp B,
        P.edgeB.smoothing i / ρ i -
          (EuclideanSpace.proj (0 : Fin 1)).comp B (cgpCircleCoord_BAUGP P i hi i),
        norm_proj_comp_le_KA7 B
          (DifferentialGeometry.Geometry.Fibration.norm_coisometry_le_one B hB),
        ?_, fun y _ => Or.inl rfl, fun x hx => ?_⟩
      · intro y hy k hk
        have hkl := (mem_tcpListedEdges_KA7_BAUGP (i := i)).mp hk
        have hkc := (Set.Finite.mem_toFinset _).mp k.2
        exact P.edgeB.cutoff_eq_formula_BAUGA hkc (hball k.1 hkc hkl hy)
      · obtain ⟨-, -, hsm, hval, hder⟩ := hhigh x hx
        refine ⟨hsm, ?_, fun w => ?_⟩
        · have h := hval
          rw [norm_single_sub_eq_KA5, map_sub] at h
          have he : P.edgeB.smoothing x / ρ x -
              ((EuclideanSpace.proj (0 : Fin 1)).comp B
                  (cgpCircleCoord_BAUGP P i hi x) +
                (P.edgeB.smoothing i / ρ i - (EuclideanSpace.proj (0 : Fin 1)).comp B
                  (cgpCircleCoord_BAUGP P i hi i))) =
              P.edgeB.smoothing x / ρ x - P.edgeB.smoothing i / ρ i -
                (B (cgpCircleCoord_BAUGP P i hi x) -
                  B (cgpCircleCoord_BAUGP P i hi i)) 0 := by
            have hp : ∀ v : ℝ¹, (EuclideanSpace.proj (0 : Fin 1) : ℝ¹ →L[ℝ] ℝ) v = v 0 :=
              fun v => rfl
            simp only [ContinuousLinearMap.comp_apply, hp, PiLp.sub_apply]
            ring
          rw [he]
          exact h
        · have h := (hder w).1
          rw [norm_single_sub_eq_KA5] at h
          exact h
  · refine ⟨fun _ => 0, 0, 0, by rw [norm_zero]; exact zero_le_one, ?_, ?_, hconst⟩
    · intro y _ k hk
      have hkl := (mem_tcpListedEdges_KA7_BAUGP (i := i)).mp hk
      exact (hex ⟨k.1, (Set.Finite.mem_toFinset _).mp k.2, hkl⟩).elim
    · intro y hy
      right
      refine ⟨rfl, ?_⟩
      have hnone : ∀ j ∈ P.edgeB.centres,
          ¬ (tsupport (P.edgeB.cutoff_BAUGA j) ∩ ball i (10 * ρ i)).Nonempty :=
        fun j hj hm => hex ⟨j, hj, hm⟩
      have hsum : cgpEdgeSum_BAUGP P y = 0 := by
        unfold cgpEdgeSum_BAUGP
        exact Finset.sum_eq_zero fun j _ => hH.1 hnone j.1 y hy
      rw [cgpEdgeMarker_BAUGP, hsum,
        cfsRamp_eq_zero (fun t ht => lc87EdgeTransition_eq_zero ht) (by norm_num) (by norm_num),
        mul_zero]

end Height


end DifferentialGeometry.Geometry.Collapse
