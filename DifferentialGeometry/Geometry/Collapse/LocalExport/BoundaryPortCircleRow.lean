import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortStageFirstPlanes

/-!
# TCP05's pruned circle model on the boundary family (lane O-PORT-A)

The model `K_i ∘ Φ_i` of the circle stage of `port_circle_interior_table_BAUGP` (PortTargets
v3.1) on the generic boundary family: `Φ_i = tcpModelGraph_BAUGP …` (TCP05's model graph with the
ACTUAL support lists of `D_i = B(i, 10ρ(i))` and TCP05's comparison data), pruned by CFS27's
`K_i = π_{keep(ρ(i))}` (`firstKeepTags_GAF5_BAUGP`). Closed twin: the model of
`exists_firstStagePlanes_PLN` (`Fibration/ActualStageFirstPlanes.lean`), i.e.
`tcp05_pruned_explicit_PLN` applied to `tcpModelGraph`; here through the boundary ports
`tcp05_row_table_PLN_BAUGP` / `tcp05_pruned_explicit_PLN_BAUGP`.

* `tcpPrunedModel_BPC`: the pruned model (a definition at the level of the generic family, so that
  every statement about it carries the decidable-equality instance of the ported rows);
* `tcpPrunedModel_marker_BPC`: a retained marker with `ρ(c_a) ≤ ρ(i)/2` has a zero block;
* `tcp05_pruned_point_BPC`: TCP05's table at `i` ⟹ the pruned model is smooth, has the own block
  `(a, 1)`, `C²` bounds `≤ C`, (TG) on the threshold-`8` core, zero deleted markers and zero
  scale derivative.
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

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

section Generic

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}
  {Lmax τ γ vs : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

open Classical in
/-- **The pruned circle model** `K_i ∘ Φ_i`: TCP05's model graph at `i` with the actual support
lists and the comparison data `A_c, c_c, A₁, c₁, B_τ, c_τ`, pruned by CFS27 at the reference radius
`ρ(i)`. -/
def tcpPrunedModel_BPC
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
      U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂) (i : X)
    (Ac : CGPTag_BAUGP L Z → ℝ² →L[ℝ] ℝ²) (cc : CGPTag_BAUGP L Z → ℝ²)
    (A1 : CGPTag_BAUGP L Z → ℝ² →L[ℝ] ℝ) (c1 : CGPTag_BAUGP L Z → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ) :
    ℝ² → BlockSpace (fun _ : CGPTag_BAUGP L Z => ℝ²) :=
  ⇑(blockRestrict (V := fun _ : CGPTag_BAUGP L Z => ℝ²) (firstKeepTags_GAF5_BAUGP L Z (ρ i))) ∘
    tcpModelGraph_BAUGP L Z i (tcpListedTags_BAUGP L Z i) (tcpListedEdges_BAUGP L i) Ac cc A1 c1
      Bτ cτ

/-- **CFS27's deleted blocks**: a retained marker with `ρ(c_a) ≤ ρ(i)/2` has a zero block in the
pruned model. -/
theorem tcpPrunedModel_marker_BPC
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
      U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂) (i : X)
    (Ac : CGPTag_BAUGP L Z → ℝ² →L[ℝ] ℝ²) (cc : CGPTag_BAUGP L Z → ℝ²)
    (A1 : CGPTag_BAUGP L Z → ℝ² →L[ℝ] ℝ) (c1 : CGPTag_BAUGP L Z → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ)
    (a : CGPMarkerIndex_BAUGP L) (ha : ρ (cgpMarkerCentre_BAUGP L a) ≤ ρ i / 2) (u : ℝ²) :
    tcpPrunedModel_BPC L Z i Ac cc A1 c1 Bτ cτ u (cgpMarkerTag_BAUGP L Z a) = 0 := by
  classical
  unfold tcpPrunedModel_BPC
  rw [Function.comp_apply, blockRestrict_apply]
  exact ite_eq_right_iff.mpr fun h => absurd h (firstKeep_marker_GAF5_BAUGP L Z a ha)

end Generic

section Packets

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- The model metrics of `LocalPacketsOnBF`, as a named local instance. -/
local instance instMetricN_BPC
    (P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
      ζ Λz U₁ U₂ Ue₁ Ue₂) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalPacketsOnBF`, as a named local instance. -/
local instance instChartedN_BPC
    (P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
      ζ Λz U₁ U₂ Ue₁ Ue₂) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalPacketsOnBF`, as a named local instance. -/
local instance instMetricC_BPC
    (P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
      ζ Λz U₁ U₂ Ue₁ Ue₂) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

open Classical in
/-- **TCP05's table at one circle reference, pruned** (`tcp05_pruned_explicit_PLN_BAUGP` for the
explicit model `tcpModelGraph_BAUGP` with the actual lists): from the `C²` bounds and (TG) of the
model graph at `j` (the conclusion of `tcp05_row_table_PLN_BAUGP` at `j`), the pruned model
`tcpPrunedModel_BPC` is smooth, has the own block `(a, 1)`, `C²` bounds `≤ C`, (TG) on
`B(j, 200ρ(j)) ∩ {‖η_j‖ ≤ 8}`, derivative annihilated by every marker with `ρ(c_a) ≤ ρ(j)/2`, and
zero scale derivative. -/
theorem tcp05_pruned_point_BPC
    (P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
      ζ Λz U₁ U₂ Ue₁ Ue₂)
    (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000) {eg : ℝ}
    (j : P.toLocalPacketsOnB.circle.finite_centres.toFinset)
    (Ac : CGPTag_BAUGP P.toLocalPacketsOnB P.zero → ℝ² →L[ℝ] ℝ²)
    (cc : CGPTag_BAUGP P.toLocalPacketsOnB P.zero → ℝ²)
    (A1 : CGPTag_BAUGP P.toLocalPacketsOnB P.zero → ℝ² →L[ℝ] ℝ)
    (c1 : CGPTag_BAUGP P.toLocalPacketsOnB P.zero → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ)
    (hb : ∀ a, ‖fderiv ℝ (tcpModelGraph_BAUGP P.toLocalPacketsOnB P.zero j.1
          (tcpListedTags_BAUGP P.toLocalPacketsOnB P.zero j.1)
          (tcpListedEdges_BAUGP P.toLocalPacketsOnB j.1) Ac cc A1 c1 Bτ cτ) a‖ ≤ tcpGraphConst ∧
        ‖fderiv ℝ (fderiv ℝ (tcpModelGraph_BAUGP P.toLocalPacketsOnB P.zero j.1
          (tcpListedTags_BAUGP P.toLocalPacketsOnB P.zero j.1)
          (tcpListedEdges_BAUGP P.toLocalPacketsOnB j.1) Ac cc A1 c1 Bτ cτ)) a‖ ≤ tcpGraphConst)
    (hTG : tcpTG_PLN_BAUGP P eg (tcpModelGraph_BAUGP P.toLocalPacketsOnB P.zero j.1
          (tcpListedTags_BAUGP P.toLocalPacketsOnB P.zero j.1)
          (tcpListedEdges_BAUGP P.toLocalPacketsOnB j.1) Ac cc A1 c1 Bτ cτ)
      (cgpCircleCoord_BAUGP P.toLocalPacketsOnB j.1 ((Set.Finite.mem_toFinset _).mp j.2)) j.1) :
    ContDiff ℝ ∞ (tcpPrunedModel_BPC P.toLocalPacketsOnB P.zero j.1 Ac cc A1 c1 Bτ cτ) ∧
    (∀ a, tcpPrunedModel_BPC P.toLocalPacketsOnB P.zero j.1 Ac cc A1 c1 Bτ cτ a (.inl j) =
      WithLp.toLp 2 (a, 1)) ∧
    (∀ a, ‖fderiv ℝ (tcpPrunedModel_BPC P.toLocalPacketsOnB P.zero j.1 Ac cc A1 c1 Bτ cτ) a‖ ≤
        tcpGraphConst ∧
      ‖fderiv ℝ (fderiv ℝ (tcpPrunedModel_BPC P.toLocalPacketsOnB P.zero j.1 Ac cc A1 c1 Bτ cτ))
        a‖ ≤ tcpGraphConst) ∧
    tcpTG_PLN_BAUGP P eg (tcpPrunedModel_BPC P.toLocalPacketsOnB P.zero j.1 Ac cc A1 c1 Bτ cτ)
      (cgpCircleCoord_BAUGP P.toLocalPacketsOnB j.1 ((Set.Finite.mem_toFinset _).mp j.2)) j.1 ∧
    (∀ a : CGPMarkerIndex_BAUGP P.toLocalPacketsOnB,
      ρ (cgpMarkerCentre_BAUGP P.toLocalPacketsOnB a) ≤ ρ j.1 / 2 → ∀ u v,
      blockMarkerCLM (cgpMarkerTag_BAUGP P.toLocalPacketsOnB P.zero a)
        (fderiv ℝ (tcpPrunedModel_BPC P.toLocalPacketsOnB P.zero j.1 Ac cc A1 c1 Bτ cτ) u v) = 0) ∧
    ∀ u v, blockMarkerCLM (cgpScaleTag_BAUGP P.toLocalPacketsOnB P.zero)
      (fderiv ℝ (tcpPrunedModel_BPC P.toLocalPacketsOnB P.zero j.1 Ac cc A1 c1 Bτ cτ) u v) = 0 := by
  have hsmall : Λ * (1000000 * Δ) ≤ 1 / 4 := by nlinarith
  have hΛ200 : Λ * 200 ≤ 1 / 4 := by nlinarith
  exact tcp05_pruned_explicit_PLN_BAUGP P hΔ hΛ hsmall hΛ200 j _
    (contDiff_tcpModelGraph_BAUGP _ _ _ _ _ _ _ _ _ _ _)
    (fun u => tcpModelGraph_own_BAUGP _ _ _ _ _ _ _ _ _ _ _ j rfl u) hb hTG
    (fun u h => tcpModelGraph_scale_fderiv_GAFS_BAUGP _ _ _ _ _ _ _ _ _ _ _ u h)

end Packets

end DifferentialGeometry.Geometry.Collapse
