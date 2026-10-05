import DifferentialGeometry.Geometry.Fibration.ActualStageChainRow

/-!
# The GAF02 chain assembler and the full CHOICE evidence (review 66, D66-2 / D66-3)

* `Gaf02Chain.ofOutputs` (D66-2): the reusable ASSEMBLER — from given selections and planes with
their
  stage-test conclusions, the packet hypotheses, the numbers and, per stage, a native CFS15 output
  whose
  plane parameter IS the given plane and whose radius is `Σ_jρ ∘ sel_j`, the chain object with
  `.active` slots (`.active O` records "has a native output", not "stage family non-empty", D66-4).
  `ofOutputs_sel`, `ofOutputs_plane`, `ofOutputs_slot`, `ofOutputs_map` (rfl): the assembled
  chain's data
  are the given ones; its smoothing maps are the outputs' ambient nearest maps. The enhanced
  producer feeds
  it `A.plane` and `A`'s forgetful tests (lane C14-GAF8, `Gaf02ChainE`).
* `gaf02_chain_choice_full_GAF8` (D66-3): ONE call of GAF01's shared-moduli row and its CHOICE
(graph
  moduli `C_TCP, C_EGP, C_SGP`) returning, besides `gaf02_chain_choice_GAF8`'s conclusions, the
  whole
  per-stage CHOICE evidence: (OS) `ε_j < 1/(1000(Ω+1))`, `e_j < Σ_j/1000`, `2e_j < 1/(48Ω)`,
  `ε_j < 1/10`,
  `ε_j < α_j`, the stage budgets (value, derivative, `ε_j(L₀ + H) + H < 1/2`), `ν + e_j ≤ 1/(48Ω)`,
  and the
  one-sheet budget (SN) — `Ω = max 1 (max C_TCP (max C_EGP C_SGP))`. Nothing is re-chosen after the
  family.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricN_GAF8A
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedN_GAF8A
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricC_GAF8A
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a
/-- **The GAF02 chain assembler** (review 66, D66-2): the chain object built from given selections
`sel` and planes `plane` with their stage-test conclusions and, per stage, a native CFS15 output
whose
plane slot is `plane st` and whose radius is `Σ_st ρ ∘ sel st`; every slot is `.active` (D66-4). -/
def Gaf02Chain.ofOutputs {P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc
    Lmax τ γ δ
    εr e T V} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (hstd : 0 ≤ Λ ∧ 1 ≤ Δ ∧ μ ≤ 1 / 100 ∧ τ ≤ 1 / 100 ∧ 1000000 * Δ * Λ < 1 / 100000 ∧
    4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax ∧ e < 1 / 40 ∧ 1600 * (1000000 * Δ) ≤ T ∧
    0 ≤ σs ∧ σs ≤ 1 / 100 ∧ σc ∈ Icc (0 : ℝ) 1 ∧ γc ∈ Icc (0 : ℝ) 1 ∧ εr ∈ Icc (0 : ℝ) 1)
    (hnum : (∀ j, 0 < Ξ j ∧ 0 < S j ∧ 128 * (Ξ j)⁻¹ * S j ≤ 1 / 5 ∧ 0 ≤ eg j) ∧
    5 / 3 * Ξ 0 * S 0 < c 0 ∧ c 0 ≤ 1 / 512 ∧
    (5 / 3 * Ξ 0 * S 0 * gafCutoffConstant * gafDerivativeBound +
        Ξ 0 * gafDerivativeBound + eg 0) < c 0 ∧
    c 0 ≤ 4 * gafKappa / 5 ∧ c 0 ≤ 3 * S 1 / 10 ∧
    (c 0 + (5 / 3 * Ξ 1 * S 1 + (1 + Ξ 1) * c 0)) < c 1 ∧ c 1 ≤ 1 / 512 ∧
    ((5 / 3 * Ξ 1 * S 1 + (1 + Ξ 1) * c 0) * gafCutoffConstant * (gafDerivativeBound + c 0) +
        Ξ 1 * (gafDerivativeBound + c 0) + eg 1 + 2 * c 0) < c 1 ∧
    c 1 ≤ 4 * gafKappa / 5 ∧ c 1 ≤ 3 * S 2 / 10 ∧
    (c 1 + (5 / 3 * Ξ 2 * S 2 + (1 + Ξ 2) * c 1)) < c 2 ∧ c 2 ≤ 1 / 512 ∧
    ((5 / 3 * Ξ 2 * S 2 + (1 + Ξ 2) * c 1) * gafCutoffConstant * (gafDerivativeBound + c 1) +
        Ξ 2 * (gafDerivativeBound + c 1) + eg 2 + 2 * c 1) < c 2)
    (sel : Fin 3 → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X)
    (hsel : ∀ st, ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero st,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero st) (sel st
          x) = x)
    (plane : Fin 3 → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
    (t0 : (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
        Module.finrank ℝ (plane 0 x) = gafStageDim 0 ∧
          plane 0 x ≤ gafStageQ P.toLocalChartFamily P.zero 0) ∧
      (∀ sel' : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
        (∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 0,
          cgpProjMap P.toLocalChartFamily P.zero
            (gafStageTags P.toLocalChartFamily P.zero 0) (sel' x) = x) →
        ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
          hausdorffEDist (gafCloudEnlarged P.toLocalChartFamily P.zero 0 ∩
              ball x (S 0 * ρ (sel' x) / Γ 0))
            ((AffineSubspace.mk' x (plane 0 x) :
                Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
              ball x (S 0 * ρ (sel' x) / Γ 0)) ≤ ENNReal.ofReal (Γ 0 * (S 0 * ρ (sel' x)))) ∧
      (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
        ∃ i : P.toLocalChartFamily.circle.finite_centres.toFinset,
        ∀ q, cgpGlobalMap P.toLocalChartFamily P.zero q = x →
        let Pq := (plane 0 x).orthogonalProjectionOnto.comp ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
          (cgpGlobalMap P.toLocalChartFamily P.zero) q)
        Function.Surjective Pq ∧
        (∀ v, ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) q v -
            (Pq v : BlockSpace _)‖ ≤ eg 0 * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
        (∀ v, (∀ k, Pq k = 0 → g.inner q v k = 0) →
          1 / 2 * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v) ≤ ‖Pq v‖) ∧
        ∀ v, ‖Pq v‖ ≤ 3 * tcpGraphConst * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
      (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
        plane 0 x ≤ LinearMap.ker ((blockMarkerCLM
          (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpScaleTag P.toLocalChartFamily P.zero) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ)) ∧
      (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0, ∀ q,
        cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0) q =
          x →
        ∀ a : CGPMarkerIndex P.toLocalChartFamily,
          ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 5 →
          plane 0 x ≤ LinearMap.ker ((blockMarkerCLM
            (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
            (cgpMarkerTag P.toLocalChartFamily P.zero a) :
              BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ)))
    (t1 : (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 1,
        Module.finrank ℝ (plane 1 x) = gafStageDim 1 ∧
          plane 1 x ≤ gafStageQ P.toLocalChartFamily P.zero 1) ∧
      (∀ sel' : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
        (∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 1,
          cgpProjMap P.toLocalChartFamily P.zero
            (gafStageTags P.toLocalChartFamily P.zero 1) (sel' x) = x) →
        ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 1,
          hausdorffEDist (gafCloudEnlarged P.toLocalChartFamily P.zero 1 ∩
              ball x (S 1 * ρ (sel' x) / Γ 1))
            ((AffineSubspace.mk' x (plane 1 x) :
                Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
              ball x (S 1 * ρ (sel' x) / Γ 1)) ≤ ENNReal.ofReal (Γ 1 * (S 1 * ρ (sel' x)))) ∧
      (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 1, ∃ i ∈ P.edge.centres,
        ∀ q : X,
        cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) q = x →
          (∀ w : TangentSpace 𝓘(ℝ, E3) q, (ρ i)⁻¹ ^ 2 * g.inner q w w = 1 →
            ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                (cgpQ2Tags P.toLocalChartFamily P.zero)) q w -
              (plane 1 x).starProjection
                ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                  (cgpQ2Tags P.toLocalChartFamily P.zero)) q w)‖ < eg 1) ∧
          (∀ w : TangentSpace 𝓘(ℝ, E3) q, (ρ i)⁻¹ ^ 2 * g.inner q w w = 1 →
            ‖(plane 1 x).starProjection
                ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                  (cgpQ2Tags P.toLocalChartFamily P.zero)) q w)‖ ≤ 3 * egpGraphConst) ∧
          (∃ w₀ : TangentSpace 𝓘(ℝ, E3) q, (ρ i)⁻¹ ^ 2 * g.inner q w₀ w₀ = 1 ∧
            1 / 2 ≤ ‖(plane 1 x).starProjection ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3)
                  (cgpProjMap P.toLocalChartFamily P.zero
                    (cgpQ2Tags P.toLocalChartFamily P.zero)) q w₀)‖) ∧
          (∀ k ∈ plane 1 x, ∃ w : TangentSpace 𝓘(ℝ, E3) q,
              (plane 1 x).starProjection
                ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                  (cgpQ2Tags P.toLocalChartFamily P.zero)) q w) = k)) ∧
      (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 1, ∀ q,
        cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 1) q =
          x →
        ∀ a : CGPMarkerIndex P.toLocalChartFamily,
          ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 5 →
          plane 1 x ≤ LinearMap.ker ((blockMarkerCLM
            (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
            (cgpMarkerTag P.toLocalChartFamily P.zero a) :
              BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ)))
    (t2 : (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2,
        Module.finrank ℝ (plane 2 x) = gafStageDim 2 ∧
          plane 2 x ≤ gafStageQ P.toLocalChartFamily P.zero 2) ∧
      (∀ sel' : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
        (∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 2,
          cgpProjMap P.toLocalChartFamily P.zero
            (gafStageTags P.toLocalChartFamily P.zero 2) (sel' x) = x) →
        ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2,
          hausdorffEDist (gafCloudEnlarged P.toLocalChartFamily P.zero 2 ∩
              ball x (S 2 * ρ (sel' x) / Γ 2))
            ((AffineSubspace.mk' x (plane 2 x) :
                Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
              ball x (S 2 * ρ (sel' x) / Γ 2)) ≤ ENNReal.ofReal (Γ 2 * (S 2 * ρ (sel' x)))) ∧
      (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2,
        ∃ i : P.toLocalChartFamily.slim.finite_centres.toFinset,
        ∀ q, cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) q =
          x →
        let Pq := (plane 2 x).orthogonalProjectionOnto.comp ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
          (cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero)) q)
        Function.Surjective Pq ∧
        (∀ v, ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
            (cgpQ3Tags P.toLocalChartFamily P.zero)) q v - (Pq v : BlockSpace _)‖ ≤
          eg 2 * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
        (∀ v, (∀ k, Pq k = 0 → g.inner q v k = 0) →
          1 / 2 * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v) ≤ ‖Pq v‖) ∧
        ∀ v, ‖Pq v‖ ≤ 3 * sgpGraphBound * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
      (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2, ∀ q,
        cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 2) q =
          x →
        ∀ a : CGPMarkerIndex P.toLocalChartFamily,
          ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 5 →
          plane 2 x ≤ LinearMap.ker ((blockMarkerCLM
            (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
            (cgpMarkerTag P.toLocalChartFamily P.zero a) :
              BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ)))
    (O : ∀ st, Cfs15StageOutput (gafStageDim st) Kj (Ξ st) (cw st) (gafCloud P.toLocalChartFamily
        P.zero st)
      (gafCloudEnlarged P.toLocalChartFamily P.zero st) (fun x => S st * ρ (sel st x)) (plane st)) :
    Gaf02Chain P Kj Ξ Γ S eg c cw :=
  ⟨hstd, hnum, sel, hsel, plane, t0, t1, t2, fun st => .active (O st)⟩

/-- The assembled chain's selections, planes and slots are the given ones; its smoothing maps are
the
outputs' ambient nearest maps `a_j = ι_j ∘ p_j`. -/
theorem Gaf02Chain.ofOutputs_data {P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s'
    ε γc βc
    Lmax τ γ δ εr e T V} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (hstd : 0 ≤ Λ ∧ 1 ≤ Δ ∧ μ ≤ 1 / 100 ∧ τ ≤ 1 / 100 ∧ 1000000 * Δ * Λ < 1 / 100000 ∧
    4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax ∧ e < 1 / 40 ∧ 1600 * (1000000 * Δ) ≤ T ∧
    0 ≤ σs ∧ σs ≤ 1 / 100 ∧ σc ∈ Icc (0 : ℝ) 1 ∧ γc ∈ Icc (0 : ℝ) 1 ∧ εr ∈ Icc (0 : ℝ) 1)
    (hnum : (∀ j, 0 < Ξ j ∧ 0 < S j ∧ 128 * (Ξ j)⁻¹ * S j ≤ 1 / 5 ∧ 0 ≤ eg j) ∧
    5 / 3 * Ξ 0 * S 0 < c 0 ∧ c 0 ≤ 1 / 512 ∧
    (5 / 3 * Ξ 0 * S 0 * gafCutoffConstant * gafDerivativeBound +
        Ξ 0 * gafDerivativeBound + eg 0) < c 0 ∧
    c 0 ≤ 4 * gafKappa / 5 ∧ c 0 ≤ 3 * S 1 / 10 ∧
    (c 0 + (5 / 3 * Ξ 1 * S 1 + (1 + Ξ 1) * c 0)) < c 1 ∧ c 1 ≤ 1 / 512 ∧
    ((5 / 3 * Ξ 1 * S 1 + (1 + Ξ 1) * c 0) * gafCutoffConstant * (gafDerivativeBound + c 0) +
        Ξ 1 * (gafDerivativeBound + c 0) + eg 1 + 2 * c 0) < c 1 ∧
    c 1 ≤ 4 * gafKappa / 5 ∧ c 1 ≤ 3 * S 2 / 10 ∧
    (c 1 + (5 / 3 * Ξ 2 * S 2 + (1 + Ξ 2) * c 1)) < c 2 ∧ c 2 ≤ 1 / 512 ∧
    ((5 / 3 * Ξ 2 * S 2 + (1 + Ξ 2) * c 1) * gafCutoffConstant * (gafDerivativeBound + c 1) +
        Ξ 2 * (gafDerivativeBound + c 1) + eg 2 + 2 * c 1) < c 2)
    (sel : Fin 3 → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X)
    (hsel : ∀ st, ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero st,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero st) (sel st
          x) = x)
    (plane : Fin 3 → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
    (t0 : (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
        Module.finrank ℝ (plane 0 x) = gafStageDim 0 ∧
          plane 0 x ≤ gafStageQ P.toLocalChartFamily P.zero 0) ∧
      (∀ sel' : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
        (∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 0,
          cgpProjMap P.toLocalChartFamily P.zero
            (gafStageTags P.toLocalChartFamily P.zero 0) (sel' x) = x) →
        ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
          hausdorffEDist (gafCloudEnlarged P.toLocalChartFamily P.zero 0 ∩
              ball x (S 0 * ρ (sel' x) / Γ 0))
            ((AffineSubspace.mk' x (plane 0 x) :
                Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
              ball x (S 0 * ρ (sel' x) / Γ 0)) ≤ ENNReal.ofReal (Γ 0 * (S 0 * ρ (sel' x)))) ∧
      (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
        ∃ i : P.toLocalChartFamily.circle.finite_centres.toFinset,
        ∀ q, cgpGlobalMap P.toLocalChartFamily P.zero q = x →
        let Pq := (plane 0 x).orthogonalProjectionOnto.comp ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
          (cgpGlobalMap P.toLocalChartFamily P.zero) q)
        Function.Surjective Pq ∧
        (∀ v, ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) q v -
            (Pq v : BlockSpace _)‖ ≤ eg 0 * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
        (∀ v, (∀ k, Pq k = 0 → g.inner q v k = 0) →
          1 / 2 * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v) ≤ ‖Pq v‖) ∧
        ∀ v, ‖Pq v‖ ≤ 3 * tcpGraphConst * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
      (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
        plane 0 x ≤ LinearMap.ker ((blockMarkerCLM
          (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpScaleTag P.toLocalChartFamily P.zero) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ)) ∧
      (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0, ∀ q,
        cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0) q =
          x →
        ∀ a : CGPMarkerIndex P.toLocalChartFamily,
          ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 5 →
          plane 0 x ≤ LinearMap.ker ((blockMarkerCLM
            (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
            (cgpMarkerTag P.toLocalChartFamily P.zero a) :
              BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ)))
    (t1 : (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 1,
        Module.finrank ℝ (plane 1 x) = gafStageDim 1 ∧
          plane 1 x ≤ gafStageQ P.toLocalChartFamily P.zero 1) ∧
      (∀ sel' : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
        (∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 1,
          cgpProjMap P.toLocalChartFamily P.zero
            (gafStageTags P.toLocalChartFamily P.zero 1) (sel' x) = x) →
        ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 1,
          hausdorffEDist (gafCloudEnlarged P.toLocalChartFamily P.zero 1 ∩
              ball x (S 1 * ρ (sel' x) / Γ 1))
            ((AffineSubspace.mk' x (plane 1 x) :
                Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
              ball x (S 1 * ρ (sel' x) / Γ 1)) ≤ ENNReal.ofReal (Γ 1 * (S 1 * ρ (sel' x)))) ∧
      (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 1, ∃ i ∈ P.edge.centres,
        ∀ q : X,
        cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) q = x →
          (∀ w : TangentSpace 𝓘(ℝ, E3) q, (ρ i)⁻¹ ^ 2 * g.inner q w w = 1 →
            ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                (cgpQ2Tags P.toLocalChartFamily P.zero)) q w -
              (plane 1 x).starProjection
                ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                  (cgpQ2Tags P.toLocalChartFamily P.zero)) q w)‖ < eg 1) ∧
          (∀ w : TangentSpace 𝓘(ℝ, E3) q, (ρ i)⁻¹ ^ 2 * g.inner q w w = 1 →
            ‖(plane 1 x).starProjection
                ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                  (cgpQ2Tags P.toLocalChartFamily P.zero)) q w)‖ ≤ 3 * egpGraphConst) ∧
          (∃ w₀ : TangentSpace 𝓘(ℝ, E3) q, (ρ i)⁻¹ ^ 2 * g.inner q w₀ w₀ = 1 ∧
            1 / 2 ≤ ‖(plane 1 x).starProjection ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3)
                  (cgpProjMap P.toLocalChartFamily P.zero
                    (cgpQ2Tags P.toLocalChartFamily P.zero)) q w₀)‖) ∧
          (∀ k ∈ plane 1 x, ∃ w : TangentSpace 𝓘(ℝ, E3) q,
              (plane 1 x).starProjection
                ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                  (cgpQ2Tags P.toLocalChartFamily P.zero)) q w) = k)) ∧
      (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 1, ∀ q,
        cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 1) q =
          x →
        ∀ a : CGPMarkerIndex P.toLocalChartFamily,
          ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 5 →
          plane 1 x ≤ LinearMap.ker ((blockMarkerCLM
            (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
            (cgpMarkerTag P.toLocalChartFamily P.zero a) :
              BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ)))
    (t2 : (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2,
        Module.finrank ℝ (plane 2 x) = gafStageDim 2 ∧
          plane 2 x ≤ gafStageQ P.toLocalChartFamily P.zero 2) ∧
      (∀ sel' : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
        (∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 2,
          cgpProjMap P.toLocalChartFamily P.zero
            (gafStageTags P.toLocalChartFamily P.zero 2) (sel' x) = x) →
        ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2,
          hausdorffEDist (gafCloudEnlarged P.toLocalChartFamily P.zero 2 ∩
              ball x (S 2 * ρ (sel' x) / Γ 2))
            ((AffineSubspace.mk' x (plane 2 x) :
                Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
              ball x (S 2 * ρ (sel' x) / Γ 2)) ≤ ENNReal.ofReal (Γ 2 * (S 2 * ρ (sel' x)))) ∧
      (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2,
        ∃ i : P.toLocalChartFamily.slim.finite_centres.toFinset,
        ∀ q, cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) q =
          x →
        let Pq := (plane 2 x).orthogonalProjectionOnto.comp ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
          (cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero)) q)
        Function.Surjective Pq ∧
        (∀ v, ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
            (cgpQ3Tags P.toLocalChartFamily P.zero)) q v - (Pq v : BlockSpace _)‖ ≤
          eg 2 * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
        (∀ v, (∀ k, Pq k = 0 → g.inner q v k = 0) →
          1 / 2 * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v) ≤ ‖Pq v‖) ∧
        ∀ v, ‖Pq v‖ ≤ 3 * sgpGraphBound * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
      (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2, ∀ q,
        cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 2) q =
          x →
        ∀ a : CGPMarkerIndex P.toLocalChartFamily,
          ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 5 →
          plane 2 x ≤ LinearMap.ker ((blockMarkerCLM
            (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
            (cgpMarkerTag P.toLocalChartFamily P.zero a) :
              BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ)))
    (O : ∀ st, Cfs15StageOutput (gafStageDim st) Kj (Ξ st) (cw st) (gafCloud P.toLocalChartFamily
        P.zero st)
      (gafCloudEnlarged P.toLocalChartFamily P.zero st) (fun x => S st * ρ (sel st x)) (plane st)) :
    (Gaf02Chain.ofOutputs hstd hnum sel hsel plane t0 t1 t2 O).sel = sel ∧
      (Gaf02Chain.ofOutputs hstd hnum sel hsel plane t0 t1 t2 O).plane = plane ∧
      (∀ st, (Gaf02Chain.ofOutputs hstd hnum sel hsel plane t0 t1 t2 O).slot st = .active (O st)) ∧
      ∀ st, ((Gaf02Chain.ofOutputs hstd hnum sel hsel plane t0 t1 t2 O).slot st).map = (O
          st).ambient :=
  ⟨rfl, rfl, fun _ => rfl, fun _ => rfl⟩

/-- **GAF01's moduli and the FULL CHOICE evidence in the chain's form** (D66-3): GAF01's shared
moduli `θ, Ξ` at jet order
`Kj` and a CHOICE `c, Γ, Σ, e` (graph moduli `C_TCP, C_EGP, C_SGP`, `c₃ < c_adj`) with the stage
tests' parameter ranges (`Γ_j < 1`, `Σ_j < Γ_j/200`, `Σ_j < Γ_j³/(100C_j)`,
`e_j < min(1/100, Γ_jΣ_j/100,
Σ_j/1000)`), CFS15's modulus and interior condition at `Γ_j`, and the kernel's numbers
(`128Ξ⁻¹Σ ≤ 1/5`, `(5/3)ΞΣ < c₁`, the derivative budgets, `c_j ≤ 4κ/5`, `c_j ≤ 3Σ_{j+1}/10`, …). -/
theorem gaf02_chain_choice_full_GAF8 (Kj : ℕ) {cadj : ℝ} (hcadj : 0 < cadj) :
    ∃ (θ : Fin 3 → ℝ) (Ξ : Fin 3 → ℝ → ℝ) (c Γ S eg : Fin 3 → ℝ),
      (∀ j, 0 < θ j ∧ 0 < Γ j ∧ Γ j < θ j ∧ Γ j < 1 ∧ 0 < Ξ j (Γ j) ∧
        Cfs15ModulusAtV2 (gafStageDim j) Kj (5 / 3) (Ξ j) (Γ j) ∧
        Γ j * ((80 * (5 / 3) + 31) * (Ξ j (Γ j))⁻¹ + 2) < 1 ∧ 0 < S j ∧
        S j < Ξ j (Γ j) / 10000 ∧ S j < Γ j / 200 ∧ 0 < eg j ∧ eg j < 1 / 100 ∧
        eg j < Γ j * S j / 100 ∧ eg j < S j / 1000 ∧ 0 < c j) ∧
      S 0 < Γ 0 ^ 3 / (100 * tcpGraphConst) ∧ S 1 < Γ 1 ^ 3 / (100 * egpGraphConst) ∧
      S 2 < Γ 2 ^ 3 / (100 * sgpGraphBound) ∧ c 0 ≤ c 1 ∧ c 1 ≤ c 2 ∧ c 2 < cadj ∧
      (∀ j, Ξ j (Γ j) < 1 / (1000 * (max 1 (max tcpGraphConst (max egpGraphConst sgpGraphBound)) +
          1)) ∧ eg j < S j / 1000 ∧
        2 * eg j < 1 / (48 * (max 1 (max tcpGraphConst (max egpGraphConst sgpGraphBound)))) ∧ Ξ j
            (Γ j) < 1 / 10 ∧
        Ξ j (Γ j) < min (c j / (16 * (1 + gafCutoffConstant) * (1 + gafDerivativeBound)))
          (1 / 2 / (8 * (1 + gafDerivativeBound))) ∧
        (∀ E H ν σ : ℝ, 0 ≤ E → E ≤ min (3 * S j / 10) (min (min (c j / (16 * (1 +
            gafCutoffConstant) * (1 + gafDerivativeBound)))
          (1 / 2 / (8 * (1 + gafDerivativeBound)))) 1) → 0 ≤ H →
          H ≤ min (3 * S j / 10) (min (min (c j / (16 * (1 + gafCutoffConstant) * (1 +
              gafDerivativeBound)))
          (1 / 2 / (8 * (1 + gafDerivativeBound)))) 1) → ν ≤ Γ j → σ ≤ 1 / 2 →
          let a := (5 / 3 : ℝ) * Ξ j (Γ j) * σ + (1 + Ξ j (Γ j)) * E
          E + a < c j ∧ a * gafCutoffConstant * (gafDerivativeBound + H) +
              Ξ j (Γ j) * (gafDerivativeBound + H) + ν + 2 * H < c j ∧
            Ξ j (Γ j) * (gafDerivativeBound + H) + H < 1 / 2) ∧
        (∀ ν : ℝ, ν ≤ eg j → ν + eg j ≤ 1 / (48 * (max 1 (max tcpGraphConst (max egpGraphConst
            sgpGraphBound))))) ∧
        ∀ R rx : ℝ, 0 < R → 9 / 20 * S j * R ≤ rx →
          (2 * eg j + 25 / 12 * (1 + max 1 (max tcpGraphConst (max egpGraphConst sgpGraphBound))) *
              Ξ j (Γ j) * S j) * R <
              S j * R / 100 ∧
            S j * R / 100 < rx / 4 ∧ Ξ j (Γ j) < 1 / (2 * (max 1 (max tcpGraphConst (max
                egpGraphConst sgpGraphBound))))) ∧
      (∀ j, 0 < Ξ j (Γ j) ∧ 0 < S j ∧ 128 * (Ξ j (Γ j))⁻¹ * S j ≤ 1 / 5 ∧ 0 ≤ eg j) ∧
    5 / 3 * Ξ 0 (Γ 0) * S 0 < c 0 ∧ c 0 ≤ 1 / 512 ∧
    (5 / 3 * Ξ 0 (Γ 0) * S 0 * gafCutoffConstant * gafDerivativeBound +
        Ξ 0 (Γ 0) * gafDerivativeBound + eg 0) < c 0 ∧
    c 0 ≤ 4 * gafKappa / 5 ∧ c 0 ≤ 3 * S 1 / 10 ∧
    (c 0 + (5 / 3 * Ξ 1 (Γ 1) * S 1 + (1 + Ξ 1 (Γ 1)) * c 0)) < c 1 ∧ c 1 ≤ 1 / 512 ∧
    ((5 / 3 * Ξ 1 (Γ 1) * S 1 + (1 + Ξ 1 (Γ 1)) * c 0) * gafCutoffConstant * (gafDerivativeBound +
        c 0) +
        Ξ 1 (Γ 1) * (gafDerivativeBound + c 0) + eg 1 + 2 * c 0) < c 1 ∧
    c 1 ≤ 4 * gafKappa / 5 ∧ c 1 ≤ 3 * S 2 / 10 ∧
    (c 1 + (5 / 3 * Ξ 2 (Γ 2) * S 2 + (1 + Ξ 2 (Γ 2)) * c 1)) < c 2 ∧ c 2 ≤ 1 / 512 ∧
    ((5 / 3 * Ξ 2 (Γ 2) * S 2 + (1 + Ξ 2 (Γ 2)) * c 1) * gafCutoffConstant * (gafDerivativeBound +
        c 1) +
        Ξ 2 (Γ 2) * (gafDerivativeBound + c 1) + eg 2 + 2 * c 1) < c 2 := by
  obtain ⟨θ, Ξ, hnear, hchoice⟩ := gaf01_row_nearest_shared_GAFS4 Kj
  have hCg : ∀ j, 0 < (![tcpGraphConst, egpGraphConst, sgpGraphBound] : Fin 3 → ℝ) j := by
    intro j
    fin_cases j
    · exact lt_of_lt_of_le one_pos one_le_tcpGraphConst
    · exact egpGraphConst_pos_KC4
    · exact sgpGraphBound_pos_GAF8
  obtain ⟨c, Γ, S, eg, hA, hB, hC, hj⟩ := hchoice _ hCg cadj hcadj
  obtain ⟨hθΓ₀, hc₀, hc1₀, hΓ₀, hΓc₀, -, -, -, hS₀, hS2₀, hSΞ₀, hSΓ₀, hSC₀, he₀, he1₀, heΓ₀, heS₀,
      -⟩ := (hj 0).1
  obtain ⟨hθΓ₁, hc₁, hc1₁, hΓ₁, hΓc₁, -, -, -, hS₁, hS2₁, hSΞ₁, hSΓ₁, hSC₁, he₁, he1₁, heΓ₁, heS₁,
      -⟩ := (hj 1).1
  obtain ⟨hθΓ₂, hc₂, hc1₂, hΓ₂, hΓc₂, -, -, -, hS₂, hS2₂, hSΞ₂, hSΓ₂, hSC₂, he₂, he1₂, heΓ₂, heS₂,
      -⟩ := (hj 2).1
  have hν₀ : eg 0 ≤ Γ 0 := by
    have h' : Γ 0 * S 0 ≤ Γ 0 * 100 := mul_le_mul_of_nonneg_left (by linarith only [hS2₀])
      hΓ₀.le
    linarith only [h', heΓ₀]
  have hν₁ : eg 1 ≤ Γ 1 := by
    have h' : Γ 1 * S 1 ≤ Γ 1 * 100 := mul_le_mul_of_nonneg_left (by linarith only [hS2₁])
      hΓ₁.le
    linarith only [h', heΓ₁]
  have hν₂ : eg 2 ≤ Γ 2 := by
    have h' : Γ 2 * S 2 ≤ Γ 2 * 100 := mul_le_mul_of_nonneg_left (by linarith only [hS2₂])
      hΓ₂.le
    linarith only [h', heΓ₂]
  have hΞpos : ∀ j, 0 < Ξ j (Γ j) := fun j =>
    ((hnear j).2.2 (Γ j) (hj j).1.2.2.2.1 (hj j).1.1).1
  have hmo : ∀ j, 128 * (Ξ j (Γ j))⁻¹ * S j ≤ 1 / 5 := fun j => by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hSΞ, -⟩ := (hj j).1
    have hΞj := hΞpos j
    have h1 : 128 * (Ξ j (Γ j))⁻¹ * S j ≤ 128 * (Ξ j (Γ j))⁻¹ * (Ξ j (Γ j) / 10000) :=
      mul_le_mul_of_nonneg_left hSΞ.le (mul_nonneg (by norm_num) (inv_nonneg.mpr hΞj.le))
    have h2 : 128 * (Ξ j (Γ j))⁻¹ * (Ξ j (Γ j) / 10000) = 128 / 10000 := by
      rw [show 128 * (Ξ j (Γ j))⁻¹ * (Ξ j (Γ j) / 10000) =
        128 / 10000 * ((Ξ j (Γ j))⁻¹ * Ξ j (Γ j)) by ring, inv_mul_cancel₀ hΞj.ne', mul_one]
    linarith only [h1, h2]
  have hb0 : 0 < 16 * (1 + gafCutoffConstant) * (1 + gafDerivativeBound) :=
    mul_pos (mul_pos (by norm_num) (by linarith only [gafCutoffConstant_nonneg]))
      (by linarith only [one_le_gafDerivativeBound])
  have hb1 : 0 < 8 * (1 + gafDerivativeBound) :=
    mul_pos (by norm_num) (by linarith only [one_le_gafDerivativeBound])
  have ht₀ : (0 : ℝ) ≤ min (3 * S 0 / 10) (min (min (c 0 / (16 * (1 + gafCutoffConstant) * (1 +
      gafDerivativeBound)))
      ((1 / 2) / (8 * (1 + gafDerivativeBound)))) 1) :=
    le_min (by linarith only [hS₀]) (le_min (le_min (div_nonneg hc₀.le hb0.le) (div_nonneg (by
        norm_num) hb1.le))
      zero_le_one)
  have k₀ := (hj 0).2.1 0 0 (eg 0) (S 0) le_rfl ht₀ le_rfl ht₀ hν₀ hS2₀.le
  have k₀v := k₀.1
  have k₀d := k₀.2.1
  simp only [mul_zero, add_zero, zero_add] at k₀v k₀d
  have k₁ := (hj 1).2.1 (c 0) (c 0) (eg 1) (S 1) hc₀.le hC.2.1 hc₀.le hC.2.1 hν₁ hS2₁.le
  have k₂ := (hj 2).2.1 (c 1) (c 1) (eg 2) (S 2) hc₁.le hB.2.1 hc₁.le hB.2.1 hν₂ hS2₂.le
  have hnum : (∀ j, 0 < Ξ j (Γ j) ∧ 0 < S j ∧ 128 * (Ξ j (Γ j))⁻¹ * S j ≤ 1 / 5 ∧ 0 ≤ eg j) ∧
    5 / 3 * Ξ 0 (Γ 0) * S 0 < c 0 ∧ c 0 ≤ 1 / 512 ∧
    (5 / 3 * Ξ 0 (Γ 0) * S 0 * gafCutoffConstant * gafDerivativeBound +
        Ξ 0 (Γ 0) * gafDerivativeBound + eg 0) < c 0 ∧
    c 0 ≤ 4 * gafKappa / 5 ∧ c 0 ≤ 3 * S 1 / 10 ∧
    (c 0 + (5 / 3 * Ξ 1 (Γ 1) * S 1 + (1 + Ξ 1 (Γ 1)) * c 0)) < c 1 ∧ c 1 ≤ 1 / 512 ∧
    ((5 / 3 * Ξ 1 (Γ 1) * S 1 + (1 + Ξ 1 (Γ 1)) * c 0) * gafCutoffConstant * (gafDerivativeBound +
        c 0) +
        Ξ 1 (Γ 1) * (gafDerivativeBound + c 0) + eg 1 + 2 * c 0) < c 1 ∧
    c 1 ≤ 4 * gafKappa / 5 ∧ c 1 ≤ 3 * S 2 / 10 ∧
    (c 1 + (5 / 3 * Ξ 2 (Γ 2) * S 2 + (1 + Ξ 2 (Γ 2)) * c 1)) < c 2 ∧ c 2 ≤ 1 / 512 ∧
    ((5 / 3 * Ξ 2 (Γ 2) * S 2 + (1 + Ξ 2 (Γ 2)) * c 1) * gafCutoffConstant * (gafDerivativeBound +
        c 1) +
        Ξ 2 (Γ 2) * (gafDerivativeBound + c 1) + eg 2 + 2 * c 1) < c 2 :=
    ⟨fun j => ⟨hΞpos j, (hj j).1.2.2.2.2.2.2.2.2.1, hmo j, (hj j).1.2.2.2.2.2.2.2.2.2.2.2.2.2.1.le⟩,
      k₀v, hC.2.2.2.2, k₀d, hC.2.2.1, hC.2.1.trans (min_le_left _ _), k₁.1, hB.2.2.2.2, k₁.2.1,
      hB.2.2.1, hB.2.1.trans (min_le_left _ _), k₂.1, hA.2.2.le, k₂.2.1⟩
  refine ⟨θ, Ξ, c, Γ, S, eg, fun j => ?_, hSC₀, hSC₁, hSC₂, hC.1, hB.1, hA.1, fun j => ?_, hnum⟩
  · obtain ⟨hθΓ, hcj, hcj1, hΓ, hΓc, -, -, -, hS, -, hSΞ, hSΓ, -, he, he1, heΓ, heS, -⟩ := (hj j).1
    obtain ⟨hΞ, -, hat, hint, -⟩ := (hnear j).2.2 (Γ j) hΓ hθΓ
    exact ⟨(hnear j).1, hΓ, hθΓ, by linarith only [hΓc, hcj1], hΞ, hat, hint, hS, hSΞ, hSΓ, he, he1,
      heΓ, heS, hcj⟩
  · obtain ⟨-, -, -, -, -, h10, hα, hΩ, -, -, -, -, -, -, -, -, heS, h48⟩ := (hj j).1
    exact ⟨hΩ, heS, h48, h10, hα, (hj j).2.1, (hj j).2.2.1, (hj j).2.2.2⟩

end DifferentialGeometry.Geometry.Collapse
