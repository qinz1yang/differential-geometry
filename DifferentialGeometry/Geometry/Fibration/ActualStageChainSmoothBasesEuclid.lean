import DifferentialGeometry.Geometry.Fibration.ActualStageChainSmoothBases

/-!
# The one-dimensional stage bases in the model `EuclideanSpace ℝ (Fin 1)` (rows' `𝓡 1`)

Lane C14-REG-CHAIN (by C14-REG-CHAINc), G15. The rows' `EdgeBundle.Base` is a smooth manifold
with model `EuclideanSpace ℝ (Fin 1)` (`𝓡 1`); G11's edge and slim charts are `ℝ`-valued. Here the
chart-form data are re-modelled through a LINEAR ISOMETRY `ℝ ≃ₗᵢ EuclideanSpace ℝ (Fin 1)`
(`oneDimIso_R74`, the singleton orthonormal basis), so balls of the same radius correspond:

* `linearChart_iso_R74` (generic): chart-form data transported through a linear isometry of the
  model space;
* `SmoothStageBasesOn74.edgeChartedSpace1`, `slimChartedSpace1` with
  `edge_isManifold1`, `slim_isManifold1` (`IsManifold (𝓡 1) ∞`, smooth immersed inclusion).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.Topology.Manifold

variable {H E E' : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E'] {ι : Type*}

/-- **Chart-form data through a linear isometry of the model**: `κ' = e ∘ κ`, `φ' = φ ∘ e⁻¹`
satisfy the chart-form hypotheses on the ball of the same radius. -/
theorem linearChart_iso_R74 (W : Set H) (κ : ι → H →L[ℝ] E) (φ : ι → E → H) (O : ι → Set H)
    (r : ℝ) (e : E ≃ₗᵢ[ℝ] E') (hφs : ∀ i, ContDiffOn ℝ ∞ (φ i) (ball 0 r))
    (hφ : ∀ i, ∀ b ∈ ball (0 : E) r, φ i b ∈ W ∩ O i ∧ κ i (φ i b) = b)
    (hκ : ∀ i, ∀ y ∈ W ∩ O i, κ i y ∈ ball (0 : E) r ∧ φ i (κ i y) = y) :
    (∀ i, ContDiffOn ℝ ∞ (φ i ∘ e.symm) (ball 0 r)) ∧
      (∀ i, ∀ b ∈ ball (0 : E') r, (φ i ∘ e.symm) b ∈ W ∩ O i ∧
        (e.toContinuousLinearEquiv.toContinuousLinearMap.comp (κ i)) ((φ i ∘ e.symm) b) = b) ∧
      (∀ i, ∀ y ∈ W ∩ O i,
        (e.toContinuousLinearEquiv.toContinuousLinearMap.comp (κ i)) y ∈ ball (0 : E') r ∧
        (φ i ∘ e.symm) ((e.toContinuousLinearEquiv.toContinuousLinearMap.comp (κ i)) y) = y) := by
  have hb : ∀ b : E', b ∈ ball (0 : E') r → e.symm b ∈ ball (0 : E) r := fun b hb => by
    rw [mem_ball_zero_iff] at hb ⊢
    rwa [LinearIsometryEquiv.norm_map]
  refine ⟨fun i => (hφs i).comp e.symm.contDiff.contDiffOn fun b h => hb b h, fun i b hb' => ?_,
    fun i y hy => ?_⟩
  · obtain ⟨h1, h2⟩ := hφ i (e.symm b) (hb b hb')
    refine ⟨h1, ?_⟩
    change e (κ i (φ i (e.symm b))) = b
    rw [h2, LinearIsometryEquiv.apply_symm_apply]
  · obtain ⟨h1, h2⟩ := hκ i y hy
    refine ⟨?_, ?_⟩
    · change e (κ i y) ∈ ball (0 : E') r
      rw [mem_ball_zero_iff, LinearIsometryEquiv.norm_map, ← mem_ball_zero_iff]
      exact h1
    · change φ i (e.symm (e (κ i y))) = y
      rw [LinearIsometryEquiv.symm_apply_apply, h2]

end DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- The linear isometry `ℝ ≃ₗᵢ EuclideanSpace ℝ (Fin 1)` (singleton orthonormal basis). -/
def oneDimIso_R74 : ℝ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 1) :=
  (OrthonormalBasis.singleton (Fin 1) ℝ).repr

variable {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

namespace SmoothStageBasesOn74

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
  {C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw}

/-- **`W₂` with the rows' model `EuclideanSpace ℝ (Fin 1)`.** -/
@[reducible]
def edgeChartedSpace1 (A : SmoothStageBasesOn74 C) :
    ChartedSpace (EuclideanSpace ℝ (Fin 1)) (C.finalBase_BAS 1) :=
  linearChartedSpace_R74 (C.finalBase_BAS 1) _ _ _ (11 / 2 * Δ)
    (fun _ => isOpen_markedCondition_BPRE _ _ _ _)
    (linearChart_iso_R74 (C.finalBase_BAS 1)
      (fun j => (ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
      (fun j => C.Θ_BAS 1 ∘ A.edgeChart j)
      (fun j => markedCondition_BPRE
        (axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
        (gafEdgeMarker P.toLocalChartFamily P.zero j) (ρ j.1) (Δ)) (11 / 2 * Δ) oneDimIso_R74
      A.charts.edge_smooth A.charts.edge_param A.charts.edge_coord).1
    (linearChart_iso_R74 (C.finalBase_BAS 1)
      (fun j => (ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
      (fun j => C.Θ_BAS 1 ∘ A.edgeChart j)
      (fun j => markedCondition_BPRE
        (axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
        (gafEdgeMarker P.toLocalChartFamily P.zero j) (ρ j.1) (Δ)) (11 / 2 * Δ) oneDimIso_R74
      A.charts.edge_smooth A.charts.edge_param A.charts.edge_coord).2.1
    (linearChart_iso_R74 (C.finalBase_BAS 1)
      (fun j => (ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
      (fun j => C.Θ_BAS 1 ∘ A.edgeChart j)
      (fun j => markedCondition_BPRE
        (axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
        (gafEdgeMarker P.toLocalChartFamily P.zero j) (ρ j.1) (Δ)) (11 / 2 * Δ) oneDimIso_R74
      A.charts.edge_smooth A.charts.edge_param A.charts.edge_coord).2.2
    A.charts.edge_cover

/-- **`W₃` with the rows' model `EuclideanSpace ℝ (Fin 1)`.** -/
@[reducible]
def slimChartedSpace1 (A : SmoothStageBasesOn74 C) :
    ChartedSpace (EuclideanSpace ℝ (Fin 1)) (C.finalBase_BAS 2) :=
  linearChartedSpace_R74 (C.finalBase_BAS 2) _ _ _ (11 / 2 * (10 ^ 5 * Δ))
    (fun _ => isOpen_markedCondition_BPRE _ _ _ _)
    (linearChart_iso_R74 (C.finalBase_BAS 2)
      (fun j => (ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
      (fun j => C.Θ_BAS 2 ∘ A.slimChart j)
      (fun j => markedCondition_BPRE
        (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
        (gafSlimMarker P.toLocalChartFamily P.zero j) (ρ j.1) (10 ^ 5 * Δ))
      (11 / 2 * (10 ^ 5 * Δ)) oneDimIso_R74
      A.charts.slim_smooth A.charts.slim_param A.charts.slim_coord).1
    (linearChart_iso_R74 (C.finalBase_BAS 2)
      (fun j => (ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
      (fun j => C.Θ_BAS 2 ∘ A.slimChart j)
      (fun j => markedCondition_BPRE
        (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
        (gafSlimMarker P.toLocalChartFamily P.zero j) (ρ j.1) (10 ^ 5 * Δ))
      (11 / 2 * (10 ^ 5 * Δ)) oneDimIso_R74
      A.charts.slim_smooth A.charts.slim_param A.charts.slim_coord).2.1
    (linearChart_iso_R74 (C.finalBase_BAS 2)
      (fun j => (ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
      (fun j => C.Θ_BAS 2 ∘ A.slimChart j)
      (fun j => markedCondition_BPRE
        (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
        (gafSlimMarker P.toLocalChartFamily P.zero j) (ρ j.1) (10 ^ 5 * Δ))
      (11 / 2 * (10 ^ 5 * Δ)) oneDimIso_R74
      A.charts.slim_smooth A.charts.slim_param A.charts.slim_coord).2.2
    A.charts.slim_cover

/-- `W₂` is a smooth `𝓡 1`-manifold and its inclusion is a smooth immersion. -/
theorem edge_isManifold1 (A : SmoothStageBasesOn74 C) :
    let _ := A.edgeChartedSpace1
    IsManifold (𝓡 1) ∞ (C.finalBase_BAS 1) ∧
      ContMDiff (𝓡 1) 𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∞
        (Subtype.val : C.finalBase_BAS 1 → _) ∧
      ∀ y, Injective (mfderiv (𝓡 1)
        𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
        (Subtype.val : C.finalBase_BAS 1 → _) y) :=
  ⟨linearIsManifold_R74 _ _ _ _ _ _ _ _ _ _, contMDiff_linearInclusion_R74 _ _ _ _ _ _ _ _ _ _,
    mfderiv_linearInclusion_injective_R74 _ _ _ _ _ _ _ _ _ _⟩

/-- `W₃` is a smooth `𝓡 1`-manifold and its inclusion is a smooth immersion. -/
theorem slim_isManifold1 (A : SmoothStageBasesOn74 C) :
    let _ := A.slimChartedSpace1
    IsManifold (𝓡 1) ∞ (C.finalBase_BAS 2) ∧
      ContMDiff (𝓡 1) 𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∞
        (Subtype.val : C.finalBase_BAS 2 → _) ∧
      ∀ y, Injective (mfderiv (𝓡 1)
        𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
        (Subtype.val : C.finalBase_BAS 2 → _) y) :=
  ⟨linearIsManifold_R74 _ _ _ _ _ _ _ _ _ _, contMDiff_linearInclusion_R74 _ _ _ _ _ _ _ _ _ _,
    mfderiv_linearInclusion_injective_R74 _ _ _ _ _ _ _ _ _ _⟩

end SmoothStageBasesOn74

end DifferentialGeometry.Geometry.Collapse
