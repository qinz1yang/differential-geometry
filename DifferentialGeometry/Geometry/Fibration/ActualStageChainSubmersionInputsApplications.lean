import DifferentialGeometry.Geometry.Fibration.ActualStageChainSubmersionInputs

/-!
# Consumers of the stage-submersion inputs (c1)–(c4)

* `surjective_of_rank_le_id_BASP`: (c1) on `ℝ²` with `Tm = ⊤` and identities.
* `Cfs15StageOutput.ambient_injOn_tangent_BASP`: (c2)'s coframe makes `u` injective on `Tm` (the
  form the stage-submersion assembly feeds to (c1)).
* `Gaf02Chain.stageMap_mfderiv_eq_BASP`: (c4b) at the level of manifold derivatives: at a plateau
  point of an active stage, `D f_st(p) = D(π_Q ∘ a ∘ π_Q ∘ g_st)(p)`.
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

/-- (c1) on `ℝ²`: identities through the whole plane are onto. -/
theorem surjective_of_rank_le_id_BASP :
    Surjective ((LinearMap.id : ℝ² →ₗ[ℝ] ℝ²) ∘ₗ (LinearMap.id : ℝ² →ₗ[ℝ] ℝ²) ∘ₗ
      (LinearMap.id : ℝ² →ₗ[ℝ] ℝ²)) := by
  refine surjective_of_rank_le_BAS LinearMap.id LinearMap.id ⊤ le_top LinearMap.id
    (fun a _ b _ h => h) (finrank_top ℝ ℝ²) ?_
  rw [LinearMap.id_comp, LinearMap.range_id, finrank_top]

/-- **The retained coordinate is injective on the ambient tangent plane** ((c2) with `ε/3 < m`). -/
theorem Cfs15StageOutput.ambient_injOn_tangent_BASP {H E : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k K : ℕ} {ε cw : ℝ} {Sc T : Set H} {r : H → ℝ} {P : H → Submodule ℝ H}
    (O : Cfs15StageOutput k K ε cw Sc T r P) (x : Sc) {z : H} (hz : z ∈ ball (x : H) (r x))
    (u : H →L[ℝ] E) (hu : ‖u‖ ≤ 1) {m : ℝ} (hm : ∀ v ∈ P x, m * ‖v‖ ≤ ‖u v‖) (hεm : ε / 3 < m) :
    ∃ Tm : Submodule ℝ H, LinearMap.range (fderiv ℝ O.ambient z : H →ₗ[ℝ] H) ≤ Tm ∧
      Module.finrank ℝ Tm = Module.finrank ℝ (P x) ∧ Set.InjOn u Tm := by
  obtain ⟨Tm, hle, hdim, hcf⟩ :=
    Cfs15StageOutput.ambient_tangent_coframe_BAS O x hz u hu hm hεm
  refine ⟨Tm, hle, hdim, fun a ha b hb hab => ?_⟩
  have hε := O.eps_pos
  have h := hcf (a - b) (Tm.sub_mem ha hb)
  rw [map_sub, hab, sub_self, norm_zero, mul_zero] at h
  have hpos : 0 < m - ε / 3 := by linarith
  have h0 : ‖a - b‖ ≤ 0 := by
    by_contra hneg
    have := mul_pos hpos (lt_of_not_ge hneg)
    linarith
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h0)

variable {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

namespace Gaf02Chain

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- **(c4b) for derivatives**: at a plateau point of an active stage the manifold derivative of the
stage map is that of `π_Q ∘ a ∘ π_Q ∘ g_st`. -/
theorem stageMap_mfderiv_eq_BASP (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    {st : Fin 3}
    {O : Cfs15StageOutput (gafStageDim st) Kj (Ξ st) (cw st) (gafCloud P.toLocalChartFamily P.zero st)
      (gafCloudEnlarged P.toLocalChartFamily P.zero st) (fun x => S st * ρ (C.sel st x))
      (C.plane st)}
    (hO : C.slot st = .active O) {p : X} (hp : p ∈ gafStagePlateau_BAS P.toLocalChartPackets st) :
    mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
        (C.stageMap_BAS st) p =
      mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
        (fun q => (gafStageQ P.toLocalChartFamily P.zero st).starProjection
          (O.ambient ((gafStageQ P.toLocalChartFamily P.zero st).starProjection
            (C.stageIn_BAS st q)))) p :=
  (C.stageMap_eventuallyEq_BAS hO hp).mfderiv_eq

end Gaf02Chain

end DifferentialGeometry.Geometry.Collapse
