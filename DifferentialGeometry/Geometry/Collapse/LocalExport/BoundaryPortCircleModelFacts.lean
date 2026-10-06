import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortCircleRow
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortSlimModelFacts

/-!
# Block facts of the pruned circle model on the boundary family (lane O-PORT-A)

The model-side steps of (FM*-int) and (ZB*-int) of `port_circle_interior_table_BAUGP`
(PortTargets v3.1) for the pruned circle model `tcpPrunedModel_BPC` (TCP05's model graph pruned by
CFS27), pointwise on the generic boundary family (no clouds). Closed twins: the last steps of
`FirstStagePlanes_PLN.full_marker` (`ActualStagePlaneFullMarker.lean`) and
`FirstStagePlanes_PLN.zero_block` (`ActualStagePlaneZeroBlock.lean`).

* `tcpPrunedModel_marker_fderiv_BPC`: if the (TG) value bound holds at `u` against a point whose
  circle block `j` is FULL (`(ρ_j η, ρ_j)`, `‖η‖ ≤ 351/49`)
  and `ρ_j/ρ_i ≥ 99/100`, the circle marker
  of `j` annihilates the derivative of the pruned model at `u` (the listed block is in the plateau
  of its bump);
* `tcpPrunedModel_zero_of_not_listed_BPC`: an unlisted zero tag has a zero block;
* `zero_not_listed_BPC`: the zero support of `k` misses `D_i` when `ρ(i) > (80/3)R_k/T`
  (LPA05 on the zero supports, `zero_cutoff_ratio_BPS`, and slow variation of `ρ`).
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

variable (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
    vs U₁ U₂ Ue₁ Ue₂)
  (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂) (i : X)
  (Ac : CGPTag_BAUGP L Z → ℝ² →L[ℝ] ℝ²) (cc : CGPTag_BAUGP L Z → ℝ²)
  (A1 : CGPTag_BAUGP L Z → ℝ² →L[ℝ] ℝ) (c1 : CGPTag_BAUGP L Z → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ)

open Classical in
/-- **The plateau step of (FM\*)** (closed `FirstStagePlanes_PLN.full_marker`, last step): if
`‖ρ(i)⁻¹y − (K_iΦ_i)(u)‖ < e` (`0 ≤ e < 1/100`), the circle block `j` of `y` is the full block
`(ρ_j·1 η, ρ_j·1)` with `‖η‖ ≤ 351/49` and `ρ_j/ρ_i ≥ 99/100`, then the circle marker of `j`
annihilates `D(K_iΦ_i)(u)`. -/
theorem tcpPrunedModel_marker_fderiv_BPC (j : L.circle.finite_centres.toFinset)
    {y : BlockSpace (fun _ : CGPTag_BAUGP L Z => ℝ²)} {η u : ℝ²} {eg : ℝ}
    (hs : 99 / 100 ≤ ρ j.1 / ρ i) (heg0 : 0 ≤ eg) (heg : eg < 1 / 100)
    (hη : ‖η‖ ≤ 351 / 49 * 1)
    (hy : y (.inl j) = WithLp.toLp 2 ((ρ j.1 * 1) • η, ρ j.1 * 1))
    (hTG : ‖(ρ i)⁻¹ • y - tcpPrunedModel_BPC L Z i Ac cc A1 c1 Bτ cτ u‖ < eg) (h : ℝ²) :
    blockMarkerCLM (.inl j : CGPTag_BAUGP L Z)
      (fderiv ℝ (tcpPrunedModel_BPC L Z i Ac cc A1 c1 Bτ cτ) u h) = 0 := by
  have hdiff : DifferentiableAt ℝ (tcpModelGraph_BAUGP L Z i (tcpListedTags_BAUGP L Z i)
      (tcpListedEdges_BAUGP L i) Ac cc A1 c1 Bτ cτ) u :=
    ((contDiff_tcpModelGraph_BAUGP _ _ _ _ _ _ _ _ _ _ _).differentiable (by simp)) _
  have hnum := plateau_numbers_PLN le_rfl hs heg0 heg
  unfold tcpPrunedModel_BPC at hTG ⊢
  set Kp := blockRestrict (V := fun _ : CGPTag_BAUGP L Z => ℝ²)
    (firstKeepTags_GAF5_BAUGP L Z (ρ i)) with hKp
  rw [fderiv_comp _ Kp.differentiableAt hdiff, Kp.fderiv,
    ContinuousLinearMap.comp_apply, blockMarkerCLM_apply, hKp, blockRestrict_apply]
  split_ifs with hkeep
  swap
  · rfl
  rw [← blockMarkerCLM_apply]
  refine tcpModelGraph_marker_fderiv_GAFS_BAUGP L Z i _ _ Ac cc A1 c1 Bτ cτ j u
    (fun hlist hji => ?_) h
  have hmt : (⇑Kp ∘ tcpModelGraph_BAUGP L Z i
        (tcpListedTags_BAUGP L Z i) (tcpListedEdges_BAUGP L i) Ac cc A1 c1 Bτ cτ) u (.inl j) =
      scaledCutoffBlock (ρ j.1 / ρ i) (circleCutoffBump_LC87 : ℝ² → ℝ)
        (Ac (.inl j) u + cc (.inl j)) := by
    simp only [Function.comp_apply, hKp, blockRestrict_apply, hkeep, ite_true]
    change tcpModelComponent_BAUGP L Z i (tcpListedTags_BAUGP L Z i) (tcpListedEdges_BAUGP L i)
      Ac cc A1 c1 Bτ cτ (.inl j) u = _
    simp only [tcpModelComponent_BAUGP, hji, hlist, ite_true, ite_false]
  have hcl := block_close_PLN (.inl j) hTG hy
  rw [hmt] at hcl
  exact scaledCutoffBlock_arg_lt_of_close_PLN (by linarith) hnum.1 hη hcl
    (by simpa using hnum.2)

open Classical in
/-- An unlisted zero tag has a zero block in the pruned model. -/
theorem tcpPrunedModel_zero_of_not_listed_BPC (k : Z.finite_centres.toFinset)
    (habs : (.inr (.inr (.inr (.inl k))) : CGPTag_BAUGP L Z) ∉ tcpListedTags_BAUGP L Z i)
    (u : ℝ²) :
    tcpPrunedModel_BPC L Z i Ac cc A1 c1 Bτ cτ u (.inr (.inr (.inr (.inl k)))) = 0 := by
  unfold tcpPrunedModel_BPC
  rw [Function.comp_apply, blockRestrict_apply]
  split_ifs
  · change tcpModelComponent_BAUGP L Z i (tcpListedTags_BAUGP L Z i) (tcpListedEdges_BAUGP L i)
      Ac cc A1 c1 Bτ cτ (.inr (.inr (.inr (.inl k)))) u = 0
    simp only [tcpModelComponent_BAUGP, habs, ite_false]
    rfl
  · rfl

end Generic

section Packets

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- The model metrics of `LocalPacketsOnBF`, as a named local instance. -/
local instance instMetricN_BPCm
    (P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
      ζ Λz U₁ U₂ Ue₁ Ue₂) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalPacketsOnBF`, as a named local instance. -/
local instance instChartedN_BPCm
    (P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
      ζ Λz U₁ U₂ Ue₁ Ue₂) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalPacketsOnBF`, as a named local instance. -/
local instance instMetricC_BPCm
    (P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
      ζ Λz U₁ U₂ Ue₁ Ue₂) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **No zero support meets a large circle reference** (closed `zero_meet_absurd_PLN` with
`C = 10`): if `ρ(i) > (80/3)R_k/T`, the zero tag `k` is not listed at `i`. -/
theorem zero_not_listed_BPC
    (P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
      ζ Λz U₁ U₂ Ue₁ Ue₂)
    (hΛ : 0 ≤ Λ) (hΛ10 : Λ * 10 ≤ 1 / 4) (hT : 0 < T) (he : e < 1 / 40) {i : X}
    (k : P.zero.finite_centres.toFinset)
    (hρi : 80 / 3 * ((P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / T) < ρ i) :
    (.inr (.inr (.inr (.inl k))) : CGPTag_BAUGP P.toLocalPacketsOnB P.zero) ∉
      tcpListedTags_BAUGP P.toLocalPacketsOnB P.zero i := by
  intro h
  obtain ⟨z, hz, hza⟩ := (mem_tcpListedTags_KA7_BAUGP (i := i)).mp h
  have hk := (Set.Finite.mem_toFinset _).mp k.2
  have h1 := zero_cutoff_ratio_BPS P hT he hk hz
  have h2 := (scale_mem_of_dist_lt_KC P.lipschitz_scale hΛ (hρ i) (mem_ball.mp hza) hΛ10).1
  have h3 : 20 * (P.zero.zero k.1 hk).radius / T = 20 * ((P.zero.zero k.1 hk).radius / T) := by
    ring
  linarith

end Packets

end DifferentialGeometry.Geometry.Collapse
