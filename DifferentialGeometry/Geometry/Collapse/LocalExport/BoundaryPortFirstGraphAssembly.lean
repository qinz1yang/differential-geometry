import DifferentialGeometry.Geometry.Fibration.ActualFirstGraphAssembly
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortChartFamilyApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortChartFamilyBindings
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortChartFamilyEdgeApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortQuantitativeApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortPacketsResidualApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortActiveSupportPacket
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortBlockBudgets
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortCloudPackets
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortEdgeComparisonList
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortEdgeSupportLink
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortFirstGraphEdgeGroup
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortFirstGraphModel
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortFirstGraphTags
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortFirstGraphTagsScalar
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortGlobalBlockMapBridge
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortRawAlignment
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortRetainedMarkerCloud
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortSupportRows
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortZeroMeeting
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAffineHeight
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryWholeSupportCount
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryReplacementStrictBCF2K

/-!
# Boundary port (lane B-PORT-A): ActualFirstGraphAssembly (circle-stage closure)

GENERATED from `DifferentialGeometry/Geometry/Fibration/ActualFirstGraphAssembly.lean` by
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

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- The scalar action on a block `ℓ²(ℝ² × ℝ)` is continuous (given directly: the instance search
for it times out). -/
local instance instContinuousSMulPlaneBlock_KA7A_BAUGP : ContinuousSMul ℝ (WithLp 2 (ℝ² × ℝ)) :=
  IsBoundedSMul.continuousSMul

section Generic

variable {κ : Type*} [Fintype κ] {W : κ → Type*} [∀ t, NormedAddCommGroup (W t)]
  [∀ t, InnerProductSpace ℝ (W t)]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]

end Generic

section Budget

end Budget

section Scalar

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}
  {vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricN_TCP05A_KA7_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedN_TCP05A_KA7_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricC_TCP05A_KA7_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **(TG) for a listed slim block** at `x ∈ B(j, 10⁶Δρ(j))` from TCP03's scalar comparison
`|s_jη_j − A₁η_i − c| ≤ ε`, `|s_j dη_j − A₁ dη_i| ≤ εν` (`s_j ≥ 99/100`, `‖A₁‖ ≤ 1`). -/
theorem tg_slim_tag_KA7_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (hΔ : 1 ≤ Δ) {i : X} (j : P.slim.finite_centres.toFinset) {x : X}
    (hxj : x ∈ ball j.1 (10 ^ 6 * Δ * ρ j.1)) (hs : 99 / 100 ≤ ρ j.1 / ρ i)
    (hcd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ)
      (P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord_BCG2 x)
    (ηi : X → ℝ²) (A₁ : ℝ² →L[ℝ] ℝ) (hA₁ : ‖A₁‖ ≤ 1) (c : ℝ)
    (ν : TangentSpace 𝓘(ℝ, E3) x → ℝ) {ε₀ : ℝ}
    (hval : |ρ j.1 / ρ i * (P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord_BCG2 x -
      A₁ (ηi x) - c| ≤ ε₀)
    (hder : ∀ w, |ρ j.1 / ρ i * mvfderiv 𝓘(ℝ, E3)
      (P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord_BCG2 x w -
        A₁ (mvfderiv 𝓘(ℝ, E3) ηi x w)| ≤ ε₀ * ν w)
    (hηi : ∀ w, ‖mvfderiv 𝓘(ℝ, E3) ηi x w‖ ≤ 2 * ν w) :
    ‖(ρ i)⁻¹ • cgpGlobalMap_BAUGP P P.zero x (.inr (.inl j)) -
        blockLift_KC3 (sgpModelBlock (10 ^ 5 * Δ) (ρ j.1 / ρ i) (A₁ (ηi x) + c))‖ ≤
        tcpBlockBound * ε₀ ∧
      ∀ w, ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3)
          (fun y => cgpGlobalMap_BAUGP P P.zero y (.inr (.inl j))) x w -
        fderiv ℝ (fun a => blockLift_KC3 (sgpModelBlock (10 ^ 5 * Δ) (ρ j.1 / ρ i) (A₁ a + c)))
          (ηi x) (mvfderiv 𝓘(ℝ, E3) ηi x w)‖ ≤ (tcpBlockBound + tcpBlockBound * 2) * ε₀ * ν w := by
  have hri := hρ i
  have hΔ0 : 0 < Δ := by linarith
  have hj := (Set.Finite.mem_toFinset _).mp j.2
  have hf : (fun y => cgpGlobalMap_BAUGP P P.zero y (.inr (.inl j))) =ᶠ[𝓝 x]
      fun y => ρ i • blockLift_KC3 (sgpModelBlock (10 ^ 5 * Δ) (ρ j.1 / ρ i)
        (ρ j.1 / ρ i * (P.slim.centre j.1 hj).coord_BCG2 y)) := by
    filter_upwards [slim_cutoff_eventuallyEq_KA2_BAUGP P hj hxj]
      with y hy
    exact cgpGlobalMap_slim_eq_KA6_BAUGP P j hri hΔ0 hy
  have hℓ : 1 ≤ 10 ^ 5 * Δ := by nlinarith
  have hW (y : ℝ) := sgpModelBlock_derivative_bounds hℓ hs y
  have hsP : 50 * (sgpProfileBound + 1) ≤ tcpBlockBound := by
    linarith [tcpBlockBound_ge_KA6.1, tcpProfileBound_spec.2.1]
  exact tg_scalar_tag_KA6 ((contDiff_sgpModelBlock _ _).of_le (by simp))
    (fun y => (hW y).1.trans hsP) (fun y => (hW y).2.trans hsP) hri.ne' hf hcd A₁ hA₁ c ν hval
    hder hηi

/-- **(TG) for the zero block** (`s₀ = R₀/R ≥ 1`) at a point where the radial function is
differentiable, from TCP03's scalar comparison. -/
theorem tg_zero_tag_KA7_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    {i : X} (k : P.zero.finite_centres.toFinset) {x : X}
    (hs : 1 ≤ (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / ρ i)
    (hrd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ)
      (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x)
    (ηi : X → ℝ²) (A₁ : ℝ² →L[ℝ] ℝ) (hA₁ : ‖A₁‖ ≤ 1) (c : ℝ)
    (ν : TangentSpace 𝓘(ℝ, E3) x → ℝ) {ε₀ : ℝ}
    (hval : |(P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / ρ i *
      (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x - A₁ (ηi x) - c| ≤ ε₀)
    (hder : ∀ w, |(P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / ρ i *
      mvfderiv 𝓘(ℝ, E3) (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x w -
        A₁ (mvfderiv 𝓘(ℝ, E3) ηi x w)| ≤ ε₀ * ν w)
    (hηi : ∀ w, ‖mvfderiv 𝓘(ℝ, E3) ηi x w‖ ≤ 2 * ν w) :
    ‖(ρ i)⁻¹ • cgpGlobalMap_BAUGP P P.zero x (.inr (.inr (.inr (.inl k)))) -
        blockLift_KC3 (zeroModelBlock
          ((P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / ρ i) (A₁ (ηi x) + c))‖ ≤
        tcpBlockBound * ε₀ ∧
      ∀ w, ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3)
          (fun y => cgpGlobalMap_BAUGP P P.zero y (.inr (.inr (.inr (.inl k))))) x w -
        fderiv ℝ (fun a => blockLift_KC3 (zeroModelBlock
          ((P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / ρ i) (A₁ a + c)))
          (ηi x) (mvfderiv 𝓘(ℝ, E3) ηi x w)‖ ≤ (tcpBlockBound + tcpBlockBound * 2) * ε₀ * ν w := by
  have hri := hρ i
  have hf : (fun y => cgpGlobalMap_BAUGP P P.zero y
      (.inr (.inr (.inr (.inl k))))) =ᶠ[𝓝 x]
      fun y => ρ i • blockLift_KC3 (zeroModelBlock
        ((P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / ρ i)
        ((P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / ρ i *
          (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial y)) :=
    Filter.Eventually.of_forall fun y => cgpGlobalMap_zero_eq_KA6_BAUGP P k hri y
  have hW (y : ℝ) := zeroModelBlock_derivative_bounds hs y
  have hzP : 50 * (zeroProfileBound + 1) ≤ tcpBlockBound := by
    linarith [tcpBlockBound_ge_KA6.1, tcpProfileBound_spec.2.2.1]
  exact tg_scalar_tag_KA6 ((contDiff_zeroModelBlock _).of_le (by simp))
    (fun y => (hW y).1.trans hzP) (fun y => (hW y).2.trans hzP) hri.ne' hf hrd A₁ hA₁ c ν hval
    hder hηi

end Scalar

section Cases

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}
  {vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricN_TCP05B_KA7_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedN_TCP05B_KA7_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricC_TCP05B_KA7_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

open Classical in
/-- **A listed circle block `j ≠ i`** within the budget (TCP03 at accuracy `θ/2`). -/
theorem tcp05_circle_case_KA7_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    {i : X} (hi : i ∈ P.circle.centres) (S : Finset (CGPTag_BAUGP P P.zero))
    (Se : Finset P.edgeB.finite_centres.toFinset)
    (Ac : CGPTag_BAUGP P P.zero → ℝ² →L[ℝ] ℝ²)
    (cc : CGPTag_BAUGP P P.zero → ℝ²)
    (A1 : CGPTag_BAUGP P P.zero → ℝ² →L[ℝ] ℝ)
    (c1 : CGPTag_BAUGP P P.zero → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ)
    {θ : ℝ} (hθ : 0 ≤ θ) (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (j : P.circle.finite_centres.toFinset)
    (hji : j.1 ≠ i) (hjS : (.inl j : CGPTag_BAUGP P P.zero) ∈ S) {x : X}
    (hxi : x ∈ ball i (200 * ρ i)) (hxj : x ∈ ball j.1 (200 * ρ j.1))
    (hs : ρ j.1 / ρ i ∈ Icc (1 / 2 : ℝ) 2) (hA : ‖Ac (.inl j)‖ ≤ 1)
    (hval : ‖(ρ j.1 / ρ i) • cgpCircleCoord_BAUGP P j.1
        ((Set.Finite.mem_toFinset _).mp j.2) x -
        Ac (.inl j) (cgpCircleCoord_BAUGP P i hi x) - cc (.inl j)‖ ≤ θ / 2)
    (hder : ∀ w : TangentSpace 𝓘(ℝ, E3) x,
      ‖(ρ j.1 / ρ i) • mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord_BAUGP P j.1
          ((Set.Finite.mem_toFinset _).mp j.2)) x w -
        Ac (.inl j) (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord_BAUGP P i hi) x w)‖ ≤
        θ / 2 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w)) :
    ‖(ρ i)⁻¹ • cgpGlobalMap_BAUGP P P.zero x (.inl j) -
        tcpModelComponent_BAUGP P P.zero i S Se Ac cc A1 c1 Bτ cτ (.inl j)
          (cgpCircleCoord_BAUGP P i hi x)‖ ≤ tcpTagBudget θ Δ Λ ∧
      ∀ w : TangentSpace 𝓘(ℝ, E3) x,
        ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3)
            (fun y => cgpGlobalMap_BAUGP P P.zero y (.inl j)) x w -
          fderiv ℝ (tcpModelComponent_BAUGP P P.zero i S Se Ac cc A1 c1 Bτ cτ (.inl j))
            (cgpCircleCoord_BAUGP P i hi x)
            (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord_BAUGP P i hi) x w)‖ ≤
          tcpTagBudget θ Δ Λ * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) := by
  have hcomp : tcpModelComponent_BAUGP P P.zero i S Se Ac cc A1 c1 Bτ cτ (.inl j) =
      fun a => scaledCutoffBlock (ρ j.1 / ρ i) (circleCutoffBump_LC87 : ℝ² → ℝ)
        (Ac (.inl j) a + cc (.inl j)) := by
    simp only [tcpModelComponent_BAUGP, hji, hjS, ite_false, ite_true]
  have h := tg_circle_tag_KA6_BAUGP P hi j hxj hxi hs (Ac (.inl j)) hA (cc (.inl j)) hval hder
  have hP := tcpProfileBound_spec.1
  have hPB : 50 * (tcpProfileBound + 1) ≤ tcpBlockBound := tcpBlockBound_ge_KA6.1
  have hb1 : 50 * (tcpProfileBound + 1) * (θ / 2) ≤ tcpTagBudget θ Δ Λ := by
    have := tcpTagBudget_fixed_KA7 (c := 1 / 2) hθ hΔ hΛ (by norm_num)
    have h2 : 50 * (tcpProfileBound + 1) * (θ / 2) ≤ 1 / 2 * tcpBlockBound * θ := by nlinarith
    linarith
  have hb2 : (50 * (tcpProfileBound + 1) + 50 * (tcpProfileBound + 1) * 2) * (θ / 2) ≤
      tcpTagBudget θ Δ Λ := by
    have := tcpTagBudget_fixed_KA7 (c := 3 / 2) hθ hΔ hΛ (by norm_num)
    have h2 : (50 * (tcpProfileBound + 1) + 50 * (tcpProfileBound + 1) * 2) * (θ / 2) ≤
        3 / 2 * tcpBlockBound * θ := by nlinarith
    linarith
  rw [hcomp]
  refine ⟨h.1.trans hb1, fun w => (h.2 w).trans ?_⟩
  exact mul_le_mul_of_nonneg_right hb2 (Real.sqrt_nonneg _)

open Classical in
/-- **The own circle block** (`j.1 = i`): no error on `{|η_i| ≤ 8}`. -/
theorem tcp05_own_case_KA7_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    {i : X} (hi : i ∈ P.circle.centres) (S : Finset (CGPTag_BAUGP P P.zero))
    (Se : Finset P.edgeB.finite_centres.toFinset)
    (Ac : CGPTag_BAUGP P P.zero → ℝ² →L[ℝ] ℝ²)
    (cc : CGPTag_BAUGP P P.zero → ℝ²)
    (A1 : CGPTag_BAUGP P P.zero → ℝ² →L[ℝ] ℝ)
    (c1 : CGPTag_BAUGP P P.zero → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ)
    {θ : ℝ} (hθ : 0 ≤ θ) (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (j : P.circle.finite_centres.toFinset)
    (hji : j.1 = i) {x : X} (hxi : x ∈ ball i (200 * ρ i))
    (h8 : ‖cgpCircleCoord_BAUGP P i hi x‖ ≤ 8) :
    ‖(ρ i)⁻¹ • cgpGlobalMap_BAUGP P P.zero x (.inl j) -
        tcpModelComponent_BAUGP P P.zero i S Se Ac cc A1 c1 Bτ cτ (.inl j)
          (cgpCircleCoord_BAUGP P i hi x)‖ ≤ tcpTagBudget θ Δ Λ ∧
      ∀ w : TangentSpace 𝓘(ℝ, E3) x,
        ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3)
            (fun y => cgpGlobalMap_BAUGP P P.zero y (.inl j)) x w -
          fderiv ℝ (tcpModelComponent_BAUGP P P.zero i S Se Ac cc A1 c1 Bτ cτ (.inl j))
            (cgpCircleCoord_BAUGP P i hi x)
            (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord_BAUGP P i hi) x w)‖ ≤
          tcpTagBudget θ Δ Λ * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) := by
  have hcomp : tcpModelComponent_BAUGP P P.zero i S Se Ac cc A1 c1 Bτ cτ (.inl j) =
      fun a => (WithLp.toLp 2 (a, (1 : ℝ)) : WithLp 2 (ℝ² × ℝ)) := by
    simp only [tcpModelComponent_BAUGP, hji, ite_true]
  have hb := tcpTagBudget_nonneg_KA7 hθ hΔ hΛ
  obtain ⟨h1, h2⟩ := tg_own_tag_KA7_BAUGP P hi j hji hxi h8
  rw [hcomp]
  refine ⟨?_, fun w => ?_⟩
  · rw [h1, sub_self, norm_zero]
    exact hb
  · rw [h2 w, sub_self, norm_zero]
    exact mul_nonneg hb (Real.sqrt_nonneg _)

open Classical in
/-- **A listed slim block** within the budget (TCP03 at accuracy `θ/2`). -/
theorem tcp05_slim_case_KA7_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    {i : X} (hi : i ∈ P.circle.centres) (S : Finset (CGPTag_BAUGP P P.zero))
    (Se : Finset P.edgeB.finite_centres.toFinset)
    (Ac : CGPTag_BAUGP P P.zero → ℝ² →L[ℝ] ℝ²)
    (cc : CGPTag_BAUGP P P.zero → ℝ²)
    (A1 : CGPTag_BAUGP P P.zero → ℝ² →L[ℝ] ℝ)
    (c1 : CGPTag_BAUGP P P.zero → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ)
    {θ : ℝ} (hθ : 0 ≤ θ) (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (j : P.slim.finite_centres.toFinset)
    (hjS : (.inr (.inl j) : CGPTag_BAUGP P P.zero) ∈ S) {x : X}
    (hxi : x ∈ ball i (200 * ρ i)) (hxj : x ∈ ball j.1 (10 ^ 6 * Δ * ρ j.1))
    (hs : 99 / 100 ≤ ρ j.1 / ρ i)
    (hcd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ)
      (P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord_BCG2 x)
    (hA : ‖A1 (.inr (.inl j))‖ ≤ 1)
    (hval : |ρ j.1 / ρ i * (P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord_BCG2 x -
      A1 (.inr (.inl j)) (cgpCircleCoord_BAUGP P i hi x) - c1 (.inr (.inl j))| ≤
        θ / 2)
    (hder : ∀ w : TangentSpace 𝓘(ℝ, E3) x, |ρ j.1 / ρ i * mvfderiv 𝓘(ℝ, E3)
      (P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord_BCG2 x w -
        A1 (.inr (.inl j)) (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord_BAUGP P i hi) x w)| ≤
        θ / 2 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w)) :
    ‖(ρ i)⁻¹ • cgpGlobalMap_BAUGP P P.zero x (.inr (.inl j)) -
        tcpModelComponent_BAUGP P P.zero i S Se Ac cc A1 c1 Bτ cτ (.inr (.inl j))
          (cgpCircleCoord_BAUGP P i hi x)‖ ≤ tcpTagBudget θ Δ Λ ∧
      ∀ w : TangentSpace 𝓘(ℝ, E3) x,
        ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3)
            (fun y => cgpGlobalMap_BAUGP P P.zero y (.inr (.inl j))) x w -
          fderiv ℝ
            (tcpModelComponent_BAUGP P P.zero i S Se Ac cc A1 c1 Bτ cτ (.inr (.inl j)))
            (cgpCircleCoord_BAUGP P i hi x)
            (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord_BAUGP P i hi) x w)‖ ≤
          tcpTagBudget θ Δ Λ * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) := by
  have hcomp : tcpModelComponent_BAUGP P P.zero i S Se Ac cc A1 c1 Bτ cτ
      (.inr (.inl j)) = fun a => blockLift_KC3 (sgpModelBlock (10 ^ 5 * Δ) (ρ j.1 / ρ i)
        (A1 (.inr (.inl j)) a + c1 (.inr (.inl j)))) := by
    simp only [tcpModelComponent_BAUGP, hjS, ite_true]
  have h := tg_slim_tag_KA7_BAUGP P hΔ j hxj hs hcd (cgpCircleCoord_BAUGP P i hi)
    (A1 (.inr (.inl j))) hA (c1 (.inr (.inl j))) _ hval hder
    (fun w => norm_mvfderiv_circleCoord_le_KA6_BAUGP P hi hxi w)
  have hb1 : tcpBlockBound * (θ / 2) ≤ tcpTagBudget θ Δ Λ := by
    have := tcpTagBudget_fixed_KA7 (c := 1 / 2) hθ hΔ hΛ (by norm_num)
    linarith
  have hb2 : (tcpBlockBound + tcpBlockBound * 2) * (θ / 2) ≤ tcpTagBudget θ Δ Λ := by
    have := tcpTagBudget_fixed_KA7 (c := 3 / 2) hθ hΔ hΛ (by norm_num)
    linarith
  rw [hcomp]
  refine ⟨h.1.trans hb1, fun w => (h.2 w).trans ?_⟩
  exact mul_le_mul_of_nonneg_right hb2 (Real.sqrt_nonneg _)

open Classical in
/-- **The listed zero block** within the budget (TCP03 at accuracy `θ/2`). -/
theorem tcp05_zero_case_KA7_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    {i : X} (hi : i ∈ P.circle.centres) (S : Finset (CGPTag_BAUGP P P.zero))
    (Se : Finset P.edgeB.finite_centres.toFinset)
    (Ac : CGPTag_BAUGP P P.zero → ℝ² →L[ℝ] ℝ²)
    (cc : CGPTag_BAUGP P P.zero → ℝ²)
    (A1 : CGPTag_BAUGP P P.zero → ℝ² →L[ℝ] ℝ)
    (c1 : CGPTag_BAUGP P P.zero → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ)
    {θ : ℝ} (hθ : 0 ≤ θ) (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (k : P.zero.finite_centres.toFinset)
    (hkS : (.inr (.inr (.inr (.inl k))) : CGPTag_BAUGP P P.zero) ∈ S) {x : X}
    (hxi : x ∈ ball i (200 * ρ i))
    (hs : 1 ≤ (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / ρ i)
    (hrd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ)
      (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x)
    (hA : ‖A1 (.inr (.inr (.inr (.inl k))))‖ ≤ 1)
    (hval : |(P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / ρ i *
      (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x -
        A1 (.inr (.inr (.inr (.inl k)))) (cgpCircleCoord_BAUGP P i hi x) -
        c1 (.inr (.inr (.inr (.inl k))))| ≤ θ / 2)
    (hder : ∀ w : TangentSpace 𝓘(ℝ, E3) x,
      |(P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / ρ i *
        mvfderiv 𝓘(ℝ, E3) (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x w -
        A1 (.inr (.inr (.inr (.inl k))))
          (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord_BAUGP P i hi) x w)| ≤
        θ / 2 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w)) :
    ‖(ρ i)⁻¹ • cgpGlobalMap_BAUGP P P.zero x (.inr (.inr (.inr (.inl k)))) -
        tcpModelComponent_BAUGP P P.zero i S Se Ac cc A1 c1 Bτ cτ
          (.inr (.inr (.inr (.inl k)))) (cgpCircleCoord_BAUGP P i hi x)‖ ≤
        tcpTagBudget θ Δ Λ ∧
      ∀ w : TangentSpace 𝓘(ℝ, E3) x,
        ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (fun y => cgpGlobalMap_BAUGP P P.zero y
            (.inr (.inr (.inr (.inl k))))) x w -
          fderiv ℝ (tcpModelComponent_BAUGP P P.zero i S Se Ac cc A1 c1 Bτ cτ
              (.inr (.inr (.inr (.inl k)))))
            (cgpCircleCoord_BAUGP P i hi x)
            (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord_BAUGP P i hi) x w)‖ ≤
          tcpTagBudget θ Δ Λ * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) := by
  have hcomp : tcpModelComponent_BAUGP P P.zero i S Se Ac cc A1 c1 Bτ cτ
      (.inr (.inr (.inr (.inl k)))) = fun a => blockLift_KC3 (zeroModelBlock
        ((P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / ρ i)
        (A1 (.inr (.inr (.inr (.inl k)))) a + c1 (.inr (.inr (.inr (.inl k)))))) := by
    simp only [tcpModelComponent_BAUGP, hkS, ite_true]
  have h := tg_zero_tag_KA7_BAUGP P k hs hrd (cgpCircleCoord_BAUGP P i hi)
    (A1 (.inr (.inr (.inr (.inl k))))) hA (c1 (.inr (.inr (.inr (.inl k))))) _ hval hder
    (fun w => norm_mvfderiv_circleCoord_le_KA6_BAUGP P hi hxi w)
  have hb1 : tcpBlockBound * (θ / 2) ≤ tcpTagBudget θ Δ Λ := by
    have := tcpTagBudget_fixed_KA7 (c := 1 / 2) hθ hΔ hΛ (by norm_num)
    linarith
  have hb2 : (tcpBlockBound + tcpBlockBound * 2) * (θ / 2) ≤ tcpTagBudget θ Δ Λ := by
    have := tcpTagBudget_fixed_KA7 (c := 3 / 2) hθ hΔ hΛ (by norm_num)
    linarith
  rw [hcomp]
  refine ⟨h.1.trans hb1, fun w => (h.2 w).trans ?_⟩
  exact mul_le_mul_of_nonneg_right hb2 (Real.sqrt_nonneg _)

open Classical in
/-- **A listed edge block** (`j ∈ S_e`) within the budget, from the input comparison
`ε = √(#S_e + 1) θ`, `L = 4√(#S_e + 1)`. -/
theorem tcp05_edge_case_KA7_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    {i : X} (hi : i ∈ P.circle.centres) (S : Finset (CGPTag_BAUGP P P.zero))
    (Se : Finset P.edgeB.finite_centres.toFinset)
    (Ac : CGPTag_BAUGP P P.zero → ℝ² →L[ℝ] ℝ²)
    (cc : CGPTag_BAUGP P P.zero → ℝ²)
    (A1 : CGPTag_BAUGP P P.zero → ℝ² →L[ℝ] ℝ)
    (c1 : CGPTag_BAUGP P P.zero → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ) (τf : X → ℝ)
    {θ : ℝ} (hθ : 0 ≤ θ) (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (j : P.edgeB.finite_centres.toFinset) (hj : j ∈ Se) {x : X}
    (hx : x ∈ ball i (10 * ρ i))
    (hcut : ∀ y ∈ ball i (10 * ρ i), ∀ k ∈ Se, P.edgeB.cutoff_BAUGA k.1 y =
      edgeCoordinateProfile (P.edgeB.coord_BAUGA k.1 y / Δ) * edgeHeightProfile (τf y / Δ))
    (hs : ∀ k : Se, ρ k.1.1 / ρ i ∈ Icc (1 / 2 : ℝ) 2)
    (hcard : (Se.card : ℝ) ≤ fc07ActiveBound)
    (hV : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, EuclideanSpace ℝ (Option Se))
      (tcpEdgeActual_BAUGP P Se τf) x)
    (hval : ‖tcpEdgeActual_BAUGP P Se τf x -
      tcpEdgeInput_BAUGP P P.zero Se A1 c1 Bτ cτ
        (cgpCircleCoord_BAUGP P i hi x)‖ ≤ Real.sqrt ((Se.card : ℝ) + 1) * θ)
    (hder : ∀ w : TangentSpace 𝓘(ℝ, E3) x,
      ‖mvfderiv 𝓘(ℝ, E3) (tcpEdgeActual_BAUGP P Se τf) x w -
        tcpEdgeLinear_BAUGP P P.zero Se A1 Bτ
          (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord_BAUGP P i hi) x w)‖ ≤
        Real.sqrt ((Se.card : ℝ) + 1) * θ * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w))
    (hbd : ∀ w : TangentSpace 𝓘(ℝ, E3) x,
      ‖tcpEdgeLinear_BAUGP P P.zero Se A1 Bτ
          (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord_BAUGP P i hi) x w)‖ ≤
        4 * Real.sqrt ((Se.card : ℝ) + 1) * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w)) :
    ‖(ρ i)⁻¹ • cgpGlobalMap_BAUGP P P.zero x (.inr (.inr (.inl j))) -
        tcpModelComponent_BAUGP P P.zero i S Se Ac cc A1 c1 Bτ cτ
          (.inr (.inr (.inl j))) (cgpCircleCoord_BAUGP P i hi x)‖ ≤
        tcpTagBudget θ Δ Λ ∧
      ∀ w : TangentSpace 𝓘(ℝ, E3) x,
        ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3)
            (fun y => cgpGlobalMap_BAUGP P P.zero y (.inr (.inr (.inl j)))) x w -
          fderiv ℝ (tcpModelComponent_BAUGP P P.zero i S Se Ac cc A1 c1 Bτ cτ
              (.inr (.inr (.inl j))))
            (cgpCircleCoord_BAUGP P i hi x)
            (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord_BAUGP P i hi) x w)‖ ≤
          tcpTagBudget θ Δ Λ * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) := by
  have hcomp : tcpModelComponent_BAUGP P P.zero i S Se Ac cc A1 c1 Bτ cτ
      (.inr (.inr (.inl j))) = fun a => blockLift_KC3 (tcpNetwork Δ
        (fun k : Se => ρ k.1.1 / ρ i) (tcpEdgeInput_BAUGP P P.zero Se A1 c1 Bτ cτ a)
        (some ⟨j, hj⟩)) := by
    simp only [tcpModelComponent_BAUGP, hj, ↓reduceDIte]
  have h := tg_edge_tag_KA7_BAUGP P P.zero Se τf A1 c1 Bτ cτ hΔ hx hcut hs hcard j hj
    hV (cgpCircleCoord_BAUGP P i hi) _ hval hder hbd
  have hb := tcpTagBudget_edge_KA7 hθ hΔ hΛ (Nat.cast_nonneg Se.card) hcard
  rw [hcomp]
  refine ⟨h.1.trans hb.1, fun w => (h.2 w).trans ?_⟩
  exact mul_le_mul_of_nonneg_right hb.2 (Real.sqrt_nonneg _)

open Classical in
/-- **The `E'` block** within the budget (`θ ≤ 1`). -/
theorem tcp05_marker_case_KA7_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    {i : X} (hi : i ∈ P.circle.centres) (S : Finset (CGPTag_BAUGP P P.zero))
    (Se : Finset P.edgeB.finite_centres.toFinset)
    (Ac : CGPTag_BAUGP P P.zero → ℝ² →L[ℝ] ℝ²)
    (cc : CGPTag_BAUGP P P.zero → ℝ²)
    (A1 : CGPTag_BAUGP P P.zero → ℝ² →L[ℝ] ℝ)
    (c1 : CGPTag_BAUGP P P.zero → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ) (τf : X → ℝ)
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) {x : X}
    (hx : x ∈ ball i (10 * ρ i))
    (hcut : ∀ y ∈ ball i (10 * ρ i), ∀ k ∈ Se, P.edgeB.cutoff_BAUGA k.1 y =
      edgeCoordinateProfile (P.edgeB.coord_BAUGA k.1 y / Δ) * edgeHeightProfile (τf y / Δ))
    (hoff : ∀ y ∈ ball i (10 * ρ i), ∀ k ∉ Se, P.edgeB.cutoff_BAUGA k.1 y = 0)
    (hτm : ∀ y ∈ ball i (10 * ρ i),
      τf y = cgpHeight_BAUGP P y ∨
        (τf y = 0 ∧ cgpEdgeMarker_BAUGP P y = 0))
    (hs : ∀ k : Se, ρ k.1.1 / ρ i ∈ Icc (1 / 2 : ℝ) 2)
    (hcard : (Se.card : ℝ) ≤ fc07ActiveBound)
    (hV : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, EuclideanSpace ℝ (Option Se))
      (tcpEdgeActual_BAUGP P Se τf) x)
    (hval : ‖tcpEdgeActual_BAUGP P Se τf x -
      tcpEdgeInput_BAUGP P P.zero Se A1 c1 Bτ cτ
        (cgpCircleCoord_BAUGP P i hi x)‖ ≤ Real.sqrt ((Se.card : ℝ) + 1) * θ)
    (hder : ∀ w : TangentSpace 𝓘(ℝ, E3) x,
      ‖mvfderiv 𝓘(ℝ, E3) (tcpEdgeActual_BAUGP P Se τf) x w -
        tcpEdgeLinear_BAUGP P P.zero Se A1 Bτ
          (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord_BAUGP P i hi) x w)‖ ≤
        Real.sqrt ((Se.card : ℝ) + 1) * θ * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w))
    (hbd : ∀ w : TangentSpace 𝓘(ℝ, E3) x,
      ‖tcpEdgeLinear_BAUGP P P.zero Se A1 Bτ
          (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord_BAUGP P i hi) x w)‖ ≤
        4 * Real.sqrt ((Se.card : ℝ) + 1) * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w)) :
    ‖(ρ i)⁻¹ • cgpGlobalMap_BAUGP P P.zero x (cgpEdgeTag_BAUGP P P.zero) -
        tcpModelComponent_BAUGP P P.zero i S Se Ac cc A1 c1 Bτ cτ
          (cgpEdgeTag_BAUGP P P.zero) (cgpCircleCoord_BAUGP P i hi x)‖ ≤
        tcpTagBudget θ Δ Λ ∧
      ∀ w : TangentSpace 𝓘(ℝ, E3) x,
        ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (fun y => cgpGlobalMap_BAUGP P P.zero y
            (cgpEdgeTag_BAUGP P P.zero)) x w -
          fderiv ℝ (tcpModelComponent_BAUGP P P.zero i S Se Ac cc A1 c1 Bτ cτ
              (cgpEdgeTag_BAUGP P P.zero))
            (cgpCircleCoord_BAUGP P i hi x)
            (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord_BAUGP P i hi) x w)‖ ≤
          tcpTagBudget θ Δ Λ * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) := by
  have hcomp : tcpModelComponent_BAUGP P P.zero i S Se Ac cc A1 c1 Bτ cτ
      (cgpEdgeTag_BAUGP P P.zero) = fun a => blockLift_KC3 (tcpNetwork Δ
        (fun k : Se => ρ k.1.1 / ρ i) (tcpEdgeInput_BAUGP P P.zero Se A1 c1 Bτ cτ a)
        none) := rfl
  have h := tg_edgeMarker_tag_KA7_BAUGP P P.zero Se τf A1 c1 Bτ cτ hΔ hΛ hx hcut hoff
    hτm hs hcard hV (cgpCircleCoord_BAUGP P i hi) hval hder hbd
  have hb := tcpTagBudget_marker_KA7 hθ hθ1 hΔ hΛ (Nat.cast_nonneg Se.card) hcard
  rw [hcomp]
  refine ⟨h.1.trans hb.1, fun w => (h.2 w).trans ?_⟩
  exact mul_le_mul_of_nonneg_right hb.2 (Real.sqrt_nonneg _)

open Classical in
/-- **The scale block** within the budget. -/
theorem tcp05_scale_case_KA7_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    {i : X} (hi : i ∈ P.circle.centres) (S : Finset (CGPTag_BAUGP P P.zero))
    (Se : Finset P.edgeB.finite_centres.toFinset)
    (Ac : CGPTag_BAUGP P P.zero → ℝ² →L[ℝ] ℝ²)
    (cc : CGPTag_BAUGP P P.zero → ℝ²)
    (A1 : CGPTag_BAUGP P P.zero → ℝ² →L[ℝ] ℝ)
    (c1 : CGPTag_BAUGP P P.zero → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ)
    {θ : ℝ} (hθ : 0 ≤ θ) (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) {x : X} (hx : x ∈ ball i (10 * ρ i)) :
    ‖(ρ i)⁻¹ • cgpGlobalMap_BAUGP P P.zero x
          (cgpScaleTag_BAUGP P P.zero) -
        tcpModelComponent_BAUGP P P.zero i S Se Ac cc A1 c1 Bτ cτ
          (cgpScaleTag_BAUGP P P.zero) (cgpCircleCoord_BAUGP P i hi x)‖ ≤
        tcpTagBudget θ Δ Λ ∧
      ∀ w : TangentSpace 𝓘(ℝ, E3) x,
        ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (fun y => cgpGlobalMap_BAUGP P P.zero y
            (cgpScaleTag_BAUGP P P.zero)) x w -
          fderiv ℝ (tcpModelComponent_BAUGP P P.zero i S Se Ac cc A1 c1 Bτ cτ
              (cgpScaleTag_BAUGP P P.zero))
            (cgpCircleCoord_BAUGP P i hi x)
            (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord_BAUGP P i hi) x w)‖ ≤
          tcpTagBudget θ Δ Λ * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) := by
  have hcomp : tcpModelComponent_BAUGP P P.zero i S Se Ac cc A1 c1 Bτ cτ
      (cgpScaleTag_BAUGP P P.zero) =
        fun _ => (WithLp.toLp 2 (0, 1) : WithLp 2 (ℝ² × ℝ)) := rfl
  have h := tg_scale_tag_KA7_BAUGP (hmetric := hmetric) P P.zero hΛ hx
  have hb := tcpTagBudget_scale_KA7 hθ hΔ hΛ
  rw [hcomp]
  refine ⟨h.1.trans hb.1, fun w => ?_⟩
  rw [fderiv_const_apply, zero_apply, sub_zero]
  exact (h.2 w).trans (mul_le_mul_of_nonneg_right hb.2 (Real.sqrt_nonneg _))

open Classical in
/-- **An inactive tag**: off the active tags of the model (and with `x` outside the closed support
of its cutoff) both the block of `R⁻¹𝓔⁰` and the model block vanish, with their derivatives. -/
theorem tcp05_off_case_KA7_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    {i : X} (hi : i ∈ P.circle.centres) (S : Finset (CGPTag_BAUGP P P.zero))
    (Se : Finset P.edgeB.finite_centres.toFinset)
    (Ac : CGPTag_BAUGP P P.zero → ℝ² →L[ℝ] ℝ²)
    (cc : CGPTag_BAUGP P P.zero → ℝ²)
    (A1 : CGPTag_BAUGP P P.zero → ℝ² →L[ℝ] ℝ)
    (c1 : CGPTag_BAUGP P P.zero → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ)
    (hown : ∀ j : P.circle.finite_centres.toFinset, j.1 = i →
      (.inl j : CGPTag_BAUGP P P.zero) ∈ S)
    (t : CGPTag_BAUGP P P.zero)
    (ht : t ∉ tcpModelActive_BAUGP P P.zero S Se) {x : X}
    (hx : x ∉ tsupport (cgpCutoff_BAUGP P P.zero t)) :
    (ρ i)⁻¹ • cgpGlobalMap_BAUGP P P.zero x t -
        tcpModelComponent_BAUGP P P.zero i S Se Ac cc A1 c1 Bτ cτ t
          (cgpCircleCoord_BAUGP P i hi x) = 0 ∧
      ∀ w : TangentSpace 𝓘(ℝ, E3) x,
        (ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (fun y => cgpGlobalMap_BAUGP P P.zero y t) x w -
          fderiv ℝ (tcpModelComponent_BAUGP P P.zero i S Se Ac cc A1 c1 Bτ cτ t)
            (cgpCircleCoord_BAUGP P i hi x)
            (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord_BAUGP P i hi) x w) = 0 := by
  have hz := tcpModelComponent_eq_zero_BAUGP P P.zero i S Se Ac cc A1 c1 Bτ cτ hown t
    ht
  obtain ⟨h1, h2⟩ := tg_unlisted_tag_KA7_BAUGP P P.zero hx
  have h0 : (0 : ℝ² → WithLp 2 (ℝ² × ℝ)) = fun _ => 0 := rfl
  rw [hz, h0]
  refine ⟨?_, fun w => ?_⟩
  · rw [h1, smul_zero, sub_zero]
  · rw [h2 w, smul_zero, fderiv_const_apply, zero_apply, sub_zero]

end Cases

section Point

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}
  {vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricN_TCP05C_KA7_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedN_TCP05C_KA7_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricC_TCP05C_KA7_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

open Classical in
/-- **TCP05's (TG) at one point** `x ∈ D_i` with `|η_i(x)| ≤ 8`, for given model data: if every
listed circle / slim / zero block satisfies TCP03's comparison at accuracy `θ/2`, the edge
coordinates and `τ` satisfy the scalar comparison at accuracy `θ` (with the cutoff identities of
TCP04's case on `D_i`), and the unlisted cutoffs have `x` outside their closed supports, then
`‖R⁻¹𝓔⁰(x) − Φ_i(η_i(x))‖ ≤ √#A b` and the derivative error is `≤ √#A b |w|`
(`A = tcpModelActive_BAUGP`, `b = tcpTagBudget θ Δ Λ`). -/
theorem tcp05_point_KA7_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    {i : X} (hi : i ∈ P.circle.centres) (S : Finset (CGPTag_BAUGP P P.zero))
    (Se : Finset P.edgeB.finite_centres.toFinset)
    (Ac : CGPTag_BAUGP P P.zero → ℝ² →L[ℝ] ℝ²)
    (cc : CGPTag_BAUGP P P.zero → ℝ²)
    (A1 : CGPTag_BAUGP P P.zero → ℝ² →L[ℝ] ℝ)
    (c1 : CGPTag_BAUGP P P.zero → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ) (τf : X → ℝ)
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) {x : X}
    (hF : MDifferentiableAt 𝓘(ℝ, E3)
      𝓘(ℝ, BlockSpace (fun _ : CGPTag_BAUGP P P.zero => ℝ²))
      (cgpGlobalMap_BAUGP P P.zero) x)
    (hx : x ∈ ball i (10 * ρ i)) (hxi : x ∈ ball i (200 * ρ i))
    (h8 : ‖cgpCircleCoord_BAUGP P i hi x‖ ≤ 8)
    (hown : ∀ j : P.circle.finite_centres.toFinset, j.1 = i →
      (.inl j : CGPTag_BAUGP P P.zero) ∈ S)
    (hSe : ∀ j : P.edgeB.finite_centres.toFinset,
      (.inr (.inr (.inl j)) : CGPTag_BAUGP P P.zero) ∉ S)
    (hC : ∀ j : P.circle.finite_centres.toFinset, j.1 ≠ i →
      (.inl j : CGPTag_BAUGP P P.zero) ∈ S →
      x ∈ ball j.1 (200 * ρ j.1) ∧ ρ j.1 / ρ i ∈ Icc (1 / 2 : ℝ) 2 ∧ ‖Ac (.inl j)‖ ≤ 1 ∧
        ‖(ρ j.1 / ρ i) • cgpCircleCoord_BAUGP P j.1
            ((Set.Finite.mem_toFinset _).mp j.2) x -
          Ac (.inl j) (cgpCircleCoord_BAUGP P i hi x) - cc (.inl j)‖ ≤ θ / 2 ∧
        ∀ w : TangentSpace 𝓘(ℝ, E3) x,
          ‖(ρ j.1 / ρ i) • mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord_BAUGP P j.1
              ((Set.Finite.mem_toFinset _).mp j.2)) x w -
            Ac (.inl j) (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord_BAUGP P i hi) x w)‖ ≤
            θ / 2 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w))
    (hS : ∀ j : P.slim.finite_centres.toFinset,
      (.inr (.inl j) : CGPTag_BAUGP P P.zero) ∈ S →
      x ∈ ball j.1 (10 ^ 6 * Δ * ρ j.1) ∧ 99 / 100 ≤ ρ j.1 / ρ i ∧
        MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ)
          (P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord_BCG2 x ∧
        ‖A1 (.inr (.inl j))‖ ≤ 1 ∧
        |ρ j.1 / ρ i * (P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord_BCG2 x -
          A1 (.inr (.inl j)) (cgpCircleCoord_BAUGP P i hi x) -
          c1 (.inr (.inl j))| ≤ θ / 2 ∧
        ∀ w : TangentSpace 𝓘(ℝ, E3) x, |ρ j.1 / ρ i * mvfderiv 𝓘(ℝ, E3)
          (P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord_BCG2 x w -
            A1 (.inr (.inl j))
              (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord_BAUGP P i hi) x w)| ≤
            θ / 2 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w))
    (hZ : ∀ k : P.zero.finite_centres.toFinset,
      (.inr (.inr (.inr (.inl k))) : CGPTag_BAUGP P P.zero) ∈ S →
      1 ≤ (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / ρ i ∧
        MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ)
          (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x ∧
        ‖A1 (.inr (.inr (.inr (.inl k))))‖ ≤ 1 ∧
        |(P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / ρ i *
          (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x -
            A1 (.inr (.inr (.inr (.inl k)))) (cgpCircleCoord_BAUGP P i hi x) -
            c1 (.inr (.inr (.inr (.inl k))))| ≤ θ / 2 ∧
        ∀ w : TangentSpace 𝓘(ℝ, E3) x,
          |(P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / ρ i *
            mvfderiv 𝓘(ℝ, E3) (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x w -
            A1 (.inr (.inr (.inr (.inl k))))
              (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord_BAUGP P i hi) x w)| ≤
            θ / 2 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w))
    (hE : ∀ k : Se, ρ k.1.1 / ρ i ∈ Icc (1 / 2 : ℝ) 2 ∧ ‖A1 (.inr (.inr (.inl k.1)))‖ ≤ 2 ∧
      ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (P.edgeB.coord_BAUGA k.1.1) x ∧
      |P.edgeB.coord_BAUGA k.1.1 x - (A1 (.inr (.inr (.inl k.1)))
          (cgpCircleCoord_BAUGP P i hi x) + c1 (.inr (.inr (.inl k.1))))| ≤ θ ∧
      ∀ w : TangentSpace 𝓘(ℝ, E3) x, |mvfderiv 𝓘(ℝ, E3) (P.edgeB.coord_BAUGA k.1.1) x w -
        A1 (.inr (.inr (.inl k.1)))
          (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord_BAUGP P i hi) x w)| ≤
        θ * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w))
    (hτ : ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ τf x ∧ ‖Bτ‖ ≤ 2 ∧
      |τf x - (Bτ (cgpCircleCoord_BAUGP P i hi x) + cτ)| ≤ θ ∧
      ∀ w : TangentSpace 𝓘(ℝ, E3) x, |mvfderiv 𝓘(ℝ, E3) τf x w -
        Bτ (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord_BAUGP P i hi) x w)| ≤
        θ * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w))
    (hcut : ∀ y ∈ ball i (10 * ρ i), ∀ k ∈ Se, P.edgeB.cutoff_BAUGA k.1 y =
      edgeCoordinateProfile (P.edgeB.coord_BAUGA k.1 y / Δ) * edgeHeightProfile (τf y / Δ))
    (hoff : ∀ y ∈ ball i (10 * ρ i), ∀ k ∉ Se, P.edgeB.cutoff_BAUGA k.1 y = 0)
    (hτm : ∀ y ∈ ball i (10 * ρ i),
      τf y = cgpHeight_BAUGP P y ∨
        (τf y = 0 ∧ cgpEdgeMarker_BAUGP P y = 0))
    (hcard : (Se.card : ℝ) ≤ fc07ActiveBound)
    (hunlC : ∀ j : P.circle.finite_centres.toFinset, j.1 ≠ i →
      (.inl j : CGPTag_BAUGP P P.zero) ∉ S → x ∉ tsupport (P.circle.cutoff j.1))
    (hunlS : ∀ j : P.slim.finite_centres.toFinset,
      (.inr (.inl j) : CGPTag_BAUGP P P.zero) ∉ S → x ∉ tsupport (P.slim.cutoff_BCNT j.1))
    (hunlZ : ∀ k : P.zero.finite_centres.toFinset,
      (.inr (.inr (.inr (.inl k))) : CGPTag_BAUGP P P.zero) ∉ S →
      x ∉ tsupport (cgpCutoff_BAUGP P P.zero (.inr (.inr (.inr (.inl k)))))) :
    ‖(ρ i)⁻¹ • cgpGlobalMap_BAUGP P P.zero x -
        tcpModelGraph_BAUGP P P.zero i S Se Ac cc A1 c1 Bτ cτ
          (cgpCircleCoord_BAUGP P i hi x)‖ ≤
        Real.sqrt ((tcpModelActive_BAUGP P P.zero S Se).card : ℝ) *
          tcpTagBudget θ Δ Λ ∧
      ∀ w : TangentSpace 𝓘(ℝ, E3) x,
        ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap_BAUGP P P.zero) x w -
          fderiv ℝ (tcpModelGraph_BAUGP P P.zero i S Se Ac cc A1 c1 Bτ cτ)
            (cgpCircleCoord_BAUGP P i hi x)
            (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord_BAUGP P i hi) x w)‖ ≤
          Real.sqrt ((tcpModelActive_BAUGP P P.zero S Se).card : ℝ) *
            (tcpTagBudget θ Δ Λ * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w)) := by
  set η := cgpCircleCoord_BAUGP P i hi with hη
  have hb := tcpTagBudget_nonneg_KA7 hθ hΔ hΛ
  have hηb : ∀ w, ‖mvfderiv 𝓘(ℝ, E3) η x w‖ ≤ 2 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) :=
    fun w => norm_mvfderiv_circleCoord_le_KA6_BAUGP P hi hxi w
  have hVs := contMDiffAt_tcpEdgeActual_KA7_BAUGP P Se τf hτ.1
    (fun k hk => (hE ⟨k, hk⟩).2.2.1)
  have hV : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, EuclideanSpace ℝ (Option Se))
      (tcpEdgeActual_BAUGP P Se τf) x := hVs.mdifferentiableAt (by simp)
  obtain ⟨hcv, hcd, hcb⟩ := tcp_edgeActual_compare_KA7_BAUGP P P.zero Se τf A1 c1 Bτ
    cτ η _ (fun w => Real.sqrt_nonneg _) hθ hV (fun k => ⟨(hE k).2.2.2.1, (hE k).2.2.2.2⟩)
    ⟨hτ.2.2.1, hτ.2.2.2⟩ (fun k => (hE k).2.1) hτ.2.1 hηb
  have hs : ∀ k : Se, ρ k.1.1 / ρ i ∈ Icc (1 / 2 : ℝ) 2 := fun k => (hE k).1
  refine block_assembly_KA7 hF (fun t => (contDiff_tcpModelComponent_BAUGP P P.zero
    i S Se Ac cc A1 c1 Bτ cτ t).differentiable (by simp)) η (ρ i)
    (tcpModelActive_BAUGP P P.zero S Se) hb _ (fun w => Real.sqrt_nonneg _)
    (fun t ht => ?_) (fun t ht => ?_)
  · rcases t with j | j | j | k | q
    · by_cases hji : j.1 = i
      · exact tcp05_own_case_KA7_BAUGP P hi S Se Ac cc A1 c1 Bτ cτ hθ hΔ hΛ j hji hxi h8
      · have hjS : (.inl j : CGPTag_BAUGP P P.zero) ∈ S := by
          simpa [tcpModelActive_BAUGP] using ht
        obtain ⟨h1, h2, h3, h4, h5⟩ := hC j hji hjS
        exact tcp05_circle_case_KA7_BAUGP P hi S Se Ac cc A1 c1 Bτ cτ hθ hΔ hΛ j hji hjS hxi h1 h2
            h3
          h4 h5
    · have hjS : (.inr (.inl j) : CGPTag_BAUGP P P.zero) ∈ S := by
        simpa [tcpModelActive_BAUGP] using ht
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hS j hjS
      exact tcp05_slim_case_KA7_BAUGP P hi S Se Ac cc A1 c1 Bτ cτ hθ hΔ hΛ j hjS hxi h1 h2 h3 h4 h5
          h6
    · have hj : j ∈ Se := by
        have h := ht
        simp only [tcpModelActive_BAUGP, Finset.mem_union, Finset.mem_image, Finset.mem_insert,
          Finset.mem_singleton] at h
        rcases h with (h | ⟨a, ha, hae⟩) | h
        · exact (hSe j h).elim
        · cases hae
          exact ha
        · rcases h with h | h <;> cases h
      exact tcp05_edge_case_KA7_BAUGP P hi S Se Ac cc A1 c1 Bτ cτ τf hθ hΔ hΛ j hj hx hcut hs hcard
          hV
        hcv hcd hcb
    · have hkS : (.inr (.inr (.inr (.inl k))) : CGPTag_BAUGP P P.zero) ∈ S := by
        simpa [tcpModelActive_BAUGP] using ht
      obtain ⟨h1, h2, h3, h4, h5⟩ := hZ k hkS
      exact tcp05_zero_case_KA7_BAUGP P hi S Se Ac cc A1 c1 Bτ cτ hθ hΔ hΛ k hkS hxi h1 h2 h3 h4 h5
    · cases q
      · exact tcp05_scale_case_KA7_BAUGP P hi S Se Ac cc A1 c1 Bτ cτ hθ hΔ hΛ hx
      · exact tcp05_marker_case_KA7_BAUGP P hi S Se Ac cc A1 c1 Bτ cτ τf hθ hθ1 hΔ hΛ hx hcut hoff
          hτm
          hs hcard hV hcv hcd hcb
  · refine tcp05_off_case_KA7_BAUGP P hi S Se Ac cc A1 c1 Bτ cτ hown t ht ?_
    rcases t with j | j | j | k | q
    · have hji : j.1 ≠ i := fun h => ht (by
        simp only [tcpModelActive_BAUGP, Finset.mem_union]
        exact Or.inl (Or.inl (hown j h)))
      have hjS : (.inl j : CGPTag_BAUGP P P.zero) ∉ S := fun h => ht (by
        simp only [tcpModelActive_BAUGP, Finset.mem_union]
        exact Or.inl (Or.inl h))
      exact hunlC j hji hjS
    · have hjS : (.inr (.inl j) : CGPTag_BAUGP P P.zero) ∉ S := fun h => ht (by
        simp only [tcpModelActive_BAUGP, Finset.mem_union]
        exact Or.inl (Or.inl h))
      exact hunlS j hjS
    · have hj : j ∉ Se := fun h => ht (by
        simp only [tcpModelActive_BAUGP, Finset.mem_union]
        exact Or.inl (Or.inr (Finset.mem_image_of_mem _ h)))
      rw [notMem_tsupport_iff_eventuallyEq]
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact hoff y hy j hj
    · have hkS : (.inr (.inr (.inr (.inl k))) : CGPTag_BAUGP P P.zero) ∉ S :=
        fun h => ht (by
          simp only [tcpModelActive_BAUGP, Finset.mem_union]
          exact Or.inl (Or.inl h))
      exact hunlZ k hkS
    · exfalso
      apply ht
      simp only [tcpModelActive_BAUGP, Finset.mem_union]
      right
      cases q <;> simp [cgpScaleTag_BAUGP, cgpEdgeTag_BAUGP]

end Point


end DifferentialGeometry.Geometry.Collapse
