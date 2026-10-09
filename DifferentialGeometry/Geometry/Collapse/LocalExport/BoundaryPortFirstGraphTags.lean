import DifferentialGeometry.Geometry.Fibration.ActualFirstGraphTags
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
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortFirstGraphModel
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortGlobalBlockMapBridge
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortRawAlignment
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortRetainedMarkerCloud
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortSupportRows
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortZeroMeeting
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAffineHeight
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryWholeSupportCount
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryReplacementStrictBCF2K

/-!
# Boundary port (lane B-PORT-A): ActualFirstGraphTags (circle-stage closure)

GENERATED from `DifferentialGeometry/Geometry/Fibration/ActualFirstGraphTags.lean` by
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
local instance instContinuousSMulPlaneBlock_KA6T_BAUGP : ContinuousSMul ℝ (WithLp 2 (ℝ² × ℝ)) :=
  IsBoundedSMul.continuousSMul

section Profiles

end Profiles

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}
  {vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricN_TCP05_KA6_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedN_TCP05_KA6_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricC_TCP05_KA6_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- The circle coordinate has `‖dη_i(w)‖ ≤ 2|w|` on `B(i, 200R)` (`|w|` of `R⁻²g`). -/
theorem norm_mvfderiv_circleCoord_le_KA6_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    {i : X} (hi : i ∈ P.circle.centres) {x : X} (hx : x ∈ ball i (200 * ρ i))
    (w : TangentSpace 𝓘(ℝ, E3) x) :
    ‖mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord_BAUGP P i hi) x w‖ ≤
      2 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) := by
  have hri := hρ i
  have hd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) (cgpCircleCoord_BAUGP P i hi) x :=
    ((cgpCircleCoord_contMDiffOn_BAUGP P hi).contMDiffAt
      (isOpen_ball.mem_nhds hx)).mdifferentiableAt (by simp)
  have h := norm_mvfderiv_le_of_lipschitzOn_riem g hmetric isOpen_ball hx hd (by positivity)
    (cgpCircleCoord_lipschitz_BAUGP P hi) w
  have hsq : Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) = (ρ i)⁻¹ * Real.sqrt (g.inner x w w) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (inv_pos.mpr hri).le]
  rw [hsq]
  calc _ ≤ 2 / ρ i * Real.sqrt (g.inner x w w) := h
    _ = 2 * ((ρ i)⁻¹ * Real.sqrt (g.inner x w w)) := by ring

/-- A circle block of `𝓔⁰` where its cutoff is `ψ ∘ η_j`:
`R • scaledCutoffBlock s_j ψ (s_j η_j)`. -/
theorem cgpGlobalMap_circle_eq_KA6_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (j : P.circle.finite_centres.toFinset) {R : ℝ} (hR : 0 < R) {y : X}
    (hy : P.circle.cutoff j.1 y = circleCutoffBump_LC87
      (cgpCircleCoord_BAUGP P j.1 ((Set.Finite.mem_toFinset _).mp j.2) y)) :
    cgpGlobalMap_BAUGP P P.zero y (.inl j) =
      R • scaledCutoffBlock (ρ j.1 / R) (circleCutoffBump_LC87 : ℝ² → ℝ)
        ((ρ j.1 / R) • cgpCircleCoord_BAUGP P j.1
          ((Set.Finite.mem_toFinset _).mp j.2) y) := by
  have hrj := hρ j.1
  set η := cgpCircleCoord_BAUGP P j.1 ((Set.Finite.mem_toFinset _).mp j.2) y
    with hη
  have hs : ρ j.1 / R ≠ 0 := (div_pos hrj hR).ne'
  change WithLp.toLp 2 ((ρ j.1 * P.circle.cutoff j.1 y) • η, ρ j.1 * P.circle.cutoff j.1 y) = _
  have hinv : (ρ j.1 / R)⁻¹ • (ρ j.1 / R) • η = η := by
    rw [smul_smul, inv_mul_cancel₀ hs, one_smul]
  have hR0 : R ≠ 0 := hR.ne'
  have e1 : R * circleCutoffBump_LC87 η * (ρ j.1 / R) = ρ j.1 * circleCutoffBump_LC87 η := by
    field_simp
  have e2 : R * (ρ j.1 / R * circleCutoffBump_LC87 η) = ρ j.1 * circleCutoffBump_LC87 η := by
    field_simp
  have hsm : ∀ (c : ℝ) (u : ℝ²) (t : ℝ),
      c • (WithLp.toLp 2 (u, t) : WithLp 2 (ℝ² × ℝ)) = WithLp.toLp 2 (c • u, c * t) :=
    fun c u t => rfl
  rw [hy, scaledCutoffBlock, hinv, hsm, smul_smul, smul_smul, e1, e2]

/-- **(TG) for a listed circle block** at a point `x` of `B(j, 200ρ(j)) ∩ B(i, 200R)`: from
TCP03's comparison `‖s_jη_j − Aη_i − c‖ ≤ ε`, `‖s_j dη_j − A dη_i‖ ≤ ε|·|` (`‖A‖ ≤ 1`,
`s_j ∈ [1/2, 2]`) against the model block `scaledCutoffBlock s_j ψ (A a + c)`. -/
theorem tg_circle_tag_KA6_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    {i : X} (hi : i ∈ P.circle.centres) (j : P.circle.finite_centres.toFinset) {x : X}
    (hxj : x ∈ ball j.1 (200 * ρ j.1)) (hxi : x ∈ ball i (200 * ρ i))
    (hs : ρ j.1 / ρ i ∈ Icc (1 / 2 : ℝ) 2) (A : ℝ² →L[ℝ] ℝ²) (hA : ‖A‖ ≤ 1) (c : ℝ²) {ε₀ : ℝ}
    (hval : ‖(ρ j.1 / ρ i) • cgpCircleCoord_BAUGP P j.1
        ((Set.Finite.mem_toFinset _).mp j.2) x - A (cgpCircleCoord_BAUGP P i hi x) -
        c‖ ≤ ε₀)
    (hder : ∀ w : TangentSpace 𝓘(ℝ, E3) x,
      ‖(ρ j.1 / ρ i) • mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord_BAUGP P j.1
          ((Set.Finite.mem_toFinset _).mp j.2)) x w -
        A (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord_BAUGP P i hi) x w)‖ ≤
        ε₀ * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w)) :
    ‖(ρ i)⁻¹ • cgpGlobalMap_BAUGP P P.zero x (.inl j) -
        scaledCutoffBlock (ρ j.1 / ρ i) (circleCutoffBump_LC87 : ℝ² → ℝ)
          (A (cgpCircleCoord_BAUGP P i hi x) + c)‖ ≤
        50 * (tcpProfileBound + 1) * ε₀ ∧
      ∀ w : TangentSpace 𝓘(ℝ, E3) x,
        ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3)
            (fun y => cgpGlobalMap_BAUGP P P.zero y (.inl j)) x w -
          fderiv ℝ (fun a => scaledCutoffBlock (ρ j.1 / ρ i) (circleCutoffBump_LC87 : ℝ² → ℝ)
            (A a + c)) (cgpCircleCoord_BAUGP P i hi x)
            (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord_BAUGP P i hi) x w)‖ ≤
          (50 * (tcpProfileBound + 1) + 50 * (tcpProfileBound + 1) * 2) * ε₀ *
            Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) := by
  have hri := hρ i
  have hj := (Set.Finite.mem_toFinset _).mp j.2
  set sj := ρ j.1 / ρ i with hsj
  set ηj := cgpCircleCoord_BAUGP P j.1 hj with hηj
  set ηi := cgpCircleCoord_BAUGP P i hi with hηi
  have hf : (fun y => cgpGlobalMap_BAUGP P P.zero y (.inl j)) =ᶠ[𝓝 x]
      fun y => ρ i • scaledCutoffBlock sj (circleCutoffBump_LC87 : ℝ² → ℝ) (sj • ηj y) := by
    filter_upwards [circle_cutoff_eventuallyEq_KA2_BAUGP P hj
      hxj] with y hy
    exact cgpGlobalMap_circle_eq_KA6_BAUGP P j hri hy
  have hηd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) ηj x :=
    ((cgpCircleCoord_contMDiffOn_BAUGP P hj).contMDiffAt
      (isOpen_ball.mem_nhds hxj)).mdifferentiableAt (by simp)
  have hV : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) (fun y => sj • ηj y) x := hηd.const_smul sj
  have hdV : ∀ w : TangentSpace 𝓘(ℝ, E3) x,
      mvfderiv 𝓘(ℝ, E3) (fun y => sj • ηj y) x w = sj • mvfderiv 𝓘(ℝ, E3) ηj x w := fun w =>
    mvfderiv_comp_hasFDerivAt hηd (sj • ContinuousLinearMap.id ℝ ℝ²).hasFDerivAt w
  have hb := circle_scaledBlock_bounds_KA6 hs
  refine tg_block_pointwise_KA6 (I := 𝓘(ℝ, E3))
    (contDiff_scaledCutoffBlock circleCutoffBump_LC87.contDiff sj) (fun y => (hb y).1)
    (fun y => (hb y).2) hri.ne' hf hV ηi A c (fun w => Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w))
    ?_ (fun w => ?_) (fun w => ?_)
  · rw [← sub_sub]
    exact hval
  · rw [hdV]
    exact hder w
  · refine (A.le_opNorm _).trans ?_
    have h2 := norm_mvfderiv_circleCoord_le_KA6_BAUGP P hi hxi w
    calc ‖A‖ * ‖mvfderiv 𝓘(ℝ, E3) ηi x w‖ ≤ 1 * (2 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w)) :=
          mul_le_mul hA h2 (norm_nonneg _) zero_le_one
      _ = 2 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) := one_mul _

/-- A slim block of `𝓔⁰` where its cutoff is `f(η_j/(10⁵Δ))`:
`R • blockLift (sgpModelBlock (10⁵Δ) s_j (s_j η_j))`. -/
theorem cgpGlobalMap_slim_eq_KA6_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (j : P.slim.finite_centres.toFinset) {R : ℝ} (hR : 0 < R) (hΔ : 0 < Δ) {y : X}
    (hy : P.slim.cutoff_BCNT j.1 y = slimCutoffProfile_LC87
      ((P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord_BCG2 y / (10 ^ 5 * Δ))) :
    cgpGlobalMap_BAUGP P P.zero y (.inr (.inl j)) =
      R • blockLift_KC3 (sgpModelBlock (10 ^ 5 * Δ) (ρ j.1 / R)
        (ρ j.1 / R * (P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord_BCG2 y)) := by
  have hrj := hρ j.1
  set η := (P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord_BCG2 y with hη
  have hs : ρ j.1 / R ≠ 0 := (div_pos hrj hR).ne'
  change WithLp.toLp 2 ((ρ j.1 * P.slim.cutoff_BCNT j.1 y) • planeAxis η,
    ρ j.1 * P.slim.cutoff_BCNT j.1 y) = _
  have hq : ρ j.1 / R * η / (ρ j.1 / R * (10 ^ 5 * Δ)) = η / (10 ^ 5 * Δ) := by
    field_simp
  rw [hy, sgpModelBlock_apply, hq, scalar_block_eq_KA6 R _ _ η hR.ne']

/-- A zero block of `𝓔⁰`: `R • blockLift (zeroModelBlock s₀ (s₀ η₀))`, `s₀ = R₀/R`. -/
theorem cgpGlobalMap_zero_eq_KA6_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (k : P.zero.finite_centres.toFinset) {R : ℝ} (hR : 0 < R) (y : X) :
    cgpGlobalMap_BAUGP P P.zero y (.inr (.inr (.inr (.inl k)))) =
      R • blockLift_KC3 (zeroModelBlock
        ((P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / R)
        ((P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / R *
          (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial y)) := by
  set Zb := P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2) with hZb
  have hr := Zb.radius_pos
  set η := Zb.radial y with hη
  have hs : Zb.radius / R ≠ 0 := (div_pos hr hR).ne'
  change WithLp.toLp 2 ((Zb.radius * annularCutoff cutoffProfile η) • planeAxis η,
    Zb.radius * annularCutoff cutoffProfile η) = _
  have hq : (Zb.radius / R)⁻¹ * (Zb.radius / R * η) = η := by
    field_simp
  rw [zeroModelBlock_apply, hq, scalar_block_eq_KA6 R _ _ η hR.ne']


end DifferentialGeometry.Geometry.Collapse
