import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ConeEndRayScalarBound
import DifferentialGeometry.Geometry.Comparison.RadialHessianLowerBound

/-!
# CH12-O39, group 2: B3 in cone-end form — the tree's punctured-cone end along a neck ray

`[FROZEN v2] CH12-O39 B3` (finding D4): the cone structure that the cone exclusion
(`rescaled_end_cone_exclusion`, `final_slab_punctured_cone_end_exclusion`) consumes is the tree's
punctured-cone end data (`PuncturedConeApproximation` at the completion point, compact punctured
closed ball, points `x n → q_W` with `c ≤ R d² ≤ B`).  `cone_end_of_ray_necks_O39` produces it from
the B1 + B2 data in O38's form (`Rm ≥ 0` as `SectionalBoundedBelowAt gL · 0`, the unit-speed ray
`γ` on `[0, ρ)` written with `riemannianEDistOf`, `R(γ t) → ∞` as `t → ρ⁻`, spatial necks along
`[t₀, ρ)`), on a limit carrying a metric-space structure with `edist = riemannianEDistOf gL`;
the completion point `q` is constructed (Cauchy ray).  Proof: the tree theorem
`exists_punctured_cone_end_of_spatial_necks_with_ray_scalar_bound` (ConeEndRayScalarBound.lean).
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian Set Filter Topology
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

/-- **B3 (cone-end form) from B1 + B2 data.** -/
theorem cone_end_of_ray_necks_O39
    {M : Type u} [MetricSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    (gL : SmoothRiemannianMetric I3 M)
    (hmetric : ∀ x y : M, edist x y = riemannianEDistOf gL x y)
    (hsec0 : ∀ x : M, SectionalBoundedBelowAt gL x 0)
    {ρ : ℝ} (hρ : 0 < ρ) (γ : ℝ → M)
    (hiso : ∀ t₁ ∈ Ico (0 : ℝ) ρ, ∀ t₂ ∈ Ico (0 : ℝ) ρ,
      riemannianEDistOf gL (γ t₁) (γ t₂) = ENNReal.ofReal |t₁ - t₂|)
    (hblow : Tendsto (fun t => metricScalarAt gL (γ t)) (𝓝[<] ρ) atTop)
    {alpha : ℝ} (ha : 0 < alpha) (hsmall : alpha < 1 / 2000000)
    {t₀ : ℝ} (ht₀ : t₀ < ρ) (hnecks : ∀ t ∈ Ico t₀ ρ, Nonempty (SpatialNeck gL alpha (γ t))) :
    ∃ g : C(Ico (0 : ℝ) ρ, M), (∀ t : Ico (0 : ℝ) ρ, g t = γ t) ∧
    ∃ q : UniformSpace.Completion M,
    Tendsto (fun t => (g t : UniformSpace.Completion M))
      (comap (Subtype.val : Ico (0 : ℝ) ρ → ℝ) (𝓝 ρ)) (𝓝 q) ∧
          ∃ W : TopologicalSpace.Opens M, ∃ hW : PathConnectedSpace W,
          let _ : PathConnectedSpace W := hW
          let mW : MetricSpace W :=
            let _ : PseudoMetricSpace W := (gL.restrictOpen W).toPseudoMetricSpace
            MetricSpace.ofT0PseudoMetricSpace W
          let _ : MetricSpace W := mW
          let _ : PseudoMetricSpace W := mW.toPseudoMetricSpace
          let _ : UniformSpace W := mW.toPseudoMetricSpace.toUniformSpace
          let eW : PseudoEMetricSpace W :=
            @PseudoMetricSpace.toPseudoEMetricSpace W mW.toPseudoMetricSpace
          let _ : WeakPseudoEMetricSpace W :=
            @PseudoEMetricSpace.toWeakPseudoEMetricSpace W eW
          ∃ qW : UniformSpace.Completion W, ∃ delta : ℝ, 0 < delta ∧
            qW ∉ range (fun x : W => (x : UniformSpace.Completion W)) ∧
            UniformSpace.Completion.map (Subtype.val : W → M) qW = q ∧
            IsCompact (Metric.closedBall qW delta) ∧
            Metric.closedBall qW delta ⊆ insert qW
              (range (fun x : W => (x : UniformSpace.Completion W))) ∧
            ∃ x : ℕ → W, ∃ times : ℕ → Ico (0 : ℝ) ρ,
              (∀ n, (x n : M) = g (times n)) ∧
              Tendsto (fun n => (times n : ℝ)) atTop (𝓝 ρ) ∧
              Tendsto (fun n => (x n : UniformSpace.Completion W)) atTop (𝓝 qW) ∧
              (∀ n, dist (x n : UniformSpace.Completion W) qW = ρ - times n) ∧
              Tendsto (fun n => metricScalarAt (gL.restrictOpen W) (x n)) atTop atTop ∧
              (∀ n, ((2 * alpha)⁻¹) ^ 2 / 8 ≤
                metricScalarAt (gL.restrictOpen W) (x n) *
                  dist (x n : UniformSpace.Completion W) qW ^ 2) ∧
              (∃ B : ℝ, 0 < B ∧ ∀ᶠ n in atTop,
                metricScalarAt (gL.restrictOpen W) (x n) *
                  dist (x n : UniformSpace.Completion W) qW ^ 2 ≤ B) ∧
              Nonempty (DifferentialGeometry.Toponogov.PuncturedConeApproximation qW delta) ∧
              ∃ K : ℝ, 1 ≤ K ∧ ∀ᶠ n in atTop, ∀ s : Ico (0 : ℝ) ρ, (s : ℝ) ≤ times n →
                metricScalarAt gL (g s) ≤ K * metricScalarAt gL (g (times n))
 := by
  have hiso' : Isometry (fun t : Ico (0 : ℝ) ρ => γ t) := by
    refine Isometry.of_dist_eq ?_
    intro t₁ t₂
    have h := hiso t₁ t₁.2 t₂ t₂.2
    rw [← hmetric] at h
    rw [dist_edist, h, Subtype.dist_eq, Real.dist_eq, ENNReal.toReal_ofReal (abs_nonneg _)]
  let g : C(Ico (0 : ℝ) ρ, M) := ⟨fun t => γ t, hiso'.continuous⟩
  have hg : Isometry g := hiso'
  have hsec : ∀ (x : M) (v w : TangentSpace I3 x), 0 ≤ metricRm04StandardAt gL x v w w v := by
    intro x v w
    have h := hsec0 x v w
    simpa only [zero_mul] using h
  let L : Filter (Ico (0 : ℝ) ρ) := comap (Subtype.val : Ico (0 : ℝ) ρ → ℝ) (𝓝 ρ)
  have hval : Tendsto (Subtype.val : Ico (0 : ℝ) ρ → ℝ) L (𝓝[<] ρ) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_comap, Eventually.of_forall fun t => t.2.2⟩
  have hblow' : Tendsto (fun t => metricScalarAt gL (g t)) L atTop := hblow.comp hval
  have hρmem : ρ ∈ closure (Ico (0 : ℝ) ρ) := by
    rw [closure_Ico hρ.ne]
    exact ⟨hρ.le, le_rfl⟩
  have hLne : L.NeBot := mem_closure_iff_comap_neBot.mp hρmem
  have hLc : Cauchy L := by
    have h1 : Cauchy (map (Subtype.val : Ico (0 : ℝ) ρ → ℝ) L) :=
      (cauchy_nhds (a := ρ)).mono map_comap_le
    exact isUniformEmbedding_subtype_val.isUniformInducing.cauchy_map_iff.mp h1
  have huc : UniformContinuous (fun t : Ico (0 : ℝ) ρ => (g t : UniformSpace.Completion M)) :=
    (UniformSpace.Completion.uniformContinuous_coe M).comp hg.uniformContinuous
  obtain ⟨q, hq⟩ := CompleteSpace.complete (hLc.map huc)
  have hnecks' : ∀ᶠ tau : Ico (0 : ℝ) ρ in L, Nonempty (SpatialNeck gL alpha (g tau)) := by
    filter_upwards [preimage_mem_comap (Ioi_mem_nhds ht₀)] with tau htau
    exact hnecks tau ⟨le_of_lt htau, tau.2.2⟩
  exact ⟨g, fun t => rfl, q, hq,
    exists_punctured_cone_end_of_spatial_necks_with_ray_scalar_bound gL hmetric hρ ha hsmall
      hsec g hg hblow' q hq hnecks'⟩

end GC.LongTime.Ch12
