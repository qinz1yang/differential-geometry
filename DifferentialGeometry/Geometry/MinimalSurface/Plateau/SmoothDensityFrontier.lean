import DifferentialGeometry.Geometry.MinimalSurface.Plateau.ExactAttainment
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SpanningDiskAreaDensity

noncomputable section

open Bundle Manifold DifferentialGeometry Set ContinuousMap Filter
open DifferentialGeometry.Topology
open scoped Bundle Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T3Space M] [CompactSpace M]

omit [FiniteDimensional ℝ E] [T3Space M] [CompactSpace M] in
theorem exists_smoothDiskExtension_area_approximation_of_tendsto
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M} {v : C(closedDisk, M)}
    {vj : ℕ → C(closedDisk, M)} {Uj : ℕ → ℂ → M}
    (hsm : ∀ j, SmoothDiskExtension (E := E) (vj j) (Uj j))
    (htr : ∀ j, diskTrace (vj j) = γ)
    (ht : Tendsto (fun j => riemannianDiskArea g (vj j)) atTop (𝓝 (riemannianDiskArea g v))) :
    ∀ ε : ℝ, 0 < ε → ∃ (w : C(closedDisk, M)) (W : ℂ → M),
      SmoothDiskExtension (E := E) w W ∧ diskTrace w = γ ∧
        |riemannianDiskArea g w - riemannianDiskArea g v| ≤ ε := by
  intro ε hε
  have hball : ∀ᶠ j in atTop, dist (riemannianDiskArea g (vj j)) (riemannianDiskArea g v) < ε :=
    ht.eventually (Metric.ball_mem_nhds _ hε)
  obtain ⟨j, hj⟩ := hball.exists
  refine ⟨vj j, Uj j, hsm j, htr j, ?_⟩
  rw [Real.dist_eq] at hj
  exact hj.le

omit [FiniteDimensional ℝ E] [T3Space M] [CompactSpace M] in
theorem exists_smoothDiskExtension_area_tendsto_of_smoothDiskExtension
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M} {v : C(closedDisk, M)} {V : ℂ → M}
    (hsm : SmoothDiskExtension (E := E) v V) (htr : diskTrace v = γ) :
    ∃ (vj : ℕ → C(closedDisk, M)) (Uj : ℕ → ℂ → M),
      (∀ j, SmoothDiskExtension (E := E) (vj j) (Uj j) ∧ diskTrace (vj j) = γ) ∧
      Tendsto (fun j => riemannianDiskArea g (vj j)) atTop (𝓝 (riemannianDiskArea g v)) :=
  ⟨fun _ => v, fun _ => V, fun _ => ⟨hsm, htr⟩, tendsto_const_nhds⟩

omit [FiniteDimensional ℝ E] [T3Space M] [CompactSpace M] in
theorem areaUpperApproximation_of_areaApproximation
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M}
    (happrox : ∀ v : C(closedDisk, M), v ∈ spanningDiskCompetitors g γ → ∀ ε : ℝ, 0 < ε →
      ∃ (w : C(closedDisk, M)) (W : ℂ → M),
        SmoothDiskExtension (E := E) w W ∧ diskTrace w = γ ∧
          |riemannianDiskArea g w - riemannianDiskArea g v| ≤ ε) :
    ∀ v : C(closedDisk, M), v ∈ spanningDiskCompetitors g γ → ∀ ε : ℝ, 0 < ε →
      ∃ (w : C(closedDisk, M)) (W : ℂ → M),
        SmoothDiskExtension (E := E) w W ∧ diskTrace w = γ ∧
          riemannianDiskArea g w ≤ riemannianDiskArea g v + ε := by
  intro v hv ε hε
  obtain ⟨w, W, hW, htr, habs⟩ := happrox v hv ε hε
  refine ⟨w, W, hW, htr, ?_⟩
  linarith [(abs_le.mp habs).2]

omit [FiniteDimensional ℝ E] [T3Space M] [CompactSpace M] in
theorem riemannianDiskArea_le_of_minimizingSmoothDisk_of_areaUpperApproximation
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M}
    (hupper : ∀ v : C(closedDisk, M), v ∈ spanningDiskCompetitors g γ → ∀ ε : ℝ, 0 < ε →
      ∃ (w : C(closedDisk, M)) (W : ℂ → M),
        SmoothDiskExtension (E := E) w W ∧ diskTrace w = γ ∧
          riemannianDiskArea g w ≤ riemannianDiskArea g v + ε)
    {u : C(closedDisk, M)}
    (hmin : ∀ w : C(closedDisk, M), DiskSmoothUpToBoundary (E := E) w → diskTrace w = γ →
      riemannianDiskArea g u ≤ riemannianDiskArea g w)
    {v : C(closedDisk, M)} (hv : v ∈ spanningDiskCompetitors g γ) :
    riemannianDiskArea g u ≤ riemannianDiskArea g v := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨w, W, hW, htr, hle⟩ := hupper v hv ε hε
  exact (hmin w hW.smoothUpToBoundary htr).trans hle

theorem IsConformalMinimizingDisk.area_eq_leastSpanningArea_of_areaUpperApproximation
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : lipschitzContractibleLoop g}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => γ.val.val (t : loopCircle)))
    (hupper : ∀ v : C(closedDisk, M), v ∈ spanningDiskCompetitors g γ.val.val →
      ∀ ε : ℝ, 0 < ε → ∃ (w : C(closedDisk, M)) (W : ℂ → M),
        SmoothDiskExtension (E := E) w W ∧ diskTrace w = γ.val.val ∧
          riemannianDiskArea g w ≤ riemannianDiskArea g v + ε)
    {u : C(closedDisk, M)} {σ : C(loopCircle, loopCircle)} {U : ℂ → M}
    (h : IsConformalMinimizingDisk g γ.val.val u σ U) :
    riemannianDiskArea g u = leastSpanningArea g γ := by
  obtain ⟨v, hv, harea⟩ :=
    exists_spanning_disk_competitor_area_eq_of_smooth_positive_trace g hγ
      h.positiveTrace h.trace (h.extension.lipschitz g)
  apply le_antisymm
  · apply le_csInf (show (spanningDiskAreas g γ).Nonempty from ⟨_, v, hv, rfl⟩)
    rintro _ ⟨w, hw, rfl⟩
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨w', W', hW', htr', hle'⟩ := hupper w hw ε hε
    exact (h.minimizesSmooth w' hW'.smoothUpToBoundary htr').trans hle'
  · exact harea ▸ leastSpanningArea_le_competitor g γ hv

omit [FiniteDimensional ℝ E] [T3Space M] [CompactSpace M] in
theorem areaUpperApproximation_constantLipschitzContractibleLoop
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (q : M) :
    ∀ v : C(closedDisk, M),
      v ∈ spanningDiskCompetitors g (constantLipschitzContractibleLoop g q).val.val →
        ∀ ε : ℝ, 0 < ε → ∃ (w : C(closedDisk, M)) (W : ℂ → M),
          SmoothDiskExtension (E := E) w W ∧
            diskTrace w = (constantLipschitzContractibleLoop g q).val.val ∧
              riemannianDiskArea g w ≤ riemannianDiskArea g v + ε := by
  intro v _hv ε hε
  refine ⟨ContinuousMap.const closedDisk q, fun _ => q, ⟨fun _ => rfl, univ, isOpen_univ,
    subset_univ _, contMDiffOn_const⟩, rfl, ?_⟩
  change riemannianDiskArea g (fun _ : closedDisk => q) ≤ riemannianDiskArea g v + ε
  rw [riemannianDiskArea_const]
  linarith [riemannianDiskArea_nonneg g v, hε.le]

end DifferentialGeometry.Geometry
