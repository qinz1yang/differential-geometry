import DifferentialGeometry.Geometry.Measure.Area.SpanningCompetitors








noncomputable section

open Manifold Set DifferentialGeometry
open DifferentialGeometry.Topology
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M]



def lipschitzContractibleLoop (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) :=
  {γ : contractibleLoop M // ∃ L : ℝ≥0, ∀ s t,
    riemannianEDistOf g (γ.val s) (γ.val t) ≤ (L : ℝ≥0∞) * edist s t}


def spanningDiskAreas (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : lipschitzContractibleLoop g) : Set ℝ :=
  (fun u : C(closedDisk, M) => riemannianDiskArea g u) '' spanningDiskCompetitors g γ.val.val


theorem spanningDiskAreas_nonempty [Nonempty M] [PreconnectedSpace M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : lipschitzContractibleLoop g) :
    (spanningDiskAreas g γ).Nonempty := by
  obtain ⟨L, hL⟩ := γ.property
  exact (spanningDiskCompetitors_nonempty g hL γ.val.property).image _

omit [CompactSpace M] [T3Space M] [FiniteDimensional ℝ E] in
theorem spanningDiskAreas_bddBelow (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : lipschitzContractibleLoop g) : BddBelow (spanningDiskAreas g γ) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨u, _, rfl⟩
  exact riemannianDiskArea_nonneg g u



def leastSpanningArea (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : lipschitzContractibleLoop g) : ℝ := sInf (spanningDiskAreas g γ)

theorem leastSpanningArea_isGLB [Nonempty M] [PreconnectedSpace M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : lipschitzContractibleLoop g) :
    IsGLB (spanningDiskAreas g γ) (leastSpanningArea g γ) :=
  isGLB_csInf (spanningDiskAreas_nonempty g γ) (spanningDiskAreas_bddBelow g γ)

theorem leastSpanningArea_nonneg [Nonempty M] [PreconnectedSpace M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : lipschitzContractibleLoop g) :
    0 ≤ leastSpanningArea g γ := by
  apply le_csInf (spanningDiskAreas_nonempty g γ)
  rintro _ ⟨u, _, rfl⟩
  exact riemannianDiskArea_nonneg g u

omit [CompactSpace M] [T3Space M] [FiniteDimensional ℝ E] in
theorem leastSpanningArea_le_competitor (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : lipschitzContractibleLoop g) {u : C(closedDisk, M)}
    (hu : u ∈ spanningDiskCompetitors g γ.val.val) :
    leastSpanningArea g γ ≤ riemannianDiskArea g u :=
  csInf_le (spanningDiskAreas_bddBelow g γ) ⟨u, hu, rfl⟩



theorem exists_spanningDisk_area_lt [Nonempty M] [PreconnectedSpace M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : lipschitzContractibleLoop g)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ u ∈ spanningDiskCompetitors g γ.val.val,
      riemannianDiskArea g u < leastSpanningArea g γ + ε := by
  obtain ⟨a, ⟨u, hu, rfl⟩, ha⟩ := exists_lt_of_csInf_lt (spanningDiskAreas_nonempty g γ)
    (show leastSpanningArea g γ < leastSpanningArea g γ + ε by linarith)
  exact ⟨u, hu, ha⟩


def constantLipschitzContractibleLoop (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (q : M) :
    lipschitzContractibleLoop g :=
  ⟨ContractibleLoop.constants q, 0, fun _ _ => by
    simp only [ContractibleLoop.constants_apply, riemannianEDistOf_self, ENNReal.coe_zero, zero_mul, le_refl]⟩


theorem leastSpanningArea_constant [Nonempty M] [PreconnectedSpace M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (q : M) :
    leastSpanningArea g (constantLipschitzContractibleLoop g q) = 0 := by
  apply le_antisymm _ (leastSpanningArea_nonneg g _)
  have hu : ContinuousMap.const closedDisk q ∈ spanningDiskCompetitors g
      (constantLipschitzContractibleLoop g q).val.val := by
    refine ⟨rfl, 0, fun z w => ?_⟩
    simp only [ContinuousMap.const_apply, riemannianEDistOf_self, ENNReal.coe_zero, zero_mul, le_refl]
  have h := leastSpanningArea_le_competitor g (constantLipschitzContractibleLoop g q) hu
  change leastSpanningArea g (constantLipschitzContractibleLoop g q) ≤
    riemannianDiskArea g (fun _ => q) at h
  rw [riemannianDiskArea_const] at h
  exact h

end DifferentialGeometry.Geometry
