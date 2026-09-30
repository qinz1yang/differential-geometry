import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticWitness

set_option autoImplicit false
noncomputable section
open Set Function Bundle Manifold TopologicalSpace DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Topology
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Metric DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology.Manifold.Attachment DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev Cap := {x : E3 // ‖x‖ ≤ transitionEnd}
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩
private local instance : ChartedSpace (EuclideanHalfSpace 3) Cap := closedBallChartedSpace transitionEnd_pos
private local instance : IsManifold (𝓡∂ 3) ∞ Cap := closedBall_isManifold transitionEnd_pos
private local instance quotientChartedSpace {B : ℝ} {hB : 0 < B} :
    ChartedSpace E3 (InsertionQuotient hB) := radialCapAttachmentChartedSpace transitionEnd_pos hB
private local instance quotientIsManifold {B : ℝ} {hB : 0 < B} :
    IsManifold (𝓡 3) ∞ (InsertionQuotient hB) := radialCapAttachment_isManifold transitionEnd_pos hB
private local instance quotientT2Space {B : ℝ} {hB : 0 < B} :
    T2Space (InsertionQuotient hB) := radialCapAttachment_t2Space transitionEnd_pos hB
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}

structure StaticInsertionAdditionalProperties (C : ℕ → ℝ)
    {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {D : ℝ} {m : ℕ} {ε : ℝ}
    (w : CanonicalStaticInsertionWitness d A hA D m ε) : Prop where
  deep_metric : ∀ (x : Cap), x.val ∈ deepRegion A → ∀ v u : TangentSpace (𝓡∂ 3) x,
    (scaleMetric (metricScalarAt g x₀) d.scalar_pos w.data.outMetric).inner (w.data.capMap x)
      (mfderiv (𝓡∂ 3) (𝓡 3) w.data.capMap x v) (mfderiv (𝓡∂ 3) (𝓡 3) w.data.capMap x u) =
    (1 - Real.sqrt δ) * metric.inner x.val
      (mfderiv (𝓡∂ 3) (𝓡 3) (Subtype.val : Cap → E3) x v)
      (mfderiv (𝓡∂ 3) (𝓡 3) (Subtype.val : Cap → E3) x u)
  positive_region : ∀ (x : Cap), x.val ∈ positiveRegion A →
    ∀ u v : TangentSpace (𝓡 3) (w.data.capMap x),
      w.data.outMetric.inner (w.data.capMap x) u u * w.data.outMetric.inner (w.data.capMap x) v v -
        w.data.outMetric.inner (w.data.capMap x) u v ^ 2 ≠ 0 →
      0 < sectionalCurvature w.data.outMetric (w.data.capMap x) u v
  hamiltonIvey : ∀ a : ℝ, 0 < a →
    (∀ q : openCylinder δ⁻¹,
      (metricScalarAt g (d.controlledMap q),
        2 * leastCurvatureOperatorEigenvalueAt g (d.controlledMap q)
          (metricAlgebraicCurvatureTensorAt g (d.controlledMap q))) ∈ fixedHamiltonIveyRegion a) →
    ∀ x, (metricScalarAt w.data.outMetric x,
      2 * leastCurvatureOperatorEigenvalueAt w.data.outMetric x
        (metricAlgebraicCurvatureTensorAt w.data.outMetric x)) ∈ fixedHamiltonIveyRegion a
  scalar_floor : ∀ L₀ : ℝ, L₀ ≤ 0 →
    (∀ q : openCylinder δ⁻¹, L₀ ≤ metricScalarAt g (d.controlledMap q)) →
    ∀ x, L₀ ≤ metricScalarAt w.data.outMetric x
  scalar_positive : ∀ x, 0 < metricScalarAt w.data.outMetric x
  cap_derivatives : ∀ x ∈ range w.data.capMap, ∀ j ≤ m,
    Real.sqrt (normSq0S w.data.outMetric x (4 + j) (iterCov w.data.outMetric 4 (metricRm04 w.data.outMetric) j x)) ≤
      C j * (metricScalarAt g x₀) ^ (1 + (j : ℝ) / 2)
  cap_scalar : ∀ x ∈ range w.data.capMap,
    0 < metricScalarAt w.data.outMetric x ∧ metricScalarAt w.data.outMetric x ≤ C 0 * metricScalarAt g x₀

theorem exists_staticInsertion_with_additional_properties :
    ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧ ∃ (A : ℝ) (hA : 0 < A), 2 * A < 1 / 2 ∧
      ∀ (D : ℝ), 0 < D → ∀ (m : ℕ) (ε : ℝ), 0 < ε →
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 / 2 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M],
        ∀ (g : SmoothRiemannianMetric I M) (x₀ : M) (d : normalizedDatum g x₀ δ (m + 4)),
          ∃ w : CanonicalStaticInsertionWitness d A hA D m ε,
            StaticInsertionAdditionalProperties C w := by
  obtain ⟨C, hC, A, hA, hsmall, hmod⟩ := exists_uniform_positiveCoordinate_static_estimates
  refine ⟨C, hC, A, hA, hsmall, ?_⟩
  intro D hD m ε hε
  obtain ⟨δ₀, hδ₀, hhalf, hb⟩ := hmod D hD m ε hε
  refine ⟨δ₀, hδ₀, hhalf, ?_⟩
  intro δ hδ hle
  obtain ⟨hAB, hfit, htip, hbound⟩ := hb δ hδ hle
  intro E H M _ _ _ _ _ I _ _ _ _ _ g x₀ d
  obtain ⟨hclose, hR, hHI, hder⟩ := hbound g x₀ d.oriented
  let w := canonicalStaticInsertionWitness d A hA D hD m ε hAB hfit htip hclose
  refine ⟨w, ?_⟩
  refine
    { deep_metric := normalizedDatum_positiveSideInsertionMetric_fixed_deep d.oriented hA hAB
      positive_region := ?_
      hamiltonIvey := ?_
      scalar_floor := fun L₀ hL₀ _ x => hL₀.trans (hR x).le
      scalar_positive := hR
      cap_derivatives := fun x hx => (hder x hx).1
      cap_scalar := fun x hx => ⟨hR x, (le_abs_self _).trans (hder x hx).2⟩ }
  · intro x hx u v hplane
    have he := normalizedDatum_positiveSideInsertionMetric_fixed_positive_sectional d.oriented hA hAB x hx u v hplane
    exact (div_pos d.scalar_pos
      (mul_pos (by norm_num) d.oriented.controlledMetric_cylinder_lower.1)).trans_eq he.symm
  · intro a ha hin
    apply hHI a ha
    intro q
    have he := d.oriented_controlledMap q
    rw [he]
    exact hin _
end DifferentialGeometry.PDE.RicciFlow.StandardCap
