import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticPinchingInsertion

/-!
# Static pinching insertion at a general order (C12X)

`exists_staticInsertion_with_additional_properties` (StaticPinchingInsertion) takes its insertion
datum at the fixed order `m + 4`.  The underlying estimates (pinching, model-window error, cap
derivative bounds) already hold at every order `k` above their thresholds, so the same witness and
the same additional properties exist for every datum of order `k ≥ m + 4`, with the threshold `δ₀`
still depending only on `(D, m, ε)`.  This is step 1 of the S10 window-order parametrization.
-/

set_option autoImplicit false
noncomputable section
open Set Function Bundle Manifold TopologicalSpace DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Topology
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Topology.Manifold.Attachment
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩
private local instance quotientChartedSpace {B : ℝ} {hB : 0 < B} :
    ChartedSpace E3 (InsertionQuotient hB) := radialCapAttachmentChartedSpace transitionEnd_pos hB
private local instance quotientIsManifold {B : ℝ} {hB : 0 < B} :
    IsManifold (𝓡 3) ∞ (InsertionQuotient hB) :=
  radialCapAttachment_isManifold transitionEnd_pos hB
private local instance quotientT2Space {B : ℝ} {hB : 0 < B} :
    T2Space (InsertionQuotient hB) := radialCapAttachment_t2Space transitionEnd_pos hB

/-- `exists_uniform_positiveCoordinate_static_estimates` at every datum order `k ≥ m + 4`. -/
theorem exists_uniform_positiveCoordinate_static_estimates_order_C12X :
    ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧ ∃ (A : ℝ) (hA : 0 < A), 2 * A < 1 / 2 ∧
      ∀ (D : ℝ), 0 < D → ∀ (m : ℕ) (ε : ℝ), 0 < ε →
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 / 2 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        ∃ (hAB : 2 * A < δ⁻¹) (hfit : D + 1 ≤ transitionEnd + δ⁻¹),
          collapseTip A ∈ Ioo (-δ⁻¹) (-2 * A - transitionEnd) ∧
          ∀ (k : ℕ), m + 4 ≤ k →
          ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
            [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
            [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
            [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M],
            ∀ (g : SmoothRiemannianMetric I M) (x₀ : M) (d : normalizedDatum g x₀ δ k),
              let out := d.positiveSideInsertionMetric hA hAB
              metricDerivENormSupOn
                {x : modelWindow (D + 1) | (riemannianEDistOf metric 0 x.val).toReal < D} m
                (modelWindowPullback (inv_pos.mpr d.precision_pos) hfit
                  (scaleMetric (metricScalarAt g x₀) d.scalar_pos out))
                (metric.restrictOpen (modelWindow (D + 1)))
                (metric.restrictOpen (modelWindow (D + 1))) <
                ENNReal.ofReal ε ∧
              (∀ x, 0 < metricScalarAt out x) ∧
              (∀ a : ℝ, 0 < a →
                (∀ q : openCylinder δ⁻¹,
                  (metricScalarAt g (d.controlledMap q),
                    2 * leastCurvatureOperatorEigenvalueAt g (d.controlledMap q)
                      (metricAlgebraicCurvatureTensorAt g (d.controlledMap q))) ∈
                    fixedHamiltonIveyRegion a) →
                ∀ x, (metricScalarAt out x,
                  2 * leastCurvatureOperatorEigenvalueAt out x
                    (metricAlgebraicCurvatureTensorAt out x)) ∈
                  fixedHamiltonIveyRegion a) ∧
              ∀ q : InsertionQuotient (inv_pos.mpr d.precision_pos),
                q ∈ range (adjunctionCell (radialCapBoundary transitionEnd_pos)
                  (retainedBoundary (inv_pos.mpr d.precision_pos))) →
                (∀ j ≤ m, Real.sqrt (normSq0S out q (4 + j) (iterCov out 4 (metricRm04 out) j q)) ≤
                  C j * (metricScalarAt g x₀) ^ (1 + (j : ℝ) / 2)) ∧
                  |metricScalarAt out q| ≤ C 0 * metricScalarAt g x₀ := by
  obtain ⟨C, hC, hder⟩ := exists_normalizedDatum_positiveSideInsertionMetric_cap_derivative_bounds
  obtain ⟨A, hA, hAsmall, δp, hδp, hδphalf, hpin⟩ :=
    exists_normalizedDatum_positiveSideInsertionMetric_pinching
  refine ⟨C, hC, A, hA, hAsmall, ?_⟩
  intro D hD m ε hε
  obtain ⟨δw, hδw, _, hwin⟩ := exists_normalizedDatum_modelWindow_error_lt A hA D hD m ε hε
  obtain ⟨δc, hδc, _, hcurv⟩ := hder A hA m
  let δt := (2 * A + 5 * transitionEnd / 2 + 3)⁻¹
  have hδt : 0 < δt := inv_pos.mpr (by linarith [transitionEnd_pos])
  let δ₀ := min δp (min δw (min δc δt))
  have hδ₀ : 0 < δ₀ := lt_min hδp (lt_min hδw (lt_min hδc hδt))
  refine ⟨δ₀, hδ₀, (min_le_left _ _).trans_lt hδphalf, ?_⟩
  intro δ hδ hle
  have hp : δ ≤ δp := hle.trans (min_le_left _ _)
  have hw : δ ≤ δw := hle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hc : δ ≤ δc :=
    hle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have ht : δ ≤ δt :=
    hle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨hAB, hb⟩ := hpin δ hδ hp
  obtain ⟨_, hfit, hwbound⟩ := hwin δ hδ hw
  obtain ⟨_, hcbound⟩ := hcurv δ hδ hc
  refine ⟨hAB, hfit, collapseTip_mem_buffer hA hδ ht, ?_⟩
  intro k hk E H M _ _ _ _ _ I _ _ _ _ _ g x₀ d
  obtain ⟨hR, hHI⟩ := hb k (by omega) g x₀ d
  exact ⟨hwbound k (by omega) g x₀ d, hR, hHI, hcbound k (by omega) g x₀ d⟩

/-- `exists_staticInsertion_with_additional_properties` for every datum order `k ≥ m + 4`; the
constants `C`, `A` and the threshold `δ₀ = δ₀ (D, m, ε)` do not depend on `k`. -/
theorem exists_staticInsertion_with_additional_properties_order_C12X :
    ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧ ∃ (A : ℝ) (hA : 0 < A), 2 * A < 1 / 2 ∧
      ∀ (D : ℝ), 0 < D → ∀ (m : ℕ) (ε : ℝ), 0 < ε →
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 / 2 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ (k : ℕ), m + 4 ≤ k →
      ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M],
        ∀ (g : SmoothRiemannianMetric I M) (x₀ : M) (d : normalizedDatum g x₀ δ k),
          ∃ w : CanonicalStaticInsertionWitness d A hA D m ε,
            StaticInsertionAdditionalProperties C w := by
  obtain ⟨C, hC, A, hA, hsmall, hmod⟩ :=
    exists_uniform_positiveCoordinate_static_estimates_order_C12X
  refine ⟨C, hC, A, hA, hsmall, ?_⟩
  intro D hD m ε hε
  obtain ⟨δ₀, hδ₀, hhalf, hb⟩ := hmod D hD m ε hε
  refine ⟨δ₀, hδ₀, hhalf, ?_⟩
  intro δ hδ hle
  obtain ⟨hAB, hfit, htip, hbound⟩ := hb δ hδ hle
  intro k hk E H M _ _ _ _ _ I _ _ _ _ _ g x₀ d
  obtain ⟨hclose, hR, hHI, hder⟩ := hbound k hk g x₀ d.oriented
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
    have he := normalizedDatum_positiveSideInsertionMetric_fixed_positive_sectional
      d.oriented hA hAB x hx u v hplane
    exact (div_pos d.scalar_pos
      (mul_pos (by norm_num) d.oriented.controlledMetric_cylinder_lower.1)).trans_eq he.symm
  · intro a ha hin
    apply hHI a ha
    intro q
    have he := d.oriented_controlledMap q
    rw [he]
    exact hin _

end DifferentialGeometry.PDE.RicciFlow.StandardCap
