import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ClosedSlabProducer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CompactUniformExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HamiltonIveyCurvatureBound

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private theorem exists_closedSlab_control_time_zero (P : OrientedThreeStage.{u})
    (g : P.Metric) (K : ℝ)
    (hK : ∀ x : P.Carrier, Real.sqrt (normSq0S g x 4 (metricRm04 g x)) ≤ K) :
    ∃ G : P.ClosedSlab 0 (compactCurvatureControlTime 3 K),
      G.flow.base.metric 0 = g ∧
      ∀ t ∈ Icc 0 (compactCurvatureControlTime 3 K), ∀ x : P.Carrier,
        Real.sqrt (normSq0S (G.flow.base.metric t) x 4 (metricRm04 (G.flow.base.metric t) x)) ≤
          Real.sqrt (2 * K ^ 2 + 1) := by
  obtain ⟨τ, hτ, ⟨F⟩⟩ := exists_compact_flow_beyond_control_time g (by simp : Module.finrank ℝ ThreeSpace = 3) K hK
  have hT : 0 < compactCurvatureControlTime 3 K := compactCurvatureControlTime_pos 3 K
  have hτ' : compactCurvatureControlTime 3 K < τ := by simpa only [finrank_euclideanSpace_fin] using hτ
  have hjoint := metricCLMSection_jointContMDiffOn_of_chartGram_on
    F.S.family.metric (Ico 0 τ) F.joint
  let G := OrientedThreeStage.ClosedSlab.ofClosedOpen P F.time_pos F.S F.isSolution hjoint hT hτ'
  refine ⟨G, F.start, ?_⟩
  have hsub : Icc 0 (compactCurvatureControlTime 3 K) ⊆ (RealTimeInterval.closedOpen 0 τ F.time_pos).carrier :=
    fun t ht => ⟨ht.1, ht.2.trans_lt hτ'⟩
  exact curvature_bound_from_initial_compact (compactCurvatureControlTime 3 K) hT.le K
    (by simp) _ F.S F.isSolution hsub
    (fun t ht => ⟨ht.1, ht.2.trans hτ'⟩)
    (fun x i j => (F.joint x i j).mono (Set.prod_mono hsub subset_rfl))
    (fun x => by
      have hstart : F.S.base.metric 0 = g := F.start
      rw [hstart]
      exact hK x)

theorem exists_closedSlab_of_curvature_bound (P : OrientedThreeStage.{u})
    (g : P.Metric) (K : ℝ)
    (hK : ∀ x : P.Carrier, Real.sqrt (normSq0S g x 4 (metricRm04 g x)) ≤ K) (a : ℝ) :
    ∃ G : P.ClosedSlab a (a + compactCurvatureControlTime 3 K),
      G.flow.base.metric a = g ∧
      ∀ t ∈ Icc a (a + compactCurvatureControlTime 3 K), ∀ x : P.Carrier,
        Real.sqrt (normSq0S (G.flow.base.metric t) x 4 (metricRm04 (G.flow.base.metric t) x)) ≤
          Real.sqrt (2 * K ^ 2 + 1) := by
  obtain ⟨G, hG, hbound⟩ := exists_closedSlab_control_time_zero P g K hK
  have h : ∃ H : P.ClosedSlab (0 + a) (compactCurvatureControlTime 3 K + a),
      H.flow.base.metric a = g ∧
      ∀ t ∈ Icc a (a + compactCurvatureControlTime 3 K), ∀ x : P.Carrier,
        Real.sqrt (normSq0S (H.flow.base.metric t) x 4 (metricRm04 (H.flow.base.metric t) x)) ≤
          Real.sqrt (2 * K ^ 2 + 1) := by
    refine ⟨G.timeTranslate a, ?_, ?_⟩
    · rw [OrientedThreeStage.ClosedSlab.timeTranslate_metric, sub_self]
      exact hG
    · intro t ht x
      rw [OrientedThreeStage.ClosedSlab.timeTranslate_metric]
      exact hbound (t - a) ⟨sub_nonneg.mpr ht.1, by linarith [ht.2]⟩ x
  rw [zero_add, add_comm (compactCurvatureControlTime 3 K) a] at h
  exact h

namespace MetricCutCapEvent

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ}

theorem exists_closedSlab_restart_of_curvature_bound (E : MetricCutCapEvent P Q a s)
    (K : ℝ) (hK : ∀ x : Q.Carrier,
      Real.sqrt (normSq0S E.outputMetric x 4 (metricRm04 E.outputMetric x)) ≤ K) :
    ∃ G : Q.ClosedSlab s (s + compactCurvatureControlTime 3 K),
      G.flow.base.metric s = E.outputMetric ∧
      ∀ t ∈ Icc s (s + compactCurvatureControlTime 3 K), ∀ x : Q.Carrier,
        Real.sqrt (normSq0S (G.flow.base.metric t) x 4 (metricRm04 (G.flow.base.metric t) x)) ≤
          Real.sqrt (2 * K ^ 2 + 1) :=
  exists_closedSlab_of_curvature_bound Q E.outputMetric K hK s

end MetricCutCapEvent

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M] [CompactSpace M]
  [BoundarylessManifold ThreeModel M]

theorem exists_compact_flow_of_normalized_scalar_bound_of_fixedHamiltonIveyRegion
    (g : SmoothRiemannianMetric ThreeModel M) {A a Q b : ℝ}
    (hA : 0 < A) (hQ : 0 < Q) (ha : A ≤ a * Q)
    (hfixed : ∀ x, InFixedHamiltonIveyRegion g a x)
    (hscalar : ∀ x, metricScalarAt g x ≤ b * Q) :
    let K := 2 * Real.sqrt 3 * (max b 0 / 2 + max b (Real.exp 4 / A))
    ∃ T : ℝ, compactCurvatureControlTime 3 K / Q < T ∧
      ∃ F : FlowTo g T,
        ∀ t ∈ Icc 0 (compactCurvatureControlTime 3 K / Q), ∀ x : M,
          Real.sqrt (normSq0S (F.S.base.metric t) x 4 (metricRm04 (F.S.base.metric t) x)) ≤
            Real.sqrt (2 * K ^ 2 + 1) * Q := by
  apply exists_compact_flow_scaled_curvature_bound g (by simp [ThreeSpace]) _ hQ
  intro x
  have h := sqrt_normSq0S_le_of_fixedHamiltonIveyRegion g x (div_pos hA hQ)
    ((div_le_iff₀ hQ).mpr ha) (hfixed x) (hscalar x)
  have he : Real.exp 4 / (A / Q) = (Real.exp 4 / A) * Q := by field_simp
  have hm : max (b * Q) 0 = max b 0 * Q := by
    rw [max_mul_of_nonneg _ _ hQ.le, zero_mul]
  rw [he, hm, ← max_mul_of_nonneg _ _ hQ.le] at h
  convert! h using 1
  ring

omit [CompactSpace M] in
theorem exists_uniform_compact_flow_of_normalized_scalar_bound_of_fixedHamiltonIveyRegion
    {A : ℝ} (hA : 0 < A) (b : ℝ) :
    ∃ τ C : ℝ, 0 < τ ∧ 0 < C ∧
      ∀ (X : Type u) [TopologicalSpace X] [ChartedSpace ThreeSpace X]
        [IsManifold ThreeModel ∞ X] [T2Space X] [CompactSpace X]
        [BoundarylessManifold ThreeModel X],
        ∀ (g : SmoothRiemannianMetric ThreeModel X) (a Q : ℝ),
          0 < Q → A ≤ a * Q →
          (∀ x, InFixedHamiltonIveyRegion g a x) →
          (∀ x, metricScalarAt g x ≤ b * Q) →
          ∃ T : ℝ, τ / Q < T ∧ ∃ F : FlowTo g T,
            ∀ t ∈ Icc 0 (τ / Q), ∀ x : X,
              Real.sqrt (normSq0S (F.S.base.metric t) x 4 (metricRm04 (F.S.base.metric t) x)) ≤
                C * Q := by
  let K := 2 * Real.sqrt 3 * (max b 0 / 2 + max b (Real.exp 4 / A))
  refine ⟨compactCurvatureControlTime 3 K, Real.sqrt (2 * K ^ 2 + 1),
    compactCurvatureControlTime_pos 3 K, ?_, ?_⟩
  · apply Real.sqrt_pos.mpr
    nlinarith [sq_nonneg K]
  · intro X _ _ _ _ _ _ g a Q hQ ha hfixed hscalar
    exact exists_compact_flow_of_normalized_scalar_bound_of_fixedHamiltonIveyRegion
      g hA hQ ha hfixed hscalar

theorem MetricCutCapEvent.exists_closedSlab_restart_of_normalized_scalar_bound_of_fixedHamiltonIveyRegion
    {P R : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P R a s)
    {A h Q b : ℝ} (hA : 0 < A) (hQ : 0 < Q) (hh : A ≤ h * Q)
    (hfixed : ∀ x, InFixedHamiltonIveyRegion E.outputMetric h x)
    (hscalar : ∀ x, metricScalarAt E.outputMetric x ≤ b * Q) :
    let K := 2 * Real.sqrt 3 * (max b 0 / 2 + max b (Real.exp 4 / A))
    ∃ G : R.ClosedSlab s (s + compactCurvatureControlTime 3 K / Q),
      G.flow.base.metric s = E.outputMetric ∧
      ∀ t ∈ Icc s (s + compactCurvatureControlTime 3 K / Q), ∀ x : R.Carrier,
        Real.sqrt (normSq0S (G.flow.base.metric t) x 4 (metricRm04 (G.flow.base.metric t) x)) ≤
          Real.sqrt (2 * K ^ 2 + 1) * Q := by
  let K := 2 * Real.sqrt 3 * (max b 0 / 2 + max b (Real.exp 4 / A))
  obtain ⟨T, hT, F, hbound⟩ :=
    exists_compact_flow_of_normalized_scalar_bound_of_fixedHamiltonIveyRegion
      E.outputMetric hA hQ hh hfixed hscalar
  have htime : 0 < compactCurvatureControlTime 3 K / Q :=
    div_pos (compactCurvatureControlTime_pos 3 K) hQ
  have hjoint := metricCLMSection_jointContMDiffOn_of_chartGram_on
    F.S.family.metric (Ico 0 T) F.joint
  let G := OrientedThreeStage.ClosedSlab.ofClosedOpen R F.time_pos F.S F.isSolution
    hjoint htime hT
  have hstart : G.flow.base.metric 0 = E.outputMetric := F.start
  have h : ∃ H : R.ClosedSlab (0 + s) (compactCurvatureControlTime 3 K / Q + s),
      H.flow.base.metric s = E.outputMetric ∧
      ∀ t ∈ Icc s (s + compactCurvatureControlTime 3 K / Q), ∀ x : R.Carrier,
        Real.sqrt (normSq0S (H.flow.base.metric t) x 4 (metricRm04 (H.flow.base.metric t) x)) ≤
          Real.sqrt (2 * K ^ 2 + 1) * Q := by
    refine ⟨G.timeTranslate s, ?_, ?_⟩
    · rw [OrientedThreeStage.ClosedSlab.timeTranslate_metric, sub_self]
      exact hstart
    · intro t ht x
      rw [OrientedThreeStage.ClosedSlab.timeTranslate_metric]
      exact hbound (t - s) ⟨sub_nonneg.mpr ht.1, by linarith [ht.2]⟩ x
  rw [zero_add, add_comm (compactCurvatureControlTime 3 K / Q) s] at h
  exact h

theorem curvature_bound_of_normalized_scalar_bound_of_fixedHamiltonIveyRegion
    {g : SmoothRiemannianMetric ThreeModel M} {T A a Q b : ℝ} (F : FlowTo g T)
    (hA : 0 < A) (hQ : 0 < Q) (ha : A ≤ a * Q)
    (hfixed : ∀ x, InFixedHamiltonIveyRegion g a x)
    (hscalar : ∀ x, metricScalarAt g x ≤ b * Q) :
    let K := 2 * Real.sqrt 3 * (max b 0 / 2 + max b (Real.exp 4 / A))
    ∀ t ∈ Icc 0 (compactCurvatureControlTime 3 K / Q), t < T → ∀ x : M,
      Real.sqrt (normSq0S (F.S.base.metric t) x 4 (metricRm04 (F.S.base.metric t) x)) ≤
        Real.sqrt (2 * K ^ 2 + 1) * Q := by
  obtain ⟨U, hU, G, hbound⟩ :=
    exists_compact_flow_of_normalized_scalar_bound_of_fixedHamiltonIveyRegion
      g hA hQ ha hfixed hscalar
  dsimp only
  intro t ht htT x
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  let : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by omega⟩
  have heq : F.S.base.metric t = G.S.base.metric t :=
    flow_to_eq F G ht.1 htT (ht.2.trans_lt hU)
  rw [heq]
  exact hbound t ht x

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
