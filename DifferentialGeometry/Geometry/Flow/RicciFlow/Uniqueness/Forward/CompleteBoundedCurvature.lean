import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Noncompact
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction
import DifferentialGeometry.Geometry.Curvature.Bounds.RicciOperatorNorm

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Manifold MeasureTheory Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M] [NoncompactSpace M]

namespace CompleteBoundedCurvatureSolutionOn

def timeRestrict
    {D D' : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : CompleteBoundedCurvatureSolutionOn (I := I) (M := M) (D := D))
    (hcar : D'.carrier ⊆ D.carrier) (hreg : D'.regular ⊆ D.regular) :
    CompleteBoundedCurvatureSolutionOn (I := I) (M := M) (D := D') where
  solution := S.solution.timeRestrict D'
  isSolution := isSolutionOn_timeRestrict S.isSolution hcar hreg
  complete := by
    intro t ht
    exact S.complete t (hcar ht)
  curvatureBound := by
    intro t ht
    exact S.curvatureBound t (hcar ht)

omit [NoncompactSpace M] in
@[simp] theorem timeRestrict_solution
    {D D' : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : CompleteBoundedCurvatureSolutionOn (I := I) (M := M) (D := D))
    (hcar : D'.carrier ⊆ D.carrier) (hreg : D'.regular ⊆ D.regular) :
    (S.timeRestrict hcar hreg).solution = S.solution.timeRestrict D' := by
  rfl

omit [NoncompactSpace M] in
theorem timeRestrict_complete
    {D D' : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : CompleteBoundedCurvatureSolutionOn (I := I) (M := M) (D := D))
    (hcar : D'.carrier ⊆ D.carrier) (hreg : D'.regular ⊆ D.regular)
    (t : Real) (ht : t ∈ D'.carrier) :
    DifferentialGeometry.RiemannianMetricComplete (I := I)
      ((S.timeRestrict hcar hreg).solution.base.metric t) := by
  exact S.complete t (hcar ht)

omit [NoncompactSpace M] in
theorem timeRestrict_curvature_bound
    {D D' : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : CompleteBoundedCurvatureSolutionOn (I := I) (M := M) (D := D))
    (hcar : D'.carrier ⊆ D.carrier) (hreg : D'.regular ⊆ D.regular)
    (t : Real) (ht : t ∈ D'.carrier) :
    ∃ C : Real, 0 ≤ C ∧ ∀ x : M,
      normSq0S (I := I) ((S.timeRestrict hcar hreg).solution.base.metric t) x 4
        (metricRm04At (I := I) ((S.timeRestrict hcar hreg).solution.base.metric t) x) ≤ C := by
  exact S.curvatureBound t (hcar ht)

def timeShift
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : CompleteBoundedCurvatureSolutionOn (I := I) (M := M) (D := D)) (τ : Real) :
    CompleteBoundedCurvatureSolutionOn (I := I) (M := M) (D := D.timeShift τ) where
  solution := S.solution.timeShift τ
  isSolution := isSolutionOn_timeShift S.isSolution τ
  complete := by
    intro t ht
    exact S.complete (t + τ) ht
  curvatureBound := by
    intro t ht
    change ∃ C : Real, 0 ≤ C ∧ ∀ x : M,
      normSq0S (I := I) (S.solution.base.metric (t + τ)) x 4
        (metricRm04At (I := I) (S.solution.base.metric (t + τ)) x) ≤ C
    exact S.curvatureBound (t + τ) ht

omit [NoncompactSpace M] in
@[simp] theorem timeShift_solution
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : CompleteBoundedCurvatureSolutionOn (I := I) (M := M) (D := D)) (τ : Real) :
    (S.timeShift τ).solution = S.solution.timeShift τ := by
  rfl

omit [NoncompactSpace M] in
theorem timeShift_complete
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : CompleteBoundedCurvatureSolutionOn (I := I) (M := M) (D := D)) (τ t : Real)
    (ht : t ∈ (D.timeShift τ).carrier) :
    DifferentialGeometry.RiemannianMetricComplete (I := I)
      ((S.timeShift τ).solution.base.metric t) := by
  exact S.complete (t + τ) ht

omit [NoncompactSpace M] in
theorem timeShift_curvature_bound
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : CompleteBoundedCurvatureSolutionOn (I := I) (M := M) (D := D)) (τ t : Real)
    (ht : t ∈ (D.timeShift τ).carrier) :
    ∃ C : Real, 0 ≤ C ∧ ∀ x : M,
      normSq0S (I := I) ((S.timeShift τ).solution.base.metric t) x 4
        (metricRm04At (I := I) ((S.timeShift τ).solution.base.metric t) x) ≤ C := by
  change ∃ C : Real, 0 ≤ C ∧ ∀ x : M,
    normSq0S (I := I) (S.solution.base.metric (t + τ)) x 4
      (metricRm04At (I := I) (S.solution.base.metric (t + τ)) x) ≤ C
  exact S.curvatureBound (t + τ) ht

end CompleteBoundedCurvatureSolutionOn

omit [SigmaCompactSpace M] [NoncompactSpace M] in
theorem metric_ricci_bound_of_curvature_bound
    (g : SmoothRiemannianMetric I M) (K : Real)
    (hRm : ∀ x : M,
      normSq0S (I := I) g x 4 (metricRm04At (I := I) g x) ≤ K) :
    ∃ C : Real, C = (Module.finrank Real E : Real) ^ 2 * Real.sqrt K ∧
      0 ≤ C ∧ ∀ (x : M) (v : TangentSpace I x),
      |metricRicciAt (I := I) g x (vec2 (I := I) v v)| ≤ C * g.inner x v v := by
  classical
  let C : Real := (Module.finrank Real E : Real) ^ 2 * Real.sqrt K
  have hC_nonneg : 0 ≤ C :=
    mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
  refine ⟨C, rfl, hC_nonneg, fun x v => ?_⟩
  obtain ⟨basis, hON⟩ :=
    DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) g x
  have hinv : MetricInverseInBasis (I := I) g x basis
      (identityInvMetric (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    have h := metricInverseInBasis_of_orthonormal (I := I) g basis hON
    intro i j
    simpa [identityInvMetric, diagonalInvMetric] using h i j
  let D := metricCurvatureSections (I := I) (M := M) g
  have hLower :
      Rm04LowersRm13At (I := I) g x
        (metricRm13 (I := I) (M := M) g x)
        (metricRm04 (I := I) (M := M) g x) :=
    rm04LowersRm13At_of_realizes
      (I := I) g (metricCov (I := I) (M := M) g)
      (metricRm13 (I := I) (M := M) g)
      (metricRm04 (I := I) (M := M) g)
      D.rm13Realizes D.rm04Realizes x
  have htrace : ∀ i j,
      metricRicciAt (I := I) (M := M) g x
          (vec2 (I := I) (basis i) (basis j)) =
        ∑ a, metricRm04At (I := I) (M := M) g x
          (vec4 (I := I) (basis a) (basis i) (basis j) (basis a)) := by
    intro i j
    simpa using
      (ricci_diag_eq_sum_rm04_diag_of_orthonormal
        (I := I) (M := M) g basis
        (metricRicci (I := I) (M := M) g)
        (metricRm13 (I := I) (M := M) g)
        (metricRm04 (I := I) (M := M) g)
        D.ricciRealizes hLower hON i j)
  have hunit : ∀ u : TangentSpace I x, g.inner x u u = 1 →
      |metricRicciAt (I := I) (M := M) g x (vec2 (I := I) u u)| ≤ C := by
    intro u hu
    have hraw := ricci_unitQuad_le_of_trace (I := I) g basis hON hinv
      (metricRicciAt (I := I) (M := M) g x)
      (metricRm04At (I := I) (M := M) g x) htrace u hu
    calc
      _ ≤ (Module.finrank Real (TangentSpace I x) : Real) ^ 2 *
          Real.sqrt (normSq0S (I := I) g x 4
            (metricRm04At (I := I) (M := M) g x)) := hraw
      _ ≤ (Module.finrank Real (TangentSpace I x) : Real) ^ 2 * Real.sqrt K := by
        exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hRm x)) (sq_nonneg _)
      _ = C := by rfl
  have hall := tensor02_quadForm_abs_le_of_unit_bound
    (I := I) g (metricRicciAt (I := I) (M := M) g x) hunit v
  exact hall

omit [SigmaCompactSpace M] [NoncompactSpace M] in
theorem ricci_bound_of_curvature_bound
    [BoundarylessManifold I M]
    (g : SmoothRiemannianMetric I M) (K : Real)
    (hRm : ∀ x : M,
      normSq0S (I := I) g x 4 (metricRm04At (I := I) g x) ≤ K) :
    ∃ C : Real, 0 ≤ C ∧ ∀ (x : M) (v : TangentSpace I x),
      |ricciTensor (I := I) g x v v| ≤ C * g.inner x v v := by
  obtain ⟨C, -, hC, hbound⟩ := metric_ricci_bound_of_curvature_bound (I := I) g K hRm
  refine ⟨C, hC, fun x v => ?_⟩
  simpa only [metricRicciAt_apply_eq_ricciTensor (I := I) g x v v] using hbound x v

omit [NoncompactSpace M] in
theorem CompleteBoundedCurvatureSolutionOn.exists_slice_ricci_bound
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : CompleteBoundedCurvatureSolutionOn (I := I) (M := M) (D := D))
    (t : Real) (ht : t ∈ D.carrier) :
    ∃ C : Real, 0 ≤ C ∧ ∀ (x : M) (v : TangentSpace I x),
      |metricRicciAt (I := I) (S.solution.base.metric t) x
          (vec2 (I := I) v v)| ≤ C * (S.solution.base.metric t).inner x v v := by
  obtain ⟨K, -, hRm⟩ := S.curvatureBound t ht
  obtain ⟨C, -, hC, hbound⟩ := metric_ricci_bound_of_curvature_bound (I := I)
    (S.solution.base.metric t) K hRm
  exact ⟨C, hC, hbound⟩

omit [NoncompactSpace M] in
theorem CompleteBoundedCurvatureSolutionOn.exists_slab_ricci_bound
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : CompleteBoundedCurvatureSolutionOn (I := I) (M := M) (D := D))
    {K : Set Real}
    (hcurv : ∃ B : Real, 0 ≤ B ∧ ∀ t ∈ K, ∀ x : M,
      normSq0S (I := I) (S.solution.base.metric t) x 4
        (metricRm04At (I := I) (S.solution.base.metric t) x) ≤ B) :
    ∃ C : Real, 0 ≤ C ∧ ∀ t ∈ K, ∀ (x : M) (v : TangentSpace I x),
      |metricRicciAt (I := I) (S.solution.base.metric t) x
          (vec2 (I := I) v v)| ≤ C * (S.solution.base.metric t).inner x v v := by
  obtain ⟨B, -, hbound⟩ := hcurv
  let C : Real := (Module.finrank Real E : Real) ^ 2 * Real.sqrt B
  have hC : 0 ≤ C := mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
  refine ⟨C, hC, ?_⟩
  intro t ht x v
  obtain ⟨C', hC'eq, -, hric⟩ := metric_ricci_bound_of_curvature_bound
    (I := I) (S.solution.base.metric t) B (hbound t ht)
  have hCeq : C' = C := by
    rw [hC'eq]
  simpa [hCeq] using hric x v

omit [NoncompactSpace M] in
theorem ricci_flow_forward_unique_of_complete_bounded_curvature_energy_criterion
    {a b : Real} (hab : a < b)
    (S₁ S₂ : CompleteBoundedCurvatureSolutionOn (I := I) (M := M)
      (D := DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen a b hab))
    (henergyCont : ContinuousOn
      (forwardUniqueEnergy (I := I) (M := M)
        S₁.solution.base.metric S₂.solution.base.metric) (Set.Icc a b))
    (henergy' : Real → Real)
    (henergyDeriv : ∀ t ∈ Set.Ioo a b,
      HasDerivAt
        (forwardUniqueEnergy (I := I) (M := M)
          S₁.solution.base.metric S₂.solution.base.metric)
        (henergy' t) t)
    (K : Real)
    (henergyBound : ∀ t ∈ Set.Ioo a b,
      henergy' t ≤
        K * forwardUniqueEnergy (I := I) (M := M)
          S₁.solution.base.metric S₂.solution.base.metric t)
    (hinitial : S₁.solution.base.metric a = S₂.solution.base.metric a)
    (hdensityCont : ∀ t ∈ Set.Icc a b,
      Continuous (fun x =>
        forwardUniqueDensity (I := I) S₁.solution.base.metric S₂.solution.base.metric t x))
    (hdensityIntegrable : ∀ t ∈ Set.Icc a b,
      Integrable (fun x =>
        forwardUniqueDensity (I := I) S₁.solution.base.metric S₂.solution.base.metric t x)
        (riemannianMeasureFamily (I := I) (M := M) S₁.solution.base.metric t)) :
    ∀ t ∈ Set.Ico a b,
      S₁.solution.base.metric t = S₂.solution.base.metric t := by
  have hcriterion :
      NoncompactForwardUniquenessCriterion (I := I)
        S₁.solution.base.metric S₂.solution.base.metric a b K henergy' :=
    { interval := hab
      energyCont := henergyCont
      energyDerivative := henergyDeriv
      energyBound := henergyBound
      initial := hinitial
      densityCont := hdensityCont
      densityIntegrable := hdensityIntegrable }
  have huniq := forward_unique_of_noncompact_criterion (I := I)
    S₁.solution.base.metric S₂.solution.base.metric hcriterion
  intro t ht
  exact huniq t ⟨ht.1, ht.2.le⟩

omit [NoncompactSpace M] in
theorem ricci_flow_forward_unique_of_complete_bounded_curvature_compact_density
    {a b : Real} (hab : a < b)
    (S₁ S₂ : CompleteBoundedCurvatureSolutionOn (I := I) (M := M)
      (D := DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen a b hab))
    (henergyCont : ContinuousOn
      (forwardUniqueEnergy (I := I) (M := M)
        S₁.solution.base.metric S₂.solution.base.metric) (Set.Icc a b))
    (henergy' : Real → Real)
    (henergyDeriv : ∀ t ∈ Set.Ioo a b,
      HasDerivAt
        (forwardUniqueEnergy (I := I) (M := M)
          S₁.solution.base.metric S₂.solution.base.metric)
        (henergy' t) t)
    (K : Real)
    (henergyBound : ∀ t ∈ Set.Ioo a b,
      henergy' t ≤
        K * forwardUniqueEnergy (I := I) (M := M)
          S₁.solution.base.metric S₂.solution.base.metric t)
    (hinitial : S₁.solution.base.metric a = S₂.solution.base.metric a)
    (hdensityCont : ∀ t ∈ Set.Icc a b,
      Continuous (fun x =>
        forwardUniqueDensity (I := I) S₁.solution.base.metric S₂.solution.base.metric t x))
    (hdensityCompact : ∀ t ∈ Set.Icc a b,
      HasCompactSupport (fun x =>
        forwardUniqueDensity (I := I) S₁.solution.base.metric S₂.solution.base.metric t x)) :
    ∀ t ∈ Set.Ico a b,
      S₁.solution.base.metric t = S₂.solution.base.metric t := by
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  have hdensityIntegrable : ∀ t ∈ Set.Icc a b,
      Integrable (fun x =>
        forwardUniqueDensity (I := I) S₁.solution.base.metric S₂.solution.base.metric t x)
        (riemannianMeasureFamily (I := I) (M := M)
          S₁.solution.base.metric t) := by
    intro t ht
    have hfinite : IsFiniteMeasureOnCompacts
        (riemannianVolumeMeasure (I := I) (M := M)
          (S₁.solution.base.metric t)) :=
      riemannianVolumeMeasure_isFiniteMeasureOnCompacts
        (I := I) (M := M) (S₁.solution.base.metric t)
    rw [riemannianMeasureFamily_def]
    exact (hdensityCont t ht).integrable_of_hasCompactSupport (hdensityCompact t ht)
  exact ricci_flow_forward_unique_of_complete_bounded_curvature_energy_criterion
    (I := I) hab S₁ S₂ henergyCont henergy' henergyDeriv K henergyBound hinitial
    hdensityCont hdensityIntegrable

end DifferentialGeometry.PDE.RicciFlow

end
