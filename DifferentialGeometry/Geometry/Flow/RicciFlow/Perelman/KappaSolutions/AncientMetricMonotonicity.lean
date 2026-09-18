import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.MetricComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness
import DifferentialGeometry.Geometry.Curvature.Bounds.RicciUpper

set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsManifold I 1 M] [T2Space M]

theorem ancientModel_metric_inner_antitoneOn
    (L : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    {kappa : ℝ} (hL : IsAncientKappaSolution (I := I) kappa L) :
    let : TopologicalSpace L.M := L.topology
    let : ChartedSpace H L.M := L.charted
    let : IsManifold I ∞ L.M := L.smooth
    let : IsManifold I 1 L.M :=
      IsManifold.of_le (n := (∞ : WithTop ℕ∞)) (by decide)
    let : SigmaCompactSpace L.M := L.sigmaCompact
    let : T2Space L.M := L.t2
    ∀ (x : L.M) (v : TangentSpace I x),
      AntitoneOn (fun t => (L.S.base.metric t).inner x v v) (Set.Iic 0) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : TopologicalSpace L.M := L.topology
  let : ChartedSpace H L.M := L.charted
  let : IsManifold I ∞ L.M := L.smooth
  let : IsManifold I 1 L.M :=
    IsManifold.of_le (n := (∞ : WithTop ℕ∞)) (by decide)
  let : SigmaCompactSpace L.M := L.sigmaCompact
  let : T2Space L.M := L.t2
  change ∀ (x : L.M) (v : TangentSpace I x),
    AntitoneOn (fun t => (L.S.base.metric t).inner x v v) (Set.Iic 0)
  intro x v s hs t ht hst
  have hRic : ∀ q ∈ Set.Ioo s t, ∀ y : L.M, ∀ w : TangentSpace I y,
      0 ≤ L.S.ricciAt q y (vec2 w w) := by
    intro q hq y w
    have hqmem : q ∈ ancientTimeInterval.carrier := by
      simpa only [ancientTimeInterval_carrier, Set.mem_Iic] using hq.2.le.trans ht
    apply metricRicciAt_nonnegative_of_curvatureOperator_nonnegative
    apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
      (I := I) (L.S.base.metric q) y).mpr
    intro n c a b
    simpa [SolutionFamily.rm04, metricRm04StandardAt_apply, vec4] using
      hL.nonnegativeCurvatureOperator q hqmem y n c a b
  have hanti := metric_inner_antitoneOn_of_ricci_nonnegative_interior L.S L.isSolution
    (a := s) (b := t)
    (fun q hq => by simpa only [ancientTimeInterval_carrier, Set.mem_Iic] using hq.2.trans ht)
    (fun q hq => by simpa only [ancientTimeInterval_regular, Set.mem_Iio] using hq.2.trans_le ht)
    hRic x v
  exact hanti ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩ hst

theorem ancientModel_metric_zero_le
    (L : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    {kappa : ℝ} (hL : IsAncientKappaSolution (I := I) kappa L)
    {s : ℝ} (hs : s ≤ 0) :
    let : TopologicalSpace L.M := L.topology
    let : ChartedSpace H L.M := L.charted
    let : IsManifold I ∞ L.M := L.smooth
    let : IsManifold I 1 L.M :=
      IsManifold.of_le (n := (∞ : WithTop ℕ∞)) (by decide)
    let : SigmaCompactSpace L.M := L.sigmaCompact
    let : T2Space L.M := L.t2
    ∀ (x : L.M) (v : TangentSpace I x),
      (L.S.base.metric 0).inner x v v ≤ (L.S.base.metric s).inner x v v := by
  let : TopologicalSpace L.M := L.topology
  let : ChartedSpace H L.M := L.charted
  let : IsManifold I ∞ L.M := L.smooth
  let : IsManifold I 1 L.M :=
    IsManifold.of_le (n := (∞ : WithTop ℕ∞)) (by decide)
  let : SigmaCompactSpace L.M := L.sigmaCompact
  let : T2Space L.M := L.t2
  change ∀ (x : L.M) (v : TangentSpace I x),
    (L.S.base.metric 0).inner x v v ≤ (L.S.base.metric s).inner x v v
  intro x v
  exact ancientModel_metric_inner_antitoneOn L hL x v hs (by simp) hs

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
