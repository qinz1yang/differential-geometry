import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.MetricComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness
import DifferentialGeometry.Geometry.Curvature.Bounds.RicciUpper

set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold ContDiff
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

end

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

private local instance ancientOrderComplete : CompleteSpace E := FiniteDimensional.complete ℝ E

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

theorem IsAncientKappaSolution.metric_inner_antitoneOn
    {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (x : F.M) (v : TangentSpace I x) :
    AntitoneOn (fun s : ℝ => (F.S.base.metric s).inner x v v) (Set.Iic 0) := by
  let _ : IsManifold I 1 F.M := IsManifold.of_le (n := ∞) (by decide)
  intro s _ t ht hst
  have hRic : ∀ r ∈ Set.Ioo s t, ∀ y : F.M, ∀ w : TangentSpace I y,
      0 ≤ F.S.ricciAt r y (vec2 w w) := by
    intro r hr y w
    have hrmem : r ∈ D.carrier := by
      rw [hF.carrier_eq]
      exact hr.2.le.trans ht
    apply metricRicciAt_nonnegative_of_curvatureOperator_nonnegative
    apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
      (I := I) (F.S.base.metric r) y).mpr
    intro n c a b
    simpa [SolutionFamily.rm04, metricRm04StandardAt_apply, vec4] using
      hF.nonnegativeCurvatureOperator r hrmem y n c a b
  have hanti := metric_inner_antitoneOn_of_ricci_nonnegative_interior F.S F.isSolution
    (a := s) (b := t)
    (fun r hr => by rw [hF.carrier_eq]; exact hr.2.trans ht)
    (fun r hr => by rw [hF.regular_eq]; exact hr.2.trans_le ht)
    hRic x v
  exact hanti ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩ hst

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

end

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {D : RealTimeInterval} {F : PointedFlowData.{u, uE, uH} (I := I) D}

private local instance metricMonotonicityTopology : TopologicalSpace F.M := F.topology
private local instance metricMonotonicityCharted : ChartedSpace H F.M := F.charted
private local instance metricMonotonicitySmooth : IsManifold I ∞ F.M := F.smooth
private local instance metricMonotonicityC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance metricMonotonicityT2 : T2Space F.M := F.t2

theorem IsAncientKappaSolution.metric_inner_le
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    {s t : ℝ} (hst : s ≤ t) (ht : t ≤ 0)
    (x : F.M) (v : TangentSpace I x) :
    (F.S.base.metric t).inner x v v ≤ (F.S.base.metric s).inner x v v := by
  exact (hF.metric_inner_antitoneOn F x v) (hst.trans ht) ht hst

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

end
