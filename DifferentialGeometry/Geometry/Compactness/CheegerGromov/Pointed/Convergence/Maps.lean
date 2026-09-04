import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Bounds.BoundedGeometry
import DifferentialGeometry.Geometry.Metric.Convergence.Defs
import DifferentialGeometry.Topology.Exhaustion
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E]
variable {H : Type uH} [TopologicalSpace H]

section MetricCompactnessCore

variable [NormedSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]

structure PointedRiemannianConvergenceMaps
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (L : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (subseq : Nat -> Nat) where
  partialDiffeomorph :
    forall k : Nat,
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : TopologicalSpace (X.obj (subseq k)).M :=
        (X.obj (subseq k)).topology
      letI : ChartedSpace H (X.obj (subseq k)).M :=
        (X.obj (subseq k)).charted
      PartialDiffeomorph I I L.M (X.obj (subseq k)).M (∞ : WithTop ℕ∞)
  source_exhausts :
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    ExhaustsByOpen (fun k =>
      letI : TopologicalSpace (X.obj (subseq k)).M :=
        (X.obj (subseq k)).topology
      letI : ChartedSpace H (X.obj (subseq k)).M :=
        (X.obj (subseq k)).charted
      (partialDiffeomorph k).source)
  base_mem :
    forall k : Nat,
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : TopologicalSpace (X.obj (subseq k)).M :=
        (X.obj (subseq k)).topology
      letI : ChartedSpace H (X.obj (subseq k)).M :=
        (X.obj (subseq k)).charted
      L.basepoint ∈ (partialDiffeomorph k).source
  basepoint_map :
    forall k : Nat,
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : TopologicalSpace (X.obj (subseq k)).M :=
        (X.obj (subseq k)).topology
      letI : ChartedSpace H (X.obj (subseq k)).M :=
        (X.obj (subseq k)).charted
      partialDiffeomorph k L.basepoint = (X.obj (subseq k)).basepoint

namespace PointedRiemannianConvergenceMaps

def source
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : Nat) : Set L.M := by
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : TopologicalSpace (X.obj (subseq k)).M :=
    (X.obj (subseq k)).topology
  letI : ChartedSpace H (X.obj (subseq k)).M :=
    (X.obj (subseq k)).charted
  exact (Φ.partialDiffeomorph k).source

def target
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : Nat) :
    Set ((X.obj (subseq k)).M) := by
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : TopologicalSpace (X.obj (subseq k)).M :=
    (X.obj (subseq k)).topology
  letI : ChartedSpace H (X.obj (subseq k)).M :=
    (X.obj (subseq k)).charted
  exact (Φ.partialDiffeomorph k).target

def map
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : Nat) :
    L.M -> (X.obj (subseq k)).M := by
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : TopologicalSpace (X.obj (subseq k)).M :=
    (X.obj (subseq k)).topology
  letI : ChartedSpace H (X.obj (subseq k)).M :=
    (X.obj (subseq k)).charted
  exact fun x => (Φ.partialDiffeomorph k) x

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem source_open
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : Nat) :
    letI : TopologicalSpace L.M := L.topology
    IsOpen (Φ.source k) := by
  let : TopologicalSpace L.M := L.topology
  let : ChartedSpace H L.M := L.charted
  let : TopologicalSpace (X.obj (subseq k)).M :=
    (X.obj (subseq k)).topology
  let : ChartedSpace H (X.obj (subseq k)).M :=
    (X.obj (subseq k)).charted
  exact (Φ.partialDiffeomorph k).open_source

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem target_open
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : Nat) :
    letI : TopologicalSpace (X.obj (subseq k)).M := (X.obj (subseq k)).topology
    IsOpen (Φ.target k) := by
  let : TopologicalSpace L.M := L.topology
  let : ChartedSpace H L.M := L.charted
  let : TopologicalSpace (X.obj (subseq k)).M :=
    (X.obj (subseq k)).topology
  let : ChartedSpace H (X.obj (subseq k)).M :=
    (X.obj (subseq k)).charted
  exact (Φ.partialDiffeomorph k).open_target

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem source_subset
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq)
    {K : Set L.M}
    (hK :
      letI : TopologicalSpace L.M := L.topology
      IsCompact K) :
    exists k0 : Nat, forall k : Nat, k0 <= k -> K ⊆ Φ.source k := by
  let : TopologicalSpace L.M := L.topology
  exact Φ.source_exhausts.subset K hK

def unrepoint
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : forall i : Nat, (X.obj i).M)
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) (X.repoint b) L subseq)
    (hbase : forall k : Nat,
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : TopologicalSpace (X.obj (subseq k)).M :=
        (X.obj (subseq k)).topology
      letI : ChartedSpace H (X.obj (subseq k)).M :=
        (X.obj (subseq k)).charted
      Φ.partialDiffeomorph k L.basepoint = (X.obj (subseq k)).basepoint) :
    PointedRiemannianConvergenceMaps (I := I) X L subseq where
  partialDiffeomorph := Φ.partialDiffeomorph
  source_exhausts := Φ.source_exhausts
  base_mem := Φ.base_mem
  basepoint_map := hbase

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
@[simp] theorem unrepoint_source
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : forall i : Nat, (X.obj i).M)
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) (X.repoint b) L subseq)
    (hbase : forall k : Nat,
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : TopologicalSpace (X.obj (subseq k)).M :=
        (X.obj (subseq k)).topology
      letI : ChartedSpace H (X.obj (subseq k)).M :=
        (X.obj (subseq k)).charted
      Φ.partialDiffeomorph k L.basepoint = (X.obj (subseq k)).basepoint)
    (k : Nat) :
    (Φ.unrepoint b hbase).source k = Φ.source k := rfl

end PointedRiemannianConvergenceMaps

def metricSourceOpenSubset
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : Nat) :
    letI : TopologicalSpace L.M := L.topology
    TopologicalSpace.Opens L.M := by
  letI : TopologicalSpace L.M := L.topology
  exact ⟨Φ.source k, Φ.source_open k⟩

def metricTargetOpenSubset
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : Nat) :
    letI : TopologicalSpace (X.obj (subseq k)).M :=
      (X.obj (subseq k)).topology
    TopologicalSpace.Opens ((X.obj (subseq k)).M) := by
  letI : TopologicalSpace (X.obj (subseq k)).M :=
    (X.obj (subseq k)).topology
  exact ⟨Φ.target k, Φ.target_open k⟩

abbrev MetricSourceDomain
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : Nat) :=
  letI : TopologicalSpace L.M := L.topology
  (metricSourceOpenSubset (I := I) Φ k : Type _)

abbrev MetricTargetDomain
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : Nat) :=
  letI : TopologicalSpace (X.obj (subseq k)).M :=
    (X.obj (subseq k)).topology
  (metricTargetOpenSubset (I := I) Φ k : Type _)

@[implicit_reducible]
noncomputable def metricSourceDomainTopology
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : Nat) :
    TopologicalSpace (MetricSourceDomain (I := I) Φ k) := by
  letI : TopologicalSpace L.M := L.topology
  change TopologicalSpace (metricSourceOpenSubset (I := I) Φ k)
  infer_instance

@[implicit_reducible]
noncomputable def metricSourceDomainChartedSpace
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : Nat) :
    letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomainTopology (I := I) Φ k
    ChartedSpace H (MetricSourceDomain (I := I) Φ k) := by
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
    metricSourceDomainTopology (I := I) Φ k
  change ChartedSpace H (metricSourceOpenSubset (I := I) Φ k)
  exact TopologicalSpace.Opens.instChartedSpace (H := H) (M := L.M)
    (s := metricSourceOpenSubset (I := I) Φ k)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
    [I.Boundaryless] in
theorem metric_source_domain_t2
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : Nat) :
    letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomainTopology (I := I) Φ k
    T2Space (MetricSourceDomain (I := I) Φ k) := by
  let : TopologicalSpace L.M := L.topology
  let : T2Space L.M := L.t2
  let : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
    metricSourceDomainTopology (I := I) Φ k
  change T2Space {x : L.M // x ∈ Φ.source k}
  infer_instance

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
    [I.Boundaryless] in
theorem metric_source_domain_smooth
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : Nat) :
    letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomainTopology (I := I) Φ k
    letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomainChartedSpace (I := I) Φ k
    IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) := by
  let : TopologicalSpace L.M := L.topology
  let : ChartedSpace H L.M := L.charted
  let : IsManifold I ∞ L.M := L.smooth
  let : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
    metricSourceDomainTopology (I := I) Φ k
  let : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
    metricSourceDomainChartedSpace (I := I) Φ k
  change IsManifold I ∞ (metricSourceOpenSubset (I := I) Φ k)
  exact { (metricSourceOpenSubset (I := I) Φ k).instHasGroupoid (contDiffGroupoid ∞ I) with }

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem metric_source_domain_sigma_compact
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : Nat)
    (hσ : letI : TopologicalSpace L.M := L.topology; IsSigmaCompact (Φ.source k)) :
    letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomainTopology (I := I) Φ k
    SigmaCompactSpace (MetricSourceDomain (I := I) Φ k) := by
  let : TopologicalSpace L.M := L.topology
  let : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
    metricSourceDomainTopology (I := I) Φ k
  change SigmaCompactSpace {x : L.M // x ∈ Φ.source k}
  exact isSigmaCompact_iff_sigmaCompactSpace.mp hσ

@[implicit_reducible]
noncomputable def metricTargetDomainTopology
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : Nat) :
    TopologicalSpace (MetricTargetDomain (I := I) Φ k) := by
  letI : TopologicalSpace (X.obj (subseq k)).M :=
    (X.obj (subseq k)).topology
  change TopologicalSpace (metricTargetOpenSubset (I := I) Φ k)
  infer_instance

@[implicit_reducible]
noncomputable def metricTargetDomainChartedSpace
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : Nat) :
    letI : TopologicalSpace (MetricTargetDomain (I := I) Φ k) :=
      metricTargetDomainTopology (I := I) Φ k
    ChartedSpace H (MetricTargetDomain (I := I) Φ k) := by
  letI : TopologicalSpace (X.obj (subseq k)).M :=
    (X.obj (subseq k)).topology
  letI : ChartedSpace H (X.obj (subseq k)).M :=
    (X.obj (subseq k)).charted
  letI : TopologicalSpace (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomainTopology (I := I) Φ k
  change ChartedSpace H (metricTargetOpenSubset (I := I) Φ k)
  exact TopologicalSpace.Opens.instChartedSpace (H := H)
    (M := (X.obj (subseq k)).M) (s := metricTargetOpenSubset (I := I) Φ k)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
    [I.Boundaryless] in
theorem metric_target_domain_t2
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : Nat) :
    letI : TopologicalSpace (MetricTargetDomain (I := I) Φ k) :=
      metricTargetDomainTopology (I := I) Φ k
    T2Space (MetricTargetDomain (I := I) Φ k) := by
  let : TopologicalSpace (X.obj (subseq k)).M :=
    (X.obj (subseq k)).topology
  let : T2Space (X.obj (subseq k)).M := (X.obj (subseq k)).t2
  let : TopologicalSpace (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomainTopology (I := I) Φ k
  change T2Space {x : (X.obj (subseq k)).M // x ∈ Φ.target k}
  infer_instance

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
    [I.Boundaryless] in
theorem metric_target_domain_smooth
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : Nat) :
    letI : TopologicalSpace (MetricTargetDomain (I := I) Φ k) :=
      metricTargetDomainTopology (I := I) Φ k
    letI : ChartedSpace H (MetricTargetDomain (I := I) Φ k) :=
      metricTargetDomainChartedSpace (I := I) Φ k
    IsManifold I ∞ (MetricTargetDomain (I := I) Φ k) := by
  let : TopologicalSpace (X.obj (subseq k)).M :=
    (X.obj (subseq k)).topology
  let : ChartedSpace H (X.obj (subseq k)).M :=
    (X.obj (subseq k)).charted
  let : IsManifold I ∞ (X.obj (subseq k)).M := (X.obj (subseq k)).smooth
  let : TopologicalSpace (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomainTopology (I := I) Φ k
  let : ChartedSpace H (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomainChartedSpace (I := I) Φ k
  change IsManifold I ∞ (metricTargetOpenSubset (I := I) Φ k)
  exact { (metricTargetOpenSubset (I := I) Φ k).instHasGroupoid (contDiffGroupoid ∞ I) with }

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem metric_target_domain_sigma_compact
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : Nat)
    (hσ :
      letI : TopologicalSpace (X.obj (subseq k)).M :=
        (X.obj (subseq k)).topology
      IsSigmaCompact (Φ.target k)) :
    letI : TopologicalSpace (MetricTargetDomain (I := I) Φ k) :=
      metricTargetDomainTopology (I := I) Φ k
    SigmaCompactSpace (MetricTargetDomain (I := I) Φ k) := by
  let : TopologicalSpace (X.obj (subseq k)).M :=
    (X.obj (subseq k)).topology
  let : TopologicalSpace (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomainTopology (I := I) Φ k
  change SigmaCompactSpace {x : (X.obj (subseq k)).M // x ∈ Φ.target k}
  exact isSigmaCompact_iff_sigmaCompactSpace.mp hσ

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
private theorem metric_cont_mdiff_open_cod
    {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold I ∞ M] [IsManifold I ∞ N]
    {U : TopologicalSpace.Opens N}
    {f : M -> U}
    (hf : ContMDiff I I (∞ : WithTop ℕ∞) (fun x : M => (f x : N))) :
    ContMDiff I I (∞ : WithTop ℕ∞) f := by
  have : IsManifold I ∞ U :=
    { U.instHasGroupoid (contDiffGroupoid ∞ I) with }
  rw [contMDiff_iff_target] at hf ⊢
  constructor
  · exact Continuous.subtype_mk hf.1 (fun x => (f x).2)
  · intro y
    have hy := hf.2 (y : N)
    simpa [Function.comp_def, extChartAt, TopologicalSpace.Opens.chartAt_eq,
      Set.preimage_preimage] using hy

noncomputable def metricSourceTargetDiffeomorph
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : Nat) :
    letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomainTopology (I := I) Φ k
    letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomainChartedSpace (I := I) Φ k
    letI : TopologicalSpace (MetricTargetDomain (I := I) Φ k) :=
      metricTargetDomainTopology (I := I) Φ k
    letI : ChartedSpace H (MetricTargetDomain (I := I) Φ k) :=
      metricTargetDomainChartedSpace (I := I) Φ k
    Diffeomorph I I (MetricSourceDomain (I := I) Φ k)
      (MetricTargetDomain (I := I) Φ k) (∞ : WithTop ℕ∞) := by
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : IsManifold I ∞ L.M := L.smooth
  letI : TopologicalSpace (X.obj (subseq k)).M :=
    (X.obj (subseq k)).topology
  letI : ChartedSpace H (X.obj (subseq k)).M :=
    (X.obj (subseq k)).charted
  letI : IsManifold I ∞ (X.obj (subseq k)).M :=
    (X.obj (subseq k)).smooth
  letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
    metricSourceDomainTopology (I := I) Φ k
  letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
    metricSourceDomainChartedSpace (I := I) Φ k
  letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) :=
    metric_source_domain_smooth (I := I) Φ k
  letI : TopologicalSpace (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomainTopology (I := I) Φ k
  letI : ChartedSpace H (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomainChartedSpace (I := I) Φ k
  letI : IsManifold I ∞ (MetricTargetDomain (I := I) Φ k) :=
    metric_target_domain_smooth (I := I) Φ k
  let e := Φ.partialDiffeomorph k
  refine
    { toEquiv := e.toPartialEquiv.toEquiv
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · have hbase :
        ContMDiff I I (∞ : WithTop ℕ∞)
          (fun x : MetricSourceDomain (I := I) Φ k => e (x : L.M)) := by
      intro x
      have hx : (x : L.M) ∈ e.source := x.2
      have hAt :
          ContMDiffAt I I (∞ : WithTop ℕ∞) (fun y : L.M => e y) (x : L.M) :=
        e.contMDiffOn_toFun.contMDiffAt (e.open_source.mem_nhds hx)
      exact (contMDiffAt_subtype_iff
        (U := metricSourceOpenSubset (I := I) Φ k)
        (f := fun y : L.M => e y) (x := x)).2 hAt
    exact metric_cont_mdiff_open_cod (I := I) (U := metricTargetOpenSubset (I := I) Φ k) hbase
  · have hbase :
        ContMDiff I I (∞ : WithTop ℕ∞)
          (fun y : MetricTargetDomain (I := I) Φ k =>
            e.toPartialEquiv.symm (y : (X.obj (subseq k)).M)) := by
      intro y
      have hy : (y : (X.obj (subseq k)).M) ∈ e.target := y.2
      have hAt :
          ContMDiffAt I I (∞ : WithTop ℕ∞)
            (fun z : (X.obj (subseq k)).M => e.toPartialEquiv.symm z)
            (y : (X.obj (subseq k)).M) :=
        e.contMDiffOn_invFun.contMDiffAt (e.open_target.mem_nhds hy)
      exact (contMDiffAt_subtype_iff
        (U := metricTargetOpenSubset (I := I) Φ k)
        (f := fun z : (X.obj (subseq k)).M => e.toPartialEquiv.symm z) (x := y)).2 hAt
    exact metric_cont_mdiff_open_cod (I := I) (U := metricSourceOpenSubset (I := I) Φ k) hbase

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
@[simp]
theorem metric_source_target_diffeomorph_apply
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : Nat)
    (x : MetricSourceDomain (I := I) Φ k) :
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : TopologicalSpace (X.obj (subseq k)).M := (X.obj (subseq k)).topology
    letI : ChartedSpace H (X.obj (subseq k)).M := (X.obj (subseq k)).charted
    letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomainTopology (I := I) Φ k
    letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomainChartedSpace (I := I) Φ k
    letI : TopologicalSpace (MetricTargetDomain (I := I) Φ k) :=
      metricTargetDomainTopology (I := I) Φ k
    letI : ChartedSpace H (MetricTargetDomain (I := I) Φ k) :=
      metricTargetDomainChartedSpace (I := I) Φ k
    (metricSourceTargetDiffeomorph (I := I) Φ k x : (X.obj (subseq k)).M) =
      Φ.map k (x : L.M) := by
  rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem metric_source_target_diffeomorph_mfderiv
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : Nat) :
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : IsManifold I ∞ L.M := L.smooth
    letI : TopologicalSpace (X.obj (subseq k)).M := (X.obj (subseq k)).topology
    letI : ChartedSpace H (X.obj (subseq k)).M := (X.obj (subseq k)).charted
    letI : IsManifold I ∞ (X.obj (subseq k)).M := (X.obj (subseq k)).smooth
    letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomainTopology (I := I) Φ k
    letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomainChartedSpace (I := I) Φ k
    letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) :=
      metric_source_domain_smooth (I := I) Φ k
    letI : TopologicalSpace (MetricTargetDomain (I := I) Φ k) :=
      metricTargetDomainTopology (I := I) Φ k
    letI : ChartedSpace H (MetricTargetDomain (I := I) Φ k) :=
      metricTargetDomainChartedSpace (I := I) Φ k
    letI : IsManifold I ∞ (MetricTargetDomain (I := I) Φ k) :=
      metric_target_domain_smooth (I := I) Φ k
    ∀ (x : MetricSourceDomain (I := I) Φ k) (v : TangentSpace I x),
      mfderiv I I (metricSourceTargetDiffeomorph (I := I) Φ k) x v =
        mfderiv I I (Φ.map k) (x : L.M) v := by
  let : TopologicalSpace L.M := L.topology
  let : ChartedSpace H L.M := L.charted
  let : IsManifold I ∞ L.M := L.smooth
  let : TopologicalSpace (X.obj (subseq k)).M := (X.obj (subseq k)).topology
  let : ChartedSpace H (X.obj (subseq k)).M := (X.obj (subseq k)).charted
  let : IsManifold I ∞ (X.obj (subseq k)).M := (X.obj (subseq k)).smooth
  let : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
    metricSourceDomainTopology (I := I) Φ k
  let : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
    metricSourceDomainChartedSpace (I := I) Φ k
  let : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) :=
    metric_source_domain_smooth (I := I) Φ k
  let : TopologicalSpace (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomainTopology (I := I) Φ k
  let : ChartedSpace H (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomainChartedSpace (I := I) Φ k
  let : IsManifold I ∞ (MetricTargetDomain (I := I) Φ k) :=
    metric_target_domain_smooth (I := I) Φ k
  intro x v
  let F := metricSourceTargetDiffeomorph (I := I) Φ k
  have hFd : MDifferentiableAt I I (F : MetricSourceDomain (I := I) Φ k ->
      MetricTargetDomain (I := I) Φ k) x :=
    F.contMDiff.contMDiffAt.mdifferentiableAt (by decide)
  have hvalT : MDifferentiableAt I I
      (Subtype.val : MetricTargetDomain (I := I) Φ k -> (X.obj (subseq k)).M) (F x) :=
    ContMDiffAt.mdifferentiableAt
      ((contMDiff_subtype_val (I := I) (n := (∞ : WithTop ℕ∞))
        (U := metricTargetOpenSubset (I := I) Φ k)).contMDiffAt)
      (by decide)
  have hvalS : MDifferentiableAt I I
      (Subtype.val : MetricSourceDomain (I := I) Φ k -> L.M) x :=
    ContMDiffAt.mdifferentiableAt
      ((contMDiff_subtype_val (I := I) (n := (∞ : WithTop ℕ∞))
        (U := metricSourceOpenSubset (I := I) Φ k)).contMDiffAt)
      (by decide)
  have hmap : MDifferentiableAt I I (Φ.map k) (x : L.M) :=
    ((Φ.partialDiffeomorph k).contMDiffOn_toFun.contMDiffAt
      ((Φ.partialDiffeomorph k).open_source.mem_nhds x.2)).mdifferentiableAt (by decide)
  have hleft := mfderiv_comp x hvalT hFd
  have hright := mfderiv_comp x hmap hvalS
  have hfun :
      (fun y : MetricSourceDomain (I := I) Φ k => ((F y :
        MetricTargetDomain (I := I) Φ k) : (X.obj (subseq k)).M)) =
        fun y : MetricSourceDomain (I := I) Φ k => Φ.map k (y : L.M) := by
    funext y
    exact metric_source_target_diffeomorph_apply (I := I) Φ k y
  have heq : mfderiv I I
      (fun y : MetricSourceDomain (I := I) Φ k => ((F y :
        MetricTargetDomain (I := I) Φ k) : (X.obj (subseq k)).M)) x =
      mfderiv I I (fun y : MetricSourceDomain (I := I) Φ k => Φ.map k (y : L.M)) x := by
    rw [hfun]
  have happ := DFunLike.congr_fun (hleft.symm.trans (heq.trans hright)) v
  change
      (mfderiv I I
          (Subtype.val : MetricTargetDomain (I := I) Φ k -> (X.obj (subseq k)).M) (F x))
        (mfderiv I I (F : MetricSourceDomain (I := I) Φ k ->
          MetricTargetDomain (I := I) Φ k) x v) =
      (mfderiv I I (Φ.map k) (x : L.M))
        (mfderiv I I (Subtype.val : MetricSourceDomain (I := I) Φ k -> L.M) x v) at happ
  have htarget :
      (mfderiv I I
          (Subtype.val : MetricTargetDomain (I := I) Φ k -> (X.obj (subseq k)).M) (F x))
        (mfderiv I I (F : MetricSourceDomain (I := I) Φ k ->
          MetricTargetDomain (I := I) Φ k) x v) =
        mfderiv I I (F : MetricSourceDomain (I := I) Φ k ->
          MetricTargetDomain (I := I) Φ k) x v := by
    simpa only using mfderiv_subtype_val_apply (I := I)
      (metricTargetOpenSubset (I := I) Φ k) (F x)
      (mfderiv I I (F : MetricSourceDomain (I := I) Φ k ->
        MetricTargetDomain (I := I) Φ k) x v)
  have hsource :
      mfderiv I I (Subtype.val : MetricSourceDomain (I := I) Φ k -> L.M) x v = v := by
    simpa only using mfderiv_subtype_val_apply (I := I)
      (metricSourceOpenSubset (I := I) Φ k) x v
  rw [htarget, hsource] at happ
  exact happ

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
@[simp]
theorem metric_source_target_diffeomorph_symm_apply
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : Nat)
    (y : MetricTargetDomain (I := I) Φ k) :
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : TopologicalSpace (X.obj (subseq k)).M := (X.obj (subseq k)).topology
    letI : ChartedSpace H (X.obj (subseq k)).M := (X.obj (subseq k)).charted
    letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomainTopology (I := I) Φ k
    letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomainChartedSpace (I := I) Φ k
    letI : TopologicalSpace (MetricTargetDomain (I := I) Φ k) :=
      metricTargetDomainTopology (I := I) Φ k
    letI : ChartedSpace H (MetricTargetDomain (I := I) Φ k) :=
      metricTargetDomainChartedSpace (I := I) Φ k
    ((metricSourceTargetDiffeomorph (I := I) Φ k).symm y : L.M) =
      (Φ.partialDiffeomorph k).toPartialEquiv.symm (y : (X.obj (subseq k)).M) := by
  rfl

def metricSourceCompactSet
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : Nat)
    (K : Set L.M) : Set (MetricSourceDomain (I := I) Φ k) :=
  {x | (x : L.M) ∈ K}

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem metric_source_compact_set_is_compact
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : Nat)
    {K : Set L.M}
    (hK :
      letI : TopologicalSpace L.M := L.topology
      IsCompact K)
    (hKsrc :
      letI : TopologicalSpace L.M := L.topology
      K ⊆ Φ.source k) :
    letI : TopologicalSpace L.M := L.topology
    IsCompact (metricSourceCompactSet (I := I) Φ k K) := by
  let : TopologicalSpace L.M := L.topology
  change IsCompact ((Subtype.val : MetricSourceDomain (I := I) Φ k -> L.M) ⁻¹' K)
  rw [Subtype.isCompact_iff]
  have hImage :
      Subtype.val '' ((Subtype.val : MetricSourceDomain (I := I) Φ k -> L.M) ⁻¹' K) =
        K := by
    ext x
    constructor
    · rintro ⟨y, hyK, rfl⟩
      exact hyK
    · intro hxK
      exact ⟨⟨x, hKsrc hxK⟩, hxK, rfl⟩
  rw [hImage]
  exact hK


end MetricCompactnessCore

end HCGCompactness
end DifferentialGeometry
