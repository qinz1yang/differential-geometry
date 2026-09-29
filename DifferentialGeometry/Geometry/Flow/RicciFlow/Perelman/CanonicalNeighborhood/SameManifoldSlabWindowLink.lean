import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SameManifoldWindowCompactness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.MaximalPointSlabLimit

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Tensor0SBundle
open scoped _root_.DifferentialGeometry.Manifold ContDiff ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]

omit [SigmaCompactSpace M] in
theorem sameManifoldSlab_isSolutionOn_intervalCast {D₁ D₂ : RealTimeInterval} (h : D₁ = D₂)
    (S : SolutionOn (I := I3) (M := M) D₁) (hS : IsSolutionOn (I := I3) S) :
    IsSolutionOn (I := I3) (h ▸ S : SolutionOn (I := I3) (M := M) D₂) := by
  cases h
  exact hS

omit [T2Space M] [SigmaCompactSpace M] in
theorem sameManifoldSlab_solutionOn_intervalCast_base_metric {D₁ D₂ : RealTimeInterval}
    (h : D₁ = D₂) (S : SolutionOn (I := I3) (M := M) D₁) (s : ℝ) :
    ((h ▸ S : SolutionOn (I := I3) (M := M) D₂)).base.metric s = S.base.metric s := by
  cases h
  rfl

theorem highCurvatureSlabIntervalEq {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (x : ℕ → M) (t : ℕ → ℝ)
    (htmem : ∀ i, t i ∈ Set.Ico (0 : ℝ) T) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i)) (i : ℕ) :
    (highCurvatureFlowSequence hT S hS x t htmem htpos hpos).interval i =
      KappaSolutions.arcInterval (t i * S.scalar (t i) (x i)) :=
  KappaSolutions.highCurvatureInterval_eq_arcInterval hT S x t htpos hpos i

noncomputable def highCurvatureSlabFlow {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (x : ℕ → M) (t : ℕ → ℝ)
    (htmem : ∀ i, t i ∈ Set.Ico (0 : ℝ) T) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i)) (i : ℕ) :
    PointedFlowData.{u, 0, 0} (I := I3)
      (KappaSolutions.arcInterval (t i * S.scalar (t i) (x i))) where
  M := M
  basepoint := x i
  S :=
    (highCurvatureSlabIntervalEq hT S hS x t htmem htpos hpos i) ▸
      ((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).term i).S
  isSolution :=
    sameManifoldSlab_isSolutionOn_intervalCast
      (highCurvatureSlabIntervalEq hT S hS x t htmem htpos hpos i)
      ((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).term i).S
      ((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).term i).isSolution

@[simp] theorem highCurvatureSlabFlow_basepoint {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (x : ℕ → M) (t : ℕ → ℝ)
    (htmem : ∀ i, t i ∈ Set.Ico (0 : ℝ) T) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i)) (i : ℕ) :
    (highCurvatureSlabFlow hT S hS x t htmem htpos hpos i).basepoint = x i :=
  rfl

theorem highCurvatureSlabFlow_metric {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (x : ℕ → M) (t : ℕ → ℝ)
    (htmem : ∀ i, t i ∈ Set.Ico (0 : ℝ) T) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i)) (i : ℕ) (s : ℝ) :
    (highCurvatureSlabFlow hT S hS x t htmem htpos hpos i).S.base.metric s =
      rescaledMetric (I := I3) S (t i) (S.scalar (t i) (x i)) (hpos i) s :=
  (sameManifoldSlab_solutionOn_intervalCast_base_metric
      (highCurvatureSlabIntervalEq hT S hS x t htmem htpos hpos i)
      ((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).term i).S s).trans
    (congrFun (highCurvatureFlowSequence_metric hT S hS x t htmem htpos hpos i) s)

noncomputable def highCurvatureSameManifoldFlowSeq {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (x : ℕ → M) (t : ℕ → ℝ)
    (htmem : ∀ i, t i ∈ Set.Ico (0 : ℝ) T) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i)) :
    KappaSolutions.SameManifoldFlowSeq.{u, 0, 0} I3 M where
  horizon i := t i * S.scalar (t i) (x i)
  horizon_pos i := mul_pos (htpos i) (hpos i)
  basepoint i := x i
  t2TangentBundle := (highCurvatureSlabFlow hT S hS x t htmem htpos hpos 0).t2TangentBundle
  solution i := (highCurvatureSlabFlow hT S hS x t htmem htpos hpos i).S
  isSolution i := (highCurvatureSlabFlow hT S hS x t htmem htpos hpos i).isSolution

@[simp] theorem highCurvatureSameManifoldFlowSeq_horizon {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (x : ℕ → M) (t : ℕ → ℝ)
    (htmem : ∀ i, t i ∈ Set.Ico (0 : ℝ) T) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i)) (i : ℕ) :
    (highCurvatureSameManifoldFlowSeq hT S hS x t htmem htpos hpos).horizon i =
      t i * S.scalar (t i) (x i) :=
  rfl

@[simp] theorem highCurvatureSameManifoldFlowSeq_basepoint {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (x : ℕ → M) (t : ℕ → ℝ)
    (htmem : ∀ i, t i ∈ Set.Ico (0 : ℝ) T) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i)) (i : ℕ) :
    (highCurvatureSameManifoldFlowSeq hT S hS x t htmem htpos hpos).basepoint i = x i :=
  rfl

@[simp] theorem highCurvatureSameManifoldFlowSeq_metricFamily {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (x : ℕ → M) (t : ℕ → ℝ)
    (htmem : ∀ i, t i ∈ Set.Ico (0 : ℝ) T) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i)) (i : ℕ) (s : ℝ) :
    ((highCurvatureSameManifoldFlowSeq hT S hS x t htmem htpos hpos).solution i).family.metric s =
      rescaledMetric (I := I3) S (t i) (S.scalar (t i) (x i)) (hpos i) s :=
  highCurvatureSlabFlow_metric hT S hS x t htmem htpos hpos i s

@[simp] theorem highCurvatureSameManifoldFlowSeq_term_metric {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (x : ℕ → M) (t : ℕ → ℝ)
    (htmem : ∀ i, t i ∈ Set.Ico (0 : ℝ) T) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i)) (i : ℕ) (u : ℝ) :
    (((highCurvatureSameManifoldFlowSeq hT S hS x t htmem htpos hpos).toFiniteArcFlowSeq.term
      i).atTime (I := I3) u).metric =
      rescaledMetric (I := I3) S (t i) (S.scalar (t i) (x i)) (hpos i) u :=
  highCurvatureSlabFlow_metric hT S hS x t htmem htpos hpos i u

theorem highCurvatureSameManifoldFlowSeq_horizon_tendsto {T theta : ℝ} (hT : 0 < T)
    (htheta : 0 < theta)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (x : ℕ → M) (t : ℕ → ℝ)
    (htmem : ∀ i, t i ∈ Set.Ico (0 : ℝ) T) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i)) (htle : ∀ i, theta ≤ t i)
    (hscalar : Filter.Tendsto (fun i => S.scalar (t i) (x i)) Filter.atTop Filter.atTop) :
    Filter.Tendsto
      (highCurvatureSameManifoldFlowSeq hT S hS x t htmem htpos hpos).horizon
      Filter.atTop Filter.atTop := by
  have hfun : (highCurvatureSameManifoldFlowSeq hT S hS x t htmem htpos hpos).horizon =
      fun i => t i * S.scalar (t i) (x i) := rfl
  rw [hfun]
  exact KappaSolutions.tendsto_mul_atTop_of_pos_le_scalar theta htheta t
    (fun i => S.scalar (t i) (x i)) htle hscalar

noncomputable def highCurvatureSlabArcSeq {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (x : ℕ → M) (t : ℕ → ℝ)
    (htmem : ∀ i, t i ∈ Set.Ico (0 : ℝ) T) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i)) :
    KappaSolutions.FiniteArcFlowSeq.{u, 0, 0} (I := I3) :=
  (highCurvatureSameManifoldFlowSeq hT S hS x t htmem htpos hpos).toFiniteArcFlowSeq

def SlabSameManifoldWindowCompactness {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (x : ℕ → M) (t : ℕ → ℝ)
    (htmem : ∀ i, t i ∈ Set.Ico (0 : ℝ) T) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i))
    (hTend : Filter.Tendsto (highCurvatureSlabArcSeq hT S hS x t htmem htpos hpos).horizon
      Filter.atTop Filter.atTop) : Prop :=
  KappaSolutions.SameManifoldWindowCompactness
    (highCurvatureSameManifoldFlowSeq hT S hS x t htmem htpos hpos) hTend

noncomputable def SlabWindowEstimates {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (x : ℕ → M) (t : ℕ → ℝ)
    (htmem : ∀ i, t i ∈ Set.Ico (0 : ℝ) T) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i))
    (hTend : Filter.Tendsto (highCurvatureSlabArcSeq hT S hS x t htmem htpos hpos).horizon
      Filter.atTop Filter.atTop) :=
  let X := highCurvatureSlabArcSeq hT S hS x t htmem htpos hpos
  ∀ m : ℕ, KappaSolutions.WindowCompactnessEstimates (X.tail (X.windowShift hTend m))
    (KappaSolutions.windowHorizon m) (KappaSolutions.windowHorizon_pos m)
    (fun k => X.le_horizon_add_windowShift hTend m k)

theorem slabSameManifoldWindowCompactness_of_windowCompactnessFrontier {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (x : ℕ → M) (t : ℕ → ℝ)
    (htmem : ∀ i, t i ∈ Set.Ico (0 : ℝ) T) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i))
    (hTend : Filter.Tendsto (highCurvatureSlabArcSeq hT S hS x t htmem htpos hpos).horizon
      Filter.atTop Filter.atTop)
    (hfrontier : KappaSolutions.WindowCompactnessFrontier
      (highCurvatureSlabArcSeq hT S hS x t htmem htpos hpos) hTend) :
    SlabSameManifoldWindowCompactness hT S hS x t htmem htpos hpos hTend :=
  KappaSolutions.sameManifoldWindowCompactness_of_windowCompactnessFrontier _ _ hfrontier

theorem finiteArcWindowCompactnessInput_of_slabSameManifoldWindowCompactness {T : ℝ}
    (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (x : ℕ → M) (t : ℕ → ℝ)
    (htmem : ∀ i, t i ∈ Set.Ico (0 : ℝ) T) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i))
    (hTend : Filter.Tendsto (highCurvatureSlabArcSeq hT S hS x t htmem htpos hpos).horizon
      Filter.atTop Filter.atTop)
    (h : SlabSameManifoldWindowCompactness hT S hS x t htmem htpos hpos hTend)
    (hest : SlabWindowEstimates hT S hS x t htmem htpos hpos hTend) :
    KappaSolutions.FiniteArcWindowCompactnessInput
      (highCurvatureSlabArcSeq hT S hS x t htmem htpos hpos) hTend :=
  fun m φ hφ => h m φ hφ (hest m)

theorem exists_strictMono_windowConverges_of_slabSameManifoldWindowCompactness {T : ℝ}
    (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (x : ℕ → M) (t : ℕ → ℝ)
    (htmem : ∀ i, t i ∈ Set.Ico (0 : ℝ) T) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i))
    (hTend : Filter.Tendsto (highCurvatureSlabArcSeq hT S hS x t htmem htpos hpos).horizon
      Filter.atTop Filter.atTop)
    (h : SlabSameManifoldWindowCompactness hT S hS x t htmem htpos hpos hTend)
    (hest : SlabWindowEstimates hT S hS x t htmem htpos hpos hTend) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ m : ℕ,
      (highCurvatureSlabArcSeq hT S hS x t htmem htpos hpos).WindowConverges
        hTend m (fun k => φ (m + k)) :=
  KappaSolutions.exists_strictMono_forall_shift_windowConverges _ hTend
    (finiteArcWindowCompactnessInput_of_slabSameManifoldWindowCompactness hT S hS x t htmem htpos
      hpos hTend h hest)
    (fun m φ ψ L hψ hconv =>
      KappaSolutions.FiniteArcFlowSeq.windowConverges_subseqClosure _ hTend m φ ψ L hψ hconv)

theorem eventually_of_eventually_add (P : ℕ → Prop) {N : ℕ}
    (h : ∀ᶠ k : ℕ in Filter.atTop, P (N + k)) :
    ∀ᶠ k : ℕ in Filter.atTop, P k := by
  obtain ⟨k0, hk0⟩ := Filter.eventually_atTop.mp h
  refine Filter.eventually_atTop.mpr ⟨N + k0, fun k hk => ?_⟩
  have hNk : N ≤ k := by omega
  have : P (N + (k - N)) := hk0 (k - N) (by omega)
  rwa [Nat.add_sub_cancel' hNk] at this

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.CheegerGromovCompactness

open DifferentialGeometry.Geometry.Curvature
open scoped _root_.DifferentialGeometry.Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

noncomputable def PointedCGHMaps.atTimeSlice
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D} {subseq : ℕ → ℕ}
    (Φ : PointedCGHMaps (I := I) X (L.atTime (I := I) 0) subseq) (t : ℝ) :
    PointedRiemannianConvergenceMaps (I := I) (X.atTime (I := I) t)
      (L.atTime (I := I) t) subseq where
  partialDiffeomorph k := Φ.partialDiffeomorph k
  source_exhausts := Φ.source_exhausts
  base_mem k := Φ.base_mem k
  basepoint_map k := Φ.basepoint_map k

omit [I.Boundaryless] in
@[simp] theorem PointedCGHMaps.atTimeSlice_source
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D} {subseq : ℕ → ℕ}
    (Φ : PointedCGHMaps (I := I) X (L.atTime (I := I) 0) subseq) (t : ℝ) (k : ℕ) :
    (Φ.atTimeSlice (I := I) t).source k = Φ.source k :=
  rfl

omit [I.Boundaryless] in
theorem metricSourceConvergesOn_atTimeSlice
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D} {subseq : ℕ → ℕ}
    {Φ : PointedCGHMaps (I := I) X (L.atTime (I := I) 0) subseq}
    {D : ∀ k : ℕ, SourceDomainMetricData (I := I) Φ k} {K : Set (L.atTime (I := I) 0).M}
    {p : ℕ} {t : ℝ}
    (h : SourceMetricCPConvergenceOn (I := I) Φ D K p t)
    (D' : ∀ k : ℕ, MetricSourceData (I := I) (Φ.atTimeSlice (I := I) t) k)
    (hderiv : ∀ k : ℕ,
      (D' k).derivNormSupOn (I := I) K p = (D k).derivNormSupOn (I := I) K p t) :
    metricSourceConvergesOn (I := I) (Φ.atTimeSlice (I := I) t) D' K p := by
  intro ε hε
  obtain ⟨k0, hk0⟩ := h ε hε
  exact ⟨k0, fun k hk => ⟨(hk0 k hk).1, by rw [hderiv k]; exact (hk0 k hk).2⟩⟩

end DifferentialGeometry.CheegerGromovCompactness

end
