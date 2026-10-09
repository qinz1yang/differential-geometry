import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Foundations.PointedMaps
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CGHSubsequenceClosure
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SameManifoldSlabWindowLink

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open scoped _root_.Manifold ContDiff _root_.Topology

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

namespace PointedFlowSeq

def subseq (X : PointedFlowSeq.{u, uE, uH} (I := I)) (f : Nat -> Nat) :
    PointedFlowSeq.{u, uE, uH} (I := I) where
  D := X.D
  term := fun i => X.term (f i)

@[simp] theorem subseq_D (X : PointedFlowSeq.{u, uE, uH} (I := I)) (f : Nat -> Nat) :
    (X.subseq f).D = X.D := rfl

@[simp] theorem subseq_term (X : PointedFlowSeq.{u, uE, uH} (I := I)) (f : Nat -> Nat)
    (i : Nat) : (X.subseq f).term i = X.term (f i) := rfl

@[simp] theorem subseq_atTime (X : PointedFlowSeq.{u, uE, uH} (I := I)) (f : Nat -> Nat)
    (t : Real) : (X.subseq f).atTime (I := I) t = (X.atTime (I := I) t).subseq f := rfl

end PointedFlowSeq

namespace PointedCGHMaps

def ofSeqSubseq
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    (f : Nat -> Nat)
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {inner : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) (X.subseq f) P inner) :
    PointedCGHMaps (I := I) X P (f ∘ inner) where
  partialDiffeomorph := Φ.partialDiffeomorph
  source_exhausts := Φ.source_exhausts
  base_mem := Φ.base_mem
  basepoint_map := Φ.basepoint_map

def ofSubseq
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    (f : Nat -> Nat)
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    (Φ : PointedCGHMaps (I := I) (X.subseq f) P id) :
    PointedCGHMaps (I := I) X P f :=
  Φ.ofSeqSubseq f

@[simp] theorem ofSeqSubseq_source
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    (f : Nat -> Nat)
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {inner : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) (X.subseq f) P inner) (k : Nat) :
    (Φ.ofSeqSubseq f).source k = Φ.source k := rfl

@[simp] theorem ofSeqSubseq_map
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    (f : Nat -> Nat)
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {inner : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) (X.subseq f) P inner) (k : Nat) :
    (Φ.ofSeqSubseq f).map k = Φ.map k := rfl

@[simp] theorem ofSubseq_source
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    (f : Nat -> Nat)
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    (Φ : PointedCGHMaps (I := I) (X.subseq f) P id) (k : Nat) :
    (Φ.ofSubseq f).source k = Φ.source k := rfl

@[simp] theorem ofSubseq_map
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    (f : Nat -> Nat)
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    (Φ : PointedCGHMaps (I := I) (X.subseq f) P id) (k : Nat) :
    (Φ.ofSubseq f).map k = Φ.map k := rfl

end PointedCGHMaps

namespace MetricInnerPullbackTendsto

theorem ofSeqSubseq
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {inner : Nat -> Nat} (f : Nat -> Nat)
    {Φ : PointedCGHMaps (I := I) (X.subseq f) P inner}
    {gInf : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      Real -> SmoothRiemannianMetric I P.M}
    (h : MetricInnerPullbackTendsto (I := I) Φ gInf) :
    MetricInnerPullbackTendsto (I := I) (Φ.ofSeqSubseq f) gInf := by
  intro t ht x v w
  refine Filter.Tendsto.congr' ?_ (h t ht x v w)
  filter_upwards with k
  rfl

end MetricInnerPullbackTendsto

namespace MetricPullbackTendsto

theorem ofSeqSubseq
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D}
    {inner : Nat -> Nat} (f : Nat -> Nat)
    {Φ : PointedCGHMaps (I := I) (X.subseq f) (L.atTime 0) inner}
    (h : MetricPullbackTendsto (I := I) Φ) :
    MetricPullbackTendsto (I := I) (Φ.ofSeqSubseq f) :=
  MetricInnerPullbackTendsto.ofSeqSubseq (I := I) f h

end MetricPullbackTendsto

namespace MetricRicciPullbackTendsto

theorem ofSeqSubseq
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {inner : Nat -> Nat} (f : Nat -> Nat)
    {Φ : PointedCGHMaps (I := I) (X.subseq f) P inner}
    {gInf : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      Real -> SmoothRiemannianMetric I P.M}
    (h : MetricRicciPullbackTendsto (I := I) Φ gInf) :
    MetricRicciPullbackTendsto (I := I) (Φ.ofSeqSubseq f) gInf := by
  intro t ht x v w
  refine Filter.Tendsto.congr' ?_ (h t ht x v w)
  filter_upwards with k
  rfl

end MetricRicciPullbackTendsto

namespace RicciPullbackTendsto

theorem ofSeqSubseq
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D}
    {inner : Nat -> Nat} (f : Nat -> Nat)
    {Φ : PointedCGHMaps (I := I) (X.subseq f) (L.atTime 0) inner}
    (h : RicciPullbackTendsto (I := I) Φ) :
    RicciPullbackTendsto (I := I) (Φ.ofSeqSubseq f) :=
  MetricRicciPullbackTendsto.ofSeqSubseq (I := I) f h

end RicciPullbackTendsto

namespace FunctionPullbackTendsto

theorem ofSeqSubseq
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {inner : Nat -> Nat} (f : Nat -> Nat)
    {Φ : PointedCGHMaps (I := I) (X.subseq f) P inner}
    {uSeq : forall k : Nat, Real -> ((X.subseq f).term (inner k)).M -> Real}
    {uInf : Real -> P.M -> Real}
    (h : FunctionPullbackTendsto (I := I) Φ uSeq uInf) :
    FunctionPullbackTendsto (I := I) (Φ.ofSeqSubseq f) uSeq uInf := by
  intro t ht x
  refine Filter.Tendsto.congr' ?_ (h t ht x)
  filter_upwards with k
  rfl

end FunctionPullbackTendsto

namespace ScalarPullbackTendsto

theorem ofSeqSubseq
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D}
    {inner : Nat -> Nat} (f : Nat -> Nat)
    {Φ : PointedCGHMaps (I := I) (X.subseq f) (L.atTime 0) inner}
    (h : ScalarPullbackTendsto (I := I) Φ) :
    ScalarPullbackTendsto (I := I) (Φ.ofSeqSubseq f) := by
  intro t ht x
  refine Filter.Tendsto.congr' ?_ (h t ht x)
  filter_upwards with k
  rfl

end ScalarPullbackTendsto

namespace RicNormPullback

theorem ofSeqSubseq
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D}
    {inner : Nat -> Nat} (f : Nat -> Nat)
    {Φ : PointedCGHMaps (I := I) (X.subseq f) (L.atTime 0) inner}
    (h : RicNormPullback (I := I) Φ) :
    RicNormPullback (I := I) (Φ.ofSeqSubseq f) := by
  intro t ht x
  refine Filter.Tendsto.congr' ?_ (h t ht x)
  filter_upwards with k
  rfl

end RicNormPullback

namespace SourceDomainMetricData

def ofSeqSubseq
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {inner : Nat -> Nat} (f : Nat -> Nat)
    {Φ : PointedCGHMaps (I := I) (X.subseq f) P inner}
    (k : Nat) (D : SourceDomainMetricData (I := I) Φ k) :
    SourceDomainMetricData (I := I) (Φ.ofSeqSubseq f) k where
  topology := D.topology
  charted := D.charted
  t2 := D.t2
  smooth := D.smooth
  sigmaCompact := D.sigmaCompact
  limitMetric := D.limitMetric
  pullbackMetric := D.pullbackMetric
  referenceMetric := D.referenceMetric
  limitMetricFamily := D.limitMetricFamily
  compact_preimage := D.compact_preimage
  limit_inner := D.limit_inner
  pullback_inner := D.pullback_inner

@[simp] theorem ofSeqSubseq_derivNormSupOn
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {inner : Nat -> Nat} (f : Nat -> Nat)
    {Φ : PointedCGHMaps (I := I) (X.subseq f) P inner}
    (k : Nat) (D : SourceDomainMetricData (I := I) Φ k)
    (K : Set P.M) (p : Nat) (t : Real) :
    (ofSeqSubseq (I := I) f k D).derivNormSupOn (I := I) K p t =
      D.derivNormSupOn (I := I) K p t := rfl

end SourceDomainMetricData

namespace SourceMetricConvergenceData

def ofSeqSubseq
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {inner : Nat -> Nat} (f : Nat -> Nat)
    {Φ : PointedCGHMaps (I := I) (X.subseq f) P inner}
    (Cd : SourceMetricConvergenceData (I := I) Φ) :
    SourceMetricConvergenceData (I := I) (Φ.ofSeqSubseq f) where
  domain k := SourceDomainMetricData.ofSeqSubseq (I := I) f k (Cd.domain k)
  converges := by
    intro K hK p t ht ε hε
    obtain ⟨k0, hk0⟩ := Cd.converges K hK p t ht ε hε
    exact ⟨k0, fun k hk => by
      simpa only [PointedCGHMaps.ofSeqSubseq_source,
        SourceDomainMetricData.ofSeqSubseq_derivNormSupOn] using hk0 k hk⟩

end SourceMetricConvergenceData

namespace SourceSpacetimeConvergenceData

theorem ofSeqSubseq
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {inner : Nat -> Nat} (f : Nat -> Nat)
    {Φ : PointedCGHMaps (I := I) (X.subseq f) P inner}
    {D : forall k : Nat, SourceDomainMetricData (I := I) Φ k}
    (Hst : SourceSpacetimeConvergenceData (I := I) Φ D) :
    SourceSpacetimeConvergenceData (I := I) (Φ.ofSeqSubseq f)
      (fun k => SourceDomainMetricData.ofSeqSubseq (I := I) f k (D k)) where
  converges_on_windows := by
    intro K hK p a b hwin ε hε
    obtain ⟨k0, hk0⟩ := Hst.converges_on_windows K hK p a b hwin ε hε
    exact ⟨k0, fun k hk => by
      simpa only [PointedCGHMaps.ofSeqSubseq_source,
        SourceDomainMetricData.ofSeqSubseq_derivNormSupOn] using hk0 k hk⟩

end SourceSpacetimeConvergenceData

namespace PointedCGConverges

def ofSeqSubseq
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D}
    {inner : Nat -> Nat} (f : Nat -> Nat)
    (C : PointedCGConverges (I := I) (X.subseq f) L inner) :
    PointedCGConverges (I := I) X L (f ∘ inner) where
  maps := C.maps.ofSeqSubseq f
  metrics := C.metrics.ofSeqSubseq f

def ofSubseq
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D}
    (f : Nat -> Nat)
    (C : PointedCGConverges (I := I) (X.subseq f) L id) :
    PointedCGConverges (I := I) X L f :=
  C.ofSeqSubseq f

end PointedCGConverges

namespace SmoothCGHConverges

def ofSeqSubseq
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D}
    {inner : Nat -> Nat} (f : Nat -> Nat)
    (h : SmoothCGHConverges (I := I) (X.subseq f) L inner) :
    SmoothCGHConverges (I := I) X L (f ∘ inner) where
  spatial := h.spatial.ofSeqSubseq f
  metric_converges := h.metric_converges.ofSeqSubseq f
  scalar_converges := h.scalar_converges.ofSeqSubseq f
  ricci_converges := h.ricci_converges.ofSeqSubseq f
  ricciNorm_converges := h.ricciNorm_converges.ofSeqSubseq f
  spacetime := h.spacetime.ofSeqSubseq f

def ofSubseq
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D}
    (f : Nat -> Nat)
    (h : SmoothCGHConverges (I := I) (X.subseq f) L id) :
    SmoothCGHConverges (I := I) X L f :=
  h.ofSeqSubseq f

end SmoothCGHConverges

namespace SourceMetricCPConvergenceOnWindow

theorem mono
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedCGHMaps (I := I) X P subseq}
    {D : forall k : Nat, SourceDomainMetricData (I := I) Φ k}
    {K : Set P.M} {p : Nat} {a b a' b' : Real}
    (h : SourceMetricCPConvergenceOnWindow (I := I) Φ D K p a b)
    (hwin : Set.Icc a' b' ⊆ Set.Icc a b) :
    SourceMetricCPConvergenceOnWindow (I := I) Φ D K p a' b' := by
  intro ε hε
  obtain ⟨k0, hk0⟩ := h ε hε
  exact ⟨k0, fun k hk => ⟨(hk0 k hk).1, fun t ht => (hk0 k hk).2 t (hwin ht)⟩⟩

end SourceMetricCPConvergenceOnWindow

namespace SourceSpacetimeConvergenceData

theorem of_exhausting_windows
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedCGHMaps (I := I) X P subseq}
    {D : forall k : Nat, SourceDomainMetricData (I := I) Φ k}
    {T U : Nat -> Real}
    (h : forall K : Set P.M,
      (letI : TopologicalSpace P.M := P.topology; IsCompact K) ->
      forall p : Nat, forall m : Nat,
        SourceMetricCPConvergenceOnWindow (I := I) Φ D K p (T m) (U m))
    (hcov : forall a b : Real, Set.Icc a b ⊆ X.D.carrier ->
      exists m : Nat, Set.Icc a b ⊆ Set.Icc (T m) (U m)) :
    SourceSpacetimeConvergenceData (I := I) Φ D where
  converges_on_windows := by
    intro K hK p a b hwin
    obtain ⟨m, hm⟩ := hcov a b hwin
    exact SourceMetricCPConvergenceOnWindow.mono (I := I) (h K hK p m) hm

end SourceSpacetimeConvergenceData

namespace PointedCGHMaps

theorem atTimeSlice_compSubseq
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D} {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X (L.atTime 0) subseq)
    (φ : Nat -> Nat) (hφ : StrictMono φ) (t : Real) :
    (Φ.compSubseq φ hφ).atTimeSlice (I := I) t =
      (Φ.atTimeSlice (I := I) t).compSubseq φ hφ := rfl

end PointedCGHMaps

theorem metricDerivNorm_self_eq_zero
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    [IsManifold I ∞ M]
    (g : SmoothRiemannianMetric I M) (a : Nat) (x : M) :
    metricDerivNorm (I := I) a g g g x = 0 := by
  rw [metricDerivNorm, metricDiffCovDerivAt, sub_self]
  simp [Tensor0SBundle.normSq0S, Tensor0SBundle.inner0S, Tensor0SBundle.MetricFiberData.inner]

theorem metricDerivNormSupOn_self_le_zero
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    [IsManifold I ∞ M]
    (K : Set M) (p : Nat) (g : SmoothRiemannianMetric I M) :
    metricDerivNormSupOn (I := I) K p g g g ≤ 0 :=
  metricDerivNormSupOn_le_of_forall (I := I) K p g g g 0 le_rfl
    fun a _ x _ => by rw [metricDerivNorm_self_eq_zero]

namespace PointedFlowData

noncomputable def staticEuclideanLine (D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval) :
    PointedFlowData.{0, 0, 0} (I := 𝓘(Real, Real)) D where
  M := Real
  basepoint := 0
  S := PDE.RicciFlow.SolutionOn.const (euclideanMetric (E := Real)) D
  isSolution := PDE.RicciFlow.isSolutionOn_const_euclidean_real D

end PointedFlowData

namespace PointedFlowSeq

noncomputable def const
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) :
    PointedFlowSeq.{u, uE, uH} (I := I) where
  D := D
  term := fun _ => F

end PointedFlowSeq

namespace PointedCGHMaps

noncomputable def staticEuclideanLine
    (D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval) :
    PointedCGHMaps (I := 𝓘(Real, Real))
      (PointedFlowSeq.const (PointedFlowData.staticEuclideanLine D))
      ((PointedFlowData.staticEuclideanLine D).atTime (I := 𝓘(Real, Real)) 0) id where
  partialDiffeomorph _ := PartialDiffeomorph.refl (I := 𝓘(Real, Real)) Real
  source_exhausts := by
    have hfun :
        (fun _ : Nat => (PartialDiffeomorph.refl (I := 𝓘(Real, Real)) Real).source) =
          (fun _ : Nat => (Set.univ : Set Real)) := by
      funext _
      rfl
    rw [hfun]
    exact ExhaustsByOpen.univ Real
  base_mem _ := Set.mem_univ _
  basepoint_map _ := rfl

end PointedCGHMaps
@[simp] theorem PointedCGHMaps.staticEuclideanLine_source
    (D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval) (k : Nat) :
    (PointedCGHMaps.staticEuclideanLine D).source (I := 𝓘(Real, Real)) k =
      (Set.univ : Set Real) := rfl

@[simp] theorem PointedCGHMaps.staticEuclideanLine_map
    (D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval) (k : Nat) (x : Real) :
    (PointedCGHMaps.staticEuclideanLine D).map (I := 𝓘(Real, Real)) k x = x := rfl

@[simp] theorem PointedFlowSeq.const_subseq
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) (f : Nat -> Nat) :
    (PointedFlowSeq.const F).subseq f = PointedFlowSeq.const F := rfl

noncomputable def PointedCGHMaps.staticEuclideanLineOfSubseq
    (D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval) :
    PointedCGHMaps (I := 𝓘(Real, Real))
      (PointedFlowSeq.const (PointedFlowData.staticEuclideanLine D))
      ((PointedFlowData.staticEuclideanLine D).atTime (I := 𝓘(Real, Real)) 0) id :=
  (show PointedCGHMaps (I := 𝓘(Real, Real))
      ((PointedFlowSeq.const (PointedFlowData.staticEuclideanLine D)).subseq id)
      ((PointedFlowData.staticEuclideanLine D).atTime (I := 𝓘(Real, Real)) 0) id from
    PointedCGHMaps.staticEuclideanLine D).ofSubseq id

end CheegerGromovCompactness
end DifferentialGeometry
