import DifferentialGeometry.Topology.Manifold.PartialDiffeomorphOpens
import DifferentialGeometry.Geometry.Curvature.PullbackNaturalityCross
import DifferentialGeometry.Geometry.Curvature.RestrictOpenRm04
import DifferentialGeometry.Geometry.Metric.LocalPullback
import DifferentialGeometry.Topology.SigmaCompactOpen

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open Set TopologicalSpace
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [CompleteSpace E] [NeZero (Module.finrank Real E)]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace Real F]
  [FiniteDimensional Real F] [CompleteSpace F] [NeZero (Module.finrank Real F)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {G : Type*} [TopologicalSpace G] {J : ModelWithCorners Real F G}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [IsManifold I 1 M]
  [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [IsManifold J ∞ N] [IsManifold J 1 N]
  [T2Space N] [SigmaCompactSpace N] [J.Boundaryless]

omit [NeZero (Module.finrank ℝ E)] [NeZero (Module.finrank ℝ F)] in
theorem rm04_localPull
    (g : SmoothRiemannianMetric J N) (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f)
    (x : M) (X Y Z W : TangentSpace I x) :
    metricRm04StdAt (I := I) (M := M)
        (localPullMetric (I := I) (J := J) g f hf) x X Y Z W =
      metricRm04StdAt (I := J) (M := N) g (f x)
        (mfderiv I J f x X) (mfderiv I J f x Y)
        (mfderiv I J f x Z) (mfderiv I J f x W) := by
  let Φ : PartialDiffeomorph I J M N ∞ := Classical.choose (hf x)
  have hxΦ : x ∈ Φ.source := (hf x).choose_spec.1
  have hEq : Set.EqOn f (Φ : M → N) Φ.source := (hf x).choose_spec.2
  let U : Opens M := ⟨Φ.source, Φ.open_source⟩
  have hU : (U : Set M) ⊆ Φ.source := Set.Subset.rfl
  let V : Opens N :=
    ⟨(Φ : M → N) '' (U : Set M), image_opens_isOpen Φ hU⟩
  let Ψ : Diffeomorph I J U V ∞ :=
    DifferentialGeometry.PartialDiffeomorph.toOpensDiffeoCross Φ hU
  let xu : U := ⟨x, hxΦ⟩
  letI : SigmaCompactSpace U :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  letI : SigmaCompactSpace V :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen J V.isOpen)
  have hEqNhds : f =ᶠ[𝓝 x] (Φ : M → N) :=
    Filter.eventuallyEq_of_mem (Φ.open_source.mem_nhds hxΦ) hEq
  have hdf : mfderiv I J f x = mfderiv I J (Φ : M → N) x :=
    hEqNhds.mfderiv_eq
  have hΨd (y : U) (v : TangentSpace I y) :
      mfderiv I J (Ψ : U → V) y v =
        mfderiv I J (Φ : M → N) (y : M) v := by
    simpa only [Ψ] using
      DifferentialGeometry.PartialDiffeomorph.mfderiv_toOpensDiffeoCross Φ hU y v
  have hΨval (y : U) : ((Ψ y : V) : N) = (Φ : M → N) (y : M) := by
    rfl
  have hmetric :
      (localPullMetric (I := I) (J := J) g f hf).restrictOpen (I := I) U =
        Diffeomorph.pullbackMetricCross (I := I) (J := J)
          (g.restrictOpen (I := J) V) Ψ := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    have hyΦ : (y : M) ∈ Φ.source := hU y.2
    have hEqYNhds : f =ᶠ[𝓝 (y : M)] (Φ : M → N) :=
      Filter.eventuallyEq_of_mem (Φ.open_source.mem_nhds hyΦ) hEq
    have hdfY : mfderiv I J f (y : M) =
        mfderiv I J (Φ : M → N) (y : M) :=
      hEqYNhds.mfderiv_eq
    rw [SmoothRiemannianMetric.restrictOpen_inner,
      localPullMetric_inner,
      Diffeomorph.pullbackMetricCross_inner,
      SmoothRiemannianMetric.restrictOpen_inner,
      hΨval, hΨd, hΨd,
      hEq hyΦ, hdfY]
  calc
    metricRm04StdAt (I := I) (M := M)
        (localPullMetric (I := I) (J := J) g f hf) x X Y Z W =
        metricRm04StdAt (I := I) (M := U)
          ((localPullMetric (I := I) (J := J) g f hf).restrictOpen (I := I) U)
          xu X Y Z W := by
            exact (metricRm04StdAt_restrictOpen
              (I := I) (localPullMetric (I := I) (J := J) g f hf)
              U xu X Y Z W).symm
    _ = metricRm04StdAt (I := I) (M := U)
          (Diffeomorph.pullbackMetricCross (I := I) (J := J)
            (g.restrictOpen (I := J) V) Ψ)
          xu X Y Z W := by rw [hmetric]
    _ = metricRm04StdAt (I := J) (M := V)
          (g.restrictOpen (I := J) V) (Ψ xu)
          (mfderiv I J (Ψ : U → V) xu X)
          (mfderiv I J (Ψ : U → V) xu Y)
          (mfderiv I J (Ψ : U → V) xu Z)
          (mfderiv I J (Ψ : U → V) xu W) :=
      metricRm04Std_pullbackCross
        (I := I) (J := J) (g.restrictOpen (I := J) V) Ψ xu X Y Z W
    _ = metricRm04StdAt (I := J) (M := N) g ((Ψ xu : V) : N)
          (mfderiv I J (Ψ : U → V) xu X)
          (mfderiv I J (Ψ : U → V) xu Y)
          (mfderiv I J (Ψ : U → V) xu Z)
          (mfderiv I J (Ψ : U → V) xu W) :=
      metricRm04StdAt_restrictOpen
        (I := J) g V (Ψ xu)
          (mfderiv I J (Ψ : U → V) xu X)
          (mfderiv I J (Ψ : U → V) xu Y)
          (mfderiv I J (Ψ : U → V) xu Z)
          (mfderiv I J (Ψ : U → V) xu W)
    _ = metricRm04StdAt (I := J) (M := N) g (f x)
          (mfderiv I J f x X) (mfderiv I J f x Y)
          (mfderiv I J f x Z) (mfderiv I J f x W) := by
      rw [hΨval, hΨd, hΨd, hΨd, hΨd, ← hdf]
      change metricRm04StdAt (I := J) (M := N) g ((Φ : M → N) x)
          (mfderiv I J f x X) (mfderiv I J f x Y)
          (mfderiv I J f x Z) (mfderiv I J f x W) = _
      rw [← hEq hxΦ]

end DifferentialGeometry.Integral.Connection
