import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Tensor.FirstNull.Compactness
import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Tensor.FirstNull.Signs
open DifferentialGeometry.Tensor.RicciIdentity
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow

noncomputable section

open Bundle DifferentialGeometry.Tensor0SBundle Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]

structure TensorWeakMaximumPrincipleCore
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (X : TimeDependentVectorField (I := I) (M := M))
    (N : TwoTensorReaction (I := I) (M := M))
    (T : Real) : Prop where
  symmetric : TwoTensorFamilySymmetricOn (I := I) (M := M) S (Set.Icc 0 T)
  bilinear :
    ∀ t, t ∈ Set.Icc 0 T -> ∀ x,
      TwoTensorBilinearAt (I := I) (M := M) (S t) x
  barrierRegularity :
    TensorBarrierRegularityOn (I := I) (M := M) G S X N T
  firstNullCompactness :
    ∀ epsilon delta t0 : Real,
      0 < epsilon ->
      0 < delta ->
      Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
      TensorFirstNullCompactnessOn (I := I) (M := M) G S epsilon delta t0

structure TensorWeakMaximumPrincipleRegularityOn
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (X : TimeDependentVectorField (I := I) (M := M))
    (N : TwoTensorReaction (I := I) (M := M))
    (T : Real) : Prop where
  symmetric : TwoTensorFamilySymmetricOn (I := I) (M := M) S (Set.Icc 0 T)
  bilinear :
    ∀ t, t ∈ Set.Icc 0 T -> ∀ x,
      TwoTensorBilinearAt (I := I) (M := M) (S t) x
  barrierRegularity :
    TensorBarrierRegularityOn (I := I) (M := M) G S X N T
  firstNullCompactness :
    ∀ epsilon delta t0 : Real,
      0 < epsilon ->
      0 < delta ->
      Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
      TensorFirstNullCompactnessOn (I := I) (M := M) G S epsilon delta t0
  firstNullScalarSigns :
    ∀ epsilon delta t0 : Real,
      0 < epsilon ->
      0 < delta ->
      Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
      ∀ (nabla2Barrier : TensorNabla2Family (I := I) (M := M))
        (nablaBarrier : TensorNabla1Family (I := I) (M := M)),
      (hstrict : TensorBarrierStrictSupersolutionOn (I := I) (M := M)
        G S X N nabla2Barrier nablaBarrier epsilon delta t0) ->
      (hnull : TensorNullEigenvectorCondition (I := I) (M := M)
        G N (Set.Icc t0 (t0 + delta))) ->
      (d : TensorFirstNullData (I := I) (M := M) G S epsilon delta t0) ->
      TensorFirstNullScalarSigns (I := I) (M := M) G S X N
        nabla2Barrier nablaBarrier epsilon delta t0 d

namespace TensorWeakMaximumPrincipleRegularityOn

omit [IsManifold I 2 M] in
theorem toCore
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {T : Real}
    (h : TensorWeakMaximumPrincipleRegularityOn (I := I) (M := M) G S X N T) :
    TensorWeakMaximumPrincipleCore (I := I) (M := M) G S X N T where
  symmetric := h.symmetric
  bilinear := h.bilinear
  barrierRegularity := h.barrierRegularity
  firstNullCompactness := h.firstNullCompactness

end TensorWeakMaximumPrincipleRegularityOn

structure TensorWeakMaximumPrincipleSectionCore
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorSecFamily (I := I) (M := M))
    (X : TimeDependentVectorField (I := I) (M := M))
    (N : TwoTensorReaction (I := I) (M := M))
    (T : Real) : Prop where
  symmetric :
    TwoTensorFamilySymmetricOn (I := I) (M := M)
      (twoTensorSecToFamily (I := I) (M := M) S) (Set.Icc 0 T)
  barrierRegularity :
    TensorBarrierRegularityOn (I := I) (M := M) G
      (twoTensorSecToFamily (I := I) (M := M) S) X N T
  unitSlabCompact :
    ∀ delta t0 : Real,
      0 < delta ->
      Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
      IsCompact
        (Set.univ :
          Set (MetricUnitTangentTimeSlab (I := I) (M := M) G
            (Set.Icc t0 (t0 + delta))))
  metricQuadCont :
    ∀ delta t0 : Real,
      0 < delta ->
      Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
      Continuous
        (metricBundleQuad (I := I) (M := M) G
          (Set.Icc t0 (t0 + delta)))
  tensorQuadCont :
    ∀ delta t0 : Real,
      0 < delta ->
      Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
      Continuous
        (tensorSecBundleQuad (I := I) (M := M) S
          (Set.Icc t0 (t0 + delta)))
  barrierFixedContinuous :
    ∀ epsilon delta t0 : Real,
      0 < epsilon ->
      0 < delta ->
      Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
      ∀ x (v : TangentSpace I x),
        ContinuousOn
          (fun t : Real =>
            tensorBarrierFamily (I := I) (M := M) G
              (twoTensorSecToFamily (I := I) (M := M) S)
              epsilon delta t0 t x v v)
          (Set.Icc t0 (t0 + delta))

structure TensorWeakMaximumPrincipleSectionRegularity
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorSecFamily (I := I) (M := M))
    (X : TimeDependentVectorField (I := I) (M := M))
    (N : TwoTensorReaction (I := I) (M := M))
    (T : Real) : Prop where
  symmetric :
    TwoTensorFamilySymmetricOn (I := I) (M := M)
      (twoTensorSecToFamily (I := I) (M := M) S) (Set.Icc 0 T)
  barrierRegularity :
    TensorBarrierRegularityOn (I := I) (M := M) G
      (twoTensorSecToFamily (I := I) (M := M) S) X N T
  unitSlabCompact :
    ∀ delta t0 : Real,
      0 < delta ->
      Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
      IsCompact
        (Set.univ :
          Set (MetricUnitTangentTimeSlab (I := I) (M := M) G
            (Set.Icc t0 (t0 + delta))))
  metricQuadCont :
    ∀ delta t0 : Real,
      0 < delta ->
      Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
      Continuous
        (metricBundleQuad (I := I) (M := M) G
          (Set.Icc t0 (t0 + delta)))
  tensorQuadCont :
    ∀ delta t0 : Real,
      0 < delta ->
      Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
      Continuous
        (tensorSecBundleQuad (I := I) (M := M) S
          (Set.Icc t0 (t0 + delta)))
  barrierFixedContinuous :
    ∀ epsilon delta t0 : Real,
      0 < epsilon ->
      0 < delta ->
      Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
      ∀ x (v : TangentSpace I x),
        ContinuousOn
          (fun t : Real =>
            tensorBarrierFamily (I := I) (M := M) G
              (twoTensorSecToFamily (I := I) (M := M) S)
              epsilon delta t0 t x v v)
          (Set.Icc t0 (t0 + delta))
  firstNullScalarSigns :
    ∀ epsilon delta t0 : Real,
      0 < epsilon ->
      0 < delta ->
      Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
      ∀ (nabla2Barrier : TensorNabla2Family (I := I) (M := M))
        (nablaBarrier : TensorNabla1Family (I := I) (M := M)),
      (hstrict : TensorBarrierStrictSupersolutionOn (I := I) (M := M)
        G (twoTensorSecToFamily (I := I) (M := M) S) X N
        nabla2Barrier nablaBarrier epsilon delta t0) ->
      (hnull : TensorNullEigenvectorCondition (I := I) (M := M)
        G N (Set.Icc t0 (t0 + delta))) ->
      (d : TensorFirstNullData (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S) epsilon delta t0) ->
      TensorFirstNullScalarSigns (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S) X N
        nabla2Barrier nablaBarrier epsilon delta t0 d

namespace TensorWeakMaximumPrincipleSectionCore

omit [IsManifold I 2 M] in
theorem ofCompact
    [CompactSpace M] [T2Space M]
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorSecFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {T : Real}
    (hsym :
      TwoTensorFamilySymmetricOn (I := I) (M := M)
        (twoTensorSecToFamily (I := I) (M := M) S) (Set.Icc 0 T))
    (hbar :
      TensorBarrierRegularityOn (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S) X N T)
    (hMetric :
      ∀ delta t0 : Real,
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        Continuous
          (metricBundleQuad (I := I) (M := M) G
            (Set.Icc t0 (t0 + delta))))
    (hTensor :
      ∀ delta t0 : Real,
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        Continuous
          (tensorSecBundleQuad (I := I) (M := M) S
            (Set.Icc t0 (t0 + delta))))
    (hFixed :
      ∀ epsilon delta t0 : Real,
        0 < epsilon ->
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        ∀ x (v : TangentSpace I x),
          ContinuousOn
            (fun t : Real =>
              tensorBarrierFamily (I := I) (M := M) G
                (twoTensorSecToFamily (I := I) (M := M) S)
                epsilon delta t0 t x v v)
            (Set.Icc t0 (t0 + delta))) :
    TensorWeakMaximumPrincipleSectionCore (I := I) (M := M) G S X N T where
  symmetric := hsym
  barrierRegularity := hbar
  unitSlabCompact := by
    intro delta t0 hdelta hsub
    exact metricUnitTimeSlab_icc_compact_of_bundle (I := I) (M := M)
      G t0 (t0 + delta) (G t0)
      (by
        change Continuous (metricBundleQuad (I := I) (M := M) G
          (Set.Icc t0 (t0 + delta)))
        exact hMetric delta t0 hdelta hsub)
  metricQuadCont := hMetric
  tensorQuadCont := hTensor
  barrierFixedContinuous := hFixed

omit [IsManifold I 2 M] in
theorem ofTotal
    [CompactSpace M] [T2Space M]
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorSecFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {T : Real}
    (hsym :
      TwoTensorFamilySymmetricOn (I := I) (M := M)
        (twoTensorSecToFamily (I := I) (M := M) S) (Set.Icc 0 T))
    (hbar :
      TensorBarrierRegularityOn (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S) X N T)
    (hMetric :
      ∀ delta t0 : Real,
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        Continuous
          (fun q : {t : Real // t ∈ Set.Icc t0 (t0 + delta)} × TangentBundle I M =>
            TotalSpace.mk' (Tensor0SModel 2 Real E)
              (E := fun x : M => Tensor0SSpace 2 I x) q.2.proj
              (metricTensorField (I := I) (G q.1.1) q.2.proj)))
    (hTensor :
      ∀ delta t0 : Real,
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        Continuous
          (fun q : {t : Real // t ∈ Set.Icc t0 (t0 + delta)} × TangentBundle I M =>
            TotalSpace.mk' (Tensor0SModel 2 Real E)
              (E := fun x : M => Tensor0SSpace 2 I x) q.2.proj
              (S q.1.1 q.2.proj)))
    (hFixed :
      ∀ epsilon delta t0 : Real,
        0 < epsilon ->
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        ∀ x (v : TangentSpace I x),
          ContinuousOn
            (fun t : Real =>
              tensorBarrierFamily (I := I) (M := M) G
                (twoTensorSecToFamily (I := I) (M := M) S)
                epsilon delta t0 t x v v)
            (Set.Icc t0 (t0 + delta))) :
    TensorWeakMaximumPrincipleSectionCore (I := I) (M := M) G S X N T :=
  ofCompact (I := I) (M := M)
    (G := G) (S := S) (X := X) (N := N) (T := T)
    hsym hbar
    (fun delta t0 hdelta hsub =>
      DifferentialGeometry.PDE.RicciFlow.metricFamQuadCont (I := I) (M := M)
        G (Set.Icc t0 (t0 + delta))
        (hMetric delta t0 hdelta hsub))
    (fun delta t0 hdelta hsub =>
      DifferentialGeometry.PDE.RicciFlow.tensorQuadCont (I := I) (M := M)
        S (Set.Icc t0 (t0 + delta))
        (hTensor delta t0 hdelta hsub))
    hFixed

omit [IsManifold I 2 M] in
theorem ofSmoothMetric
    [CompactSpace M] [T2Space M]
    {D : RealTimeInterval}
    (G : MetricConnectionFamilyOn (I := I) (M := M) D)
    {S : TwoTensorSecFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {T : Real}
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (hsym :
      TwoTensorFamilySymmetricOn (I := I) (M := M)
        (twoTensorSecToFamily (I := I) (M := M) S) (Set.Icc 0 T))
    (hbar :
      TensorBarrierRegularityOn (I := I) (M := M) (fun t => G.metric t)
        (twoTensorSecToFamily (I := I) (M := M) S) X N T)
    (hTensor :
      ∀ delta t0 : Real,
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        Continuous
          (fun q : {t : Real // t ∈ Set.Icc t0 (t0 + delta)} × TangentBundle I M =>
            TotalSpace.mk' (Tensor0SModel 2 Real E)
              (E := fun x : M => Tensor0SSpace 2 I x) q.2.proj
              (S q.1.1 q.2.proj)))
    (hFixed :
      ∀ epsilon delta t0 : Real,
        0 < epsilon ->
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        ∀ x (v : TangentSpace I x),
          ContinuousOn
            (fun t : Real =>
              tensorBarrierFamily (I := I) (M := M) (fun t => G.metric t)
                (twoTensorSecToFamily (I := I) (M := M) S)
                epsilon delta t0 t x v v)
            (Set.Icc t0 (t0 + delta))) :
    TensorWeakMaximumPrincipleSectionCore (I := I) (M := M) (fun t => G.metric t) S X N T :=
  ofTotal (I := I) (M := M)
    (G := fun t => G.metric t) (S := S) (X := X) (N := N) (T := T)
    hsym hbar
    (fun _delta _t0 _hdelta hsub =>
      metricTensor_tangentBundle_cont_of_metricFamilySmoothOn
        (I := I) (M := M) G.metric hG
        (fun _t ht => hTsub (hsub ht)))
    hTensor hFixed

omit [IsManifold I 2 M] in
theorem toRaw
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorSecFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {T : Real}
    (h : TensorWeakMaximumPrincipleSectionCore (I := I) (M := M) G S X N T) :
    TensorWeakMaximumPrincipleCore (I := I) (M := M) G
      (twoTensorSecToFamily (I := I) (M := M) S) X N T where
  symmetric := h.symmetric
  bilinear := fun t _ht x => twoTensorSecToFamily_bilin (I := I) (M := M) S t x
  barrierRegularity := h.barrierRegularity
  firstNullCompactness := by
    intro epsilon delta t0 hepsilon hdelta hsub
    exact TensorFirstNullCompactnessOn.of_section_timeSlab (I := I) (M := M)
      G S epsilon delta t0
      (h.unitSlabCompact delta t0 hdelta hsub)
      (barrierTimeCont (I := I) (M := M) G S epsilon delta t0
        (Set.Icc t0 (t0 + delta))
        (h.tensorQuadCont delta t0 hdelta hsub)
        (h.metricQuadCont delta t0 hdelta hsub))
      (h.barrierFixedContinuous epsilon delta t0 hepsilon hdelta hsub)

end TensorWeakMaximumPrincipleSectionCore

namespace TensorWeakMaximumPrincipleSectionRegularity

omit [IsManifold I 2 M] in
theorem toCore
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorSecFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {T : Real}
    (h : TensorWeakMaximumPrincipleSectionRegularity (I := I) (M := M) G S X N T) :
    TensorWeakMaximumPrincipleSectionCore (I := I) (M := M) G S X N T where
  symmetric := h.symmetric
  barrierRegularity := h.barrierRegularity
  unitSlabCompact := h.unitSlabCompact
  metricQuadCont := h.metricQuadCont
  tensorQuadCont := h.tensorQuadCont
  barrierFixedContinuous := h.barrierFixedContinuous

omit [IsManifold I 2 M] in
theorem ofCompact
    [CompactSpace M] [T2Space M]
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorSecFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {T : Real}
    (hsym :
      TwoTensorFamilySymmetricOn (I := I) (M := M)
        (twoTensorSecToFamily (I := I) (M := M) S) (Set.Icc 0 T))
    (hbar :
      TensorBarrierRegularityOn (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S) X N T)
    (hMetric :
      ∀ delta t0 : Real,
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        Continuous
          (metricBundleQuad (I := I) (M := M) G
            (Set.Icc t0 (t0 + delta))))
    (hTensor :
      ∀ delta t0 : Real,
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        Continuous
          (tensorSecBundleQuad (I := I) (M := M) S
            (Set.Icc t0 (t0 + delta))))
    (hFixed :
      ∀ epsilon delta t0 : Real,
        0 < epsilon ->
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        ∀ x (v : TangentSpace I x),
          ContinuousOn
            (fun t : Real =>
              tensorBarrierFamily (I := I) (M := M) G
                (twoTensorSecToFamily (I := I) (M := M) S)
                epsilon delta t0 t x v v)
            (Set.Icc t0 (t0 + delta)))
    (hSigns :
      ∀ epsilon delta t0 : Real,
        0 < epsilon ->
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        ∀ (nabla2Barrier : TensorNabla2Family (I := I) (M := M))
          (nablaBarrier : TensorNabla1Family (I := I) (M := M)),
        (hstrict : TensorBarrierStrictSupersolutionOn (I := I) (M := M)
          G (twoTensorSecToFamily (I := I) (M := M) S) X N
          nabla2Barrier nablaBarrier epsilon delta t0) ->
        (hnull : TensorNullEigenvectorCondition (I := I) (M := M)
          G N (Set.Icc t0 (t0 + delta))) ->
        (d : TensorFirstNullData (I := I) (M := M) G
          (twoTensorSecToFamily (I := I) (M := M) S) epsilon delta t0) ->
        TensorFirstNullScalarSigns (I := I) (M := M) G
          (twoTensorSecToFamily (I := I) (M := M) S) X N
          nabla2Barrier nablaBarrier epsilon delta t0 d) :
    TensorWeakMaximumPrincipleSectionRegularity (I := I) (M := M) G S X N T where
  symmetric := hsym
  barrierRegularity := hbar
  unitSlabCompact := by
    intro delta t0 hdelta hsub
    exact metricUnitTimeSlab_icc_compact_of_bundle (I := I) (M := M)
      G t0 (t0 + delta) (G t0)
      (by
        change Continuous (metricBundleQuad (I := I) (M := M) G
          (Set.Icc t0 (t0 + delta)))
        exact hMetric delta t0 hdelta hsub)
  metricQuadCont := hMetric
  tensorQuadCont := hTensor
  barrierFixedContinuous := hFixed
  firstNullScalarSigns := hSigns

omit [IsManifold I 2 M] in
theorem ofTotal
    [CompactSpace M] [T2Space M]
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorSecFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {T : Real}
    (hsym :
      TwoTensorFamilySymmetricOn (I := I) (M := M)
        (twoTensorSecToFamily (I := I) (M := M) S) (Set.Icc 0 T))
    (hbar :
      TensorBarrierRegularityOn (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S) X N T)
    (hMetric :
      ∀ delta t0 : Real,
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        Continuous
          (fun q : {t : Real // t ∈ Set.Icc t0 (t0 + delta)} × TangentBundle I M =>
            TotalSpace.mk' (Tensor0SModel 2 Real E)
              (E := fun x : M => Tensor0SSpace 2 I x) q.2.proj
              (metricTensorField (I := I) (G q.1.1) q.2.proj)))
    (hTensor :
      ∀ delta t0 : Real,
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        Continuous
          (fun q : {t : Real // t ∈ Set.Icc t0 (t0 + delta)} × TangentBundle I M =>
            TotalSpace.mk' (Tensor0SModel 2 Real E)
              (E := fun x : M => Tensor0SSpace 2 I x) q.2.proj
              (S q.1.1 q.2.proj)))
    (hFixed :
      ∀ epsilon delta t0 : Real,
        0 < epsilon ->
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        ∀ x (v : TangentSpace I x),
          ContinuousOn
            (fun t : Real =>
              tensorBarrierFamily (I := I) (M := M) G
                (twoTensorSecToFamily (I := I) (M := M) S)
                epsilon delta t0 t x v v)
            (Set.Icc t0 (t0 + delta)))
    (hSigns :
      ∀ epsilon delta t0 : Real,
        0 < epsilon ->
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        ∀ (nabla2Barrier : TensorNabla2Family (I := I) (M := M))
          (nablaBarrier : TensorNabla1Family (I := I) (M := M)),
        (hstrict : TensorBarrierStrictSupersolutionOn (I := I) (M := M)
          G (twoTensorSecToFamily (I := I) (M := M) S) X N
          nabla2Barrier nablaBarrier epsilon delta t0) ->
        (hnull : TensorNullEigenvectorCondition (I := I) (M := M)
          G N (Set.Icc t0 (t0 + delta))) ->
        (d : TensorFirstNullData (I := I) (M := M) G
          (twoTensorSecToFamily (I := I) (M := M) S) epsilon delta t0) ->
        TensorFirstNullScalarSigns (I := I) (M := M) G
          (twoTensorSecToFamily (I := I) (M := M) S) X N
          nabla2Barrier nablaBarrier epsilon delta t0 d) :
    TensorWeakMaximumPrincipleSectionRegularity (I := I) (M := M) G S X N T :=
  ofCompact (I := I) (M := M)
    (G := G) (S := S) (X := X) (N := N) (T := T)
    hsym hbar
    (fun delta t0 hdelta hsub =>
      DifferentialGeometry.PDE.RicciFlow.metricFamQuadCont (I := I) (M := M)
        G (Set.Icc t0 (t0 + delta))
        (hMetric delta t0 hdelta hsub))
    (fun delta t0 hdelta hsub =>
      DifferentialGeometry.PDE.RicciFlow.tensorQuadCont (I := I) (M := M)
        S (Set.Icc t0 (t0 + delta))
        (hTensor delta t0 hdelta hsub))
    hFixed hSigns

omit [IsManifold I 2 M] in
theorem ofSmoothMetric
    [CompactSpace M] [T2Space M]
    {D : RealTimeInterval}
    (G : MetricConnectionFamilyOn (I := I) (M := M) D)
    {S : TwoTensorSecFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {T : Real}
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (hsym :
      TwoTensorFamilySymmetricOn (I := I) (M := M)
        (twoTensorSecToFamily (I := I) (M := M) S) (Set.Icc 0 T))
    (hbar :
      TensorBarrierRegularityOn (I := I) (M := M) (fun t => G.metric t)
        (twoTensorSecToFamily (I := I) (M := M) S) X N T)
    (hTensor :
      ∀ delta t0 : Real,
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        Continuous
          (fun q : {t : Real // t ∈ Set.Icc t0 (t0 + delta)} × TangentBundle I M =>
            TotalSpace.mk' (Tensor0SModel 2 Real E)
              (E := fun x : M => Tensor0SSpace 2 I x) q.2.proj
              (S q.1.1 q.2.proj)))
    (hFixed :
      ∀ epsilon delta t0 : Real,
        0 < epsilon ->
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        ∀ x (v : TangentSpace I x),
          ContinuousOn
            (fun t : Real =>
              tensorBarrierFamily (I := I) (M := M) (fun t => G.metric t)
                (twoTensorSecToFamily (I := I) (M := M) S)
                epsilon delta t0 t x v v)
            (Set.Icc t0 (t0 + delta)))
    (hSigns :
      ∀ epsilon delta t0 : Real,
        0 < epsilon ->
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        ∀ (nabla2Barrier : TensorNabla2Family (I := I) (M := M))
          (nablaBarrier : TensorNabla1Family (I := I) (M := M)),
        (hstrict : TensorBarrierStrictSupersolutionOn (I := I) (M := M)
          (fun t => G.metric t) (twoTensorSecToFamily (I := I) (M := M) S) X N
          nabla2Barrier nablaBarrier epsilon delta t0) ->
        (hnull : TensorNullEigenvectorCondition (I := I) (M := M)
          (fun t => G.metric t) N (Set.Icc t0 (t0 + delta))) ->
        (d : TensorFirstNullData (I := I) (M := M) (fun t => G.metric t)
          (twoTensorSecToFamily (I := I) (M := M) S) epsilon delta t0) ->
        TensorFirstNullScalarSigns (I := I) (M := M) (fun t => G.metric t)
          (twoTensorSecToFamily (I := I) (M := M) S) X N
          nabla2Barrier nablaBarrier epsilon delta t0 d) :
    TensorWeakMaximumPrincipleSectionRegularity (I := I) (M := M) (fun t => G.metric t) S X N T :=
  ofTotal (I := I) (M := M)
    (G := fun t => G.metric t) (S := S) (X := X) (N := N) (T := T)
    hsym hbar
    (fun _delta _t0 _hdelta hsub =>
      metricTensor_tangentBundle_cont_of_metricFamilySmoothOn
        (I := I) (M := M) G.metric hG
        (fun _t ht => hTsub (hsub ht)))
    hTensor hFixed hSigns

omit [IsManifold I 2 M] in
theorem toRaw
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorSecFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {T : Real}
    (h : TensorWeakMaximumPrincipleSectionRegularity (I := I) (M := M) G S X N T) :
    TensorWeakMaximumPrincipleRegularityOn (I := I) (M := M) G
      (twoTensorSecToFamily (I := I) (M := M) S) X N T where
  symmetric := h.symmetric
  bilinear := fun t _ht x => twoTensorSecToFamily_bilin (I := I) (M := M) S t x
  barrierRegularity := h.barrierRegularity
  firstNullCompactness := by
    intro epsilon delta t0 hepsilon hdelta hsub
    exact TensorFirstNullCompactnessOn.of_section_timeSlab (I := I) (M := M)
      G S epsilon delta t0
      (h.unitSlabCompact delta t0 hdelta hsub)
      (barrierTimeCont (I := I) (M := M) G S epsilon delta t0
        (Set.Icc t0 (t0 + delta))
        (h.tensorQuadCont delta t0 hdelta hsub)
        (h.metricQuadCont delta t0 hdelta hsub))
      (h.barrierFixedContinuous epsilon delta t0 hepsilon hdelta hsub)
  firstNullScalarSigns := h.firstNullScalarSigns

end TensorWeakMaximumPrincipleSectionRegularity

end

end DifferentialGeometry.PDE.RicciFlow
