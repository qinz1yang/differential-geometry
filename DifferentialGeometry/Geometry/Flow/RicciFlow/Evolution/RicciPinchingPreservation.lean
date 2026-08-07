import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.RicciPreservation
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow


open Bundle
open DifferentialGeometry.Tensor0SBundle
open scoped BigOperators Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem pinchParabolic_of_react
    [I.Boundaryless]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    {T delta : Real}
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (hTreg : Set.Ioc 0 T ⊆ D.regular)
    (hreact :
      ∀ t, t ∈ Set.Ioc 0 T -> ∀ x, ∀ v : TangentSpace I x,
        (shiftNRaw (I := I) (M := M) delta t (S.base.metric t)
          (twoTensorSecToFamily (I := I) (M := M)
            (pinchSec (I := I) S delta) t)) x v v =
          pinchCoordReact (I := I) S delta t x v) :
    TensorParabolicSupersolutionWithDriftOn (I := I) (M := M)
      (fun t : Real => S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M) (pinchSec (I := I) S delta))
      (fun _t x => (0 : TangentSpace I x))
      (shiftNRaw (I := I) (M := M) delta)
      (fun t x => pinchNab2ModelSec (I := I) S delta t x)
      (fun t x => pinchNablaModel (I := I) S delta t x) T := by
  refine ⟨?_⟩
  refine ⟨fun t x v => pinchCoordTime (I := I) S delta t x v, ?_, ?_⟩
  · intro t ht x v
    have htreg : t ∈ D.regular := hTreg ht
    have hderiv :=
      pinchQuadDeriv_coord (I := I) (M := M) S hS
        (delta := delta) ⟨t, htreg⟩ x v
    simpa [pinchCoordTime, ricciCoordQuadRHS] using hderiv.mono hTsub
  · intro t ht x v
    have hheat := pinchHeat_coord (I := I) S delta t x v
    have hN := hreact t ht x v
    apply le_of_eq
    calc
      tensorHeatWithDrift2QuadMetricAt (I := I) (S.base.metric t)
            (fun x => (0 : TangentSpace I x))
            (pinchNab2ModelSec (I := I) S delta t x)
            (pinchNablaModel (I := I) S delta t x) v +
          (shiftNRaw (I := I) (M := M) delta t (S.base.metric t)
            (twoTensorSecToFamily (I := I) (M := M)
              (pinchSec (I := I) S delta) t)) x v v
          =
        (ricciCoordRough (I := I) S t x v -
            delta *
              (DifferentialGeometry.Geometry.Curvature.laplacianAt (I := I) (flowG (I := I) S) t
                  (S.scalar t) x *
                (S.base.metric t).inner x v v)) +
          pinchCoordReact (I := I) S delta t x v := by
            rw [hheat, hN]
            rfl
      _ = pinchCoordTime (I := I) S delta t x v := by
            simp [pinchCoordTime, pinchCoordReact, ricciCoordReact,
              ricciCoordQuadRHS, ricciCoordRough, SolutionOn.family]
            ring






theorem pinchParabolic
    [I.Boundaryless]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    {T delta : Real}
    (hdelta13 : delta < (1 : Real) / 3)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (hTreg : Set.Ioc 0 T ⊆ D.regular) :
    TensorParabolicSupersolutionWithDriftOn (I := I) (M := M)
      (fun t : Real => S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M) (pinchSec (I := I) S delta))
      (fun _t x => (0 : TangentSpace I x))
      (shiftNRaw (I := I) (M := M) delta)
      (fun t x => pinchNab2ModelSec (I := I) S delta t x)
      (fun t x => pinchNablaModel (I := I) S delta t x) T :=
  pinchParabolic_of_react (I := I) (M := M) S hS hTsub hTreg
    (fun _t _ht x v =>
      shiftNRaw_pinchCoordReact (I := I) (M := M) S
        hdelta13 (hdim x) v)



theorem pinchSpatialModel
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (delta : Real) :
    TensorSpatialDerivs (I := I) (M := M)
      (fun t : Real => S.base.connection t) (pinchSec (I := I) S delta)
      (pinchNablaModel (I := I) S delta)
      (pinchNab2ModelSec (I := I) S delta) := by
  constructor
  · intro t
    letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2
    letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 3
    have hRic := (ricciSpatialWMP (I := I) S).first t
    have hRg := scalarMetric1Sec_realizes (I := I) S t
    have hscaled :
        TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) 2 (S.base.connection t)
          (delta • tensor0SField_smulByFun (𝕜 := Real) (E := E) (H := H)
            (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s := 2)
            (fun x : M => S.scalar t x)
            (by
              simpa [SolutionOn.scalar, SolutionFamily.scalar] using
                metricScalar_smooth (I := I) (M := M) (S.base.metric t))
            (metricTensorField (I := I) (S.base.metric t)))
          (delta • scalarMetric1Sec (I := I) S t) :=
      TotalNabla0SRealizes.smul (I := I) (M := M) delta hRg
    have hscaled' :
        TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) 2 (S.base.connection t)
          (tensor0SField_smulByFun (𝕜 := Real) (E := E) (H := H)
            (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s := 2)
            (fun x : M => delta * S.scalar t x)
            (by
              have hR :
                  ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
                    (fun x : M => S.scalar t x) := by
                simpa [SolutionOn.scalar, SolutionFamily.scalar] using
                  metricScalar_smooth (I := I) (M := M) (S.base.metric t)
              simpa only [Pi.mul_apply] using (contMDiff_const.mul hR))
            (metricTensorField (I := I) (S.base.metric t)))
          (delta • scalarMetric1Sec (I := I) S t) := by
      convert hscaled using 1
      apply ContMDiffSection.ext
      intro x
      simp [tensor0SField_smulByFun_apply, smul_smul]
    have hneg := TotalNabla0SRealizes.smul (I := I) (M := M)
      (-1 : Real) hscaled'
    have hadd := TotalNabla0SRealizes.add (I := I) (M := M) hRic hneg
    simpa [pinchSec, pinchNablaModel, sub_eq_add_neg, smul_smul,
      tensor0SField_smulByFun_apply, mul_assoc, mul_left_comm, mul_comm]
      using hadd
  · intro t
    letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 3
    letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 4
    have hRic := (ricciSpatialWMP (I := I) S).second t
    have hRg := scalarMetric2Sec_realizes (I := I) S t
    have hscaled := TotalNabla0SRealizes.smul (I := I) (M := M)
      delta hRg
    have hneg := TotalNabla0SRealizes.smul (I := I) (M := M)
      (-1 : Real) hscaled
    have hadd := TotalNabla0SRealizes.add (I := I) (M := M) hRic hneg
    simpa [pinchNablaModel, pinchNab2ModelSec, sub_eq_add_neg, smul_smul]
      using hadd




theorem pinchSecFamilyContinuousOnSet
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (delta : Real) :
    Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 D.carrier
      (fun t x => (pinchSec (I := I) S delta) t x) := by
  have hcoef :
      Continuous (fun q : {t : Real // t ∈ D.carrier} × M =>
        delta * S.scalar q.1.1 q.2) := by
    have hscalarSub :
        Continuous (fun q : {t : Real // t ∈ D.carrier} × M =>
          S.scalar q.1.1 q.2) := by
      exact ScalarSTContOn.continuous_subtype (I := I) (M := M) (S := S)
        ({ scalar_continuousOn := hS.scalarCont } :
          ScalarSTContOn (I := I) (M := M) S)
    exact continuous_const.mul hscalarSub
  have hmetric :
      Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 D.carrier
        (fun t x => metricTensorField (I := I) (S.base.metric t) x) := by
    simpa [SolutionOn.family] using hS.smoothMetric.metricTensor_cont
  have hscaled :
      Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 D.carrier
        (fun t x =>
          (delta * S.scalar t x) •
            metricTensorField (I := I) (S.base.metric t) x) :=
    Tensor0SFamilyContinuousOnSet.smul (I := I) (M := M)
      (s := 2) (K := D.carrier)
      (f := fun t x => delta * S.scalar t x)
      (A := fun t x => metricTensorField (I := I) (S.base.metric t) x)
      hcoef hmetric
  have hneg :
      Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 D.carrier
        (fun t x =>
          (-1 : Real) •
            ((delta * S.scalar t x) •
              metricTensorField (I := I) (S.base.metric t) x)) :=
    Tensor0SFamilyContinuousOnSet.const_smul (I := I) (M := M)
      (s := 2) (K := D.carrier)
      (A := fun t x =>
        (delta * S.scalar t x) •
          metricTensorField (I := I) (S.base.metric t) x)
      (-1 : Real) hscaled
  have hsum :
      Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 D.carrier
        (fun t x =>
          S.ricci t x +
            (-1 : Real) •
              ((delta * S.scalar t x) •
                metricTensorField (I := I) (S.base.metric t) x)) :=
    Tensor0SFamilyContinuousOnSet.add (I := I) (M := M)
      (s := 2) (K := D.carrier)
      (A := fun t x => S.ricci t x)
      (B := fun t x =>
        (-1 : Real) •
          ((delta * S.scalar t x) •
            metricTensorField (I := I) (S.base.metric t) x))
      hS.ricciCont hneg
  simpa [pinchSec, tensor0SField_smulByFun_apply] using hsum



theorem pinchLipFamilyContinuousOnSet
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) :
    Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 D.carrier
      (fun t x => (pinchLipSec (I := I) S) t x) := by
  have hscalarSub :
      Continuous (fun q : {t : Real // t ∈ D.carrier} × M =>
        S.scalar q.1.1 q.2) := by
    exact ScalarSTContOn.continuous_subtype (I := I) (M := M) (S := S)
      ({ scalar_continuousOn := hS.scalarCont } :
        ScalarSTContOn (I := I) (M := M) S)
  have hmetric :
      Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 D.carrier
        (fun t x => metricTensorField (I := I) (S.base.metric t) x) := by
    simpa [SolutionOn.family] using hS.smoothMetric.metricTensor_cont
  have hscaled :
      Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 D.carrier
        (fun t x =>
          S.scalar t x • metricTensorField (I := I) (S.base.metric t) x) :=
    Tensor0SFamilyContinuousOnSet.smul (I := I) (M := M)
      (s := 2) (K := D.carrier)
      (f := fun t x => S.scalar t x)
      (A := fun t x => metricTensorField (I := I) (S.base.metric t) x)
      hscalarSub hmetric
  have hneg :
      Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 D.carrier
        (fun t x =>
          (-1 : Real) •
            (S.scalar t x • metricTensorField (I := I) (S.base.metric t) x)) :=
    Tensor0SFamilyContinuousOnSet.const_smul (I := I) (M := M)
      (s := 2) (K := D.carrier)
      (A := fun t x =>
        S.scalar t x • metricTensorField (I := I) (S.base.metric t) x)
      (-1 : Real) hscaled
  have hric3 :
      Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 D.carrier
        (fun t x => (3 : Real) • S.ricci t x) :=
    Tensor0SFamilyContinuousOnSet.const_smul (I := I) (M := M)
      (s := 2) (K := D.carrier)
      (A := fun t x => S.ricci t x) (3 : Real) hS.ricciCont
  have hsum :
      Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 D.carrier
        (fun t x =>
          (3 : Real) • S.ricci t x +
            (-1 : Real) •
              (S.scalar t x •
                metricTensorField (I := I) (S.base.metric t) x)) :=
    Tensor0SFamilyContinuousOnSet.add (I := I) (M := M)
      (s := 2) (K := D.carrier)
      (A := fun t x => (3 : Real) • S.ricci t x)
      (B := fun t x =>
        (-1 : Real) •
          (S.scalar t x • metricTensorField (I := I) (S.base.metric t) x))
      hric3 hneg
  simpa [pinchLipSec, tensor0SField_smulByFun_apply] using hsum


theorem pinchLip_tangentBundle_cont
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval} {K : Set Real}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (hK : K ⊆ D.carrier) :
    Continuous (fun q : {t : Real // t ∈ K} × TangentBundle I M =>
      TotalSpace.mk' (Tensor0SModel 2 Real E)
        (E := fun x : M => Tensor0SSpace 2 I x) q.2.proj
        ((pinchLipSec (I := I) S) q.1.1 q.2.proj)) := by
  exact Tensor0SFamilyContinuousOnSet.tangentBundle (I := I) (M := M)
    (Tensor0SFamilyContinuousOnSet.mono (I := I) (M := M)
      (pinchLipFamilyContinuousOnSet (I := I) S hS) hK)



theorem pinchLip_bound_Icc
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {t0 t1 : Real}
    (hK : Set.Icc t0 t1 ⊆ D.carrier) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ t, t ∈ Set.Icc t0 t1 ->
        ∀ x (v : TangentSpace I x),
          |(pinchLipSec (I := I) S t x) (vec2 (I := I) v v)| ≤
            C * (S.base.metric t).inner x v v := by
  let G : Real -> SmoothRiemannianMetric I M := fun t => S.base.metric t
  let A : (t : Real) -> (x : M) -> Tensor0SSpace 2 I x :=
    fun t x => (pinchLipSec (I := I) S) t x
  have hGcont :
      Continuous
        (metricTimeBundleQuad (I := I) (M := M) G (Set.Icc t0 t1)) := by
    simpa [G, SolutionOn.family] using
      metricTimeBundleQuad_cont_of_metricFamilySmoothOn (I := I) (M := M)
        S.family hS.smoothMetric hK
  have hcompact :
      IsCompact
        (Set.univ :
          Set (MetricUnitTangentTimeSlab (I := I) (M := M) G
            (Set.Icc t0 t1))) :=
    metricUnitTimeSlab_icc_compact_of_bundle (I := I) (M := M)
      G t0 t1 (S.base.metric t0) hGcont
  have hcont :
      Continuous
        (fun p : MetricUnitTangentTimeSlab (I := I) (M := M) G
            (Set.Icc t0 t1) =>
          |quad02 (I := I) (M := M)
            (A (MetricUnitTangentTimeSlab.time (I := I) (M := M) p)
              (MetricUnitTangentTimeSlab.base (I := I) (M := M) p))
            (MetricUnitTangentTimeSlab.vec (I := I) (M := M) p)|) := by
    exact timeSlabAbsQuadCont (I := I) (M := M) G A
      (Set.Icc t0 t1)
      (pinchLip_tangentBundle_cont (I := I) S hS hK)
  obtain ⟨C, hC, hbound⟩ :=
    compactUnitTimeSlab_absBound (I := I) (M := M) G A
      (Set.Icc t0 t1) hcompact hcont
  refine ⟨C, hC, ?_⟩
  intro t ht x v
  simpa [G, A, quad02, vec2_self_eq_const] using hbound t ht x v



theorem pinchSec_tangentBundle_cont
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval} {K : Set Real}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (delta : Real)
    (hK : K ⊆ D.carrier) :
    Continuous (fun q : {t : Real // t ∈ K} × TangentBundle I M =>
      TotalSpace.mk' (Tensor0SModel 2 Real E)
        (E := fun x : M => Tensor0SSpace 2 I x) q.2.proj
        ((pinchSec (I := I) S delta) q.1.1 q.2.proj)) := by
  exact Tensor0SFamilyContinuousOnSet.tangentBundle (I := I) (M := M)
    (Tensor0SFamilyContinuousOnSet.mono (I := I) (M := M)
      (pinchSecFamilyContinuousOnSet (I := I) S hS delta) hK)



theorem pinchSec_tensorQuadCont
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval} {K : Set Real}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (delta : Real)
    (hK : K ⊆ D.carrier) :
    Continuous
      (tensorSecBundleQuad (I := I) (M := M)
        (pinchSec (I := I) S delta) K) :=
  tensorQuadCont (I := I) (M := M) (pinchSec (I := I) S delta) K
    (pinchSec_tangentBundle_cont (I := I) S hS delta hK)



theorem tensorEval_contOn
    {K : Set Real}
    {A : (t : Real) -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x}
    (hA : Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 K A)
    (x : M) (v w : TangentSpace I x) :
    ContinuousOn (fun t : Real => A t x (vec2 (I := I) v w)) K := by
  rw [continuousOn_iff_continuous_restrict]
  let P := {t : Real // t ∈ K}
  let b : P -> M := fun _ => x
  let T : (p : P) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 (b p) :=
    fun p => A p.1 x
  let V : Fin 2 -> ∀ p : P, TangentSpace I (b p) :=
    fun i _ => vec2 (I := I) v w i
  have hb : Continuous b := by
    exact continuous_const
  have hT : Continuous (fun p : P =>
      TotalSpace.mk' (Tensor0SModel 2 Real E)
        (E := fun x : M => Tensor0SSpace 2 I x) (b p) (T p)) := by
    have hincl : Continuous (fun p : P => (p, x)) :=
      continuous_id.prodMk continuous_const
    simpa [P, b, T] using hA.comp hincl
  have hV : ∀ i : Fin 2, Continuous (fun p : P =>
      TotalSpace.mk' E (E := fun x : M => TangentSpace I x)
        (b p) (V i p)) := by
    intro i
    change Continuous (fun _ : P =>
      (TotalSpace.mk' E (E := fun x : M => TangentSpace I x)
        x (vec2 (I := I) v w i) : TangentBundle I M))
    exact continuous_const
  have hEval := TensorMultilinear.continuous_section_apply_base
    (𝕜 := Real) (I := I) (M := M) (P := P) (n := 2)
    b hb T hT V hV
  simpa [P, b, T, V, Tensor0SSpace.toModel,
    tensor0SSpace_continuousLinearEquiv_apply] using hEval


theorem pinchEval_contOn
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) {T delta : Real}
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (x : M) (v w : TangentSpace I x) :
    ContinuousOn
      (fun t : Real =>
        twoTensorSecToFamily (I := I) (M := M)
          (pinchSec (I := I) S delta) t x v w)
      (Set.Icc 0 T) := by
  have hcont :=
    tensorEval_contOn (I := I) (M := M)
      (Tensor0SFamilyContinuousOnSet.mono (I := I) (M := M)
        (pinchSecFamilyContinuousOnSet (I := I) S hS delta) hTsub)
      x v w
  simpa [twoTensorSecToFamily] using hcont



theorem pinchMetricGain
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) {T : Real}
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (hTreg : Set.Ioc 0 T ⊆ D.regular) :
    ∀ t0 : Real,
      t0 ∈ Set.Icc 0 T ->
      t0 < T ->
      ∃ delta0 : Real,
        0 < delta0 ∧ t0 + delta0 ≤ T ∧
          ∀ delta : Real,
            0 < delta ->
            delta ≤ delta0 ->
            ∀ epsilon : Real,
              SmallBarrierEps epsilon ->
              ∃ metricDeriv : TensorQuadraticFormFamily (I := I) (M := M),
                (∀ t, t ∈ Set.Ioc t0 (t0 + delta) ->
                  ∀ x, ∀ v : TangentSpace I x,
                    HasDerivWithinAt
                      (fun s : Real => (S.base.metric s).inner x v v)
                      (metricDeriv t x v) (Set.Icc t0 (t0 + delta)) t) ∧
                (∀ t, t ∈ Set.Ioc t0 (t0 + delta) ->
                  ∀ x, ∀ v : TangentSpace I x,
                    (epsilon / 2) * (S.base.metric t).inner x v v ≤
                      epsilon * ((S.base.metric t).inner x v v +
                        (delta + t - t0) * metricDeriv t x v)) := by
  let A : (t : Real) -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
    fun t x => (-2 : Real) • S.ricci t x
  have hgain := metricGainControl_of_metricVariationOn (I := I) (M := M)
    (D := D) (G := S.family)
    (Ric := RicciAtFamily.toTensorField (I := I) S.ricciAt)
    (A := A) (T := T)
    (by
      simpa [MetricVariationEquationOn] using hS.equation)
    (by
      intro t0 ht0 ht0T
      let deltaRaw : Real := (T - t0) / 2
      have hdeltaRaw : 0 < deltaRaw := by
        dsimp [deltaRaw]
        linarith
      have hdeltaRawT : t0 + deltaRaw ≤ T := by
        dsimp [deltaRaw]
        linarith
      have hcarrier : Set.Icc t0 (t0 + deltaRaw) ⊆ D.carrier := by
        intro s hs
        exact hTsub ⟨le_trans ht0.1 hs.1, le_trans hs.2 hdeltaRawT⟩
      have hregular : ∀ t, t ∈ Set.Ioc t0 (t0 + deltaRaw) -> t ∈ D.regular := by
        intro t ht
        exact hTreg ⟨lt_of_le_of_lt ht0.1 ht.1, le_trans ht.2 hdeltaRawT⟩
      have hAeval :
          ∀ t, t ∈ Set.Ioc t0 (t0 + deltaRaw) ->
            ∀ x, ∀ v : TangentSpace I x,
              quad02 (I := I) (M := M) (A t x) v =
                (-2 : Real) *
                  RicciAtFamily.toTensorField (I := I) S.ricciAt t x v v := by
        intro t ht x v
        simp [A, quad02, vec2_self_eq_const, RicciAtFamily.toTensorField,
          SolutionOn.ricci, SolutionFamily.ricci, SolutionOn.ricciAt,
          SolutionFamily.ricciAt]
      have hGcont :
          Continuous
            (metricTimeBundleQuad (I := I) (M := M)
              (fun t => S.family.metric t)
              (Set.Icc t0 (t0 + deltaRaw))) := by
        exact metricTimeBundleQuad_cont_of_metricFamilySmoothOn
          (I := I) (M := M) S.family hS.smoothMetric hcarrier
      have hAcont :
          Continuous (fun q :
              {t : Real // t ∈ Set.Icc t0 (t0 + deltaRaw)} ×
                  TangentBundle I M =>
            TotalSpace.mk' (Tensor0SModel 2 Real E)
              (E := fun x : M => Tensor0SSpace 2 I x) q.2.proj
              (A q.1.1 q.2.proj)) := by
        have hAset :
            Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2
              (Set.Icc t0 (t0 + deltaRaw)) A :=
          Tensor0SFamilyContinuousOnSet.const_smul (I := I) (M := M)
            (s := 2) (K := Set.Icc t0 (t0 + deltaRaw))
            (A := fun t x => S.ricci t x) (-2 : Real)
            (Tensor0SFamilyContinuousOnSet.mono (I := I) (M := M)
              hS.ricciCont hcarrier)
        exact Tensor0SFamilyContinuousOnSet.tangentBundle
          (I := I) (M := M) hAset
      exact ⟨deltaRaw, hdeltaRaw, hdeltaRawT, hcarrier, hregular,
        hAeval, hGcont, hAcont⟩)
  simpa [SolutionOn.family] using hgain



theorem pinchSmallLip
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {T delta : Real}
    (hdelta : delta < (1 : Real) / 3)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (hTsub : Set.Icc 0 T ⊆ D.carrier) :
    ∀ delta0 t0 : Real, 0 < delta0 ->
      Set.Icc t0 (t0 + delta0) ⊆ Set.Icc 0 T ->
      ∃ K : Real, 0 ≤ K ∧
        ∀ epsilon d : Real,
          SmallBarrierEps epsilon -> 0 < d -> d ≤ delta0 ->
          ∀ t, t ∈ Set.Icc t0 (t0 + d) -> ∀ x, ∀ v : TangentSpace I x,
            |(shiftNRaw (I := I) (M := M) delta t (S.base.metric t)
                (twoTensorSecToFamily (I := I) (M := M)
                  (pinchSec (I := I) S delta) t)) x v v -
              (shiftNRaw (I := I) (M := M) delta t (S.base.metric t)
                (tensorBarrierFamily (I := I) (M := M)
                  (fun s : Real => S.base.metric s)
                  (twoTensorSecToFamily (I := I) (M := M)
                    (pinchSec (I := I) S delta))
                  epsilon d t0 t)) x v v| ≤
                K *
                  |epsilon * (d + t - t0) * (S.base.metric t).inner x v v| := by
  intro delta0 t0 hdelta0 hsub0
  have hKcarrier : Set.Icc t0 (t0 + delta0) ⊆ D.carrier := by
    intro s hs
    exact hTsub (hsub0 hs)
  obtain ⟨C, hC, hbound⟩ :=
    pinchLip_bound_Icc (I := I) S hS
      (t0 := t0) (t1 := t0 + delta0) hKcarrier
  let alpha : Real := (2 * delta - 1) / (1 - 3 * delta)
  refine ⟨|alpha| * C, mul_nonneg (abs_nonneg alpha) hC, ?_⟩
  intro epsilon d hepsilon hd hdle t ht x v
  let c : Real := epsilon * (d + t - t0)
  let base : Real :=
    (shiftNRaw (I := I) (M := M) delta t (S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M)
        (pinchSec (I := I) S delta) t)) x v v
  let barr : Real :=
    (shiftNRaw (I := I) (M := M) delta t (S.base.metric t)
      (tensorBarrierFamily (I := I) (M := M)
        (fun s : Real => S.base.metric s)
        (twoTensorSecToFamily (I := I) (M := M)
          (pinchSec (I := I) S delta))
        epsilon d t0 t)) x v v
  let lip : Real := (pinchLipSec (I := I) S t x) (vec2 (I := I) v v)
  let gvv : Real := (S.base.metric t).inner x v v
  have ht_delta0 : t ∈ Set.Icc t0 (t0 + delta0) :=
    ⟨ht.1, by linarith [ht.2, hdle]⟩
  have hdiff :
      barr - base =
        (c / (1 - 3 * delta)) * (2 * delta - 1) * lip := by
    simpa [base, barr, lip, c] using
      shiftNRaw_barrier_diff (I := I) (M := M) S
        (delta := delta) (epsilon := epsilon) (d := d)
        (t0 := t0) (t := t) (x := x) hdelta (hdim x) v
  have hbase :
      base - barr =
        -((c / (1 - 3 * delta)) * (2 * delta - 1) * lip) := by
    rw [← hdiff]
    ring
  have hden : 1 - 3 * delta ≠ 0 := by nlinarith
  have hcoef :
      (c / (1 - 3 * delta)) * (2 * delta - 1) = alpha * c := by
    dsimp [alpha]
    field_simp [hden]
  have hmetric_nonneg : 0 ≤ gvv := by
    by_cases hv : v = 0
    · subst v
      simp [gvv]
    · exact le_of_lt ((S.base.metric t).pos x v hv)
  have hLip := hbound t ht_delta0 x v
  have hleft :
      |base - barr| = |alpha| * |c| * |lip| := by
    rw [hbase, hcoef]
    simp [abs_mul, mul_assoc, mul_comm]
  calc
    |base - barr| = |alpha| * |c| * |lip| := hleft
    _ ≤ |alpha| * |c| * (C * gvv) := by
      exact mul_le_mul_of_nonneg_left hLip
        (mul_nonneg (abs_nonneg alpha) (abs_nonneg c))
    _ = (|alpha| * C) * |c * gvv| := by
      simp [c, gvv, abs_mul, abs_of_nonneg hmetric_nonneg]
      ring
    _ = (|alpha| * C) *
          |epsilon * (d + t - t0) * (S.base.metric t).inner x v v| := by
      simp [c, gvv, mul_assoc]



theorem pinchBarrierReg
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) {T delta : Real}
    (hdelta : delta < (1 : Real) / 3)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (hTreg : Set.Ioc 0 T ⊆ D.regular) :
    TensorBarrierRegularityOn (I := I) (M := M)
      (fun t : Real => S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M) (pinchSec (I := I) S delta))
      (fun _t x => (0 : TangentSpace I x))
      (shiftNRaw (I := I) (M := M) delta) T where
  tensor_eval_continuous := by
    intro x v w
    exact pinchEval_contOn (I := I) (M := M) S hS hTsub x v w
  metric_eval_continuous := by
    intro x v w
    simpa [SolutionOn.family] using
      ((hS.smoothMetric.coeff_cont x v w).mono hTsub)
  barrier_eval_continuous := by
    intro epsilon d t0 hsub x v w
    have hScont :
        ContinuousOn
          (fun t : Real =>
            twoTensorSecToFamily (I := I) (M := M)
              (pinchSec (I := I) S delta) t x v w)
          (Set.Icc t0 (t0 + d)) :=
      (pinchEval_contOn (I := I) (M := M) S hS hTsub x v w).mono hsub
    have hGcont :
        ContinuousOn
          (fun t : Real => (S.base.metric t).inner x v w)
          (Set.Icc t0 (t0 + d)) := by
      exact
        (by
          simpa [SolutionOn.family] using
            ((hS.smoothMetric.coeff_cont x v w).mono hTsub) :
          ContinuousOn
            (fun t : Real => (S.base.metric t).inner x v w)
            (Set.Icc 0 T)).mono hsub
    have hcoef :
        ContinuousOn (fun t : Real => epsilon * (d + t - t0))
          (Set.Icc t0 (t0 + d)) := by
      have hlin : Continuous (fun t : Real => d + t - t0) :=
        (continuous_const.add continuous_id).sub continuous_const
      exact (continuous_const.mul hlin).continuousOn
    simpa [tensorBarrierFamily] using hScont.add (hcoef.mul hGcont)
  metricGainControl :=
    pinchMetricGain (I := I) (M := M) S hS hTsub hTreg
  smallBarrierLip :=
    pinchSmallLip (I := I) (M := M) S hS hdelta hdim hTsub








theorem pinchSecCore
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) {T delta : Real}
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    (hbar : TensorBarrierRegularityOn (I := I) (M := M)
      (fun t : Real => S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M) (pinchSec (I := I) S delta))
      X N T) :
    TensorWMPSectionCore (I := I) (M := M)
      (fun t : Real => S.base.metric t) (pinchSec (I := I) S delta) X N T := by
  exact TensorWMPSectionCore.ofSmoothMetric (I := I) (M := M)
    (G := S.family) (S := pinchSec (I := I) S delta)
    (X := X) (N := N) (T := T)
    hTsub hS.smoothMetric
    (pinchSec_symm (I := I) S delta (Set.Icc 0 T))
    (by simpa [SolutionOn.family] using hbar)
    (fun d t0 _hd hsub =>
      pinchSec_tangentBundle_cont (I := I) S hS delta
        (fun t ht => hTsub (hsub ht)))
    (fun epsilon d t0 _hepsilon _hd hsub x v =>
      hbar.barrier_eval_continuous epsilon d t0 hsub x v v)





structure RicciWMPData
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (T : Real) : Type _ where
  X : TimeDependentVectorField (I := I) (M := M)
  N : TwoTensorReaction (I := I) (M := M)
  reg :
    TensorWMPSectionCore (I := I) (M := M)
      (fun t : Real => S.base.metric t) S.ricci X N T
  parabolic :
    TensorParabolicSupersolutionWithDriftOn (I := I) (M := M)
      (fun t : Real => S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M) S.ricci) X N
      (fun t x => ricciNabla2WMP (I := I) S t x)
      (fun t x => ricciNablaWMP (I := I) S t x) T
  null :
    TensorNullEigenvectorCondition (I := I) (M := M)
      (fun t : Real => S.base.metric t) N (Set.Icc 0 T)
  initial :
    TwoTensorFamilyNonnegativeAtTime (I := I) (M := M)
      (twoTensorSecToFamily (I := I) (M := M) S.ricci) 0

namespace RicciWMPData



def toInput
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    {S : SolutionOn (I := I) (M := M) D} {T : Real}
    (data : RicciWMPData (I := I) (M := M) S T) (hT : 0 <= T) :
    TensorWMPInput (I := I) (M := M)
      (fun t : Real => S.base.metric t) S.ricci data.X data.N
      (fun t : Real => S.base.connection t)
      (ricciNablaWMP (I := I) S) (ricciNabla2WMP (I := I) S) T where
  hT := hT
  reg := data.reg
  parabolic := data.parabolic
  null := data.null
  initial := data.initial
  hcov1 := fun t => ricciCov1 (I := I) S t
  hcovInf := fun t => ricciCovInf (I := I) S t
  hmc := fun t => ricciMetricComp (I := I) S t
  spatial := ricciSpatialWMP (I := I) S

end RicciWMPData


structure PinchWMPData
    (G : Real -> SmoothRiemannianMetric I M)
    (Ric : TwoTensorFamily (I := I) (M := M))
    (scalar : Real -> M -> Real) (T delta : Real) : Type _ where
  S : TwoTensorSecFamily (I := I) (M := M)
  X : TimeDependentVectorField (I := I) (M := M)
  N : TwoTensorReaction (I := I) (M := M)
  cov : Real -> CovariantDerivative I E (TangentSpace I : M -> Type _)
  nablaS : TensorNabla1SecFamily (I := I) (M := M)
  nabla2S : TensorNabla2SecFamily (I := I) (M := M)
  section_eq :
    twoTensorSecToFamily (I := I) (M := M) S =
      pinchTensor (I := I) (M := M) G Ric scalar delta
  reg :
    TensorWMPSectionCore (I := I) (M := M) G S X N T
  parabolic :
    TensorParabolicSupersolutionWithDriftOn (I := I) (M := M) G
      (twoTensorSecToFamily (I := I) (M := M) S) X N
      (fun t x => nabla2S t x) (fun t x => nablaS t x) T
  null :
    TensorNullEigenvectorCondition (I := I) (M := M) G N (Set.Icc 0 T)
  hcov1 :
    forall t : Real,
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (cov t) (1 : WithTop ℕ∞)
  hcovInf :
    forall t : Real,
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (cov t) (∞ : WithTop ℕ∞)
  hmc :
    forall t : Real,
      DifferentialGeometry.Geometry.Connection.IsMetricCompatible_gen (I := I) (cov t) (G t)
  spatial : TensorSpatialDerivs (I := I) (M := M) cov S nablaS nabla2S

namespace PinchWMPData


def toInput
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {T delta : Real}
    (data : PinchWMPData (I := I) (M := M) G Ric scalar T delta)
    (hT : 0 <= T)
    (hinit : TwoTensorFamilyNonnegativeAtTime (I := I) (M := M)
      (pinchTensor (I := I) (M := M) G Ric scalar delta) 0) :
    TensorWMPInput (I := I) (M := M)
      G data.S data.X data.N data.cov data.nablaS data.nabla2S T where
  hT := hT
  reg := data.reg
  parabolic := data.parabolic
  null := data.null
  initial := by
    simpa [data.section_eq] using hinit
  hcov1 := data.hcov1
  hcovInf := data.hcovInf
  hmc := data.hmc
  spatial := data.spatial

end PinchWMPData






structure PinchFlowWMPData
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (T delta : Real) : Type _ where
  X : TimeDependentVectorField (I := I) (M := M)
  N : TwoTensorReaction (I := I) (M := M)
  reg :
    TensorWMPSectionCore (I := I) (M := M)
      (fun t : Real => S.base.metric t) (pinchSec (I := I) S delta) X N T
  spatial :
    TensorSpatialDerivs (I := I) (M := M)
      (fun t : Real => S.base.connection t) (pinchSec (I := I) S delta)
      (pinchNablaModel (I := I) S delta) (pinchNab2ModelSec (I := I) S delta)
  parabolic :
    TensorParabolicSupersolutionWithDriftOn (I := I) (M := M)
      (fun t : Real => S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M) (pinchSec (I := I) S delta))
      X N
      (fun t x => pinchNab2ModelSec (I := I) S delta t x)
      (fun t x => pinchNablaModel (I := I) S delta t x) T
  null :
    TensorNullEigenvectorCondition (I := I) (M := M)
      (fun t : Real => S.base.metric t) N (Set.Icc 0 T)

namespace PinchFlowWMPData





def ofBarrier
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [CompactSpace M] [T2Space M]
    {S : SolutionOn (I := I) (M := M) D} (hS : IsSolutionOn (I := I) S)
    {T delta : Real}
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (X : TimeDependentVectorField (I := I) (M := M))
    (N : TwoTensorReaction (I := I) (M := M))
    (hbar : TensorBarrierRegularityOn (I := I) (M := M)
      (fun t : Real => S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M) (pinchSec (I := I) S delta))
      X N T)
    (hparabolic :
      TensorParabolicSupersolutionWithDriftOn (I := I) (M := M)
        (fun t : Real => S.base.metric t)
        (twoTensorSecToFamily (I := I) (M := M) (pinchSec (I := I) S delta))
        X N
        (fun t x => pinchNab2ModelSec (I := I) S delta t x)
        (fun t x => pinchNablaModel (I := I) S delta t x) T)
    (hnull :
      TensorNullEigenvectorCondition (I := I) (M := M)
        (fun t : Real => S.base.metric t) N (Set.Icc 0 T)) :
    PinchFlowWMPData (I := I) (M := M) S T delta where
  X := X
  N := N
  reg := pinchSecCore (I := I) S hS hTsub hbar
  spatial := pinchSpatialModel (I := I) S delta
  parabolic := hparabolic
  null := hnull





def ofSymmNull
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [CompactSpace M] [T2Space M]
    {S : SolutionOn (I := I) (M := M) D} (hS : IsSolutionOn (I := I) S)
    {T delta : Real}
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (X : TimeDependentVectorField (I := I) (M := M))
    (N : TwoTensorReaction (I := I) (M := M))
    (hbar : TensorBarrierRegularityOn (I := I) (M := M)
      (fun t : Real => S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M) (pinchSec (I := I) S delta))
      X N T)
    (hparabolic :
      TensorParabolicSupersolutionWithDriftOn (I := I) (M := M)
        (fun t : Real => S.base.metric t)
        (twoTensorSecToFamily (I := I) (M := M) (pinchSec (I := I) S delta))
        X N
        (fun t x => pinchNab2ModelSec (I := I) S delta t x)
        (fun t x => pinchNablaModel (I := I) S delta t x) T)
    (hdep :
      TensorReactionSymmInputOn (I := I) (M := M)
        (fun t : Real => S.base.metric t) N (Set.Icc 0 T))
    (hnull :
      TensorNullEigenvectorConditionSymm (I := I) (M := M)
        (fun t : Real => S.base.metric t) N (Set.Icc 0 T)) :
    PinchFlowWMPData (I := I) (M := M) S T delta :=
  ofBarrier (I := I) (M := M) hS hTsub X N hbar hparabolic
    (null_of_symm (I := I) (M := M) hdep hnull)





def ofShiftN
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [CompactSpace M] [T2Space M]
    {S : SolutionOn (I := I) (M := M) D} (hS : IsSolutionOn (I := I) S)
    {T delta : Real}
    (hdelta0 : 0 < delta) (hdelta13 : delta < (1 : Real) / 3)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (X : TimeDependentVectorField (I := I) (M := M))
    (hbar : TensorBarrierRegularityOn (I := I) (M := M)
      (fun t : Real => S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M) (pinchSec (I := I) S delta))
      X (shiftNRaw (I := I) (M := M) delta) T)
    (hparabolic :
      TensorParabolicSupersolutionWithDriftOn (I := I) (M := M)
        (fun t : Real => S.base.metric t)
        (twoTensorSecToFamily (I := I) (M := M) (pinchSec (I := I) S delta))
        X (shiftNRaw (I := I) (M := M) delta)
        (fun t x => pinchNab2ModelSec (I := I) S delta t x)
        (fun t x => pinchNablaModel (I := I) S delta t x) T) :
    PinchFlowWMPData (I := I) (M := M) S T delta :=
  ofSymmNull (I := I) (M := M) hS hTsub X
    (shiftNRaw (I := I) (M := M) delta) hbar hparabolic
    (shiftNRaw_symmInputOn (I := I) (M := M)
      (fun t : Real => S.base.metric t) (Set.Icc 0 T) delta)
    (shiftNRaw_null_symm (I := I) (M := M)
      (G := fun t : Real => S.base.metric t) (U := Set.Icc 0 T)
      hdelta0 hdelta13 hdim)





def ofShiftNLt
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [CompactSpace M] [T2Space M]
    {S : SolutionOn (I := I) (M := M) D} (hS : IsSolutionOn (I := I) S)
    {T delta : Real}
    (hdelta13 : delta < (1 : Real) / 3)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (X : TimeDependentVectorField (I := I) (M := M))
    (hbar : TensorBarrierRegularityOn (I := I) (M := M)
      (fun t : Real => S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M) (pinchSec (I := I) S delta))
      X (shiftNRaw (I := I) (M := M) delta) T)
    (hparabolic :
      TensorParabolicSupersolutionWithDriftOn (I := I) (M := M)
        (fun t : Real => S.base.metric t)
        (twoTensorSecToFamily (I := I) (M := M) (pinchSec (I := I) S delta))
        X (shiftNRaw (I := I) (M := M) delta)
        (fun t x => pinchNab2ModelSec (I := I) S delta t x)
        (fun t x => pinchNablaModel (I := I) S delta t x) T) :
    PinchFlowWMPData (I := I) (M := M) S T delta :=
  ofSymmNull (I := I) (M := M) hS hTsub X
    (shiftNRaw (I := I) (M := M) delta) hbar hparabolic
    (shiftNRaw_symmInputOn (I := I) (M := M)
      (fun t : Real => S.base.metric t) (Set.Icc 0 T) delta)
    (shiftNRaw_null_symm_of_lt (I := I) (M := M)
      (G := fun t : Real => S.base.metric t) (U := Set.Icc 0 T)
      hdelta13 hdim)




def ofShiftNReact
    [I.Boundaryless]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [CompactSpace M] [T2Space M]
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    {T delta : Real}
    (hdelta0 : 0 < delta) (hdelta13 : delta < (1 : Real) / 3)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (hTreg : Set.Ioc 0 T ⊆ D.regular)
    (hbar : TensorBarrierRegularityOn (I := I) (M := M)
      (fun t : Real => S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M) (pinchSec (I := I) S delta))
      (fun _t x => (0 : TangentSpace I x))
      (shiftNRaw (I := I) (M := M) delta) T)
    (hreact :
      ∀ t, t ∈ Set.Ioc 0 T -> ∀ x, ∀ v : TangentSpace I x,
        (shiftNRaw (I := I) (M := M) delta t (S.base.metric t)
          (twoTensorSecToFamily (I := I) (M := M)
            (pinchSec (I := I) S delta) t)) x v v =
          pinchCoordReact (I := I) S delta t x v) :
    PinchFlowWMPData (I := I) (M := M) S T delta :=
  ofShiftN (I := I) (M := M) hS.isSolution hdelta0 hdelta13 hdim hTsub
    (fun _t x => (0 : TangentSpace I x)) hbar
    (pinchParabolic_of_react (I := I) (M := M) S hS
      hTsub hTreg hreact)






def ofShiftNDirect
    [I.Boundaryless]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [CompactSpace M] [T2Space M]
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    {T delta : Real}
    (hdelta0 : 0 < delta) (hdelta13 : delta < (1 : Real) / 3)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (hTreg : Set.Ioc 0 T ⊆ D.regular)
    (hbar : TensorBarrierRegularityOn (I := I) (M := M)
      (fun t : Real => S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M) (pinchSec (I := I) S delta))
      (fun _t x => (0 : TangentSpace I x))
      (shiftNRaw (I := I) (M := M) delta) T) :
    PinchFlowWMPData (I := I) (M := M) S T delta :=
  ofShiftN (I := I) (M := M) hS.isSolution hdelta0 hdelta13 hdim hTsub
    (fun _t x => (0 : TangentSpace I x)) hbar
    (pinchParabolic (I := I) (M := M) S hS hdelta13 hdim hTsub hTreg)



def ofShiftNClosed
    [I.Boundaryless]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [CompactSpace M] [T2Space M]
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    {T delta : Real}
    (hdelta0 : 0 < delta) (hdelta13 : delta < (1 : Real) / 3)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (hTreg : Set.Ioc 0 T ⊆ D.regular) :
    PinchFlowWMPData (I := I) (M := M) S T delta :=
  ofShiftNDirect (I := I) (M := M) hS hdelta0 hdelta13 hdim hTsub hTreg
    (pinchBarrierReg (I := I) (M := M) S hS.isSolution
      hdelta13 hdim hTsub hTreg)



def toPinchWMPData
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    {S : SolutionOn (I := I) (M := M) D} {T delta : Real}
    (data : PinchFlowWMPData (I := I) (M := M) S T delta) :
    PinchWMPData (I := I) (M := M)
      (fun t : Real => S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M) S.ricci)
      S.scalar T delta where
  S := pinchSec (I := I) S delta
  X := data.X
  N := data.N
  cov := fun t : Real => S.base.connection t
  nablaS := pinchNablaModel (I := I) S delta
  nabla2S := pinchNab2ModelSec (I := I) S delta
  section_eq := pinchSec_eq (I := I) S delta
  reg := data.reg
  parabolic := data.parabolic
  null := data.null
  hcov1 := fun t => ricciCov1 (I := I) S t
  hcovInf := fun t => ricciCovInf (I := I) S t
  hmc := fun t => ricciMetricComp (I := I) S t
  spatial := data.spatial

end PinchFlowWMPData


theorem ricci_nonneg_wmp_raw
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2Ric : TensorNabla2Family (I := I) (M := M)}
    {nablaRic : TensorNabla1Family (I := I) (M := M)}
    {T : Real}
    (hT : 0 <= T)
    (hreg : TensorWMPRegularityOn (I := I) (M := M) G Ric X N T)
    (hparabolic : TensorParabolicSupersolutionWithDriftOn
      (I := I) (M := M) G Ric X N nabla2Ric nablaRic T)
    (hnull : TensorNullEigenvectorCondition (I := I) (M := M) G N (Set.Icc 0 T))
    (hinit : TwoTensorFamilyNonnegativeAtTime (I := I) (M := M) Ric 0) :
    TwoTensorFamilyNonnegativeOn (I := I) (M := M) Ric (Set.Icc 0 T) := by
  exact hamilton_tensor_wmp (I := I) (M := M) (G := G) (S := Ric)
    (X := X) (N := N) (nabla2S := nabla2Ric) (nablaS := nablaRic)
    hT hreg hparabolic hnull hinit


theorem ricci_nonneg_wmp
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {RicSec : TwoTensorSecFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {cov : Real -> CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {nablaRic : TensorNabla1SecFamily (I := I) (M := M)}
    {nabla2Ric : TensorNabla2SecFamily (I := I) (M := M)}
    {T : Real}
    (hRic :
      twoTensorSecToFamily (I := I) (M := M) RicSec = Ric)
    (data : TensorWMPInput (I := I) (M := M)
      G RicSec X N cov nablaRic nabla2Ric T) :
    TwoTensorFamilyNonnegativeOn (I := I) (M := M) Ric (Set.Icc 0 T) := by
  have hsec :
      TwoTensorFamilyNonnegativeOn (I := I) (M := M)
        (twoTensorSecToFamily (I := I) (M := M) RicSec) (Set.Icc 0 T) :=
    tensor_wmp (I := I) (M := M) data
  simpa [hRic] using hsec




theorem ricci_nonneg_sol
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M]
    (S : SolutionOn (I := I) (M := M) D)
    {T : Real}
    (hT : 0 <= T)
    (data : RicciWMPData (I := I) (M := M) S T) :
    TwoTensorFamilyNonnegativeOn (I := I) (M := M)
      (twoTensorSecToFamily (I := I) (M := M) S.ricci) (Set.Icc 0 T) := by
  exact tensor_wmp (I := I) (M := M) (RicciWMPData.toInput
    (I := I) (M := M) data hT)


theorem ricci_pinch_wmp_raw
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {delta : Real}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2S : TensorNabla2Family (I := I) (M := M)}
    {nablaS : TensorNabla1Family (I := I) (M := M)}
    {T : Real}
    (hT : 0 <= T)
    (_hdelta0 : 0 <= delta) (_hdelta13 : delta <= (1 : Real) / 3)
    (hreg : TensorWMPRegularityOn (I := I) (M := M) G
      (pinchTensor (I := I) (M := M) G Ric scalar delta) X N T)
    (hparabolic : TensorParabolicSupersolutionWithDriftOn
      (I := I) (M := M) G
      (pinchTensor (I := I) (M := M) G Ric scalar delta) X N
      nabla2S nablaS T)
    (hnull : TensorNullEigenvectorCondition (I := I) (M := M) G N (Set.Icc 0 T))
    (hinit : TwoTensorFamilyNonnegativeAtTime (I := I) (M := M)
      (pinchTensor (I := I) (M := M) G Ric scalar delta) 0) :
    TwoTensorFamilyNonnegativeOn (I := I) (M := M)
      (pinchTensor (I := I) (M := M) G Ric scalar delta) (Set.Icc 0 T) := by
  exact hamilton_tensor_wmp (I := I) (M := M) (G := G)
    (S := pinchTensor (I := I) (M := M) G Ric scalar delta)
    (X := X) (N := N) (nabla2S := nabla2S) (nablaS := nablaS)
    hT hreg hparabolic hnull hinit


theorem ricci_pinch_wmp
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {delta : Real}
    {S : TwoTensorSecFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {cov : Real -> CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {nablaS : TensorNabla1SecFamily (I := I) (M := M)}
    {nabla2S : TensorNabla2SecFamily (I := I) (M := M)}
    {T : Real}
    (_hdelta0 : 0 <= delta) (_hdelta13 : delta <= (1 : Real) / 3)
    (hS :
      twoTensorSecToFamily (I := I) (M := M) S =
        pinchTensor (I := I) (M := M) G Ric scalar delta)
    (data : TensorWMPInput (I := I) (M := M)
      G S X N cov nablaS nabla2S T) :
    PinchPres (I := I) (M := M) G Ric scalar T delta := by
  have hsec :
      TwoTensorFamilyNonnegativeOn (I := I) (M := M)
        (twoTensorSecToFamily (I := I) (M := M) S) (Set.Icc 0 T) :=
    tensor_wmp (I := I) (M := M) data
  simpa [PinchPres, hS] using hsec

namespace PinchWMPData


theorem preserve
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {T delta : Real}
    (data : PinchWMPData (I := I) (M := M) G Ric scalar T delta)
    (hT : 0 <= T)
    (hdelta0 : 0 <= delta) (hdelta13 : delta <= (1 : Real) / 3)
    (hinit : TwoTensorFamilyNonnegativeAtTime (I := I) (M := M)
      (pinchTensor (I := I) (M := M) G Ric scalar delta) 0) :
    PinchPres (I := I) (M := M) G Ric scalar T delta := by
  exact ricci_pinch_wmp (I := I) (M := M) (G := G) (Ric := Ric)
    (scalar := scalar) (delta := delta) (S := data.S) (X := data.X)
    (N := data.N) (cov := data.cov) (nablaS := data.nablaS)
    (nabla2S := data.nabla2S) (T := T)
    hdelta0 hdelta13 data.section_eq (data.toInput hT hinit)

end PinchWMPData

namespace PinchFlowWMPData




theorem preserve
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M]
    {S : SolutionOn (I := I) (M := M) D}
    {T delta : Real}
    (data : PinchFlowWMPData (I := I) (M := M) S T delta)
    (hT : 0 <= T)
    (hdelta0 : 0 <= delta) (hdelta13 : delta <= (1 : Real) / 3)
    (hinit : TwoTensorFamilyNonnegativeAtTime (I := I) (M := M)
      (pinchTensor (I := I) (M := M) (fun t : Real => S.base.metric t)
        (twoTensorSecToFamily (I := I) (M := M) S.ricci) S.scalar delta) 0) :
    PinchPres (I := I) (M := M) (fun t : Real => S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M) S.ricci) S.scalar T delta := by
  exact (data.toPinchWMPData (I := I) (M := M)).preserve
    (I := I) (M := M) hT hdelta0 hdelta13 hinit

end PinchFlowWMPData



theorem pinch_sol_closed
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [CompactSpace M]
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    {T delta : Real}
    (hT : 0 ≤ T) (hdelta0 : 0 < delta)
    (hdelta13 : delta < (1 : Real) / 3)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (hTreg : Set.Ioc 0 T ⊆ D.regular)
    (hinit : TwoTensorFamilyNonnegativeAtTime (I := I) (M := M)
      (pinchTensor (I := I) (M := M) (fun t : Real => S.base.metric t)
        (twoTensorSecToFamily (I := I) (M := M) S.ricci) S.scalar delta) 0) :
    PinchPres (I := I) (M := M) (fun t : Real => S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M) S.ricci) S.scalar T delta := by
  exact (PinchFlowWMPData.ofShiftNClosed (I := I) (M := M) hS
    hdelta0 hdelta13 hdim hTsub hTreg).preserve
      (I := I) (M := M) hT (le_of_lt hdelta0)
      (le_of_lt hdelta13) hinit




theorem pinch_sol_closed_nonneg
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [CompactSpace M]
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    {T delta : Real}
    (hT : 0 ≤ T) (hdelta0 : 0 ≤ delta)
    (hdelta13 : delta < (1 : Real) / 3)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (hTreg : Set.Ioc 0 T ⊆ D.regular)
    (hinit : TwoTensorFamilyNonnegativeAtTime (I := I) (M := M)
      (pinchTensor (I := I) (M := M) (fun t : Real => S.base.metric t)
        (twoTensorSecToFamily (I := I) (M := M) S.ricci) S.scalar delta) 0) :
    PinchPres (I := I) (M := M) (fun t : Real => S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M) S.ricci) S.scalar T delta := by
  exact (PinchFlowWMPData.ofShiftNLt (I := I) (M := M) hS.isSolution
    hdelta13 hdim hTsub (fun _t x => (0 : TangentSpace I x))
    (pinchBarrierReg (I := I) (M := M) S hS.isSolution
      hdelta13 hdim hTsub hTreg)
    (pinchParabolic (I := I) (M := M) S hS hdelta13 hdim hTsub hTreg)).preserve
      (I := I) (M := M) hT hdelta0 (le_of_lt hdelta13) hinit



theorem ricci_nonneg_sol_closed
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [CompactSpace M]
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    {T : Real}
    (hT : 0 ≤ T)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (hTreg : Set.Ioc 0 T ⊆ D.regular)
    (hinit : TwoTensorFamilyNonnegativeAtTime (I := I) (M := M)
      (twoTensorSecToFamily (I := I) (M := M) S.ricci) 0) :
    TwoTensorFamilyNonnegativeOn (I := I) (M := M)
      (twoTensorSecToFamily (I := I) (M := M) S.ricci) (Set.Icc 0 T) := by
  have hinit0 : TwoTensorFamilyNonnegativeAtTime (I := I) (M := M)
      (pinchTensor (I := I) (M := M) (fun t : Real => S.base.metric t)
        (twoTensorSecToFamily (I := I) (M := M) S.ricci) S.scalar 0) 0 := by
    intro x v
    simpa [pinchTensor] using hinit x v
  have hpinch : PinchPres (I := I) (M := M)
      (fun t : Real => S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M) S.ricci) S.scalar T 0 :=
    pinch_sol_closed_nonneg (I := I) (M := M) hS hT (le_refl 0)
      (by norm_num) hdim hTsub hTreg hinit0
  intro t ht x v
  exact (by
    simpa [PinchPres, pinchTensor] using hpinch t ht x v)


theorem pinch_init_wmp
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {T : Real}
    (hT : 0 <= T)
    (hinit : PinchInit (I := I) (M := M) G Ric scalar)
    (hdata :
      ∀ delta : Real, 0 < delta -> delta <= (1 : Real) / 3 ->
        PinchWMPData (I := I) (M := M) G Ric scalar T delta) :
    ∃ delta : Real,
      0 < delta ∧ delta <= (1 : Real) / 3 ∧
        PinchPres (I := I) (M := M) G Ric scalar T delta := by
  rcases hinit with ⟨delta, hdelta0, hdelta13, hpinch0⟩
  let data := hdata delta hdelta0 hdelta13
  refine ⟨delta, hdelta0, hdelta13, ?_⟩
  exact data.preserve (I := I) (M := M) hT
    (le_of_lt hdelta0) hdelta13 hpinch0


theorem pinch_init_wmp_lt
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {T : Real}
    (hT : 0 <= T)
    (hinit : PinchInitLt (I := I) (M := M) G Ric scalar)
    (hdata :
      ∀ delta : Real, 0 < delta -> delta < (1 : Real) / 3 ->
        PinchWMPData (I := I) (M := M) G Ric scalar T delta) :
    ∃ delta : Real,
      0 < delta ∧ delta < (1 : Real) / 3 ∧
        PinchPres (I := I) (M := M) G Ric scalar T delta := by
  rcases hinit with ⟨delta, hdelta0, hdelta13, hpinch0⟩
  let data := hdata delta hdelta0 hdelta13
  refine ⟨delta, hdelta0, hdelta13, ?_⟩
  exact data.preserve (I := I) (M := M) hT
    (le_of_lt hdelta0) (le_of_lt hdelta13) hpinch0



theorem pinch_init_sol_lt
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [CompactSpace M]
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    {T : Real}
    (hT : 0 ≤ T)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (hTreg : Set.Ioc 0 T ⊆ D.regular)
    (hinit : PinchInitLt (I := I) (M := M)
      (fun t : Real => S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M) S.ricci) S.scalar) :
    ∃ delta : Real,
      0 < delta ∧ delta < (1 : Real) / 3 ∧
        PinchPres (I := I) (M := M) (fun t : Real => S.base.metric t)
          (twoTensorSecToFamily (I := I) (M := M) S.ricci) S.scalar T delta := by
  refine pinch_init_wmp_lt (I := I) (M := M)
    (G := fun t : Real => S.base.metric t)
    (Ric := twoTensorSecToFamily (I := I) (M := M) S.ricci)
    (scalar := S.scalar) (T := T) hT hinit ?_
  intro delta hdelta0 hdelta13
  exact (PinchFlowWMPData.ofShiftNClosed (I := I) (M := M) hS
    hdelta0 hdelta13 hdim hTsub hTreg).toPinchWMPData (I := I) (M := M)



theorem strict_pinch_wmp
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {T : Real}
    (hT : 0 <= T)
    (hpos : RicciPosInit (I := I) (M := M) Ric)
    (hselect : BoundsOfPosRic (I := I) (M := M) G Ric scalar)
    (hdata :
      ∀ delta : Real, 0 < delta -> delta <= (1 : Real) / 3 ->
        PinchWMPData (I := I) (M := M) G Ric scalar T delta) :
    ∃ delta : Real,
      0 < delta ∧ delta <= (1 : Real) / 3 ∧
        PinchPres (I := I) (M := M) G Ric scalar T delta := by
  exact pinch_init_wmp (I := I) (M := M) (G := G) (Ric := Ric)
    (scalar := scalar) (T := T) hT
    (pinchInit_of_pos (I := I) (M := M) (G := G) (Ric := Ric)
      (scalar := scalar) hpos hselect)
    hdata



theorem strict_pinch_wmp_lt
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {T : Real}
    (hT : 0 <= T)
    (hpos : RicciPosInit (I := I) (M := M) Ric)
    (hselect : BoundsOfPosRic (I := I) (M := M) G Ric scalar)
    (hdata :
      ∀ delta : Real, 0 < delta -> delta < (1 : Real) / 3 ->
        PinchWMPData (I := I) (M := M) G Ric scalar T delta) :
    ∃ delta : Real,
      0 < delta ∧ delta < (1 : Real) / 3 ∧
        PinchPres (I := I) (M := M) G Ric scalar T delta := by
  exact pinch_init_wmp_lt (I := I) (M := M) (G := G) (Ric := Ric)
    (scalar := scalar) (T := T) hT
    (pinchInitLt_of_pos (I := I) (M := M) (G := G) (Ric := Ric)
      (scalar := scalar) hpos hselect)
    hdata



theorem strict_pinch_min
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [CompactSpace M] [Nonempty M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {ricMin : M -> Real}
    {T : Real}
    (hT : 0 <= T)
    (hmin : RicMinData (I := I) (M := M) G Ric ricMin)
    (hscalar : Continuous (fun x : M => scalar 0 x))
    (hdata :
      ∀ delta : Real, 0 < delta -> delta <= (1 : Real) / 3 ->
        PinchWMPData (I := I) (M := M) G Ric scalar T delta) :
    ∃ delta : Real,
      0 < delta ∧ delta <= (1 : Real) / 3 ∧
        PinchPres (I := I) (M := M) G Ric scalar T delta := by
  exact pinch_init_wmp (I := I) (M := M) (G := G) (Ric := Ric)
    (scalar := scalar) (T := T) hT
    (pinchInit_ricMin (I := I) (M := M) (G := G) (Ric := Ric)
      (scalar := scalar) (ricMin := ricMin) hmin hscalar)
    hdata



theorem strict_pinch_min_lt
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [CompactSpace M] [Nonempty M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {ricMin : M -> Real}
    {T : Real}
    (hT : 0 <= T)
    (hmin : RicMinData (I := I) (M := M) G Ric ricMin)
    (hscalar : Continuous (fun x : M => scalar 0 x))
    (hdata :
      ∀ delta : Real, 0 < delta -> delta < (1 : Real) / 3 ->
        PinchWMPData (I := I) (M := M) G Ric scalar T delta) :
    ∃ delta : Real,
      0 < delta ∧ delta < (1 : Real) / 3 ∧
        PinchPres (I := I) (M := M) G Ric scalar T delta := by
  exact pinch_init_wmp_lt (I := I) (M := M) (G := G) (Ric := Ric)
    (scalar := scalar) (T := T) hT
    (pinchInitLt_ricMin (I := I) (M := M) (G := G) (Ric := Ric)
      (scalar := scalar) (ricMin := ricMin) hmin hscalar)
    hdata



theorem strict_pinch_metric
    [I.Boundaryless]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [CompactSpace M] [T2Space M] [Nonempty M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {ricMin : M -> Real}
    {T : Real}
    (hT : 0 <= T)
    (D : MetricRicciData (I := I) (M := M) G Ric)
    (hmin : MetricRicciMin (I := I) (M := M) D ricMin)
    (hscalar : Continuous (fun x : M => scalar 0 x))
    (hdata :
      ∀ delta : Real, 0 < delta -> delta <= (1 : Real) / 3 ->
        PinchWMPData (I := I) (M := M) G Ric scalar T delta) :
    ∃ delta : Real,
      0 < delta ∧ delta <= (1 : Real) / 3 ∧
        PinchPres (I := I) (M := M) G Ric scalar T delta := by
  exact pinch_init_wmp (I := I) (M := M) (G := G) (Ric := Ric)
    (scalar := scalar) (T := T) hT
    (pinchInit_metric (I := I) (M := M) (G := G) (Ric := Ric)
      (scalar := scalar) (ricMin := ricMin) D hmin hscalar)
    hdata



theorem strict_pinch_metric_lt
    [I.Boundaryless]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [CompactSpace M] [T2Space M] [Nonempty M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {ricMin : M -> Real}
    {T : Real}
    (hT : 0 <= T)
    (D : MetricRicciData (I := I) (M := M) G Ric)
    (hmin : MetricRicciMin (I := I) (M := M) D ricMin)
    (hscalar : Continuous (fun x : M => scalar 0 x))
    (hdata :
      ∀ delta : Real, 0 < delta -> delta < (1 : Real) / 3 ->
        PinchWMPData (I := I) (M := M) G Ric scalar T delta) :
    ∃ delta : Real,
      0 < delta ∧ delta < (1 : Real) / 3 ∧
        PinchPres (I := I) (M := M) G Ric scalar T delta := by
  exact pinch_init_wmp_lt (I := I) (M := M) (G := G) (Ric := Ric)
    (scalar := scalar) (T := T) hT
    (pinchInitLt_metric (I := I) (M := M) (G := G) (Ric := Ric)
      (scalar := scalar) (ricMin := ricMin) D hmin hscalar)
    hdata



theorem strict_pinch_pos
    [I.Boundaryless]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [CompactSpace M] [T2Space M] [Nonempty M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {T : Real}
    (hT : 0 <= T)
    (D : MetricRicciData (I := I) (M := M) G Ric)
    (hpos : MetricRicciPos (I := I) (M := M) D)
    (hscalar : Continuous (fun x : M => scalar 0 x))
    (hdata :
      ∀ delta : Real, 0 < delta -> delta <= (1 : Real) / 3 ->
        PinchWMPData (I := I) (M := M) G Ric scalar T delta) :
    ∃ delta : Real,
      0 < delta ∧ delta <= (1 : Real) / 3 ∧
        PinchPres (I := I) (M := M) G Ric scalar T delta := by
  exact pinch_init_wmp (I := I) (M := M) (G := G) (Ric := Ric)
    (scalar := scalar) (T := T) hT
    (pinchInit_pos (I := I) (M := M) (G := G) (Ric := Ric)
      (scalar := scalar) D hpos hscalar)
    hdata


theorem strict_pinch_pos_lt
    [I.Boundaryless]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [CompactSpace M] [T2Space M] [Nonempty M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {T : Real}
    (hT : 0 <= T)
    (D : MetricRicciData (I := I) (M := M) G Ric)
    (hpos : MetricRicciPos (I := I) (M := M) D)
    (hscalar : Continuous (fun x : M => scalar 0 x))
    (hdata :
      ∀ delta : Real, 0 < delta -> delta < (1 : Real) / 3 ->
        PinchWMPData (I := I) (M := M) G Ric scalar T delta) :
    ∃ delta : Real,
      0 < delta ∧ delta < (1 : Real) / 3 ∧
        PinchPres (I := I) (M := M) G Ric scalar T delta := by
  exact pinch_init_wmp_lt (I := I) (M := M) (G := G) (Ric := Ric)
    (scalar := scalar) (T := T) hT
    (pinchInitLt_pos (I := I) (M := M) (G := G) (Ric := Ric)
      (scalar := scalar) D hpos hscalar)
    hdata



theorem strict_pinch_sol_lt
    [I.Boundaryless]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [CompactSpace M] [T2Space M]
    [Nonempty M]
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    {T : Real}
    (hT : 0 ≤ T)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (hTreg : Set.Ioc 0 T ⊆ D.regular)
    (hpos : RicciPosInit (I := I) (M := M)
      (twoTensorSecToFamily (I := I) (M := M) S.ricci)) :
    ∃ delta : Real,
      0 < delta ∧ delta < (1 : Real) / 3 ∧
        PinchPres (I := I) (M := M) (fun t : Real => S.base.metric t)
          (twoTensorSecToFamily (I := I) (M := M) S.ricci) S.scalar T delta := by
  exact pinch_init_sol_lt (I := I) (M := M) hS hT hdim hTsub hTreg
    (pinchInitLt_pos (I := I) (M := M)
      (G := fun t : Real => S.base.metric t)
      (Ric := twoTensorSecToFamily (I := I) (M := M) S.ricci)
      (scalar := S.scalar)
      (metricData_sol0 (I := I) (M := M) S)
      (metricData_sol0_pos (I := I) (M := M) S hpos)
      (scalar0_cont_sol (I := I) (M := M) S hS.isSolution
        (hTsub (show (0 : Real) ∈ Set.Icc 0 T from ⟨le_rfl, hT⟩))))

end DifferentialGeometry.PDE.RicciFlow
