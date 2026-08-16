import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.HamiltonIveySupportUpper
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.RicciPreservation

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

theorem hamiltonIveySupportCoefficient_continuousOn
    {K a t0 T : Real} (hK : 0 < K) (ha : 0 < a) (ht0 : t0 ≤ 0) :
    ContinuousOn (fun t : Real => hamiltonIveySupportCoefficient K a t0 t) (Set.Icc 0 T) := by
  unfold hamiltonIveySupportCoefficient
  have hden : ∀ t ∈ Set.Icc 0 T, 0 < 1 + 2 * K * (t - t0) := by
    intro t ht
    have ht0' : 0 ≤ t - t0 := by linarith [ht.1, ht0]
    nlinarith [mul_nonneg (mul_pos (by norm_num : (0 : ℝ) < 2) hK).le ht0']
  have hnum : ContinuousOn (fun t : Real => K * Real.exp (a + 2)) (Set.Icc 0 T) := by
    fun_prop
  have hdenc : ContinuousOn (fun t : Real => a * (1 + 2 * K * (t - t0))) (Set.Icc 0 T) := by
    fun_prop
  exact hnum.div hdenc (fun t ht => by
    have h1 : 0 < a * (1 + 2 * K * (t - t0)) := mul_pos ha (hden t ht)
    exact ne_of_gt h1)

theorem hamiltonIveySupportCoefficient_continuous_subtype
    {K a t0 T : Real} (hK : 0 < K) (ha : 0 < a) (ht0 : t0 ≤ 0) :
    Continuous (fun q : {t : Real // t ∈ Set.Icc 0 T} × M =>
      hamiltonIveySupportCoefficient K a t0 q.1.1) := by
  have hc : ContinuousOn (fun t : Real => hamiltonIveySupportCoefficient K a t0 t)
      (Set.Icc 0 T) :=
    hamiltonIveySupportCoefficient_continuousOn hK ha ht0
  have hc' : Continuous (fun t : {t : Real // t ∈ Set.Icc 0 T} =>
      hamiltonIveySupportCoefficient K a t0 (t : Real)) :=
    continuousOn_iff_continuous_restrict.mp hc
  exact hc'.comp continuous_fst

theorem hamiltonIveySupportUpperSecFamilyContinuousOnSet
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {K a t0 T : Real} (hK : 0 < K) (ha : 0 < a) (ht0 : t0 ≤ 0)
    (hTsub : Set.Icc 0 T ⊆ D.carrier) :
    Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 (Set.Icc 0 T)
      (fun t x => (hamiltonIveySupportUpperSec S K a t0) t x) := by
  have hcoef :
      Continuous (fun q : {t : Real // t ∈ Set.Icc 0 T} × M =>
        hamiltonIveySupportCoefficient K a t0 q.1.1) :=
    hamiltonIveySupportCoefficient_continuous_subtype hK ha ht0
  have hmetric :
      Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 (Set.Icc 0 T)
        (fun t x => metricTensorField (I := I) (S.base.metric t) x) := by
    have hcont := hS.smoothMetric.metricTensor_cont
    exact Tensor0SFamilyContinuousOnSet.mono (I := I) (M := M)
      (by simpa [SolutionOn.family] using hcont) hTsub
  have hscaled :
      Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 (Set.Icc 0 T)
        (fun t x => hamiltonIveySupportCoefficient K a t0 t •
          metricTensorField (I := I) (S.base.metric t) x) :=
    Tensor0SFamilyContinuousOnSet.smul (I := I) (M := M)
      (s := 2) (K := Set.Icc 0 T)
      (f := fun t x => hamiltonIveySupportCoefficient K a t0 t)
      (A := fun t x => metricTensorField (I := I) (S.base.metric t) x)
      hcoef hmetric
  have hpinch := pinchSecFamilyContinuousOnSet (I := I) (M := M) S hS
    ((1 + a) / (2 * a))
  have hpinch' := Tensor0SFamilyContinuousOnSet.mono (I := I) (M := M) hpinch hTsub
  have hneg := Tensor0SFamilyContinuousOnSet.const_smul (I := I) (M := M)
    (s := 2) (K := Set.Icc 0 T)
    (A := fun t x => (pinchSec (I := I) S ((1 + a) / (2 * a))) t x) (-1 : Real) hpinch'
  have hsub := Tensor0SFamilyContinuousOnSet.add (I := I) (M := M)
    (s := 2) (K := Set.Icc 0 T)
    (A := fun t x => hamiltonIveySupportCoefficient K a t0 t •
      metricTensorField (I := I) (S.base.metric t) x)
    (B := fun t x => (-1 : Real) • (pinchSec (I := I) S ((1 + a) / (2 * a))) t x)
    hscaled hneg
  simpa [hamiltonIveySupportUpperSec, hamiltonIveySupportPinchDelta, sub_eq_add_neg]
    using hsub

theorem hamiltonIveySupportUpperSec_tangentBundle_cont
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval} {K : Set Real}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {Kc a t0 T : Real} (hK : 0 < Kc) (ha : 0 < a) (ht0 : t0 ≤ 0)
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (hKsub : K ⊆ Set.Icc 0 T) :
    Continuous (fun q : {t : Real // t ∈ K} × TangentBundle I M =>
      TotalSpace.mk' (Tensor0SModel 2 Real E)
        (E := fun x : M => Tensor0SSpace 2 I x) q.2.proj
        ((hamiltonIveySupportUpperSec S Kc a t0) q.1.1 q.2.proj)) := by
  exact Tensor0SFamilyContinuousOnSet.tangentBundle (I := I) (M := M)
    (Tensor0SFamilyContinuousOnSet.mono (I := I) (M := M)
      (hamiltonIveySupportUpperSecFamilyContinuousOnSet (I := I) S hS hK ha ht0 hTsub)
      hKsub)

theorem hamiltonIveySupportUpperSpatialModel
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (Kc a t0 : Real) :
    TensorSpatialDerivs (I := I) (M := M)
      (fun t : Real => S.base.connection t)
      (hamiltonIveySupportUpperSec S Kc a t0)
      (hamiltonIveySupportUpperNablaModel S a)
      (hamiltonIveySupportUpperNab2ModelSec S a) := by
  constructor
  · intro t
    letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2
    letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 3
    have hPinchFirst := (pinchSpatialModel (I := I) S ((1 + a) / (2 * a))).first t
    have hneg := TotalNabla0SRealizes.smul (I := I) (M := M) (-1 : Real) hPinchFirst
    have hmetric : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 2 (S.base.connection t)
        (hamiltonIveySupportCoefficient Kc a t0 t •
          metricTensorField (I := I) (S.base.metric t))
        (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (n := (∞ : WithTop ℕ∞)) 3) := by
      have hz := zero_realizes_metric (I := I) (S.base.connection t)
        (S.base.metric t) (ricciMetricComp (I := I) S t)
      have hsmul := TotalNabla0SRealizes.smul (I := I) (M := M)
        (hamiltonIveySupportCoefficient Kc a t0 t) hz
      simpa using hsmul
    have hadd := TotalNabla0SRealizes.add (I := I) (M := M) hmetric hneg
    simpa [hamiltonIveySupportUpperSec, hamiltonIveySupportUpperNablaModel,
      hamiltonIveySupportPinchDelta, sub_eq_add_neg] using hadd
  · intro t
    letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 3
    letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 4
    have hPinchSecond := (pinchSpatialModel (I := I) S ((1 + a) / (2 * a))).second t
    have hneg := TotalNabla0SRealizes.smul (I := I) (M := M) (-1 : Real) hPinchSecond
    simpa [hamiltonIveySupportUpperNablaModel, hamiltonIveySupportUpperNab2ModelSec,
      hamiltonIveySupportPinchDelta] using hneg

end DifferentialGeometry.PDE.RicciFlow

end
