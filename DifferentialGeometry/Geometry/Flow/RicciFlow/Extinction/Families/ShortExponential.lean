import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.Preparation
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Geodesic.Basic

noncomputable section
open Bundle Manifold Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.PDE.RicciFlow.Extinction.Families

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q]
  [IsManifold I ∞ Q] [T2Space Q] [SigmaCompactSpace Q]
  [RiemannianBundle (fun x : Q => TangentSpace I x)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem shortSegment_exp_of_isShortSegment
    [PseudoEMetricSpace Q] [IsRiemannianManifold I Q] [CompleteSpace Q]
    [IsContinuousRiemannianBundle E (fun x : Q => TangentSpace I x)]
    (g : SmoothRiemannianMetric I Q) (hEnorm : IsMetricNorm (I := I) g)
    (p q : Q) (c : ℝ → Q) (hc : IsShortSegment g p q c)
    (t : ℝ) (ht : t ∈ Ioo (-1 : ℝ) 2) :
    c t = expMapIntrinsic g hEnorm p
      (t • (show TangentSpace I p from (mfderiv 𝓘(ℝ, ℝ) I c 0 (1 : ℝ) : E))) := by
  let v : TangentSpace I p :=
    (show E from mfderiv 𝓘(ℝ, ℝ) I c 0 (1 : ℝ))
  have heq : EqOn c (intrinsicGeodesic g hEnorm p v) (Ioo (-1 : ℝ) 2) := by
    apply geo_eqOn_of_initial g isOpen_Ioo isPreconnected_Ioo
      (show (0 : ℝ) ∈ Ioo (-1 : ℝ) 2 by norm_num)
      hc.2.1 ((intrinsicGeodesic_isGeodesic g hEnorm p v).isGeodesicOn _)
      hc.1.continuousOn (intrinsicGeodesic_continuous g hEnorm p v).continuousOn
    · rw [intrinsicGeodesic_zero]
      exact hc.2.2.1
    · exact (intrinsicGeodesic_mfderiv_zero g hEnorm p v).symm
  calc
    c t = intrinsicGeodesic g hEnorm p v t := heq ht
    _ = intrinsicGeodesic g hEnorm p (t • v) 1 :=
      (intrinsicGeodesic_smul g hEnorm p v t).symm
    _ = expMapIntrinsic g hEnorm p (t • v) := rfl

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
