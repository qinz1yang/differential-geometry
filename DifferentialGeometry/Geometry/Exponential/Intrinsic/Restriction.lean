import DifferentialGeometry.Geometry.Geodesic.Naturality.OpenSubtype
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Framed.Coordinates

set_option autoImplicit false

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

namespace DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

variable [PseudoEMetricSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

theorem intrinsicGeodesic_restrictOpen
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (U : TopologicalSpace.Opens M) [SigmaCompactSpace U]
    [RiemannianBundle (fun x : U => TangentSpace I x)]
    [IsRiemannianManifold I U] [hcompleteU : CompleteSpace U]
    [IsContinuousRiemannianBundle E (fun x : U => TangentSpace I x)]
    (hUEnorm : IsMetricNorm (g.restrictOpen U))
    (x : U) (v : TangentSpace I x) (t : ℝ) :
    (intrinsicGeodesic (I := I) (M := U) (g.restrictOpen U) hUEnorm x v t : M) =
      intrinsicGeodesic g hEnorm (x : M) (mfderiv I I (Subtype.val : U → M) x v) t := by
  let γ := intrinsicGeodesic (I := I) (M := U) (g.restrictOpen U) hUEnorm x v
  have hγgeo : Geodesic.IsGeodesic g (fun t => (γ t : M)) :=
    (Geodesic.geodesic_open_iff g U γ).mp
      (intrinsicGeodesic_isGeodesic (g.restrictOpen U) hUEnorm x v)
  have hγcont : Continuous γ :=
    intrinsicGeodesic_continuous (g.restrictOpen U) hUEnorm x v
  have hγ0 : γ 0 = x := intrinsicGeodesic_zero (g.restrictOpen U) hUEnorm x v
  let w := mfderiv I I (Subtype.val : U → M) x v
  have heq := isGeodesic_eq_of_initial g hγgeo
    (intrinsicGeodesic_isGeodesic g hEnorm (x : M) w)
    (continuous_subtype_val.comp hγcont)
    (intrinsicGeodesic_continuous g hEnorm (x : M) w)
    ((congrArg Subtype.val hγ0).trans (intrinsicGeodesic_zero g hEnorm (x : M) w).symm)
    (show (mfderiv 𝓘(ℝ, ℝ) I (fun t => (γ t : M)) 0 1 : E) =
      (mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic g hEnorm (x : M) w) 0 1 : E) from by
      have hc' := congrArg (fun L : ℝ →L[ℝ] E => L 1)
        (DifferentialGeometry.mfderiv_subtypeVal_comp (I := 𝓘(ℝ, ℝ)) (J := I) γ 0)
      have hvU : (mfderiv 𝓘(ℝ, ℝ) I γ 0 1 : E) = (v : E) :=
        intrinsicGeodesic_mfderiv_zero (g.restrictOpen U) hUEnorm x v
      have hvM : (mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic g hEnorm (x : M) w) 0 1 : E) =
          (w : E) := intrinsicGeodesic_mfderiv_zero g hEnorm (x : M) w
      exact hc'.trans (hvU.trans ((mfderiv_subtype_val_apply U x v).symm.trans hvM.symm)))
  exact congrFun heq t

theorem expMapIntrinsic_restrictOpen
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (U : TopologicalSpace.Opens M) [SigmaCompactSpace U]
    [RiemannianBundle (fun x : U => TangentSpace I x)]
    [IsRiemannianManifold I U] [hcompleteU : CompleteSpace U]
    [IsContinuousRiemannianBundle E (fun x : U => TangentSpace I x)]
    (hUEnorm : IsMetricNorm (g.restrictOpen U))
    (x : U) (v : TangentSpace I x) :
    (expMapIntrinsic (I := I) (M := U) (g.restrictOpen U) hUEnorm x v : M) =
      expMapIntrinsic g hEnorm (x : M) (mfderiv I I (Subtype.val : U → M) x v) := by
  exact intrinsicGeodesic_restrictOpen g hEnorm U hUEnorm x v 1

end DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

open Exponential

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  [PseudoEMetricSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

theorem intrinsicFramedExp_restrictOpen
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (U : TopologicalSpace.Opens M) [SigmaCompactSpace U]
    [RiemannianBundle (fun x : U => TangentSpace I x)]
    [IsRiemannianManifold I U] [CompleteSpace U]
    [IsContinuousRiemannianBundle E (fun x : U => TangentSpace I x)]
    (hUEnorm : IsMetricNorm (g.restrictOpen U)) (x : U) (v : E) :
    (intrinsicFramedExp (I := I) (M := U) (g.restrictOpen U) hUEnorm x v : M) =
      intrinsicFramedExp g hEnorm (x : M) v := by
  have hfU := intrinsicFrame_apply (g.restrictOpen U) hUEnorm x v
  have hfM := intrinsicFrame_apply g hEnorm (x : M) v
  have hexp := expMapIntrinsic_restrictOpen g hEnorm U hUEnorm x
    (normalFrame (g.restrictOpen U) x v)
  have hv : mfderiv I I (Subtype.val : U → M) x (normalFrame (g.restrictOpen U) x v) =
      normalFrame g (x : M) v :=
    (mfderiv_subtype_val_apply U x _).trans (normalFrame_restrictOpen g U x v)
  exact (congrArg Subtype.val hfU).trans
    (hexp.trans ((congrArg (expMapIntrinsic g hEnorm (x : M)) hv).trans hfM.symm))

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

end
