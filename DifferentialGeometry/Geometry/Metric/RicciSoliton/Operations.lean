import DifferentialGeometry.Geometry.Curvature.Scaling
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciNaturalityCross
import DifferentialGeometry.Geometry.Metric.Product
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Defs
import DifferentialGeometry.Geometry.Operator.Pullback

set_option autoImplicit false

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

open Curvature Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem gradientRicciSoliton_scaleMetric
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {σ : Real}
    (h : gradientRicciSoliton (I := I) g f σ)
    (c : Real) (hc : 0 < c) :
    gradientRicciSoliton (I := I) (scaleMetric (I := I) c hc g) f (σ / c) := by
  intro x v w
  rw [Curvature.ricciTensor_scaleMetric, Operator.hessFun_scaleMetric,
    scaleMetric_inner, h x v w]
  field_simp [ne_of_gt hc]

end DifferentialGeometry.Geometry

namespace DifferentialGeometry.Geometry

open Curvature Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
  [FiniteDimensional Real F]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {G : Type*} [TopologicalSpace G]
variable {J : ModelWithCorners Real F G}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
variable [T2Space M] [I.Boundaryless] [T2Space N] [J.Boundaryless]

theorem gradientRicciSoliton_pullbackCross
    {g : SmoothRiemannianMetric J N} {f : C^∞⟮J, N; Real⟯} {σ : Real}
    (h : gradientRicciSoliton (I := J) g f σ)
    (Φ : M ≃ₘ⟮I, J⟯ N) :
    gradientRicciSoliton (I := I)
      (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Φ)
      (f.comp Φ.toContMDiffMap) σ := by
  intro x v w
  rw [Curvature.ricciTensor_pullbackCross, Operator.hessFun_pullbackCross,
    Diffeomorph.pullbackMetricCross_inner]
  exact h (Φ x) (mfderiv I J (Φ : M → N) x v)
    (mfderiv I J (Φ : M → N) x w)

theorem gradientRicciSoliton_prod
    [CompleteSpace E] [CompleteSpace F]
    [BoundarylessManifold I M] [BoundarylessManifold J N]
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric J N}
    {f : C^∞⟮I, M; Real⟯} {k : C^∞⟮J, N; Real⟯} {σ : Real}
    (hg : gradientRicciSoliton (I := I) g f σ)
    (hh : gradientRicciSoliton (I := J) h k σ) :
    gradientRicciSoliton (I := I.prod J) (g.prod h)
      (f.comp ContMDiffMap.fst + k.comp ContMDiffMap.snd) σ := by
  intro x u v
  let uM : TangentSpace I x.1 := u.1
  let uN : TangentSpace J x.2 := u.2
  let vM : TangentSpace I x.1 := v.1
  let vN : TangentSpace J x.2 := v.2
  change Curvature.ricciTensor (I := I.prod J) (g.prod h) x u v +
      Operator.hessFun (I := I.prod J) (g.prod h)
        (fun q : M × N => f q.1 + k q.2) x u v =
    (σ / 2) * (g.prod h).inner x u v
  rw [Curvature.ricciTensor_prod, Operator.hessFun_prod,
    SmoothRiemannianMetric.prod_inner, mfderiv_fst, mfderiv_snd]
  change Curvature.ricciTensor (I := I) g x.1 uM vM +
        Curvature.ricciTensor (I := J) h x.2 uN vN +
      (Operator.hessFun (I := I) g f x.1 uM vM +
        Operator.hessFun (I := J) h k x.2 uN vN) =
    (σ / 2) * (g.inner x.1 uM vM + h.inner x.2 uN vN)
  calc
    _ = (Curvature.ricciTensor (I := I) g x.1 uM vM +
          Operator.hessFun (I := I) g f x.1 uM vM) +
        (Curvature.ricciTensor (I := J) h x.2 uN vN +
          Operator.hessFun (I := J) h k x.2 uN vN) := by ring
    _ = (σ / 2) * g.inner x.1 uM vM +
        (σ / 2) * h.inner x.2 uN vN := by
      rw [hg x.1 uM vM, hh x.2 uN vN]
    _ = _ := by ring

end DifferentialGeometry.Geometry
