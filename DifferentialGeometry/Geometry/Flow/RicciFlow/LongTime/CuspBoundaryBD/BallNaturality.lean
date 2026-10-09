import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspBoundaryBD.BallPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspBoundaryBD.CurvatureKernel
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Naturality.PullbackLocalIso

/-!
# IMS04 / O4b（S-A10-BOUNDARY, suffix `_BD`）：曲线的 speed / 曲率向量沿 local isometry 的 naturality

`f : M → N` local diffeomorphism，`g' = localPullMetric G f`（`g'(v,w) = G(Df v, Df w)`），`β : ℝ → M`
光滑正则。则

* `riemannianCurveSpeed G (f ∘ β) = riemannianCurveSpeed g' β`；
* `riemannianCurveCurvature G (f ∘ β) s = Df (riemannianCurveCurvature g' β s)`（曲率向量），
  从而 `|κ_G(f∘β)|_G = |κ_{g'}(β)|_{g'}`。

证明：unit tangent `T_G = Df ∘ T_{g'}`，`covDerivAlong_map_localPullMetric`。
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace GC.LongTime

section Generic

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
  [IsManifold (𝓡 3) ∞ N] [T2Space N]

omit [T2Space N] in
theorem riemannianCurveSpeed_comp_localPull_BD (G : SmoothRiemannianMetric (𝓡 3) N) {f : M → N}
    (hld : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ f) {β : ℝ → M} (s : ℝ)
    (hβ : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 3) β s) :
    riemannianCurveSpeed G (f ∘ β) s =
      riemannianCurveSpeed (localPullMetric (I := 𝓡 3) (J := 𝓡 3) G f hld) β s := by
  have hdf : MDifferentiableAt (𝓡 3) (𝓡 3) f (β s) :=
    (hld.contMDiff).mdifferentiableAt (by simp)
  unfold riemannianCurveSpeed
  rw [mfderiv_comp s hdf hβ, localPullMetric_inner]
  rfl

variable [BoundarylessManifold (𝓡 3) M] [BoundarylessManifold (𝓡 3) N]

/-- 曲率向量的 naturality：`Df (κ_{g'}(β) s) = κ_G(f ∘ β) s`。 -/
theorem riemannianCurveCurvature_comp_localPull_BD (G : SmoothRiemannianMetric (𝓡 3) N)
    {f : M → N} (hld : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ f) {β : ℝ → M}
    (hβ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) ∞ β) (hi : ∀ s, mfderiv 𝓘(ℝ, ℝ) (𝓡 3) β s 1 ≠ 0) (s : ℝ) :
    mfderiv (𝓡 3) (𝓡 3) f (β s)
        (riemannianCurveCurvature (localPullMetric (I := 𝓡 3) (J := 𝓡 3) G f hld) β s) =
      riemannianCurveCurvature G (f ∘ β) s := by
  set g' := localPullMetric (I := 𝓡 3) (J := 𝓡 3) G f hld with hg'
  have hdf : ∀ u, MDifferentiableAt (𝓡 3) (𝓡 3) f (β u) := fun u =>
    (hld.contMDiff).mdifferentiableAt (by simp)
  have hβd : ∀ u, MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 3) β u := fun u =>
    (hβ u).mdifferentiableAt (by simp)
  have hvel : ∀ u, mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (f ∘ β) u 1 =
      mfderiv (𝓡 3) (𝓡 3) f (β u) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) β u 1) := fun u => by
    rw [mfderiv_comp u (hdf u) (hβd u)]
    rfl
  have hsp : ∀ u, riemannianCurveSpeed G (f ∘ β) u = riemannianCurveSpeed g' β u := fun u =>
    riemannianCurveSpeed_comp_localPull_BD G hld u (hβd u)
  have hT : riemannianCurveUnitTangent G (f ∘ β) =
      fun u => mfderiv (𝓡 3) (𝓡 3) f (β u) (riemannianCurveUnitTangent g' β u) := by
    funext u
    unfold riemannianCurveUnitTangent
    rw [hsp u, hvel u, map_smul]
  have hTd : DifferentiableAt ℝ (chartRepAt β (riemannianCurveUnitTangent g' β) s) s :=
    (contDiffAt_chartRepAt_of_section
      ((contMDiff_riemannianCurveUnitTangent g' hβ hi).contMDiffAt (x := s))).differentiableAt
      (by simp)
  have hnat := covDerivAlong_map_localPullMetric G hld β (riemannianCurveUnitTangent g' β) s
    (hβ s) hTd
  unfold riemannianCurveCurvature
  rw [hT, ← hsp s, map_smul, hnat]
  rfl

omit [T2Space N] [BoundarylessManifold (𝓡 3) N] [BoundarylessManifold (𝓡 3) M] in
/-- 曲率范数相等：`|κ_G(f∘β)|_G = |κ_{g'}(β)|_{g'}`。 -/
theorem sqrt_curvature_comp_localPull_BD (G : SmoothRiemannianMetric (𝓡 3) N)
    {f : M → N} (hld : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ f) {β : ℝ → M} (s : ℝ)
    (hκ : mfderiv (𝓡 3) (𝓡 3) f (β s)
        (riemannianCurveCurvature (localPullMetric (I := 𝓡 3) (J := 𝓡 3) G f hld) β s) =
      riemannianCurveCurvature G (f ∘ β) s) :
    Real.sqrt (G.inner ((f ∘ β) s) (riemannianCurveCurvature G (f ∘ β) s)
        (riemannianCurveCurvature G (f ∘ β) s)) =
      Real.sqrt ((localPullMetric (I := 𝓡 3) (J := 𝓡 3) G f hld).inner (β s)
        (riemannianCurveCurvature (localPullMetric (I := 𝓡 3) (J := 𝓡 3) G f hld) β s)
        (riemannianCurveCurvature (localPullMetric (I := 𝓡 3) (J := 𝓡 3) G f hld) β s)) := by
  rw [← hκ, localPullMetric_inner]
  rfl

end Generic

end GC.LongTime
