import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Projection
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.CoverCovariantDerivative
import DifferentialGeometry.Geometry.Connection.ParallelTransport.CovariantDerivativeRegularity
import DifferentialGeometry.Bundle.VelocityLift
import DifferentialGeometry.Bundle.Section

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem coverLift_space_contMDiff (c : ProductCurve M) {J : Set ℝ}
    (hc : c.SmoothOn (I := I) J) (t : ℝ) (ht : t ∈ J) :
    ContMDiff 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) ∞ (fun x => c.coverLift x t) := by
  have hbase : ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun x => c.projection.lift x t) :=
    contMDiffOn_univ.mp (c.projection.space_slice_contMDiffOn J hc.1 t ht)
  have hy : ContDiff ℝ ∞ (fun x => c.y x t) :=
    contDiffOn_univ.mp (hc.2.comp (contDiff_id.prodMk contDiff_const).contDiffOn
      (fun x _ => ⟨Set.mem_univ x, ht⟩))
  exact hbase.prodMk hy.contMDiff

variable [IsManifold I ∞ M]

theorem cover_X_contMDiff (c : ProductCurve M) {J : Set ℝ}
    (hc : c.SmoothOn (I := I) J) (t : ℝ) (ht : t ∈ J) :
    ContMDiff 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)).tangent ∞
      (fun x => (⟨c.coverLift x t, c.X (I := I) x t⟩ :
        TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))) := by
  intro x
  have h := ((c.coverLift_space_contMDiff hc t ht).contMDiffAt (x := x)).velocityLift
    (m := ∞) (by simp)
  apply h.congr_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro y
  exact congrArg (fun v => (⟨c.coverLift y t, v⟩ :
    TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))) (c.cover_spatial_derivative J hc y t ht).symm

theorem cover_unitTangent_contMDiff (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    {J : Set ℝ} (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (t : ℝ) (ht : t ∈ J) :
    ContMDiff 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)).tangent ∞
      (fun x => (⟨c.coverLift x t, c.unitTangent g lambda x t⟩ :
        TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))) := by
  have hs := (c.speed_contDiff_of_immersedOn g lambda hlambda hc hi t ht).inv
    (fun x => (c.speed_pos_of_immersedOn g lambda hlambda hi x t ht).ne')
  exact hs.contMDiff.smul_bundle (c.cover_X_contMDiff hc t ht)

variable [FiniteDimensional ℝ E] [T2Space M] [I.Boundaryless]

theorem cover_Dx_contMDiff (c : ProductCurve M) (g : ℝ → SmoothRiemannianMetric I M)
    (V : c.Field (I := I)) (t : ℝ)
    (hV : ContMDiff 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)).tangent ∞
      (fun x => (⟨c.coverLift x t, V x t⟩ :
        TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ)))) :
    ContMDiff 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)).tangent ∞
      (fun x => (⟨c.coverLift x t, c.Dx g V x t⟩ :
        TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))) := by
  have h := contMDiff_covDerivAlong (coverProductMetric (g t) 1 zero_lt_one)
    hV (m := ⊤) (by simp)
  apply h.congr
  intro x
  exact congrArg (fun v => (⟨c.coverLift x t, v⟩ :
    TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ)))
    (c.cover_covariantDerivative_of_boundaryless g 1 zero_lt_one t V hV x).symm

theorem cover_Ds_contMDiff (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    {J : Set ℝ} (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (V : c.Field (I := I)) (t : ℝ) (ht : t ∈ J)
    (hV : ContMDiff 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)).tangent ∞
      (fun x => (⟨c.coverLift x t, V x t⟩ :
        TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ)))) :
    ContMDiff 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)).tangent ∞
      (fun x => (⟨c.coverLift x t, c.Ds g lambda V x t⟩ :
        TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))) := by
  have hs := (c.speed_contDiff_of_immersedOn g lambda hlambda hc hi t ht).inv
    (fun x => (c.speed_pos_of_immersedOn g lambda hlambda hi x t ht).ne')
  exact hs.contMDiff.smul_bundle (c.cover_Dx_contMDiff g V t hV)

theorem cover_curvatureVector_contMDiff (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    {J : Set ℝ} (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (t : ℝ) (ht : t ∈ J) :
    ContMDiff 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)).tangent ∞
      (fun x => (⟨c.coverLift x t, c.curvatureVector g lambda x t⟩ :
        TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))) :=
  c.cover_Ds_contMDiff g lambda hlambda hc hi (c.unitTangent g lambda) t ht
    (c.cover_unitTangent_contMDiff g lambda hlambda hc hi t ht)

theorem cover_iteratedDs_contMDiff (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    {J : Set ℝ} (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (V : c.Field (I := I)) (t : ℝ) (ht : t ∈ J)
    (hV : ContMDiff 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)).tangent ∞
      (fun x => (⟨c.coverLift x t, V x t⟩ :
        TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ)))) (m : ℕ) :
    ContMDiff 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)).tangent ∞
      (fun x => (⟨c.coverLift x t, c.iteratedDs g lambda m V x t⟩ :
        TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))) := by
  induction m with
  | zero => exact hV
  | succ m ih =>
    simp only [iteratedDs, Function.iterate_succ_apply']
    exact c.cover_Ds_contMDiff g lambda hlambda hc hi (c.iteratedDs g lambda m V) t ht ih

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve
