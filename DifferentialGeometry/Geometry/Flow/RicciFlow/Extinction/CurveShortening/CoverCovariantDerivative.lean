import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Product
import DifferentialGeometry.Geometry.Connection.ProductAlongCurve
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.CovariantDerivativeScaling
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Construction.Existence

noncomputable section

open Bundle Manifold Set Filter
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open scoped Manifold ContDiff Topology
open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong (covDerivAlong)

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

theorem ProductCurve.cover_covariantDerivative_of_boundaryless {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [BoundarylessManifold I M]
    (c : ProductCurve M) (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ)
    (hlambda : 0 < lambda) (t : ℝ) (V : c.Field (I := I))
    (hV : ContMDiff 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)).tangent ∞
      (fun x => (⟨c.coverLift x t, V x t⟩ : TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))))
    (x : ℝ) :
    covDerivAlong (coverProductMetric (g t) lambda hlambda) (fun z => c.coverLift z t)
      (fun z => V z t) x = c.Dx g V x t := by
  have hsec : ContMDiffAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)).tangent ∞
      (fun z => (⟨c.coverLift z t, V z t⟩ : TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))) x :=
    hV.contMDiffAt
  have hprod : ContMDiffAt 𝓘(ℝ, ℝ) (I.tangent.prod 𝓘(ℝ, ℝ).tangent) ∞
      (fun z => (equivTangentBundleProd I M 𝓘(ℝ, ℝ) ℝ)
        (⟨c.coverLift z t, V z t⟩ : TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))) x :=
    (contMDiff_equivTangentBundleProd (I := I) (I' := 𝓘(ℝ, ℝ)) (M := M) (M' := ℝ)
      (n := ∞)).contMDiffAt.comp x hsec
  have hfirst : MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent
      (fun z => (⟨c.projection.lift z t, (V z t).1⟩ : TangentBundle I M)) x :=
    ((contMDiff_fst (I := I.tangent) (J := 𝓘(ℝ, ℝ).tangent) (M := TangentBundle I M)
      (N := TangentBundle 𝓘(ℝ, ℝ) ℝ)).contMDiffAt.comp x hprod).mdifferentiableAt (by simp)
  have hsecond : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ).tangent
      (fun z => (⟨c.y z t, (V z t).2⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) x :=
    ((contMDiff_snd (I := I.tangent) (J := 𝓘(ℝ, ℝ).tangent) (M := TangentBundle I M)
      (N := TangentBundle 𝓘(ℝ, ℝ) ℝ)).contMDiffAt.comp x hprod).mdifferentiableAt (by simp)
  have hsplit := DifferentialGeometry.Geometry.Connection.covDerivAlong_prod (g := g t)
    (g' := DifferentialGeometry.scaleMetric (I := 𝓘(ℝ, ℝ)) (lambda ^ 2) (pow_pos hlambda 2)
      (DifferentialGeometry.euclideanMetric (E := ℝ)))
    (γ := fun z => c.projection.lift z t) (γ' := fun z => c.y z t)
    (Z := fun z => (V z t).1) (Z' := fun z => (V z t).2) x hfirst hsecond
  have hflat := covDerivAlong_scaleEuclideanLine_eq_deriv (lambda ^ 2) (pow_pos hlambda 2)
    (fun z => c.y z t) (fun z => (V z t).2) x
  have hcongr :=
    DifferentialGeometry.Geometry.Riemannian.Variation.covDerivAlong_congr_of_eventuallyEq
      (g := coverProductMetric (g t) lambda hlambda) (γ := fun z => c.coverLift z t)
    (V := fun z => V z t)
    (W := fun u => ((fun z => (V z t).1) u, (fun z => (V z t).2) u)) (t := x)
    (Filter.Eventually.of_forall fun u => Prod.mk.eta.symm)
  have hcur : (fun z => c.coverLift z t) = fun u => (c.projection.lift u t, c.y u t) := rfl
  rw [hcongr]
  unfold coverProductMetric
  rw [hcur, ProductCurve.Dx]
  exact hsplit.trans (by rw [hflat]; rfl)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
