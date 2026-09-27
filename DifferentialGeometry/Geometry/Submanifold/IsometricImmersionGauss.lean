import DifferentialGeometry.Topology.VectorField.OpenSubtypePullback
import DifferentialGeometry.Geometry.Curvature.Metric.Defs
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.CovariantDerivativeAlong

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Bundle Function Manifold Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

namespace DifferentialGeometry.Geometry

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem mfderiv_opens_eq_fderiv (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin m)))
    {ψ : EuclideanSpace ℝ (Fin m) → ℝ} {x : EuclideanSpace ℝ (Fin m)} (hx : x ∈ U)
    (hψ : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ) ψ x)
    (v : EuclideanSpace ℝ (Fin m)) :
    mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ)
      (fun u : U => ψ (u : EuclideanSpace ℝ (Fin m))) ⟨x, hx⟩ v = fderiv ℝ ψ x v := by
  have hsub : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      (Subtype.val : U → EuclideanSpace ℝ (Fin m)) (⟨x, hx⟩ : U) :=
    (contMDiff_subtype_val (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (U := U) (n := ∞)).mdifferentiableAt
      (by simp)
  have hcomp := mfderiv_comp_apply (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
    (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (I'' := 𝓘(ℝ))
    (x := (⟨x, hx⟩ : U)) (f := (Subtype.val : U → EuclideanSpace ℝ (Fin m))) (g := ψ) hψ hsub v
  have hstep : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      (Subtype.val : U → EuclideanSpace ℝ (Fin m)) (⟨x, hx⟩ : U) v = v := by
    rw [DifferentialGeometry.mfderiv_subtype_val]
    rfl
  rw [hstep, mfderiv_eq_fderiv] at hcomp
  exact hcomp

def IsometricImmersionPullbackConnection (g : SmoothRiemannianMetric I M)
    (F : EuclideanSpace ℝ (Fin m) → M) (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin m)))
    (h : SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) U) : Prop :=
  ∀ (x : U) (X Y Z : EuclideanSpace ℝ (Fin m)),
    g.inner (F x)
        (covDerivAlong (I := I) g (fun t : ℝ => F ((x : EuclideanSpace ℝ (Fin m)) + t • X))
          (fun t : ℝ => mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F
            ((x : EuclideanSpace ℝ (Fin m)) + t • X) Y) 0)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F (x : EuclideanSpace ℝ (Fin m)) Z) =
      h.inner x ((metricCov (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (M := U) h)
        (fun _ : U => Y) x X) Z

theorem isometricImmersionPullbackConnection_iff_secondFundamentalForm_orthogonal
    (g : SmoothRiemannianMetric I M) (F : EuclideanSpace ℝ (Fin m) → M)
    (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin m)))
    (h : SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) U)
    (hinduced : ∀ (x : U) (X Y : EuclideanSpace ℝ (Fin m)),
      h.inner x X Y = g.inner (F x)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F (x : EuclideanSpace ℝ (Fin m)) X)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F (x : EuclideanSpace ℝ (Fin m)) Y)) :
    IsometricImmersionPullbackConnection g F U h ↔
      ∀ (x : U) (X Y Z : EuclideanSpace ℝ (Fin m)),
        g.inner (F x)
          ((show TangentSpace I (F (x : EuclideanSpace ℝ (Fin m))) from
              covDerivAlong (I := I) g (fun t : ℝ => F ((x : EuclideanSpace ℝ (Fin m)) + t • X))
                (fun t : ℝ => mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F
                  ((x : EuclideanSpace ℝ (Fin m)) + t • X) Y) 0) -
            mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F (x : EuclideanSpace ℝ (Fin m))
              ((metricCov (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (M := U) h)
                (fun _ : U => Y) x X))
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F (x : EuclideanSpace ℝ (Fin m)) Z) = 0 := by
  constructor
  · intro hpc x X Y Z
    have hx := hpc x X Y Z
    have hsub := hinduced x
      ((metricCov (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (M := U) h) (fun _ : U => Y) x X) Z
    rw [map_sub, sub_apply, hx, hsub, sub_self]
  · intro horth x X Y Z
    have hz := horth x X Y Z
    have hsub := hinduced x
      ((metricCov (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (M := U) h) (fun _ : U => Y) x X) Z
    rw [map_sub, sub_apply] at hz
    rw [hsub]
    exact sub_eq_zero.mp hz

end DifferentialGeometry.Geometry
