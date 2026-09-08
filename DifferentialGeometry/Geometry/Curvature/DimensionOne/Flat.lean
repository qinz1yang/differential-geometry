import DifferentialGeometry.Geometry.Curvature.CoordRm04Bridge

set_option autoImplicit false

noncomputable section

open Bundle DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [T2Space M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module Real (V x)]
  [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul Real (V x)]
  [FiberBundle F V] [VectorBundle Real F V] [ContMDiffVectorBundle ∞ F V I]
  [FiniteDimensional Real F]

theorem riemannOp_eq_zero_of_finrank_le_one [BoundarylessManifold I M]
    (cov : CovariantDerivative I F V)
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hE : Module.finrank Real E ≤ 1)
    (x : M) (v w : TangentSpace I x) (u : V x) :
    riemannOp cov x v w u = 0 := by
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  obtain ⟨b, hb⟩ := (finrank_le_one_iff (K := Real) (V := TangentSpace I x)).mp hE
  obtain ⟨c, rfl⟩ := hb v
  obtain ⟨d, rfl⟩ := hb w
  have hself : riemannOp cov x b b u = 0 := by
    have hs := riemannOp_swap cov x b b u
    have htwo : (2 : Real) • riemannOp cov x b b u = 0 := by
      rw [two_smul]
      nth_rewrite 1 [hs]
      abel
    exact (smul_eq_zero.mp htwo).resolve_left two_ne_zero
  rw [(riemannOp cov x).map_smul,
    smul_apply,
    (riemannOp cov x b).map_smul]
  simp only [smul_apply, hself, smul_zero]

variable [I.Boundaryless]

theorem metricRm04At_eq_zero_of_finrank_le_one
    (g : SmoothRiemannianMetric I M) (hE : Module.finrank Real E ≤ 1) (x : M) :
    metricRm04At (I := I) g x = 0 := by
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  ext v
  have hv : v = vec4 (I := I) (v 0) (v 1) (v 2) (v 3) := by
    ext i
    fin_cases i <;> rfl
  rw [hv]
  change metricRm04StdAt (I := I) g x (v 0) (v 1) (v 2) (v 3) = 0
  rw [DifferentialGeometry.rm04_eq_inner_riem,
    riemannOp_eq_zero_of_finrank_le_one (LeviCivita g) hE, map_zero]

theorem metricScalarAt_eq_zero_of_finrank_le_one
    (g : SmoothRiemannianMetric I M) (hE : Module.finrank Real E ≤ 1) (x : M) :
    metricScalarAt (I := I) g x = 0 :=
  metricScalarAt_eq_zero_of_metricRm04At_eq_zero g x
    (metricRm04At_eq_zero_of_finrank_le_one g hE x)

end DifferentialGeometry.Geometry.Curvature
