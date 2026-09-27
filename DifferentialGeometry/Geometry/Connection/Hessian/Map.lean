import DifferentialGeometry.Geometry.Connection.Laplacian.VectorBundle

set_option autoImplicit false

noncomputable section

open Bundle DifferentialGeometry
open DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff

namespace CovariantDerivative

theorem hessian_map
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
    [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
    [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
    [∀ x, ContinuousSMul ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    {W : M → Type*} [TopologicalSpace (TotalSpace G W)]
    [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)]
    [∀ x, TopologicalSpace (W x)] [∀ x, IsTopologicalAddGroup (W x)]
    [∀ x, ContinuousSMul ℝ (W x)]
    [FiberBundle G W] [VectorBundle ℝ G W] [ContMDiffVectorBundle ∞ G W I]
    (D : CovariantDerivative I F V) (hD : ContMDiffCovariantDerivative D ∞)
    (C : CovariantDerivative I G W) (hC : ContMDiffCovariantDerivative C ∞)
    (φ : ∀ x, V x →ₗ[ℝ] W x)
    (hmap : ∀ (S : ∀ x, V x),
      ContMDiff I (I.prod 𝓘(ℝ, F)) 1 (fun x => TotalSpace.mk' F x (S x)) →
      ∀ (x : M) (X : TangentSpace I x),
        C (fun y => φ y (S y)) x X = φ x (D S x X))
    (base : CovariantDerivative I E (TangentSpace I : M → Type _))
    (R : ∀ x, V x)
    (hR : ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun x => TotalSpace.mk' F x (R x)))
    (hT : ContMDiff I (I.prod 𝓘(ℝ, G)) 2 (fun x => TotalSpace.mk' G x (φ x (R x))))
    (x : M) (X Y : TangentSpace I x) :
    C.hessian base (fun y => φ y (R y)) x X Y = φ x (D.hessian base R x X Y) := by
  obtain ⟨Z, hZ⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x Y
  have hDZ : ContMDiff I (I.prod 𝓘(ℝ, F)) 1
      (fun y => TotalSpace.mk' F y (D R y (Z y))) := by
    intro y
    exact (hD.contMDiffAt (m := 1) (hR y) (by norm_num)).clm_bundle_apply
      (Z.contMDiff.contMDiffAt.of_le (by simp))
  rw [← hZ, hessian_apply_of_contMDiffAt C hC base (hT x) Z.mdifferentiableAt,
    hessian_apply_of_contMDiffAt D hD base (hR x) Z.mdifferentiableAt]
  have hfirst : (fun y => C (fun z => φ z (R z)) y (Z y)) =
      (fun y => φ y (D R y (Z y))) := by
    funext y
    exact hmap R (hR.of_le (by norm_num)) y (Z y)
  rw [hfirst, hmap _ hDZ, hmap R (hR.of_le (by norm_num)), map_sub]

end CovariantDerivative
