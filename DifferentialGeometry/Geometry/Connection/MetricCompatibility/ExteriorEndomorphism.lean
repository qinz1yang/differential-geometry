import DifferentialGeometry.Geometry.Metric.ExteriorEndomorphismBundle
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.ExteriorPower
import DifferentialGeometry.Geometry.Connection.NormalSection

set_option autoImplicit false

noncomputable section

open Bundle
open DifferentialGeometry.HomConnectionGen DifferentialGeometry.Geometry.Connection
open scoped Bundle Manifold ContDiff RealInnerProductSpace BigOperators

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I 1 F V]

theorem IsMetricCompatible.multilinear_endomorphismTensor
    {cov : CovariantDerivative I F V} (hcov : cov.IsMetricCompatible) (k : ℕ) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI := Bundle.ExteriorPower.totalSpaceTopology F V k
    letI := Bundle.ExteriorPower.fiberBundle F V k
    letI := Bundle.ExteriorPower.vector_bundle F V k
    letI := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V k
    let c := cov.exteriorPower k
    let D := homBundleCovariantDerivativeGen I M (⋀[ℝ]^k F) (fun x => ⋀[ℝ]^k (V x))
      (⋀[ℝ]^k F) (fun x => ⋀[ℝ]^k (V x)) c c
    ∀ (R : ∀ x, (⋀[ℝ]^k (V x)) →L[ℝ] ⋀[ℝ]^k (V x)),
    ContMDiff I (I.prod 𝓘(ℝ, (⋀[ℝ]^k F) →L[ℝ] ⋀[ℝ]^k F)) 1
      (fun x => TotalSpace.mk' ((⋀[ℝ]^k F) →L[ℝ] ⋀[ℝ]^k F) x (R x)) →
    ∀ (x : M) (X : TangentSpace I x),
      cov.multilinear (k + k) (fun y => _root_.exteriorPower.endomorphismTensor k (R y)) x X =
        _root_.exteriorPower.endomorphismTensor k (D R x X) := by
  dsimp only
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let := Bundle.ExteriorPower.totalSpaceTopology F V k
  let := Bundle.ExteriorPower.fiberBundle F V k
  let := Bundle.ExteriorPower.vector_bundle F V k
  let := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V k
  let := Bundle.ExteriorPower.isContMDiffRiemannianBundle (IB := I) (n := 1) F V k
  let c := cov.exteriorPower k
  let D := homBundleCovariantDerivativeGen I M (⋀[ℝ]^k F) (fun x => ⋀[ℝ]^k (V x))
    (⋀[ℝ]^k F) (fun x => ⋀[ℝ]^k (V x)) c c
  intro R hR x X
  have hT := Bundle.ExteriorPower.contMDiff_endomorphismTensor (IB := I) (n := 1) F V k R hR
  apply ContinuousMultilinearMap.ext
  intro v
  choose W hW hDW using fun i : Fin (k + k) =>
    exists_section_with_value_and_covariantDerivative_zero cov x (v i)
  obtain ⟨Z, hZ⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x X
  let L (y : M) := _root_.exteriorPower.ιMulti ℝ k (fun i => W (Fin.castAdd k i) y)
  let N (y : M) := _root_.exteriorPower.ιMulti ℝ k (fun i => W (Fin.natAdd k i) y)
  have hL := Bundle.ExteriorPower.mdifferentiableAt_ιMulti (IB := I) (x := x) F V k
    (fun i y => W (Fin.castAdd k i) y) (fun i => (W (Fin.castAdd k i)).mdifferentiableAt)
  have hN := Bundle.ExteriorPower.mdifferentiableAt_ιMulti (IB := I) (x := x) F V k
    (fun i y => W (Fin.natAdd k i) y) (fun i => (W (Fin.natAdd k i)).mdifferentiableAt)
  have hDL : c L x X = 0 := by
    rw [exteriorPower_ιMulti cov k _ (fun i => (W (Fin.castAdd k i)).mdifferentiableAt)]
    simp only [hDW, zero_apply, AlternatingMap.map_update_zero, Finset.sum_const_zero]
  have hDN : c N x X = 0 := by
    rw [exteriorPower_ιMulti cov k _ (fun i => (W (Fin.natAdd k i)).mdifferentiableAt)]
    simp only [hDW, zero_apply, AlternatingMap.map_update_zero, Finset.sum_const_zero]
  have hD := homBundleCovariantDerivativeGen_apply_of_mdifferentiableAt I M
    (⋀[ℝ]^k F) (fun x => ⋀[ℝ]^k (V x))
    (⋀[ℝ]^k F) (fun x => ⋀[ℝ]^k (V x)) c c R
    ((hR x).mdifferentiableAt one_ne_zero) Z.mdifferentiableAt hL
  rw [hZ] at hD
  change D R x X (L x) = c (fun y => R y (L y)) x X - R x (c L x X) at hD
  rw [hDL, map_zero, sub_zero] at hD
  have hInner := (hcov.exteriorPower k).mvfderiv_inner_eq (fun y => Z y)
    (((hR x).mdifferentiableAt one_ne_zero).clm_bundle_apply hL) hN
  change mvfderiv I (fun y => ⟪R y (L y), N y⟫) x (Z x) =
    ⟪c (fun y => R y (L y)) x (Z x), N x⟫ + ⟪R x (L x), c N x (Z x)⟫ at hInner
  rw [hZ, hDN, inner_zero_right, add_zero, ← hD] at hInner
  have hslots : (fun i => W i x) = v := funext hW
  rw [← hslots, multilinear_apply cov (k + k) (fun i y => W i y)
    ((hT x).mdifferentiableAt one_ne_zero) (fun i => (W i).mdifferentiableAt)]
  simp only [hDW, zero_apply, ContinuousMultilinearMap.map_coord_zero _ _
      (Function.update_self _ _ _),
    Finset.sum_const_zero, sub_zero]
  have hfun : (fun y => _root_.exteriorPower.endomorphismTensor k (R y)
      (fun i => W i y)) = (fun y => ⟪R y (L y), N y⟫) := by
    funext y
    exact _root_.exteriorPower.endomorphismTensor_apply k (R y) (fun i => W i y)
  rw [hfun, hInner, _root_.exteriorPower.endomorphismTensor_apply]
  rfl

end CovariantDerivative
