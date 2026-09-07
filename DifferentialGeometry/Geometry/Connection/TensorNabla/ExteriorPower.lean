import DifferentialGeometry.Geometry.Metric.ExteriorPowerDualityBundle
import DifferentialGeometry.Geometry.Connection.TensorNabla.Alternating
import DifferentialGeometry.Geometry.Connection.Trivial

noncomputable section

open Bundle
open scoped Bundle Manifold ContDiff

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]

private instance alternatingFiniteDimensional (k : ℕ) :
    FiniteDimensional ℝ (F [⋀^Fin k]→L[ℝ] ℝ) :=
  (ContinuousAlternatingMap.elementaryCovectorBasis (k := k)
    (Module.finBasis ℝ F)).finiteDimensional_of_finite

def exteriorPower (cov : CovariantDerivative I F V) (k : ℕ) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI := Bundle.ExteriorPower.totalSpaceTopology F V k
    letI := Bundle.ExteriorPower.fiberBundle F V k
    letI := Bundle.ExteriorPower.vector_bundle F V k
    CovariantDerivative I (⋀[ℝ]^k F) (fun x => ⋀[ℝ]^k (V x)) := by
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let := Bundle.ExteriorPower.totalSpaceTopology F V k
  let := Bundle.ExteriorPower.fiberBundle F V k
  let := Bundle.ExteriorPower.vector_bundle F V k
  exact pullbackFiberwiseLinearEquiv
    (fun x => (_root_.exteriorPower.alternatingDualEquiv (E := V x) k).toLinearEquiv)
    (Bundle.ExteriorPower.contMDiff_alternatingDualEquiv_map (IB := I) F V k 1)
    (DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen I M
      (F [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial M ℝ))
      ℝ (Bundle.Trivial M ℝ) (alternating cov k) (trivial I M ℝ))

theorem exteriorPower_apply (cov : CovariantDerivative I F V) (k : ℕ)
    (u : ∀ x, ⋀[ℝ]^k (V x)) (x : M) (X : TangentSpace I x) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI := Bundle.ExteriorPower.totalSpaceTopology F V k
    letI := Bundle.ExteriorPower.fiberBundle F V k
    letI := Bundle.ExteriorPower.vector_bundle F V k
    exteriorPower cov k u x X =
      (_root_.exteriorPower.alternatingDualEquiv k).symm
        (DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen I M
          (F [⋀^Fin k]→L[ℝ] ℝ)
          (Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial M ℝ))
          ℝ (Bundle.Trivial M ℝ) (alternating cov k) (trivial I M ℝ)
          (fun y => _root_.exteriorPower.alternatingDualEquiv k (u y)) x X) := by
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let := Bundle.ExteriorPower.totalSpaceTopology F V k
  let := Bundle.ExteriorPower.fiberBundle F V k
  let := Bundle.ExteriorPower.vector_bundle F V k
  exact pullbackFiberwiseLinearEquiv_apply _
    (Bundle.ExteriorPower.contMDiff_alternatingDualEquiv_map (IB := I) F V k 1) _ u x X

theorem exteriorPower_contMDiff (cov : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov ∞] (k : ℕ) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI := Bundle.ExteriorPower.totalSpaceTopology F V k
    letI := Bundle.ExteriorPower.fiberBundle F V k
    letI := Bundle.ExteriorPower.vector_bundle F V k
    ContMDiffCovariantDerivative (exteriorPower cov k) ∞ := by
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let := Bundle.ExteriorPower.totalSpaceTopology F V k
  let := Bundle.ExteriorPower.fiberBundle F V k
  let := Bundle.ExteriorPower.vector_bundle F V k
  exact ContMDiffCovariantDerivative.pullbackFiberwiseLinearEquiv _
    (Bundle.ExteriorPower.contMDiff_alternatingDualEquiv_map (IB := I) F V k ∞)
    (Bundle.ExteriorPower.contMDiff_alternatingDualEquiv_symm_map (IB := I) F V k ∞) _

theorem exteriorPower_ιMulti (cov : CovariantDerivative I F V) (k : ℕ)
    (Y : Fin k → ∀ x, V x) {x : M}
    (hY : ∀ i, MDifferentiableAt I (I.prod 𝓘(ℝ, F))
      (fun y => (⟨y, Y i y⟩ : TotalSpace F V)) x) (X : TangentSpace I x) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI := Bundle.ExteriorPower.totalSpaceTopology F V k
    letI := Bundle.ExteriorPower.fiberBundle F V k
    letI := Bundle.ExteriorPower.vector_bundle F V k
    exteriorPower cov k (fun y => _root_.exteriorPower.ιMulti ℝ k (fun i => Y i y)) x X =
      ∑ i, _root_.exteriorPower.ιMulti ℝ k
        (Function.update (fun j => Y j x) i (cov (Y i) x X)) := by
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let := Bundle.ExteriorPower.totalSpaceTopology F V k
  let := Bundle.ExteriorPower.fiberBundle F V k
  let := Bundle.ExteriorPower.vector_bundle F V k
  classical
  apply (_root_.exteriorPower.alternatingDualEquiv k).injective
  rw [exteriorPower_apply, ContinuousLinearEquiv.apply_symm_apply, map_sum]
  apply ContinuousLinearMap.ext
  intro a
  obtain ⟨A, hA⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := F [⋀^Fin k]→L[ℝ] ℝ)
    (V := Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial M ℝ))
    (n := (⊤ : ℕ∞)) x a
  obtain ⟨Z, hZ⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := TangentSpace I) (n := (⊤ : ℕ∞)) x X
  rw [← hA, ← hZ]
  have hu := Bundle.ExteriorPower.mdifferentiableAt_ιMulti (IB := I) F V k Y hY
  have hmap := Bundle.ExteriorPower.contMDiff_alternatingDualEquiv_map (IB := I) F V k 1
  have hd := (hmap.mdifferentiableAt one_ne_zero).comp x hu
  rw [DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen_apply_of_mdifferentiableAt
    I M (F [⋀^Fin k]→L[ℝ] ℝ)
    (Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial M ℝ))
    ℝ (Bundle.Trivial M ℝ) (alternating cov k) (trivial I M ℝ)
    _ hd Z.mdifferentiableAt A.mdifferentiableAt]
  simp only [_root_.exteriorPower.alternatingDualEquiv_ιMulti_apply, sum_apply]
  rw [alternating_apply_of_mdifferentiableAt cov k Y A.mdifferentiableAt hY]
  change mvfderiv (I := I) (fun y => A y (fun i => Y i y)) x (Z x) -
      (mvfderiv (I := I) (fun y => A y (fun i => Y i y)) x (Z x) -
        ∑ i, A x (Function.update (fun j => Y j x) i (cov (Y i) x (Z x)))) = _
  abel

theorem exteriorPower_alternatingDualEquiv_apply
    (cov : CovariantDerivative I F V) (k : ℕ)
    (u : ∀ x, ⋀[ℝ]^k (V x)) (a : ∀ x, V x [⋀^Fin k]→L[ℝ] ℝ)
    (x : M) (X : TangentSpace I x)
    (ha : MDifferentiableAt I (I.prod 𝓘(ℝ, F [⋀^Fin k]→L[ℝ] ℝ))
      (fun y => (⟨y, a y⟩ : TotalSpace (F [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial M ℝ)))) x) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI := Bundle.ExteriorPower.totalSpaceTopology F V k
    letI := Bundle.ExteriorPower.fiberBundle F V k
    letI := Bundle.ExteriorPower.vector_bundle F V k
    MDifferentiableAt I (I.prod 𝓘(ℝ, ⋀[ℝ]^k F))
      (fun y => (⟨y, u y⟩ : TotalSpace (⋀[ℝ]^k F) (fun z => ⋀[ℝ]^k (V z)))) x →
      _root_.exteriorPower.alternatingDualEquiv k (cov.exteriorPower k u x X) (a x) =
        mvfderiv (I := I)
          (fun y => _root_.exteriorPower.alternatingDualEquiv k (u y) (a y)) x X -
            _root_.exteriorPower.alternatingDualEquiv k (u x)
              (CovariantDerivative.alternating cov k a x X) := by
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let := Bundle.ExteriorPower.totalSpaceTopology F V k
  let := Bundle.ExteriorPower.fiberBundle F V k
  let := Bundle.ExteriorPower.vector_bundle F V k
  intro hu
  have heval := Bundle.ExteriorPower.contMDiff_alternatingDualEquiv_map (IB := I) F V k 1
  have heu := (heval.mdifferentiableAt one_ne_zero).comp x hu
  obtain ⟨Z, hZ⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := TangentSpace I) (n := (⊤ : ℕ∞)) x X
  rw [← hZ, exteriorPower_apply, ContinuousLinearEquiv.apply_symm_apply]
  exact DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen_apply_of_mdifferentiableAt
    I M (F [⋀^Fin k]→L[ℝ] ℝ)
    (Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial M ℝ))
    ℝ (Bundle.Trivial M ℝ) (CovariantDerivative.alternating cov k) (trivial I M ℝ)
    _ heu Z.mdifferentiableAt ha

end CovariantDerivative
