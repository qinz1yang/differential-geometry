import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.PulledCurvatureEvolution
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorNormalization

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {V : M → Type*} [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]

theorem riemann_pullback_trace_normalized_components_hasDerivWithinAt_of_ricci_ode
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (t : D.RegularTime)
    (ι : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x) {J : Set ℝ}
    (hι : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) 1
      (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι t x).toContinuousLinearMap))
    (x : M) (hode : ∀ v, HasDerivWithinAt (fun s => ι s x v)
      (ricciSharp (I := I) (S.family.metric t) x (ι t x v)) J t)
    (h : V x →L[ℝ] V x →L[ℝ] ℝ)
    (hmetric : ∀ v w, (S.family.metric t).inner x (ι t x v) (ι t x w) = h v w)
    (b : Module.Basis (Fin 3) ℝ (V x))
    (horth : ∀ i j, h (b i) (b j) = delta3 i j) (i j : Fin 3) :
    let m : Fin 4 → Fin 3 :=
      ![(bivectorIndex3 i).1, (bivectorIndex3 i).2,
        (bivectorIndex3 j).2, (bivectorIndex3 j).1]
    let A := fun p q => 2 * S.base.rm04 t x
      (vec4 (ι t x (b (bivectorIndex3 p).1)) (ι t x (b (bivectorIndex3 p).2))
        (ι t x (b (bivectorIndex3 q).2)) (ι t x (b (bivectorIndex3 q).1)))
    HasDerivWithinAt (fun s => 2 * S.base.rm04 s x (fun q => ι s x (b (m q))))
      (2 * (rawBundleConnLap (S.family.metric t)
          (CovariantDerivative.multilinear
            (CovariantDerivative.pullbackFiberwiseLinearEquiv
              (fun y => (ι t y).toLinearEquiv) hι.clm_bundle_map
              (LeviCivita (S.family.metric t))) 4)
          (fun y => (S.base.rm04 t y).compContinuousLinearMap
            (fun _ => (ι t y).toContinuousLinearMap)) x) (fun q => b (m q)) +
        curvatureOperatorReaction3 A i j) J t := by
  let R := fun a b' c d => S.base.rm04 t x
    (vec4 (ι t x (b a)) (ι t x (b b')) (ι t x (b c)) (ι t x (b d)))
  have hform := mem_algebraicCurvatureTensorSubmodule.mp
    (metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) (S.base.metric t) x)
  have hR : AlgebraicCurvatureSymmetries3 R := by
    refine ⟨?_, ?_, ?_⟩
    · intro a b' c d
      exact hform.anti_first (ι t x (b b')) (ι t x (b a))
        (ι t x (b c)) (ι t x (b d))
    · intro a b' c d
      exact hform.anti_last (ι t x (b a)) (ι t x (b b'))
        (ι t x (b d)) (ι t x (b c))
    · intro a b' c d
      exact hform.pair_swap (ι t x (b c)) (ι t x (b d))
        (ι t x (b a)) (ι t x (b b'))
  have hinv : ∀ i j,
      (∑ k, delta3 i k * h (b k) (b j)) = (if i = j then 1 else 0) ∧
      (∑ k, h (b i) (b k) * delta3 k j) = (if i = j then 1 else 0) := by
    intro i j
    simp [horth, delta3]
  let m : Fin 4 → Fin 3 :=
    ![(bivectorIndex3 i).1, (bivectorIndex3 i).2,
      (bivectorIndex3 j).2, (bivectorIndex3 j).1]
  have hd := (riemann_pullback_components_hasDerivWithinAt_laplacian_of_ricci_ode
    S hS t ι hι x hode h hmetric b delta3 hinv m).const_mul 2
  have hreaction := curvatureOperatorReaction3_apply_eq_negative_b_comp R hR i j
  apply hd.congr_deriv
  dsimp only at hreaction ⊢
  rw [hreaction]
  dsimp [m]
  ring

end DifferentialGeometry.PDE.RicciFlow
