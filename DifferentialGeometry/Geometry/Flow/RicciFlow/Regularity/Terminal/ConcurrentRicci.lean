import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ConcurrentKernelHessian
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.IntrinsicDerivation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Equation.Lichnerowicz

set_option autoImplicit false
noncomputable section
open Bundle Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [T2Space M] in
private theorem tensor_eval_update_basis {J : Type*} [Fintype J] {n : ℕ} {x : M}
    (b : Module.Basis J ℝ (TangentSpace I x))
    (T : Tensor0SSpace n I x) (m : Fin n → TangentSpace I x) (a : Fin n)
    (v : TangentSpace I x) :
    T (Function.update m a v) =
      ∑ j, b.coord j v * T (Function.update m a (b j)) := by
  classical
  calc
    T (Function.update m a v) =
        (T.toMultilinearMap.toLinearMap m a) (∑ j, b.repr v j • b j) := by
      rw [b.sum_repr]
      rfl
    _ = _ := by
      simp only [map_sum, map_smul, MultilinearMap.toLinearMap_apply,
        smul_eq_mul, Module.Basis.coord_apply]
      rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] [T2Space M] in
private theorem tensor02_second_basis {J : Type*} [Fintype J] {x : M}
    (b : Module.Basis J ℝ (TangentSpace I x)) (T : Tensor0SSpace 2 I x)
    (u v : TangentSpace I x) :
    T (vec2 u v) = ∑ j, b.coord j v * T (vec2 u (b j)) := by
  have hu (w : TangentSpace I x) : Function.update (vec2 u 0) (1 : Fin 2) w = vec2 u w := by
    funext i
    fin_cases i <;> rfl
  simpa only [hu] using tensor_eval_update_basis b T (vec2 u 0) 1 v

omit [FiniteDimensional ℝ E] [CompleteSpace E] [T2Space M] in
private theorem tensor04_third_basis {J : Type*} [Fintype J] {x : M}
    (b : Module.Basis J ℝ (TangentSpace I x)) (T : Tensor0SSpace 4 I x)
    (u v w z : TangentSpace I x) :
    T (vec4 u v w z) = ∑ j, b.coord j w * T (vec4 u v (b j) z) := by
  have hu (a : TangentSpace I x) :
      Function.update (vec4 u v 0 z) (2 : Fin 4) a = vec4 u v a z := by
    funext i
    fin_cases i <;> rfl
  simpa only [hu] using tensor_eval_update_basis b T (vec4 u v 0 z) 2 w

omit [FiniteDimensional ℝ E] [CompleteSpace E] [T2Space M] in
private theorem tensor04_last_basis {J : Type*} [Fintype J] {x : M}
    (b : Module.Basis J ℝ (TangentSpace I x)) (T : Tensor0SSpace 4 I x)
    (u v w z : TangentSpace I x) :
    T (vec4 u v w z) = ∑ j, b.coord j z * T (vec4 u v w (b j)) := by
  have hu (a : TangentSpace I x) :
      Function.update (vec4 u v w 0) (3 : Fin 4) a = vec4 u v w a := by
    funext i
    fin_cases i <;> rfl
  simpa only [hu] using tensor_eval_update_basis b T (vec4 u v w 0) 3 z

private theorem sum_pair_exchange {J : Type*} [Fintype J] (f : J → J → J → J → ℝ) :
    (∑ i, ∑ j, ∑ a, ∑ b, f i j a b) = ∑ a, ∑ b, ∑ i, ∑ j, f i j a b := by
  calc
    _ = ∑ i, ∑ a, ∑ j, ∑ b, f i j a b := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ a, ∑ i, ∑ j, ∑ b, f i j a b := by rw [Finset.sum_comm]
    _ = ∑ a, ∑ b, ∑ i, ∑ j, f i j a b := by
      apply Finset.sum_congr rfl
      intro a _
      calc
        _ = ∑ i, ∑ b, ∑ j, f i j a b := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_comm]
        _ = _ := by rw [Finset.sum_comm]

theorem coordNab2Ric_eq_metricNabla2Ric
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (x : M) (t : ℝ) (a b i j : CoordinateIdx (𝕜 := ℝ) E) :
    coordNab2Ric S x t x a b i j = metricNabla2Ric (S.base.metric t) x
      (vec4 (coordinateFrameAt (I := I) x a x) (coordinateFrameAt (I := I) x b x)
        (coordinateFrameAt (I := I) x i x) (coordinateFrameAt (I := I) x j x)) := by
  rw [coordNab2Ric_eq_nabla2RicField S x t a b i j]
  rfl

theorem ricciPairRHS_concurrent
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (t : ℝ)
    (Z : ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) {x : M}
    (hZ : ∀ᶠ y in 𝓝 x, ∀ v : TangentSpace I y,
      metricCov (S.base.metric t) Z y v = v) :
    ricciPairRHS S t x (Z x) (Z x) = 2 * metricScalarAt (S.base.metric t) x := by
  classical
  let b := coordinateFrameAtToBasis (I := I) x
  let c : CoordinateIdx (𝕜 := ℝ) E → ℝ := fun i => b.coord i (Z x)
  let frame := coordinateFrameAt (I := I) x
  let G := coordInv S x
  let R := rmRicciContractionCompInFrame S S.base.rm04 G frame t x
  let Q := ricciQuadraticCompInFrame S G frame t x
  let L := coordRoughRic S x (coordNab2Ric S x) t x
  have hframe (i) : frame i x = b i :=
    (coordinateFrameAt_toBasis_apply (I := I) x i).symm
  have hRic (i j) : ricciCompInFrame S frame t x i j =
      metricRicciAt (S.base.metric t) x (vec2 (b i) (b j)) := by
    change metricRicciAt (S.base.metric t) x (vec2 (frame i x) (frame j x)) = _
    rw [hframe, hframe]
  have hRm (i k j l) : rm04Comp (S.base.rm04 t) frame x i k j l =
      metricRm04At (S.base.metric t) x (vec4 (b i) (b k) (b j) (b l)) := by
    change metricRm04At (S.base.metric t) x
      (vec4 (frame i x) (frame k x) (frame j x) (frame l x)) = _
    rw [hframe, hframe, hframe, hframe]
  have hRicRow (k) : (∑ j, c j * ricciCompInFrame S frame t x k j) = 0 := by
    simp_rw [hRic]
    rw [← tensor02_second_basis b (metricRicciAt (S.base.metric t) x) (b k) (Z x)]
    exact metricRicci_concurrent_eq_zero (S.base.metric t) Z hZ (b k)
  have hRmRow (i k l) : (∑ j, c j * rm04Comp (S.base.rm04 t) frame x i k j l) = 0 := by
    simp_rw [hRm]
    rw [← tensor04_third_basis b (metricRm04At (S.base.metric t) x) (b i) (b k) (Z x) (b l)]
    exact metricRm04_concurrent_eq_zero (S.base.metric t) Z hZ (b i) (b k) (b l)
  have hR (i) : (∑ j, c j * R i j) = 0 := by
    change (∑ j, c j * ∑ k, ∑ l, rm04Comp (S.base.rm04 t) frame x i k j l *
      raisedRicciCompInFrame S G frame t x k l) = 0
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro k _
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro l _
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul, hRmRow, zero_mul]
  have hQ (i) : (∑ j, c j * Q i j) = 0 := by
    change (∑ j, c j * ∑ k, ricciOneUpCompInFrame S G frame t x i k *
      ricciCompInFrame S frame t x k j) = 0
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro k _
    have hmove (j) : c j * (ricciOneUpCompInFrame S G frame t x i k *
        ricciCompInFrame S frame t x k j) =
        ricciOneUpCompInFrame S G frame t x i k *
          (c j * ricciCompInFrame S frame t x k j) := by ring
    simp_rw [hmove]
    rw [← Finset.mul_sum, hRicRow, mul_zero]
  have hHess (a d) :
      (∑ i, ∑ j, c i * c j * coordNab2Ric S x t x a d i j) =
        metricNabla2Ric (S.base.metric t) x (vec4 (b a) (b d) (Z x) (Z x)) := by
    symm
    calc
      _ = ∑ i, c i * metricNabla2Ric (S.base.metric t) x
          (vec4 (b a) (b d) (b i) (Z x)) :=
        tensor04_third_basis b _ (b a) (b d) (Z x) (Z x)
      _ = ∑ i, ∑ j, c i * c j * metricNabla2Ric (S.base.metric t) x
          (vec4 (b a) (b d) (b i) (b j)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [tensor04_last_basis b _ (b a) (b d) (b i) (Z x)]
        simp only [Finset.mul_sum, mul_assoc, c]
      _ = _ := by
        simp only [coordNab2Ric_eq_metricNabla2Ric, b, coordinateFrameAt_toBasis_apply]
  have hL : (∑ i, ∑ j, c i * c j * L i j) =
      2 * metricScalarAt (S.base.metric t) x := by
    change (∑ i, ∑ j, c i * c j * ∑ a, ∑ d,
      G t x a d * coordNab2Ric S x t x a d i j) = _
    simp_rw [Finset.mul_sum]
    rw [sum_pair_exchange]
    have heq : (∑ a, ∑ d, ∑ i, ∑ j,
        c i * c j * (G t x a d * coordNab2Ric S x t x a d i j)) =
        ∑ a, ∑ d, G t x a d *
          (∑ i, ∑ j, c i * c j * coordNab2Ric S x t x a d i j) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [heq]
    simp_rw [hHess]
    exact trace_metricNabla2Ric_concurrent (S.base.metric t) Z hZ b (G t x)
      (coordInvReal S x t)
  have hRpair : (∑ i, ∑ j, c i * c j * R i j) = 0 := by
    calc
      _ = ∑ i, c i * (∑ j, c j * R i j) := by simp only [Finset.mul_sum, mul_assoc]
      _ = 0 := by simp only [hR, mul_zero, Finset.sum_const_zero]
  have hQpair : (∑ i, ∑ j, c i * c j * Q i j) = 0 := by
    calc
      _ = ∑ i, c i * (∑ j, c j * Q i j) := by simp only [Finset.mul_sum, mul_assoc]
      _ = 0 := by simp only [hQ, mul_zero, Finset.sum_const_zero]
  change (∑ i, ∑ j, c i * c j * (L i j - 2 * R i j - 2 * Q i j)) = _
  have heval (i j) : c i * c j * (L i j - 2 * R i j - 2 * Q i j) =
      c i * c j * L i j - 2 * (c i * c j * R i j) - 2 * (c i * c j * Q i j) := by ring
  simp_rw [heval, Finset.sum_sub_distrib]
  have htwo (A : CoordinateIdx (𝕜 := ℝ) E → CoordinateIdx (𝕜 := ℝ) E → ℝ) :
      (∑ i, ∑ j, 2 * (c i * c j * A i j)) =
        2 * (∑ i, ∑ j, c i * c j * A i j) := by
    simp only [Finset.mul_sum]
  rw [htwo, htwo, hL, hRpair, hQpair]
  ring

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
