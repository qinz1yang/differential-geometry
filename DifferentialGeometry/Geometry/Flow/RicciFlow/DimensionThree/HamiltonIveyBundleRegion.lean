import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.HamiltonIveyRegionReaction
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.HamiltonIveyIntrinsicRegion

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set
open DifferentialGeometry.Analysis.Convex
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology RealInnerProductSpace BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M]
variable [SigmaCompactSpace M] [T2Space M]

def fiberBivectorTwoForm
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (i : Fin 3) (X Y : TangentSpace I x) : Real :=
  (g.inner x X (basis (bivectorIndex3 i).1)) * (g.inner x Y (basis (bivectorIndex3 i).2)) -
    (g.inner x X (basis (bivectorIndex3 i).2)) * (g.inner x Y (basis (bivectorIndex3 i).1))

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
private lemma fiberBivectorTwoForm_add_left
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (p : Fin 3) (x₁ x₂ y : TangentSpace I x) :
    fiberBivectorTwoForm g basis p (x₁ + x₂) y =
      fiberBivectorTwoForm g basis p x₁ y + fiberBivectorTwoForm g basis p x₂ y := by
  unfold fiberBivectorTwoForm
  rw [(g.inner x).map_add x₁ x₂]
  simp
  ring

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
private lemma fiberBivectorTwoForm_add_right
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (p : Fin 3) (X y₁ y₂ : TangentSpace I x) :
    fiberBivectorTwoForm g basis p X (y₁ + y₂) =
      fiberBivectorTwoForm g basis p X y₁ + fiberBivectorTwoForm g basis p X y₂ := by
  unfold fiberBivectorTwoForm
  rw [(g.inner x).map_add y₁ y₂]
  simp
  ring

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
private lemma fiberBivectorTwoForm_smul_left
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (p : Fin 3) (a : ℝ) (x₁ y : TangentSpace I x) :
    fiberBivectorTwoForm g basis p (a • x₁) y = a * fiberBivectorTwoForm g basis p x₁ y := by
  unfold fiberBivectorTwoForm
  rw [(g.inner x).map_smul a x₁]
  simp
  ring

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
private lemma fiberBivectorTwoForm_smul_right
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (p : Fin 3) (a : ℝ) (X y₁ : TangentSpace I x) :
    fiberBivectorTwoForm g basis p X (a • y₁) = a * fiberBivectorTwoForm g basis p X y₁ := by
  unfold fiberBivectorTwoForm
  rw [(g.inner x).map_smul a y₁]
  simp
  ring

noncomputable def fiberOperatorTensor
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (Rmat : Matrix (Fin 3) (Fin 3) ℝ) : Tensor04At (I := I) (M := M) x :=
  { toMultilinearMap := MultilinearMap.mk' (R := ℝ) (M₁ := fun _ : Fin 4 => TangentSpace I x) (M₂ := ℝ)
      (fun m : Fin 4 → TangentSpace I x =>
        ∑ p : Fin 3, ∑ q : Fin 3,
          Rmat p q * fiberBivectorTwoForm g basis p (m 0) (m 1) *
            fiberBivectorTwoForm g basis q (m 3) (m 2))
      (by
        intro m i x y
        fin_cases i
        · change (∑ p : Fin 3, ∑ q : Fin 3,
              Rmat p q * fiberBivectorTwoForm g basis p (x + y) (m 1) *
                fiberBivectorTwoForm g basis q (m 3) (m 2)) =
            (∑ p : Fin 3, ∑ q : Fin 3,
              Rmat p q * fiberBivectorTwoForm g basis p x (m 1) *
                fiberBivectorTwoForm g basis q (m 3) (m 2)) +
              (∑ p : Fin 3, ∑ q : Fin 3,
                Rmat p q * fiberBivectorTwoForm g basis p y (m 1) *
                  fiberBivectorTwoForm g basis q (m 3) (m 2))
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro p hp
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro q hq
          rw [fiberBivectorTwoForm_add_left]
          ring
        · change (∑ p : Fin 3, ∑ q : Fin 3,
              Rmat p q * fiberBivectorTwoForm g basis p (m 0) (x + y) *
                fiberBivectorTwoForm g basis q (m 3) (m 2)) =
            (∑ p : Fin 3, ∑ q : Fin 3,
              Rmat p q * fiberBivectorTwoForm g basis p (m 0) x *
                fiberBivectorTwoForm g basis q (m 3) (m 2)) +
              (∑ p : Fin 3, ∑ q : Fin 3,
                Rmat p q * fiberBivectorTwoForm g basis p (m 0) y *
                  fiberBivectorTwoForm g basis q (m 3) (m 2))
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro p hp
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro q hq
          rw [fiberBivectorTwoForm_add_right]
          ring
        · change (∑ p : Fin 3, ∑ q : Fin 3,
              Rmat p q * fiberBivectorTwoForm g basis p (m 0) (m 1) *
                fiberBivectorTwoForm g basis q (m 3) (x + y)) =
            (∑ p : Fin 3, ∑ q : Fin 3,
              Rmat p q * fiberBivectorTwoForm g basis p (m 0) (m 1) *
                fiberBivectorTwoForm g basis q (m 3) x) +
              (∑ p : Fin 3, ∑ q : Fin 3,
                Rmat p q * fiberBivectorTwoForm g basis p (m 0) (m 1) *
                  fiberBivectorTwoForm g basis q (m 3) y)
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro p hp
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro q hq
          rw [fiberBivectorTwoForm_add_right]
          ring
        · change (∑ p : Fin 3, ∑ q : Fin 3,
              Rmat p q * fiberBivectorTwoForm g basis p (m 0) (m 1) *
                fiberBivectorTwoForm g basis q (x + y) (m 2)) =
            (∑ p : Fin 3, ∑ q : Fin 3,
              Rmat p q * fiberBivectorTwoForm g basis p (m 0) (m 1) *
                fiberBivectorTwoForm g basis q x (m 2)) +
              (∑ p : Fin 3, ∑ q : Fin 3,
                Rmat p q * fiberBivectorTwoForm g basis p (m 0) (m 1) *
                  fiberBivectorTwoForm g basis q y (m 2))
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro p hp
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro q hq
          rw [fiberBivectorTwoForm_add_left]
          ring)
      (by
        intro m i c x
        fin_cases i
        · change (∑ p : Fin 3, ∑ q : Fin 3,
              Rmat p q * fiberBivectorTwoForm g basis p (c • x) (m 1) *
                fiberBivectorTwoForm g basis q (m 3) (m 2)) =
            c * (∑ p : Fin 3, ∑ q : Fin 3,
              Rmat p q * fiberBivectorTwoForm g basis p x (m 1) *
                fiberBivectorTwoForm g basis q (m 3) (m 2))
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro p hp
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro q hq
          rw [fiberBivectorTwoForm_smul_left]
          ring
        · change (∑ p : Fin 3, ∑ q : Fin 3,
              Rmat p q * fiberBivectorTwoForm g basis p (m 0) (c • x) *
                fiberBivectorTwoForm g basis q (m 3) (m 2)) =
            c * (∑ p : Fin 3, ∑ q : Fin 3,
              Rmat p q * fiberBivectorTwoForm g basis p (m 0) x *
                fiberBivectorTwoForm g basis q (m 3) (m 2))
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro p hp
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro q hq
          rw [fiberBivectorTwoForm_smul_right]
          ring
        · change (∑ p : Fin 3, ∑ q : Fin 3,
              Rmat p q * fiberBivectorTwoForm g basis p (m 0) (m 1) *
                fiberBivectorTwoForm g basis q (m 3) (c • x)) =
            c * (∑ p : Fin 3, ∑ q : Fin 3,
              Rmat p q * fiberBivectorTwoForm g basis p (m 0) (m 1) *
                fiberBivectorTwoForm g basis q (m 3) x)
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro p hp
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro q hq
          rw [fiberBivectorTwoForm_smul_right]
          ring
        · change (∑ p : Fin 3, ∑ q : Fin 3,
              Rmat p q * fiberBivectorTwoForm g basis p (m 0) (m 1) *
                fiberBivectorTwoForm g basis q (c • x) (m 2)) =
            c * (∑ p : Fin 3, ∑ q : Fin 3,
              Rmat p q * fiberBivectorTwoForm g basis p (m 0) (m 1) *
                fiberBivectorTwoForm g basis q x (m 2))
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro p hp
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro q hq
          rw [fiberBivectorTwoForm_smul_left]
          ring)
    cont := by
      unfold fiberBivectorTwoForm
      fun_prop }

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
theorem fiberOperatorTensor_apply
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (Rmat : Matrix (Fin 3) (Fin 3) ℝ) (X Y Z W : TangentSpace I x) :
    tensor04StdAt (I := I) (M := M) (fiberOperatorTensor g basis Rmat) X Y Z W =
      ∑ p : Fin 3, ∑ q : Fin 3,
        Rmat p q * fiberBivectorTwoForm g basis p X Y * fiberBivectorTwoForm g basis q W Z := by
  unfold tensor04StdAt fiberOperatorTensor
  change (∑ p : Fin 3, ∑ q : Fin 3,
      Rmat p q * fiberBivectorTwoForm g basis p (vec4 X Y Z W 0) (vec4 X Y Z W 1) *
        fiberBivectorTwoForm g basis q (vec4 X Y Z W 3) (vec4 X Y Z W 2)) =
    ∑ p : Fin 3, ∑ q : Fin 3,
      Rmat p q * fiberBivectorTwoForm g basis p X Y * fiberBivectorTwoForm g basis q W Z
  simp [vec4]

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
theorem fiberOperatorTensor_apply_basis
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : ∀ i j : Fin 3, (g.inner x (basis i) (basis j)) = if i = j then 1 else 0)
    (Rmat : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) :
    tensor04StdAt (I := I) (M := M) (fiberOperatorTensor g basis Rmat)
        (basis (bivectorIndex3 i).1) (basis (bivectorIndex3 i).2)
        (basis (bivectorIndex3 j).2) (basis (bivectorIndex3 j).1) =
      Rmat i j := by
  classical
  rw [fiberOperatorTensor_apply]
  have hα : ∀ p : Fin 3, fiberBivectorTwoForm g basis p
      (basis (bivectorIndex3 i).1) (basis (bivectorIndex3 i).2) = if p = i then 1 else 0 := by
    intro p
    unfold fiberBivectorTwoForm
    fin_cases p <;> fin_cases i <;> simp [bivectorIndex3, horth]
  have hβ : ∀ q : Fin 3, fiberBivectorTwoForm g basis q
      (basis (bivectorIndex3 j).1) (basis (bivectorIndex3 j).2) = if q = j then 1 else 0 := by
    intro q
    unfold fiberBivectorTwoForm
    fin_cases q <;> fin_cases j <;> simp [bivectorIndex3, horth]
  simp [hα, hβ]

noncomputable def fiberCurvatureOperatorMatrix
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (x : M) (A : Tensor04At (I := I) (M := M) x) : Matrix (Fin 3) (Fin 3) ℝ := by
  classical
  exact if h : A ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x then
    curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨A, h⟩
  else 0

def fiberHamiltonIveyRegion
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (K τ : ℝ) (x : M) : Set (Tensor04At (I := I) (M := M) x) :=
  {A | ∃ h : A ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x,
    curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨A, h⟩ ∈ hamiltonIveyConvexMatrixRegion K τ}

def fiberHamiltonIveyNormalDirections
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (x : M) : Set (Tensor04At (I := I) (M := M) x) :=
  {ν | ∃ h : ν ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x,
    (symmEuclid_isHermitian (matrixToEuclid (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨ν, h⟩))).eigenvalues₀ 0 < 0 ∨
      symmEuclid (matrixToEuclid (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨ν, h⟩)) = 0}

noncomputable def fiberHamiltonIveySupport
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (K τ : ℝ) (x : M) (ν : Tensor04At (I := I) (M := M) x) : ℝ := by
  classical
  exact if h : ν ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x then
    4 * hamiltonIveyConvexMatrixRegionSupportEuclid K τ
      (matrixToEuclid (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨ν, h⟩))
  else 0

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
private lemma fiberBivectorTwoForm_anti
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (p : Fin 3) (X Y : TangentSpace I x) :
    fiberBivectorTwoForm g basis p X Y = -fiberBivectorTwoForm g basis p Y X := by
  unfold fiberBivectorTwoForm
  ring

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
private lemma fiberBivectorTwoForm_cyclic_antisymm
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (p q : Fin 3) (X Y Z W : TangentSpace I x) :
    (fiberBivectorTwoForm g basis p X Y * fiberBivectorTwoForm g basis q W Z +
      fiberBivectorTwoForm g basis p Y Z * fiberBivectorTwoForm g basis q W X +
      fiberBivectorTwoForm g basis p Z X * fiberBivectorTwoForm g basis q W Y) +
    (fiberBivectorTwoForm g basis q X Y * fiberBivectorTwoForm g basis p W Z +
      fiberBivectorTwoForm g basis q Y Z * fiberBivectorTwoForm g basis p W X +
      fiberBivectorTwoForm g basis q Z X * fiberBivectorTwoForm g basis p W Y) = 0 := by
  unfold fiberBivectorTwoForm
  fin_cases p <;> fin_cases q <;> simp [bivectorIndex3] <;> ring

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
theorem fiberBivectorTwoForm_continuous
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x)) (i : Fin 3) :
    Continuous (fun q : TangentSpace I x × TangentSpace I x =>
      fiberBivectorTwoForm g basis i q.1 q.2) := by
  unfold fiberBivectorTwoForm
  have hinner (e : TangentSpace I x) :
      Continuous (fun q : TangentSpace I x × TangentSpace I x => g.inner x q.1 e) := by
    fun_prop
  have hinner' (e : TangentSpace I x) :
      Continuous (fun q : TangentSpace I x × TangentSpace I x => g.inner x q.2 e) := by
    fun_prop
  exact ((hinner (basis (bivectorIndex3 i).1)).mul (hinner' (basis (bivectorIndex3 i).2))).sub
    ((hinner (basis (bivectorIndex3 i).2)).mul (hinner' (basis (bivectorIndex3 i).1)))

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
theorem fiberOperatorTensor_mem_algebraic
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    {Rmat : Matrix (Fin 3) (Fin 3) ℝ} (hR : Rmat.IsSymm) :
    fiberOperatorTensor g basis Rmat ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x := by
  rw [mem_algebraicCurvatureTensorSubmodule_iff_symmetries]
  constructor
  · intro X Y Z W
    rw [fiberOperatorTensor_apply, fiberOperatorTensor_apply]
    have hzero : (∑ p : Fin 3, ∑ q : Fin 3,
          Rmat p q * fiberBivectorTwoForm g basis p X Y * fiberBivectorTwoForm g basis q W Z) +
        (∑ p : Fin 3, ∑ q : Fin 3,
          Rmat p q * fiberBivectorTwoForm g basis p Y X * fiberBivectorTwoForm g basis q W Z) = 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_eq_zero; intro p hp
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_eq_zero; intro q hq
      rw [fiberBivectorTwoForm_anti g basis _ X Y]
      ring
    linarith
  · constructor
    · intro X Y Z W
      rw [fiberOperatorTensor_apply, fiberOperatorTensor_apply]
      have hzero : (∑ p : Fin 3, ∑ q : Fin 3,
            Rmat p q * fiberBivectorTwoForm g basis p X Y * fiberBivectorTwoForm g basis q W Z) +
          (∑ p : Fin 3, ∑ q : Fin 3,
            Rmat p q * fiberBivectorTwoForm g basis p X Y * fiberBivectorTwoForm g basis q Z W) = 0 := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_eq_zero; intro p hp
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_eq_zero; intro q hq
        rw [fiberBivectorTwoForm_anti g basis _ W Z]
        ring
      linarith
    · intro X Y Z W
      rw [fiberOperatorTensor_apply, fiberOperatorTensor_apply, fiberOperatorTensor_apply]
      simp only [← Finset.sum_add_distrib]
      let D : Fin 3 → Fin 3 → ℝ := fun p q =>
        fiberBivectorTwoForm g basis p X Y * fiberBivectorTwoForm g basis q W Z +
          fiberBivectorTwoForm g basis p Y Z * fiberBivectorTwoForm g basis q W X +
          fiberBivectorTwoForm g basis p Z X * fiberBivectorTwoForm g basis q W Y
      have hRsym : ∀ i j : Fin 3, Rmat i j = Rmat j i := by
        intro i j
        have h := congrFun (congrFun hR i) j
        simpa [Matrix.transpose_apply] using h.symm
      have hD : ∀ p q : Fin 3, D p q = -D q p := by
        intro p q
        have h := fiberBivectorTwoForm_cyclic_antisymm g basis p q X Y Z W
        linarith
      have hsum : ∀ p q : Fin 3,
          ((Rmat p q * fiberBivectorTwoForm g basis p X Y * fiberBivectorTwoForm g basis q W Z +
              Rmat p q * fiberBivectorTwoForm g basis p Y Z * fiberBivectorTwoForm g basis q W X) +
            Rmat p q * fiberBivectorTwoForm g basis p Z X * fiberBivectorTwoForm g basis q W Y) =
          Rmat p q * D p q := by
        intro p q
        unfold D
        ring
      have hDsum : (∑ p : Fin 3, ∑ q : Fin 3,
            ((Rmat p q * fiberBivectorTwoForm g basis p X Y * fiberBivectorTwoForm g basis q W Z +
                Rmat p q * fiberBivectorTwoForm g basis p Y Z * fiberBivectorTwoForm g basis q W X) +
              Rmat p q * fiberBivectorTwoForm g basis p Z X * fiberBivectorTwoForm g basis q W Y)) =
          (∑ p : Fin 3, ∑ q : Fin 3, Rmat p q * D p q) := by
        apply Finset.sum_congr rfl; intro p hp
        apply Finset.sum_congr rfl; intro q hq
        exact hsum p q
      rw [hDsum]
      have hzero : (∑ p : Fin 3, ∑ q : Fin 3, Rmat p q * D p q) +
          (∑ p : Fin 3, ∑ q : Fin 3, Rmat p q * D p q) = 0 := by
        have hswap : (∑ p : Fin 3, ∑ q : Fin 3, Rmat p q * D p q) =
            ∑ p : Fin 3, ∑ q : Fin 3, Rmat q p * D q p := by
          have h1 : (∑ p : Fin 3, ∑ q : Fin 3, Rmat p q * D p q) =
              ∑ ij : Fin 3 × Fin 3, Rmat ij.1 ij.2 * D ij.1 ij.2 := by
            rw [Fintype.sum_prod_type]
          have h2 : (∑ p : Fin 3, ∑ q : Fin 3, Rmat q p * D q p) =
              ∑ ij : Fin 3 × Fin 3, Rmat ij.2 ij.1 * D ij.2 ij.1 := by
            rw [Fintype.sum_prod_type]
          calc
            (∑ p : Fin 3, ∑ q : Fin 3, Rmat p q * D p q)
                = ∑ ij : Fin 3 × Fin 3, Rmat ij.1 ij.2 * D ij.1 ij.2 := h1
            _ = ∑ ij : Fin 3 × Fin 3, Rmat ij.2 ij.1 * D ij.2 ij.1 := by
                rw [sum_pair_swap_three (fun ij : Fin 3 × Fin 3 => Rmat ij.1 ij.2 * D ij.1 ij.2)]
            _ = ∑ p : Fin 3, ∑ q : Fin 3, Rmat q p * D q p := h2.symm
        nth_rewrite 2 [hswap]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_eq_zero; intro p hp
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_eq_zero; intro q hq
        rw [show D p q = -D q p from hD p q]
        rw [show Rmat q p = Rmat p q from hRsym q p]
        ring
      linarith

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
private lemma fiberOperatorTensor_curvatureOperatorMatrix
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : ∀ i j : Fin 3, g.inner x (basis i) (basis j) = if i = j then 1 else 0)
    {Rmat : Matrix (Fin 3) (Fin 3) ℝ} (hR : Rmat.IsSymm) :
    curvatureOperatorMatrixAt (I := I) x basis
        ⟨fiberOperatorTensor g basis Rmat, fiberOperatorTensor_mem_algebraic g basis hR⟩ = Rmat := by
  ext i j
  exact fiberOperatorTensor_apply_basis g basis horth Rmat i j

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
private lemma inner0S_algebraic_eq_four_inner_matrixToEuclid
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) g x basis)
    (A B : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    inner0S (I := I) g x 4 (A : Tensor04At (I := I) (M := M) x)
        (B : Tensor04At (I := I) (M := M) x) =
      4 * inner ℝ (matrixToEuclid (curvatureOperatorMatrixAt (I := I) x basis B))
        (matrixToEuclid (curvatureOperatorMatrixAt (I := I) x basis A)) := by
  have h4 := inner0S_algebraic_eq_four_mul_operatorInner g x basis horth A B
  rw [h4]
  congr 1
  rw [inner_matrixToEuclid]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro p hp
  apply Finset.sum_congr rfl; intro q hq
  change curvatureOperatorMatrixAt (I := I) x basis A p q * curvatureOperatorMatrixAt (I := I) x basis B p q =
    curvatureOperatorMatrixAt (I := I) x basis B p q * curvatureOperatorMatrixAt (I := I) x basis A p q
  ring

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
private lemma symmEuclid_isSymm (v : EuclideanSpace ℝ (Fin 3 × Fin 3)) :
    (symmEuclid v).IsSymm := by
  rw [Matrix.IsSymm]
  ext i j
  simp [symmEuclid, Matrix.transpose_apply]
  ring

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
private lemma isSymm_of_isHermitian_real {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : A.IsHermitian) :
    A.IsSymm := by
  rw [Matrix.IsSymm]
  ext i j
  have h := congrFun (congrFun hA i) j
  simpa [Matrix.conjTranspose, Matrix.transpose_apply] using h

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
private lemma euclidToMatrix_isHermitian_of_mem_hamiltonIveyConvexMatrixRegionEuclid
    {K τ : ℝ} {c : EuclideanSpace ℝ (Fin 3 × Fin 3)}
    (hc : c ∈ hamiltonIveyConvexMatrixRegionEuclid K τ) :
    (euclidToMatrix c).IsHermitian := by
  have hcm : euclidToMatrix c ∈ hamiltonIveyConvexMatrixRegion K τ :=
    (mem_hamiltonIveyConvexMatrixRegionEuclid_iff K τ c).mp hc
  rw [hamiltonIveyConvexMatrixRegion_eq_violation] at hcm
  exact hcm.1

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
private lemma euclidToMatrix_isSymm_of_mem_hamiltonIveyConvexMatrixRegionEuclid
    {K τ : ℝ} {c : EuclideanSpace ℝ (Fin 3 × Fin 3)}
    (hc : c ∈ hamiltonIveyConvexMatrixRegionEuclid K τ) :
    (euclidToMatrix c).IsSymm :=
  isSymm_of_isHermitian_real (euclidToMatrix_isHermitian_of_mem_hamiltonIveyConvexMatrixRegionEuclid hc)

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
private lemma inner_eq_symm_inner_of_mem_hamiltonIveyConvexMatrixRegionEuclid
    {K τ : ℝ} {w : EuclideanSpace ℝ (Fin 3 × Fin 3)}
    (c : EuclideanSpace ℝ (Fin 3 × Fin 3))
    (hc : c ∈ hamiltonIveyConvexMatrixRegionEuclid K τ) :
    inner ℝ w c = inner ℝ (matrixToEuclid (symmEuclid w)) c := by
  have hcherm := euclidToMatrix_isHermitian_of_mem_hamiltonIveyConvexMatrixRegionEuclid hc
  have h := inner_matrixToEuclid_symm w (euclidToMatrix c) hcherm
  simpa [matrixToEuclid_euclidToMatrix] using h

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
private lemma symmEuclid_symmEuclid_matrixToEuclid
    (v : EuclideanSpace ℝ (Fin 3 × Fin 3)) :
    symmEuclid (matrixToEuclid (symmEuclid v)) = symmEuclid v := by
  unfold symmEuclid
  rw [euclidToMatrix_matrixToEuclid]
  ext i j
  simp [Matrix.transpose_apply]
  ring

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
private lemma finiteSupportDirections_of_symmEuclid_eq
    {K τ : ℝ} {v w : EuclideanSpace ℝ (Fin 3 × Fin 3)}
    (hv : v ∈ finiteSupportDirections (hamiltonIveyConvexMatrixRegionEuclid K τ))
    (h : symmEuclid v = symmEuclid w) :
    w ∈ finiteSupportDirections (hamiltonIveyConvexMatrixRegionEuclid K τ) := by
  unfold finiteSupportDirections
  rcases hv with ⟨B, hB⟩
  refine ⟨B, ?_⟩
  rintro x ⟨c, hc, rfl⟩
  calc
    inner ℝ w c = inner ℝ v c := by
      rw [inner_eq_symm_inner_of_mem_hamiltonIveyConvexMatrixRegionEuclid (w := w) c hc]
      rw [inner_eq_symm_inner_of_mem_hamiltonIveyConvexMatrixRegionEuclid (w := v) c hc]
      rw [← h]
    _ ≤ B := hB ⟨c, hc, rfl⟩

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
private lemma hamiltonIveyConvexMatrixRegionSupportEuclid_eq_of_symmEuclid_eq
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ)
    {v w : EuclideanSpace ℝ (Fin 3 × Fin 3)}
    (hv : v ∈ finiteSupportDirections (hamiltonIveyConvexMatrixRegionEuclid K τ))
    (h : symmEuclid v = symmEuclid w) :
    hamiltonIveyConvexMatrixRegionSupportEuclid K τ v =
      hamiltonIveyConvexMatrixRegionSupportEuclid K τ w := by
  have hw : w ∈ finiteSupportDirections (hamiltonIveyConvexMatrixRegionEuclid K τ) :=
    finiteSupportDirections_of_symmEuclid_eq hv h
  have h1 := hamiltonIveyConvexMatrixRegionSupportEuclid_eq_supportFunction_of_finiteSupportDirections
    hK hτ v hv
  have h2 := hamiltonIveyConvexMatrixRegionSupportEuclid_eq_supportFunction_of_finiteSupportDirections
    hK hτ w hw
  rw [h1, h2]
  unfold supportFunction
  apply congrArg sSup
  ext x
  constructor <;> rintro ⟨c, hc, rfl⟩ <;> refine ⟨c, hc, ?_⟩
  · rw [inner_eq_symm_inner_of_mem_hamiltonIveyConvexMatrixRegionEuclid (w := v) c hc]
    rw [inner_eq_symm_inner_of_mem_hamiltonIveyConvexMatrixRegionEuclid (w := w) c hc]
    rw [h]
  · rw [inner_eq_symm_inner_of_mem_hamiltonIveyConvexMatrixRegionEuclid (w := w) c hc]
    rw [inner_eq_symm_inner_of_mem_hamiltonIveyConvexMatrixRegionEuclid (w := v) c hc]
    rw [← h]

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
private lemma fiberHamiltonIveySupport_eq
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (K τ : ℝ) (x : M) {ν : Tensor04At (I := I) (M := M) x}
    (hν : ν ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    fiberHamiltonIveySupport basisAt K τ x ν =
      4 * hamiltonIveyConvexMatrixRegionSupportEuclid K τ
        (matrixToEuclid (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨ν, hν⟩)) := by
  unfold fiberHamiltonIveySupport
  rw [dif_pos hν]

omit [CompleteSpace E] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
private lemma inner0S_fiberOperatorTensor_eq
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) g x basis)
    {A : Tensor04At (I := I) (M := M) x}
    (hA : A ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    {Rmat : Matrix (Fin 3) (Fin 3) ℝ} (hR : Rmat.IsSymm) :
    inner0S (I := I) g x 4 A (fiberOperatorTensor g basis Rmat) =
      4 * inner ℝ (matrixToEuclid Rmat)
        (matrixToEuclid (curvatureOperatorMatrixAt (I := I) x basis ⟨A, hA⟩)) := by
  have h4 := inner0S_algebraic_eq_four_inner_matrixToEuclid g x basis horth
    ⟨A, hA⟩ ⟨fiberOperatorTensor g basis Rmat, fiberOperatorTensor_mem_algebraic g basis hR⟩
  rw [h4]
  congr 1
  congr 1
  congr 1
  exact fiberOperatorTensor_curvatureOperatorMatrix g basis
    (fun i j => by simpa [OrthonormalBasisAt, delta3] using horth i j) hR

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
private lemma sSup_mul_image
    {s : Set ℝ} (hs : BddAbove s) (hsne : s.Nonempty) :
    sSup {x : ℝ | ∃ y ∈ s, x = 4 * y} = 4 * sSup s := by
  have hLUB : IsLUB s (sSup s) := isLUB_csSup hsne hs
  have hLUB' : IsLUB {x : ℝ | ∃ y ∈ s, x = 4 * y} (4 * sSup s) := by
    constructor
    · rintro x ⟨y, hy, rfl⟩
      exact mul_le_mul_of_nonneg_left (hLUB.1 hy) (by norm_num)
    · intro u hu
      have hdiv : ∀ y ∈ s, y ≤ u / 4 := by
        intro y hy
        have hy' : 4 * y ≤ u := hu ⟨y, hy, rfl⟩
        exact (le_div_iff₀' (by norm_num : (0 : ℝ) < 4)).mpr hy'
      have hsup_le : sSup s ≤ u / 4 := hLUB.2 hdiv
      exact (le_div_iff₀' (by norm_num : (0 : ℝ) < 4)).mp hsup_le
  exact hLUB'.csSup_eq (by
    rcases hsne with ⟨y, hy⟩
    exact ⟨4 * y, ⟨y, hy, rfl⟩⟩)

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
private lemma inner0S_sub_right
    (g : SmoothRiemannianMetric I M) (x : M)
    (A B C : Tensor04At (I := I) (M := M) x) :
    inner0S (I := I) g x 4 A (B - C) = inner0S (I := I) g x 4 A B - inner0S (I := I) g x 4 A C := by
  unfold inner0S MetricFiberData.inner
  exact map_sub ((tensor0SMetricData (I := I) g x 4).flat A) B C

omit [CompleteSpace E] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
theorem fiberHamiltonIveyRegion_mem_iff_forall_support_le
    (g : SmoothRiemannianMetric I M)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) g x (basisAt x))
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ) (x : M)
    (A : Tensor04At (I := I) (M := M) x)
    (hA : A ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    A ∈ fiberHamiltonIveyRegion basisAt K τ x ↔
      ∀ ν : Tensor04At (I := I) (M := M) x,
        ν ∈ fiberHamiltonIveyNormalDirections basisAt x →
          inner0S (I := I) g x 4 A ν ≤ fiberHamiltonIveySupport basisAt K τ x ν := by
  constructor
  · intro hAregion ν hν
    rcases hAregion with ⟨hAlg, hmat⟩
    rcases hν with ⟨hν, hcond⟩
    let matA := curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨A, hAlg⟩
    let matν := curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨ν, hν⟩
    have hν' : matrixToEuclid matν ∈ finiteSupportDirections (hamiltonIveyConvexMatrixRegionEuclid K τ) := by
      rw [mem_finiteSupportDirections_hamiltonIvey_region_iff hK hτ]
      exact hcond
    have hmatA' : matrixToEuclid matA ∈ hamiltonIveyConvexMatrixRegionEuclid K τ := by
      rw [mem_hamiltonIveyConvexMatrixRegionEuclid_iff]
      simpa [matA, euclidToMatrix_matrixToEuclid] using hmat
    have hmain := (hamiltonIveyConvexMatrixRegionEuclid_mem_iff_forall_support_le hK hτ (matrixToEuclid matA)).mp
      hmatA' (matrixToEuclid matν) hν'
    have hinner : inner0S (I := I) g x 4 A ν =
        4 * inner ℝ (matrixToEuclid matν) (matrixToEuclid matA) :=
      inner0S_algebraic_eq_four_inner_matrixToEuclid g x (basisAt x) (horth0 x) ⟨A, hAlg⟩ ⟨ν, hν⟩
    have hsup : fiberHamiltonIveySupport basisAt K τ x ν =
        4 * hamiltonIveyConvexMatrixRegionSupportEuclid K τ (matrixToEuclid matν) :=
      fiberHamiltonIveySupport_eq basisAt K τ x hν
    calc
      inner0S (I := I) g x 4 A ν = 4 * inner ℝ (matrixToEuclid matν) (matrixToEuclid matA) := hinner
      _ ≤ 4 * hamiltonIveyConvexMatrixRegionSupportEuclid K τ (matrixToEuclid matν) := by
        nlinarith [hmain]
      _ = fiberHamiltonIveySupport basisAt K τ x ν := hsup.symm
  · intro hle
    have hmatAherm : (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨A, hA⟩).IsHermitian :=
      curvatureOperatorMatrixAt_isHermitian x (basisAt x) ⟨A, hA⟩
    have hmatA' : matrixToEuclid (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨A, hA⟩) ∈
        hamiltonIveyConvexMatrixRegionEuclid K τ := by
      rw [mem_hamiltonIveyConvexMatrixRegionEuclid_iff]
      refine (hamiltonIveyConvexMatrixRegionEuclid_mem_iff_forall_support_le hK hτ
        (matrixToEuclid (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨A, hA⟩))).mpr ?_
      intro w hw
      let w' : EuclideanSpace ℝ (Fin 3 × Fin 3) := matrixToEuclid (symmEuclid w)
      have hsymm : symmEuclid w = symmEuclid w' := by
        change symmEuclid w = symmEuclid (matrixToEuclid (symmEuclid w))
        exact (symmEuclid_symmEuclid_matrixToEuclid w).symm
      have hw' : w' ∈ finiteSupportDirections (hamiltonIveyConvexMatrixRegionEuclid K τ) :=
        finiteSupportDirections_of_symmEuclid_eq hw hsymm
      let νT : Tensor04At (I := I) (M := M) x := fiberOperatorTensor g (basisAt x) (symmEuclid w)
      have hνTalg : νT ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
        fiberOperatorTensor_mem_algebraic g (basisAt x) (symmEuclid_isSymm w)
      have hνTN : νT ∈ fiberHamiltonIveyNormalDirections basisAt x := by
        unfold fiberHamiltonIveyNormalDirections
        refine ⟨hνTalg, ?_⟩
        have hfs' : matrixToEuclid (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨νT, hνTalg⟩) ∈
            finiteSupportDirections (hamiltonIveyConvexMatrixRegionEuclid K τ) := by
          rw [show matrixToEuclid (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨νT, hνTalg⟩) = w' by
            dsimp [νT]
            rw [fiberOperatorTensor_curvatureOperatorMatrix g (basisAt x)
              (fun i j => by simpa [OrthonormalBasisAt, delta3] using horth0 x i j) (symmEuclid_isSymm w)]]
          exact hw'
        exact (mem_finiteSupportDirections_hamiltonIvey_region_iff hK hτ
          (matrixToEuclid (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨νT, hνTalg⟩))).mp hfs'
      have hieq : inner0S (I := I) g x 4 A νT =
          4 * inner ℝ w' (matrixToEuclid (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨A, hA⟩)) := by
        have h4 := inner0S_fiberOperatorTensor_eq g (basisAt x) (horth0 x) hA (symmEuclid_isSymm w)
        rw [h4]
      have hsup' : fiberHamiltonIveySupport basisAt K τ x νT =
          4 * hamiltonIveyConvexMatrixRegionSupportEuclid K τ w' := by
        rw [fiberHamiltonIveySupport_eq basisAt K τ x hνTalg]
        congr 1
        rw [fiberOperatorTensor_curvatureOperatorMatrix g (basisAt x)
          (fun i j => by simpa [OrthonormalBasisAt, delta3] using horth0 x i j) (symmEuclid_isSymm w)]
      have hmain := hle νT hνTN
      rw [hieq, hsup'] at hmain
      have hwle : inner ℝ w' (matrixToEuclid (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨A, hA⟩)) ≤
          hamiltonIveyConvexMatrixRegionSupportEuclid K τ w' := by
        nlinarith
      have hsupEq : hamiltonIveyConvexMatrixRegionSupportEuclid K τ w' =
          hamiltonIveyConvexMatrixRegionSupportEuclid K τ w :=
        (hamiltonIveyConvexMatrixRegionSupportEuclid_eq_of_symmEuclid_eq hK hτ (v := w) (w := w') hw hsymm).symm
      have hinnerEq : inner ℝ w (matrixToEuclid (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨A, hA⟩)) =
          inner ℝ w' (matrixToEuclid (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨A, hA⟩)) := by
        rw [inner_matrixToEuclid_symm w (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨A, hA⟩) hmatAherm]
      rw [hinnerEq]
      rwa [← hsupEq]
    exact ⟨hA, by
      simpa [euclidToMatrix_matrixToEuclid] using
        (mem_hamiltonIveyConvexMatrixRegionEuclid_iff K τ
          (matrixToEuclid (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨A, hA⟩))).mp hmatA'⟩

omit [CompleteSpace E] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
theorem fiberHamiltonIveySupport_eq_sSup
    (g : SmoothRiemannianMetric I M)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) g x (basisAt x))
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ) (x : M)
    {ν : Tensor04At (I := I) (M := M) x}
    (hν : ν ∈ fiberHamiltonIveyNormalDirections basisAt x) :
    fiberHamiltonIveySupport basisAt K τ x ν =
      sSup {r : ℝ | ∃ q : Tensor04At (I := I) (M := M) x,
        q ∈ fiberHamiltonIveyRegion basisAt K τ x ∧ r = inner0S (I := I) g x 4 q ν} := by
  rcases hν with ⟨hνalg, hcond⟩
  let matν := curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨ν, hνalg⟩
  let ν' : EuclideanSpace ℝ (Fin 3 × Fin 3) := matrixToEuclid matν
  have hν' : ν' ∈ finiteSupportDirections (hamiltonIveyConvexMatrixRegionEuclid K τ) := by
    rw [mem_finiteSupportDirections_hamiltonIvey_region_iff hK hτ]
    exact hcond
  have hsup : fiberHamiltonIveySupport basisAt K τ x ν =
      4 * hamiltonIveyConvexMatrixRegionSupportEuclid K τ ν' := by
    rw [fiberHamiltonIveySupport_eq basisAt K τ x hνalg]
  have hEq := hamiltonIveyConvexMatrixRegionSupportEuclid_eq_supportFunction_of_finiteSupportDirections
    hK hτ ν' hν'
  unfold supportFunction at hEq
  have hset : {r : ℝ | ∃ q : Tensor04At (I := I) (M := M) x,
        q ∈ fiberHamiltonIveyRegion basisAt K τ x ∧ r = inner0S (I := I) g x 4 q ν} =
      {x : ℝ | ∃ c : EuclideanSpace ℝ (Fin 3 × Fin 3),
        c ∈ hamiltonIveyConvexMatrixRegionEuclid K τ ∧ x = 4 * inner ℝ ν' c} := by
    ext r
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases hq with ⟨hqalg, hqmat⟩
      let c : EuclideanSpace ℝ (Fin 3 × Fin 3) :=
        matrixToEuclid (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨q, hqalg⟩)
      refine ⟨c, ?_, ?_⟩
      · rw [mem_hamiltonIveyConvexMatrixRegionEuclid_iff]
        simpa [c, euclidToMatrix_matrixToEuclid] using hqmat
      · have h4 := inner0S_algebraic_eq_four_inner_matrixToEuclid g x (basisAt x) (horth0 x)
          ⟨q, hqalg⟩ ⟨ν, hνalg⟩
        simpa [ν', c] using h4
    · rintro ⟨c, hc, rfl⟩
      let q := fiberOperatorTensor g (basisAt x) (euclidToMatrix c)
      have hqalg : q ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
        fiberOperatorTensor_mem_algebraic g (basisAt x)
          (euclidToMatrix_isSymm_of_mem_hamiltonIveyConvexMatrixRegionEuclid hc)
      refine ⟨q, ⟨hqalg, ?_⟩, ?_⟩
      · rw [fiberOperatorTensor_curvatureOperatorMatrix g (basisAt x)
          (fun i j => by simpa [OrthonormalBasisAt, delta3] using horth0 x i j)
          (euclidToMatrix_isSymm_of_mem_hamiltonIveyConvexMatrixRegionEuclid hc)]
        exact (mem_hamiltonIveyConvexMatrixRegionEuclid_iff K τ c).mp hc
      · have h4 := inner0S_algebraic_eq_four_inner_matrixToEuclid g x (basisAt x) (horth0 x)
          ⟨q, hqalg⟩ ⟨ν, hνalg⟩
        rw [h4]
        congr 1
        rw [fiberOperatorTensor_curvatureOperatorMatrix g (basisAt x)
          (fun i j => by simpa [OrthonormalBasisAt, delta3] using horth0 x i j)
          (euclidToMatrix_isSymm_of_mem_hamiltonIveyConvexMatrixRegionEuclid hc)]
        rw [matrixToEuclid_euclidToMatrix]
  calc
    fiberHamiltonIveySupport basisAt K τ x ν = 4 * hamiltonIveyConvexMatrixRegionSupportEuclid K τ ν' := hsup
    _ = 4 * sSup {x : ℝ | ∃ c : EuclideanSpace ℝ (Fin 3 × Fin 3),
          c ∈ hamiltonIveyConvexMatrixRegionEuclid K τ ∧ x = inner ℝ ν' c} := by
      rw [hEq]
    _ = sSup {x : ℝ | ∃ c : EuclideanSpace ℝ (Fin 3 × Fin 3),
          c ∈ hamiltonIveyConvexMatrixRegionEuclid K τ ∧ x = 4 * inner ℝ ν' c} := by
      rw [← sSup_mul_image hν' (⟨(0 : ℝ), ⟨(0 : EuclideanSpace ℝ (Fin 3 × Fin 3)),
        ⟨zero_mem_hamiltonIveyConvexMatrixRegionEuclid hK hτ, by simp⟩⟩⟩)]
      apply congrArg sSup
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        rcases hy with ⟨c, hc, rfl⟩
        exact ⟨c, hc, rfl⟩
      · rintro ⟨c, hc, rfl⟩
        refine ⟨inner ℝ ν' c, ?_⟩
        constructor
        · exact ⟨c, hc, rfl⟩
        · rfl
    _ = sSup {r : ℝ | ∃ q : Tensor04At (I := I) (M := M) x,
          q ∈ fiberHamiltonIveyRegion basisAt K τ x ∧ r = inner0S (I := I) g x 4 q ν} := by
      rw [hset]

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
theorem mem_fiberHamiltonIveyNormalDirections_iff
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ) (x : M)
    {ν : Tensor04At (I := I) (M := M) x} :
    ν ∈ fiberHamiltonIveyNormalDirections basisAt x ↔
      ∃ h : ν ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x,
        matrixToEuclid (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨ν, h⟩) ∈
          finiteSupportDirections (hamiltonIveyConvexMatrixRegionEuclid K τ) := by
  unfold fiberHamiltonIveyNormalDirections
  constructor <;> rintro ⟨hν, hc⟩ <;> refine ⟨hν, ?_⟩
  · rwa [mem_finiteSupportDirections_hamiltonIvey_region_iff hK hτ]
  · rwa [mem_finiteSupportDirections_hamiltonIvey_region_iff hK hτ] at hc

omit [CompleteSpace E] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
theorem fiberHamiltonIveyRegion_normal
    (g : SmoothRiemannianMetric I M)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) g x (basisAt x))
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ) (x : M)
    {p : Tensor04At (I := I) (M := M) x}
    {ν : Tensor04At (I := I) (M := M) x}
    (hν : ν ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (hnormal : ∀ q : Tensor04At (I := I) (M := M) x,
      q ∈ fiberHamiltonIveyRegion basisAt K τ x → inner0S (I := I) g x 4 ν (q - p) ≤ 0) :
    ν ∈ fiberHamiltonIveyNormalDirections basisAt x := by
  unfold fiberHamiltonIveyNormalDirections
  refine ⟨hν, ?_⟩
  rw [← mem_finiteSupportDirections_hamiltonIvey_region_iff hK hτ]
  have hbdd : BddAbove {r : ℝ | ∃ q : Tensor04At (I := I) (M := M) x,
      q ∈ fiberHamiltonIveyRegion basisAt K τ x ∧ r = inner0S (I := I) g x 4 ν q} := by
    refine ⟨inner0S (I := I) g x 4 ν p, ?_⟩
    rintro x ⟨q, hq, rfl⟩
    have hqle : inner0S (I := I) g x 4 ν q - inner0S (I := I) g x 4 ν p ≤ 0 := by
      have h := hnormal q hq
      rw [inner0S_sub_right g x ν q p] at h
      linarith
    linarith
  unfold finiteSupportDirections
  refine ⟨inner0S (I := I) g x 4 ν p / 4, ?_⟩
  rintro x ⟨c, hc, rfl⟩
  let q := fiberOperatorTensor g (basisAt x) (euclidToMatrix c)
  have hqalg : q ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
    fiberOperatorTensor_mem_algebraic g (basisAt x)
      (euclidToMatrix_isSymm_of_mem_hamiltonIveyConvexMatrixRegionEuclid hc)
  have hqregion : q ∈ fiberHamiltonIveyRegion basisAt K τ x := by
    refine ⟨hqalg, ?_⟩
    rw [fiberOperatorTensor_curvatureOperatorMatrix g (basisAt x)
      (fun i j => by simpa [OrthonormalBasisAt, delta3] using horth0 x i j)
      (euclidToMatrix_isSymm_of_mem_hamiltonIveyConvexMatrixRegionEuclid hc)]
    exact (mem_hamiltonIveyConvexMatrixRegionEuclid_iff K τ c).mp hc
  have hle : inner0S (I := I) g x 4 ν q ≤ inner0S (I := I) g x 4 ν p := by
    have hqle : inner0S (I := I) g x 4 ν q - inner0S (I := I) g x 4 ν p ≤ 0 := by
      have h := hnormal q hqregion
      rw [inner0S_sub_right g x ν q p] at h
      linarith
    linarith
  have h4 : 4 * inner ℝ (matrixToEuclid (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨ν, hν⟩)) c =
      inner0S (I := I) g x 4 ν q := by
    have h4' := inner0S_algebraic_eq_four_inner_matrixToEuclid g x (basisAt x) (horth0 x)
      ⟨ν, hν⟩ ⟨q, hqalg⟩
    rw [h4']
    congr 1
    rw [fiberOperatorTensor_curvatureOperatorMatrix g (basisAt x)
      (fun i j => by simpa [OrthonormalBasisAt, delta3] using horth0 x i j)
      (euclidToMatrix_isSymm_of_mem_hamiltonIveyConvexMatrixRegionEuclid hc)]
    rw [matrixToEuclid_euclidToMatrix]
    rw [real_inner_comm]
  have hle4 : 4 * inner ℝ (matrixToEuclid (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨ν, hν⟩)) c ≤
      inner0S (I := I) g x 4 ν p := by
    rw [h4]
    exact hle
  exact (le_div_iff₀' (by norm_num : (0 : ℝ) < 4)).mpr hle4

end DifferentialGeometry.PDE.RicciFlow

end
