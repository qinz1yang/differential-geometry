import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperator.Metric

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

open Bundle
open DifferentialGeometry.Analysis.InnerProductSpace
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
    tensor04StandardAt (I := I) (M := M) (fiberOperatorTensor g basis Rmat) X Y Z W =
      ∑ p : Fin 3, ∑ q : Fin 3,
        Rmat p q * fiberBivectorTwoForm g basis p X Y * fiberBivectorTwoForm g basis q W Z := by
  unfold tensor04StandardAt fiberOperatorTensor
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
    tensor04StandardAt (I := I) (M := M) (fiberOperatorTensor g basis Rmat)
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

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
theorem tensor04CurvatureOperatorMatrixAt_fiberOperatorTensor
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) g x basis)
    (Rmat : Matrix (Fin 3) (Fin 3) ℝ) :
    tensor04CurvatureOperatorMatrixAt (I := I) basis
        (fiberOperatorTensor g basis Rmat) = Rmat := by
  ext i j
  exact fiberOperatorTensor_apply_basis g basis horth Rmat i j


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
                rw [sum_pair_swap (fun ij : Fin 3 × Fin 3 => Rmat ij.1 ij.2 * D ij.1 ij.2)]
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

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
    [SigmaCompactSpace M] [T2Space M] in
private lemma inner_basis_eq_repr3
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) g x basis)
    (X : TangentSpace I x) (k : Fin 3) :
    g.inner x X (basis k) = basis.repr X k := by
  classical
  rw [inner_eq_sum_repr3 (I := I) horth X (basis k)]
  have hsingle : ∀ i : Fin 3, basis.repr (basis k) i = if i = k then 1 else 0 := by
    intro i
    rw [basis.repr_self k, Finsupp.single_apply]
    by_cases h : k = i
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun hi => h hi.symm)]
  calc
    (∑ i : Fin 3, basis.repr X i * basis.repr (basis k) i) =
        ∑ i : Fin 3, basis.repr X i * (if i = k then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hsingle i]
    _ = basis.repr X k := by
      rw [Finset.sum_eq_single k]
      · rw [if_pos rfl]
        simp
      · intro i _ hik
        rw [if_neg hik]
        simp
      · intro hk
        exact absurd (Finset.mem_univ k) hk

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
    [SigmaCompactSpace M] [T2Space M] in
theorem fiberBivectorTwoForm_eq_repr
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) g x basis)
    (p : Fin 3) (X Y : TangentSpace I x) :
    fiberBivectorTwoForm (I := I) g basis p X Y =
      basis.repr X (bivectorIndex3 p).1 * basis.repr Y (bivectorIndex3 p).2 -
        basis.repr X (bivectorIndex3 p).2 * basis.repr Y (bivectorIndex3 p).1 := by
  unfold fiberBivectorTwoForm
  rw [inner_basis_eq_repr3 (I := I) g basis horth X (bivectorIndex3 p).1]
  rw [inner_basis_eq_repr3 (I := I) g basis horth X (bivectorIndex3 p).2]
  rw [inner_basis_eq_repr3 (I := I) g basis horth Y (bivectorIndex3 p).1]
  rw [inner_basis_eq_repr3 (I := I) g basis horth Y (bivectorIndex3 p).2]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [IsManifold I 1 M]
    [IsManifold I 2 M] [SigmaCompactSpace M] [T2Space M]
    in
private lemma bivectorSum_prod_eq
    (a b c d : Fin 3 → ℝ) :
    (∑ p : Fin 3,
        (a (bivectorIndex3 p).1 * b (bivectorIndex3 p).2 - a (bivectorIndex3 p).2 * b (bivectorIndex3 p).1) *
          (c (bivectorIndex3 p).1 * d (bivectorIndex3 p).2 - c (bivectorIndex3 p).2 * d (bivectorIndex3 p).1)) =
      (∑ k : Fin 3, a k * c k) * (∑ k : Fin 3, b k * d k) -
        (∑ k : Fin 3, a k * d k) * (∑ k : Fin 3, b k * c k) := by
  classical
  rw [Fin.sum_univ_three]
  rw [show (∑ k : Fin 3, a k * c k) = a 0 * c 0 + a 1 * c 1 + a 2 * c 2 by rw [Fin.sum_univ_three]]
  rw [show (∑ k : Fin 3, b k * d k) = b 0 * d 0 + b 1 * d 1 + b 2 * d 2 by rw [Fin.sum_univ_three]]
  rw [show (∑ k : Fin 3, a k * d k) = a 0 * d 0 + a 1 * d 1 + a 2 * d 2 by rw [Fin.sum_univ_three]]
  rw [show (∑ k : Fin 3, b k * c k) = b 0 * c 0 + b 1 * c 1 + b 2 * c 2 by rw [Fin.sum_univ_three]]
  simp [bivectorIndex3]
  ring

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
    [SigmaCompactSpace M] [T2Space M] in
theorem fiberBivectorTwoForm_sum_pair
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) g x basis)
    (X Y Z W : TangentSpace I x) :
    (∑ p : Fin 3,
        fiberBivectorTwoForm (I := I) g basis p X Y *
          fiberBivectorTwoForm (I := I) g basis p Z W) =
      g.inner x X Z * g.inner x Y W - g.inner x X W * g.inner x Y Z := by
  classical
  simp_rw [fiberBivectorTwoForm_eq_repr (I := I) g basis horth]
  rw [inner_eq_sum_repr3 (I := I) horth X Z, inner_eq_sum_repr3 (I := I) horth Y W,
    inner_eq_sum_repr3 (I := I) horth X W, inner_eq_sum_repr3 (I := I) horth Y Z]
  exact bivectorSum_prod_eq (basis.repr X) (basis.repr Y) (basis.repr Z) (basis.repr W)

omit [E : Type*] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] [H : Type*] [TopologicalSpace H] [I : ModelWithCorners ℝ E H]
    [M : Type*] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [IsManifold I 1 M] [IsManifold I 2 M] [SigmaCompactSpace M]
    [T2Space M] in
private lemma delta3_bivector_mul
    (i j : Fin 3) :
    delta3 (bivectorIndex3 i).1 (bivectorIndex3 j).1 *
        delta3 (bivectorIndex3 i).2 (bivectorIndex3 j).2 -
      delta3 (bivectorIndex3 i).1 (bivectorIndex3 j).2 *
        delta3 (bivectorIndex3 i).2 (bivectorIndex3 j).1 = delta3 i j := by
  fin_cases i <;> fin_cases j <;> simp [bivectorIndex3, delta3]

noncomputable def bivectorFrameChangeMatrix
    (g : SmoothRiemannianMetric I M) {x : M}
    (b b' : Module.Basis (Fin 3) ℝ (TangentSpace I x)) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  fun p i => fiberBivectorTwoForm (I := I) g b p
    (b' (bivectorIndex3 i).1) (b' (bivectorIndex3 i).2)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
    [SigmaCompactSpace M] [T2Space M] in
theorem bivectorFrameChangeMatrix_mul_transpose_of_orthonormal
    (g : SmoothRiemannianMetric I M) {x : M}
    (b b' : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (hb : OrthonormalBasisAt (I := I) g x b)
    (hb' : OrthonormalBasisAt (I := I) g x b') :
    bivectorFrameChangeMatrix (I := I) g b b' *
        (bivectorFrameChangeMatrix (I := I) g b b').transpose = 1 := by
  classical
  let O : Matrix (Fin 3) (Fin 3) ℝ := bivectorFrameChangeMatrix (I := I) g b b'
  have hOtO : O.transpose * O = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    change (∑ p : Fin 3, bivectorFrameChangeMatrix (I := I) g b b' p i *
          bivectorFrameChangeMatrix (I := I) g b b' p j) =
        if i = j then 1 else 0
    simp only [bivectorFrameChangeMatrix]
    rw [fiberBivectorTwoForm_sum_pair (I := I) g b hb
      (b' (bivectorIndex3 i).1) (b' (bivectorIndex3 i).2)
      (b' (bivectorIndex3 j).1) (b' (bivectorIndex3 j).2)]
    rw [hb' (bivectorIndex3 i).1 (bivectorIndex3 j).1, hb' (bivectorIndex3 i).2 (bivectorIndex3 j).2,
      hb' (bivectorIndex3 i).1 (bivectorIndex3 j).2, hb' (bivectorIndex3 i).2 (bivectorIndex3 j).1]
    simpa [delta3] using delta3_bivector_mul i j
  exact matrixTransposeMul_orthogonal (O := O.transpose) (by simpa [Matrix.transpose_transpose] using hOtO)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
    [SigmaCompactSpace M] [T2Space M] in
private lemma matrix_conj_dot
    (M O : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) :
    (O.transpose * M * O) i j = ∑ p : Fin 3, ∑ q : Fin 3, M p q * O p i * O q j := by
  classical
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [SigmaCompactSpace M] [T2Space M] in
theorem tensor04CurvatureOperatorMatrixAt_conj_of_orthonormal
    (g : SmoothRiemannianMetric I M) {x : M}
    (b b' : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (hb : OrthonormalBasisAt (I := I) g x b)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    tensor04CurvatureOperatorMatrixAt (I := I) b' (A : Tensor04At x) =
      (bivectorFrameChangeMatrix (I := I) g b b').transpose *
        tensor04CurvatureOperatorMatrixAt (I := I) b (A : Tensor04At x) *
        bivectorFrameChangeMatrix (I := I) g b b' := by
  classical
  let Mat : Matrix (Fin 3) (Fin 3) ℝ := tensor04CurvatureOperatorMatrixAt (I := I) b (A : Tensor04At x)
  let O : Matrix (Fin 3) (Fin 3) ℝ := bivectorFrameChangeMatrix (I := I) g b b'
  have hsymm : Mat.IsSymm := by
    rw [Matrix.IsSymm]
    ext i j
    have hM : (curvatureOperatorMatrixAt (I := I) x b A).IsHermitian :=
      curvatureOperatorMatrixAt_isHermitian (I := I) x b A
    have h := congrFun (congrFun hM i) j
    rw [Matrix.conjTranspose_apply, star_trivial] at h
    change tensor04CurvatureOperatorMatrixAt (I := I) b (A : Tensor04At x) j i =
      tensor04CurvatureOperatorMatrixAt (I := I) b (A : Tensor04At x) i j
    simpa only [tensor04CurvatureOperatorMatrixAt_eq_curvatureOperatorMatrixAt] using h
  have hTensor_mem : fiberOperatorTensor (I := I) g b Mat ∈
      algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
    fiberOperatorTensor_mem_algebraic (I := I) g b hsymm
  have hTensor_map : tensor04CurvatureOperatorMatrixAt (I := I) b
      (fiberOperatorTensor (I := I) g b Mat) = Mat :=
    tensor04CurvatureOperatorMatrixAt_fiberOperatorTensor (I := I) g b hb Mat
  have hA_eq : fiberOperatorTensor (I := I) g b Mat = (A : Tensor04At x) := by
    have hzero : (⟨fiberOperatorTensor (I := I) g b Mat, hTensor_mem⟩ :
        algebraicCurvatureTensorSubmodule (I := I) (M := M) x) - A = 0 := by
      apply curvatureOperatorMatrixAt_eq_zero_of_orthonormal (I := I) (M := M) g x b hb
      change tensor04CurvatureOperatorMatrixAt (I := I) b
          (fiberOperatorTensor (I := I) g b Mat - (A : Tensor04At x)) = 0
      rw [tensor04CurvatureOperatorMatrixAt_sub]
      rw [hTensor_map]
      change Mat - Mat = 0
      simp
    exact congrArg (fun Y : algebraicCurvatureTensorSubmodule (I := I) (M := M) x =>
      (Y : Tensor04At (I := I) (M := M) x)) (sub_eq_zero.mp hzero)
  ext i j
  calc
    tensor04CurvatureOperatorMatrixAt (I := I) b' (A : Tensor04At x) i j
        = tensor04StandardAt (I := I) (M := M) (A : Tensor04At x)
            (b' (bivectorIndex3 i).1) (b' (bivectorIndex3 i).2)
            (b' (bivectorIndex3 j).2) (b' (bivectorIndex3 j).1) := rfl
    _ = tensor04StandardAt (I := I) (M := M) (fiberOperatorTensor (I := I) g b Mat)
            (b' (bivectorIndex3 i).1) (b' (bivectorIndex3 i).2)
            (b' (bivectorIndex3 j).2) (b' (bivectorIndex3 j).1) := by rw [hA_eq]
    _ = ∑ p : Fin 3, ∑ q : Fin 3,
          Mat p q * fiberBivectorTwoForm (I := I) g b p (b' (bivectorIndex3 i).1) (b' (bivectorIndex3 i).2) *
            fiberBivectorTwoForm (I := I) g b q (b' (bivectorIndex3 j).1) (b' (bivectorIndex3 j).2) :=
          fiberOperatorTensor_apply (I := I) g b Mat
            (b' (bivectorIndex3 i).1) (b' (bivectorIndex3 i).2)
            (b' (bivectorIndex3 j).2) (b' (bivectorIndex3 j).1)
    _ = (O.transpose * Mat * O) i j := by
          rw [show (O.transpose * Mat * O) i j = ∑ p : Fin 3, ∑ q : Fin 3,
              Mat p q * O p i * O q j from matrix_conj_dot Mat O i j]
          apply Finset.sum_congr rfl
          intro p hp
          apply Finset.sum_congr rfl
          intro q hq
          simp only [O, bivectorFrameChangeMatrix]


end DifferentialGeometry.Geometry.Curvature.DimensionThree

end
