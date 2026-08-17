import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.BundleConvex
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.HamiltonIveyIntrinsicTransfer
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.HamiltonIveyIntrinsicContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.HamiltonIveyInnerLaplacian
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.HamiltonIveyCurvatureEvolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.HamiltonIveyFixedFrameEvolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.SolutionTimeRestrict

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology RealInnerProductSpace BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
variable [SigmaCompactSpace M] [T2Space M]

noncomputable instance modelF_finiteDimensional :
    FiniteDimensional ℝ (Tensor0SModel 4 ℝ E) := by
  unfold Tensor0SModel
  exact inferInstance

@[implicit_reducible]
noncomputable def modelF_core
    (b : Module.Basis (Fin (Module.finrank ℝ (Tensor0SModel 4 ℝ E))) ℝ (Tensor0SModel 4 ℝ E)) :
    InnerProductSpace.Core ℝ (Tensor0SModel 4 ℝ E) where
  inner x y := ∑ i : Fin (Module.finrank ℝ (Tensor0SModel 4 ℝ E)), b.repr x i * b.repr y i
  conj_inner_symm x y := by
    change star (∑ i : Fin (Module.finrank ℝ (Tensor0SModel 4 ℝ E)),
        (b.repr y) i * (b.repr x) i) =
      ∑ i : Fin (Module.finrank ℝ (Tensor0SModel 4 ℝ E)),
        (b.repr x) i * (b.repr y) i
    rw [star_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp [mul_comm]
  re_inner_nonneg x := by
    change 0 ≤ ∑ i : Fin (Module.finrank ℝ (Tensor0SModel 4 ℝ E)),
        (b.repr x) i * (b.repr x) i
    exact Finset.sum_nonneg (fun i _ => by simpa [pow_two] using sq_nonneg (b.repr x i))
  add_left x y z := by
    change (∑ i : Fin (Module.finrank ℝ (Tensor0SModel 4 ℝ E)),
        (b.repr (x + y)) i * (b.repr z) i) =
      (∑ i : Fin (Module.finrank ℝ (Tensor0SModel 4 ℝ E)),
        (b.repr x) i * (b.repr z) i) +
      (∑ i : Fin (Module.finrank ℝ (Tensor0SModel 4 ℝ E)),
        (b.repr y) i * (b.repr z) i)
    simp [map_add, add_mul, Finset.sum_add_distrib]
  smul_left x y r := by
    change (∑ i : Fin (Module.finrank ℝ (Tensor0SModel 4 ℝ E)),
        (b.repr (r • x)) i * (b.repr y) i) =
      star r * (∑ i : Fin (Module.finrank ℝ (Tensor0SModel 4 ℝ E)),
        (b.repr x) i * (b.repr y) i)
    simp [map_smul, Finset.mul_sum, mul_left_comm, mul_comm]
  definite x hx := by
    have hsq : ∀ i : Fin (Module.finrank ℝ (Tensor0SModel 4 ℝ E)), b.repr x i = 0 := by
      intro i
      have hsum : (∑ j : Fin (Module.finrank ℝ (Tensor0SModel 4 ℝ E)), b.repr x j ^ 2) = 0 := by
        simpa [pow_two] using hx
      have hle : b.repr x i ^ 2 ≤ ∑ j : Fin (Module.finrank ℝ (Tensor0SModel 4 ℝ E)), b.repr x j ^ 2 := by
        exact Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
      have hzero : b.repr x i ^ 2 = 0 := by
        have hnn : 0 ≤ b.repr x i ^ 2 := sq_nonneg _
        nlinarith [hle, hsum, hnn]
      exact sq_eq_zero_iff.mp hzero
    have hz : b.repr x = 0 := by
      ext i
      exact hsq i
    exact (b.repr.map_eq_zero_iff).mp hz

section IntrinsicRegionData

variable {T : ℝ} (hT : 0 < T)

@[implicit_reducible]
noncomputable def fiberCore0S (g : SmoothRiemannianMetric I M) (x : M) :
    InnerProductSpace.Core ℝ (Tensor04At (I := I) (M := M) x) :=
  (tensor0SMetricData (I := I) g x 4).toCore

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
  [SigmaCompactSpace M] [T2Space M] in
theorem exists_fiberProjW (g : SmoothRiemannianMetric I M) (x : M)
    (ν : Tensor04At (I := I) (M := M) x) :
    ∃ w : algebraicCurvatureTensorSubmodule (I := I) (M := M) x,
      ∀ q : algebraicCurvatureTensorSubmodule (I := I) (M := M) x,
        inner0S (I := I) g x 4 (w : Tensor04At (I := I) (M := M) x) q =
          inner0S (I := I) g x 4 ν (q : Tensor04At (I := I) (M := M) x) := by
  let W : Submodule ℝ (Tensor04At (I := I) (M := M) x) :=
    algebraicCurvatureTensorSubmodule (I := I) (M := M) x
  let D : MetricFiberData (Tensor04At (I := I) (M := M) x) :=
    tensor0SMetricData (I := I) g x 4
  have hinner_add : ∀ (a b c : Tensor04At (I := I) (M := M) x),
      inner0S (I := I) g x 4 (a + b) c = inner0S (I := I) g x 4 a c + inner0S (I := I) g x 4 b c := by
    intro a b c
    change D.inner (a + b) c = D.inner a c + D.inner b c
    change D.flat (a + b) c = D.flat a c + D.flat b c
    rw [map_add]
    rfl
  have hinner_smul : ∀ (r : ℝ) (a c : Tensor04At (I := I) (M := M) x),
      inner0S (I := I) g x 4 (r • a) c = r * inner0S (I := I) g x 4 a c := by
    intro r a c
    change D.inner (r • a) c = r * D.inner a c
    change D.flat (r • a) c = r * D.flat a c
    rw [map_smul]
    rfl
  have hinner_definite : ∀ (a : Tensor04At (I := I) (M := M) x),
      inner0S (I := I) g x 4 a a = 0 → a = 0 := by
    intro a ha
    change D.inner a a = 0 at ha
    exact (D.inner_self_eq_zero_iff a).mp ha
  let L : W →ₗ[ℝ] Module.Dual ℝ W :=
    { toFun := fun w =>
        { toFun := fun q => inner0S (I := I) g x 4 (w : Tensor04At (I := I) (M := M) x) (q : Tensor04At (I := I) (M := M) x)
          map_add' := by
            intro q₁ q₂
            change inner0S (I := I) g x 4 (w : Tensor04At (I := I) (M := M) x) (q₁ + q₂) =
              inner0S (I := I) g x 4 (w : Tensor04At (I := I) (M := M) x) (q₁ : Tensor04At (I := I) (M := M) x) +
              inner0S (I := I) g x 4 (w : Tensor04At (I := I) (M := M) x) (q₂ : Tensor04At (I := I) (M := M) x)
            change D.flat (w : Tensor04At (I := I) (M := M) x) (q₁ + q₂) =
              D.flat (w : Tensor04At (I := I) (M := M) x) (q₁ : Tensor04At (I := I) (M := M) x) +
              D.flat (w : Tensor04At (I := I) (M := M) x) (q₂ : Tensor04At (I := I) (M := M) x)
            exact map_add (D.flat (w : Tensor04At (I := I) (M := M) x))
              (q₁ : Tensor04At (I := I) (M := M) x) (q₂ : Tensor04At (I := I) (M := M) x)
          map_smul' := by
            intro r q
            change inner0S (I := I) g x 4 (w : Tensor04At (I := I) (M := M) x) (r • q) =
              r * inner0S (I := I) g x 4 (w : Tensor04At (I := I) (M := M) x) (q : Tensor04At (I := I) (M := M) x)
            change D.flat (w : Tensor04At (I := I) (M := M) x) (r • q) =
              r * D.flat (w : Tensor04At (I := I) (M := M) x) (q : Tensor04At (I := I) (M := M) x)
            simp [smul_eq_mul, map_smul] }
      map_add' := by
        intro w₁ w₂
        ext q
        change inner0S (I := I) g x 4 ((w₁ + w₂ : W) : Tensor04At (I := I) (M := M) x) (q : Tensor04At (I := I) (M := M) x) =
          inner0S (I := I) g x 4 (w₁ : Tensor04At (I := I) (M := M) x) (q : Tensor04At (I := I) (M := M) x) +
          inner0S (I := I) g x 4 (w₂ : Tensor04At (I := I) (M := M) x) (q : Tensor04At (I := I) (M := M) x)
        exact hinner_add (w₁ : Tensor04At (I := I) (M := M) x) (w₂ : Tensor04At (I := I) (M := M) x) (q : Tensor04At (I := I) (M := M) x)
      map_smul' := by
        intro r w₁
        ext q
        change inner0S (I := I) g x 4 ((r • w₁ : W) : Tensor04At (I := I) (M := M) x) (q : Tensor04At (I := I) (M := M) x) =
          r * inner0S (I := I) g x 4 (w₁ : Tensor04At (I := I) (M := M) x) (q : Tensor04At (I := I) (M := M) x)
        exact hinner_smul r (w₁ : Tensor04At (I := I) (M := M) x) (q : Tensor04At (I := I) (M := M) x) }
  have hinj : Function.Injective L := by
    intro w₁ w₂ h
    have hz : ∀ q : W, inner0S (I := I) g x 4 ((w₁ - w₂ : W) : Tensor04At (I := I) (M := M) x) (q : Tensor04At (I := I) (M := M) x) = 0 := by
      intro q
      have hq := congrArg (fun l : Module.Dual ℝ W => l q) h
      change inner0S (I := I) g x 4 (w₁ : Tensor04At (I := I) (M := M) x) (q : Tensor04At (I := I) (M := M) x) =
        inner0S (I := I) g x 4 (w₂ : Tensor04At (I := I) (M := M) x) (q : Tensor04At (I := I) (M := M) x) at hq
      have hsub : inner0S (I := I) g x 4 ((w₁ - w₂ : W) : Tensor04At (I := I) (M := M) x) (q : Tensor04At (I := I) (M := M) x) =
          inner0S (I := I) g x 4 (w₁ : Tensor04At (I := I) (M := M) x) (q : Tensor04At (I := I) (M := M) x) -
          inner0S (I := I) g x 4 (w₂ : Tensor04At (I := I) (M := M) x) (q : Tensor04At (I := I) (M := M) x) := by
        change D.flat (w₁ - w₂ : Tensor04At (I := I) (M := M) x) (q : Tensor04At (I := I) (M := M) x) =
          D.flat (w₁ : Tensor04At (I := I) (M := M) x) (q : Tensor04At (I := I) (M := M) x) -
          D.flat (w₂ : Tensor04At (I := I) (M := M) x) (q : Tensor04At (I := I) (M := M) x)
        rw [map_sub]
        rfl
      rw [hsub]
      linarith
    have hself : inner0S (I := I) g x 4 ((w₁ - w₂ : W) : Tensor04At (I := I) (M := M) x)
        (w₁ - w₂ : Tensor04At (I := I) (M := M) x) = 0 := by
      simpa using hz ⟨(w₁ - w₂ : Tensor04At (I := I) (M := M) x), by
        exact Submodule.sub_mem W w₁.2 w₂.2⟩
    have hzero : (w₁ - w₂ : Tensor04At (I := I) (M := M) x) = 0 :=
      hinner_definite (w₁ - w₂ : Tensor04At (I := I) (M := M) x) hself
    apply Subtype.ext
    exact sub_eq_zero.mp hzero
  have hdim : Module.finrank ℝ W = Module.finrank ℝ (Module.Dual ℝ W) := by
    exact (Subspace.dual_finrank_eq (K := ℝ) (V := W)).symm
  have hsurj : Function.Surjective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K := ℝ) (V := W)
      (V₂ := Module.Dual ℝ W) hdim).mp hinj
  let f : Module.Dual ℝ W :=
    { toFun := fun q => inner0S (I := I) g x 4 ν (q : Tensor04At (I := I) (M := M) x)
      map_add' := by
        intro q₁ q₂
        change inner0S (I := I) g x 4 ν (q₁ + q₂) =
          inner0S (I := I) g x 4 ν (q₁ : Tensor04At (I := I) (M := M) x) +
          inner0S (I := I) g x 4 ν (q₂ : Tensor04At (I := I) (M := M) x)
        change D.flat ν (q₁ + q₂) = D.flat ν (q₁ : Tensor04At (I := I) (M := M) x) +
          D.flat ν (q₂ : Tensor04At (I := I) (M := M) x)
        exact map_add (D.flat ν) (q₁ : Tensor04At (I := I) (M := M) x) (q₂ : Tensor04At (I := I) (M := M) x)
      map_smul' := by
        intro r q
        change inner0S (I := I) g x 4 ν (r • q) = r * inner0S (I := I) g x 4 ν (q : Tensor04At (I := I) (M := M) x)
        change D.flat ν (r • q) = r * D.flat ν (q : Tensor04At (I := I) (M := M) x)
        simp [smul_eq_mul, map_smul] }
  rcases hsurj f with ⟨w, hw⟩
  refine ⟨w, ?_⟩
  intro q
  have hq := congrArg (fun l : Module.Dual ℝ W => l q) hw
  change inner0S (I := I) g x 4 (w : Tensor04At (I := I) (M := M) x) (q : Tensor04At (I := I) (M := M) x) =
    inner0S (I := I) g x 4 ν (q : Tensor04At (I := I) (M := M) x)
  simpa [L, f] using hq

noncomputable def fiberProjW (g : SmoothRiemannianMetric I M) (x : M)
    (ν : Tensor04At (I := I) (M := M) x) :
    algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
  Classical.choose (exists_fiberProjW (I := I) g x ν)

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
  [SigmaCompactSpace M] [T2Space M] in
theorem fiberProjW_spec (g : SmoothRiemannianMetric I M) (x : M)
    (ν : Tensor04At (I := I) (M := M) x)
    (q : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    inner0S (I := I) g x 4 (fiberProjW (I := I) g x ν : Tensor04At (I := I) (M := M) x) q =
      inner0S (I := I) g x 4 ν (q : Tensor04At (I := I) (M := M) x) :=
  Classical.choose_spec (exists_fiberProjW (I := I) g x ν) q

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
  [SigmaCompactSpace M] [T2Space M] in
theorem fiberProjW_inner_eq
    (g : SmoothRiemannianMetric I M) (x : M)
    (ν : Tensor04At (I := I) (M := M) x)
    (q : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    inner0S (I := I) g x 4 (fiberProjW (I := I) g x ν : Tensor04At (I := I) (M := M) x) q =
      inner0S (I := I) g x 4 ν (q : Tensor04At (I := I) (M := M) x) :=
  fiberProjW_spec (I := I) g x ν q

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
  [SigmaCompactSpace M] [T2Space M] in
theorem fiberProjW_self
    (g : SmoothRiemannianMetric I M) (x : M)
    {ν : Tensor04At (I := I) (M := M) x}
    (hν : ν ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    (fiberProjW (I := I) g x ν : Tensor04At (I := I) (M := M) x) = ν := by
  let W : Submodule ℝ (Tensor04At (I := I) (M := M) x) :=
    algebraicCurvatureTensorSubmodule (I := I) (M := M) x
  let u : W := ⟨ν, hν⟩
  let p : W := fiberProjW (I := I) g x ν
  have hchar_p : ∀ q : W, inner0S (I := I) g x 4 (p : Tensor04At (I := I) (M := M) x) q =
      inner0S (I := I) g x 4 ν (q : Tensor04At (I := I) (M := M) x) :=
    fiberProjW_spec (I := I) g x ν
  have hchar_u : ∀ q : W, inner0S (I := I) g x 4 (u : Tensor04At (I := I) (M := M) x) q =
      inner0S (I := I) g x 4 ν (q : Tensor04At (I := I) (M := M) x) := by
    intro q
    rfl
  have hdiff : ∀ q : W, inner0S (I := I) g x 4 ((p - u) : Tensor04At (I := I) (M := M) x) q = 0 := by
    intro q
    have h1 := hchar_p q
    have h2 := hchar_u q
    have hsub : inner0S (I := I) g x 4 ((p - u) : Tensor04At (I := I) (M := M) x) q =
        inner0S (I := I) g x 4 (p : Tensor04At (I := I) (M := M) x) q -
          inner0S (I := I) g x 4 (u : Tensor04At (I := I) (M := M) x) q := by
      change (tensor0SMetricData (I := I) g x 4).flat ((p : Tensor04At (I := I) (M := M) x) - u) (q : Tensor04At (I := I) (M := M) x) =
        (tensor0SMetricData (I := I) g x 4).flat (p : Tensor04At (I := I) (M := M) x) (q : Tensor04At (I := I) (M := M) x) -
          (tensor0SMetricData (I := I) g x 4).flat (u : Tensor04At (I := I) (M := M) x) (q : Tensor04At (I := I) (M := M) x)
      simp [map_sub]
    rw [hsub]
    linarith
  have hself : inner0S (I := I) g x 4 ((p - u) : Tensor04At (I := I) (M := M) x) (p - u) = 0 := by
    simpa using hdiff ⟨(p - u : Tensor04At (I := I) (M := M) x), by
      exact Submodule.sub_mem W p.2 u.2⟩
  have hzero : (p - u : Tensor04At (I := I) (M := M) x) = 0 := by
    change (tensor0SMetricData (I := I) g x 4).inner ((p - u : Tensor04At (I := I) (M := M) x)) (p - u) = 0 at hself
    exact ((tensor0SMetricData (I := I) g x 4).inner_self_eq_zero_iff (p - u : Tensor04At (I := I) (M := M) x)).mp hself
  have hpeq : p = u := by
    apply Subtype.ext
    exact sub_eq_zero.mp hzero
  simpa [p, u] using congrArg Subtype.val hpeq

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
  [SigmaCompactSpace M] [T2Space M] in
theorem fiberProjW_idem
    (g : SmoothRiemannianMetric I M) (x : M)
    (ν : Tensor04At (I := I) (M := M) x) :
    (fiberProjW (I := I) g x (fiberProjW (I := I) g x ν : Tensor04At (I := I) (M := M) x) :
        Tensor04At (I := I) (M := M) x) =
      (fiberProjW (I := I) g x ν : Tensor04At (I := I) (M := M) x) :=
  fiberProjW_self (I := I) g x (fiberProjW (I := I) g x ν).2

noncomputable def regionProjMatrix
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (ν : Tensor04At (I := I) (M := M) x) : Matrix (Fin 3) (Fin 3) Real :=
  curvatureOperatorMatrixAt (I := I) x basis (fiberProjW (I := I) g x ν)

noncomputable def regionSupport
    (g : SmoothRiemannianMetric I M)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (K τ : ℝ) (x : M) (ν : Tensor04At (I := I) (M := M) x) : ℝ :=
  4 * hamiltonIveyConvexMatrixRegionSupportEuclid K τ
    (matrixToEuclid (regionProjMatrix (I := I) g (basisAt x) ν))

noncomputable def regionSupportDeriv
    (g : SmoothRiemannianMetric I M)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    {K : ℝ} (hK : 0 < K) (τ : ℝ) (x : M)
    (ν : Tensor04At (I := I) (M := M) x) : ℝ :=
  4 * hamiltonIveyConvexMatrixRegionSupportDeriv K hK τ
    (matrixToEuclid (regionProjMatrix (I := I) g (basisAt x) ν))

noncomputable def regionSource
    (g : SmoothRiemannianMetric I M)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (x : M) (p ν : Tensor04At (I := I) (M := M) x) : ℝ :=
  4 * inner ℝ
    (uhlenbeckCurvatureOperatorReactionState (matrixToEuclid (regionProjMatrix (I := I) g (basisAt x) p)))
    (matrixToEuclid (regionProjMatrix (I := I) g (basisAt x) ν))

def regionNormalDirections
    (g : SmoothRiemannianMetric I M)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (x : M) : Set (Tensor04At (I := I) (M := M) x) :=
  {ν | (symmEuclid_isHermitian (matrixToEuclid (regionProjMatrix (I := I) g (basisAt x) ν))).eigenvalues₀ 0 < 0 ∨
    symmEuclid (matrixToEuclid (regionProjMatrix (I := I) g (basisAt x) ν)) = 0}

end IntrinsicRegionData

section RegionMatrixLemmas

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
  [SigmaCompactSpace M] [T2Space M] in
theorem regionProjMatrix_eq_curvatureOperatorMatrixAt
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    {A : Tensor04At (I := I) (M := M) x}
    (hA : A ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    regionProjMatrix (I := I) g basis A =
      curvatureOperatorMatrixAt (I := I) x basis ⟨A, hA⟩ := by
  unfold regionProjMatrix
  have heq : fiberProjW (I := I) g x A = ⟨A, hA⟩ := by
    apply Subtype.ext
    exact fiberProjW_self (I := I) g x hA
  rw [heq]

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
  [SigmaCompactSpace M] [T2Space M] in
theorem inner0S_eq_four_mul_inner_regionProjMatrix
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) g x basis)
    {q : Tensor04At (I := I) (M := M) x}
    (hq : q ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (ν : Tensor04At (I := I) (M := M) x) :
    inner0S (I := I) g x 4 q ν =
      4 * inner ℝ (matrixToEuclid (regionProjMatrix (I := I) g basis ν))
        (matrixToEuclid (curvatureOperatorMatrixAt (I := I) x basis ⟨q, hq⟩)) := by
  have hpq := fiberProjW_inner_eq (I := I) g x ν ⟨q, hq⟩
  let pν : algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
    fiberProjW (I := I) g x ν
  have h4 : inner0S (I := I) g x 4 (pν : Tensor04At (I := I) (M := M) x) q =
      4 * inner ℝ (matrixToEuclid (regionProjMatrix (I := I) g basis ν))
        (matrixToEuclid (curvatureOperatorMatrixAt (I := I) x basis ⟨q, hq⟩)) := by
    have hmain := inner0S_algebraic_eq_four_mul_matrixInner (I := I) g x basis horth pν ⟨q, hq⟩
    rw [intrinsicFiberCurvatureOperatorMatrix_eq_curvatureOperatorMatrixAt,
      intrinsicFiberCurvatureOperatorMatrix_eq_curvatureOperatorMatrixAt] at hmain
    have hreg : regionProjMatrix (I := I) g basis ν =
        curvatureOperatorMatrixAt (I := I) x basis pν := by
      rfl
    rw [hreg]
    exact hmain
  calc
    inner0S (I := I) g x 4 q ν
        = inner0S (I := I) g x 4 q (pν : Tensor04At (I := I) (M := M) x) := by
          rw [inner0S, inner0S]
          rw [MetricFiberData.inner_comm (tensor0SMetricData (I := I) g x 4) q ν]
          rw [MetricFiberData.inner_comm (tensor0SMetricData (I := I) g x 4) q (pν : Tensor04At (I := I) (M := M) x)]
          simpa [pν, inner0S] using hpq.symm
    _ = inner0S (I := I) g x 4 (pν : Tensor04At (I := I) (M := M) x) q := by
          rw [inner0S, inner0S]
          exact MetricFiberData.inner_comm (tensor0SMetricData (I := I) g x 4) q (pν : Tensor04At (I := I) (M := M) x)
    _ = 4 * inner ℝ (matrixToEuclid (regionProjMatrix (I := I) g basis ν))
        (matrixToEuclid (curvatureOperatorMatrixAt (I := I) x basis ⟨q, hq⟩)) := by
          simpa [pν, regionProjMatrix, fiberProjW_idem] using h4

theorem symmEuclid_matrixToEuclid_symm
    {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : M.IsSymm) :
    symmEuclid (matrixToEuclid M) = M := by
  unfold symmEuclid
  rw [euclidToMatrix_matrixToEuclid]
  ext i j
  have hs : M i j = M j i := by
    have h := congrFun (congrFun hM i) j
    simpa [Matrix.transpose_apply] using h.symm
  simp [hs]
  ring

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
  [SigmaCompactSpace M] [T2Space M] in
theorem regionSupport_eq_of_mem_algebraic
    (g : SmoothRiemannianMetric I M)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (K τ : ℝ) (x : M) {ν : Tensor04At (I := I) (M := M) x}
    (hν : ν ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    regionSupport (I := I) g basisAt K τ x ν =
      4 * hamiltonIveyConvexMatrixRegionSupportEuclid K τ
        (matrixToEuclid (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨ν, hν⟩)) := by
  unfold regionSupport
  congr 1
  congr 1
  rw [regionProjMatrix_eq_curvatureOperatorMatrixAt (I := I) g (basisAt x) hν]

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
  [SigmaCompactSpace M] [T2Space M] in
omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
theorem fiberHamiltonIveySupport_eq_of_mem_algebraic
    (g : SmoothRiemannianMetric I M)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (K τ : ℝ) (x : M) {ν : Tensor04At (I := I) (M := M) x}
    (hν : ν ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    fiberHamiltonIveySupport g basisAt K τ x ν =
      4 * hamiltonIveyConvexMatrixRegionSupportEuclid K τ
        (matrixToEuclid (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨ν, hν⟩)) := by
  unfold fiberHamiltonIveySupport
  rw [dif_pos hν]

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
  [SigmaCompactSpace M] [T2Space M] in
theorem regionSupport_eq_fiberHamiltonIveySupport_of_mem_algebraic
    (g : SmoothRiemannianMetric I M)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (K τ : ℝ) (x : M) {ν : Tensor04At (I := I) (M := M) x}
    (hν : ν ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    regionSupport (I := I) g basisAt K τ x ν =
      fiberHamiltonIveySupport g basisAt K τ x ν := by
  rw [regionSupport_eq_of_mem_algebraic (I := I) g basisAt K τ x hν,
    fiberHamiltonIveySupport_eq_of_mem_algebraic (I := I) g basisAt K τ x hν]

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
  [SigmaCompactSpace M] [T2Space M] in
theorem mem_regionNormalDirections_iff_mem_fiberNormalDirections
    (g : SmoothRiemannianMetric I M)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (x : M) {ν : Tensor04At (I := I) (M := M) x}
    (hν : ν ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    ν ∈ regionNormalDirections (I := I) g basisAt x ↔
      ν ∈ fiberHamiltonIveyNormalDirections basisAt x := by
  constructor
  · intro h
    rw [fiberHamiltonIveyNormalDirections]
    simp only [Set.mem_setOf_eq]
    refine ⟨hν, ?_⟩
    rcases h with hlt | hz
    · left
      simpa [regionProjMatrix_eq_curvatureOperatorMatrixAt (I := I) g (basisAt x) hν] using hlt
    · right
      simpa [regionProjMatrix_eq_curvatureOperatorMatrixAt (I := I) g (basisAt x) hν] using hz
  · intro h
    rw [fiberHamiltonIveyNormalDirections] at h
    simp only [Set.mem_setOf_eq] at h
    rcases h with ⟨hν', hlt⟩
    -- hν' : ν ∈ submodule, hlt : eigen₀(curvOpMat ⟨ν, hν'⟩) < 0 ∨ ...
    rw [regionNormalDirections]
    simp only [Set.mem_setOf_eq]
    rcases hlt with hlt | hz
    · left
      have hw : curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨ν, hν'⟩ =
          curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨ν, hν⟩ := by
        apply curvatureOperatorMatrixAt_independent_of_witness
      simpa [hw, regionProjMatrix_eq_curvatureOperatorMatrixAt (I := I) g (basisAt x) hν] using hlt
    · right
      have hw : curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨ν, hν'⟩ =
          curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨ν, hν⟩ := by
        apply curvatureOperatorMatrixAt_independent_of_witness
      simpa [hw, regionProjMatrix_eq_curvatureOperatorMatrixAt (I := I) g (basisAt x) hν] using hz

end RegionMatrixLemmas


end DifferentialGeometry.PDE.RicciFlow

end
