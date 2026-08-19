import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.BundleConvex
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.HamiltonIveyIntrinsicTransfer
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.HamiltonIveyIntrinsicContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.HamiltonIveyInnerLaplacian
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.HamiltonIveyCurvatureEvolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.HamiltonIveyFixedFrameEvolution
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Radial
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.SolutionTimeRestrict
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.TensorLoweringParallel
import DifferentialGeometry.Analysis.Calculus.MatrixInverseSmooth
import DifferentialGeometry.Topology.FiberBundleT2

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set Filter
open DifferentialGeometry.Analysis.Convex
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.Variation
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

@[irreducible]
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
      inner0S (I := I) g x 4 ν (q : Tensor04At (I := I) (M := M) x) := by
  simpa [fiberProjW] using (Classical.choose_spec (exists_fiberProjW (I := I) g x ν) q)

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

omit [CompleteSpace E] [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
theorem inner0S_comm (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (A B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x) :
    inner0S (I := I) g x s A B = inner0S (I := I) g x s B A := by
  unfold inner0S
  exact (tensor0SMetricData (I := I) g x s).inner_comm A B

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

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
theorem fiberHamiltonIveySupport_eq_of_mem_algebraic
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (K τ : ℝ) (x : M) {ν : Tensor04At (I := I) (M := M) x}
    (hν : ν ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    fiberHamiltonIveySupport basisAt K τ x ν =
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
      fiberHamiltonIveySupport basisAt K τ x ν := by
  rw [regionSupport_eq_of_mem_algebraic (I := I) g basisAt K τ x hν,
    fiberHamiltonIveySupport_eq_of_mem_algebraic (I := I) basisAt K τ x hν]

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

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
  [SigmaCompactSpace M] [T2Space M] in
theorem sSup_inner0S_proj_eq
    (g : SmoothRiemannianMetric I M)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (K τ : ℝ) (x : M) (ν : Tensor04At (I := I) (M := M) x) :
    sSup {r : ℝ | ∃ q : Tensor04At (I := I) (M := M) x,
        q ∈ fiberHamiltonIveyRegion basisAt K τ x ∧ r = inner0S (I := I) g x 4 q ν} =
      sSup {r : ℝ | ∃ q : Tensor04At (I := I) (M := M) x,
        q ∈ fiberHamiltonIveyRegion basisAt K τ x ∧
          r = inner0S (I := I) g x 4 q (fiberProjW (I := I) g x ν : Tensor04At (I := I) (M := M) x)} := by
  congr 1
  ext r
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨q, hq, ?_⟩
    rw [inner0S_comm (I := I) g x 4 q ν]
    rw [inner0S_comm (I := I) g x 4 q (fiberProjW (I := I) g x ν : Tensor04At (I := I) (M := M) x)]
    rcases hq with ⟨hqalg, hqmat⟩
    exact (fiberProjW_inner_eq (I := I) g x ν ⟨q, hqalg⟩).symm
  · rintro ⟨q, hq, rfl⟩
    refine ⟨q, hq, ?_⟩
    rw [inner0S_comm (I := I) g x 4 q (fiberProjW (I := I) g x ν : Tensor04At (I := I) (M := M) x)]
    rw [inner0S_comm (I := I) g x 4 q ν]
    rcases hq with ⟨hqalg, hqmat⟩
    exact fiberProjW_inner_eq (I := I) g x ν ⟨q, hqalg⟩

end RegionMatrixLemmas

section RegionCharacterization

omit [CompleteSpace E] [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
theorem fiberRegion_mem_iff_forall_normalDirections
    (g : SmoothRiemannianMetric I M)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) g x (basisAt x))
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ) (x : M)
    (p : Tensor04At (I := I) (M := M) x)
    (hp : p ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    p ∈ fiberHamiltonIveyRegion basisAt K τ x ↔
      ∀ ν : Tensor04At (I := I) (M := M) x,
        ν ∈ regionNormalDirections (I := I) g basisAt x →
          inner0S (I := I) g x 4 ν p ≤ regionSupport (I := I) g basisAt K τ x ν := by
  constructor
  · intro hpC ν hν
    let w : EuclideanSpace ℝ (Fin 3 × Fin 3) :=
      matrixToEuclid (regionProjMatrix (I := I) g (basisAt x) ν)
    have hinner : inner0S (I := I) g x 4 ν p =
        4 * inner ℝ w (matrixToEuclid (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨p, hp⟩)) := by
      calc
        inner0S (I := I) g x 4 ν p = inner0S (I := I) g x 4 p ν := by
          exact inner0S_comm (I := I) g x 4 ν p
        _ = 4 * inner ℝ w (matrixToEuclid (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨p, hp⟩)) := by
          simpa [w] using (inner0S_eq_four_mul_inner_regionProjMatrix (I := I) g x (basisAt x) (horth0 x) hp ν)
    have hsupport : regionSupport (I := I) g basisAt K τ x ν =
        4 * hamiltonIveyConvexMatrixRegionSupportEuclid K τ w := by
      rfl
    have hwfs : w ∈ finiteSupportDirections (hamiltonIveyConvexMatrixRegionEuclid K τ) := by
      rw [mem_finiteSupportDirections_hamiltonIvey_region_iff hK hτ w]
      exact hν
    rcases hpC with ⟨hAlg, hmat⟩
    have hpmat : matrixToEuclid (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨p, hp⟩) ∈
        hamiltonIveyConvexMatrixRegionEuclid K τ := by
      rw [mem_hamiltonIveyConvexMatrixRegionEuclid_iff]
      have hw : curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨p, hAlg⟩ =
          curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨p, hp⟩ := by
        apply curvatureOperatorMatrixAt_independent_of_witness
      rwa [hw]
    have hmain := (hamiltonIveyConvexMatrixRegionEuclid_mem_iff_forall_support_le hK hτ
      (matrixToEuclid (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨p, hp⟩))).mp
      hpmat w hwfs
    calc
      inner0S (I := I) g x 4 ν p
          = 4 * inner ℝ w (matrixToEuclid (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨p, hp⟩)) := hinner
      _ ≤ 4 * hamiltonIveyConvexMatrixRegionSupportEuclid K τ w := by
            nlinarith [hmain]
      _ = regionSupport (I := I) g basisAt K τ x ν := hsupport.symm
  · intro hle
    have hback := (fiberHamiltonIveyRegion_mem_iff_forall_support_le (I := I) g basisAt horth0 hK hτ x p hp).mpr
    apply hback
    intro ν hν
    rcases hν with ⟨hνalg, hc⟩
    have hνN : ν ∈ regionNormalDirections (I := I) g basisAt x := by
      exact (mem_regionNormalDirections_iff_mem_fiberNormalDirections (I := I) g basisAt x hνalg).mpr ⟨hνalg, hc⟩
    have hle' := hle ν hνN
    have hsup : regionSupport (I := I) g basisAt K τ x ν =
        fiberHamiltonIveySupport basisAt K τ x ν := by
      exact regionSupport_eq_fiberHamiltonIveySupport_of_mem_algebraic (I := I) g basisAt K τ x hνalg
    rw [inner0S_comm (I := I) g x 4 ν p] at hle'
    rw [← hsup]
    exact hle'

omit [CompleteSpace E] [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
theorem regionSupport_eq_sSup
    (g : SmoothRiemannianMetric I M)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) g x (basisAt x))
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ) (x : M)
    {ν : Tensor04At (I := I) (M := M) x}
    (hν : ν ∈ regionNormalDirections (I := I) g basisAt x) :
    regionSupport (I := I) g basisAt K τ x ν =
      sSup {r : ℝ | ∃ q : Tensor04At (I := I) (M := M) x,
        q ∈ fiberHamiltonIveyRegion basisAt K τ x ∧ r = inner0S (I := I) g x 4 q ν} := by
  have hν₀alg : (fiberProjW (I := I) g x ν : Tensor04At (I := I) (M := M) x) ∈
      algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
    (fiberProjW (I := I) g x ν).2
  have hreg : regionProjMatrix (I := I) g (basisAt x)
        (fiberProjW (I := I) g x ν : Tensor04At (I := I) (M := M) x) =
      regionProjMatrix (I := I) g (basisAt x) ν := by
    unfold regionProjMatrix
    have hself : fiberProjW (I := I) g x
          (fiberProjW (I := I) g x ν : Tensor04At (I := I) (M := M) x) =
        fiberProjW (I := I) g x ν := by
      apply Subtype.ext
      exact fiberProjW_self (I := I) g x (fiberProjW (I := I) g x ν).2
    rw [hself]
  have hν₀N : (fiberProjW (I := I) g x ν : Tensor04At (I := I) (M := M) x) ∈
      fiberHamiltonIveyNormalDirections basisAt x := by
    exact (mem_regionNormalDirections_iff_mem_fiberNormalDirections (I := I) g basisAt x hν₀alg).mp
      (by
        rw [regionNormalDirections]
        simp only [Set.mem_setOf_eq]
        simpa [hreg] using hν)
  have hmain := fiberHamiltonIveySupport_eq_sSup (I := I) g basisAt horth0 hK hτ x hν₀N
  have hsup : fiberHamiltonIveySupport basisAt K τ x
        (fiberProjW (I := I) g x ν : Tensor04At (I := I) (M := M) x) =
      regionSupport (I := I) g basisAt K τ x ν := by
    unfold regionSupport fiberHamiltonIveySupport
    rw [dif_pos hν₀alg]
    rw [← hreg]
    rw [regionProjMatrix_eq_curvatureOperatorMatrixAt (I := I) g (basisAt x) hν₀alg]
  calc
    regionSupport (I := I) g basisAt K τ x ν
        = fiberHamiltonIveySupport basisAt K τ x
            (fiberProjW (I := I) g x ν : Tensor04At (I := I) (M := M) x) := hsup.symm
    _ = sSup {r : ℝ | ∃ q : Tensor04At (I := I) (M := M) x,
          q ∈ fiberHamiltonIveyRegion basisAt K τ x ∧
            r = inner0S (I := I) g x 4 q (fiberProjW (I := I) g x ν : Tensor04At (I := I) (M := M) x)} := hmain
    _ = sSup {r : ℝ | ∃ q : Tensor04At (I := I) (M := M) x,
          q ∈ fiberHamiltonIveyRegion basisAt K τ x ∧ r = inner0S (I := I) g x 4 q ν} := by
          congr 1
          ext r
          constructor <;> rintro ⟨q, hq, rfl⟩ <;> refine ⟨q, hq, ?_⟩
          · rw [inner0S_comm (I := I) g x 4 q ν]
            rw [inner0S_comm (I := I) g x 4 q (fiberProjW (I := I) g x ν : Tensor04At (I := I) (M := M) x)]
            rcases hq with ⟨hqalg, hqmat⟩
            exact fiberProjW_inner_eq (I := I) g x ν ⟨q, hqalg⟩
          · rw [inner0S_comm (I := I) g x 4 q (fiberProjW (I := I) g x ν : Tensor04At (I := I) (M := M) x)]
            rw [inner0S_comm (I := I) g x 4 q ν]
            rcases hq with ⟨hqalg, hqmat⟩
            exact (fiberProjW_inner_eq (I := I) g x ν ⟨q, hqalg⟩).symm

omit [CompleteSpace E] [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
theorem regionNormalDirections_of_normal
    (g : SmoothRiemannianMetric I M)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) g x (basisAt x))
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ) (x : M)
    {p : Tensor04At (I := I) (M := M) x}
    (hp : p ∈ fiberHamiltonIveyRegion basisAt K τ x)
    {ν : Tensor04At (I := I) (M := M) x}
    (hnormal : ∀ q : Tensor04At (I := I) (M := M) x,
      q ∈ fiberHamiltonIveyRegion basisAt K τ x → inner0S (I := I) g x 4 ν (q - p) ≤ 0) :
    ν ∈ regionNormalDirections (I := I) g basisAt x := by
  let pν : algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
    fiberProjW (I := I) g x ν
  have hν₀alg : (pν : Tensor04At (I := I) (M := M) x) ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
    pν.2
  have hnormal' : ∀ q : Tensor04At (I := I) (M := M) x,
      q ∈ fiberHamiltonIveyRegion basisAt K τ x → inner0S (I := I) g x 4 (pν : Tensor04At (I := I) (M := M) x) (q - p) ≤ 0 := by
    intro q hq
    have h1 := hnormal q hq
    rcases hq with ⟨hqalg, hqmat⟩
    rcases hp with ⟨hpalg, hpmat⟩
    have h2 : inner0S (I := I) g x 4 (pν : Tensor04At (I := I) (M := M) x) (q - p) =
        inner0S (I := I) g x 4 ν (q - p) := by
      exact fiberProjW_inner_eq (I := I) g x ν
        ⟨(q - p), Submodule.sub_mem (algebraicCurvatureTensorSubmodule (I := I) (M := M) x) hqalg hpalg⟩
    rwa [h2]
  have hν₀N : (pν : Tensor04At (I := I) (M := M) x) ∈ fiberHamiltonIveyNormalDirections basisAt x :=
    fiberHamiltonIveyRegion_normal (I := I) g basisAt horth0 hK hτ x hν₀alg hnormal'
  have hν₀R : (pν : Tensor04At (I := I) (M := M) x) ∈ regionNormalDirections (I := I) g basisAt x :=
    (mem_regionNormalDirections_iff_mem_fiberNormalDirections (I := I) g basisAt x hν₀alg).mpr hν₀N
  rw [regionNormalDirections] at hν₀R ⊢
  simp only [Set.mem_setOf_eq] at hν₀R ⊢
  have hreg : regionProjMatrix (I := I) g (basisAt x) (pν : Tensor04At (I := I) (M := M) x) =
      regionProjMatrix (I := I) g (basisAt x) ν := by
    unfold regionProjMatrix
    have hself : fiberProjW (I := I) g x (pν : Tensor04At (I := I) (M := M) x) = pν := by
      apply Subtype.ext
      exact fiberProjW_self (I := I) g x pν.2
    rw [hself]
  simpa [hreg] using hν₀R

end RegionCharacterization

section RegionSupportTime

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
  [SigmaCompactSpace M] [T2Space M] in
theorem regionSupport_continuousOn_time
    (g : SmoothRiemannianMetric I M)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    {K T : ℝ} (hK : 0 < K) (x : M) (ν : Tensor04At (I := I) (M := M) x) :
    ContinuousOn (fun τ : ℝ => regionSupport (I := I) g basisAt K τ x ν) (Set.Icc 0 T) := by
  let w : EuclideanSpace ℝ (Fin 3 × Fin 3) :=
    matrixToEuclid (regionProjMatrix (I := I) g (basisAt x) ν)
  by_cases hlt : (symmEuclid_isHermitian w).eigenvalues₀ 0 < 0
  · have hmain := hamiltonIveyConvexMatrixRegionSupportEuclid_continuousOn (K := K) (T := T) hK w hlt
    have hmain4 : ContinuousOn (fun τ : ℝ => 4 * hamiltonIveyConvexMatrixRegionSupportEuclid K τ w)
        (Set.Icc 0 T) := hmain.const_mul 4
    have hfun : (fun τ : ℝ => regionSupport (I := I) g basisAt K τ x ν) =
        fun τ : ℝ => 4 * hamiltonIveyConvexMatrixRegionSupportEuclid K τ w := by
      funext τ
      simp [regionSupport, w]
    simpa [hfun] using hmain4
  · have hconst : ∀ τ : ℝ, regionSupport (I := I) g basisAt K τ x ν = 0 := by
      intro τ
      unfold regionSupport hamiltonIveyConvexMatrixRegionSupportEuclid
      rw [if_neg hlt]
      simp
    have hconst0 : (fun τ : ℝ => regionSupport (I := I) g basisAt K τ x ν) =
        fun _ : ℝ => 0 := by
      funext τ
      exact hconst τ
    simpa [hconst0] using (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Set.Icc 0 T))

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
  [SigmaCompactSpace M] [T2Space M] in
theorem regionSupport_hasDerivAt_time
    (g : SmoothRiemannianMetric I M)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    {K : ℝ} (hK : 0 < K) {t : ℝ} (ht : 0 < t) (x : M) (ν : Tensor04At (I := I) (M := M) x) :
    HasDerivAt (fun τ : ℝ => regionSupport (I := I) g basisAt K τ x ν)
      (regionSupportDeriv (I := I) g basisAt hK t x ν) t := by
  let w : EuclideanSpace ℝ (Fin 3 × Fin 3) :=
    matrixToEuclid (regionProjMatrix (I := I) g (basisAt x) ν)
  by_cases hlt : (symmEuclid_isHermitian w).eigenvalues₀ 0 < 0
  · have hmain := hamiltonIveyConvexMatrixRegionSupportEuclid_hasDerivAt hK ht w
    have hmain4 : HasDerivAt (fun τ : ℝ => 4 * hamiltonIveyConvexMatrixRegionSupportEuclid K τ w)
        (4 * hamiltonIveyConvexMatrixRegionSupportDeriv K hK t w) t := hmain.const_mul 4
    have hfun : (fun τ : ℝ => regionSupport (I := I) g basisAt K τ x ν) =
        fun τ : ℝ => 4 * hamiltonIveyConvexMatrixRegionSupportEuclid K τ w := by
      funext τ
      simp [regionSupport, w]
    have hmain4' : HasDerivAt (fun τ : ℝ => regionSupport (I := I) g basisAt K τ x ν)
        (4 * hamiltonIveyConvexMatrixRegionSupportDeriv K hK t w) t := by
      simpa [hfun] using hmain4
    simpa [regionSupportDeriv, w] using hmain4'
  · have hnot : ¬ (symmEuclid_isHermitian w).eigenvalues₀ 0 < 0 := hlt
    have hconst : ∀ τ : ℝ, regionSupport (I := I) g basisAt K τ x ν = 0 := by
      intro τ
      unfold regionSupport hamiltonIveyConvexMatrixRegionSupportEuclid
      rw [if_neg hlt]
      simp
    have hmain : HasDerivAt (fun τ : ℝ => regionSupport (I := I) g basisAt K τ x ν) 0 t := by
      simpa [hconst] using (hasDerivAt_const (x := t) (c := (0 : ℝ)))
    have hz : regionSupportDeriv (I := I) g basisAt hK t x ν = 0 := by
      unfold regionSupportDeriv hamiltonIveyConvexMatrixRegionSupportDeriv
      rw [if_neg hnot]
      simp
    simpa [hz] using hmain

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
  [SigmaCompactSpace M] [T2Space M] in
theorem regionSource_le_regionSupportDeriv_of_tangent
    (g : SmoothRiemannianMetric I M)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) g x (basisAt x))
    {K t : ℝ} (hK : 0 < K) (ht : 0 < t) (x : M)
    {p ν : Tensor04At (I := I) (M := M) x}
    (hp : p ∈ fiberHamiltonIveyRegion basisAt K t x)
    (hν : ν ∈ regionNormalDirections (I := I) g basisAt x)
    (htangent : regionSupport (I := I) g basisAt K t x ν = inner0S (I := I) g x 4 ν p) :
    regionSource (I := I) g basisAt x p ν ≤
      regionSupportDeriv (I := I) g basisAt hK t x ν := by
  rcases hp with ⟨hpalg, hpmat⟩
  let w : EuclideanSpace ℝ (Fin 3 × Fin 3) :=
    matrixToEuclid (regionProjMatrix (I := I) g (basisAt x) ν)
  let A : EuclideanSpace ℝ (Fin 3 × Fin 3) :=
    matrixToEuclid (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨p, hpalg⟩)
  have hA : A ∈ hamiltonIveyConvexMatrixRegionEuclid K t := by
    rw [mem_hamiltonIveyConvexMatrixRegionEuclid_iff]
    simpa [A, euclidToMatrix_matrixToEuclid] using hpmat
  have hinner : inner0S (I := I) g x 4 ν p = 4 * inner ℝ w A := by
    calc
      inner0S (I := I) g x 4 ν p = inner0S (I := I) g x 4 p ν := by
        exact inner0S_comm (I := I) g x 4 ν p
      _ = 4 * inner ℝ (matrixToEuclid (regionProjMatrix (I := I) g (basisAt x) ν))
          (matrixToEuclid (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨p, hpalg⟩)) := by
        exact inner0S_eq_four_mul_inner_regionProjMatrix (I := I) g x (basisAt x) (horth0 x) hpalg ν
  have hsupport : regionSupport (I := I) g basisAt K t x ν = 4 * hamiltonIveyConvexMatrixRegionSupportEuclid K t w := by
    rfl
  have htouching : hamiltonIveyConvexMatrixRegionSupportEuclid K t w = inner ℝ w A := by
    have h4 : 4 * hamiltonIveyConvexMatrixRegionSupportEuclid K t w = 4 * inner ℝ w A := by
      rw [← hsupport, ← hinner]
      exact htangent
    nlinarith
  rcases hν with hlt | hz
  · have hmain := hamiltonIveyConvexMatrixRegionSupportEuclid_reaction_le_deriv hK (le_of_lt ht) w hlt A hA htouching
      (hamiltonIveyConvexMatrixRegionSupportDeriv K hK t w)
      (hamiltonIveyConvexMatrixRegionSupportEuclid_hasDerivAt hK ht w)
    have hsource : regionSource (I := I) g basisAt x p ν =
        4 * inner ℝ (uhlenbeckCurvatureOperatorReactionState A) w := by
      unfold regionSource
      rw [regionProjMatrix_eq_curvatureOperatorMatrixAt (I := I) g (basisAt x) hpalg]
    have hderiv : regionSupportDeriv (I := I) g basisAt hK t x ν =
        4 * hamiltonIveyConvexMatrixRegionSupportDeriv K hK t w := by
      rfl
    rw [hsource, hderiv]
    exact mul_le_mul_of_nonneg_left hmain (by norm_num)
  · have hsymm0 : symmEuclid w = 0 := by
      change symmEuclid (matrixToEuclid (regionProjMatrix (I := I) g (basisAt x) ν)) = 0
      exact hz
    have hw0 : w = 0 := by
      have hwreg : euclidToMatrix w = regionProjMatrix (I := I) g (basisAt x) ν := by
        rw [euclidToMatrix_matrixToEuclid]
      have hM : (euclidToMatrix w).IsSymm := by
        rw [hwreg]
        have hherm : (curvatureOperatorMatrixAt (I := I) x (basisAt x)
            (fiberProjW (I := I) g x ν)).IsHermitian := by
          exact curvatureOperatorMatrixAt_isHermitian x (basisAt x) (fiberProjW (I := I) g x ν)
        exact Matrix.IsSymm.ext (fun i j => by
          have hh := congrFun (congrFun hherm i) j
          simpa [Matrix.conjTranspose, star_trivial] using hh)
      have hzeroM : euclidToMatrix w = 0 := by
        have h := symmEuclid_matrixToEuclid_symm (M := euclidToMatrix w) hM
        rw [matrixToEuclid_euclidToMatrix] at h
        rw [hsymm0] at h
        exact h.symm
      rw [← matrixToEuclid_euclidToMatrix w, hzeroM]
      ext ij
      simp [matrixToEuclid]
    have hsource0 : regionSource (I := I) g basisAt x p ν = 0 := by
      rw [regionSource]
      rw [show matrixToEuclid (regionProjMatrix (I := I) g (basisAt x) ν) = w from rfl, hw0]
      simp
    have hderiv0 : regionSupportDeriv (I := I) g basisAt hK t x ν = 0 := by
      rw [regionSupportDeriv]
      rw [show matrixToEuclid (regionProjMatrix (I := I) g (basisAt x) ν) = w from rfl]
      rw [hamiltonIveyConvexMatrixRegionSupportDeriv_eq_zero_of_symm_zero hK t w hsymm0]
      simp
    rw [hsource0, hderiv0]

end RegionSupportTime

section FiberRegionTopology

omit [CompleteSpace E] [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
theorem continuous_tensor04StdAt_eval (x : M) (X Y Z W : TangentSpace I x) :
    Continuous (fun A : Tensor04At (I := I) (M := M) x => tensor04StdAt (I := I) (M := M) A X Y Z W) := by
  let g : Tensor04At (I := I) (M := M) x →ₗ[ℝ] ℝ :=
    { toFun := fun A => tensor04StdAt (I := I) (M := M) A X Y Z W
      map_add' := by
        intro A B
        change tensor04StdAt (I := I) (M := M) (A + B) X Y Z W =
          tensor04StdAt (I := I) (M := M) A X Y Z W + tensor04StdAt (I := I) (M := M) B X Y Z W
        simp [Tensor0SSpace.add_apply]
      map_smul' := by
        intro c A
        change tensor04StdAt (I := I) (M := M) (c • A) X Y Z W =
          c * tensor04StdAt (I := I) (M := M) A X Y Z W
        simp [Tensor0SSpace.smul_apply, smul_eq_mul] }
  haveI : FiniteDimensional ℝ (Tensor04At (I := I) (M := M) x) := by
    change FiniteDimensional ℝ (Tensor0SSpace 4 I x)
    exact tensor0SSpace_finiteDimensional 4 x
  exact g.continuous_of_finiteDimensional

omit [CompleteSpace E] [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
omit [CompleteSpace E] [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
theorem isClosed_algebraicCurvatureTensorSubmodule (x : M) :
    IsClosed (algebraicCurvatureTensorSubmodule (I := I) (M := M) x : Set (Tensor04At (I := I) (M := M) x)) := by
  have hEq : (algebraicCurvatureTensorSubmodule (I := I) (M := M) x : Set (Tensor04At (I := I) (M := M) x)) =
      {A | (∀ X Y Z W : TangentSpace I x,
          tensor04StdAt (I := I) (M := M) A X Y Z W = -tensor04StdAt (I := I) (M := M) A Y X Z W) ∧
        (∀ X Y Z W : TangentSpace I x,
          tensor04StdAt (I := I) (M := M) A X Y Z W = -tensor04StdAt (I := I) (M := M) A X Y W Z) ∧
        (∀ X Y Z W : TangentSpace I x,
          tensor04StdAt (I := I) (M := M) A X Y Z W +
            tensor04StdAt (I := I) (M := M) A Y Z X W +
            tensor04StdAt (I := I) (M := M) A Z X Y W = 0)} := by
    ext A
    exact mem_algebraicCurvatureTensorSubmodule_iff_symmetries (I := I) (M := M)
  rw [hEq]
  have hanti1 : IsClosed {A : Tensor04At (I := I) (M := M) x | ∀ X Y Z W : TangentSpace I x,
      tensor04StdAt (I := I) (M := M) A X Y Z W = -tensor04StdAt (I := I) (M := M) A Y X Z W} := by
    rw [show {A : Tensor04At (I := I) (M := M) x | ∀ X Y Z W : TangentSpace I x,
          tensor04StdAt (I := I) (M := M) A X Y Z W = -tensor04StdAt (I := I) (M := M) A Y X Z W} =
        ⋂ X : TangentSpace I x, ⋂ Y : TangentSpace I x, ⋂ Z : TangentSpace I x,
          ⋂ W : TangentSpace I x, {A : Tensor04At (I := I) (M := M) x |
            tensor04StdAt (I := I) (M := M) A X Y Z W + tensor04StdAt (I := I) (M := M) A Y X Z W = 0} from by
      ext A
      simp [eq_neg_iff_add_eq_zero]]
    exact isClosed_iInter (fun X => isClosed_iInter (fun Y => isClosed_iInter (fun Z => isClosed_iInter (fun W =>
      isClosed_eq ((continuous_tensor04StdAt_eval x X Y Z W).add (continuous_tensor04StdAt_eval x Y X Z W))
        continuous_const))))
  have hanti2 : IsClosed {A : Tensor04At (I := I) (M := M) x | ∀ X Y Z W : TangentSpace I x,
      tensor04StdAt (I := I) (M := M) A X Y Z W = -tensor04StdAt (I := I) (M := M) A X Y W Z} := by
    rw [show {A : Tensor04At (I := I) (M := M) x | ∀ X Y Z W : TangentSpace I x,
          tensor04StdAt (I := I) (M := M) A X Y Z W = -tensor04StdAt (I := I) (M := M) A X Y W Z} =
        ⋂ X : TangentSpace I x, ⋂ Y : TangentSpace I x, ⋂ Z : TangentSpace I x,
          ⋂ W : TangentSpace I x, {A : Tensor04At (I := I) (M := M) x |
            tensor04StdAt (I := I) (M := M) A X Y Z W + tensor04StdAt (I := I) (M := M) A X Y W Z = 0} from by
      ext A
      simp [eq_neg_iff_add_eq_zero]]
    exact isClosed_iInter (fun X => isClosed_iInter (fun Y => isClosed_iInter (fun Z => isClosed_iInter (fun W =>
      isClosed_eq ((continuous_tensor04StdAt_eval x X Y Z W).add (continuous_tensor04StdAt_eval x X Y W Z))
        continuous_const))))
  have hbianchi : IsClosed {A : Tensor04At (I := I) (M := M) x | ∀ X Y Z W : TangentSpace I x,
      tensor04StdAt (I := I) (M := M) A X Y Z W + tensor04StdAt (I := I) (M := M) A Y Z X W +
        tensor04StdAt (I := I) (M := M) A Z X Y W = 0} := by
    rw [show {A : Tensor04At (I := I) (M := M) x | ∀ X Y Z W : TangentSpace I x,
          tensor04StdAt (I := I) (M := M) A X Y Z W + tensor04StdAt (I := I) (M := M) A Y Z X W +
            tensor04StdAt (I := I) (M := M) A Z X Y W = 0} =
        ⋂ X : TangentSpace I x, ⋂ Y : TangentSpace I x, ⋂ Z : TangentSpace I x,
          ⋂ W : TangentSpace I x, {A : Tensor04At (I := I) (M := M) x |
            tensor04StdAt (I := I) (M := M) A X Y Z W + tensor04StdAt (I := I) (M := M) A Y Z X W +
              tensor04StdAt (I := I) (M := M) A Z X Y W = 0} from by
      ext A
      simp]
    exact isClosed_iInter (fun X => isClosed_iInter (fun Y => isClosed_iInter (fun Z => isClosed_iInter (fun W =>
      isClosed_eq (((continuous_tensor04StdAt_eval x X Y Z W).add (continuous_tensor04StdAt_eval x Y Z X W)).add
        (continuous_tensor04StdAt_eval x Z X Y W)) continuous_const))))
  exact hanti1.inter (hanti2.inter hbianchi)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
theorem convex_fiberHamiltonIveyRegion
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ) (x : M) :
    Convex ℝ (fiberHamiltonIveyRegion basisAt K τ x) := by
  let f : Tensor04At (I := I) (M := M) x →ₗ[ℝ] EuclideanSpace ℝ (Fin 3 × Fin 3) :=
    { toFun := fun A => matrixToEuclid (intrinsicFiberCurvatureOperatorMatrix (I := I) (basisAt x) A)
      map_add' := by
        intro A B
        ext ij
        simp [matrixToEuclid, intrinsicFiberCurvatureOperatorMatrix]
      map_smul' := by
        intro c A
        ext ij
        simp [matrixToEuclid, intrinsicFiberCurvatureOperatorMatrix] }
  have hpre : Convex ℝ (f ⁻¹' hamiltonIveyConvexMatrixRegionEuclid K τ) :=
    Convex.linear_preimage (convex_hamiltonIveyConvexMatrixRegionEuclid hK hτ) f
  have hEq : intrinsicFiberHamiltonIveyRegion (I := I) basisAt K τ x =
      fiberHamiltonIveyRegion basisAt K τ x :=
    intrinsicFiberHamiltonIveyRegion_eq_fiberHamiltonIveyRegion (I := I) basisAt K τ x
  rw [← hEq]
  rw [intrinsicFiberHamiltonIveyRegion]
  change Convex ℝ ((algebraicCurvatureTensorSubmodule (I := I) (M := M) x : Set (Tensor04At (I := I) (M := M) x)) ∩
    {A | matrixToEuclid (intrinsicFiberCurvatureOperatorMatrix (I := I) (basisAt x) A) ∈ hamiltonIveyConvexMatrixRegionEuclid K τ})
  exact (Submodule.convex (algebraicCurvatureTensorSubmodule (I := I) (M := M) x)).inter hpre

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
theorem nonempty_fiberHamiltonIveyRegion
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ) (x : M) :
    (fiberHamiltonIveyRegion basisAt K τ x).Nonempty := by
  refine ⟨0, ?_⟩
  rw [fiberHamiltonIveyRegion]
  refine ⟨by simp, ?_⟩
  simpa [curvatureOperatorMatrixAt] using (zero_mem_hamiltonIveyConvexMatrixRegion hK hτ)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
theorem zero_mem_fiberHamiltonIveyRegion
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ) (x : M) :
    (0 : Tensor04At (I := I) (M := M) x) ∈ fiberHamiltonIveyRegion basisAt K τ x := by
  rw [fiberHamiltonIveyRegion]
  refine ⟨by simp, ?_⟩
  simpa [curvatureOperatorMatrixAt] using (zero_mem_hamiltonIveyConvexMatrixRegion hK hτ)

end FiberRegionTopology

section PulledScalarization

noncomputable def regionSupportVector
    (g : SmoothRiemannianMetric I M)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (x : M) (ν : Tensor04At (I := I) (M := M) x) : EuclideanSpace ℝ (Fin 3 × Fin 3) :=
  matrixToEuclid (regionProjMatrix (I := I) g (basisAt x) ν)

noncomputable def pulledRmComp
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (iota : MatrixComp M (Fin 3)) : FourComp M (Fin 3) :=
  fun t x a b c d => tensor04StdAt (uhlenbeckPulledRm04At S basisAt iota t x)
    (basisAt x a) (basisAt x b) (basisAt x c) (basisAt x d)

noncomputable def uhlenbeckPullbackTensorAt
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (iota : MatrixComp M (Fin 3)) (t : ℝ) (x : M)
    (A : Tensor04At (I := I) (M := M) x) : Tensor04At (I := I) (M := M) x :=
  A.compContinuousLinearMap (fun _ : Fin 4 => uhlenbeckEndomorphismAt (basisAt x) iota t)

omit [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] in
theorem pulledMatrix_eq_curvatureOperatorMatrixAt
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (iota : MatrixComp M (Fin 3)) (t : ℝ) (x : M)
    (hAlg : uhlenbeckPulledRm04At S basisAt iota t x ∈
      algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    uhlenbeckCurvatureOperatorMatrix (pulledRmComp S basisAt iota) t x =
      matrixToEuclid (curvatureOperatorMatrixAt (I := I) x (basisAt x)
        ⟨uhlenbeckPulledRm04At S basisAt iota t x, hAlg⟩) := by
  have hmain := uhlenbeckCurvatureOperatorMatrixAsMatrix_eq_curvatureOperatorMatrixAt
    (I := I) (M := M) (x := x) (basis := basisAt x)
    (A := ⟨uhlenbeckPulledRm04At S basisAt iota t x, hAlg⟩)
    (pulledRm := pulledRmComp S basisAt iota) (t := t)
    (by intro a b c d; rfl)
  rw [← hmain]
  unfold matrixToEuclid uhlenbeckCurvatureOperatorMatrixAsMatrix
    uhlenbeckCurvatureOperatorMatrix pulledRmComp
  rfl

omit [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] in
theorem pulledScalarization_eq
    (g : SmoothRiemannianMetric I M)
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (iota : MatrixComp M (Fin 3)) (t : ℝ) (x : M)
    (horth : OrthonormalBasisAt (I := I) g x (basisAt x))
    (hAlg : uhlenbeckPulledRm04At S basisAt iota t x ∈
      algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (ν : Tensor04At (I := I) (M := M) x) :
    inner0S (I := I) g x 4 (uhlenbeckPulledRm04At S basisAt iota t x) ν =
      4 * inner ℝ (uhlenbeckCurvatureOperatorMatrix (pulledRmComp S basisAt iota) t x)
        (regionSupportVector g basisAt x ν) := by
  have hmain := inner0S_eq_four_mul_inner_regionProjMatrix (I := I) g x (basisAt x) horth hAlg ν
  rw [← pulledMatrix_eq_curvatureOperatorMatrixAt (I := I) (M := M) S basisAt iota t x hAlg] at hmain
  rw [real_inner_comm] at hmain
  simpa [regionSupportVector] using hmain

omit [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] in
theorem regionSource_at_pulled_eq
    (g : SmoothRiemannianMetric I M)
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (iota : MatrixComp M (Fin 3)) (t : ℝ) (x : M)
    (hAlg : uhlenbeckPulledRm04At S basisAt iota t x ∈
      algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (ν : Tensor04At (I := I) (M := M) x) :
    regionSource g basisAt x (uhlenbeckPulledRm04At S basisAt iota t x) ν =
      4 * inner ℝ (uhlenbeckCurvatureOperatorReactionState
        (uhlenbeckCurvatureOperatorMatrix (pulledRmComp S basisAt iota) t x))
        (regionSupportVector g basisAt x ν) := by
  have hreg : regionProjMatrix (I := I) g (basisAt x) (uhlenbeckPulledRm04At S basisAt iota t x) =
      curvatureOperatorMatrixAt (I := I) x (basisAt x)
        ⟨uhlenbeckPulledRm04At S basisAt iota t x, hAlg⟩ :=
    regionProjMatrix_eq_curvatureOperatorMatrixAt (I := I) g (basisAt x) hAlg
  unfold regionSource
  rw [hreg]
  rw [← pulledMatrix_eq_curvatureOperatorMatrixAt (I := I) (M := M) S basisAt iota t x hAlg]
  simp [regionSupportVector]

omit [CompleteSpace E] [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
theorem inner0S_add_left (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (A B C : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x) :
    inner0S (I := I) g x s (A + B) C =
      inner0S (I := I) g x s A C + inner0S (I := I) g x s B C := by
  let D : MetricFiberData (Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x) :=
    tensor0SMetricData (I := I) g x s
  change D.flat (A + B) C = D.flat A C + D.flat B C
  have hmap : D.flat (A + B) = D.flat A + D.flat B :=
    LinearMap.map_add (D.flat : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x →ₗ[ℝ]
      Module.Dual ℝ (Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)) A B
  have h := congrArg (fun (f : Module.Dual ℝ (Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)) => f C) hmap
  simp [LinearMap.add_apply]

omit [CompleteSpace E] [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
theorem inner0S_add_right (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (A B C : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x) :
    inner0S (I := I) g x s A (B + C) =
      inner0S (I := I) g x s A B + inner0S (I := I) g x s A C := by
  calc
    inner0S (I := I) g x s A (B + C) = inner0S (I := I) g x s (B + C) A :=
      inner0S_comm (I := I) g x s A (B + C)
    _ = inner0S (I := I) g x s B A + inner0S (I := I) g x s C A :=
      inner0S_add_left (I := I) g x s B C A
    _ = inner0S (I := I) g x s A B + inner0S (I := I) g x s A C := by
      rw [inner0S_comm (I := I) g x s B A, inner0S_comm (I := I) g x s C A]

omit [CompleteSpace E] [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
theorem inner0S_sub_left (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (A B C : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x) :
    inner0S (I := I) g x s (A - B) C =
      inner0S (I := I) g x s A C - inner0S (I := I) g x s B C := by
  let D : MetricFiberData (Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x) :=
    tensor0SMetricData (I := I) g x s
  change D.flat (A - B) C = D.flat A C - D.flat B C
  have hmap : D.flat (A - B) = D.flat A - D.flat B :=
    LinearMap.map_sub (D.flat : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x →ₗ[ℝ]
      Module.Dual ℝ (Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)) A B
  have h := congrArg (fun (f : Module.Dual ℝ (Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)) => f C) hmap
  simp [LinearMap.sub_apply]

omit [CompleteSpace E] [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
theorem fiberProjW_sub
    (g : SmoothRiemannianMetric I M) (x : M)
    (ν₁ ν₂ : Tensor04At (I := I) (M := M) x) :
    (fiberProjW (I := I) g x (ν₁ - ν₂) : Tensor04At (I := I) (M := M) x) =
      (fiberProjW (I := I) g x ν₁ : Tensor04At (I := I) (M := M) x) -
        (fiberProjW (I := I) g x ν₂ : Tensor04At (I := I) (M := M) x) := by
  let W : Submodule ℝ (Tensor04At (I := I) (M := M) x) :=
    algebraicCurvatureTensorSubmodule (I := I) (M := M) x
  let d : W := fiberProjW (I := I) g x (ν₁ - ν₂) - fiberProjW (I := I) g x ν₁ + fiberProjW (I := I) g x ν₂
  have hchar : ∀ q : W, inner0S (I := I) g x 4 (d : Tensor04At (I := I) (M := M) x) q = 0 := by
    intro q
    have h1 := fiberProjW_spec (I := I) g x (ν₁ - ν₂) q
    have h2 := fiberProjW_spec (I := I) g x ν₁ q
    have h3 := fiberProjW_spec (I := I) g x ν₂ q
    have h12 : inner0S (I := I) g x 4 (ν₁ - ν₂) (q : Tensor04At (I := I) (M := M) x) =
          inner0S (I := I) g x 4 ν₁ (q : Tensor04At (I := I) (M := M) x) -
            inner0S (I := I) g x 4 ν₂ (q : Tensor04At (I := I) (M := M) x) :=
        inner0S_sub_left (I := I) g x 4 ν₁ ν₂ (q : Tensor04At (I := I) (M := M) x)
    have hdq : inner0S (I := I) g x 4 (d : Tensor04At (I := I) (M := M) x) q =
        inner0S (I := I) g x 4 (fiberProjW (I := I) g x (ν₁ - ν₂) : Tensor04At (I := I) (M := M) x) q -
          inner0S (I := I) g x 4 (fiberProjW (I := I) g x ν₁ : Tensor04At (I := I) (M := M) x) q +
            inner0S (I := I) g x 4 (fiberProjW (I := I) g x ν₂ : Tensor04At (I := I) (M := M) x) q := by
      dsimp [d]
      change inner0S (I := I) g x 4
          ((fiberProjW (I := I) g x (ν₁ - ν₂) : Tensor04At (I := I) (M := M) x) -
            (fiberProjW (I := I) g x ν₁ : Tensor04At (I := I) (M := M) x) +
            (fiberProjW (I := I) g x ν₂ : Tensor04At (I := I) (M := M) x)) (q : Tensor04At (I := I) (M := M) x) =
        inner0S (I := I) g x 4 (fiberProjW (I := I) g x (ν₁ - ν₂) : Tensor04At (I := I) (M := M) x) (q : Tensor04At (I := I) (M := M) x) -
          inner0S (I := I) g x 4 (fiberProjW (I := I) g x ν₁ : Tensor04At (I := I) (M := M) x) (q : Tensor04At (I := I) (M := M) x) +
            inner0S (I := I) g x 4 (fiberProjW (I := I) g x ν₂ : Tensor04At (I := I) (M := M) x) (q : Tensor04At (I := I) (M := M) x)
      rw [inner0S_add_left (I := I) g x 4, inner0S_sub_left (I := I) g x 4]
    have hsub : inner0S (I := I) g x 4
        ((fiberProjW (I := I) g x (ν₁ - ν₂) : Tensor04At (I := I) (M := M) x) - ν₁ + ν₂) q = 0 := by
      change inner0S (I := I) g x 4
          ((fiberProjW (I := I) g x (ν₁ - ν₂) : Tensor04At (I := I) (M := M) x) - ν₁ + ν₂) (q : Tensor04At (I := I) (M := M) x) = 0
      rw [inner0S_add_left (I := I) g x 4, inner0S_sub_left (I := I) g x 4]
      linarith [h1, h2, h3, h12]
    calc
      inner0S (I := I) g x 4 (d : Tensor04At (I := I) (M := M) x) q
          = inner0S (I := I) g x 4 (fiberProjW (I := I) g x (ν₁ - ν₂) : Tensor04At (I := I) (M := M) x) q -
              inner0S (I := I) g x 4 (fiberProjW (I := I) g x ν₁ : Tensor04At (I := I) (M := M) x) q +
                inner0S (I := I) g x 4 (fiberProjW (I := I) g x ν₂ : Tensor04At (I := I) (M := M) x) q := hdq
      _ = 0 := by
        linarith [hsub, h1, h2, h3, h12]
  have hself : inner0S (I := I) g x 4 (d : Tensor04At (I := I) (M := M) x) (d : Tensor04At (I := I) (M := M) x) = 0 := by
    simpa using hchar ⟨(d : Tensor04At (I := I) (M := M) x), by
      exact Submodule.add_mem W (Submodule.sub_mem W (fiberProjW (I := I) g x (ν₁ - ν₂)).2 (fiberProjW (I := I) g x ν₁).2)
        (fiberProjW (I := I) g x ν₂).2⟩
  have hzero : (d : Tensor04At (I := I) (M := M) x) = 0 := by
    change (tensor0SMetricData (I := I) g x 4).inner (d : Tensor04At (I := I) (M := M) x)
      (d : Tensor04At (I := I) (M := M) x) = 0 at hself
    exact ((tensor0SMetricData (I := I) g x 4).inner_self_eq_zero_iff (d : Tensor04At (I := I) (M := M) x)).mp hself
  change (fiberProjW (I := I) g x (ν₁ - ν₂) : Tensor04At (I := I) (M := M) x) =
    (fiberProjW (I := I) g x ν₁ : Tensor04At (I := I) (M := M) x) -
      (fiberProjW (I := I) g x ν₂ : Tensor04At (I := I) (M := M) x)
  rw [← sub_eq_zero]
  have hconv : (fiberProjW (I := I) g x (ν₁ - ν₂) : Tensor04At (I := I) (M := M) x) -
      ((fiberProjW (I := I) g x ν₁ : Tensor04At (I := I) (M := M) x) -
        (fiberProjW (I := I) g x ν₂ : Tensor04At (I := I) (M := M) x)) =
      (d : Tensor04At (I := I) (M := M) x) := by
    dsimp [d]
    abel
  rw [hconv]
  exact hzero

omit [CompleteSpace E] [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M]
  [T2Space M] in
theorem fiberProjW_smul
    (g : SmoothRiemannianMetric I M) (x : M) (c : ℝ)
    (A : Tensor04At (I := I) (M := M) x) :
    (fiberProjW (I := I) g x (c • A) : Tensor04At (I := I) (M := M) x) =
      c • (fiberProjW (I := I) g x A : Tensor04At (I := I) (M := M) x) := by
  let p : algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
    fiberProjW (I := I) g x (c • A)
  let u : algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
    c • fiberProjW (I := I) g x A
  have hchar : ∀ q : algebraicCurvatureTensorSubmodule (I := I) (M := M) x,
      inner0S (I := I) g x 4 (p : Tensor04At (I := I) (M := M) x) q =
        inner0S (I := I) g x 4 (u : Tensor04At (I := I) (M := M) x) q := by
    intro q
    rw [show inner0S (I := I) g x 4 (p : Tensor04At (I := I) (M := M) x) q =
      inner0S (I := I) g x 4 (c • A) q from
        fiberProjW_spec (I := I) g x (c • A) q]
    change (tensor0SMetricData (I := I) g x 4).flat (c • A) q =
      (tensor0SMetricData (I := I) g x 4).flat
        (c • (fiberProjW (I := I) g x A : Tensor04At (I := I) (M := M) x)) q
    rw [map_smul, map_smul]
    exact congrArg (fun z : ℝ => c • z) (fiberProjW_spec (I := I) g x A q).symm
  have hdiff : ∀ q : algebraicCurvatureTensorSubmodule (I := I) (M := M) x,
      inner0S (I := I) g x 4
        ((p - u : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
          Tensor04At (I := I) (M := M) x) q = 0 := by
    intro q
    rw [show ((p - u : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
        Tensor04At (I := I) (M := M) x) =
      (p : Tensor04At (I := I) (M := M) x) -
        (u : Tensor04At (I := I) (M := M) x) by rfl]
    rw [inner0S_sub_left (I := I) g x 4]
    exact sub_eq_zero.mpr (hchar q)
  have hself := hdiff (p - u)
  have hzero : ((p - u : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
      Tensor04At (I := I) (M := M) x) = 0 := by
    exact ((tensor0SMetricData (I := I) g x 4).inner_self_eq_zero_iff
      (((p - u : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
        Tensor04At (I := I) (M := M) x))).mp hself
  have hpu : p = u := by
    apply Subtype.ext
    exact sub_eq_zero.mp hzero
  exact congrArg Subtype.val hpu

omit [CompleteSpace E] [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
omit [IsManifold I 1 M] in
theorem fiberProjW_norm_le
    (g : SmoothRiemannianMetric I M) (x : M)
    (ν : Tensor04At (I := I) (M := M) x) :
    tensor04FiberNorm (I := I) g x (fiberProjW (I := I) g x ν : Tensor04At (I := I) (M := M) x) ≤
      tensor04FiberNorm (I := I) g x ν := by
  let pν : algebraicCurvatureTensorSubmodule (I := I) (M := M) x := fiberProjW (I := I) g x ν
  have hspec : inner0S (I := I) g x 4 (pν : Tensor04At (I := I) (M := M) x) (pν : Tensor04At (I := I) (M := M) x) =
      inner0S (I := I) g x 4 ν (pν : Tensor04At (I := I) (M := M) x) :=
    fiberProjW_spec (I := I) g x ν pν
  have hsq : inner0S (I := I) g x 4 (pν : Tensor04At (I := I) (M := M) x) ν =
      inner0S (I := I) g x 4 ν (pν : Tensor04At (I := I) (M := M) x) :=
    inner0S_comm (I := I) g x 4 (pν : Tensor04At (I := I) (M := M) x) ν
  have hnormSq : normSq0S (I := I) g x 4 (pν : Tensor04At (I := I) (M := M) x) =
      inner0S (I := I) g x 4 (pν : Tensor04At (I := I) (M := M) x) ν := by
    rw [normSq0S]
    exact hspec.trans hsq.symm
  have hmain := inner0S_sq_le_mul (I := I) g x 4 (pν : Tensor04At (I := I) (M := M) x) ν
  have hmain2 : (normSq0S (I := I) g x 4 (pν : Tensor04At (I := I) (M := M) x)) ^ 2 ≤
      normSq0S (I := I) g x 4 (pν : Tensor04At (I := I) (M := M) x) * normSq0S (I := I) g x 4 ν := by
    rw [hnormSq] at hmain ⊢
    simpa [normSq0S] using hmain
  have hnn : 0 ≤ normSq0S (I := I) g x 4 (pν : Tensor04At (I := I) (M := M) x) := by
    rw [normSq0S]
    exact MetricFiberData.inner_nonneg (tensor0SMetricData (I := I) g x 4) (pν : Tensor04At (I := I) (M := M) x)
  have hnnν : 0 ≤ normSq0S (I := I) g x 4 ν := by
    rw [normSq0S]
    exact MetricFiberData.inner_nonneg (tensor0SMetricData (I := I) g x 4) ν
  have hleq : normSq0S (I := I) g x 4 (pν : Tensor04At (I := I) (M := M) x) ≤
      normSq0S (I := I) g x 4 ν := by
    by_cases hz : normSq0S (I := I) g x 4 (pν : Tensor04At (I := I) (M := M) x) = 0
    · rw [hz]
      exact hnnν
    · have hpos : 0 < normSq0S (I := I) g x 4 (pν : Tensor04At (I := I) (M := M) x) :=
        lt_of_le_of_ne hnn (Ne.symm hz)
      have hmain3 : normSq0S (I := I) g x 4 (pν : Tensor04At (I := I) (M := M) x) *
            normSq0S (I := I) g x 4 (pν : Tensor04At (I := I) (M := M) x) ≤
          normSq0S (I := I) g x 4 ν * normSq0S (I := I) g x 4 (pν : Tensor04At (I := I) (M := M) x) := by
        simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hmain2
      exact le_of_mul_le_mul_right hmain3 hpos
  unfold tensor04FiberNorm
  exact Real.sqrt_le_sqrt hleq

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
  [SigmaCompactSpace M] [T2Space M] in
theorem regionSupportVector_norm_le
    (g : SmoothRiemannianMetric I M) (x : M)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) g x (basisAt x))
    (ν : Tensor04At (I := I) (M := M) x) :
    ‖regionSupportVector g basisAt x ν‖ ≤ tensor04FiberNorm (I := I) g x ν / 2 := by
  let pν : algebraicCurvatureTensorSubmodule (I := I) (M := M) x := fiberProjW (I := I) g x ν
  have hmain := inner0S_eq_four_mul_inner_regionProjMatrix (I := I) g x (basisAt x) horth pν.2
    (pν : Tensor04At (I := I) (M := M) x)
  have hid : fiberProjW (I := I) g x (pν : Tensor04At (I := I) (M := M) x) = pν :=
    Subtype.ext (fiberProjW_idem (I := I) g x ν)
  have hreg : matrixToEuclid (regionProjMatrix (I := I) g (basisAt x) (pν : Tensor04At (I := I) (M := M) x)) =
      matrixToEuclid (curvatureOperatorMatrixAt (I := I) x (basisAt x) pν) := by
    unfold regionProjMatrix
    rw [hid]
  have hw : matrixToEuclid (curvatureOperatorMatrixAt (I := I) x (basisAt x) pν) =
      regionSupportVector g basisAt x ν := by
    unfold regionSupportVector
    rw [regionProjMatrix]
  have h4 : inner0S (I := I) g x 4 (pν : Tensor04At (I := I) (M := M) x) (pν : Tensor04At (I := I) (M := M) x) =
      4 * ‖regionSupportVector g basisAt x ν‖ ^ 2 := by
    have hA : matrixToEuclid (regionProjMatrix (I := I) g (basisAt x) (pν : Tensor04At (I := I) (M := M) x)) =
        regionSupportVector g basisAt x ν := hreg.trans hw
    rw [hA, hw] at hmain
    simpa [norm_sq_eq_re_inner] using hmain
  have hsqrt : ‖regionSupportVector g basisAt x ν‖ =
      Real.sqrt (inner0S (I := I) g x 4 (pν : Tensor04At (I := I) (M := M) x) (pν : Tensor04At (I := I) (M := M) x)) / 2 := by
    have hnn : 0 ≤ inner0S (I := I) g x 4 (pν : Tensor04At (I := I) (M := M) x) (pν : Tensor04At (I := I) (M := M) x) :=
      MetricFiberData.inner_nonneg (tensor0SMetricData (I := I) g x 4) (pν : Tensor04At (I := I) (M := M) x)
    have hsq : ‖regionSupportVector g basisAt x ν‖ ^ 2 =
        inner0S (I := I) g x 4 (pν : Tensor04At (I := I) (M := M) x) (pν : Tensor04At (I := I) (M := M) x) / 4 := by
      linarith [h4]
    have hsqrt' : Real.sqrt (‖regionSupportVector g basisAt x ν‖ ^ 2) = ‖regionSupportVector g basisAt x ν‖ :=
      Real.sqrt_sq (norm_nonneg (regionSupportVector g basisAt x ν))
    calc
      ‖regionSupportVector g basisAt x ν‖ = Real.sqrt (‖regionSupportVector g basisAt x ν‖ ^ 2) := hsqrt'.symm
      _ = Real.sqrt (inner0S (I := I) g x 4 (pν : Tensor04At (I := I) (M := M) x) (pν : Tensor04At (I := I) (M := M) x) / 4) := by rw [hsq]
      _ = Real.sqrt (inner0S (I := I) g x 4 (pν : Tensor04At (I := I) (M := M) x) (pν : Tensor04At (I := I) (M := M) x)) / Real.sqrt 4 := by
            rw [Real.sqrt_div hnn (4 : ℝ)]
      _ = Real.sqrt (inner0S (I := I) g x 4 (pν : Tensor04At (I := I) (M := M) x) (pν : Tensor04At (I := I) (M := M) x)) / 2 := by norm_num
  calc
    ‖regionSupportVector g basisAt x ν‖
        = Real.sqrt (inner0S (I := I) g x 4 (pν : Tensor04At (I := I) (M := M) x) (pν : Tensor04At (I := I) (M := M) x)) / 2 := hsqrt
    _ ≤ tensor04FiberNorm (I := I) g x ν / 2 := by
      have hle : tensor04FiberNorm (I := I) g x (pν : Tensor04At (I := I) (M := M) x) ≤
          tensor04FiberNorm (I := I) g x ν := fiberProjW_norm_le (I := I) g x ν
      have hle' : Real.sqrt (inner0S (I := I) g x 4 (pν : Tensor04At (I := I) (M := M) x) (pν : Tensor04At (I := I) (M := M) x)) ≤
          tensor04FiberNorm (I := I) g x ν := by
        unfold tensor04FiberNorm at hle ⊢
        exact hle
      exact div_le_div_of_nonneg_right hle' (by norm_num)

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
  [SigmaCompactSpace M] [T2Space M] in
theorem regionSupportVector_sub
    (g : SmoothRiemannianMetric I M)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (x : M) (ν₁ ν₂ : Tensor04At (I := I) (M := M) x) :
    regionSupportVector g basisAt x (ν₁ - ν₂) =
      regionSupportVector g basisAt x ν₁ - regionSupportVector g basisAt x ν₂ := by
  unfold regionSupportVector regionProjMatrix
  have hsub' : fiberProjW (I := I) g x (ν₁ - ν₂) =
      fiberProjW (I := I) g x ν₁ - fiberProjW (I := I) g x ν₂ :=
    Subtype.ext (fiberProjW_sub (I := I) g x ν₁ ν₂)
  rw [hsub']
  ext ij
  simp only [matrixToEuclid, curvatureOperatorMatrixAt]
  exact Tensor0SSpace.sub_apply 4 x (fiberProjW (I := I) g x ν₁ : Tensor04At (I := I) (M := M) x)
    (fiberProjW (I := I) g x ν₂ : Tensor04At (I := I) (M := M) x)
    (vec4 (basisAt x (bivectorIndex3 ij.1).1) (basisAt x (bivectorIndex3 ij.1).2)
      (basisAt x (bivectorIndex3 ij.2).2) (basisAt x (bivectorIndex3 ij.2).1))

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
  [SigmaCompactSpace M] [T2Space M] in
theorem regionSource_lipschitzOn_closedBall_uniform
    (g : SmoothRiemannianMetric I M)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : ∀ x : M, OrthonormalBasisAt (I := I) g x (basisAt x))
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ L : NNReal, ∀ x : M, ∀ ν : Tensor04At (I := I) (M := M) x,
      letI : InnerProductSpace.Core ℝ (Tensor04At (I := I) (M := M) x) :=
        (tensor0SMetricData (I := I) g x 4).toCore
      letI : NormedAddCommGroup (Tensor04At (I := I) (M := M) x) :=
        @InnerProductSpace.Core.toNormedAddCommGroup ℝ (Tensor04At (I := I) (M := M) x)
          inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) g x 4).toCore
      letI : InnerProductSpace ℝ (Tensor04At (I := I) (M := M) x) :=
        @InnerProductSpace.ofCore ℝ (Tensor04At (I := I) (M := M) x)
          inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) g x 4).toCore.toCore
      LipschitzOnWith (L * ‖ν‖₊)
        (fun p : Tensor04At (I := I) (M := M) x => regionSource g basisAt x p ν)
        (Metric.closedBall 0 (2 * R)) := by
  classical
  rcases uhlenbeckCurvatureOperatorReactionState_lipschitzOn_closedBall R hR with ⟨Lst, hLst⟩
  refine ⟨Lst, ?_⟩
  intro x ν
  letI : InnerProductSpace.Core ℝ (Tensor04At (I := I) (M := M) x) :=
    (tensor0SMetricData (I := I) g x 4).toCore
  letI : NormedAddCommGroup (Tensor04At (I := I) (M := M) x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℝ (Tensor04At (I := I) (M := M) x)
      inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) g x 4).toCore
  letI : InnerProductSpace ℝ (Tensor04At (I := I) (M := M) x) :=
    @InnerProductSpace.ofCore ℝ (Tensor04At (I := I) (M := M) x)
      inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) g x 4).toCore.toCore
  have hnorm_eq : ∀ A : Tensor04At (I := I) (M := M) x,
      tensor04FiberNorm (I := I) g x A = ‖A‖ := tensor04FiberNorm_eq_norm (I := I) g x
  have hw : ∀ A : Tensor04At (I := I) (M := M) x,
      ‖regionSupportVector g basisAt x A‖ ≤ ‖A‖ / 2 := by
    intro A
    have h := regionSupportVector_norm_le (I := I) g x basisAt (horth x) A
    rwa [hnorm_eq A] at h
  have hAball : ∀ A : Tensor04At (I := I) (M := M) x,
      A ∈ Metric.closedBall 0 (2 * R) →
        regionSupportVector g basisAt x A ∈ Metric.closedBall 0 R := by
    intro A hA
    have hA' : ‖A‖ ≤ 2 * R := by
      simpa [dist_eq_norm, sub_zero] using (Metric.mem_closedBall.mp hA)
    have hle := hw A
    rw [Metric.mem_closedBall]
    rw [dist_eq_norm, sub_zero]
    nlinarith
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro p hp q hq
  rw [dist_eq_norm, dist_eq_norm]
  let Ap : EuclideanSpace ℝ (Fin 3 × Fin 3) := regionSupportVector g basisAt x p
  let Aq : EuclideanSpace ℝ (Fin 3 × Fin 3) := regionSupportVector g basisAt x q
  let wν : EuclideanSpace ℝ (Fin 3 × Fin 3) := regionSupportVector g basisAt x ν
  have hsrc : regionSource g basisAt x p ν - regionSource g basisAt x q ν =
      4 * inner ℝ (uhlenbeckCurvatureOperatorReactionState Ap -
        uhlenbeckCurvatureOperatorReactionState Aq) wν := by
    dsimp [Ap, Aq, wν]
    unfold regionSource
    simp only [regionSupportVector]
    rw [← mul_sub]
    congr 1
    rw [← inner_sub_left]
  have h1 : |inner ℝ (uhlenbeckCurvatureOperatorReactionState Ap -
      uhlenbeckCurvatureOperatorReactionState Aq) wν| ≤
      ‖uhlenbeckCurvatureOperatorReactionState Ap - uhlenbeckCurvatureOperatorReactionState Aq‖ * ‖wν‖ := by
    have h := norm_inner_le_norm (𝕜 := ℝ) (uhlenbeckCurvatureOperatorReactionState Ap -
      uhlenbeckCurvatureOperatorReactionState Aq) wν
    simpa [Real.norm_eq_abs] using h
  have h2 : ‖uhlenbeckCurvatureOperatorReactionState Ap - uhlenbeckCurvatureOperatorReactionState Aq‖ ≤
      (Lst : ℝ) * ‖Ap - Aq‖ := by
    have hLip := hLst.dist_le_mul Ap (hAball p hp) Aq (hAball q hq)
    simpa [dist_eq_norm, Ap, Aq] using hLip
  have h3 : ‖wν‖ ≤ ‖ν‖ / 2 := by
    dsimp [wν]
    exact hw ν
  have h4 : ‖Ap - Aq‖ ≤ ‖p - q‖ / 2 := by
    have hsub : regionSupportVector g basisAt x (p - q) =
        regionSupportVector g basisAt x p - regionSupportVector g basisAt x q :=
      regionSupportVector_sub (I := I) g basisAt x p q
    have h := hw (p - q)
    rwa [hsub] at h
  have habs : |regionSource g basisAt x p ν - regionSource g basisAt x q ν| ≤ (Lst : ℝ) * ‖ν‖ * ‖p - q‖ := by
    rw [hsrc]
    calc
      |4 * inner ℝ (uhlenbeckCurvatureOperatorReactionState Ap -
          uhlenbeckCurvatureOperatorReactionState Aq) wν|
          = 4 * |inner ℝ (uhlenbeckCurvatureOperatorReactionState Ap -
              uhlenbeckCurvatureOperatorReactionState Aq) wν| := by
            rw [abs_mul]
            norm_num
      _ ≤ 4 * (‖uhlenbeckCurvatureOperatorReactionState Ap -
          uhlenbeckCurvatureOperatorReactionState Aq‖ * ‖wν‖) := by
            exact mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ ≤ 4 * (((Lst : ℝ) * ‖Ap - Aq‖) * (‖ν‖ / 2)) := by
            exact mul_le_mul_of_nonneg_left (mul_le_mul h2 h3 (norm_nonneg _)
              (mul_nonneg (NNReal.coe_nonneg Lst) (norm_nonneg _))) (by norm_num)
      _ ≤ 4 * (((Lst : ℝ) * (‖p - q‖ / 2)) * (‖ν‖ / 2)) := by
            exact mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul_of_nonneg_left h4 (NNReal.coe_nonneg Lst))
              le_rfl (by positivity) (by positivity)) (by norm_num)
      _ = (Lst : ℝ) * ‖ν‖ * ‖p - q‖ := by ring
  have hcoef : (Lst : ℝ) * ‖ν‖ = ((Lst * ‖ν‖₊ : NNReal) : ℝ) := by
    rw [NNReal.coe_mul]
    simp
  rw [Real.norm_eq_abs]
  calc
    |regionSource g basisAt x p ν - regionSource g basisAt x q ν| ≤ (Lst : ℝ) * ‖ν‖ * ‖p - q‖ := habs
    _ = ((Lst * ‖ν‖₊ : NNReal) : ℝ) * ‖p - q‖ := by rw [hcoef]

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
  [SigmaCompactSpace M] [T2Space M] in
theorem fiberRegion_mem_iff_forall_normalDirections_full
    (g : SmoothRiemannianMetric I M)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) g x (basisAt x))
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ) (x : M)
    (p : Tensor04At (I := I) (M := M) x) :
    p ∈ fiberHamiltonIveyRegion basisAt K τ x ↔
      ∀ ν : Tensor04At (I := I) (M := M) x,
        ν ∈ regionNormalDirections (I := I) g basisAt x →
          inner0S (I := I) g x 4 ν p ≤ regionSupport (I := I) g basisAt K τ x ν := by
  constructor
  · intro hpC ν hν
    exact (fiberRegion_mem_iff_forall_normalDirections (I := I) g basisAt horth0 hK hτ x p hpC.1).mp hpC ν hν
  · intro hle
    let pν : algebraicCurvatureTensorSubmodule (I := I) (M := M) x := fiberProjW (I := I) g x p
    let q : Tensor04At (I := I) (M := M) x := p - (pν : Tensor04At (I := I) (M := M) x)
    have hqW : ∀ r : Tensor04At (I := I) (M := M) x,
        r ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x →
          inner0S (I := I) g x 4 q r = 0 := by
      intro r hr
      have h1 := fiberProjW_spec (I := I) g x p ⟨r, hr⟩
      have hsub : inner0S (I := I) g x 4 q r =
          inner0S (I := I) g x 4 p r - inner0S (I := I) g x 4 (pν : Tensor04At (I := I) (M := M) x) r := by
        dsimp [q]
        rw [inner0S_sub_left]
      rw [hsub]
      have h1' : inner0S (I := I) g x 4 (pν : Tensor04At (I := I) (M := M) x) r =
          inner0S (I := I) g x 4 p r := by
        simpa using h1
      rw [h1']
      ring
    have hqproj : (fiberProjW (I := I) g x q : Tensor04At (I := I) (M := M) x) = 0 := by
      have hself : inner0S (I := I) g x 4
          (fiberProjW (I := I) g x q : Tensor04At (I := I) (M := M) x)
          (fiberProjW (I := I) g x q : Tensor04At (I := I) (M := M) x) = 0 := by
        have h := fiberProjW_spec (I := I) g x q (fiberProjW (I := I) g x q)
        have h' : inner0S (I := I) g x 4
            (fiberProjW (I := I) g x q : Tensor04At (I := I) (M := M) x)
            (fiberProjW (I := I) g x q : Tensor04At (I := I) (M := M) x) =
            inner0S (I := I) g x 4 q
              (fiberProjW (I := I) g x q : Tensor04At (I := I) (M := M) x) := by
          simpa using h
        rw [h']
        exact hqW (fiberProjW (I := I) g x q : Tensor04At (I := I) (M := M) x) (fiberProjW (I := I) g x q).2
      change (tensor0SMetricData (I := I) g x 4).inner
          (fiberProjW (I := I) g x q : Tensor04At (I := I) (M := M) x)
          (fiberProjW (I := I) g x q : Tensor04At (I := I) (M := M) x) = 0 at hself
      exact ((tensor0SMetricData (I := I) g x 4).inner_self_eq_zero_iff
        (fiberProjW (I := I) g x q : Tensor04At (I := I) (M := M) x)).mp hself
    have hqproj0 : fiberProjW (I := I) g x q = 0 := by
      apply Subtype.ext
      simpa using hqproj
    have hregq : regionProjMatrix (I := I) g (basisAt x) q = 0 := by
      unfold regionProjMatrix
      rw [hqproj0]
      ext i j
      change tensor04StdAt (I := I) (M := M)
        ((0 : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) : Tensor04At (I := I) (M := M) x)
        (basisAt x (bivectorIndex3 i).1) (basisAt x (bivectorIndex3 i).2)
        (basisAt x (bivectorIndex3 j).2) (basisAt x (bivectorIndex3 j).1) = 0
      have hz : ((0 : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) : Tensor04At (I := I) (M := M) x) = 0 := by
        rfl
      rw [hz]
      simp
    have hqN : q ∈ regionNormalDirections (I := I) g basisAt x := by
      rw [regionNormalDirections]
      right
      rw [hregq]
      unfold symmEuclid
      ext i j
      simp [euclidToMatrix, matrixToEuclid, smul_eq_mul]
    have hsupp : regionSupport (I := I) g basisAt K τ x q = 0 := by
      have hz : hamiltonIveyConvexMatrixRegionSupportEuclid K τ
          (0 : EuclideanSpace ℝ (Fin 3 × Fin 3)) = 0 :=
        hamiltonIveyConvexMatrixRegionSupportEuclid_eq_zero_of_symm_zero (K := K) (τ := τ)
          (0 : EuclideanSpace ℝ (Fin 3 × Fin 3)) (by
            unfold symmEuclid
            ext i j
            simp [euclidToMatrix, smul_eq_mul])
      unfold regionSupport
      rw [hregq]
      have hme : matrixToEuclid (0 : Matrix (Fin 3) (Fin 3) ℝ) =
          (0 : EuclideanSpace ℝ (Fin 3 × Fin 3)) := by
        ext ij
        simp [matrixToEuclid]
      rw [hme]
      simp [hz]
    have hle' := hle q hqN
    have hqp : inner0S (I := I) g x 4 q p = inner0S (I := I) g x 4 q q := by
      have h1 : inner0S (I := I) g x 4 q (pν : Tensor04At (I := I) (M := M) x) = 0 :=
        hqW (pν : Tensor04At (I := I) (M := M) x) pν.2
      calc
        inner0S (I := I) g x 4 q p
            = inner0S (I := I) g x 4 q ((pν : Tensor04At (I := I) (M := M) x) + q) := by
              congr 2
              dsimp [q]
              abel
        _ = inner0S (I := I) g x 4 q (pν : Tensor04At (I := I) (M := M) x) + inner0S (I := I) g x 4 q q := by
              exact inner0S_add_right (I := I) g x 4 q (pν : Tensor04At (I := I) (M := M) x) q
        _ = inner0S (I := I) g x 4 q q := by
              rw [h1]
              simp
    have hqq : inner0S (I := I) g x 4 q q ≤ 0 := by
      rw [hsupp] at hle'
      rwa [hqp] at hle'
    have hqzero : q = 0 := by
      have hnonneg : 0 ≤ inner0S (I := I) g x 4 q q :=
        MetricFiberData.inner_nonneg (tensor0SMetricData (I := I) g x 4) q
      have hz : inner0S (I := I) g x 4 q q = 0 := le_antisymm hqq hnonneg
      exact ((tensor0SMetricData (I := I) g x 4).inner_self_eq_zero_iff q).mp hz
    have hpW : p ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x := by
      have hpeq : p = (pν : Tensor04At (I := I) (M := M) x) := by
        have hz : p - (pν : Tensor04At (I := I) (M := M) x) = 0 := by
          simpa [q] using hqzero
        exact sub_eq_zero.mp hz
      rw [hpeq]
      exact pν.2
    exact (fiberRegion_mem_iff_forall_normalDirections (I := I) g basisAt horth0 hK hτ x p hpW).mpr hle

end PulledScalarization

section FiberRegionFlatPredicate

noncomputable def fiberRegionFlat
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (iota : MatrixComp M (Fin 3))
    (t : ℝ) (x₀ : M) (ν : (x : M) → Tensor04At (I := I) (M := M) x) : Prop :=
  ∃ (η : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (nablaη : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 5)
    (nabla2η : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 6)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x₀)),
    OrthonormalBasisAt (I := I) (S.base.metric t) x₀ basis ∧
    (∀ᶠ y in 𝓝 x₀, ν y = uhlenbeckPullbackTensorAt (I := I) basisAt iota t y (η y)) ∧
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4
      (S.base.connection t) η nablaη ∧
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5
      (S.base.connection t) nablaη nabla2η ∧
    nablaη x₀ = 0 ∧
    metricTrace0S2TensorInBasis (I := I) (basis := basis)
      (identityInvMetric (Idx := Fin 3)) (nabla2η x₀) = 0

end FiberRegionFlatPredicate

section FiberMaximumPrinciple

open DifferentialGeometry.Analysis.Parabolic

variable {T : ℝ} (hT : 0 < T) [I.Boundaryless]
variable (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
variable (hS : IsSolutionOn (I := I) S)
variable (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
variable (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
variable (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt x))
variable (iota : MatrixComp M (Fin 3))
variable (hiota0 : ∀ x : M, ∀ a k : Fin 3, iota 0 x a k = if a = k then 1 else 0)
variable (hgram : ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Fin 3,
  movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota t x a b =
  movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota 0 x a b)

noncomputable def intrinsicUhlenbeckIota
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn (I := I) S)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x)) :
    MatrixComp M (Fin 3) :=
  Classical.choose (uhlenbeckIotaOfSolution (I := I) (M := M) hT S
    (solutionInverseMetricComponents (I := I) (M := M) S basisAt)
    (fun x i j => solutionInverseMetricComponents_entry_continuousOn
      (I := I) (M := M) hT S hS basisAt x i j)
    (fun x v w => ricciAt_continuousOn_perPoint (I := I) (M := M) hT S hS x v w)
    (fun a x => basisAt x a)
    (fun a k : Fin 3 => if a = k then 1 else 0))

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] in
theorem intrinsicUhlenbeckIota_spec :
    (∀ x : M, ∀ a k : Fin 3,
      intrinsicUhlenbeckIota hT S hS basisAt 0 x a k = if a = k then 1 else 0) ∧
    (∀ x : M, ContinuousOn (fun t : ℝ => intrinsicUhlenbeckIota hT S hS basisAt t x)
      (Set.Icc 0 T)) ∧
    FrameRicciODEInFrameOn (D := RealTimeInterval.closed 0 T hT.le)
      (intrinsicUhlenbeckIota hT S hS basisAt)
      (uhlenbeckRupOfSolution (I := I) S (solutionInverseMetricComponents S basisAt)
        (fun a x => basisAt x a)) ∧
    (∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Fin 3,
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a))
        (intrinsicUhlenbeckIota hT S hS basisAt) t x a b =
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a))
        (intrinsicUhlenbeckIota hT S hS basisAt) 0 x a b) := by
  classical
  let iota : MatrixComp M (Fin 3) := intrinsicUhlenbeckIota hT S hS basisAt
  have hraw := Classical.choose_spec (uhlenbeckIotaOfSolution (I := I) (M := M) hT S
    (solutionInverseMetricComponents (I := I) (M := M) S basisAt)
    (fun x i j => solutionInverseMetricComponents_entry_continuousOn
      (I := I) (M := M) hT S hS basisAt x i j)
    (fun x v w => ricciAt_continuousOn_perPoint (I := I) (M := M) hT S hS x v w)
    (fun a x => basisAt x a)
    (fun a k : Fin 3 => if a = k then 1 else 0))
  have hiota0 : ∀ x : M, ∀ a k : Fin 3, iota 0 x a k = if a = k then 1 else 0 := hraw.1
  have hiota_cont : ∀ x : M, ContinuousOn (fun t : ℝ => iota t x) (Set.Icc 0 T) := hraw.2.1
  have hiota_deriv : ∀ t : ℝ, t ∈ Set.Ico 0 T → ∀ x : M, ∀ a k : Fin 3,
      HasDerivWithinAt (fun s : ℝ => iota s x a k)
        (∑ l : Fin 3, uhlenbeckRupOfSolution (I := I) S
          (solutionInverseMetricComponents S basisAt) (fun a x => basisAt x a) t x l k *
            iota t x a l)
        (Set.Ici 0) t := hraw.2.2
  have hframeODE : FrameRicciODEInFrameOn (D := RealTimeInterval.closed 0 T hT.le) iota
      (uhlenbeckRupOfSolution (I := I) S (solutionInverseMetricComponents S basisAt)
        (fun a x => basisAt x a)) := by
    intro t x a k
    have hderiv := hiota_deriv (t : ℝ) ⟨le_of_lt t.2.1, t.2.2⟩ x a k
    have hnhds : Set.Ici 0 ∈ 𝓝 (t : ℝ) := by
      have hpos : Set.Ioi (0 : ℝ) ∈ 𝓝 (t : ℝ) := Ioi_mem_nhds t.2.1
      exact Filter.mem_of_superset hpos (by intro s hs; exact le_of_lt (show (0 : ℝ) < s from hs))
    exact (hderiv.hasDerivAt hnhds).hasDerivWithinAt
  have hgram' : ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Fin 3,
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota t x a b =
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota 0 x a b := by
    let gInv : Real → DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M (Fin 3) :=
      solutionInverseMetricComponents (I := I) (M := M) S basisAt
    have hcompat : RicciEndomorphismCompatibleInFrame
        (metricCompInFrame (I := I) S (fun a x => basisAt x a))
        (ricciCompInFrame (I := I) S (fun a x => basisAt x a))
        (uhlenbeckRupOfSolution (I := I) S gInv (fun a x => basisAt x a)) := by
      exact ricciOneUpCompatible_of_inverseMetric (I := I) (M := M) S gInv (fun a x => basisAt x a)
        (by intro t x i j; exact solutionInverseMetricComponents_mul_metric (I := I) (M := M) S basisAt t x i j)
        (by intro t x i j; exact solutionInverseMetricComponents_symm (I := I) (M := M) S basisAt t x i j)
    have hmetric : MetricCompRicciFlowInFrameOn (D := RealTimeInterval.closed 0 T hT.le)
        (metricCompInFrame (I := I) S (fun a x => basisAt x a))
        (ricciCompInFrame (I := I) S (fun a x => basisAt x a)) := by
      intro τ x i j
      exact metricCompInFrame_timeDeriv (I := I) S hS (fun a x => basisAt x a) τ x i j
    have hgram_cont : ∀ x : M, ∀ a b : Fin 3,
        ContinuousOn (fun s : ℝ =>
          movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota s x a b)
          (Set.Icc 0 T) := by
      intro x a b
      exact movingFrameGram_continuousOn_of_metricFamily (I := I) (M := M) hT S hS
        iota hiota_cont (fun a x => basisAt x a) a b
    intro t ht x a b
    exact movingFrameGram_valueConstant_of_ricciFlow
      (D := RealTimeInterval.closed 0 T hT.le) (T := T)
      (metricCompInFrame (I := I) S (fun a x => basisAt x a))
      (ricciCompInFrame (I := I) S (fun a x => basisAt x a))
      iota (uhlenbeckRupOfSolution (I := I) S gInv (fun a x => basisAt x a))
      hmetric hframeODE hcompat (by
        intro s hs
        change s ∈ Set.Ioo 0 T
        exact hs)
      hgram_cont ht x a b
  constructor
  · intro x a k
    simpa [iota] using hiota0 x a k
  · constructor
    · simpa [iota] using hiota_cont
    · constructor
      · simpa [iota] using hframeODE
      · intro t ht x a b
        simpa [iota] using hgram' t ht x a b

def fiberRegionSet
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (K t : ℝ) (x : M) : Set (Tensor04At (I := I) (M := M) x) :=
  fiberHamiltonIveyRegion basisAt K (max t 0) x

def fiberRegionSupport
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (K t : ℝ) (x : M) (ν : Tensor04At (I := I) (M := M) x) : ℝ :=
  regionSupport (I := I) (S.base.metric 0) basisAt K (max t 0) x ν

def fiberRegionSupportDeriv
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    {K : ℝ} (hK : 0 < K) (t : ℝ) (x : M)
    (ν : Tensor04At (I := I) (M := M) x) : ℝ :=
  regionSupportDeriv (I := I) (S.base.metric 0) basisAt hK t x ν

def fiberRegionSource
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (x : M) (p ν : Tensor04At (I := I) (M := M) x) : ℝ :=
  regionSource (I := I) (S.base.metric 0) basisAt x p ν

@[implicit_reducible]
noncomputable def tensor04FiberNACG
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le)) :
    ∀ x : M, NormedAddCommGroup (Tensor04At (I := I) (M := M) x) :=
  fun x => @InnerProductSpace.Core.toNormedAddCommGroup ℝ (Tensor04At (I := I) (M := M) x)
    inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) (S.base.metric 0) x 4).toCore

@[implicit_reducible]
noncomputable def tensor04FiberIP
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le)) :
    ∀ x : M,
      letI : NormedAddCommGroup (Tensor04At (I := I) (M := M) x) := tensor04FiberNACG hT S x
      InnerProductSpace ℝ (Tensor04At (I := I) (M := M) x) :=
  fun x => by
    letI : NormedAddCommGroup (Tensor04At (I := I) (M := M) x) := tensor04FiberNACG hT S x
    exact @InnerProductSpace.ofCore ℝ (Tensor04At (I := I) (M := M) x)
      inferInstance inferInstance inferInstance
      (tensor0SMetricData (I := I) (S.base.metric 0) x 4).toCore.toCore

@[implicit_reducible]
noncomputable def tensor04FiberComplete
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le)) :
    ∀ x : M,
      letI : NormedAddCommGroup (Tensor04At (I := I) (M := M) x) := tensor04FiberNACG hT S x
      letI : InnerProductSpace ℝ (Tensor04At (I := I) (M := M) x) := tensor04FiberIP hT S x
      @CompleteSpace (Tensor04At (I := I) (M := M) x)
        (inferInstance : UniformSpace (Tensor04At (I := I) (M := M) x)) :=
  fun x => by
    letI : NormedAddCommGroup (Tensor04At (I := I) (M := M) x) := tensor04FiberNACG hT S x
    letI : InnerProductSpace ℝ (Tensor04At (I := I) (M := M) x) := tensor04FiberIP hT S x
    infer_instance

noncomputable def tensor04FiberHomeo
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le)) (x : M) :
    let topLocal : TopologicalSpace (Tensor04At (I := I) (M := M) x) :=
      (tensor04FiberNACG hT S x).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    let topGlobal : TopologicalSpace (Tensor04At (I := I) (M := M) x) :=
      inferInstance
    @Homeomorph (Tensor04At (I := I) (M := M) x) (Tensor04At (I := I) (M := M) x)
      topLocal topGlobal := by
  classical
  let topLocal : TopologicalSpace (Tensor04At (I := I) (M := M) x) :=
    (tensor04FiberNACG hT S x).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let topGlobal : TopologicalSpace (Tensor04At (I := I) (M := M) x) :=
    inferInstance
  refine @Homeomorph.mk (Tensor04At (I := I) (M := M) x) (Tensor04At (I := I) (M := M) x)
    topLocal topGlobal (Equiv.refl (Tensor04At (I := I) (M := M) x)) ?_ ?_
  · letI : NormedAddCommGroup (Tensor04At (I := I) (M := M) x) := tensor04FiberNACG hT S x
    letI : InnerProductSpace ℝ (Tensor04At (I := I) (M := M) x) := tensor04FiberIP hT S x
    exact @LinearMap.continuous_of_finiteDimensional ℝ inferInstance
      (Tensor04At (I := I) (M := M) x)
      inferInstance inferInstance topLocal inferInstance inferInstance
      (Tensor04At (I := I) (M := M) x)
      inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance
      (LinearMap.id : Tensor04At (I := I) (M := M) x →ₗ[ℝ] Tensor04At (I := I) (M := M) x)
  · letI : NormedAddCommGroup (Tensor04At (I := I) (M := M) x) := tensor04FiberNACG hT S x
    letI : InnerProductSpace ℝ (Tensor04At (I := I) (M := M) x) := tensor04FiberIP hT S x
    exact @LinearMap.continuous_of_finiteDimensional ℝ inferInstance
      (Tensor04At (I := I) (M := M) x)
      inferInstance inferInstance inferInstance inferInstance inferInstance
      (Tensor04At (I := I) (M := M) x)
      inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance
      (LinearMap.id : Tensor04At (I := I) (M := M) x →ₗ[ℝ] Tensor04At (I := I) (M := M) x)

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
  [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem isClosed_fiberHamiltonIveyRegion
    (hT : 0 < T) (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    {K τ : ℝ} (hK : 0 < K) (x : M) :
    @IsClosed (Tensor04At (I := I) (M := M) x)
      (tensor04FiberNACG hT S x).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      (fiberHamiltonIveyRegion basisAt K τ x) := by
  letI : NormedAddCommGroup (Tensor04At (I := I) (M := M) x) := tensor04FiberNACG hT S x
  letI : InnerProductSpace ℝ (Tensor04At (I := I) (M := M) x) := tensor04FiberIP hT S x
  letI : TopologicalSpace (Tensor04At (I := I) (M := M) x) :=
    (tensor04FiberNACG hT S x).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  rw [← intrinsicFiberHamiltonIveyRegion_eq_fiberHamiltonIveyRegion (I := I) basisAt K τ x]
  have hEq : (intrinsicFiberHamiltonIveyRegion (I := I) basisAt K τ x : Set (Tensor04At (I := I) (M := M) x)) =
      (algebraicCurvatureTensorSubmodule (I := I) (M := M) x : Set (Tensor04At (I := I) (M := M) x)) ∩
        (fun A : Tensor04At (I := I) (M := M) x =>
          matrixToEuclid (intrinsicFiberCurvatureOperatorMatrix (I := I) (basisAt x) A)) ⁻¹'
            hamiltonIveyConvexMatrixRegionEuclid K τ := by
    ext A
    rw [mem_intrinsicFiberHamiltonIveyRegion]
    rfl
  rw [hEq]
  have hclosedE : IsClosed (hamiltonIveyConvexMatrixRegionEuclid K τ) := by
    have hpre : hamiltonIveyConvexMatrixRegionEuclid K τ =
        euclidToMatrix ⁻¹' hamiltonIveyConvexMatrixRegion K τ := by
      ext c
      rfl
    rw [hpre]
    have hlin : Continuous euclidToMatrix := by
      let L : EuclideanSpace ℝ (Fin 3 × Fin 3) →ₗ[ℝ] Matrix (Fin 3) (Fin 3) ℝ :=
        { toFun := euclidToMatrix
          map_add' := by
            intro A B
            ext i j
            simp [euclidToMatrix]
          map_smul' := by
            intro c A
            ext i j
            simp [euclidToMatrix] }
      exact L.continuous_of_finiteDimensional
    exact (isClosed_hamiltonIveyConvexMatrixRegion hK).preimage hlin
  have hfcont : Continuous (fun A : Tensor04At (I := I) (M := M) x =>
      matrixToEuclid (intrinsicFiberCurvatureOperatorMatrix (I := I) (basisAt x) A)) := by
    let L : Tensor04At (I := I) (M := M) x →ₗ[ℝ] EuclideanSpace ℝ (Fin 3 × Fin 3) :=
      { toFun := fun A => matrixToEuclid (intrinsicFiberCurvatureOperatorMatrix (I := I) (basisAt x) A)
        map_add' := by
          intro A B
          ext ij
          simp [matrixToEuclid, intrinsicFiberCurvatureOperatorMatrix]
        map_smul' := by
          intro c A
          ext ij
          simp [matrixToEuclid, intrinsicFiberCurvatureOperatorMatrix] }
    exact L.continuous_of_finiteDimensional
  have hcont04 : ∀ X Y Z W : TangentSpace I x,
      Continuous (fun A : Tensor04At (I := I) (M := M) x =>
        tensor04StdAt (I := I) (M := M) A X Y Z W) := by
    intro X Y Z W
    let g : Tensor04At (I := I) (M := M) x →ₗ[ℝ] ℝ :=
      { toFun := fun A => tensor04StdAt (I := I) (M := M) A X Y Z W
        map_add' := by
          intro A B
          change tensor04StdAt (I := I) (M := M) (A + B) X Y Z W =
            tensor04StdAt (I := I) (M := M) A X Y Z W + tensor04StdAt (I := I) (M := M) B X Y Z W
          simp [Tensor0SSpace.add_apply]
        map_smul' := by
          intro c A
          change tensor04StdAt (I := I) (M := M) (c • A) X Y Z W =
            c * tensor04StdAt (I := I) (M := M) A X Y Z W
          simp [Tensor0SSpace.smul_apply, smul_eq_mul] }
    exact g.continuous_of_finiteDimensional
  have hanti1 : IsClosed {A : Tensor04At (I := I) (M := M) x | ∀ X Y Z W : TangentSpace I x,
      tensor04StdAt (I := I) (M := M) A X Y Z W = -tensor04StdAt (I := I) (M := M) A Y X Z W} := by
    rw [show {A : Tensor04At (I := I) (M := M) x | ∀ X Y Z W : TangentSpace I x,
          tensor04StdAt (I := I) (M := M) A X Y Z W = -tensor04StdAt (I := I) (M := M) A Y X Z W} =
        ⋂ X : TangentSpace I x, ⋂ Y : TangentSpace I x, ⋂ Z : TangentSpace I x,
          ⋂ W : TangentSpace I x, {A : Tensor04At (I := I) (M := M) x |
            tensor04StdAt (I := I) (M := M) A X Y Z W + tensor04StdAt (I := I) (M := M) A Y X Z W = 0} from by
      ext A
      simp [eq_neg_iff_add_eq_zero]]
    exact isClosed_iInter (fun X => isClosed_iInter (fun Y => isClosed_iInter (fun Z => isClosed_iInter (fun W =>
      isClosed_eq ((hcont04 X Y Z W).add (hcont04 Y X Z W)) continuous_const))))
  have hanti2 : IsClosed {A : Tensor04At (I := I) (M := M) x | ∀ X Y Z W : TangentSpace I x,
      tensor04StdAt (I := I) (M := M) A X Y Z W = -tensor04StdAt (I := I) (M := M) A X Y W Z} := by
    rw [show {A : Tensor04At (I := I) (M := M) x | ∀ X Y Z W : TangentSpace I x,
          tensor04StdAt (I := I) (M := M) A X Y Z W = -tensor04StdAt (I := I) (M := M) A X Y W Z} =
        ⋂ X : TangentSpace I x, ⋂ Y : TangentSpace I x, ⋂ Z : TangentSpace I x,
          ⋂ W : TangentSpace I x, {A : Tensor04At (I := I) (M := M) x |
            tensor04StdAt (I := I) (M := M) A X Y Z W + tensor04StdAt (I := I) (M := M) A X Y W Z = 0} from by
      ext A
      simp [eq_neg_iff_add_eq_zero]]
    exact isClosed_iInter (fun X => isClosed_iInter (fun Y => isClosed_iInter (fun Z => isClosed_iInter (fun W =>
      isClosed_eq ((hcont04 X Y Z W).add (hcont04 X Y W Z)) continuous_const))))
  have hbianchi : IsClosed {A : Tensor04At (I := I) (M := M) x | ∀ X Y Z W : TangentSpace I x,
      tensor04StdAt (I := I) (M := M) A X Y Z W + tensor04StdAt (I := I) (M := M) A Y Z X W +
        tensor04StdAt (I := I) (M := M) A Z X Y W = 0} := by
    rw [show {A : Tensor04At (I := I) (M := M) x | ∀ X Y Z W : TangentSpace I x,
          tensor04StdAt (I := I) (M := M) A X Y Z W + tensor04StdAt (I := I) (M := M) A Y Z X W +
            tensor04StdAt (I := I) (M := M) A Z X Y W = 0} =
        ⋂ X : TangentSpace I x, ⋂ Y : TangentSpace I x, ⋂ Z : TangentSpace I x,
          ⋂ W : TangentSpace I x, {A : Tensor04At (I := I) (M := M) x |
            tensor04StdAt (I := I) (M := M) A X Y Z W + tensor04StdAt (I := I) (M := M) A Y Z X W +
              tensor04StdAt (I := I) (M := M) A Z X Y W = 0} from by
      ext A
      simp [add_assoc]]
    exact isClosed_iInter (fun X => isClosed_iInter (fun Y => isClosed_iInter (fun Z => isClosed_iInter (fun W =>
      isClosed_eq (((hcont04 X Y Z W).add (hcont04 Y Z X W)).add (hcont04 Z X Y W)) continuous_const))))
  rw [show (algebraicCurvatureTensorSubmodule (I := I) (M := M) x : Set (Tensor04At (I := I) (M := M) x)) =
      {A : Tensor04At (I := I) (M := M) x |
        (∀ X Y Z W : TangentSpace I x,
          tensor04StdAt (I := I) (M := M) A X Y Z W = -tensor04StdAt (I := I) (M := M) A Y X Z W) ∧
        (∀ X Y Z W : TangentSpace I x,
          tensor04StdAt (I := I) (M := M) A X Y Z W = -tensor04StdAt (I := I) (M := M) A X Y W Z) ∧
        (∀ X Y Z W : TangentSpace I x,
          tensor04StdAt (I := I) (M := M) A X Y Z W +
            tensor04StdAt (I := I) (M := M) A Y Z X W +
            tensor04StdAt (I := I) (M := M) A Z X Y W = 0)} from by
    ext A
    exact mem_algebraicCurvatureTensorSubmodule_iff_symmetries (I := I) (M := M)]
  rw [show {A : Tensor04At (I := I) (M := M) x |
        (∀ X Y Z W : TangentSpace I x,
          tensor04StdAt (I := I) (M := M) A X Y Z W = -tensor04StdAt (I := I) (M := M) A Y X Z W) ∧
        (∀ X Y Z W : TangentSpace I x,
          tensor04StdAt (I := I) (M := M) A X Y Z W = -tensor04StdAt (I := I) (M := M) A X Y W Z) ∧
        (∀ X Y Z W : TangentSpace I x,
          tensor04StdAt (I := I) (M := M) A X Y Z W +
            tensor04StdAt (I := I) (M := M) A Y Z X W +
            tensor04StdAt (I := I) (M := M) A Z X Y W = 0)} =
      {A : Tensor04At (I := I) (M := M) x | ∀ X Y Z W : TangentSpace I x,
          tensor04StdAt (I := I) (M := M) A X Y Z W = -tensor04StdAt (I := I) (M := M) A Y X Z W} ∩
        {A : Tensor04At (I := I) (M := M) x | ∀ X Y Z W : TangentSpace I x,
          tensor04StdAt (I := I) (M := M) A X Y Z W = -tensor04StdAt (I := I) (M := M) A X Y W Z} ∩
        {A : Tensor04At (I := I) (M := M) x | ∀ X Y Z W : TangentSpace I x,
          tensor04StdAt (I := I) (M := M) A X Y Z W +
            tensor04StdAt (I := I) (M := M) A Y Z X W +
            tensor04StdAt (I := I) (M := M) A Z X Y W = 0} from by
    ext A
    simp [and_assoc]]
  exact ((hanti1.inter hanti2).inter hbianchi).inter (hclosedE.preimage hfcont)

omit [I.Boundaryless] in
theorem fiberRegionPropagationOn_of_flatSupport
    {T : ℝ} (hT : 0 < T) [I.Boundaryless] [CompactSpace M] [NeZero (Module.finrank ℝ E)]
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn (I := I) S)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt x))
    (iota : MatrixComp M (Fin 3))
    (hiota0 : ∀ x : M, ∀ a k : Fin 3, iota 0 x a k = if a = k then 1 else 0)
    (hgram : ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Fin 3,
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota t x a b =
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota 0 x a b)
    {K : ℝ} (hK : 0 < K)
    (hinit : ∀ x : M,
      uhlenbeckPulledRm04At S basisAt iota 0 x ∈ fiberHamiltonIveyRegion basisAt K 0 x)
    (hsol : by
      letI : ∀ x : M, NormedAddCommGroup (Tensor04At (I := I) (M := M) x) :=
        fun x => @InnerProductSpace.Core.toNormedAddCommGroup ℝ (Tensor04At (I := I) (M := M) x)
          inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) (S.base.metric 0) x 4).toCore
      letI : ∀ x : M, InnerProductSpace ℝ (Tensor04At (I := I) (M := M) x) :=
        fun x => @InnerProductSpace.ofCore ℝ (Tensor04At (I := I) (M := M) x)
          inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) (S.base.metric 0) x 4).toCore.toCore
      letI : ∀ x : M, CompleteSpace (Tensor04At (I := I) (M := M) x) :=
        fun x => inferInstance
      exact IsBundleHeatReactionOn
        (V := fun x : M => Tensor04At (I := I) (M := M) x)
        (fiberRegionFlat (I := I) (M := M) S basisAt iota)
        (RealTimeInterval.closed 0 T hT.le) (flowG (I := I) S)
        (fun _ => fiberRegionSource hT (I := I) (M := M) S basisAt)
        (uhlenbeckPulledRm04At S basisAt iota))
    (hflat : by
      letI : ∀ x : M, NormedAddCommGroup (Tensor04At (I := I) (M := M) x) :=
        fun x => @InnerProductSpace.Core.toNormedAddCommGroup ℝ (Tensor04At (I := I) (M := M) x)
          inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) (S.base.metric 0) x 4).toCore
      letI : ∀ x : M, InnerProductSpace ℝ (Tensor04At (I := I) (M := M) x) :=
        fun x => @InnerProductSpace.ofCore ℝ (Tensor04At (I := I) (M := M) x)
          inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) (S.base.metric 0) x 4).toCore.toCore
      letI : ∀ x : M, CompleteSpace (Tensor04At (I := I) (M := M) x) :=
        fun x => inferInstance
      exact HasFlatSupportSectionsOn (I := I) (Set.Icc 0 T)
        (V := fun x : M => Tensor04At (I := I) (M := M) x)
        (fiberRegionFlat (I := I) (M := M) S basisAt iota)
        (regionNormalDirections (I := I) (S.base.metric 0) basisAt)
        (fiberRegionSupport hT (I := I) (M := M) S basisAt K)) :
    ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M,
      uhlenbeckPulledRm04At S basisAt iota t x ∈ fiberHamiltonIveyRegion basisAt K t x := by
  classical
  letI : ∀ x : M, NormedAddCommGroup (Tensor04At (I := I) (M := M) x) :=
    fun x => @InnerProductSpace.Core.toNormedAddCommGroup ℝ (Tensor04At (I := I) (M := M) x)
      inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) (S.base.metric 0) x 4).toCore
  letI : ∀ x : M, InnerProductSpace ℝ (Tensor04At (I := I) (M := M) x) :=
    fun x => @InnerProductSpace.ofCore ℝ (Tensor04At (I := I) (M := M) x)
      inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) (S.base.metric 0) x 4).toCore.toCore
  letI : ∀ x : M, CompleteSpace (Tensor04At (I := I) (M := M) x) :=
    fun x => inferInstance
  rcases exists_pulledRm_norm_bound (I := I) (M := M) hT S hS hdim basisAt iota hiota0 hgram horth0 with
    ⟨R, hRge, hbound⟩
  rcases regionSource_lipschitzOn_closedBall_uniform (I := I) (S.base.metric 0) basisAt horth0 hRge with
    ⟨L, hL⟩
  let hCclosed : ∀ t x, @IsClosed (Tensor04At (I := I) (M := M) x)
      (tensor04FiberNACG hT S x).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      (fiberRegionSet (I := I) (M := M) basisAt K t x) := by
    intro t x
    exact isClosed_fiberHamiltonIveyRegion hT S basisAt (τ := max t 0) hK x
  let hCconvex : ∀ t x, Convex ℝ (fiberRegionSet (I := I) (M := M) basisAt K t x) := by
    intro t x
    exact convex_fiberHamiltonIveyRegion (I := I) basisAt hK (le_max_right t 0) x
  let hCne : ∀ t x, (fiberRegionSet (I := I) (M := M) basisAt K t x).Nonempty := by
    intro t x
    exact nonempty_fiberHamiltonIveyRegion (I := I) basisAt hK (le_max_right t 0) x
  let hCzero : ∀ t x, (0 : Tensor04At (I := I) (M := M) x) ∈ fiberRegionSet (I := I) (M := M) basisAt K t x := by
    intro t x
    exact zero_mem_fiberHamiltonIveyRegion (I := I) basisAt hK (le_max_right t 0) x
  let hsupp : ∀ t x p, p ∈ fiberRegionSet (I := I) (M := M) basisAt K t x ↔
      ∀ ν : Tensor04At (I := I) (M := M) x,
        ν ∈ regionNormalDirections (I := I) (S.base.metric 0) basisAt x →
          inner ℝ ν p ≤ fiberRegionSupport hT (I := I) (M := M) S basisAt K t x ν := by
    intro t x p
    have hτ : 0 ≤ max t 0 := le_max_right t 0
    have hmain := fiberRegion_mem_iff_forall_normalDirections_full (I := I) (S.base.metric 0)
      basisAt horth0 hK hτ x p
    constructor
    · intro hp ν hν
      have hle := (hmain.mp hp) ν hν
      have hin : inner ℝ ν p = inner0S (I := I) (S.base.metric 0) x 4 ν p :=
        tensor04_fiberInner_eq (I := I) (S.base.metric 0) x ν p
      rw [fiberRegionSupport, hin]
      exact hle
    · intro hle
      apply hmain.mpr
      intro ν hν
      have hle' := hle ν hν
      have hin : inner0S (I := I) (S.base.metric 0) x 4 ν p = inner ℝ ν p :=
        (tensor04_fiberInner_eq (I := I) (S.base.metric 0) x ν p).symm
      dsimp [fiberRegionSupport] at hle'
      rwa [← hin] at hle'
  let hsupport_sup : ∀ t x ν,
      ν ∈ regionNormalDirections (I := I) (S.base.metric 0) basisAt x →
      fiberRegionSupport hT (I := I) (M := M) S basisAt K t x ν =
        sSup {r : ℝ | ∃ q : Tensor04At (I := I) (M := M) x,
          q ∈ fiberRegionSet (I := I) (M := M) basisAt K t x ∧ r = inner ℝ q ν} := by
    intro t x ν hν
    have hτ : 0 ≤ max t 0 := le_max_right t 0
    have hmain := regionSupport_eq_sSup (I := I) (S.base.metric 0) basisAt horth0 hK hτ x hν
    rw [fiberRegionSupport]
    calc
      regionSupport (I := I) (S.base.metric 0) basisAt K (max t 0) x ν
          = sSup {r : ℝ | ∃ q : Tensor04At (I := I) (M := M) x,
              q ∈ fiberHamiltonIveyRegion basisAt K (max t 0) x ∧
                r = inner0S (I := I) (S.base.metric 0) x 4 q ν} := hmain
      _ = sSup {r : ℝ | ∃ q : Tensor04At (I := I) (M := M) x,
              q ∈ fiberRegionSet (I := I) (M := M) basisAt K t x ∧ r = inner ℝ q ν} := by
            apply congrArg sSup
            ext r
            constructor
            · rintro ⟨q, hq, rfl⟩
              refine ⟨q, by simpa [fiberRegionSet] using hq, ?_⟩
              exact tensor04_fiberInner_eq (I := I) (S.base.metric 0) x q ν
            · rintro ⟨q, hq, rfl⟩
              refine ⟨q, by simpa [fiberRegionSet] using hq, ?_⟩
              exact (tensor04_fiberInner_eq (I := I) (S.base.metric 0) x q ν).symm
  let hNnormal : ∀ t x, ∀ p : Tensor04At (I := I) (M := M) x,
      p ∈ fiberRegionSet (I := I) (M := M) basisAt K t x → ∀ ν : Tensor04At (I := I) (M := M) x,
      (∀ q : Tensor04At (I := I) (M := M) x, q ∈ fiberRegionSet (I := I) (M := M) basisAt K t x →
        inner ℝ ν (q - p) ≤ 0) → ν ∈ regionNormalDirections (I := I) (S.base.metric 0) basisAt x := by
    intro t x p hp ν hnormal
    have hτ : 0 ≤ max t 0 := le_max_right t 0
    have hp' : p ∈ fiberHamiltonIveyRegion basisAt K (max t 0) x := by
      simpa [fiberRegionSet] using hp
    have hnormal' : ∀ q : Tensor04At (I := I) (M := M) x,
        q ∈ fiberHamiltonIveyRegion basisAt K (max t 0) x →
          inner0S (I := I) (S.base.metric 0) x 4 ν (q - p) ≤ 0 := by
      intro q hq
      have hq' : q ∈ fiberRegionSet (I := I) (M := M) basisAt K t x := by
        simpa [fiberRegionSet] using hq
      have hle := hnormal q hq'
      have hin : inner0S (I := I) (S.base.metric 0) x 4 ν (q - p) = inner ℝ ν (q - p) :=
        (tensor04_fiberInner_eq (I := I) (S.base.metric 0) x ν (q - p)).symm
      rwa [← hin] at hle
    exact regionNormalDirections_of_normal (I := I) (S.base.metric 0) basisAt horth0 hK hτ x hp' hnormal'
  let hCdist_cont : ContinuousOn
      (fun q : ℝ × M => Metric.infDist (uhlenbeckPulledRm04At S basisAt iota q.1 q.2)
        (fiberRegionSet (I := I) (M := M) basisAt K q.1 q.2))
      (Set.Icc 0 T ×ˢ (Set.univ : Set M)) := by
    have h := fiberInfDist_continuousOn_regionFile (I := I) (M := M) hT S hS hdim basisAt horth0 iota
      hiota0 hgram hK
    refine h.congr ?_
    intro q hq
    exact congrArg (Metric.infDist (uhlenbeckPulledRm04At S basisAt iota q.1 q.2)) (by
      dsimp [fiberRegionSet]
      rw [max_eq_left (show (0 : ℝ) ≤ q.1 from hq.1.1)])
  let hsupport_cont : ∀ ν : (x : M) → Tensor04At (I := I) (M := M) x, ∀ x : M,
      ContinuousOn (fun t : ℝ => fiberRegionSupport hT (I := I) (M := M) S basisAt K t x (ν x))
        (Set.Icc 0 T) := by
    intro ν x
    have h := regionSupport_continuousOn_time (I := I) (S.base.metric 0) basisAt (T := T) hK x (ν x)
    refine h.congr ?_
    intro t ht
    dsimp [fiberRegionSupport]
    rw [max_eq_left ht.1]
  let hsupport_time : ∀ ν : (x : M) → Tensor04At (I := I) (M := M) x,
      ∀ t : ℝ, t ∈ Set.Icc 0 T → 0 < t → ∀ x : M,
      HasDerivAt (fun s : ℝ => fiberRegionSupport hT (I := I) (M := M) S basisAt K s x (ν x))
        (fiberRegionSupportDeriv hT (I := I) (M := M) S basisAt hK t x (ν x)) t := by
    intro ν t ht htpos x
    have hmain := regionSupport_hasDerivAt_time (I := I) (S.base.metric 0) basisAt hK htpos x (ν x)
    have heq : (fun s : ℝ => fiberRegionSupport hT (I := I) (M := M) S basisAt K s x (ν x)) =ᶠ[𝓝 t]
        fun τ : ℝ => regionSupport (I := I) (S.base.metric 0) basisAt K τ x (ν x) := by
      have hpos : Set.Ioi (t / 2) ∈ 𝓝 t := Ioi_mem_nhds (half_lt_self htpos)
      filter_upwards [hpos] with s hs
      dsimp [fiberRegionSupport]
      have hmax : max s 0 = s := max_eq_left (le_of_lt (lt_trans (by positivity : (0 : ℝ) < t / 2) hs))
      rw [hmax]
    have hmain' : HasDerivAt (fun s : ℝ => fiberRegionSupport hT (I := I) (M := M) S basisAt K s x (ν x))
        (regionSupportDeriv (I := I) (S.base.metric 0) basisAt hK t x (ν x)) t :=
      hmain.congr_of_eventuallyEq heq
    simpa [fiberRegionSupportDeriv] using hmain'
  let htangent : ∀ t : ℝ, t ∈ Set.Icc 0 T → 0 < t → ∀ x : M, ∀ p : Tensor04At (I := I) (M := M) x,
      p ∈ fiberRegionSet (I := I) (M := M) basisAt K t x →
      ∀ ν : Tensor04At (I := I) (M := M) x,
        ν ∈ regionNormalDirections (I := I) (S.base.metric 0) basisAt x →
        fiberRegionSupport hT (I := I) (M := M) S basisAt K t x ν = inner ℝ ν p →
        fiberRegionSource hT (I := I) (M := M) S basisAt x p ν ≤
          fiberRegionSupportDeriv hT (I := I) (M := M) S basisAt hK t x ν := by
    intro t ht htpos x p hp ν hν htangent
    have hmax : max t 0 = t := max_eq_left ht.1
    have hp' : p ∈ fiberHamiltonIveyRegion basisAt K t x := by
      dsimp [fiberRegionSet] at hp
      rwa [hmax] at hp
    have hin : inner ℝ ν p = inner0S (I := I) (S.base.metric 0) x 4 ν p :=
      tensor04_fiberInner_eq (I := I) (S.base.metric 0) x ν p
    have hsup' : regionSupport (I := I) (S.base.metric 0) basisAt K t x ν =
        inner0S (I := I) (S.base.metric 0) x 4 ν p := by
      dsimp [fiberRegionSupport] at htangent
      rw [hmax] at htangent
      rw [hin] at htangent
      exact htangent
    exact regionSource_le_regionSupportDeriv_of_tangent (I := I) (S.base.metric 0) basisAt horth0 hK
      htpos x hp' hν hsup'
  have hres : ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M,
      uhlenbeckPulledRm04At S basisAt iota t x ∈ fiberRegionSet (I := I) (M := M) basisAt K t x :=
    bundleClosedConvex_timeDep_heat_reaction_mem_of_support_tangent
      (V := fun x : M => Tensor04At (I := I) (M := M) x)
      (flowG (I := I) S) hT
      (fiberRegionFlat (I := I) (M := M) S basisAt iota)
      (fun t x => fiberRegionSet (I := I) (M := M) basisAt K t x)
      (regionNormalDirections (I := I) (S.base.metric 0) basisAt)
      (fiberRegionSupport hT (I := I) (M := M) S basisAt K)
      (fiberRegionSupportDeriv hT (I := I) (M := M) S basisAt hK)
      hCclosed hCconvex hCne hsupp hsupport_sup hNnormal
      (fun _ => fiberRegionSource hT (I := I) (M := M) S basisAt)
      (uhlenbeckPulledRm04At S basisAt iota)
      hsol R hbound hCzero L (fun t ht x ν => by simpa [fiberRegionSource] using hL x ν)
      hCdist_cont hflat hsupport_cont hsupport_time htangent (fun x => by simpa [fiberRegionSet] using hinit x)
  intro t ht x
  have hmem := hres t ht x
  have hmax : max t 0 = t := max_eq_left ht.1
  rwa [fiberRegionSet, hmax] at hmem

end FiberMaximumPrinciple

section FiberHeatReactionSolution

open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Dim3Reaction

omit [CompleteSpace E] [FiniteDimensional Real E] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
theorem tensor04StdAt_compU_apply_all
    {x : M} (X : Tensor04At (I := I) (M := M) x)
    (U : TangentSpace I x →L[ℝ] TangentSpace I x)
    (v y z w : TangentSpace I x) :
    tensor04StdAt (I := I) (M := M) (X.compContinuousLinearMap (fun _ : Fin 4 => U)) v y z w =
      tensor04StdAt (I := I) (M := M) X (U v) (U y) (U z) (U w) := by
  change (X : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ)
      (fun i : Fin 4 => U (vec4 v y z w i)) =
    (X : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ)
      (vec4 (U v) (U y) (U z) (U w))
  congr 1
  funext i
  fin_cases i <;> simp [vec4]

omit [CompleteSpace E] [FiniteDimensional Real E] [IsManifold I ∞ M] [IsManifold I 1 M]
  [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
theorem basis_repr_uhlenbeckEndomorphism_apply_basis
    {x : M} (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (iota : MatrixComp M (Fin 3)) (t : ℝ) (a j : Fin 3) :
    basis.repr (uhlenbeckEndomorphismAt basis iota t (basis a)) j =
      iota t x a j := by
  rw [uhlenbeckEndomorphism_apply_basis]
  rw [Module.Basis.repr_sum_self basis (fun k : Fin 3 => iota t x a k)]

omit [CompleteSpace E] [FiniteDimensional Real E] [IsManifold I ∞ M] [IsManifold I 1 M]
  [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
private theorem sum_fin4_eq_sum_i_j_k_l (F : (Fin 4 → Fin 3) → ℝ) :
    (∑ J : Fin 4 → Fin 3, F J) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
        F (slots4 i j k l) := by
  classical
  let e : (Fin 4 → Fin 3) ≃ (((Fin 3 × Fin 3) × Fin 3) × Fin 3) :=
    { toFun := fun f => (((f 0, f 1), f 2), f 3)
      invFun := fun p => slots4 p.1.1.1 p.1.1.2 p.1.2 p.2
      left_inv := by
        intro f
        funext a
        fin_cases a <;> simp [slots4]
      right_inv := by
        intro p
        rcases p with ⟨⟨⟨i, j⟩, k⟩, l⟩
        simp [slots4] }
  rw [Fintype.sum_equiv e F (fun p => F (e.symm p))
    (fun x => congrArg F (e.left_inv x).symm)]
  · repeat rw [Fintype.sum_prod_type]
    rfl

variable {T : ℝ} (hT : 0 < T) [I.Boundaryless]
variable (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
variable (hS : IsSolutionOn (I := I) S)
variable (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
variable (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
variable (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt x))

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [I.Boundaryless] in
theorem pulledRmComp_eq_uhlenbeckPullbackRmInFrame
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (iota : MatrixComp M (Fin 3)) (t : ℝ) (x : M) (a b c d : Fin 3) :
    pulledRmComp S basisAt iota t x a b c d =
      uhlenbeckPullbackRmInFrame iota
        (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a))
        t x a b c d := by
  classical
  let e : Fin 3 → TangentSpace I x := fun i => uhlenbeckEndomorphismAt (basisAt x) iota t (basisAt x i)
  let P : Fin 3 → Fin 3 → ℝ := fun j i => iota t x i j
  have hP : ∀ i j : Fin 3, P j i = (basisAt x).repr (e i) j := by
    intro i j
    dsimp [e, P]
    exact (basis_repr_uhlenbeckEndomorphism_apply_basis (I := I) (basisAt x) iota t i j).symm
  have hmain := rm04Comp_expand (I := I) S t e (basisAt x) P hP a b c d
  calc
    pulledRmComp S basisAt iota t x a b c d
        = tensor04StdAt (I := I) (M := M)
            (uhlenbeckPulledRm04At S basisAt iota t x)
            (basisAt x a) (basisAt x b) (basisAt x c) (basisAt x d) := by
          rfl
    _ = tensor04StdAt (I := I) (M := M) (S.base.rm04 t x)
          (e a) (e b) (e c) (e d) := by
          rw [uhlenbeckPulledRm04At_apply]
    _ = S.base.rm04 t x (vec4 (e a) (e b) (e c) (e d)) := by
          rfl
    _ = ∑ J : Fin 4 → Fin 3,
          S.base.rm04 t x (fun p : Fin 4 => basisAt x (J p)) *
            (∏ p : Fin 4, P (J p) (slots4 a b c d p)) := hmain
    _ = ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
          tensor04StdAt (I := I) (M := M) (S.base.rm04 t x)
            (basisAt x i) (basisAt x j) (basisAt x k) (basisAt x l) *
            (iota t x a i * iota t x b j * iota t x c k * iota t x d l) := by
          rw [sum_fin4_eq_sum_i_j_k_l]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro k _
          apply Finset.sum_congr rfl
          intro l _
          rw [tensor04StdAt]
          apply congrArg₂ (fun X Y : ℝ => X * Y)
          · congr 1
            funext p
            fin_cases p <;> rfl
          · simp [slots4, P, Fin.prod_univ_four]
    _ = uhlenbeckPullbackRmInFrame iota
          (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a))
          t x a b c d := by
          simp only [uhlenbeckPullbackRmInFrame, solutionRm04CompInFrame, rm04Comp, tensor04StdAt]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro k _
          apply Finset.sum_congr rfl
          intro l _
          ring_nf


omit [CompleteSpace E] [FiniteDimensional Real E] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
omit [I.Boundaryless] in
theorem identityInvMetric_inverseInBasis_of_orthonormal
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) g x basis) :
    MetricInverseInBasis_gen (I := I) g x basis (identityInvMetric (Idx := Fin 3)) := by
  intro i j
  constructor
  · calc
      (∑ k : Fin 3, identityInvMetric (Idx := Fin 3) i k * g.inner x (basis k) (basis j))
          = g.inner x (basis i) (basis j) := by
            rw [Finset.sum_eq_single i]
            · simp [identityInvMetric]
            · intro k _ hk
              rw [identityInvMetric, diagonalInvMetric]
              rw [if_neg (Ne.symm hk)]
              ring
            · intro hi
              exact False.elim (hi (Finset.mem_univ i))
    _ = if i = j then 1 else 0 := by
          simpa [delta3] using horth i j
  · calc
      (∑ k : Fin 3, g.inner x (basis i) (basis k) * identityInvMetric (Idx := Fin 3) k j)
          = g.inner x (basis i) (basis j) := by
            rw [Finset.sum_eq_single j]
            · simp [identityInvMetric]
            · intro k _ hk
              rw [identityInvMetric, diagonalInvMetric]
              rw [if_neg hk]
              ring
            · intro hj
              exact False.elim (hj (Finset.mem_univ j))
    _ = if i = j then 1 else 0 := by
          simpa [delta3] using horth i j

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M]
  [I.Boundaryless] in
theorem fiberInner_compUhlenbeck_isometry_full
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (iota : MatrixComp M (Fin 3))
    (hiota0 : ∀ x : M, ∀ a k : Fin 3, iota 0 x a k = if a = k then 1 else 0)
    (hgram : ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Fin 3,
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota t x a b =
        movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota 0 x a b)
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt x))
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) (x : M)
    (A B : Tensor04At (I := I) (M := M) x) :
    inner0S (I := I) (S.base.metric 0) x 4
        (A.compContinuousLinearMap (fun _ : Fin 4 => uhlenbeckEndomorphismAt (basisAt x) iota t))
        (B.compContinuousLinearMap (fun _ : Fin 4 => uhlenbeckEndomorphismAt (basisAt x) iota t)) =
      inner0S (I := I) (S.base.metric t) x 4 A B := by
  classical
  let moving : Module.Basis (Fin 3) Real (TangentSpace I x) :=
    uhlenbeckMovingBasis hT S basisAt iota hiota0 hgram t ht x
  let U : TangentSpace I x →L[ℝ] TangentSpace I x :=
    uhlenbeckEndomorphismAt (basisAt x) iota t
  have horth_moving : OrthonormalBasisAt (I := I) (S.base.metric t) x moving :=
    uhlenbeckMovingBasis_orthonormalBasisAt (I := I) (M := M) hT S basisAt iota hiota0 hgram x
      (horth0 x) ht
  have hinv0 : MetricInverseInBasis_gen (I := I) (S.base.metric 0) x (basisAt x)
      (identityInvMetric (Idx := Fin 3)) :=
    identityInvMetric_inverseInBasis_of_orthonormal (I := I) (S.base.metric 0) x (basisAt x) (horth0 x)
  have hinvt : MetricInverseInBasis_gen (I := I) (S.base.metric t) x moving
      (identityInvMetric (Idx := Fin 3)) :=
    identityInvMetric_inverseInBasis_of_orthonormal (I := I) (S.base.metric t) x moving horth_moving
  have hdiag : ∀ (g : SmoothRiemannianMetric I M)
      (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
      (hinv : MetricInverseInBasis_gen (I := I) g x basis (identityInvMetric (Idx := Fin 3)))
      (A B : Tensor04At (I := I) (M := M) x),
      inner0S (I := I) g x 4 A B =
        ∑ I0 : Fin 4 → Fin 3,
          tensor0SComponent (I := I) A (fun i => basis i) I0 *
            tensor0SComponent (I := I) B (fun i => basis i) I0 := by
    intro g basis hinv A B
    rw [inner0S_eq_coord (I := I) g x 4 basis (identityInvMetric (Idx := Fin 3)) hinv A B]
    exact coordInner0S_identity_eq_sum (I := I) (x := x) 4 A B basis
  calc
    inner0S (I := I) (S.base.metric 0) x 4
        (A.compContinuousLinearMap (fun _ : Fin 4 => U))
        (B.compContinuousLinearMap (fun _ : Fin 4 => U))
        = ∑ I0 : Fin 4 → Fin 3,
            tensor0SComponent (I := I) (A.compContinuousLinearMap (fun _ : Fin 4 => U))
                (fun i => basisAt x i) I0 *
              tensor0SComponent (I := I) (B.compContinuousLinearMap (fun _ : Fin 4 => U))
                (fun i => basisAt x i) I0 :=
          hdiag (S.base.metric 0) (basisAt x) hinv0 _ _
    _ = ∑ I0 : Fin 4 → Fin 3,
            tensor0SComponent (I := I) A (fun i => moving i) I0 *
              tensor0SComponent (I := I) B (fun i => moving i) I0 := by
          apply Finset.sum_congr rfl
          intro I0 _
          rfl
    _ = inner0S (I := I) (S.base.metric t) x 4 A B :=
          (hdiag (S.base.metric t) moving hinvt A B).symm

omit [CompleteSpace E] [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M]
  [T2Space M] [I.Boundaryless] in
theorem metricTraceFirstTwo0SAt_eq_metricTrace0S2TensorInBasis
    (g : SmoothRiemannianMetric I M) {x : M} {s : ℕ}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (hinv : MetricInverseInBasis_gen (I := I) g x basis (identityInvMetric (Idx := Fin 3)))
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 2) x)
    (tail : Fin s → TangentSpace I x) :
    metricTraceFirstTwo0SAt (I := I) g T tail =
      metricTrace0S2TensorInBasis (I := I) basis (identityInvMetric (Idx := Fin 3)) T tail := by
  rw [metricTrace0S2TensorInBasis_apply]
  unfold metricTraceFirstTwo0SAt
  rw [metricTracePair0SAt_eq_sum_basis (I := I) g basis (identityInvMetric (Idx := Fin 3)) hinv]
  unfold metricTrace0S2InBasis
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [freezeFirstTwo0S_apply]


omit [CompleteSpace E] [FiniteDimensional Real E] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
omit [I.Boundaryless] in
theorem compUhlenbeck_mem_algebraicCurvatureTensorSubmodule
    {x : M}
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (iota : MatrixComp M (Fin 3)) (t : Real)
    (X : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    (X : Tensor04At (I := I) (M := M) x).compContinuousLinearMap
        (fun _ : Fin 4 => uhlenbeckEndomorphismAt (basisAt x) iota t) ∈
      algebraicCurvatureTensorSubmodule (I := I) (M := M) x := by
  have hform : IsAlgCurvForm (tensor04StdAt (I := I) (M := M) (X : Tensor04At (I := I) (M := M) x)) :=
    (mem_algebraicCurvatureTensorSubmodule (I := I) (M := M)).mp X.2
  rw [show (X : Tensor04At (I := I) (M := M) x).compContinuousLinearMap
        (fun _ : Fin 4 => uhlenbeckEndomorphismAt (basisAt x) iota t) ∈
        algebraicCurvatureTensorSubmodule (I := I) (M := M) x ↔
      IsAlgCurvForm (tensor04StdAt (I := I) (M := M)
        ((X : Tensor04At (I := I) (M := M) x).compContinuousLinearMap
          (fun _ : Fin 4 => uhlenbeckEndomorphismAt (basisAt x) iota t))) from
    mem_algebraicCurvatureTensorSubmodule (I := I) (M := M)]
  change IsAlgCurvForm (fun v y z w =>
    tensor04StdAt (I := I) (M := M)
      ((X : Tensor04At (I := I) (M := M) x).compContinuousLinearMap
        (fun _ : Fin 4 => uhlenbeckEndomorphismAt (basisAt x) iota t)) v y z w)
  simp_rw [tensor04StdAt_compU_apply_all]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x₁ x₂ y z w
    rw [map_add (uhlenbeckEndomorphismAt (basisAt x) iota t)]
    exact hform.add_left _ _ _ _ _
  · intro a u y z w
    rw [map_smul (uhlenbeckEndomorphismAt (basisAt x) iota t)]
    exact hform.smul_left _ _ _ _ _
  · intro u v y z
    exact hform.anti_first _ _ _ _
  · intro u v y z
    exact hform.anti_last _ _ _ _
  · intro u v y z
    exact hform.bianchi _ _ _ _

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M]
  [I.Boundaryless] in
theorem curvatureOperatorMatrixAt_compU_eq_moving
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (iota : MatrixComp M (Fin 3))
    (hiota0 : ∀ x : M, ∀ a k : Fin 3, iota 0 x a k = if a = k then 1 else 0)
    (hgram : ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Fin 3,
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota t x a b =
        movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota 0 x a b)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) (x : M)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    curvatureOperatorMatrixAt (I := I) x (basisAt x)
        ⟨(A : Tensor04At (I := I) (M := M) x).compContinuousLinearMap
          (fun _ : Fin 4 => uhlenbeckEndomorphismAt (basisAt x) iota t),
          compUhlenbeck_mem_algebraicCurvatureTensorSubmodule basisAt iota t A⟩ =
      curvatureOperatorMatrixAt (I := I) x
        (uhlenbeckMovingBasis hT S basisAt iota hiota0 hgram t ht x) A := by
  classical
  let moving : Module.Basis (Fin 3) Real (TangentSpace I x) :=
    uhlenbeckMovingBasis hT S basisAt iota hiota0 hgram t ht x
  ext p q
  unfold curvatureOperatorMatrixAt
  rw [tensor04StdAt_compU_apply_all (A : Tensor04At (I := I) (M := M) x)
    (uhlenbeckEndomorphismAt (basisAt x) iota t)]
  simp [uhlenbeckMovingBasis_apply]

omit [IsManifold I 2 M] [IsManifold I 3 M] [I.Boundaryless] in
theorem pulledRmComp_eq_rm_ricci_moving
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (iota : MatrixComp M (Fin 3))
    (hiota0 : ∀ x : M, ∀ a k : Fin 3, iota 0 x a k = if a = k then 1 else 0)
    (hgram : ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Fin 3,
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota t x a b =
        movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota 0 x a b)
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt x))
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) (x : M) (a b c d : Fin 3) :
    pulledRmComp S basisAt iota t x a b c d =
      rm (fun i j : Fin 3 => S.ricciAt t x (vec2 (I := I)
        (uhlenbeckMovingBasis hT S basisAt iota hiota0 hgram t ht x i)
        (uhlenbeckMovingBasis hT S basisAt iota hiota0 hgram t ht x j))) a b c d := by
  classical
  let moving : Module.Basis (Fin 3) Real (TangentSpace I x) :=
    uhlenbeckMovingBasis hT S basisAt iota hiota0 hgram t ht x
  have horth_moving : ∀ i j : Fin 3,
      (S.base.metric t).inner x (moving i) (moving j) = kd i j := by
    intro i j
    have h := uhlenbeckMovingBasis_orthonormalBasisAt (I := I) (M := M) hT S basisAt iota hiota0 hgram x
      (horth0 x) ht
    rw [h i j]
    rfl
  have hmain := rm04Comp_ortho_eq_rm (I := I) (M := M) S t (hdim x) moving horth_moving (slots4 a b c d)
  calc
    pulledRmComp S basisAt iota t x a b c d
        = tensor04StdAt (I := I) (M := M)
            (uhlenbeckPulledRm04At S basisAt iota t x)
            (basisAt x a) (basisAt x b) (basisAt x c) (basisAt x d) := by
          rfl
    _ = tensor04StdAt (I := I) (M := M) (S.base.rm04 t x)
          (moving a) (moving b) (moving c) (moving d) := by
          rw [uhlenbeckPulledRm04At_apply]
          dsimp [moving]
          simp [uhlenbeckMovingBasis_apply]
    _ = S.base.rm04 t x (fun p : Fin 4 => moving (slots4 a b c d p)) := by
          rw [tensor04StdAt]
          apply congrArg (S.base.rm04 t x)
          funext p
          fin_cases p <;> simp [vec4, slots4]
    _ = rm (fun i j : Fin 3 => S.ricciAt t x (vec2 (I := I) (moving i) (moving j))) a b c d := by
          simpa using hmain


omit [CompleteSpace E] [IsManifold I ∞ M] [IsManifold I 2 M] [IsManifold I 3 M]
  [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
private theorem tangentSection_cont_constBase_of_fiber_cont
    {x : M} {P : Type*} [TopologicalSpace P] {w : P → TangentSpace I x}
    (hw : Continuous w) :
    Continuous (fun p : P =>
      TotalSpace.mk' E (E := fun y : M => TangentSpace I y) x (w p)) := by
  classical
  let e := trivializationAt E (TangentSpace I) x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x
  have hlin : Continuous (fun p : P => e.linearMapAt ℝ x (w p)) := by
    have h1 : e.linearMapAt ℝ x = e.linearEquivAt ℝ x hx := e.linearMapAt_def_of_mem hx
    rw [h1]
    exact (e.linearEquivAt ℝ x hx).toLinearMap.continuous_of_finiteDimensional.comp hw
  have hpair : ContinuousOn (fun p : P => (x, e.linearMapAt ℝ x (w p))) univ := by
    exact ContinuousOn.prodMk continuousOn_const hlin.continuousOn
  have hsec : ContinuousOn (fun p : P =>
      TotalSpace.mk' E (E := fun y : M => TangentSpace I y) x (e.symm x (e.linearMapAt ℝ x (w p)))) univ := by
    have hc := e.continuousOn_symm.comp hpair (by intro p _; exact ⟨hx, trivial⟩)
    exact hc
  have hcont : Continuous (fun p : P =>
      TotalSpace.mk' E (E := fun y : M => TangentSpace I y) x (e.symm x (e.linearMapAt ℝ x (w p)))) :=
    continuousOn_univ.mp hsec
  refine hcont.congr ?_
  intro p
  congr 1
  rw [e.linearMapAt_apply, if_pos hx]
  rw [e.symm_apply_apply_mk hx (w p)]

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M]
  [I.Boundaryless] in
theorem iotaT_mul_iota_eq_gInv
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (iota : MatrixComp M (Fin 3))
    (hiota0 : ∀ x : M, ∀ a k : Fin 3, iota 0 x a k = if a = k then 1 else 0)
    (hgram : ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Fin 3,
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota t x a b =
        movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota 0 x a b)
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt x))
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) (x : M) (j j' : Fin 3) :
    (∑ e : Fin 3, iota t x e j * iota t x e j') =
      solutionInverseMetricComponents (I := I) (M := M) S basisAt t x j j' := by
  classical
  let Mtx : Matrix (Fin 3) (Fin 3) ℝ := solutionGramMatrix (I := I) (M := M) S basisAt t x
  let L : Matrix (Fin 3) (Fin 3) ℝ := fun a k => iota t x a k
  have hMunit : IsUnit Mtx.det :=
    solutionGramMatrix_det_isUnit (I := I) (M := M) S basisAt t x
  have hgramδ : ∀ a b : Fin 3,
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota t x a b =
        if a = b then 1 else 0 := by
    intro a b
    have h1 := hgram t ht x a b
    have h2 : movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota 0 x a b =
        if a = b then 1 else 0 := by
      unfold movingFrameGramInFrame
      rw [Finset.sum_eq_single a]
      · rw [Finset.sum_eq_single b]
        · have haa : iota 0 x a a = 1 := by rw [hiota0 x a a, if_pos rfl]
          have hbb : iota 0 x b b = 1 := by rw [hiota0 x b b, if_pos rfl]
          rw [haa, hbb]
          norm_num
          change metricCompInFrame (I := I) S (fun a x => basisAt x a) 0 x a b = if a = b then 1 else 0
          simpa [metricCompInFrame, delta3] using horth0 x a b
        · intro k _ hk
          rw [hiota0 x b k]
          rw [if_neg (Ne.symm hk)]
          simp
        · intro hb
          exact False.elim (hb (Finset.mem_univ b))
      · intro k _ hk
        rw [hiota0 x a k]
        rw [if_neg (Ne.symm hk)]
        simp
      · intro ha
        exact False.elim (ha (Finset.mem_univ a))
    rw [h1, h2]
  have horth : ∀ a b : Fin 3, (L * Mtx * L.transpose) a b = if a = b then 1 else 0 := by
    intro a b
    calc
      (L * Mtx * L.transpose) a b
          = movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota t x a b := by
            unfold movingFrameGramInFrame
            simp only [Matrix.mul_apply, Matrix.transpose_apply, L, Mtx,
              solutionGramMatrix, Matrix.of_apply, Finset.sum_mul]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = if a = b then 1 else 0 := hgramδ a b
  have horthM : L * Mtx * L.transpose = 1 := by
    ext a b
    rw [Matrix.one_apply]
    exact horth a b
  have hcomm : L.transpose * (L * Mtx) = 1 := by
    exact mul_eq_one_comm.2 (by simpa [Matrix.mul_assoc] using horthM)
  have hLLM : (L.transpose * L) * Mtx = 1 := by
    simpa [Matrix.mul_assoc] using hcomm
  have hLL : L.transpose * L = Mtx⁻¹ := by
    calc
      L.transpose * L = (L.transpose * L) * 1 := by rw [Matrix.mul_one]
      _ = (L.transpose * L) * (Mtx * Mtx⁻¹) := by rw [← Matrix.mul_nonsing_inv Mtx hMunit]
      _ = ((L.transpose * L) * Mtx) * Mtx⁻¹ := by
            simp only [Matrix.mul_assoc]
      _ = Mtx⁻¹ := by
            rw [hLLM]
            simp
  have hentry := congrFun (congrFun hLL j) j'
  calc
    (∑ e : Fin 3, iota t x e j * iota t x e j')
        = (L.transpose * L) j j' := by
          simp [Matrix.mul_apply, L]
    _ = Mtx⁻¹ j j' := hentry
    _ = solutionInverseMetricComponents (I := I) (M := M) S basisAt t x j j' := by
          rfl


omit [IsManifold I 2 M] [IsManifold I 3 M] [I.Boundaryless] in
theorem laplacianAt_congr_flowG
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) {t : ℝ} {x : M}
    {f h : M → ℝ}
    (hf : ContMDiffAt I 𝓘(Real, Real) ∞ f x)
    (hh : ContMDiffAt I 𝓘(Real, Real) ∞ h x)
    (heq : f =ᶠ[𝓝 x] h) :
    laplacianAt (I := I) (flowG (I := I) S) t f x =
      laplacianAt (I := I) (flowG (I := I) S) t h x := by
  unfold laplacianAt
  change laplacian (I := I) (S.base.connection t) (S.base.metric t) f x =
    laplacian (I := I) (S.base.connection t) (S.base.metric t) h x
  exact laplacian_congr_of_eventuallyEq (I := I) (S.base.connection t) (S.base.metric t) hf hh heq

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [I.Boundaryless] in
theorem pulledRmComp_entry_continuousOn_time
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn (I := I) S)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (iota : MatrixComp M (Fin 3))
    (hiota_cont : ∀ x : M, ContinuousOn (fun t : ℝ => iota t x) (Set.Icc 0 T))
    (x : M) (a b c d : Fin 3) :
    ContinuousOn (fun s : ℝ => pulledRmComp S basisAt iota s x a b c d) (Set.Icc 0 T) := by
  classical
  rw [continuousOn_iff_continuous_restrict]
  let P := {s : ℝ // s ∈ Set.Icc 0 T}
  have hA : Tensor0SFamilyContinuousOnSet (I := I) (M := M) 4 (Set.Icc 0 T)
      (fun t y => S.base.rm04 t y) := by
    exact Tensor0SFamilyContinuousOnSet.mono (I := I) (M := M) hS.rm04Cont (by intro s hs; exact hs)
  have hiota_entry : ∀ k j : Fin 3, Continuous (fun p : P => iota p.1 x k j) := by
    intro k j
    have h1 : ∀ i : Fin 3, ContinuousOn (fun t : ℝ => iota t x i) (Set.Icc 0 T) :=
      continuousOn_pi.mp (hiota_cont x)
    have h2 : ∀ j' : Fin 3, ContinuousOn (fun t : ℝ => iota t x k j') (Set.Icc 0 T) :=
      continuousOn_pi.mp (h1 k)
    exact (h2 j).comp_continuous continuous_subtype_val (by intro p; exact p.2)
  have hU : ∀ k : Fin 3, Continuous (fun p : P =>
      uhlenbeckEndomorphismAt (basisAt x) iota p.1 (basisAt x k)) := by
    intro k
    have hsum : (fun p : P => uhlenbeckEndomorphismAt (basisAt x) iota p.1 (basisAt x k)) =
        fun p : P => ∑ j : Fin 3, iota p.1 x k j • basisAt x j := by
      funext p
      exact uhlenbeckEndomorphism_apply_basis (basisAt x) iota p.1 k
    rw [hsum]
    refine continuous_finset_sum Finset.univ ?_
    intro j _
    exact (hiota_entry k j).smul continuous_const
  have heval := Tensor0SFamilyContinuousOnSet.eval_continuous (I := I) (M := M) (s := 4)
    (K := Set.Icc 0 T) (A := fun t y => S.base.rm04 t y) hA
    (P := P) (τ := fun p : P => p.1) (b := fun p : P => x)
    continuous_subtype_val (fun p : P => p.2) continuous_const
    (v := fun n : Fin 4 => fun p : P =>
      vec4 (uhlenbeckEndomorphismAt (basisAt x) iota p.1 (basisAt x a))
           (uhlenbeckEndomorphismAt (basisAt x) iota p.1 (basisAt x b))
           (uhlenbeckEndomorphismAt (basisAt x) iota p.1 (basisAt x c))
           (uhlenbeckEndomorphismAt (basisAt x) iota p.1 (basisAt x d)) n)
    (by
      intro n
      fin_cases n
      · change Continuous (fun p : P =>
          TotalSpace.mk' E (E := fun y : M => TangentSpace I y) x
            (uhlenbeckEndomorphismAt (basisAt x) iota p.1 (basisAt x a)))
        exact tangentSection_cont_constBase_of_fiber_cont (I := I) (hU a)
      · change Continuous (fun p : P =>
          TotalSpace.mk' E (E := fun y : M => TangentSpace I y) x
            (uhlenbeckEndomorphismAt (basisAt x) iota p.1 (basisAt x b)))
        exact tangentSection_cont_constBase_of_fiber_cont (I := I) (hU b)
      · change Continuous (fun p : P =>
          TotalSpace.mk' E (E := fun y : M => TangentSpace I y) x
            (uhlenbeckEndomorphismAt (basisAt x) iota p.1 (basisAt x c)))
        exact tangentSection_cont_constBase_of_fiber_cont (I := I) (hU c)
      · change Continuous (fun p : P =>
          TotalSpace.mk' E (E := fun y : M => TangentSpace I y) x
            (uhlenbeckEndomorphismAt (basisAt x) iota p.1 (basisAt x d)))
        exact tangentSection_cont_constBase_of_fiber_cont (I := I) (hU d))
  refine heval.congr ?_
  intro p
  unfold pulledRmComp
  change S.base.rm04 p.1 x (fun i : Fin 4 =>
    vec4 (uhlenbeckEndomorphismAt (basisAt x) iota p.1 (basisAt x a))
         (uhlenbeckEndomorphismAt (basisAt x) iota p.1 (basisAt x b))
         (uhlenbeckEndomorphismAt (basisAt x) iota p.1 (basisAt x c))
         (uhlenbeckEndomorphismAt (basisAt x) iota p.1 (basisAt x d)) i) =
    tensor04StdAt (I := I) (M := M) (uhlenbeckPulledRm04At S basisAt iota p.1 x)
      (basisAt x a) (basisAt x b) (basisAt x c) (basisAt x d)
  rw [uhlenbeckPulledRm04At_apply]
  rfl


end FiberHeatReactionSolution

section FiberHeatReactionSolutionProof

open DifferentialGeometry.Tensor.Coordinates

omit [CompleteSpace E] [FiniteDimensional Real E] [IsManifold I ∞ M] [IsManifold I 1 M]
  [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
private def succPerm {s : ℕ} (e : Equiv.Perm (Fin s)) : Equiv.Perm (Fin (s + 1)) where
  toFun := fun i => Fin.cases (0 : Fin (s + 1)) (fun i' : Fin s => Fin.succ (e i')) i
  invFun := fun i => Fin.cases (0 : Fin (s + 1)) (fun i' : Fin s => Fin.succ (e.symm i')) i
  left_inv := by
    intro i
    cases i using Fin.cases with
    | zero => rfl
    | succ i' => simp
  right_inv := by
    intro i
    cases i using Fin.cases with
    | zero => rfl
    | succ i' => simp

omit [CompleteSpace E] [FiniteDimensional Real E] [IsManifold I ∞ M] [IsManifold I 1 M]
  [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
private theorem fin_cons_comp_succPerm {s : ℕ} {V : Type*} (u : V) (f : Fin s → V)
    (e : Equiv.Perm (Fin s)) :
    (Fin.cons u f) ∘ succPerm e = Fin.cons u (f ∘ e) := by
  funext i
  cases i using Fin.cases with
  | zero => simp [succPerm]
  | succ i' => simp [succPerm, Function.comp_def]

omit [CompleteSpace E] [FiniteDimensional Real E] [IsManifold I ∞ M] [IsManifold I 1 M]
  [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
private theorem fin_cons_tail {s : ℕ} {V : Type*} (f : Fin (s + 1) → V) :
    Fin.cons (f 0) (fun i : Fin s => f (i.succ)) = f := by
  funext i
  cases i using Fin.cases with
  | zero => simp
  | succ i' => simp

omit [CompleteSpace E] [FiniteDimensional Real E] [IsManifold I ∞ M] [IsManifold I 1 M]
  [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
private theorem update_comp_perm {s : ℕ} {V : Type*} (e : Equiv.Perm (Fin s))
    (slots : Fin s → V) (a : Fin s) (w : V) :
    Function.update (fun b : Fin s => slots (e b)) a w =
      (Function.update slots (e a) w) ∘ e := by
  funext b
  by_cases hb : b = a
  · subst hb
    simp [Function.update]
  · have hne : e b ≠ e a := fun h => hb (e.injective h)
    simp [Function.update, hb, hne]

omit [CompleteSpace E] [FiniteDimensional Real E] [IsManifold I ∞ M] [IsManifold I 1 M]
  [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
private def finCycle012 : Equiv.Perm (Fin 4) where
  toFun := fun i => if i = 0 then 1 else if i = 1 then 2 else if i = 2 then 0 else 3
  invFun := fun i => if i = 0 then 2 else if i = 1 then 0 else if i = 2 then 1 else 3
  left_inv := by intro i; fin_cases i <;> simp
  right_inv := by intro i; fin_cases i <;> simp

omit [CompleteSpace E] [FiniteDimensional Real E] [IsManifold I ∞ M] [IsManifold I 1 M]
  [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
private theorem vec4_comp_swap01 {x : M} (slots : Fin 4 → TangentSpace I x) :
    (fun a : Fin 4 => slots (Equiv.swap (0 : Fin 4) (1 : Fin 4) a)) =
      vec4 (slots 1) (slots 0) (slots 2) (slots 3) := by
  funext a
  cases a using Fin.cases with
  | zero => simp [vec4]
  | succ a0 =>
      cases a0 using Fin.cases with
      | zero => simp [vec4]
      | succ a1 =>
          cases a1 using Fin.cases with
          | zero => simp [vec4, Equiv.swap_apply_def]
          | succ a2 =>
              cases a2 using Fin.cases with
              | zero => simp [vec4, Equiv.swap_apply_def]
              | succ a3 => exact Fin.elim0 a3

omit [CompleteSpace E] [FiniteDimensional Real E] [IsManifold I ∞ M] [IsManifold I 1 M]
  [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
private theorem vec4_comp_swap23 {x : M} (slots : Fin 4 → TangentSpace I x) :
    (fun a : Fin 4 => slots (Equiv.swap (2 : Fin 4) (3 : Fin 4) a)) =
      vec4 (slots 0) (slots 1) (slots 3) (slots 2) := by
  funext a
  cases a using Fin.cases with
  | zero => simp [vec4, Equiv.swap_apply_def]
  | succ a0 =>
      cases a0 using Fin.cases with
      | zero => simp [vec4, Equiv.swap_apply_def]
      | succ a1 =>
          cases a1 using Fin.cases with
          | zero => simp [vec4]
          | succ a2 =>
              cases a2 using Fin.cases with
              | zero => simp [vec4]
              | succ a3 => exact Fin.elim0 a3

omit [CompleteSpace E] [FiniteDimensional Real E] [IsManifold I ∞ M] [IsManifold I 1 M]
  [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
private theorem vec4_comp_cycle012 {x : M} (slots : Fin 4 → TangentSpace I x) :
    (fun a : Fin 4 => slots (finCycle012 a)) =
      vec4 (slots 1) (slots 2) (slots 0) (slots 3) := by
  funext a
  cases a using Fin.cases with
  | zero => simp [vec4, finCycle012]
  | succ a0 =>
      cases a0 using Fin.cases with
      | zero => simp [vec4, finCycle012]
      | succ a1 =>
          cases a1 using Fin.cases with
          | zero => simp [vec4, finCycle012]
          | succ a2 =>
              cases a2 using Fin.cases with
              | zero => simp [vec4, finCycle012]
              | succ a3 => exact Fin.elim0 a3

omit [CompleteSpace E] [FiniteDimensional Real E] [IsManifold I ∞ M] [IsManifold I 1 M]
  [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
private theorem vec4_comp_cycle012_sq {x : M} (slots : Fin 4 → TangentSpace I x) :
    (fun a : Fin 4 => slots ((finCycle012.trans finCycle012) a)) =
      vec4 (slots 2) (slots 0) (slots 1) (slots 3) := by
  funext a
  cases a using Fin.cases with
  | zero => simp [vec4, finCycle012]
  | succ a0 =>
      cases a0 using Fin.cases with
      | zero => simp [vec4, finCycle012]
      | succ a1 =>
          cases a1 using Fin.cases with
          | zero => simp [vec4, finCycle012]
          | succ a2 =>
              cases a2 using Fin.cases with
              | zero => simp [vec4, finCycle012]
              | succ a3 => exact Fin.elim0 a3

omit [CompleteSpace E] [FiniteDimensional Real E] [IsManifold I ∞ M] [IsManifold I 1 M]
  [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
private theorem metricTraceInput_eq_cons_cons {x : M} {s : ℕ}
    (X Y : TangentSpace I x) (tail : Fin s → TangentSpace I x) :
    metricTraceInput (I := I) X Y tail = Fin.cons X (Fin.cons Y tail) := by
  rfl

omit [CompleteSpace E] [FiniteDimensional Real E] [IsManifold I ∞ M] [IsManifold I 1 M]
  [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
private theorem extDerivFun_zero_at {x : M} (v : TangentSpace I x) :
    extDerivFun (I := I) (fun _ : M => (0 : Real)) x v = 0 := by
  rw [DifferentialGeometry.extDerivFun_real_eq_mfderiv (I := I) (fun _ : M => (0 : Real)) x v]
  simp
  rfl

omit [CompleteSpace E] [FiniteDimensional Real E] [IsManifold I ∞ M] [IsManifold I 1 M]
  [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
private theorem mdiffAt_const_mul {f : M → ℝ} {x : M} (c : ℝ)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x) :
    MDifferentiableAt I 𝓘(Real, Real) (fun p : M => c * f p) x := by
  have hfun : (fun p : M => c * f p) = f * (fun _ : M => c) := by
    funext p
    simp [Pi.mul_apply, mul_comm]
  rw [hfun]
  exact hf.mul (mdifferentiableAt_const (I := I) (I' := 𝓘(Real, Real)) (c := c) (x := x))

omit [CompleteSpace E] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
theorem TotalNabla0SRealizes.deriv_linear_combination {s : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    {nablaAlpha : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1)}
    (h : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s cov α nablaAlpha)
    {ι : Type*} [Fintype ι]
    (perms : ι → Equiv.Perm (Fin s)) (c : ι → ℝ)
    (hid : ∀ p : M, ∀ slots : Fin s → TangentSpace I p,
      (∑ k : ι, c k * α p (fun a : Fin s => slots (perms k a))) = 0)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (V : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x : M) :
    (∑ k : ι, c k * nablaAlpha x (Fin.cons (X x) (fun a : Fin s => V (perms k a) x))) = 0 := by
  classical
  have hEV : ∀ k : ι,
      nablaAlpha x (Fin.cons (X x) (fun a : Fin s => V (perms k a) x)) =
        extDerivFun (I := I) (fun p : M => α p (fun a : Fin s => V (perms k a) p)) x (X x) -
          ∑ a : Fin s, α x (Function.update (fun b : Fin s => V (perms k b) x) a
            ((cov (fun p : M => V (perms k a) p) x) (X x))) := by
    intro k
    exact TotalNabla0SRealizes.eval_smooth_slots (I := I) h X (fun a : Fin s => V (perms k a)) x
  have hgdiff : ∀ k : ι, MDifferentiableAt I 𝓘(Real, Real)
      (fun p : M => α p (fun a : Fin s => V (perms k a) p)) x := by
    intro k
    exact (tensor0SField_eval_smooth_slots_contMDiffAt (I := I) α
      (fun a : Fin s => V (perms k a)) x).mdifferentiableAt (by simp)
  have hgzero : (fun p : M => ∑ k : ι, c k * α p (fun a : Fin s => V (perms k a) p)) =ᶠ[𝓝 x]
      fun _ : M => (0 : Real) := by
    filter_upwards with p
    exact hid p (fun a : Fin s => V a p)
  have hExt : (∑ k : ι, c k * extDerivFun (I := I)
      (fun p : M => α p (fun a : Fin s => V (perms k a) p)) x (X x)) = 0 := by
    calc
      (∑ k : ι, c k * extDerivFun (I := I)
          (fun p : M => α p (fun a : Fin s => V (perms k a) p)) x (X x))
          = ∑ k : ι, extDerivFun (I := I)
              (fun p : M => c k * α p (fun a : Fin s => V (perms k a) p)) x (X x) := by
            refine Finset.sum_congr rfl ?_
            intro k _
            rw [extDerivFun_const_mul_apply (I := I) (c k) (X x) (hgdiff k)]
      _ = extDerivFun (I := I)
            (fun p : M => ∑ k : ι, c k * α p (fun a : Fin s => V (perms k a) p)) x (X x) := by
          have hfun : (fun p : M => ∑ k : ι, c k * α p (fun a : Fin s => V (perms k a) p)) =
              Finset.univ.sum (fun k : ι => fun p : M => c k * α p (fun a : Fin s => V (perms k a) p)) := by
            funext p
            simp [Finset.sum_apply]
          rw [hfun]
          rw [extDerivFun_finset_sum (I := I) (t := Finset.univ)
            (f := fun k : ι => fun p : M => c k * α p (fun a : Fin s => V (perms k a) p))
            (x := x) (v := X x) (by
              intro k _
              exact mdiffAt_const_mul (c k) (hgdiff k))]
      _ = 0 := by
          rw [extDerivFun_congr_eventually (I := I) (v := X x) hgzero]
          exact extDerivFun_zero_at (I := I) (X x)
  have hreindex : ∀ k : ι,
      (∑ a : Fin s, α x (Function.update (fun b : Fin s => V (perms k b) x) a
          ((cov (fun p : M => V (perms k a) p) x) (X x)))) =
        ∑ a' : Fin s, α x ((Function.update (fun b : Fin s => V b x) a'
          ((cov (fun p : M => V a' p) x) (X x))) ∘ (perms k)) := by
    intro k
    calc
      (∑ a : Fin s, α x (Function.update (fun b : Fin s => V (perms k b) x) a
          ((cov (fun p : M => V (perms k a) p) x) (X x))))
          = ∑ a' : Fin s, α x (Function.update (fun b : Fin s => V (perms k b) x) ((perms k).symm a')
              ((cov (fun p : M => V a' p) x (X x)))) := by
            rw [← Equiv.sum_comp (perms k).symm (fun a : Fin s =>
              α x (Function.update (fun b : Fin s => V (perms k b) x) a
                ((cov (fun p : M => V (perms k a) p) x (X x)))))]
            refine Finset.sum_congr rfl ?_
            intro a' _
            congr 1
            simp [Equiv.apply_symm_apply]
      _ = ∑ a' : Fin s, α x ((Function.update (fun b : Fin s => V b x) a'
              ((cov (fun p : M => V a' p) x) (X x))) ∘ (perms k)) := by
            refine Finset.sum_congr rfl ?_
            intro a' _
            rw [update_comp_perm (perms k) (fun b : Fin s => V b x) ((perms k).symm a')
              (cov (fun p : M => V a' p) x (X x))]
            simp [Equiv.apply_symm_apply, Function.comp_def]
  have hCorr : (∑ k : ι, c k * (∑ a : Fin s, α x
      (Function.update (fun b : Fin s => V (perms k b) x) a
        ((cov (fun p : M => V (perms k a) p) x) (X x))))) = 0 := by
    calc
      (∑ k : ι, c k * (∑ a : Fin s, α x
          (Function.update (fun b : Fin s => V (perms k b) x) a
            ((cov (fun p : M => V (perms k a) p) x) (X x)))))
          = ∑ k : ι, c k * (∑ a' : Fin s, α x ((Function.update (fun b : Fin s => V b x) a'
              ((cov (fun p : M => V a' p) x) (X x))) ∘ (perms k))) := by
            refine Finset.sum_congr rfl ?_
            intro k _
            rw [hreindex k]
      _ = ∑ a' : Fin s, ∑ k : ι, c k * α x ((Function.update (fun b : Fin s => V b x) a'
              ((cov (fun p : M => V a' p) x) (X x))) ∘ (perms k)) := by
            have hmul : (∑ k : ι, c k * (∑ a' : Fin s, α x ((Function.update (fun b : Fin s => V b x) a'
                  ((cov (fun p : M => V a' p) x) (X x))) ∘ (perms k)))) =
                ∑ k : ι, ∑ a' : Fin s, c k * α x ((Function.update (fun b : Fin s => V b x) a'
                  ((cov (fun p : M => V a' p) x) (X x))) ∘ (perms k)) := by
              refine Finset.sum_congr rfl ?_
              intro k _
              calc
                c k * (∑ a' : Fin s, α x ((Function.update (fun b : Fin s => V b x) a'
                      ((cov (fun p : M => V a' p) x) (X x))) ∘ (perms k)))
                    = (∑ a' : Fin s, α x ((Function.update (fun b : Fin s => V b x) a'
                          ((cov (fun p : M => V a' p) x) (X x))) ∘ (perms k))) * c k := by
                        rw [mul_comm]
                _ = ∑ a' : Fin s, (α x ((Function.update (fun b : Fin s => V b x) a'
                          ((cov (fun p : M => V a' p) x) (X x))) ∘ (perms k))) * c k := by
                        rw [Finset.sum_mul]
                _ = ∑ a' : Fin s, c k * α x ((Function.update (fun b : Fin s => V b x) a'
                          ((cov (fun p : M => V a' p) x) (X x))) ∘ (perms k)) := by
                        refine Finset.sum_congr rfl ?_
                        intro a' _
                        rw [mul_comm]
            rw [hmul]
            rw [Finset.sum_comm]
      _ = 0 := by
            refine Finset.sum_eq_zero ?_
            intro a' _
            simpa [Function.comp_def] using
              (hid x (Function.update (fun b : Fin s => V b x) a'
                ((cov (fun p : M => V a' p) x) (X x))))
  calc
    (∑ k : ι, c k * nablaAlpha x (Fin.cons (X x) (fun a : Fin s => V (perms k a) x)))
        = ∑ k : ι, c k * (extDerivFun (I := I)
            (fun p : M => α p (fun a : Fin s => V (perms k a) p)) x (X x) -
          ∑ a : Fin s, α x (Function.update (fun b : Fin s => V (perms k b) x) a
            ((cov (fun p : M => V (perms k a) p) x) (X x)))) := by
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [hEV k]
    _ = (∑ k : ι, c k * extDerivFun (I := I)
          (fun p : M => α p (fun a : Fin s => V (perms k a) p)) x (X x)) -
        (∑ k : ι, c k * (∑ a : Fin s, α x
          (Function.update (fun b : Fin s => V (perms k b) x) a
            ((cov (fun p : M => V (perms k a) p) x) (X x))))) := by
          simp [Finset.sum_sub_distrib, mul_sub]
    _ = 0 := by
          rw [hExt, hCorr]
          ring

end FiberHeatReactionSolutionProof

omit [CompleteSpace E] [FiniteDimensional Real E] [IsManifold I ∞ M] [IsManifold I 1 M]
  [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
private theorem vec4_self {x : M} (slots : Fin 4 → TangentSpace I x) :
    (fun a : Fin 4 => slots a) = vec4 (slots 0) (slots 1) (slots 2) (slots 3) := by
  funext a
  cases a using Fin.cases with
  | zero => simp [vec4]
  | succ a0 =>
      cases a0 using Fin.cases with
      | zero => simp [vec4]
      | succ a1 =>
          cases a1 using Fin.cases with
          | zero => simp [vec4]
          | succ a2 =>
              cases a2 using Fin.cases with
              | zero => simp [vec4]
              | succ a3 => exact Fin.elim0 a3

section RoughLapAlgebraic

variable {D : RealTimeInterval}

omit [SigmaCompactSpace M] in
theorem nablaKRm04Field_one_anti12_cond
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M)
    (u : TangentSpace I x) (slots : Fin 4 → TangentSpace I x) :
    (nablaKRm04Field (I := I) S t 1 x)
        (Fin.cons u (slots ∘ Equiv.swap (0 : Fin 4) (1 : Fin 4))) +
      (nablaKRm04Field (I := I) S t 1 x) (Fin.cons u slots) = 0 := by
  classical
  let X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    (ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x u).choose
  have hX : X x = u :=
    (ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x u).choose_spec
  let V : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    fun a => (ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x (slots a)).choose
  have hV : ∀ a : Fin 4, V a x = slots a := fun a =>
    (ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x (slots a)).choose_spec
  let perms : Bool → Equiv.Perm (Fin 4) :=
    fun k => if k then Equiv.swap (0 : Fin 4) (1 : Fin 4) else 1
  let c : Bool → ℝ := fun _ => 1
  have hhid : ∀ p : M, ∀ s : Fin 4 → TangentSpace I p,
      (∑ k : Bool, c k * (S.base.rm04 t p) (fun a : Fin 4 => s (perms k a))) = 0 := by
    intro p s
    have hA : (S.base.rm04 t p) = metricRm04At (I := I) (M := M) (S.base.metric t) p := by
      rfl
    have hform := (mem_algebraicCurvatureTensorSubmodule_iff_symmetries (I := I) (M := M)).1
      (metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) (S.base.metric t) p)
    have h1 := hform.1 (s 0) (s 1) (s 2) (s 3)
    rw [Fintype.sum_bool]
    change (1 : ℝ) * (S.base.rm04 t p)
          (fun a : Fin 4 => s (Equiv.swap (0 : Fin 4) (1 : Fin 4) a)) +
      (1 : ℝ) * (S.base.rm04 t p) (fun a : Fin 4 => s a) = 0
    simp only [one_mul]
    rw [vec4_comp_swap01 s, vec4_self s, hA]
    change tensor04StdAt (I := I) (M := M) (metricRm04At (I := I) (M := M) (S.base.metric t) p)
        (s 1) (s 0) (s 2) (s 3) +
      tensor04StdAt (I := I) (M := M) (metricRm04At (I := I) (M := M) (S.base.metric t) p)
        (s 0) (s 1) (s 2) (s 3) = 0
    rw [h1]
    ring
  have hmain := TotalNabla0SRealizes.deriv_linear_combination
    (I := I) (s := 4) (cov := S.family.connection t)
    (α := S.base.rm04 t) (nablaAlpha := nablaKRm04Field (I := I) S t 1)
    (h := nablaKRm04Field_realizes (I := I) S t 0)
    (perms := perms) (c := c)
    (hid := hhid) X V x
  have hsum' : (nablaKRm04Field (I := I) S t 1 x)
        (Fin.cons u (fun a : Fin 4 => V (Equiv.swap (0 : Fin 4) (1 : Fin 4) a) x)) +
      (nablaKRm04Field (I := I) S t 1 x) (Fin.cons u (fun a : Fin 4 => V a x)) = 0 := by
    rw [Fintype.sum_bool] at hmain
    rw [hX] at hmain
    change (1 : ℝ) * (nablaKRm04Field (I := I) S t 1 x)
        (Fin.cons u (fun a : Fin 4 => V (Equiv.swap (0 : Fin 4) (1 : Fin 4) a) x)) +
      (1 : ℝ) * (nablaKRm04Field (I := I) S t 1 x) (Fin.cons u (fun a : Fin 4 => V a x)) = 0 at hmain
    simpa using hmain
  have hVat : (fun a : Fin 4 => V a x) = slots := by
    funext a
    exact hV a
  have hswapV : (fun a : Fin 4 => V (Equiv.swap (0 : Fin 4) (1 : Fin 4) a) x) =
      slots ∘ Equiv.swap (0 : Fin 4) (1 : Fin 4) := by
    funext a
    exact hV (Equiv.swap (0 : Fin 4) (1 : Fin 4) a)
  calc
    (nablaKRm04Field (I := I) S t 1 x)
        (Fin.cons u (slots ∘ Equiv.swap (0 : Fin 4) (1 : Fin 4))) +
      (nablaKRm04Field (I := I) S t 1 x) (Fin.cons u slots)
        = (nablaKRm04Field (I := I) S t 1 x)
            (Fin.cons u (fun a : Fin 4 => V (Equiv.swap (0 : Fin 4) (1 : Fin 4) a) x)) +
          (nablaKRm04Field (I := I) S t 1 x) (Fin.cons u (fun a : Fin 4 => V a x)) := by
          rw [← hswapV, ← hVat]
    _ = 0 := hsum'

omit [SigmaCompactSpace M] in
theorem nablaKRm04Field_one_anti34_cond
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M)
    (u : TangentSpace I x) (slots : Fin 4 → TangentSpace I x) :
    (nablaKRm04Field (I := I) S t 1 x)
        (Fin.cons u (slots ∘ Equiv.swap (2 : Fin 4) (3 : Fin 4))) +
      (nablaKRm04Field (I := I) S t 1 x) (Fin.cons u slots) = 0 := by
  classical
  let X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    (ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x u).choose
  have hX : X x = u :=
    (ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x u).choose_spec
  let V : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    fun a => (ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x (slots a)).choose
  have hV : ∀ a : Fin 4, V a x = slots a := fun a =>
    (ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x (slots a)).choose_spec
  let perms : Bool → Equiv.Perm (Fin 4) :=
    fun k => if k then Equiv.swap (2 : Fin 4) (3 : Fin 4) else 1
  let c : Bool → ℝ := fun _ => 1
  have hhid : ∀ p : M, ∀ s : Fin 4 → TangentSpace I p,
      (∑ k : Bool, c k * (S.base.rm04 t p) (fun a : Fin 4 => s (perms k a))) = 0 := by
    intro p s
    have hA : (S.base.rm04 t p) = metricRm04At (I := I) (M := M) (S.base.metric t) p := by
      rfl
    have hform := (mem_algebraicCurvatureTensorSubmodule_iff_symmetries (I := I) (M := M)).1
      (metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) (S.base.metric t) p)
    have h1 := hform.2.1 (s 0) (s 1) (s 2) (s 3)
    rw [Fintype.sum_bool]
    change (1 : ℝ) * (S.base.rm04 t p)
          (fun a : Fin 4 => s (Equiv.swap (2 : Fin 4) (3 : Fin 4) a)) +
      (1 : ℝ) * (S.base.rm04 t p) (fun a : Fin 4 => s a) = 0
    simp only [one_mul]
    rw [vec4_comp_swap23 s, vec4_self s, hA]
    change tensor04StdAt (I := I) (M := M) (metricRm04At (I := I) (M := M) (S.base.metric t) p)
        (s 0) (s 1) (s 3) (s 2) +
      tensor04StdAt (I := I) (M := M) (metricRm04At (I := I) (M := M) (S.base.metric t) p)
        (s 0) (s 1) (s 2) (s 3) = 0
    rw [h1]
    ring
  have hmain := TotalNabla0SRealizes.deriv_linear_combination
    (I := I) (s := 4) (cov := S.family.connection t)
    (α := S.base.rm04 t) (nablaAlpha := nablaKRm04Field (I := I) S t 1)
    (h := nablaKRm04Field_realizes (I := I) S t 0)
    (perms := perms) (c := c)
    (hid := hhid) X V x
  have hsum' : (nablaKRm04Field (I := I) S t 1 x)
        (Fin.cons u (fun a : Fin 4 => V (Equiv.swap (2 : Fin 4) (3 : Fin 4) a) x)) +
      (nablaKRm04Field (I := I) S t 1 x) (Fin.cons u (fun a : Fin 4 => V a x)) = 0 := by
    rw [Fintype.sum_bool] at hmain
    rw [hX] at hmain
    change (1 : ℝ) * (nablaKRm04Field (I := I) S t 1 x)
        (Fin.cons u (fun a : Fin 4 => V (Equiv.swap (2 : Fin 4) (3 : Fin 4) a) x)) +
      (1 : ℝ) * (nablaKRm04Field (I := I) S t 1 x) (Fin.cons u (fun a : Fin 4 => V a x)) = 0 at hmain
    simpa using hmain
  have hVat : (fun a : Fin 4 => V a x) = slots := by
    funext a
    exact hV a
  have hswapV : (fun a : Fin 4 => V (Equiv.swap (2 : Fin 4) (3 : Fin 4) a) x) =
      slots ∘ Equiv.swap (2 : Fin 4) (3 : Fin 4) := by
    funext a
    exact hV (Equiv.swap (2 : Fin 4) (3 : Fin 4) a)
  calc
    (nablaKRm04Field (I := I) S t 1 x)
        (Fin.cons u (slots ∘ Equiv.swap (2 : Fin 4) (3 : Fin 4))) +
      (nablaKRm04Field (I := I) S t 1 x) (Fin.cons u slots)
        = (nablaKRm04Field (I := I) S t 1 x)
            (Fin.cons u (fun a : Fin 4 => V (Equiv.swap (2 : Fin 4) (3 : Fin 4) a) x)) +
          (nablaKRm04Field (I := I) S t 1 x) (Fin.cons u (fun a : Fin 4 => V a x)) := by
          rw [← hswapV, ← hVat]
    _ = 0 := hsum'

omit [CompleteSpace E] [FiniteDimensional Real E] [IsManifold I ∞ M] [IsManifold I 1 M]
  [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
private theorem vec4_self_refl {x : M} (s : Fin 4 → TangentSpace I x) :
    (fun a : Fin 4 => s ((Equiv.refl (Fin 4)) a)) = vec4 (s 0) (s 1) (s 2) (s 3) := by
  funext a
  cases a using Fin.cases with
  | zero => simp [vec4]
  | succ a0 =>
      cases a0 using Fin.cases with
      | zero => simp [vec4]
      | succ a1 =>
          cases a1 using Fin.cases with
          | zero => simp [vec4]
          | succ a2 =>
              cases a2 using Fin.cases with
              | zero => simp [vec4]
              | succ a3 => exact Fin.elim0 a3

omit [SigmaCompactSpace M] in
private theorem rm04BianchiCond'
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (p : M)
    (s : Fin 4 → TangentSpace I p) :
    tensor04StdAt (I := I) (M := M) (S.base.rm04 t p) (s 0) (s 1) (s 2) (s 3) +
      tensor04StdAt (I := I) (M := M) (S.base.rm04 t p) (s 1) (s 2) (s 0) (s 3) +
        tensor04StdAt (I := I) (M := M) (S.base.rm04 t p) (s 2) (s 0) (s 1) (s 3) = 0 := by
  have hmem : (S.base.rm04 t p) ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) p :=
    metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) (S.base.metric t) p
  have hform := (mem_algebraicCurvatureTensorSubmodule_iff_symmetries (I := I) (M := M)).1 hmem
  exact hform.2.2 (s 0) (s 1) (s 2) (s 3)

omit [SigmaCompactSpace M] in
private theorem rm04BianchiCond
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (p : M)
    (s : Fin 4 → TangentSpace I p) :
    (S.base.rm04 t p) (fun a : Fin 4 => s ((Equiv.refl (Fin 4)) a)) +
      (S.base.rm04 t p) (fun a : Fin 4 => s (finCycle012 a)) +
        (S.base.rm04 t p) (fun a : Fin 4 => s ((finCycle012.trans finCycle012) a)) = 0 := by
  rw [vec4_self_refl s]
  rw [vec4_comp_cycle012 s, vec4_comp_cycle012_sq s]
  have h1 := rm04BianchiCond' S t p s
  rw [show tensor04StdAt (I := I) (M := M) (S.base.rm04 t p) (s 0) (s 1) (s 2) (s 3) =
      (S.base.rm04 t p) (vec4 (I := I) (s 0) (s 1) (s 2) (s 3)) by rfl,
    show tensor04StdAt (I := I) (M := M) (S.base.rm04 t p) (s 1) (s 2) (s 0) (s 3) =
      (S.base.rm04 t p) (vec4 (I := I) (s 1) (s 2) (s 0) (s 3)) by rfl,
    show tensor04StdAt (I := I) (M := M) (S.base.rm04 t p) (s 2) (s 0) (s 1) (s 3) =
      (S.base.rm04 t p) (vec4 (I := I) (s 2) (s 0) (s 1) (s 3)) by rfl] at h1
  nlinarith

omit [SigmaCompactSpace M] in
theorem nablaKRm04Field_one_bianchi123_cond
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M)
    (u : TangentSpace I x) (slots : Fin 4 → TangentSpace I x) :
    (nablaKRm04Field (I := I) S t 1 x)
        (Fin.cons u (slots ∘ finCycle012)) +
      (nablaKRm04Field (I := I) S t 1 x)
        (Fin.cons u (slots ∘ (finCycle012.trans finCycle012))) +
        (nablaKRm04Field (I := I) S t 1 x) (Fin.cons u slots) = 0 := by
  classical
  let X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    (ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x u).choose
  have hX : X x = u :=
    (ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x u).choose_spec
  let V : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    fun a => (ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x (slots a)).choose
  have hV : ∀ a : Fin 4, V a x = slots a := fun a =>
    (ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x (slots a)).choose_spec
  let perms : Fin 3 → Equiv.Perm (Fin 4) :=
    fun k => if k.val = 0 then Equiv.refl (Fin 4) else if k.val = 1 then finCycle012 else finCycle012.trans finCycle012
  let c : Fin 3 → ℝ := fun _ => 1
  have hhid : ∀ p : M, ∀ s : Fin 4 → TangentSpace I p,
      (∑ k : Fin 3, c k * (S.base.rm04 t p) (fun a : Fin 4 => s (perms k a))) = 0 := by
    intro p s
    rw [Fin.sum_univ_three]
    change (1 : ℝ) * (S.base.rm04 t p) (fun a : Fin 4 => s ((Equiv.refl (Fin 4)) a)) +
      (1 : ℝ) * (S.base.rm04 t p) (fun a : Fin 4 => s (finCycle012 a)) +
        (1 : ℝ) * (S.base.rm04 t p) (fun a : Fin 4 => s ((finCycle012.trans finCycle012) a)) = 0
    simp only [one_mul]
    exact rm04BianchiCond S t p s
  have hmain := TotalNabla0SRealizes.deriv_linear_combination
    (I := I) (s := 4) (cov := S.family.connection t)
    (α := S.base.rm04 t) (nablaAlpha := nablaKRm04Field (I := I) S t 1)
    (h := nablaKRm04Field_realizes (I := I) S t 0)
    (perms := perms) (c := c)
    (hid := hhid) X V x
  have hsum' : (nablaKRm04Field (I := I) S t 1 x)
        (Fin.cons u (fun a : Fin 4 => V (finCycle012 a) x)) +
      (nablaKRm04Field (I := I) S t 1 x)
        (Fin.cons u (fun a : Fin 4 => V ((finCycle012.trans finCycle012) a) x)) +
        (nablaKRm04Field (I := I) S t 1 x) (Fin.cons u (fun a : Fin 4 => V a x)) = 0 := by
    rw [Fin.sum_univ_three] at hmain
    rw [hX] at hmain
    change (1 : ℝ) * (nablaKRm04Field (I := I) S t 1 x) (Fin.cons u (fun a : Fin 4 => V a x)) +
      (1 : ℝ) * (nablaKRm04Field (I := I) S t 1 x)
          (Fin.cons u (fun a : Fin 4 => V (finCycle012 a) x)) +
        (1 : ℝ) * (nablaKRm04Field (I := I) S t 1 x)
          (Fin.cons u (fun a : Fin 4 => V ((finCycle012.trans finCycle012) a) x)) = 0 at hmain
    have hsum0 : (nablaKRm04Field (I := I) S t 1 x) (Fin.cons u (fun a : Fin 4 => V a x)) +
        (nablaKRm04Field (I := I) S t 1 x)
          (Fin.cons u (fun a : Fin 4 => V (finCycle012 a) x)) +
        (nablaKRm04Field (I := I) S t 1 x)
          (Fin.cons u (fun a : Fin 4 => V ((finCycle012.trans finCycle012) a) x)) = 0 := by
      simpa using hmain
    nlinarith
  have hVat : (fun a : Fin 4 => V a x) = slots := by
    funext a
    exact hV a
  have hcycV : (fun a : Fin 4 => V (finCycle012 a) x) = slots ∘ finCycle012 := by
    funext a
    exact hV (finCycle012 a)
  have hcyc2V : (fun a : Fin 4 => V ((finCycle012.trans finCycle012) a) x) =
      slots ∘ (finCycle012.trans finCycle012) := by
    funext a
    exact hV ((finCycle012.trans finCycle012) a)
  calc
    (nablaKRm04Field (I := I) S t 1 x) (Fin.cons u (slots ∘ finCycle012)) +
      (nablaKRm04Field (I := I) S t 1 x)
        (Fin.cons u (slots ∘ (finCycle012.trans finCycle012))) +
      (nablaKRm04Field (I := I) S t 1 x) (Fin.cons u slots)
        = (nablaKRm04Field (I := I) S t 1 x)
            (Fin.cons u (fun a : Fin 4 => V (finCycle012 a) x)) +
          (nablaKRm04Field (I := I) S t 1 x)
            (Fin.cons u (fun a : Fin 4 => V ((finCycle012.trans finCycle012) a) x)) +
          (nablaKRm04Field (I := I) S t 1 x) (Fin.cons u (fun a : Fin 4 => V a x)) := by
          rw [← hcycV, ← hcyc2V, ← hVat]
    _ = 0 := hsum'

omit [SigmaCompactSpace M] in
theorem nablaKRm04Field_two_anti23_cond
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M)
    (u v : TangentSpace I x) (slots : Fin 4 → TangentSpace I x) :
    (nablaKRm04Field (I := I) S t 2 x)
        (Fin.cons u (Fin.cons v (slots ∘ Equiv.swap (0 : Fin 4) (1 : Fin 4)))) +
      (nablaKRm04Field (I := I) S t 2 x) (Fin.cons u (Fin.cons v slots)) = 0 := by
  classical
  let X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    (ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x u).choose
  have hX : X x = u :=
    (ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x u).choose_spec
  let V5 : Fin 5 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    fun a => (ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x (Fin.cases v (fun i : Fin 4 => slots i) a)).choose
  have hV5 : ∀ a : Fin 5, V5 a x = Fin.cases v (fun i : Fin 4 => slots i) a := fun a =>
    (ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x (Fin.cases v (fun i : Fin 4 => slots i) a)).choose_spec
  let perms : Bool → Equiv.Perm (Fin 5) :=
    fun k => if k then succPerm (Equiv.swap (0 : Fin 4) (1 : Fin 4)) else 1
  let c : Bool → ℝ := fun _ => 1
  have hhid : ∀ p : M, ∀ s5 : Fin 5 → TangentSpace I p,
      (∑ k : Bool, c k * (nablaKRm04Field (I := I) S t 1 p)
          (fun a : Fin 5 => s5 (perms k a))) = 0 := by
    intro p s5
    have h1 := nablaKRm04Field_one_anti12_cond (I := I) S t p (s5 0) (fun i : Fin 4 => s5 (i.succ))
    rw [Fintype.sum_bool]
    change (1 : ℝ) * (nablaKRm04Field (I := I) S t 1 p)
          (fun a : Fin 5 => s5 (succPerm (Equiv.swap (0 : Fin 4) (1 : Fin 4)) a)) +
      (1 : ℝ) * (nablaKRm04Field (I := I) S t 1 p) (fun a : Fin 5 => s5 a) = 0
    simp only [one_mul]
    calc
      (nablaKRm04Field (I := I) S t 1 p)
          (fun a : Fin 5 => s5 (succPerm (Equiv.swap (0 : Fin 4) (1 : Fin 4)) a)) +
        (nablaKRm04Field (I := I) S t 1 p) (fun a : Fin 5 => s5 a)
          = (nablaKRm04Field (I := I) S t 1 p)
              (Fin.cons (s5 0) ((fun i : Fin 4 => s5 (i.succ)) ∘ Equiv.swap (0 : Fin 4) (1 : Fin 4))) +
            (nablaKRm04Field (I := I) S t 1 p) (Fin.cons (s5 0) (fun i : Fin 4 => s5 (i.succ))) := by
            congr 1
            · congr 1
              rw [← fin_cons_comp_succPerm (s5 0) (fun i : Fin 4 => s5 (i.succ))
                (Equiv.swap (0 : Fin 4) (1 : Fin 4))]
              rw [fin_cons_tail (fun i : Fin 5 => s5 i)]
              rfl
            · congr 1
              rw [fin_cons_tail (fun i : Fin 5 => s5 i)]
    _ = 0 := h1
  have hmain := TotalNabla0SRealizes.deriv_linear_combination
    (I := I) (s := 5) (cov := S.family.connection t)
    (α := nablaKRm04Field (I := I) S t 1) (nablaAlpha := nablaKRm04Field (I := I) S t 2)
    (h := nablaKRm04Field_realizes (I := I) S t 1)
    (perms := perms) (c := c)
    (hid := hhid) X V5 x
  have hsum0 : (nablaKRm04Field (I := I) S t 2 x)
        (Fin.cons u (fun a : Fin 5 => V5 (succPerm (Equiv.swap (0 : Fin 4) (1 : Fin 4)) a) x)) +
      (nablaKRm04Field (I := I) S t 2 x) (Fin.cons u (fun a : Fin 5 => V5 a x)) = 0 := by
    rw [Fintype.sum_bool] at hmain
    rw [hX] at hmain
    change (1 : ℝ) * (nablaKRm04Field (I := I) S t 2 x)
        (Fin.cons u (fun a : Fin 5 => V5 (succPerm (Equiv.swap (0 : Fin 4) (1 : Fin 4)) a) x)) +
      (1 : ℝ) * (nablaKRm04Field (I := I) S t 2 x) (Fin.cons u (fun a : Fin 5 => V5 a x)) = 0 at hmain
    simpa using hmain
  have hVat5 : (fun a : Fin 5 => V5 a x) = Fin.cons v (fun i : Fin 4 => slots i) := by
    funext a
    exact hV5 a
  have hswap5 : (fun a : Fin 5 => V5 (succPerm (Equiv.swap (0 : Fin 4) (1 : Fin 4)) a) x) =
      Fin.cons v (fun i : Fin 4 => slots (Equiv.swap (0 : Fin 4) (1 : Fin 4) i)) := by
    funext a
    rw [hV5]
    cases a using Fin.cases with
    | zero => simp [succPerm]
    | succ i' => simp [succPerm]
  calc
    (nablaKRm04Field (I := I) S t 2 x)
        (Fin.cons u (Fin.cons v (slots ∘ Equiv.swap (0 : Fin 4) (1 : Fin 4)))) +
      (nablaKRm04Field (I := I) S t 2 x) (Fin.cons u (Fin.cons v slots))
        = (nablaKRm04Field (I := I) S t 2 x)
            (Fin.cons u (fun a : Fin 5 => V5 (succPerm (Equiv.swap (0 : Fin 4) (1 : Fin 4)) a) x)) +
          (nablaKRm04Field (I := I) S t 2 x) (Fin.cons u (fun a : Fin 5 => V5 a x)) := by
          congr 1
          · congr 1
            rw [hswap5]
            rfl
          · congr 1
            rw [hVat5]
    _ = 0 := hsum0

omit [SigmaCompactSpace M] in
theorem nablaKRm04Field_two_anti45_cond
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M)
    (u v : TangentSpace I x) (slots : Fin 4 → TangentSpace I x) :
    (nablaKRm04Field (I := I) S t 2 x)
        (Fin.cons u (Fin.cons v (slots ∘ Equiv.swap (2 : Fin 4) (3 : Fin 4)))) +
      (nablaKRm04Field (I := I) S t 2 x) (Fin.cons u (Fin.cons v slots)) = 0 := by
  classical
  let X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    (ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x u).choose
  have hX : X x = u :=
    (ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x u).choose_spec
  let V5 : Fin 5 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    fun a => (ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x (Fin.cases v (fun i : Fin 4 => slots i) a)).choose
  have hV5 : ∀ a : Fin 5, V5 a x = Fin.cases v (fun i : Fin 4 => slots i) a := fun a =>
    (ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x (Fin.cases v (fun i : Fin 4 => slots i) a)).choose_spec
  let perms : Bool → Equiv.Perm (Fin 5) :=
    fun k => if k then succPerm (Equiv.swap (2 : Fin 4) (3 : Fin 4)) else 1
  let c : Bool → ℝ := fun _ => 1
  have hhid : ∀ p : M, ∀ s5 : Fin 5 → TangentSpace I p,
      (∑ k : Bool, c k * (nablaKRm04Field (I := I) S t 1 p)
          (fun a : Fin 5 => s5 (perms k a))) = 0 := by
    intro p s5
    have h1 := nablaKRm04Field_one_anti34_cond (I := I) S t p (s5 0) (fun i : Fin 4 => s5 (i.succ))
    rw [Fintype.sum_bool]
    change (1 : ℝ) * (nablaKRm04Field (I := I) S t 1 p)
          (fun a : Fin 5 => s5 (succPerm (Equiv.swap (2 : Fin 4) (3 : Fin 4)) a)) +
      (1 : ℝ) * (nablaKRm04Field (I := I) S t 1 p) (fun a : Fin 5 => s5 a) = 0
    simp only [one_mul]
    calc
      (nablaKRm04Field (I := I) S t 1 p)
          (fun a : Fin 5 => s5 (succPerm (Equiv.swap (2 : Fin 4) (3 : Fin 4)) a)) +
        (nablaKRm04Field (I := I) S t 1 p) (fun a : Fin 5 => s5 a)
          = (nablaKRm04Field (I := I) S t 1 p)
              (Fin.cons (s5 0) ((fun i : Fin 4 => s5 (i.succ)) ∘ Equiv.swap (2 : Fin 4) (3 : Fin 4))) +
            (nablaKRm04Field (I := I) S t 1 p) (Fin.cons (s5 0) (fun i : Fin 4 => s5 (i.succ))) := by
            congr 1
            · congr 1
              rw [← fin_cons_comp_succPerm (s5 0) (fun i : Fin 4 => s5 (i.succ))
                (Equiv.swap (2 : Fin 4) (3 : Fin 4))]
              rw [fin_cons_tail (fun i : Fin 5 => s5 i)]
              rfl
            · congr 1
              rw [fin_cons_tail (fun i : Fin 5 => s5 i)]
    _ = 0 := h1
  have hmain := TotalNabla0SRealizes.deriv_linear_combination
    (I := I) (s := 5) (cov := S.family.connection t)
    (α := nablaKRm04Field (I := I) S t 1) (nablaAlpha := nablaKRm04Field (I := I) S t 2)
    (h := nablaKRm04Field_realizes (I := I) S t 1)
    (perms := perms) (c := c)
    (hid := hhid) X V5 x
  have hsum0 : (nablaKRm04Field (I := I) S t 2 x)
        (Fin.cons u (fun a : Fin 5 => V5 (succPerm (Equiv.swap (2 : Fin 4) (3 : Fin 4)) a) x)) +
      (nablaKRm04Field (I := I) S t 2 x) (Fin.cons u (fun a : Fin 5 => V5 a x)) = 0 := by
    rw [Fintype.sum_bool] at hmain
    rw [hX] at hmain
    change (1 : ℝ) * (nablaKRm04Field (I := I) S t 2 x)
        (Fin.cons u (fun a : Fin 5 => V5 (succPerm (Equiv.swap (2 : Fin 4) (3 : Fin 4)) a) x)) +
      (1 : ℝ) * (nablaKRm04Field (I := I) S t 2 x) (Fin.cons u (fun a : Fin 5 => V5 a x)) = 0 at hmain
    simpa using hmain
  have hVat5 : (fun a : Fin 5 => V5 a x) = Fin.cons v (fun i : Fin 4 => slots i) := by
    funext a
    exact hV5 a
  have hswap5 : (fun a : Fin 5 => V5 (succPerm (Equiv.swap (2 : Fin 4) (3 : Fin 4)) a) x) =
      Fin.cons v (fun i : Fin 4 => slots (Equiv.swap (2 : Fin 4) (3 : Fin 4) i)) := by
    funext a
    rw [hV5]
    cases a using Fin.cases with
    | zero => simp [succPerm]
    | succ i' => simp [succPerm]
  calc
    (nablaKRm04Field (I := I) S t 2 x)
        (Fin.cons u (Fin.cons v (slots ∘ Equiv.swap (2 : Fin 4) (3 : Fin 4)))) +
      (nablaKRm04Field (I := I) S t 2 x) (Fin.cons u (Fin.cons v slots))
        = (nablaKRm04Field (I := I) S t 2 x)
            (Fin.cons u (fun a : Fin 5 => V5 (succPerm (Equiv.swap (2 : Fin 4) (3 : Fin 4)) a) x)) +
          (nablaKRm04Field (I := I) S t 2 x) (Fin.cons u (fun a : Fin 5 => V5 a x)) := by
          congr 1
          · congr 1
            rw [hswap5]
            rfl
          · congr 1
            rw [hVat5]
    _ = 0 := hsum0

end RoughLapAlgebraic

open Bundle Set Filter
open DifferentialGeometry.Analysis.Convex
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology RealInnerProductSpace BigOperators
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Dim3Reaction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
variable [SigmaCompactSpace M] [T2Space M]
variable {T : ℝ} (hT : 0 < T) [I.Boundaryless]
variable (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
variable (hS : IsSolutionOn (I := I) S)
variable (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
variable (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
variable (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt x))
variable (iota : MatrixComp M (Fin 3))
variable (hiota0 : ∀ x : M, ∀ a k : Fin 3, iota 0 x a k = if a = k then 1 else 0)
variable (hgram : ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Fin 3,
  movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota t x a b =
  movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota 0 x a b)


section Helpers

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem fiberRegion_metricInverseInBasis_identity_of_orthonormal
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : DifferentialGeometry.SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : ∀ i j : Idx, g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0) :
    MetricInverseInBasis_gen (I := I) g x basis (identityInvMetric (Idx := Idx)) := by
  classical
  intro i j
  refine ⟨?_, ?_⟩
  · rw [Finset.sum_eq_single i]
    · rw [identityInvMetric_apply_self, one_mul]
      exact horth i j
    · intro k _ hk
      rw [identityInvMetric, diagonalInvMetric_eq_zero_of_ne (fun h => hk h.symm), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  · rw [Finset.sum_eq_single j]
    · rw [identityInvMetric_apply_self, mul_one]
      exact horth i j
    · intro k _ hk
      rw [identityInvMetric, diagonalInvMetric_eq_zero_of_ne hk, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h

omit [CompleteSpace E] [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M]
  [T2Space M] [I.Boundaryless] in
theorem fiberRegion_metricTraceFirstTwo0SAt_eq_metricTrace0S2InBasis
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : DifferentialGeometry.SmoothRiemannianMetric I M) {x : M} {s : ℕ}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx → Idx → ℝ)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 2) x)
    (tail : Fin s → TangentSpace I x) :
    metricTraceFirstTwo0SAt (I := I) g T tail =
      metricTrace0S2InBasis (I := I) basis gInv T tail := by
  unfold metricTraceFirstTwo0SAt
  rw [metricTracePair0SAt_eq_sum_basis (I := I) g basis gInv hinv (freezeFirstTwo0S (I := I) T tail)]
  unfold metricTrace0S2InBasis
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [freezeFirstTwo0S_apply]

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem fiberInner_compUhlenbeck_isometry_general
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (iota : MatrixComp M (Fin 3))
    (hiota0 : ∀ x : M, ∀ a k : Fin 3, iota 0 x a k = if a = k then 1 else 0)
    (hgram : ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Fin 3,
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota t x a b =
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota 0 x a b)
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt x))
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) (x : M)
    (X Y : Tensor04At (I := I) (M := M) x) :
    inner0S (I := I) (S.base.metric 0) x 4
        (X.compContinuousLinearMap (fun _ : Fin 4 => uhlenbeckEndomorphismAt (basisAt x) iota t))
        (Y.compContinuousLinearMap (fun _ : Fin 4 => uhlenbeckEndomorphismAt (basisAt x) iota t)) =
      inner0S (I := I) (S.base.metric t) x 4 X Y := by
  classical
  let moving : Module.Basis (Fin 3) Real (TangentSpace I x) :=
    uhlenbeckMovingBasis hT S basisAt iota hiota0 hgram t ht x
  have hmovingOrth : ∀ i j : Fin 3,
      (S.base.metric t).inner x (moving i) (moving j) = delta3 i j := by
    intro i j
    dsimp [moving]
    exact uhlenbeckMovingBasis_orthonormalBasisAt (I := I) (M := M) hT S basisAt iota hiota0 hgram x
      (horth0 x) ht i j
  have hinv0 : MetricInverseInBasis (I := I) (S.base.metric 0) x (basisAt x)
      (identityInvMetric (Idx := Fin 3)) := by
    have h := fiberRegion_metricInverseInBasis_identity_of_orthonormal (I := I)
      (S.base.metric 0) (basisAt x) (by
        intro i j
        simpa [delta3] using horth0 x i j)
    exact h
  have hinvT : MetricInverseInBasis (I := I) (S.base.metric t) x moving
      (identityInvMetric (Idx := Fin 3)) := by
    have h := fiberRegion_metricInverseInBasis_identity_of_orthonormal (I := I)
      (S.base.metric t) moving hmovingOrth
    exact h
  have hU : ∀ a : Fin 3,
      uhlenbeckEndomorphismAt (basisAt x) iota t (basisAt x a) = moving a := by
    intro a
    exact (uhlenbeckMovingBasis_apply (I := I) (M := M) hT S basisAt iota hiota0 hgram t ht x a).symm
  let Xc : Tensor04At (I := I) (M := M) x :=
    X.compContinuousLinearMap (fun _ : Fin 4 => uhlenbeckEndomorphismAt (basisAt x) iota t)
  let Yc : Tensor04At (I := I) (M := M) x :=
    Y.compContinuousLinearMap (fun _ : Fin 4 => uhlenbeckEndomorphismAt (basisAt x) iota t)
  have hleft : inner0S (I := I) (S.base.metric 0) x 4 Xc Yc =
      coordInner0S (I := I) (x := x) 4 (identityInvMetric (Idx := Fin 3)) Xc Yc (basisAt x) := by
    exact inner0S_eq_coord (I := I) (S.base.metric 0) x 4 (basisAt x)
      (identityInvMetric (Idx := Fin 3)) hinv0 Xc Yc
  have hright : inner0S (I := I) (S.base.metric t) x 4 X Y =
      coordInner0S (I := I) (x := x) 4 (identityInvMetric (Idx := Fin 3)) X Y moving := by
    exact inner0S_eq_coord (I := I) (S.base.metric t) x 4 moving
      (identityInvMetric (Idx := Fin 3)) hinvT X Y
  have hXcomp : ∀ I0 : Fin 4 → Fin 3,
      tensor0SComponent (I := I) Xc (fun i : Fin 3 => basisAt x i) I0 =
        tensor0SComponent (I := I) X (fun i : Fin 3 => moving i) I0 := by
    intro I0
    change (X : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ)
        (fun a : Fin 4 => uhlenbeckEndomorphismAt (basisAt x) iota t (basisAt x (I0 a))) =
      (X : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ)
        (fun a : Fin 4 => moving (I0 a))
    have harg : (fun a : Fin 4 => uhlenbeckEndomorphismAt (basisAt x) iota t (basisAt x (I0 a))) =
        fun a : Fin 4 => moving (I0 a) := by
      funext a
      exact hU (I0 a)
    rw [harg]
  have hYcomp : ∀ J0 : Fin 4 → Fin 3,
      tensor0SComponent (I := I) Yc (fun i : Fin 3 => basisAt x i) J0 =
        tensor0SComponent (I := I) Y (fun i : Fin 3 => moving i) J0 := by
    intro J0
    change (Y : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ)
        (fun a : Fin 4 => uhlenbeckEndomorphismAt (basisAt x) iota t (basisAt x (J0 a))) =
      (Y : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ)
        (fun a : Fin 4 => moving (J0 a))
    have harg : (fun a : Fin 4 => uhlenbeckEndomorphismAt (basisAt x) iota t (basisAt x (J0 a))) =
        fun a : Fin 4 => moving (J0 a) := by
      funext a
      exact hU (J0 a)
    rw [harg]
  calc
    inner0S (I := I) (S.base.metric 0) x 4 Xc Yc
        = coordInner0S (I := I) (x := x) 4 (identityInvMetric (Idx := Fin 3)) Xc Yc (basisAt x) := hleft
    _ = coordInner0S (I := I) (x := x) 4 (identityInvMetric (Idx := Fin 3)) X Y moving := by
          unfold coordInner0S
          apply Finset.sum_congr rfl
          intro I0 _
          apply Finset.sum_congr rfl
          intro J0 _
          rw [hXcomp I0, hYcomp J0]
    _ = inner0S (I := I) (S.base.metric t) x 4 X Y := hright.symm

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [IsManifold I 2 M]
  [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
lemma fiberRegion_tensor_sum_antiPair
    {n : ℕ} {x : M}
    (β : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) n x)
    (s d : Fin n → TangentSpace I x)
    (σ : Fin n → Fin n)
    (hσinv : ∀ a : Fin n, σ (σ a) = a)
    (hβ : ∀ u : Fin n → TangentSpace I x, β u + β (u ∘ σ) = 0) :
    (∑ a : Fin n, β (Function.update s a (d a))) +
        (∑ a : Fin n, β (Function.update (s ∘ σ) a (d (σ a)))) = 0 := by
  classical
  have hupdate : ∀ a : Fin n,
      Function.update (s ∘ σ) (σ a) (d a) = (Function.update s a (d a)) ∘ σ := by
    intro a
    funext b
    by_cases h : b = σ a
    · have hb : σ b = a := by
        rw [h]
        exact hσinv a
      simp [Function.update, h, hσinv a]
    · have hb : σ b ≠ a := by
        intro hb
        apply h
        have hσb : σ (σ b) = σ a := congrArg σ hb
        rwa [hσinv b] at hσb
      simp [Function.update, h, hb]
  have hreindex : (∑ a : Fin n, β (Function.update (s ∘ σ) a (d (σ a)))) =
      ∑ a : Fin n, β (Function.update (s ∘ σ) (σ a) (d a)) := by
    refine Finset.sum_bij (fun a _ => σ a) ?_ ?_ ?_ ?_
    · intro a ha
      simp
    · intro a₁ ha₁ a₂ ha₂ h
      have h' := congrArg σ h
      rwa [hσinv a₁, hσinv a₂] at h'
    · intro b hb
      refine ⟨σ b, by simp, ?_⟩
      exact hσinv b
    · intro a ha
      rw [hσinv a]
  calc
    (∑ a : Fin n, β (Function.update s a (d a))) +
        (∑ a : Fin n, β (Function.update (s ∘ σ) a (d (σ a))))
        = (∑ a : Fin n, β (Function.update s a (d a))) +
            (∑ a : Fin n, β (Function.update (s ∘ σ) (σ a) (d a))) := by
          rw [hreindex]
    _ = (∑ a : Fin n, (β (Function.update s a (d a)) +
          β (Function.update (s ∘ σ) (σ a) (d a)))) := by
          simp [Finset.sum_add_distrib]
    _ = 0 := by
          simp [hupdate, hβ]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [IsManifold I 2 M]
  [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
lemma fiberRegion_tensor_sum_cyclePair
    {n : ℕ} {x : M}
    (β : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) n x)
    (s d : Fin n → TangentSpace I x)
    (τ : Fin n → Fin n)
    (hτ3id : ∀ a : Fin n, τ (τ (τ a)) = a)
    (hβ : ∀ u : Fin n → TangentSpace I x, β u + β (u ∘ τ) + β (u ∘ τ ∘ τ) = 0) :
    (∑ a : Fin n, β (Function.update s a (d a))) +
        (∑ a : Fin n, β (Function.update (s ∘ τ) a (d (τ a)))) +
        (∑ a : Fin n, β (Function.update (s ∘ τ ∘ τ) a (d (τ (τ a))))) = 0 := by
  classical
  have hupdate1 : ∀ a : Fin n,
      Function.update (s ∘ τ) (τ (τ a)) (d a) = (Function.update s a (d a)) ∘ τ := by
    intro a
    funext b
    by_cases h : b = τ (τ a)
    · have hb : τ b = a := by
        rw [h]
        exact hτ3id a
      simp [Function.update, h, hτ3id a]
    · have hb : τ b ≠ a := by
        intro hb
        apply h
        have hτb : τ (τ (τ b)) = τ (τ a) := congrArg τ (congrArg τ hb)
        rwa [hτ3id b] at hτb
      simp [Function.update, h, hb]
  have hupdate2 : ∀ a : Fin n,
      Function.update (s ∘ τ ∘ τ) (τ a) (d a) = (Function.update s a (d a)) ∘ τ ∘ τ := by
    intro a
    funext b
    by_cases h : b = τ a
    · have hb : τ (τ b) = a := by
        rw [h]
        exact hτ3id a
      simp [Function.update, h, hτ3id a]
    · have hb : τ (τ b) ≠ a := by
        intro hb
        apply h
        have hτb : τ (τ (τ b)) = τ a := congrArg τ hb
        rwa [hτ3id b] at hτb
      simp [Function.update, h, hb]
  have hreindex1 : (∑ a : Fin n, β (Function.update (s ∘ τ) a (d (τ a)))) =
      ∑ a : Fin n, β (Function.update (s ∘ τ) (τ (τ a)) (d a)) := by
    refine Finset.sum_bij (fun a _ => τ a) ?_ ?_ ?_ ?_
    · intro a ha
      simp
    · intro a₁ ha₁ a₂ ha₂ h
      have h' := congrArg τ (congrArg τ h)
      rwa [hτ3id a₁, hτ3id a₂] at h'
    · intro b hb
      refine ⟨τ (τ b), by simp, ?_⟩
      exact hτ3id b
    · intro a ha
      rw [hτ3id a]
  have hreindex2 : (∑ a : Fin n, β (Function.update (s ∘ τ ∘ τ) a (d (τ (τ a))))) =
      ∑ a : Fin n, β (Function.update (s ∘ τ ∘ τ) (τ a) (d a)) := by
    refine Finset.sum_bij (fun a _ => τ (τ a)) ?_ ?_ ?_ ?_
    · intro a ha
      simp
    · intro a₁ ha₁ a₂ ha₂ h
      have h' := congrArg τ h
      rwa [hτ3id a₁, hτ3id a₂] at h'
    · intro b hb
      refine ⟨τ b, by simp, ?_⟩
      exact hτ3id b
    · intro a ha
      rw [hτ3id a]
  calc
    (∑ a : Fin n, β (Function.update s a (d a))) +
        (∑ a : Fin n, β (Function.update (s ∘ τ) a (d (τ a)))) +
        (∑ a : Fin n, β (Function.update (s ∘ τ ∘ τ) a (d (τ (τ a)))))
        = (∑ a : Fin n, β (Function.update s a (d a))) +
            (∑ a : Fin n, β (Function.update (s ∘ τ) (τ (τ a)) (d a))) +
            (∑ a : Fin n, β (Function.update (s ∘ τ ∘ τ) (τ a) (d a))) := by
          rw [hreindex1, hreindex2]
    _ = (∑ a : Fin n, (β (Function.update s a (d a)) +
          β (Function.update (s ∘ τ) (τ (τ a)) (d a)) +
          β (Function.update (s ∘ τ ∘ τ) (τ a) (d a)))) := by
          simp [Finset.sum_add_distrib]
    _ = 0 := by
          simp [hupdate1, hupdate2, hβ]

omit [CompleteSpace E] [IsManifold I 3 M] [SigmaCompactSpace M] [I.Boundaryless] in
lemma fiberRegion_nabla_of_algCurvForm
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 4)
    (nablaα : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 5)
    (hA : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 cov α nablaα)
    (hAlg : ∀ y : M, IsAlgCurvForm
      (fun X Y Z W : TangentSpace I y => tensor04StdAt (I := I) (M := M) (α y) X Y Z W))
    (x : M) :
    ∀ u X Y Z W : TangentSpace I x,
      nablaα x (Fin.cons u (vec4 X Y Z W)) = -nablaα x (Fin.cons u (vec4 Y X Z W)) ∧
      nablaα x (Fin.cons u (vec4 X Y Z W)) = -nablaα x (Fin.cons u (vec4 X Y W Z)) ∧
      nablaα x (Fin.cons u (vec4 X Y Z W)) + nablaα x (Fin.cons u (vec4 Y Z X W)) +
        nablaα x (Fin.cons u (vec4 Z X Y W)) = 0 := by
  classical
  intro u X Y Z W
  let U : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    (ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x u).choose
  have hU : U x = u :=
    (ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x u).choose_spec
  let V : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    fun a => (ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x
      (vec4 X Y Z W a)).choose
  have hV : ∀ a : Fin 4, V a x = vec4 X Y Z W a := fun a =>
    (ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x
      (vec4 X Y Z W a)).choose_spec
  let s : Fin 4 → TangentSpace I x := fun b => V b x
  let d : Fin 4 → TangentSpace I x := fun a => (cov (fun p : M => V a p) x) (U x)
  let f : M → ℝ := fun p => α p (fun a : Fin 4 => V a p)
  have hslots : (fun a : Fin 4 => V a x) = vec4 X Y Z W := by
    funext a
    exact hV a
  have hderiv : nablaα x (Fin.cons u (vec4 X Y Z W)) =
      extDerivFun (I := I) f x (U x) - ∑ a : Fin 4, α x (Function.update s a (d a)) := by
    have h := TotalNabla0SRealizes.eval_smooth_slots (I := I) hA U V x
    simpa [hU, s, d, f, hslots] using h
  have hmdiff_f : MDifferentiableAt I 𝓘(Real, Real) f x :=
    ContMDiffAt.mdifferentiableAt
      (tensor0SField_eval_smooth_slots_contMDiffAt (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) α V x)
      (by simp)
  have hderiv_perm : ∀ (Wp : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
      (hW : (fun a : Fin 4 => Wp a x) = vec4 Y X Z W),
      nablaα x (Fin.cons u (vec4 Y X Z W)) =
        extDerivFun (I := I) (fun p : M => α p (fun a : Fin 4 => Wp a p)) x (U x) -
          ∑ a : Fin 4, α x (Function.update (fun b : Fin 4 => Wp b x) a
            ((cov (fun p : M => Wp a p) x) (U x))) := by
    intro Wp hW
    have h := TotalNabla0SRealizes.eval_smooth_slots (I := I) hA U Wp x
    simpa [hU, hW] using h
  have hanti1 : nablaα x (Fin.cons u (vec4 X Y Z W)) = -nablaα x (Fin.cons u (vec4 Y X Z W)) := by
    let σ01 : Fin 4 → Fin 4 := fun a => if a = 0 then 1 else if a = 1 then 0 else a
    let V01 : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
      fun a => V (σ01 a)
    have hV01 : (fun a : Fin 4 => V01 a x) = vec4 Y X Z W := by
      funext a
      fin_cases a <;> simp [V01, σ01, hV, vec4]
    have hderiv01 : nablaα x (Fin.cons u (vec4 Y X Z W)) =
        extDerivFun (I := I) (fun p : M => α p (fun a : Fin 4 => V01 a p)) x (U x) -
          ∑ a : Fin 4, α x (Function.update (fun b : Fin 4 => V01 b x) a
            ((cov (fun p : M => V01 a p) x) (U x))) := hderiv_perm V01 hV01
    have hfun01 : (fun p : M => α p (fun a : Fin 4 => V01 a p)) =
        fun p : M => -α p (fun a : Fin 4 => V a p) := by
      funext p
      have hrec1 : (fun a : Fin 4 => V01 a p) = vec4 (V 1 p) (V 0 p) (V 2 p) (V 3 p) := by
        funext a
        fin_cases a <;> simp [V01, σ01, vec4]
      have hrec2 : (fun a : Fin 4 => V a p) = vec4 (V 0 p) (V 1 p) (V 2 p) (V 3 p) := by
        funext a
        fin_cases a <;> simp [vec4]
      calc
        α p (fun a : Fin 4 => V01 a p)
            = tensor04StdAt (I := I) (M := M) (α p) (V 1 p) (V 0 p) (V 2 p) (V 3 p) := by
              rw [hrec1]
              rfl
        _ = -tensor04StdAt (I := I) (M := M) (α p) (V 0 p) (V 1 p) (V 2 p) (V 3 p) := by
              exact (hAlg p).anti_first (V 1 p) (V 0 p) (V 2 p) (V 3 p)
        _ = -α p (fun a : Fin 4 => V a p) := by
              rw [hrec2]
              rfl
    have hext01 : extDerivFun (I := I) (fun p : M => α p (fun a : Fin 4 => V01 a p)) x (U x) =
        -extDerivFun (I := I) f x (U x) := by
      have hneg : extDerivFun (I := I) (fun p : M => -α p (fun a : Fin 4 => V a p)) x (U x) =
          -extDerivFun (I := I) f x (U x) :=
        DifferentialGeometry.Tensor.RicciIdentity.extDerivFun_neg_at (I := I) (f := f) (x := x) (U x) hmdiff_f
      rw [← hfun01] at hneg
      simpa [f] using hneg
    have hβ : ∀ v : Fin 4 → TangentSpace I x, α x v + α x (v ∘ σ01) = 0 := by
      intro v
      have h1 : α x v = tensor04StdAt (I := I) (M := M) (α x) (v 0) (v 1) (v 2) (v 3) := by
        congr 1
        funext b
        fin_cases b <;> simp [vec4]
      have h2 : α x (v ∘ σ01) = tensor04StdAt (I := I) (M := M) (α x) (v 1) (v 0) (v 2) (v 3) := by
        congr 1
        funext b
        fin_cases b <;> simp [σ01, vec4]
      have hanti := (hAlg x).anti_first (v 0) (v 1) (v 2) (v 3)
      rw [h1, h2, hanti]
      ring
    have hsum01 : (∑ a : Fin 4, α x (Function.update s a (d a))) =
        -(∑ a : Fin 4, α x (Function.update (fun b : Fin 4 => V01 b x) a
          ((cov (fun p : M => V01 a p) x) (U x)))) := by
      have hpair := fiberRegion_tensor_sum_antiPair (α x) s d σ01
        (by intro a; fin_cases a <;> simp [σ01]) hβ
      have hsimpa : (∑ a : Fin 4, α x (Function.update (s ∘ σ01) a (d (σ01 a)))) =
          ∑ a : Fin 4, α x (Function.update (fun b : Fin 4 => V01 b x) a
            ((cov (fun p : M => V01 a p) x) (U x))) := by
        apply Finset.sum_congr rfl
        intro a _
        congr 1
      linarith [hpair, hsimpa]
    calc
      nablaα x (Fin.cons u (vec4 X Y Z W))
          = extDerivFun (I := I) f x (U x) - ∑ a : Fin 4, α x (Function.update s a (d a)) := hderiv
      _ = -nablaα x (Fin.cons u (vec4 Y X Z W)) := by
            rw [hderiv01]
            rw [hext01, hsum01]
            ring
  have hanti2 : nablaα x (Fin.cons u (vec4 X Y Z W)) = -nablaα x (Fin.cons u (vec4 X Y W Z)) := by
    let σ23 : Fin 4 → Fin 4 := fun a => if a = 2 then 3 else if a = 3 then 2 else a
    let V23 : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
      fun a => V (σ23 a)
    have hV23 : (fun a : Fin 4 => V23 a x) = vec4 X Y W Z := by
      funext a
      fin_cases a <;> simp [V23, σ23, hV, vec4]
    have hderiv23 : nablaα x (Fin.cons u (vec4 X Y W Z)) =
        extDerivFun (I := I) (fun p : M => α p (fun a : Fin 4 => V23 a p)) x (U x) -
          ∑ a : Fin 4, α x (Function.update (fun b : Fin 4 => V23 b x) a
            ((cov (fun p : M => V23 a p) x) (U x))) := by
      have h := TotalNabla0SRealizes.eval_smooth_slots (I := I) hA U V23 x
      simpa [hU, hV23] using h
    have hfun23 : (fun p : M => α p (fun a : Fin 4 => V23 a p)) =
        fun p : M => -α p (fun a : Fin 4 => V a p) := by
      funext p
      have hrec1 : (fun a : Fin 4 => V23 a p) = vec4 (V 0 p) (V 1 p) (V 3 p) (V 2 p) := by
        funext a
        fin_cases a <;> simp [V23, σ23, vec4]
      have hrec2 : (fun a : Fin 4 => V a p) = vec4 (V 0 p) (V 1 p) (V 2 p) (V 3 p) := by
        funext a
        fin_cases a <;> simp [vec4]
      calc
        α p (fun a : Fin 4 => V23 a p)
            = tensor04StdAt (I := I) (M := M) (α p) (V 0 p) (V 1 p) (V 3 p) (V 2 p) := by
              rw [hrec1]
              rfl
        _ = -tensor04StdAt (I := I) (M := M) (α p) (V 0 p) (V 1 p) (V 2 p) (V 3 p) := by
              exact (hAlg p).anti_last (V 0 p) (V 1 p) (V 3 p) (V 2 p)
        _ = -α p (fun a : Fin 4 => V a p) := by
              rw [hrec2]
              rfl
    have hext23 : extDerivFun (I := I) (fun p : M => α p (fun a : Fin 4 => V23 a p)) x (U x) =
        -extDerivFun (I := I) f x (U x) := by
      have hneg : extDerivFun (I := I) (fun p : M => -α p (fun a : Fin 4 => V a p)) x (U x) =
          -extDerivFun (I := I) f x (U x) :=
        DifferentialGeometry.Tensor.RicciIdentity.extDerivFun_neg_at (I := I) (f := f) (x := x) (U x) hmdiff_f
      rw [← hfun23] at hneg
      simpa [f] using hneg
    have hβ : ∀ v : Fin 4 → TangentSpace I x, α x v + α x (v ∘ σ23) = 0 := by
      intro v
      have h1 : α x v = tensor04StdAt (I := I) (M := M) (α x) (v 0) (v 1) (v 2) (v 3) := by
        congr 1
        funext b
        fin_cases b <;> simp [vec4]
      have h2 : α x (v ∘ σ23) = tensor04StdAt (I := I) (M := M) (α x) (v 0) (v 1) (v 3) (v 2) := by
        congr 1
        funext b
        fin_cases b <;> simp [σ23, vec4]
      have hanti := (hAlg x).anti_last (v 0) (v 1) (v 2) (v 3)
      rw [h1, h2, hanti]
      ring
    have hsum23 : (∑ a : Fin 4, α x (Function.update s a (d a))) =
        -(∑ a : Fin 4, α x (Function.update (fun b : Fin 4 => V23 b x) a
          ((cov (fun p : M => V23 a p) x) (U x)))) := by
      have hpair := fiberRegion_tensor_sum_antiPair (α x) s d σ23
        (by intro a; fin_cases a <;> simp [σ23]) hβ
      have hsimpa : (∑ a : Fin 4, α x (Function.update (s ∘ σ23) a (d (σ23 a)))) =
          ∑ a : Fin 4, α x (Function.update (fun b : Fin 4 => V23 b x) a
            ((cov (fun p : M => V23 a p) x) (U x))) := by
        apply Finset.sum_congr rfl
        intro a _
        congr 1
      linarith [hpair, hsimpa]
    calc
      nablaα x (Fin.cons u (vec4 X Y Z W))
          = extDerivFun (I := I) f x (U x) - ∑ a : Fin 4, α x (Function.update s a (d a)) := hderiv
      _ = -nablaα x (Fin.cons u (vec4 X Y W Z)) := by
            rw [hderiv23]
            rw [hext23, hsum23]
            ring
  have hbianchi : nablaα x (Fin.cons u (vec4 X Y Z W)) + nablaα x (Fin.cons u (vec4 Y Z X W)) +
      nablaα x (Fin.cons u (vec4 Z X Y W)) = 0 := by
    let τ : Fin 4 → Fin 4 := fun a => if a = 0 then 1 else if a = 1 then 2 else if a = 2 then 0 else a
    let V2 : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
      fun a => V (τ a)
    let V3 : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
      fun a => V (τ (τ a))
    have hV2 : (fun a : Fin 4 => V2 a x) = vec4 Y Z X W := by
      funext a
      fin_cases a <;> simp [V2, τ, hV, vec4]
    have hV3 : (fun a : Fin 4 => V3 a x) = vec4 Z X Y W := by
      funext a
      fin_cases a <;> simp [V3, τ, hV, vec4]
    have hderiv2 : nablaα x (Fin.cons u (vec4 Y Z X W)) =
        extDerivFun (I := I) (fun p : M => α p (fun a : Fin 4 => V2 a p)) x (U x) -
          ∑ a : Fin 4, α x (Function.update (fun b : Fin 4 => V2 b x) a
            ((cov (fun p : M => V2 a p) x) (U x))) := by
      have h := TotalNabla0SRealizes.eval_smooth_slots (I := I) hA U V2 x
      simpa [hU, hV2] using h
    have hderiv3 : nablaα x (Fin.cons u (vec4 Z X Y W)) =
        extDerivFun (I := I) (fun p : M => α p (fun a : Fin 4 => V3 a p)) x (U x) -
          ∑ a : Fin 4, α x (Function.update (fun b : Fin 4 => V3 b x) a
            ((cov (fun p : M => V3 a p) x) (U x))) := by
      have h := TotalNabla0SRealizes.eval_smooth_slots (I := I) hA U V3 x
      simpa [hU, hV3] using h
    have hfun2 : (fun p : M => α p (fun a : Fin 4 => V2 a p)) =
        fun p : M => α p (vec4 (V 1 p) (V 2 p) (V 0 p) (V 3 p)) := by
      funext p
      congr 1
      funext a
      fin_cases a <;> simp [V2, τ, vec4]
    have hfun3 : (fun p : M => α p (fun a : Fin 4 => V3 a p)) =
        fun p : M => α p (vec4 (V 2 p) (V 0 p) (V 1 p) (V 3 p)) := by
      funext p
      congr 1
      funext a
      fin_cases a <;> simp [V3, τ, vec4]
    have hfun : (fun p : M => α p (fun a : Fin 4 => V a p)) +
        (fun p : M => α p (fun a : Fin 4 => V2 a p)) +
        (fun p : M => α p (fun a : Fin 4 => V3 a p)) = 0 := by
      funext p
      have hrec1 : (fun a : Fin 4 => V a p) = vec4 (V 0 p) (V 1 p) (V 2 p) (V 3 p) := by
        funext a
        fin_cases a <;> simp [vec4]
      have hb := (hAlg p).bianchi (V 0 p) (V 1 p) (V 2 p) (V 3 p)
      have h2p : α p (fun a : Fin 4 => V2 a p) = α p (vec4 (V 1 p) (V 2 p) (V 0 p) (V 3 p)) := by
        congr 1
        funext a
        fin_cases a <;> simp [V2, τ, vec4]
      have h3p : α p (fun a : Fin 4 => V3 a p) = α p (vec4 (V 2 p) (V 0 p) (V 1 p) (V 3 p)) := by
        congr 1
        funext a
        fin_cases a <;> simp [V3, τ, vec4]
      calc
        α p (fun a : Fin 4 => V a p) + α p (fun a : Fin 4 => V2 a p) + α p (fun a : Fin 4 => V3 a p)
            = α p (vec4 (V 0 p) (V 1 p) (V 2 p) (V 3 p)) +
                α p (vec4 (V 1 p) (V 2 p) (V 0 p) (V 3 p)) +
                α p (vec4 (V 2 p) (V 0 p) (V 1 p) (V 3 p)) := by
              rw [hrec1, h2p, h3p]
        _ = 0 := hb
    have hext2 : extDerivFun (I := I) (fun p : M => α p (fun a : Fin 4 => V2 a p)) x (U x) =
        -extDerivFun (I := I) f x (U x) - extDerivFun (I := I) (fun p : M => α p (fun a : Fin 4 => V3 a p)) x (U x) := by
      let f2 : M → ℝ := fun p => α p (fun a : Fin 4 => V2 a p)
      let f3 : M → ℝ := fun p => α p (fun a : Fin 4 => V3 a p)
      have h1 : extDerivFun (I := I) (f + f2 + f3) x (U x) = 0 := by
        have hzero : f + f2 + f3 = 0 := hfun
        simp [hzero]
      have hmd1 : MDifferentiableAt I 𝓘(Real, Real) f x := hmdiff_f
      have hmd2 : MDifferentiableAt I 𝓘(Real, Real) f2 x :=
        ContMDiffAt.mdifferentiableAt
          (tensor0SField_eval_smooth_slots_contMDiffAt (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) α V2 x)
          (by simp)
      have hmd3 : MDifferentiableAt I 𝓘(Real, Real) f3 x :=
        ContMDiffAt.mdifferentiableAt
          (tensor0SField_eval_smooth_slots_contMDiffAt (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) α V3 x)
          (by simp)
      have h12 := extDerivFun_add (I := I) (g := f) (g' := f2) (x := x) hmd1 hmd2
      have h123 := extDerivFun_add (I := I) (g := f + f2) (g' := f3) (x := x) (hmd1.add hmd2) hmd3
      have hsum_deriv : extDerivFun (I := I) (f + f2 + f3) x (U x) =
          extDerivFun (I := I) f x (U x) + extDerivFun (I := I) f2 x (U x) +
            extDerivFun (I := I) f3 x (U x) := by
        calc
          extDerivFun (I := I) (f + f2 + f3) x (U x)
              = extDerivFun (I := I) (f + f2) x (U x) + extDerivFun (I := I) f3 x (U x) := by
                simpa [ContinuousLinearMap.add_apply] using congr(($(h123) : _) (U x))
          _ = (extDerivFun (I := I) f x (U x) + extDerivFun (I := I) f2 x (U x)) +
                extDerivFun (I := I) f3 x (U x) := by
                have happ : extDerivFun (I := I) (f + f2) x (U x) =
                    extDerivFun (I := I) f x (U x) + extDerivFun (I := I) f2 x (U x) := by
                  simpa [ContinuousLinearMap.add_apply] using congr(($(h12) : _) (U x))
                rw [happ]
          _ = extDerivFun (I := I) f x (U x) + extDerivFun (I := I) f2 x (U x) +
                extDerivFun (I := I) f3 x (U x) := by
                simp [add_assoc]
      have htotal : extDerivFun (I := I) f x (U x) + extDerivFun (I := I) f2 x (U x) +
            extDerivFun (I := I) f3 x (U x) = 0 := by
        rwa [hsum_deriv] at h1
      linarith
    have hβ : ∀ v : Fin 4 → TangentSpace I x, α x v + α x (v ∘ τ) + α x (v ∘ τ ∘ τ) = 0 := by
      intro v
      have h1 : α x v = tensor04StdAt (I := I) (M := M) (α x) (v 0) (v 1) (v 2) (v 3) := by
        congr 1
        funext b
        fin_cases b <;> simp [vec4]
      have h2 : α x (v ∘ τ) = tensor04StdAt (I := I) (M := M) (α x) (v 1) (v 2) (v 0) (v 3) := by
        congr 1
        funext b
        fin_cases b <;> simp [τ, vec4]
      have h3 : α x (v ∘ τ ∘ τ) = tensor04StdAt (I := I) (M := M) (α x) (v 2) (v 0) (v 1) (v 3) := by
        congr 1
        funext b
        fin_cases b <;> simp [τ, vec4]
      have hb := (hAlg x).bianchi (v 0) (v 1) (v 2) (v 3)
      rw [h1, h2, h3]
      exact hb
    have hsum2 : (∑ a : Fin 4, α x (Function.update (fun b : Fin 4 => V2 b x) a
          ((cov (fun p : M => V2 a p) x) (U x)))) =
        ∑ a : Fin 4, α x (Function.update (s ∘ τ) a (d (τ a))) := by
      apply Finset.sum_congr rfl
      intro a _
      congr 1
    have hsum3 : (∑ a : Fin 4, α x (Function.update (fun b : Fin 4 => V3 b x) a
          ((cov (fun p : M => V3 a p) x) (U x)))) =
        ∑ a : Fin 4, α x (Function.update (s ∘ τ ∘ τ) a (d (τ (τ a)))) := by
      apply Finset.sum_congr rfl
      intro a _
      congr 1
    have hpair := fiberRegion_tensor_sum_cyclePair (α x) s d τ
      (by intro a; fin_cases a <;> simp [τ]) hβ
    have hS : (∑ a : Fin 4, α x (Function.update s a (d a))) +
        (∑ a : Fin 4, α x (Function.update (fun b : Fin 4 => V2 b x) a
          ((cov (fun p : M => V2 a p) x) (U x)))) +
        (∑ a : Fin 4, α x (Function.update (fun b : Fin 4 => V3 b x) a
          ((cov (fun p : M => V3 a p) x) (U x)))) = 0 := by
      simpa [hsum2, hsum3] using hpair
    calc
      nablaα x (Fin.cons u (vec4 X Y Z W)) + nablaα x (Fin.cons u (vec4 Y Z X W)) +
          nablaα x (Fin.cons u (vec4 Z X Y W))
          = (extDerivFun (I := I) f x (U x) - ∑ a : Fin 4, α x (Function.update s a (d a))) +
              (extDerivFun (I := I) (fun p : M => α p (fun a : Fin 4 => V2 a p)) x (U x) -
                ∑ a : Fin 4, α x (Function.update (fun b : Fin 4 => V2 b x) a
                  ((cov (fun p : M => V2 a p) x) (U x)))) +
              (extDerivFun (I := I) (fun p : M => α p (fun a : Fin 4 => V3 a p)) x (U x) -
                ∑ a : Fin 4, α x (Function.update (fun b : Fin 4 => V3 b x) a
                  ((cov (fun p : M => V3 a p) x) (U x)))) := by
            rw [hderiv, hderiv2, hderiv3]
      _ = 0 := by
            rw [hext2]
            linarith [hS]
  exact ⟨hanti1, hanti2, hbianchi⟩

def fiberRegion_fin5_cons {α : Type*} (a0 : α) (f : Fin 4 → α) : Fin 5 → α :=
  fun a => Fin.cases (motive := fun _ : Fin 5 => α) a0 f a

@[simp] lemma fiberRegion_fin5_cons_zero {α : Type*} (a0 : α) (f : Fin 4 → α) :
    fiberRegion_fin5_cons a0 f 0 = a0 := by
  change Fin.cases (motive := fun _ : Fin 5 => α) a0 f 0 = a0
  simp

@[simp] lemma fiberRegion_fin5_cons_succ {α : Type*} (a0 : α) (f : Fin 4 → α) (i : Fin 4) :
    fiberRegion_fin5_cons a0 f i.succ = f i := by
  change Fin.cases (motive := fun _ : Fin 5 => α) a0 f i.succ = f i
  simp

@[simp] lemma fiberRegion_fin5_cons_apply {α : Type*} (a0 : α) (f : Fin 4 → α) :
    fiberRegion_fin5_cons a0 f 1 = f 0 ∧
      fiberRegion_fin5_cons a0 f 2 = f 1 ∧
      fiberRegion_fin5_cons a0 f 3 = f 2 ∧
      fiberRegion_fin5_cons a0 f 4 = f 3 := by
  constructor
  · simpa using (fiberRegion_fin5_cons_succ a0 f (0 : Fin 4))
  · constructor
    · simpa using (fiberRegion_fin5_cons_succ a0 f (1 : Fin 4))
    · constructor
      · simpa using (fiberRegion_fin5_cons_succ a0 f (2 : Fin 4))
      · simpa using (fiberRegion_fin5_cons_succ a0 f (3 : Fin 4))

lemma fiberRegion_fin5_cons_eq_cons {α : Type*} (a0 : α) (f : Fin 4 → α) :
    fiberRegion_fin5_cons a0 f = Fin.cons a0 f := by
  funext b
  cases b using Fin.cases with
  | zero => rfl
  | succ i => rfl

omit [CompleteSpace E] [IsManifold I 3 M] [SigmaCompactSpace M] [I.Boundaryless] in
lemma fiberRegion_nabla2_of_algCurvForm
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 4)
    (nablaα : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 5)
    (nabla2α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 6)
    (hA : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 cov α nablaα)
    (h2A : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5 cov nablaα nabla2α)
    (hAlg : ∀ y : M, IsAlgCurvForm
      (fun X Y Z W : TangentSpace I y => tensor04StdAt (I := I) (M := M) (α y) X Y Z W))
    (x : M) :
    ∀ u1 u2 X Y Z W : TangentSpace I x,
      nabla2α x (Fin.cons u1 (fiberRegion_fin5_cons u2 (vec4 X Y Z W))) =
          -nabla2α x (Fin.cons u1 (fiberRegion_fin5_cons u2 (vec4 Y X Z W))) ∧
      nabla2α x (Fin.cons u1 (fiberRegion_fin5_cons u2 (vec4 X Y Z W))) =
          -nabla2α x (Fin.cons u1 (fiberRegion_fin5_cons u2 (vec4 X Y W Z))) ∧
      nabla2α x (Fin.cons u1 (fiberRegion_fin5_cons u2 (vec4 X Y Z W))) +
          nabla2α x (Fin.cons u1 (fiberRegion_fin5_cons u2 (vec4 Y Z X W))) +
          nabla2α x (Fin.cons u1 (fiberRegion_fin5_cons u2 (vec4 Z X Y W))) = 0 := by
  classical
  have hSym5 : ∀ y : M, ∀ u X Y Z W : TangentSpace I y,
      nablaα y (Fin.cons u (vec4 X Y Z W)) = -nablaα y (Fin.cons u (vec4 Y X Z W)) ∧
      nablaα y (Fin.cons u (vec4 X Y Z W)) = -nablaα y (Fin.cons u (vec4 X Y W Z)) ∧
      nablaα y (Fin.cons u (vec4 X Y Z W)) + nablaα y (Fin.cons u (vec4 Y Z X W)) +
        nablaα y (Fin.cons u (vec4 Z X Y W)) = 0 :=
    fun y => fiberRegion_nabla_of_algCurvForm (I := I) cov α nablaα hA hAlg y
  intro u1 u2 X Y Z W
  let U1 : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    (ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x u1).choose
  have hU1 : U1 x = u1 :=
    (ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x u1).choose_spec
  let U2 : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    (ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x u2).choose
  have hU2 : U2 x = u2 :=
    (ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x u2).choose_spec
  let V : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    fun a => (ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x
      (vec4 X Y Z W a)).choose
  have hV : ∀ a : Fin 4, V a x = vec4 X Y Z W a := fun a =>
    (ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x
      (vec4 X Y Z W a)).choose_spec
  let W2 : Fin 5 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    fiberRegion_fin5_cons U2 V
  let s5 : Fin 5 → TangentSpace I x := fun b => W2 b x
  let d5 : Fin 5 → TangentSpace I x := fun a => (cov (fun p : M => W2 a p) x) (U1 x)
  let f : M → ℝ := fun p => nablaα p (fun a : Fin 5 => W2 a p)
  have hslots : (fun a : Fin 5 => W2 a x) = fiberRegion_fin5_cons u2 (vec4 X Y Z W) := by
    funext a
    fin_cases a <;> simp [W2, hU2, hV, vec4]
  have hderiv : nabla2α x (Fin.cons u1 (fiberRegion_fin5_cons u2 (vec4 X Y Z W))) =
      extDerivFun (I := I) f x (U1 x) - ∑ a : Fin 5, nablaα x (Function.update s5 a (d5 a)) := by
    have h := TotalNabla0SRealizes.eval_smooth_slots (I := I) h2A U1 W2 x
    simpa [hU1, s5, d5, f, hslots] using h
  have hmdiff_f : MDifferentiableAt I 𝓘(Real, Real) f x :=
    ContMDiffAt.mdifferentiableAt
      (tensor0SField_eval_smooth_slots_contMDiffAt (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) nablaα W2 x)
      (by simp)
  have hrec5 : ∀ v : Fin 5 → TangentSpace I x,
      v = fiberRegion_fin5_cons (v 0) (vec4 (v 1) (v 2) (v 3) (v 4)) := by
    intro v
    funext b
    fin_cases b <;> simp [vec4]
  have hanti1 : nabla2α x (Fin.cons u1 (fiberRegion_fin5_cons u2 (vec4 X Y Z W))) =
      -nabla2α x (Fin.cons u1 (fiberRegion_fin5_cons u2 (vec4 Y X Z W))) := by
    let σ12 : Fin 5 → Fin 5 := fun a => if a = 1 then 2 else if a = 2 then 1 else a
    let V01 : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
      fun a => V (if a = 0 then 1 else if a = 1 then 0 else a)
    have hV01 : ∀ a : Fin 4, V01 a x = vec4 Y X Z W a := by
      intro a
      fin_cases a <;> simp [V01, hV, vec4]
    let W2' : Fin 5 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
      fiberRegion_fin5_cons U2 V01
    have hslots01 : (fun a : Fin 5 => W2' a x) = fiberRegion_fin5_cons u2 (vec4 Y X Z W) := by
      funext a
      fin_cases a <;> simp [W2', hU2, hV01, vec4]
    have hderiv01 : nabla2α x (Fin.cons u1 (fiberRegion_fin5_cons u2 (vec4 Y X Z W))) =
        extDerivFun (I := I) (fun p : M => nablaα p (fun a : Fin 5 => W2' a p)) x (U1 x) -
          ∑ a : Fin 5, nablaα x (Function.update (fun b : Fin 5 => W2' b x) a
            ((cov (fun p : M => W2' a p) x) (U1 x))) := by
      have h := TotalNabla0SRealizes.eval_smooth_slots (I := I) h2A U1 W2' x
      simpa [hU1, hslots01] using h
    have hfun01 : (fun p : M => nablaα p (fun a : Fin 5 => W2' a p)) =
        fun p : M => -nablaα p (fun a : Fin 5 => W2 a p) := by
      funext p
      have hrec1 : (fun a : Fin 5 => W2' a p) = fiberRegion_fin5_cons (U2 p) (vec4 (V 1 p) (V 0 p) (V 2 p) (V 3 p)) := by
        funext a
        refine Fin.cases (motive := fun a => W2' a p =
            (fiberRegion_fin5_cons (U2 p) (vec4 (V 1 p) (V 0 p) (V 2 p) (V 3 p)) : Fin 5 → TangentSpace I p) a) ?_ ?_ a
        · simp [W2']
        · intro i
          change V01 i p = (vec4 (V 1 p) (V 0 p) (V 2 p) (V 3 p)) i
          fin_cases i <;> simp [V01, vec4]
      have hrec2 : (fun a : Fin 5 => W2 a p) = fiberRegion_fin5_cons (U2 p) (vec4 (V 0 p) (V 1 p) (V 2 p) (V 3 p)) := by
        funext a
        refine Fin.cases (motive := fun a => W2 a p =
            (fiberRegion_fin5_cons (U2 p) (vec4 (V 0 p) (V 1 p) (V 2 p) (V 3 p)) : Fin 5 → TangentSpace I p) a) ?_ ?_ a
        · simp [W2]
        · intro i
          change V i p = (vec4 (V 0 p) (V 1 p) (V 2 p) (V 3 p)) i
          fin_cases i <;> simp [vec4]
      have hsym := (hSym5 p (U2 p) (V 1 p) (V 0 p) (V 2 p) (V 3 p)).1
      calc
        nablaα p (fun a : Fin 5 => W2' a p)
            = nablaα p (fiberRegion_fin5_cons (U2 p) (vec4 (V 1 p) (V 0 p) (V 2 p) (V 3 p))) := by
              rw [hrec1]
        _ = -nablaα p (fiberRegion_fin5_cons (U2 p) (vec4 (V 0 p) (V 1 p) (V 2 p) (V 3 p))) := hsym
        _ = -nablaα p (fun a : Fin 5 => W2 a p) := by
              rw [hrec2]
    have hext01 : extDerivFun (I := I) (fun p : M => nablaα p (fun a : Fin 5 => W2' a p)) x (U1 x) =
        -extDerivFun (I := I) f x (U1 x) := by
      have hneg : extDerivFun (I := I) (fun p : M => -nablaα p (fun a : Fin 5 => W2 a p)) x (U1 x) =
          -extDerivFun (I := I) f x (U1 x) :=
        DifferentialGeometry.Tensor.RicciIdentity.extDerivFun_neg_at (I := I) (f := f) (x := x) (U1 x) hmdiff_f
      rw [← hfun01] at hneg
      simpa [f] using hneg
    have hβ : ∀ v : Fin 5 → TangentSpace I x, nablaα x v + nablaα x (v ∘ σ12) = 0 := by
      intro v
      have h1 : nablaα x v = nablaα x (fiberRegion_fin5_cons (v 0) (vec4 (v 1) (v 2) (v 3) (v 4))) := by
        rw [← hrec5 v]
      have h2 : nablaα x (v ∘ σ12) = nablaα x (fiberRegion_fin5_cons (v 0) (vec4 (v 2) (v 1) (v 3) (v 4))) := by
        congr 1
        funext b
        refine Fin.cases (motive := fun b => (v ∘ σ12) b =
            (fiberRegion_fin5_cons (v 0) (vec4 (v 2) (v 1) (v 3) (v 4)) : Fin 5 → TangentSpace I x) b) ?_ ?_ b
        · simp [σ12]
        · intro i
          change v (σ12 i.succ) = (vec4 (v 2) (v 1) (v 3) (v 4)) i
          fin_cases i <;> simp [σ12, vec4]
      have hsym := (hSym5 x (v 0) (v 1) (v 2) (v 3) (v 4)).1
      calc
        nablaα x v + nablaα x (v ∘ σ12)
            = nablaα x (fiberRegion_fin5_cons (v 0) (vec4 (v 1) (v 2) (v 3) (v 4))) +
                nablaα x (fiberRegion_fin5_cons (v 0) (vec4 (v 2) (v 1) (v 3) (v 4))) := by
              rw [h1, h2]
        _ = 0 := by
              rw [fiberRegion_fin5_cons_eq_cons (v 0) (vec4 (v 1) (v 2) (v 3) (v 4)),
                fiberRegion_fin5_cons_eq_cons (v 0) (vec4 (v 2) (v 1) (v 3) (v 4))]
              rw [hsym]
              ring
    have hpair : (∑ a : Fin 5, nablaα x (Function.update s5 a (d5 a))) +
        (∑ a : Fin 5, nablaα x (Function.update (s5 ∘ σ12) a (d5 (σ12 a)))) = 0 :=
      fiberRegion_tensor_sum_antiPair (nablaα x) s5 d5 σ12
        (by intro a; fin_cases a <;> simp [σ12]) hβ
    have hsimpa : (∑ a : Fin 5, nablaα x (Function.update (fun b : Fin 5 => W2' b x) a
          ((cov (fun p : M => W2' a p) x) (U1 x)))) =
        ∑ a : Fin 5, nablaα x (Function.update (s5 ∘ σ12) a (d5 (σ12 a))) := by
      apply Finset.sum_congr rfl
      intro a _
      congr 1
      funext b
      fin_cases a <;> fin_cases b <;> simp [s5, W2, W2', V01, σ12, d5, hU2, hV, vec4]
    have hsum01 : (∑ a : Fin 5, nablaα x (Function.update s5 a (d5 a))) =
        -(∑ a : Fin 5, nablaα x (Function.update (fun b : Fin 5 => W2' b x) a
          ((cov (fun p : M => W2' a p) x) (U1 x)))) := by
      rw [hsimpa]
      linarith [hpair]
    calc
      nabla2α x (Fin.cons u1 (fiberRegion_fin5_cons u2 (vec4 X Y Z W)))
          = extDerivFun (I := I) f x (U1 x) - ∑ a : Fin 5, nablaα x (Function.update s5 a (d5 a)) := hderiv
      _ = -nabla2α x (Fin.cons u1 (fiberRegion_fin5_cons u2 (vec4 Y X Z W))) := by
            rw [hderiv01]
            rw [hext01, hsum01]
            ring
  have hanti2 : nabla2α x (Fin.cons u1 (fiberRegion_fin5_cons u2 (vec4 X Y Z W))) =
      -nabla2α x (Fin.cons u1 (fiberRegion_fin5_cons u2 (vec4 X Y W Z))) := by
    let σ34 : Fin 5 → Fin 5 := fun a => if a = 3 then 4 else if a = 4 then 3 else a
    let V02 : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
      fun a => V (if a = 2 then 3 else if a = 3 then 2 else a)
    have hV02 : ∀ a : Fin 4, V02 a x = vec4 X Y W Z a := by
      intro a
      fin_cases a <;> simp [V02, hV, vec4]
    let W2'' : Fin 5 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
      fiberRegion_fin5_cons U2 V02
    have hslots02 : (fun a : Fin 5 => W2'' a x) = fiberRegion_fin5_cons u2 (vec4 X Y W Z) := by
      funext a
      fin_cases a <;> simp [W2'', hU2, hV02, vec4]
    have hderiv02 : nabla2α x (Fin.cons u1 (fiberRegion_fin5_cons u2 (vec4 X Y W Z))) =
        extDerivFun (I := I) (fun p : M => nablaα p (fun a : Fin 5 => W2'' a p)) x (U1 x) -
          ∑ a : Fin 5, nablaα x (Function.update (fun b : Fin 5 => W2'' b x) a
            ((cov (fun p : M => W2'' a p) x) (U1 x))) := by
      have h := TotalNabla0SRealizes.eval_smooth_slots (I := I) h2A U1 W2'' x
      simpa [hU1, hslots02] using h
    have hfun02 : (fun p : M => nablaα p (fun a : Fin 5 => W2'' a p)) =
        fun p : M => -nablaα p (fun a : Fin 5 => W2 a p) := by
      funext p
      have hrec1 : (fun a : Fin 5 => W2'' a p) = fiberRegion_fin5_cons (U2 p) (vec4 (V 0 p) (V 1 p) (V 3 p) (V 2 p)) := by
        funext a
        refine Fin.cases (motive := fun a => W2'' a p =
            (fiberRegion_fin5_cons (U2 p) (vec4 (V 0 p) (V 1 p) (V 3 p) (V 2 p)) : Fin 5 → TangentSpace I p) a) ?_ ?_ a
        · simp [W2'']
        · intro i
          change V02 i p = (vec4 (V 0 p) (V 1 p) (V 3 p) (V 2 p)) i
          fin_cases i <;> simp [V02, vec4]
      have hrec2 : (fun a : Fin 5 => W2 a p) = fiberRegion_fin5_cons (U2 p) (vec4 (V 0 p) (V 1 p) (V 2 p) (V 3 p)) := by
        funext a
        refine Fin.cases (motive := fun a => W2 a p =
            (fiberRegion_fin5_cons (U2 p) (vec4 (V 0 p) (V 1 p) (V 2 p) (V 3 p)) : Fin 5 → TangentSpace I p) a) ?_ ?_ a
        · simp [W2]
        · intro i
          change V i p = (vec4 (V 0 p) (V 1 p) (V 2 p) (V 3 p)) i
          fin_cases i <;> simp [vec4]
      have hsym := (hSym5 p (U2 p) (V 0 p) (V 1 p) (V 3 p) (V 2 p)).2.1
      calc
        nablaα p (fun a : Fin 5 => W2'' a p)
            = nablaα p (fiberRegion_fin5_cons (U2 p) (vec4 (V 0 p) (V 1 p) (V 3 p) (V 2 p))) := by
              rw [hrec1]
        _ = -nablaα p (fiberRegion_fin5_cons (U2 p) (vec4 (V 0 p) (V 1 p) (V 2 p) (V 3 p))) := hsym
        _ = -nablaα p (fun a : Fin 5 => W2 a p) := by
              rw [hrec2]
    have hext02 : extDerivFun (I := I) (fun p : M => nablaα p (fun a : Fin 5 => W2'' a p)) x (U1 x) =
        -extDerivFun (I := I) f x (U1 x) := by
      have hneg : extDerivFun (I := I) (fun p : M => -nablaα p (fun a : Fin 5 => W2 a p)) x (U1 x) =
          -extDerivFun (I := I) f x (U1 x) :=
        DifferentialGeometry.Tensor.RicciIdentity.extDerivFun_neg_at (I := I) (f := f) (x := x) (U1 x) hmdiff_f
      rw [← hfun02] at hneg
      simpa [f] using hneg
    have hβ : ∀ v : Fin 5 → TangentSpace I x, nablaα x v + nablaα x (v ∘ σ34) = 0 := by
      intro v
      have h1 : nablaα x v = nablaα x (fiberRegion_fin5_cons (v 0) (vec4 (v 1) (v 2) (v 3) (v 4))) := by
        rw [← hrec5 v]
      have h2 : nablaα x (v ∘ σ34) = nablaα x (fiberRegion_fin5_cons (v 0) (vec4 (v 1) (v 2) (v 4) (v 3))) := by
        congr 1
        funext b
        refine Fin.cases (motive := fun b => (v ∘ σ34) b =
            (fiberRegion_fin5_cons (v 0) (vec4 (v 1) (v 2) (v 4) (v 3)) : Fin 5 → TangentSpace I x) b) ?_ ?_ b
        · simp [σ34]
        · intro i
          change v (σ34 i.succ) = (vec4 (v 1) (v 2) (v 4) (v 3)) i
          fin_cases i <;> simp [σ34, vec4]
      have hsym := (hSym5 x (v 0) (v 1) (v 2) (v 3) (v 4)).2.1
      calc
        nablaα x v + nablaα x (v ∘ σ34)
            = nablaα x (fiberRegion_fin5_cons (v 0) (vec4 (v 1) (v 2) (v 3) (v 4))) +
                nablaα x (fiberRegion_fin5_cons (v 0) (vec4 (v 1) (v 2) (v 4) (v 3))) := by
              rw [h1, h2]
        _ = 0 := by
              rw [fiberRegion_fin5_cons_eq_cons (v 0) (vec4 (v 1) (v 2) (v 3) (v 4)),
                fiberRegion_fin5_cons_eq_cons (v 0) (vec4 (v 1) (v 2) (v 4) (v 3))]
              rw [hsym]
              ring
    have hpair : (∑ a : Fin 5, nablaα x (Function.update s5 a (d5 a))) +
        (∑ a : Fin 5, nablaα x (Function.update (s5 ∘ σ34) a (d5 (σ34 a)))) = 0 :=
      fiberRegion_tensor_sum_antiPair (nablaα x) s5 d5 σ34
        (by intro a; fin_cases a <;> simp [σ34]) hβ
    have hsimpa : (∑ a : Fin 5, nablaα x (Function.update (fun b : Fin 5 => W2'' b x) a
          ((cov (fun p : M => W2'' a p) x) (U1 x)))) =
        ∑ a : Fin 5, nablaα x (Function.update (s5 ∘ σ34) a (d5 (σ34 a))) := by
      apply Finset.sum_congr rfl
      intro a _
      congr 1
      funext b
      fin_cases a <;> fin_cases b <;> simp [s5, W2, W2'', V02, σ34, d5, hU2, hV, vec4]
    have hsum02 : (∑ a : Fin 5, nablaα x (Function.update s5 a (d5 a))) =
        -(∑ a : Fin 5, nablaα x (Function.update (fun b : Fin 5 => W2'' b x) a
          ((cov (fun p : M => W2'' a p) x) (U1 x)))) := by
      rw [hsimpa]
      linarith [hpair]
    calc
      nabla2α x (Fin.cons u1 (fiberRegion_fin5_cons u2 (vec4 X Y Z W)))
          = extDerivFun (I := I) f x (U1 x) - ∑ a : Fin 5, nablaα x (Function.update s5 a (d5 a)) := hderiv
      _ = -nabla2α x (Fin.cons u1 (fiberRegion_fin5_cons u2 (vec4 X Y W Z))) := by
            rw [hderiv02]
            rw [hext02, hsum02]
            ring
  have hbianchi : nabla2α x (Fin.cons u1 (fiberRegion_fin5_cons u2 (vec4 X Y Z W))) +
      nabla2α x (Fin.cons u1 (fiberRegion_fin5_cons u2 (vec4 Y Z X W))) +
      nabla2α x (Fin.cons u1 (fiberRegion_fin5_cons u2 (vec4 Z X Y W))) = 0 := by
    let τ : Fin 5 → Fin 5 := fun a => if a = 1 then 2 else if a = 2 then 3 else if a = 3 then 1 else a
    let V2 : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
      fun a => V (if a = 0 then 1 else if a = 1 then 2 else if a = 2 then 0 else a)
    let V3 : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
      fun a => V (if a = 0 then 2 else if a = 1 then 0 else if a = 2 then 1 else a)
    have hV2 : ∀ a : Fin 4, V2 a x = vec4 Y Z X W a := by
      intro a
      fin_cases a <;> simp [V2, hV, vec4]
    have hV3 : ∀ a : Fin 4, V3 a x = vec4 Z X Y W a := by
      intro a
      fin_cases a <;> simp [V3, hV, vec4]
    let W2b : Fin 5 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
      fiberRegion_fin5_cons U2 V2
    let W2c : Fin 5 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
      fiberRegion_fin5_cons U2 V3
    have hslots2 : (fun a : Fin 5 => W2b a x) = fiberRegion_fin5_cons u2 (vec4 Y Z X W) := by
      funext a
      fin_cases a <;> simp [W2b, hU2, hV2, vec4]
    have hslots3 : (fun a : Fin 5 => W2c a x) = fiberRegion_fin5_cons u2 (vec4 Z X Y W) := by
      funext a
      fin_cases a <;> simp [W2c, hU2, hV3, vec4]
    have hderiv2 : nabla2α x (Fin.cons u1 (fiberRegion_fin5_cons u2 (vec4 Y Z X W))) =
        extDerivFun (I := I) (fun p : M => nablaα p (fun a : Fin 5 => W2b a p)) x (U1 x) -
          ∑ a : Fin 5, nablaα x (Function.update (fun b : Fin 5 => W2b b x) a
            ((cov (fun p : M => W2b a p) x) (U1 x))) := by
      have h := TotalNabla0SRealizes.eval_smooth_slots (I := I) h2A U1 W2b x
      simpa [hU1, hslots2] using h
    have hderiv3 : nabla2α x (Fin.cons u1 (fiberRegion_fin5_cons u2 (vec4 Z X Y W))) =
        extDerivFun (I := I) (fun p : M => nablaα p (fun a : Fin 5 => W2c a p)) x (U1 x) -
          ∑ a : Fin 5, nablaα x (Function.update (fun b : Fin 5 => W2c b x) a
            ((cov (fun p : M => W2c a p) x) (U1 x))) := by
      have h := TotalNabla0SRealizes.eval_smooth_slots (I := I) h2A U1 W2c x
      simpa [hU1, hslots3] using h
    let f2 : M → ℝ := fun p => nablaα p (fun a : Fin 5 => W2b a p)
    let f3 : M → ℝ := fun p => nablaα p (fun a : Fin 5 => W2c a p)
    have hfun : f + f2 + f3 = 0 := by
      funext p
      have hrec1 : (fun a : Fin 5 => W2 a p) = fiberRegion_fin5_cons (U2 p) (vec4 (V 0 p) (V 1 p) (V 2 p) (V 3 p)) := by
        funext a
        refine Fin.cases (motive := fun a => W2 a p =
            (fiberRegion_fin5_cons (U2 p) (vec4 (V 0 p) (V 1 p) (V 2 p) (V 3 p)) : Fin 5 → TangentSpace I p) a) ?_ ?_ a
        · simp [W2]
        · intro i
          change V i p = (vec4 (V 0 p) (V 1 p) (V 2 p) (V 3 p)) i
          fin_cases i <;> simp [vec4]
      have hrec2 : (fun a : Fin 5 => W2b a p) = fiberRegion_fin5_cons (U2 p) (vec4 (V 1 p) (V 2 p) (V 0 p) (V 3 p)) := by
        funext a
        refine Fin.cases (motive := fun a => W2b a p =
            (fiberRegion_fin5_cons (U2 p) (vec4 (V 1 p) (V 2 p) (V 0 p) (V 3 p)) : Fin 5 → TangentSpace I p) a) ?_ ?_ a
        · simp [W2b]
        · intro i
          change V2 i p = (vec4 (V 1 p) (V 2 p) (V 0 p) (V 3 p)) i
          fin_cases i <;> simp [V2, vec4]
      have hrec3 : (fun a : Fin 5 => W2c a p) = fiberRegion_fin5_cons (U2 p) (vec4 (V 2 p) (V 0 p) (V 1 p) (V 3 p)) := by
        funext a
        refine Fin.cases (motive := fun a => W2c a p =
            (fiberRegion_fin5_cons (U2 p) (vec4 (V 2 p) (V 0 p) (V 1 p) (V 3 p)) : Fin 5 → TangentSpace I p) a) ?_ ?_ a
        · simp [W2c]
        · intro i
          change V3 i p = (vec4 (V 2 p) (V 0 p) (V 1 p) (V 3 p)) i
          fin_cases i <;> simp [V3, vec4]
      have hsym := (hSym5 p (U2 p) (V 0 p) (V 1 p) (V 2 p) (V 3 p)).2.2
      calc
        nablaα p (fun a : Fin 5 => W2 a p) + nablaα p (fun a : Fin 5 => W2b a p) +
            nablaα p (fun a : Fin 5 => W2c a p)
            = nablaα p (fiberRegion_fin5_cons (U2 p) (vec4 (V 0 p) (V 1 p) (V 2 p) (V 3 p))) +
                nablaα p (fiberRegion_fin5_cons (U2 p) (vec4 (V 1 p) (V 2 p) (V 0 p) (V 3 p))) +
                nablaα p (fiberRegion_fin5_cons (U2 p) (vec4 (V 2 p) (V 0 p) (V 1 p) (V 3 p))) := by
              rw [hrec1, hrec2, hrec3]
        _ = 0 := hsym
    have hext2 : extDerivFun (I := I) f2 x (U1 x) =
        -extDerivFun (I := I) f x (U1 x) - extDerivFun (I := I) f3 x (U1 x) := by
      have h1 : extDerivFun (I := I) (f + f2 + f3) x (U1 x) = 0 := by
        have hzero : f + f2 + f3 = 0 := hfun
        simp [hzero]
      have hmd1 : MDifferentiableAt I 𝓘(Real, Real) f x := hmdiff_f
      have hmd2 : MDifferentiableAt I 𝓘(Real, Real) f2 x :=
        ContMDiffAt.mdifferentiableAt
          (tensor0SField_eval_smooth_slots_contMDiffAt (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) nablaα W2b x)
          (by simp)
      have hmd3 : MDifferentiableAt I 𝓘(Real, Real) f3 x :=
        ContMDiffAt.mdifferentiableAt
          (tensor0SField_eval_smooth_slots_contMDiffAt (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) nablaα W2c x)
          (by simp)
      have h12 := extDerivFun_add (I := I) (g := f) (g' := f2) (x := x) hmd1 hmd2
      have h123 := extDerivFun_add (I := I) (g := f + f2) (g' := f3) (x := x) (hmd1.add hmd2) hmd3
      have hsum_deriv : extDerivFun (I := I) (f + f2 + f3) x (U1 x) =
          extDerivFun (I := I) f x (U1 x) + extDerivFun (I := I) f2 x (U1 x) +
            extDerivFun (I := I) f3 x (U1 x) := by
        calc
          extDerivFun (I := I) (f + f2 + f3) x (U1 x)
              = extDerivFun (I := I) (f + f2) x (U1 x) + extDerivFun (I := I) f3 x (U1 x) := by
                simpa [ContinuousLinearMap.add_apply] using congr(($(h123) : _) (U1 x))
          _ = (extDerivFun (I := I) f x (U1 x) + extDerivFun (I := I) f2 x (U1 x)) +
                extDerivFun (I := I) f3 x (U1 x) := by
                have happ : extDerivFun (I := I) (f + f2) x (U1 x) =
                    extDerivFun (I := I) f x (U1 x) + extDerivFun (I := I) f2 x (U1 x) := by
                  simpa [ContinuousLinearMap.add_apply] using congr(($(h12) : _) (U1 x))
                rw [happ]
          _ = extDerivFun (I := I) f x (U1 x) + extDerivFun (I := I) f2 x (U1 x) +
                extDerivFun (I := I) f3 x (U1 x) := by
                simp [add_assoc]
      have htotal : extDerivFun (I := I) f x (U1 x) + extDerivFun (I := I) f2 x (U1 x) +
            extDerivFun (I := I) f3 x (U1 x) = 0 := by
        rwa [hsum_deriv] at h1
      linarith
    have hβ : ∀ v : Fin 5 → TangentSpace I x,
        nablaα x v + nablaα x (v ∘ τ) + nablaα x (v ∘ τ ∘ τ) = 0 := by
      intro v
      have h1 : nablaα x v = nablaα x (fiberRegion_fin5_cons (v 0) (vec4 (v 1) (v 2) (v 3) (v 4))) := by
        rw [← hrec5 v]
      have h2 : nablaα x (v ∘ τ) = nablaα x (fiberRegion_fin5_cons (v 0) (vec4 (v 2) (v 3) (v 1) (v 4))) := by
        congr 1
        funext b
        refine Fin.cases (motive := fun b => (v ∘ τ) b =
            (fiberRegion_fin5_cons (v 0) (vec4 (v 2) (v 3) (v 1) (v 4)) : Fin 5 → TangentSpace I x) b) ?_ ?_ b
        · simp [τ]
        · intro i
          change v (τ i.succ) = (vec4 (v 2) (v 3) (v 1) (v 4)) i
          fin_cases i <;> simp [τ, vec4]
      have h3 : nablaα x (v ∘ τ ∘ τ) = nablaα x (fiberRegion_fin5_cons (v 0) (vec4 (v 3) (v 1) (v 2) (v 4))) := by
        congr 1
        funext b
        refine Fin.cases (motive := fun b => (v ∘ τ ∘ τ) b =
            (fiberRegion_fin5_cons (v 0) (vec4 (v 3) (v 1) (v 2) (v 4)) : Fin 5 → TangentSpace I x) b) ?_ ?_ b
        · simp [τ]
        · intro i
          change v (τ (τ i.succ)) = (vec4 (v 3) (v 1) (v 2) (v 4)) i
          fin_cases i <;> simp [τ, vec4]
      have hsym := (hSym5 x (v 0) (v 1) (v 2) (v 3) (v 4)).2.2
      calc
        nablaα x v + nablaα x (v ∘ τ) + nablaα x (v ∘ τ ∘ τ)
            = nablaα x (fiberRegion_fin5_cons (v 0) (vec4 (v 1) (v 2) (v 3) (v 4))) +
                nablaα x (fiberRegion_fin5_cons (v 0) (vec4 (v 2) (v 3) (v 1) (v 4))) +
                nablaα x (fiberRegion_fin5_cons (v 0) (vec4 (v 3) (v 1) (v 2) (v 4))) := by
              rw [h1, h2, h3]
        _ = 0 := by
              rw [fiberRegion_fin5_cons_eq_cons (v 0) (vec4 (v 1) (v 2) (v 3) (v 4)),
                fiberRegion_fin5_cons_eq_cons (v 0) (vec4 (v 2) (v 3) (v 1) (v 4)),
                fiberRegion_fin5_cons_eq_cons (v 0) (vec4 (v 3) (v 1) (v 2) (v 4))]
              exact hsym
    have hW2b : ∀ a : Fin 5, (fun p : M => W2b a p) = fun p : M => W2 (τ a) p := by
      intro a
      funext p
      fin_cases a <;> simp [W2b, W2, V2, τ]
    have hW2c : ∀ a : Fin 5, (fun p : M => W2c a p) = fun p : M => W2 (τ (τ a)) p := by
      intro a
      funext p
      fin_cases a <;> simp [W2c, W2, V3, τ]
    have hupd2 : ∀ a : Fin 5,
        Function.update (fun b : Fin 5 => W2b b x) a ((cov (fun p : M => W2b a p) x) (U1 x)) =
          Function.update (s5 ∘ τ) a (d5 (τ a)) := by
      intro a
      apply funext
      intro b
      rcases eq_or_ne b a with rfl | hb
      · rw [hW2b b]
        simp [Function.update, d5]
      · have hf : W2b b x = (s5 ∘ τ) b := by
          fin_cases b <;> simp [s5, W2, W2b, V2, τ, hV, vec4]
        simp [Function.update, hb, hf]
    have hupd3 : ∀ a : Fin 5,
        Function.update (fun b : Fin 5 => W2c b x) a ((cov (fun p : M => W2c a p) x) (U1 x)) =
          Function.update (s5 ∘ τ ∘ τ) a (d5 (τ (τ a))) := by
      intro a
      apply funext
      intro b
      rcases eq_or_ne b a with rfl | hb
      · rw [hW2c b]
        simp [Function.update, d5]
      · have hf : W2c b x = (s5 ∘ τ ∘ τ) b := by
          fin_cases b <;> simp [s5, W2, W2c, V3, τ, hV, vec4]
        simp [Function.update, hb, hf]
    have hsum2 : (∑ a : Fin 5, nablaα x (Function.update (fun b : Fin 5 => W2b b x) a
          ((cov (fun p : M => W2b a p) x) (U1 x)))) =
        ∑ a : Fin 5, nablaα x (Function.update (s5 ∘ τ) a (d5 (τ a))) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [hupd2 a]
    have hsum3 : (∑ a : Fin 5, nablaα x (Function.update (fun b : Fin 5 => W2c b x) a
          ((cov (fun p : M => W2c a p) x) (U1 x)))) =
        ∑ a : Fin 5, nablaα x (Function.update (s5 ∘ τ ∘ τ) a (d5 (τ (τ a)))) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [hupd3 a]
    have hpair := fiberRegion_tensor_sum_cyclePair (nablaα x) s5 d5 τ
      (by intro a; fin_cases a <;> simp [τ]) hβ
    have hS : (∑ a : Fin 5, nablaα x (Function.update s5 a (d5 a))) +
        (∑ a : Fin 5, nablaα x (Function.update (fun b : Fin 5 => W2b b x) a
          ((cov (fun p : M => W2b a p) x) (U1 x)))) +
        (∑ a : Fin 5, nablaα x (Function.update (fun b : Fin 5 => W2c b x) a
          ((cov (fun p : M => W2c a p) x) (U1 x)))) = 0 := by
      simpa [hsum2, hsum3] using hpair
    calc
      nabla2α x (Fin.cons u1 (fiberRegion_fin5_cons u2 (vec4 X Y Z W))) +
          nabla2α x (Fin.cons u1 (fiberRegion_fin5_cons u2 (vec4 Y Z X W))) +
          nabla2α x (Fin.cons u1 (fiberRegion_fin5_cons u2 (vec4 Z X Y W)))
          = (extDerivFun (I := I) f x (U1 x) - ∑ a : Fin 5, nablaα x (Function.update s5 a (d5 a))) +
              (extDerivFun (I := I) f2 x (U1 x) -
                ∑ a : Fin 5, nablaα x (Function.update (fun b : Fin 5 => W2b b x) a
                  ((cov (fun p : M => W2b a p) x) (U1 x)))) +
              (extDerivFun (I := I) f3 x (U1 x) -
                ∑ a : Fin 5, nablaα x (Function.update (fun b : Fin 5 => W2c b x) a
                  ((cov (fun p : M => W2c a p) x) (U1 x)))) := by
            rw [hderiv, hderiv2, hderiv3]
      _ = 0 := by
            rw [hext2]
            linarith [hS]
  exact ⟨hanti1, hanti2, hbianchi⟩

omit [SigmaCompactSpace M] [I.Boundaryless] in
theorem fiberRegion_roughLapRm04_mem_algebraicCurvatureTensorSubmodule
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (t : ℝ) (x : M)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x)) :
    metricTrace0S2TensorInBasis (I := I) basis (identityInvMetric (Idx := Fin 3))
        (nablaKRm04Field (I := I) S t 2 x) ∈
      algebraicCurvatureTensorSubmodule (I := I) (M := M) x := by
  classical
  have hA1 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4
      (S.base.connection t) (S.base.rm04 t) (nablaKRm04Field (I := I) S t 1) := by
    simpa [nablaKRm04Field_zero] using (nablaKRm04Field_realizes (I := I) S t 0)
  have hA2 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5
      (S.base.connection t) (nablaKRm04Field (I := I) S t 1) (nablaKRm04Field (I := I) S t 2) := by
    simpa using (nablaKRm04Field_realizes (I := I) S t 1)
  have hAlg : ∀ y : M, IsAlgCurvForm
      (fun X Y Z W : TangentSpace I y => tensor04StdAt (I := I) (M := M) (S.base.rm04 t y) X Y Z W) := by
    intro y
    exact mem_algebraicCurvatureTensorSubmodule.mp
      (metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) (S.base.metric t) y)
  have hSym6 : ∀ u1 u2 X Y Z W : TangentSpace I x,
      nablaKRm04Field (I := I) S t 2 x (Fin.cons u1 (Fin.cons u2 (vec4 X Y Z W))) =
          -nablaKRm04Field (I := I) S t 2 x (Fin.cons u1 (Fin.cons u2 (vec4 Y X Z W))) ∧
      nablaKRm04Field (I := I) S t 2 x (Fin.cons u1 (Fin.cons u2 (vec4 X Y Z W))) =
          -nablaKRm04Field (I := I) S t 2 x (Fin.cons u1 (Fin.cons u2 (vec4 X Y W Z))) ∧
      nablaKRm04Field (I := I) S t 2 x (Fin.cons u1 (Fin.cons u2 (vec4 X Y Z W))) +
          nablaKRm04Field (I := I) S t 2 x (Fin.cons u1 (Fin.cons u2 (vec4 Y Z X W))) +
          nablaKRm04Field (I := I) S t 2 x (Fin.cons u1 (Fin.cons u2 (vec4 Z X Y W))) = 0 :=
    fiberRegion_nabla2_of_algCurvForm (I := I) (S.base.connection t) (S.base.rm04 t)
      (nablaKRm04Field (I := I) S t 1) (nablaKRm04Field (I := I) S t 2) hA1 hA2 hAlg x
  let T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 6 x :=
    nablaKRm04Field (I := I) S t 2 x
  let R : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x :=
    metricTrace0S2TensorInBasis (I := I) basis (identityInvMetric (Idx := Fin 3)) T
  have hRapply : ∀ tail : Fin 4 → TangentSpace I x,
      R tail = ∑ i : Fin 3, ∑ j : Fin 3,
        identityInvMetric (Idx := Fin 3) i j * T (metricTraceInput (I := I) (basis i) (basis j) tail) := by
    intro tail
    rw [metricTrace0S2TensorInBasis_apply]
    rfl
  have hcons : ∀ (u1 u2 : TangentSpace I x) (tail : Fin 4 → TangentSpace I x),
      metricTraceInput (I := I) u1 u2 tail = Fin.cons u1 (Fin.cons u2 tail) := by
    intro u1 u2 tail
    rfl
  rw [mem_algebraicCurvatureTensorSubmodule_iff_symmetries]
  refine ⟨?_, ?_, ?_⟩
  · intro X Y Z W
    have hsym_per : ∀ i j : Fin 3,
        T (metricTraceInput (I := I) (basis i) (basis j) (vec4 X Y Z W)) =
          -T (metricTraceInput (I := I) (basis i) (basis j) (vec4 Y X Z W)) := by
      intro i j
      have h := (hSym6 (basis i) (basis j) X Y Z W).1
      simpa [T, hcons] using h
    calc
      tensor04StdAt (I := I) (M := M) R X Y Z W
          = ∑ i : Fin 3, ∑ j : Fin 3,
              identityInvMetric (Idx := Fin 3) i j *
                T (metricTraceInput (I := I) (basis i) (basis j) (vec4 X Y Z W)) := by
            simpa [R] using hRapply (vec4 X Y Z W)
      _ = -∑ i : Fin 3, ∑ j : Fin 3,
              identityInvMetric (Idx := Fin 3) i j *
                T (metricTraceInput (I := I) (basis i) (basis j) (vec4 Y X Z W)) := by
            simp_rw [hsym_per]
            simp [Finset.sum_neg_distrib, mul_neg]
      _ = -tensor04StdAt (I := I) (M := M) R Y X Z W := by
            rw [← hRapply (vec4 Y X Z W)]
            rfl
  · intro X Y Z W
    have hsym_per : ∀ i j : Fin 3,
        T (metricTraceInput (I := I) (basis i) (basis j) (vec4 X Y Z W)) =
          -T (metricTraceInput (I := I) (basis i) (basis j) (vec4 X Y W Z)) := by
      intro i j
      have h := (hSym6 (basis i) (basis j) X Y Z W).2.1
      simpa [T, hcons] using h
    calc
      tensor04StdAt (I := I) (M := M) R X Y Z W
          = ∑ i : Fin 3, ∑ j : Fin 3,
              identityInvMetric (Idx := Fin 3) i j *
                T (metricTraceInput (I := I) (basis i) (basis j) (vec4 X Y Z W)) := by
            simpa [R] using hRapply (vec4 X Y Z W)
      _ = -∑ i : Fin 3, ∑ j : Fin 3,
              identityInvMetric (Idx := Fin 3) i j *
                T (metricTraceInput (I := I) (basis i) (basis j) (vec4 X Y W Z)) := by
            simp_rw [hsym_per]
            simp [Finset.sum_neg_distrib, mul_neg]
      _ = -tensor04StdAt (I := I) (M := M) R X Y W Z := by
            rw [← hRapply (vec4 X Y W Z)]
            rfl
  · intro X Y Z W
    have hsym_per : ∀ i j : Fin 3,
        T (metricTraceInput (I := I) (basis i) (basis j) (vec4 X Y Z W)) +
            T (metricTraceInput (I := I) (basis i) (basis j) (vec4 Y Z X W)) +
            T (metricTraceInput (I := I) (basis i) (basis j) (vec4 Z X Y W)) = 0 := by
      intro i j
      have h := (hSym6 (basis i) (basis j) X Y Z W).2.2
      simpa [T, hcons] using h
    calc
      tensor04StdAt (I := I) (M := M) R X Y Z W +
          tensor04StdAt (I := I) (M := M) R Y Z X W +
          tensor04StdAt (I := I) (M := M) R Z X Y W
          = (∑ i : Fin 3, ∑ j : Fin 3,
              identityInvMetric (Idx := Fin 3) i j *
                T (metricTraceInput (I := I) (basis i) (basis j) (vec4 X Y Z W))) +
              (∑ i : Fin 3, ∑ j : Fin 3,
                identityInvMetric (Idx := Fin 3) i j *
                  T (metricTraceInput (I := I) (basis i) (basis j) (vec4 Y Z X W))) +
              (∑ i : Fin 3, ∑ j : Fin 3,
                identityInvMetric (Idx := Fin 3) i j *
                  T (metricTraceInput (I := I) (basis i) (basis j) (vec4 Z X Y W))) := by
            rw [show tensor04StdAt (I := I) (M := M) R X Y Z W =
                ∑ i : Fin 3, ∑ j : Fin 3, identityInvMetric (Idx := Fin 3) i j *
                  T (metricTraceInput (I := I) (basis i) (basis j) (vec4 X Y Z W)) from by
              simpa [R] using hRapply (vec4 X Y Z W)]
            rw [show tensor04StdAt (I := I) (M := M) R Y Z X W =
                ∑ i : Fin 3, ∑ j : Fin 3, identityInvMetric (Idx := Fin 3) i j *
                  T (metricTraceInput (I := I) (basis i) (basis j) (vec4 Y Z X W)) from by
              simpa [R] using hRapply (vec4 Y Z X W)]
            rw [show tensor04StdAt (I := I) (M := M) R Z X Y W =
                ∑ i : Fin 3, ∑ j : Fin 3, identityInvMetric (Idx := Fin 3) i j *
                  T (metricTraceInput (I := I) (basis i) (basis j) (vec4 Z X Y W)) from by
              simpa [R] using hRapply (vec4 Z X Y W)]
      _ = 0 := by
            have hper2 : ∀ i j : Fin 3,
                identityInvMetric (Idx := Fin 3) i j *
                    T (metricTraceInput (I := I) (basis i) (basis j) (vec4 X Y Z W)) +
                  identityInvMetric (Idx := Fin 3) i j *
                    T (metricTraceInput (I := I) (basis i) (basis j) (vec4 Y Z X W)) +
                  identityInvMetric (Idx := Fin 3) i j *
                    T (metricTraceInput (I := I) (basis i) (basis j) (vec4 Z X Y W)) = 0 := by
              intro i j
              have h := hsym_per i j
              calc
                identityInvMetric (Idx := Fin 3) i j *
                      T (metricTraceInput (I := I) (basis i) (basis j) (vec4 X Y Z W)) +
                    identityInvMetric (Idx := Fin 3) i j *
                      T (metricTraceInput (I := I) (basis i) (basis j) (vec4 Y Z X W)) +
                    identityInvMetric (Idx := Fin 3) i j *
                      T (metricTraceInput (I := I) (basis i) (basis j) (vec4 Z X Y W))
                    = identityInvMetric (Idx := Fin 3) i j *
                        (T (metricTraceInput (I := I) (basis i) (basis j) (vec4 X Y Z W)) +
                          T (metricTraceInput (I := I) (basis i) (basis j) (vec4 Y Z X W)) +
                          T (metricTraceInput (I := I) (basis i) (basis j) (vec4 Z X Y W))) := by
                      ring
                _ = 0 := by
                      rw [h]
                      ring
            calc
              (∑ i : Fin 3, ∑ j : Fin 3,
                    identityInvMetric (Idx := Fin 3) i j *
                      T (metricTraceInput (I := I) (basis i) (basis j) (vec4 X Y Z W))) +
                  (∑ i : Fin 3, ∑ j : Fin 3,
                    identityInvMetric (Idx := Fin 3) i j *
                      T (metricTraceInput (I := I) (basis i) (basis j) (vec4 Y Z X W))) +
                  (∑ i : Fin 3, ∑ j : Fin 3,
                    identityInvMetric (Idx := Fin 3) i j *
                      T (metricTraceInput (I := I) (basis i) (basis j) (vec4 Z X Y W)))
                  = ∑ i : Fin 3, ∑ j : Fin 3,
                      (identityInvMetric (Idx := Fin 3) i j *
                          T (metricTraceInput (I := I) (basis i) (basis j) (vec4 X Y Z W)) +
                        identityInvMetric (Idx := Fin 3) i j *
                          T (metricTraceInput (I := I) (basis i) (basis j) (vec4 Y Z X W)) +
                        identityInvMetric (Idx := Fin 3) i j *
                          T (metricTraceInput (I := I) (basis i) (basis j) (vec4 Z X Y W))) := by
                    rw [← Finset.sum_add_distrib]
                    rw [← Finset.sum_add_distrib]
                    apply Finset.sum_congr rfl
                    intro i _
                    rw [← Finset.sum_add_distrib]
                    rw [← Finset.sum_add_distrib]
              _ = 0 := by
                    apply Finset.sum_eq_zero
                    intro i _
                    apply Finset.sum_eq_zero
                    intro j _
                    exact hper2 i j

omit [IsManifold I 3 M] [SigmaCompactSpace M] [I.Boundaryless] in
theorem fiberRegion_roughLapRm04_component_eq
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    {t : ℝ} (x : M)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (hOrth : OrthonormalBasisAt (I := I) (S.base.metric t) x basis)
    (a b c d : Fin 3) :
    metricTraceFirstTwo0SAt (I := I) (S.base.metric t) (nablaKRm04Field (I := I) S t 2 x)
        (vec4 (I := I) (basisAt x a) (basisAt x b) (basisAt x c) (basisAt x d)) =
      tensor04StdAt (I := I) (M := M)
        (metricTrace0S2TensorInBasis (I := I) basis (identityInvMetric (Idx := Fin 3))
          (nablaKRm04Field (I := I) S t 2 x))
        (basisAt x a) (basisAt x b) (basisAt x c) (basisAt x d) := by
  have hinv : MetricInverseInBasis_gen (I := I) (S.base.metric t) x basis
      (identityInvMetric (Idx := Fin 3)) := by
    exact fiberRegion_metricInverseInBasis_identity_of_orthonormal (I := I)
      (S.base.metric t) basis (by
        intro i j
        simpa [delta3] using hOrth i j)
  rw [fiberRegion_metricTraceFirstTwo0SAt_eq_metricTrace0S2InBasis (I := I) (S.base.metric t) basis
    (identityInvMetric (Idx := Fin 3)) hinv (nablaKRm04Field (I := I) S t 2 x)
    (vec4 (I := I) (basisAt x a) (basisAt x b) (basisAt x c) (basisAt x d))]
  rw [← metricTrace0S2TensorInBasis_apply]
  rfl

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [I.Boundaryless] in
theorem pulledRmComp_pullback
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (iota : MatrixComp M (Fin 3)) :
    UhlenbeckPullbackRmComponents iota
      (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a))
      (pulledRmComp S basisAt iota) := by
  intro t x a b c d
  change tensor04StdAt (I := I) (M := M) (uhlenbeckPulledRm04At S basisAt iota t x)
      (basisAt x a) (basisAt x b) (basisAt x c) (basisAt x d) =
    uhlenbeckPullbackRmInFrame iota
      (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a)) t x a b c d
  simpa [solutionRm04CompInFrame, rm04Comp] using
    uhlenbeckPulledRm04At_apply_basis (I := I) (M := M) S basisAt iota t x a b c d

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [I.Boundaryless] in
lemma fiberRegion_pulledComponent_continuousOn_time
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn (I := I) S)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (iota : MatrixComp M (Fin 3))
    (hiotaCont : ∀ x : M, ContinuousOn (fun t : ℝ => iota t x) (Set.Icc 0 T))
    (x : M) (a b c d : Fin 3) :
    ContinuousOn (fun s : ℝ => tensor04StdAt (I := I) (M := M)
        (uhlenbeckPulledRm04At S basisAt iota s x)
        (basisAt x a) (basisAt x b) (basisAt x c) (basisAt x d))
      (Set.Icc 0 T) := by
  classical
  have hiota_comp : ∀ a k : Fin 3, ContinuousOn (fun s : ℝ => iota s x a k) (Set.Icc 0 T) := by
    intro a k
    have h1 : ContinuousOn (fun s : ℝ => iota s x a) (Set.Icc 0 T) := (continuousOn_pi.mp (hiotaCont x)) a
    exact (continuousOn_pi.mp h1) k
  have hrm04_comp : ∀ v w y z : TangentSpace I x,
      ContinuousOn (fun s : ℝ => tensor04StdAt (I := I) (M := M) (S.base.rm04 s x) v w y z)
        (Set.Icc 0 T) := by
    intro v w y z
    rw [continuousOn_iff_continuous_restrict]
    let P : Set ℝ := Set.Icc 0 T
    have hA : Tensor0SFamilyContinuousOnSet (I := I) (M := M) 4 P
        (fun t x => S.base.rm04 t x) := by
      exact Tensor0SFamilyContinuousOnSet.mono (I := I) (M := M)
        hS.rm04Cont (by intro s hs; exact hs)
    have heval := Tensor0SFamilyContinuousOnSet.eval_continuous (I := I) (M := M) (s := 4)
      (K := P) (A := fun t x => S.base.rm04 t x) hA
      (P := {q : ℝ // q ∈ P}) (τ := fun p : {q : ℝ // q ∈ P} => p.1)
      (b := fun p : {q : ℝ // q ∈ P} => x)
      continuous_subtype_val (fun p : {q : ℝ // q ∈ P} => p.2) continuous_const
      (v := fun i : Fin 4 => fun p : {q : ℝ // q ∈ P} =>
        if i = 0 then v else if i = 1 then w else if i = 2 then y else z)
      (by
        intro i
        fin_cases i
        · exact continuous_const
        · exact continuous_const
        · exact continuous_const
        · exact continuous_const)
    have hmain : Continuous (fun p : {q : ℝ // q ∈ P} =>
        tensor04StdAt (I := I) (M := M) (S.base.rm04 p.1 x) v w y z) := by
      refine heval.congr (fun p => ?_)
      rfl
    simpa [P] using hmain
  have hpoly : ∀ s : ℝ,
      tensor04StdAt (I := I) (M := M) (uhlenbeckPulledRm04At S basisAt iota s x)
          (basisAt x a) (basisAt x b) (basisAt x c) (basisAt x d) =
        ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
          iota s x a i * iota s x b j * iota s x c k * iota s x d l *
            tensor04StdAt (I := I) (M := M) (S.base.rm04 s x)
              (basisAt x i) (basisAt x j) (basisAt x k) (basisAt x l) := by
    intro s
    have h := uhlenbeckPulledRm04At_apply_basis (I := I) (M := M) S basisAt iota s x a b c d
    simpa [solutionRm04CompInFrame, rm04Comp] using h
  rw [continuousOn_congr (fun s hs => hpoly s)]
  refine continuousOn_finset_sum Finset.univ ?_
  intro i _
  refine continuousOn_finset_sum Finset.univ ?_
  intro j _
  refine continuousOn_finset_sum Finset.univ ?_
  intro k _
  refine continuousOn_finset_sum Finset.univ ?_
  intro l _
  simpa [mul_assoc] using
    ((((hiota_comp a i).mul (hiota_comp b j)).mul (hiota_comp c k)).mul (hiota_comp d l)).mul
      (hrm04_comp (basisAt x i) (basisAt x j) (basisAt x k) (basisAt x l))


omit [I.Boundaryless] [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] in
theorem fiberRegion_rm04Comp_expand_gen
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) {x : M}
    (e : Fin 3 → TangentSpace I x)
    (f : Module.Basis (Fin 3) Real (TangentSpace I x))
    (P : Fin 3 → Fin 3 → ℝ)
    (hP : ∀ i j : Fin 3, P j i = f.repr (e i) j)
    (H : Fin 4 → Fin 3) :
    S.base.rm04 t x (fun p : Fin 4 => e (H p)) =
      ∑ J : Fin 4 → Fin 3,
        S.base.rm04 t x (fun p : Fin 4 => f (J p)) *
          (∏ p : Fin 4, P (J p) (H p)) := by
  classical
  have hsum := tensor0S_apply_eq_sum (𝕜 := ℝ) (I := I) f (S.base.rm04 t x)
    (fun p : Fin 4 => e (H p))
  rw [hsum]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [show component0S (I := I) f (S.base.rm04 t x) J =
      S.base.rm04 t x (fun p : Fin 4 => f (J p)) by rfl]
  congr 1
  apply Finset.prod_congr rfl
  intro p _
  exact fixedFrame_coord_eq f e P hP (H p) (J p)

theorem fiberRegion_sum_comp_perm
    (σ : Equiv.Perm (Fin 4)) (F : (Fin 4 → Fin 3) → ℝ) :
    (∑ J : Fin 4 → Fin 3, F (fun p : Fin 4 => J (σ p))) = ∑ J : Fin 4 → Fin 3, F J := by
  classical
  let e : (Fin 4 → Fin 3) ≃ (Fin 4 → Fin 3) := {
    toFun := fun J : Fin 4 → Fin 3 => fun p : Fin 4 => J (σ p)
    invFun := fun J : Fin 4 → Fin 3 => fun p : Fin 4 => J (σ.symm p)
    left_inv := by
      intro J
      funext p
      simp
    right_inv := by
      intro J
      funext p
      simp
  }
  exact Fintype.sum_equiv e (fun J => F (fun p : Fin 4 => J (σ p))) (fun J => F J)
    (by intro J; rfl)

theorem fiberRegion_sum_lin_comb (w A B1 B2 B3 B4 D : (Fin 4 → Fin 3) → ℝ) :
    (∑ J : Fin 4 → Fin 3, w J * A J)
        - 2 * ((∑ J : Fin 4 → Fin 3, w J * B1 J) - (∑ J : Fin 4 → Fin 3, w J * B2 J)
            + (∑ J : Fin 4 → Fin 3, w J * B3 J) - (∑ J : Fin 4 → Fin 3, w J * B4 J))
        - (∑ J : Fin 4 → Fin 3, w J * D J)
      = (∑ J : Fin 4 → Fin 3,
          w J * (A J + (-2 * (B1 J - B2 J + B3 J - B4 J) - D J))) := by
  rw [show (∑ J : Fin 4 → Fin 3,
        w J * (A J + (-2 * (B1 J - B2 J + B3 J - B4 J) - D J))) =
      (∑ J : Fin 4 → Fin 3,
        (w J * A J + w J * (-2 * (B1 J - B2 J + B3 J - B4 J)) - w J * D J)) by
    refine Finset.sum_congr rfl fun J _ => ?_
    ring]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [show (∑ J : Fin 4 → Fin 3, w J * (-2 * (B1 J - B2 J + B3 J - B4 J))) =
      (∑ J : Fin 4 → Fin 3, -2 * (w J * (B1 J - B2 J + B3 J - B4 J))) by
    refine Finset.sum_congr rfl fun J _ => ?_
    ring]
  rw [← Finset.mul_sum]
  rw [show (∑ J : Fin 4 → Fin 3, w J * (B1 J - B2 J + B3 J - B4 J)) =
      (∑ J : Fin 4 → Fin 3, w J * B1 J) - (∑ J : Fin 4 → Fin 3, w J * B2 J)
        + (∑ J : Fin 4 → Fin 3, w J * B3 J) - (∑ J : Fin 4 → Fin 3, w J * B4 J) by
    rw [show (∑ J : Fin 4 → Fin 3,
          w J * (B1 J - B2 J + B3 J - B4 J)) =
        (∑ J : Fin 4 → Fin 3,
          (w J * B1 J - w J * B2 J + w J * B3 J - w J * B4 J)) by
      refine Finset.sum_congr rfl fun J _ => ?_
      ring]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib]]
  ring
omit [IsManifold I 3 M] in
theorem fiberRegion_solutionRm04FixedFrameEvolution
    (T : ℝ) (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn (I := I) S)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x)) :
    Riemann04BTensorWithRicciDriftEvolutionInFrameOn
      (D := RealTimeInterval.closed 0 T hT.le)
      (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a))
      (fun t x a b c d =>
        metricTraceFirstTwo0SAt (I := I) (S.base.metric t) (nablaKRm04Field (I := I) S t 2 x)
          (vec4 (I := I) (basisAt x a) (basisAt x b) (basisAt x c) (basisAt x d)))
      (uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
        (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a)))
      (solutionRicciOneUpInFrame (I := I) S (solutionInverseMetricComponents S basisAt)
        (fun a x => basisAt x a)) := by
  classical
  intro t x a b c d
  let D : RealTimeInterval := RealTimeInterval.closed 0 T hT.le
  rcases exists_orthonormalBasisAt (I := I) (S.base.metric (t : ℝ)) x (hdim x) with ⟨f, hf⟩
  let e : Fin 3 → TangentSpace I x := fun i => basisAt x i
  let P : Fin 3 → Fin 3 → ℝ := fun j i => f.repr (e i) j
  have hP : ∀ i j : Fin 3, P j i = f.repr (e i) j := by
    intro i j
    rfl
  have horth : ∀ i j : Fin 3, (S.base.metric (t : ℝ)).inner x (f i) (f j) = kd i j := by
    intro i j
    simpa [kd, delta3] using hf i j
  let gInvAt : Fin 3 → Fin 3 → ℝ := fun i j =>
    solutionInverseMetricComponents S basisAt (t : ℝ) x i j
  have hginv : ∀ i j : Fin 3,
      (∑ k : Fin 3, gInvAt i k * (S.base.metric (t : ℝ)).inner x (e k) (e j)) = kd i j := by
    intro i j
    have h := solutionInverseMetricComponents_mul_metric (I := I) (M := M) S basisAt (t : ℝ) x i j
    simpa [gInvAt, e, metricCompInFrame, kd] using h
  have hbase : ∀ I0 : Fin 4 → Fin 3,
      HasDerivWithinAt
        (fun r : ℝ => S.base.rm04 r x (fun p : Fin 4 => f (I0 p)))
        (tensor0SComponent (I := I)
            (metricTrace0S2TensorInBasis (I := I) f (identityInvMetric (Idx := Fin 3))
              (nablaKRm04Field (I := I) S (t : ℝ) 2 x))
            (fun i => f i) I0 +
          (-2 * (Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                  (I0 0) (I0 1) (I0 2) (I0 3) -
                Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                  (I0 0) (I0 1) (I0 3) (I0 2) +
                Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                  (I0 0) (I0 2) (I0 1) (I0 3) -
                Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                  (I0 0) (I0 3) (I0 1) (I0 2)) -
            drift (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
              (I0 0) (I0 1) (I0 2) (I0 3)))
        (RealTimeInterval.closed 0 T hT.le).carrier (t : ℝ) := by
    intro I0
    have h := rm04Base_of_sol (I := I) (M := M) S hS t hdim x f horth I0
    simpa [kd] using h
  have hfun : (fun r : ℝ => S.base.rm04 r x (vec4 (I := I) (e a) (e b) (e c) (e d))) =
      fun r : ℝ => ∑ J : Fin 4 → Fin 3,
        (∏ p : Fin 4, P (J p) (slots4 a b c d p)) * S.base.rm04 r x (fun p : Fin 4 => f (J p)) := by
    funext r
    have hgen := fiberRegion_rm04Comp_expand_gen (I := I) S r e f P hP (slots4 a b c d)
    calc
      S.base.rm04 r x (vec4 (I := I) (e a) (e b) (e c) (e d))
          = S.base.rm04 r x (fun p : Fin 4 => e (slots4 a b c d p)) := by
            congr 1
            funext p
            fin_cases p <;> simp [slots4, vec4]
      _ = ∑ J : Fin 4 → Fin 3,
            (∏ p : Fin 4, P (J p) (slots4 a b c d p)) * S.base.rm04 r x (fun p : Fin 4 => f (J p)) := by
            simpa [mul_comm, mul_left_comm, mul_assoc] using hgen
  have hmain : HasDerivWithinAt
      (fun r : ℝ => ∑ J : Fin 4 → Fin 3,
        (∏ p : Fin 4, P (J p) (slots4 a b c d p)) * S.base.rm04 r x (fun p : Fin 4 => f (J p)))
      (∑ J : Fin 4 → Fin 3, (∏ p : Fin 4, P (J p) (slots4 a b c d p)) *
        (tensor0SComponent (I := I)
            (metricTrace0S2TensorInBasis (I := I) f (identityInvMetric (Idx := Fin 3))
              (nablaKRm04Field (I := I) S (t : ℝ) 2 x))
            (fun i => f i) J +
          (-2 * (Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                  (J 0) (J 1) (J 2) (J 3) -
                Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                  (J 0) (J 1) (J 3) (J 2) +
                Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                  (J 0) (J 2) (J 1) (J 3) -
                Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                  (J 0) (J 3) (J 1) (J 2)) -
            drift (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
              (J 0) (J 1) (J 2) (J 3))))
      (RealTimeInterval.closed 0 T hT.le).carrier (t : ℝ) := by
    refine HasDerivWithinAt.fun_sum ?_
    intro J _hJ
    exact (hbase J).const_mul (∏ p : Fin 4, P (J p) (slots4 a b c d p))
  have hfin : HasDerivWithinAt
      (fun r : ℝ => solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a)
        r x a b c d)
      (metricTraceFirstTwo0SAt (I := I) (S.base.metric (t : ℝ)) (nablaKRm04Field (I := I) S (t : ℝ) 2 x)
          (vec4 (I := I) (e a) (e b) (e c) (e d)) -
        2 * (uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
              (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a))
              (t : ℝ) x a b c d -
            uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
              (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a))
              (t : ℝ) x a b d c +
            uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
              (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a))
              (t : ℝ) x a c b d -
            uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
              (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a))
              (t : ℝ) x a d b c) -
        riemann04RicciDriftInFrame
          (solutionRicciOneUpInFrame (I := I) S (solutionInverseMetricComponents S basisAt)
            (fun a x => basisAt x a))
          (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a))
          (t : ℝ) x a b c d)
      (RealTimeInterval.closed 0 T hT.le).carrier (t : ℝ) := by
    have hT1 := roughLapRm04_fixedFrame_pullback (I := I) (M := M) S (t : ℝ) e f P hP horth a b c d
    have hT2 := uhlenbeckBTensorInFrame_fixedFrame_pullback (I := I) (M := M) S (t : ℝ) (hdim x) e f P
      (solutionInverseMetricComponents S basisAt) hP horth hginv a b c d
    have hT3 := riemann04RicciDriftInFrame_fixedFrame_pullback (I := I) (M := M) S (t : ℝ) (hdim x) e f P
      (solutionInverseMetricComponents S basisAt) hP horth hginv a b c d
    let σ23 : Equiv.Perm (Fin 4) := {
      toFun := fun p => if p = 2 then 3 else if p = 3 then 2 else p
      invFun := fun p => if p = 2 then 3 else if p = 3 then 2 else p
      left_inv := by intro p; fin_cases p <;> simp
      right_inv := by intro p; fin_cases p <;> simp
    }
    have hσ23_0 : σ23 0 = 0 := by decide
    have hσ23_1 : σ23 1 = 1 := by decide
    have hσ23_2 : σ23 2 = 3 := by decide
    have hσ23_3 : σ23 3 = 2 := by decide
    have hB0 : uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
          (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a)) (t : ℝ) x a b c d =
        ∑ I0 : Fin 4 → Fin 3,
          (∏ p : Fin 4, P (I0 p) (slots4 a b c d p)) *
            Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
              (I0 0) (I0 1) (I0 2) (I0 3) := by
      have hA : uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
            (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a)) (t : ℝ) x a b c d =
          uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
            (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a _ => e a)) (t : ℝ) x a b c d := by
        simp [uhlenbeckBTensorInFrame, solutionRm04CompInFrame, rm04Comp, e]
      exact hA.trans hT2
    have hdrift : riemann04RicciDriftInFrame
          (solutionRicciOneUpInFrame (I := I) S (solutionInverseMetricComponents S basisAt)
            (fun a x => basisAt x a))
          (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a))
          (t : ℝ) x a b c d =
        ∑ I0 : Fin 4 → Fin 3,
          (∏ p : Fin 4, P (I0 p) (slots4 a b c d p)) *
            drift (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
              (I0 0) (I0 1) (I0 2) (I0 3) := by
      have hA : riemann04RicciDriftInFrame
            (solutionRicciOneUpInFrame (I := I) S (solutionInverseMetricComponents S basisAt)
              (fun a x => basisAt x a))
            (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a))
            (t : ℝ) x a b c d =
          riemann04RicciDriftInFrame
            (solutionRicciOneUpInFrame (I := I) S (solutionInverseMetricComponents S basisAt)
              (fun a _ => e a))
            (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a _ => e a))
            (t : ℝ) x a b c d := by
        simp [riemann04RicciDriftInFrame, solutionRicciOneUpInFrame, solutionRm04CompInFrame, rm04Comp, e]
      exact hA.trans hT3
    have hlap : metricTraceFirstTwo0SAt (I := I) (S.base.metric (t : ℝ)) (nablaKRm04Field (I := I) S (t : ℝ) 2 x)
          (vec4 (I := I) (e a) (e b) (e c) (e d)) =
        ∑ I0 : Fin 4 → Fin 3,
          (∏ p : Fin 4, P (I0 p) (slots4 a b c d p)) *
            tensor0SComponent (metricTrace0S2TensorInBasis (I := I) f (identityInvMetric (Idx := Fin 3))
              (nablaKRm04Field (I := I) S (t : ℝ) 2 x)) (fun i => f i) I0 := by
      exact hT1.trans rfl
    have hT2b := uhlenbeckBTensorInFrame_fixedFrame_pullback (I := I) (M := M) S (t : ℝ) (hdim x) e f P
      (solutionInverseMetricComponents S basisAt) hP horth hginv a b d c
    have hA1 : uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
          (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a)) (t : ℝ) x a b d c =
        uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
          (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a _ => e a)) (t : ℝ) x a b d c := by
      simp [uhlenbeckBTensorInFrame, solutionRm04CompInFrame, rm04Comp, e]
    have hB1 : uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
          (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a)) (t : ℝ) x a b d c =
        ∑ J : Fin 4 → Fin 3,
          (∏ p : Fin 4, P (J p) (slots4 a b c d p)) *
            Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
              (J 0) (J 1) (J 3) (J 2) := by
      calc
        uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
            (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a)) (t : ℝ) x a b d c
            = uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
              (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a _ => e a)) (t : ℝ) x a b d c := hA1
        _ = ∑ I0 : Fin 4 → Fin 3,
                (∏ p : Fin 4, P (I0 p) (slots4 a b d c p)) *
                  Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                    (I0 0) (I0 1) (I0 2) (I0 3) := hT2b
        _ = ∑ J : Fin 4 → Fin 3,
                (∏ p : Fin 4, P (J (σ23 p)) (slots4 a b d c p)) *
                  Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                    (J (σ23 0)) (J (σ23 1)) (J (σ23 2)) (J (σ23 3)) := by
              rw [← fiberRegion_sum_comp_perm σ23 (fun J =>
                (∏ p : Fin 4, P (J p) (slots4 a b d c p)) *
                  Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                    (J 0) (J 1) (J 2) (J 3))]
        _ = ∑ J : Fin 4 → Fin 3,
                (∏ p : Fin 4, P (J p) (slots4 a b c d p)) *
                  Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                    (J 0) (J 1) (J 3) (J 2) := by
              refine Finset.sum_congr rfl fun J _ => ?_
              simp only [Fin.prod_univ_four, slots4, Fin.isValue, Fin.reduceEq, reduceIte]
              rw [hσ23_0, hσ23_1, hσ23_2, hσ23_3]
              ring
    let σ12 : Equiv.Perm (Fin 4) := {
      toFun := fun p => if p = 1 then 2 else if p = 2 then 1 else p
      invFun := fun p => if p = 1 then 2 else if p = 2 then 1 else p
      left_inv := by intro p; fin_cases p <;> simp
      right_inv := by intro p; fin_cases p <;> simp
    }
    have hσ12_0 : σ12 0 = 0 := by decide
    have hσ12_1 : σ12 1 = 2 := by decide
    have hσ12_2 : σ12 2 = 1 := by decide
    have hσ12_3 : σ12 3 = 3 := by decide
    let σ13 : Equiv.Perm (Fin 4) := {
      toFun := fun p => if p = 1 then 3 else if p = 2 then 1 else if p = 3 then 2 else p
      invFun := fun p => if p = 2 then 3 else if p = 3 then 1 else if p = 1 then 2 else p
      left_inv := by intro p; fin_cases p <;> simp
      right_inv := by intro p; fin_cases p <;> simp
    }
    have hσ13_0 : σ13 0 = 0 := by decide
    have hσ13_1 : σ13 1 = 3 := by decide
    have hσ13_2 : σ13 2 = 1 := by decide
    have hσ13_3 : σ13 3 = 2 := by decide
    have hT2c := uhlenbeckBTensorInFrame_fixedFrame_pullback (I := I) (M := M) S (t : ℝ) (hdim x) e f P
      (solutionInverseMetricComponents S basisAt) hP horth hginv a c b d
    have hA2 : uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
          (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a)) (t : ℝ) x a c b d =
        uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
          (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a _ => e a)) (t : ℝ) x a c b d := by
      simp [uhlenbeckBTensorInFrame, solutionRm04CompInFrame, rm04Comp, e]
    have hB2 : uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
          (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a)) (t : ℝ) x a c b d =
        ∑ J : Fin 4 → Fin 3,
          (∏ p : Fin 4, P (J p) (slots4 a b c d p)) *
            Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
              (J 0) (J 2) (J 1) (J 3) := by
      calc
        uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
            (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a)) (t : ℝ) x a c b d
            = uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
              (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a _ => e a)) (t : ℝ) x a c b d := hA2
        _ = ∑ I0 : Fin 4 → Fin 3,
                (∏ p : Fin 4, P (I0 p) (slots4 a c b d p)) *
                  Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                    (I0 0) (I0 1) (I0 2) (I0 3) := hT2c
        _ = ∑ J : Fin 4 → Fin 3,
                (∏ p : Fin 4, P (J (σ12 p)) (slots4 a c b d p)) *
                  Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                    (J (σ12 0)) (J (σ12 1)) (J (σ12 2)) (J (σ12 3)) := by
              rw [← fiberRegion_sum_comp_perm σ12 (fun J =>
                (∏ p : Fin 4, P (J p) (slots4 a c b d p)) *
                  Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                    (J 0) (J 1) (J 2) (J 3))]
        _ = ∑ J : Fin 4 → Fin 3,
                (∏ p : Fin 4, P (J p) (slots4 a b c d p)) *
                  Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                    (J 0) (J 2) (J 1) (J 3) := by
              refine Finset.sum_congr rfl fun J _ => ?_
              simp only [Fin.prod_univ_four, slots4, Fin.isValue, Fin.reduceEq, reduceIte]
              rw [hσ12_0, hσ12_1, hσ12_2, hσ12_3]
              ring
    have hT2d := uhlenbeckBTensorInFrame_fixedFrame_pullback (I := I) (M := M) S (t : ℝ) (hdim x) e f P
      (solutionInverseMetricComponents S basisAt) hP horth hginv a d b c
    have hA3 : uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
          (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a)) (t : ℝ) x a d b c =
        uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
          (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a _ => e a)) (t : ℝ) x a d b c := by
      simp [uhlenbeckBTensorInFrame, solutionRm04CompInFrame, rm04Comp, e]
    have hB3 : uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
          (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a)) (t : ℝ) x a d b c =
        ∑ J : Fin 4 → Fin 3,
          (∏ p : Fin 4, P (J p) (slots4 a b c d p)) *
            Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
              (J 0) (J 3) (J 1) (J 2) := by
      calc
        uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
            (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a)) (t : ℝ) x a d b c
            = uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
              (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a _ => e a)) (t : ℝ) x a d b c := hA3
        _ = ∑ I0 : Fin 4 → Fin 3,
                (∏ p : Fin 4, P (I0 p) (slots4 a d b c p)) *
                  Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                    (I0 0) (I0 1) (I0 2) (I0 3) := hT2d
        _ = ∑ J : Fin 4 → Fin 3,
                (∏ p : Fin 4, P (J (σ13 p)) (slots4 a d b c p)) *
                  Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                    (J (σ13 0)) (J (σ13 1)) (J (σ13 2)) (J (σ13 3)) := by
              rw [← fiberRegion_sum_comp_perm σ13 (fun J =>
                (∏ p : Fin 4, P (J p) (slots4 a d b c p)) *
                  Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                    (J 0) (J 1) (J 2) (J 3))]
        _ = ∑ J : Fin 4 → Fin 3,
                (∏ p : Fin 4, P (J p) (slots4 a b c d p)) *
                  Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                    (J 0) (J 3) (J 1) (J 2) := by
              refine Finset.sum_congr rfl fun J _ => ?_
              simp only [Fin.prod_univ_four, slots4, Fin.isValue, Fin.reduceEq, reduceIte]
              rw [hσ13_0, hσ13_1, hσ13_2, hσ13_3]
              ring
    have hRHS : metricTraceFirstTwo0SAt (I := I) (S.base.metric (t : ℝ)) (nablaKRm04Field (I := I) S (t : ℝ) 2 x)
          (vec4 (I := I) (e a) (e b) (e c) (e d)) -
        2 * (uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
              (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a))
              (t : ℝ) x a b c d -
            uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
              (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a))
              (t : ℝ) x a b d c +
            uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
              (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a))
              (t : ℝ) x a c b d -
            uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
              (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a))
              (t : ℝ) x a d b c) -
        riemann04RicciDriftInFrame
          (solutionRicciOneUpInFrame (I := I) S (solutionInverseMetricComponents S basisAt)
            (fun a x => basisAt x a))
          (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a))
          (t : ℝ) x a b c d
        = (∑ I0 : Fin 4 → Fin 3,
            (∏ p : Fin 4, P (I0 p) (slots4 a b c d p)) *
              tensor0SComponent (metricTrace0S2TensorInBasis (I := I) f (identityInvMetric (Idx := Fin 3))
                (nablaKRm04Field (I := I) S (t : ℝ) 2 x)) (fun i => f i) I0)
          - 2 * ((∑ I0 : Fin 4 → Fin 3,
                (∏ p : Fin 4, P (I0 p) (slots4 a b c d p)) *
                  Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                    (I0 0) (I0 1) (I0 2) (I0 3))
              - (∑ I0 : Fin 4 → Fin 3,
                (∏ p : Fin 4, P (I0 p) (slots4 a b c d p)) *
                  Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                    (I0 0) (I0 1) (I0 3) (I0 2))
              + (∑ I0 : Fin 4 → Fin 3,
                (∏ p : Fin 4, P (I0 p) (slots4 a b c d p)) *
                  Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                    (I0 0) (I0 2) (I0 1) (I0 3))
              - (∑ I0 : Fin 4 → Fin 3,
                (∏ p : Fin 4, P (I0 p) (slots4 a b c d p)) *
                  Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                    (I0 0) (I0 3) (I0 1) (I0 2)))
          - (∑ I0 : Fin 4 → Fin 3,
              (∏ p : Fin 4, P (I0 p) (slots4 a b c d p)) *
                drift (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                  (I0 0) (I0 1) (I0 2) (I0 3)) := by
      rw [hlap, hB0, hB1, hB2, hB3, hdrift]
    have hEq : metricTraceFirstTwo0SAt (I := I) (S.base.metric (t : ℝ)) (nablaKRm04Field (I := I) S (t : ℝ) 2 x)
          (vec4 (I := I) (e a) (e b) (e c) (e d)) -
        2 * (uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
              (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a))
              (t : ℝ) x a b c d -
            uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
              (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a))
              (t : ℝ) x a b d c +
            uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
              (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a))
              (t : ℝ) x a c b d -
            uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
              (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a))
              (t : ℝ) x a d b c) -
        riemann04RicciDriftInFrame
          (solutionRicciOneUpInFrame (I := I) S (solutionInverseMetricComponents S basisAt)
            (fun a x => basisAt x a))
          (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a))
          (t : ℝ) x a b c d
        = ∑ I0 : Fin 4 → Fin 3, (∏ p : Fin 4, P (I0 p) (slots4 a b c d p)) *
            (tensor0SComponent (I := I)
                (metricTrace0S2TensorInBasis (I := I) f (identityInvMetric (Idx := Fin 3))
                  (nablaKRm04Field (I := I) S (t : ℝ) 2 x))
                (fun i => f i) I0 +
              (-2 * (Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                      (I0 0) (I0 1) (I0 2) (I0 3) -
                    Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                      (I0 0) (I0 1) (I0 3) (I0 2) +
                    Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                      (I0 0) (I0 2) (I0 1) (I0 3) -
                    Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                      (I0 0) (I0 3) (I0 1) (I0 2)) -
                drift (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                  (I0 0) (I0 1) (I0 2) (I0 3))) := by
      rw [hRHS]
      rw [fiberRegion_sum_lin_comb (fun I0 : Fin 4 → Fin 3 => ∏ p : Fin 4, P (I0 p) (slots4 a b c d p))
          (fun I0 => tensor0SComponent (metricTrace0S2TensorInBasis (I := I) f (identityInvMetric (Idx := Fin 3))
            (nablaKRm04Field (I := I) S (t : ℝ) 2 x)) (fun i => f i) I0)
          (fun I0 => Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j))) (I0 0) (I0 1) (I0 2) (I0 3))
          (fun I0 => Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j))) (I0 0) (I0 1) (I0 3) (I0 2))
          (fun I0 => Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j))) (I0 0) (I0 2) (I0 1) (I0 3))
          (fun I0 => Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j))) (I0 0) (I0 3) (I0 1) (I0 2))
          (fun I0 => drift (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j))) (I0 0) (I0 1) (I0 2) (I0 3))]
    have hdev : HasDerivWithinAt
        (fun r : ℝ => S.base.rm04 r x (vec4 (I := I) (e a) (e b) (e c) (e d)))
        (∑ I0 : Fin 4 → Fin 3, (∏ p : Fin 4, P (I0 p) (slots4 a b c d p)) *
          (tensor0SComponent (I := I)
              (metricTrace0S2TensorInBasis (I := I) f (identityInvMetric (Idx := Fin 3))
                (nablaKRm04Field (I := I) S (t : ℝ) 2 x))
              (fun i => f i) I0 +
            (-2 * (Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                    (I0 0) (I0 1) (I0 2) (I0 3) -
                  Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                    (I0 0) (I0 1) (I0 3) (I0 2) +
                  Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                    (I0 0) (I0 2) (I0 1) (I0 3) -
                  Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                    (I0 0) (I0 3) (I0 1) (I0 2)) -
              drift (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                (I0 0) (I0 1) (I0 2) (I0 3)))) D.carrier (t : ℝ) := by
      rw [hfun]
      exact hmain
    simpa [hEq, e, solutionRm04CompInFrame, rm04Comp] using hdev
  simpa [solutionRicciOneUpInFrame, e] using hfin


omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless] [IsManifold I 1 M]
  [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
theorem fiberRegion_pullbackTensorAt_apply
    (iota : MatrixComp M (Fin 3)) (t : ℝ) (x : M)
    (A : Tensor04At (I := I) (M := M) x) (X Y Z W : TangentSpace I x) :
    tensor04StdAt (I := I) (M := M) (uhlenbeckPullbackTensorAt basisAt iota t x A) X Y Z W =
      tensor04StdAt (I := I) (M := M) A
        (uhlenbeckEndomorphismAt (basisAt x) iota t X)
        (uhlenbeckEndomorphismAt (basisAt x) iota t Y)
        (uhlenbeckEndomorphismAt (basisAt x) iota t Z)
        (uhlenbeckEndomorphismAt (basisAt x) iota t W) := by
  change (A : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ)
      (fun i : Fin 4 =>
        uhlenbeckEndomorphismAt (basisAt x) iota t (vec4 X Y Z W i)) =
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ)
      (vec4 (uhlenbeckEndomorphismAt (basisAt x) iota t X)
        (uhlenbeckEndomorphismAt (basisAt x) iota t Y)
        (uhlenbeckEndomorphismAt (basisAt x) iota t Z)
        (uhlenbeckEndomorphismAt (basisAt x) iota t W))
  congr 1
  funext i
  fin_cases i <;> simp [vec4]


omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
  [SigmaCompactSpace M] [T2Space M] in
theorem fiberRegion_sum4_factor (A B C D : Fin 3 → ℝ) :
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3, A i * B j * C k * D l) =
      (∑ i : Fin 3, A i) * (∑ j : Fin 3, B j) * (∑ k : Fin 3, C k) * (∑ l : Fin 3, D l) := by
  calc
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3, A i * B j * C k * D l)
        = ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, A i * B j * C k * (∑ l : Fin 3, D l) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
            Finset.sum_congr rfl fun k _ => ?_
          rw [← Finset.mul_sum]
    _ = ∑ i : Fin 3, ∑ j : Fin 3, (A i * B j) * (∑ k : Fin 3, C k * (∑ l : Fin 3, D l)) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [show (∑ k : Fin 3, A i * B j * C k * (∑ l : Fin 3, D l)) =
              ∑ k : Fin 3, (A i * B j) * (C k * (∑ l : Fin 3, D l)) by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [mul_assoc]]
          rw [← Finset.mul_sum]
    _ = ∑ i : Fin 3, A i * (∑ j : Fin 3, B j * (∑ k : Fin 3, C k * (∑ l : Fin 3, D l))) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [show (∑ j : Fin 3, (A i * B j) * (∑ k : Fin 3, C k * (∑ l : Fin 3, D l))) =
              ∑ j : Fin 3, A i * (B j * (∑ k : Fin 3, C k * (∑ l : Fin 3, D l))) by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [← mul_assoc]]
          rw [← Finset.mul_sum]
    _ = (∑ i : Fin 3, A i) * ((∑ j : Fin 3, B j) * ((∑ k : Fin 3, C k) * (∑ l : Fin 3, D l))) := by
          rw [← Finset.sum_mul]
          rw [← Finset.sum_mul]
          rw [← Finset.sum_mul]
    _ = (∑ i : Fin 3, A i) * (∑ j : Fin 3, B j) * (∑ k : Fin 3, C k) * (∑ l : Fin 3, D l) := by
          rw [mul_assoc, mul_assoc]

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
  [SigmaCompactSpace M] [T2Space M] in
theorem fiberRegion_sum5_swap
    (F : Fin 3 → Fin 3 → Fin 3 → Fin 3 → (Fin 4 → Fin 3) → ℝ) :
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3, ∑ I0 : Fin 4 → Fin 3, F i j k l I0) =
      ∑ I0 : Fin 4 → Fin 3, ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3, F i j k l I0 := by
  rw [show (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3, ∑ I0 : Fin 4 → Fin 3, F i j k l I0) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ I0 : Fin 4 → Fin 3, ∑ l : Fin 3, F i j k l I0 by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]]
  rw [show (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ I0 : Fin 4 → Fin 3, ∑ l : Fin 3, F i j k l I0) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ I0 : Fin 4 → Fin 3, ∑ k : Fin 3, ∑ l : Fin 3, F i j k l I0 by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]]
  rw [show (∑ i : Fin 3, ∑ j : Fin 3, ∑ I0 : Fin 4 → Fin 3, ∑ k : Fin 3, ∑ l : Fin 3, F i j k l I0) =
      ∑ i : Fin 3, ∑ I0 : Fin 4 → Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3, F i j k l I0 by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]]
  rw [show (∑ i : Fin 3, ∑ I0 : Fin 4 → Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3, F i j k l I0) =
      ∑ I0 : Fin 4 → Fin 3, ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3, F i j k l I0 by
    rw [Finset.sum_comm]]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless] [IsManifold I 1 M]
  [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
theorem fiberRegion_compU_mem_algebraicCurvatureTensorSubmodule
    (iota : MatrixComp M (Fin 3)) (t : ℝ) (x : M)
    (A : Tensor04At (I := I) (M := M) x)
    (hA : A ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    uhlenbeckPullbackTensorAt basisAt iota t x A ∈
      algebraicCurvatureTensorSubmodule (I := I) (M := M) x := by
  rw [mem_algebraicCurvatureTensorSubmodule]
  have hform : IsAlgCurvForm (tensor04StdAt (I := I) (M := M) A) :=
    mem_algebraicCurvatureTensorSubmodule.mp hA
  change IsAlgCurvForm (fun X Y Z W =>
    tensor04StdAt (uhlenbeckPullbackTensorAt basisAt iota t x A) X Y Z W)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x₁ x₂ y z w
    rw [fiberRegion_pullbackTensorAt_apply (I := I) (M := M) basisAt iota t x A (x₁ + x₂) y z w,
      fiberRegion_pullbackTensorAt_apply (I := I) (M := M) basisAt iota t x A x₁ y z w,
      fiberRegion_pullbackTensorAt_apply (I := I) (M := M) basisAt iota t x A x₂ y z w]
    rw [show uhlenbeckEndomorphismAt (basisAt x) iota t (x₁ + x₂) =
        uhlenbeckEndomorphismAt (basisAt x) iota t x₁ +
          uhlenbeckEndomorphismAt (basisAt x) iota t x₂ from by simp]
    exact hform.add_left _ _ _ _ _
  · intro a u y z w
    rw [fiberRegion_pullbackTensorAt_apply (I := I) (M := M) basisAt iota t x A (a • u) y z w,
      fiberRegion_pullbackTensorAt_apply (I := I) (M := M) basisAt iota t x A u y z w]
    rw [show uhlenbeckEndomorphismAt (basisAt x) iota t (a • u) =
        a • uhlenbeckEndomorphismAt (basisAt x) iota t u from by simp]
    exact hform.smul_left _ _ _ _ _
  · intro u v y z
    rw [fiberRegion_pullbackTensorAt_apply (I := I) (M := M) basisAt iota t x A u v y z,
      fiberRegion_pullbackTensorAt_apply (I := I) (M := M) basisAt iota t x A v u y z]
    exact hform.anti_first _ _ _ _
  · intro u v y z
    rw [fiberRegion_pullbackTensorAt_apply (I := I) (M := M) basisAt iota t x A u v y z,
      fiberRegion_pullbackTensorAt_apply (I := I) (M := M) basisAt iota t x A u v z y]
    exact hform.anti_last _ _ _ _
  · intro u v y z
    rw [fiberRegion_pullbackTensorAt_apply (I := I) (M := M) basisAt iota t x A u v y z,
      fiberRegion_pullbackTensorAt_apply (I := I) (M := M) basisAt iota t x A v y u z,
      fiberRegion_pullbackTensorAt_apply (I := I) (M := M) basisAt iota t x A y u v z]
    exact hform.bianchi _ _ _ _

omit [CompleteSpace E] [I.Boundaryless] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
  [SigmaCompactSpace M] [T2Space M] in
theorem fiberRegion_pulledTensor_scalarization_eq
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (iota : MatrixComp M (Fin 3)) (t : ℝ) (x : M)
    (horth : OrthonormalBasisAt (I := I) g x (basisAt x))
    (A : Tensor04At (I := I) (M := M) x)
    (hAlg : uhlenbeckPullbackTensorAt basisAt iota t x A ∈
      algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (ν : Tensor04At (I := I) (M := M) x) :
    inner0S (I := I) g x 4 (uhlenbeckPullbackTensorAt basisAt iota t x A) ν =
      4 * inner ℝ (uhlenbeckCurvatureOperatorMatrix
        (fun t' x' a b c d => tensor04StdAt (I := I) (M := M)
          (uhlenbeckPullbackTensorAt basisAt iota t' x' A)
          (basisAt x' a) (basisAt x' b) (basisAt x' c) (basisAt x' d)) t x)
        (regionSupportVector g basisAt x ν) := by
  have hmat : uhlenbeckCurvatureOperatorMatrix
        (fun t' x' a b c d => tensor04StdAt (I := I) (M := M)
          (uhlenbeckPullbackTensorAt basisAt iota t' x' A)
          (basisAt x' a) (basisAt x' b) (basisAt x' c) (basisAt x' d)) t x =
      matrixToEuclid (curvatureOperatorMatrixAt (I := I) x (basisAt x)
        ⟨uhlenbeckPullbackTensorAt basisAt iota t x A, hAlg⟩) := by
    have hmain := uhlenbeckCurvatureOperatorMatrixAsMatrix_eq_curvatureOperatorMatrixAt
      (I := I) (M := M) (x := x) (basis := basisAt x)
      (A := ⟨uhlenbeckPullbackTensorAt basisAt iota t x A, hAlg⟩)
      (pulledRm := fun t' x' a b c d => tensor04StdAt (I := I) (M := M)
        (uhlenbeckPullbackTensorAt basisAt iota t' x' A)
        (basisAt x' a) (basisAt x' b) (basisAt x' c) (basisAt x' d))
      (t := t)
      (by intro a b c d; rfl)
    rw [← hmain]
    unfold matrixToEuclid uhlenbeckCurvatureOperatorMatrixAsMatrix uhlenbeckCurvatureOperatorMatrix
    rfl
  have hmain := inner0S_eq_four_mul_inner_regionProjMatrix (I := I) g x (basisAt x) horth hAlg ν
  rw [← hmat] at hmain
  rw [real_inner_comm] at hmain
  simpa [regionSupportVector] using hmain

omit [I.Boundaryless] [IsManifold I 2 M] [IsManifold I 3 M] in
theorem fiberRegion_pulledRmComp_eq_rm
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt x))
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) (x : M) :
    ∀ a b c d : Fin 3,
      pulledRmComp S basisAt iota t x a b c d =
        rm (fun i j : Fin 3 => S.ricciAt t x (vec2 (I := I)
          (uhlenbeckMovingBasis hT S basisAt iota hiota0 hgram t ht x i)
          (uhlenbeckMovingBasis hT S basisAt iota hiota0 hgram t ht x j))) a b c d := by
  intro a b c d
  let moving : Module.Basis (Fin 3) Real (TangentSpace I x) :=
    uhlenbeckMovingBasis hT S basisAt iota hiota0 hgram t ht x
  have hmovingOrth : ∀ i j : Fin 3, (S.base.metric t).inner x (moving i) (moving j) = kd i j := by
    intro i j
    dsimp [moving]
    exact uhlenbeckMovingBasis_orthonormalBasisAt (I := I) (M := M) hT S basisAt iota hiota0 hgram x
      (horth0 x) ht i j
  calc
    pulledRmComp S basisAt iota t x a b c d
        = tensor04StdAt (uhlenbeckPulledRm04At S basisAt iota t x)
            (basisAt x a) (basisAt x b) (basisAt x c) (basisAt x d) := rfl
    _ = tensor04StdAt (S.base.rm04 t x) (moving a) (moving b) (moving c) (moving d) := by
          rw [uhlenbeckPulledRm04At_apply]
          simp [moving, uhlenbeckMovingBasis_apply]
    _ = S.base.rm04 t x (vec4 (I := I) (moving a) (moving b) (moving c) (moving d)) := rfl
    _ = rm (fun i j : Fin 3 => S.ricciAt t x (vec2 (I := I) (moving i) (moving j))) a b c d := by
          have h := rm04Comp_ortho_eq_rm (I := I) S t (hdim x) moving hmovingOrth (slots4 a b c d)
          simpa [slots4, Fin.isValue, Fin.reduceEq, reduceIte] using h

omit [I.Boundaryless] [IsManifold I 2 M] [IsManifold I 3 M] in
theorem fiberRegion_pulledBTensor_eq_bTensorDown
    (hiota0 : ∀ x : M, ∀ a k : Fin 3, iota 0 x a k = if a = k then 1 else 0)
    (hgram : ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Fin 3,
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota t x a b =
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota 0 x a b)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt x))
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) (x : M) (a b c d : Fin 3) :
    uhlenbeckPullbackRmInFrame iota
        (uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
          (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a)))
        t x a b c d =
      bTensorDown (fun a' b' c' d' => pulledRmComp S basisAt iota t x a' b' c' d') a b c d := by
  let moving : Module.Basis (Fin 3) Real (TangentSpace I x) :=
    uhlenbeckMovingBasis hT S basisAt iota hiota0 hgram t ht x
  let e : Fin 3 → TangentSpace I x := fun a => basisAt x a
  let P : Fin 3 → Fin 3 → ℝ := fun j i => moving.repr (basisAt x i) j
  have hP : ∀ i j : Fin 3, P j i = moving.repr (basisAt x i) j := by
    intro i j
    rfl
  have hmovingOrth : ∀ i j : Fin 3, (S.base.metric t).inner x (moving i) (moving j) = kd i j := by
    intro i j
    dsimp [moving]
    exact uhlenbeckMovingBasis_orthonormalBasisAt (I := I) (M := M) hT S basisAt iota hiota0 hgram x
      (horth0 x) ht i j
  have hginv : ∀ i j : Fin 3,
      (∑ k : Fin 3, solutionInverseMetricComponents S basisAt t x i k *
        (S.base.metric t).inner x (basisAt x k) (basisAt x j)) = kd i j := by
    intro i j
    have h := solutionInverseMetricComponents_mul_metric (I := I) (M := M) S basisAt t x i j
    simpa [metricCompInFrame, kd] using h
  have hiotaP : ∀ u v : Fin 3, (∑ i : Fin 3, iota t x u i * P v i) = kd u v := by
    intro u v
    calc
      (∑ i : Fin 3, iota t x u i * P v i)
          = moving.repr (∑ i : Fin 3, iota t x u i • basisAt x i) v := by
            rw [map_sum]
            simp [P, smul_eq_mul]
      _ = moving.repr (moving u) v := by
            congr 1
            rw [uhlenbeckMovingBasis_apply, uhlenbeckEndomorphism_apply_basis]
      _ = kd u v := by
            rw [moving.repr_self u, Finsupp.single_apply]
            simp [kd]
  let Rf : Fin 3 → Fin 3 → ℝ := fun i j => S.ricciAt t x (vec2 (I := I) (moving i) (moving j))
  have hBpull : uhlenbeckPullbackRmInFrame iota
        (uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
          (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a)))
        t x a b c d =
      Bt Rf a b c d := by
    calc
      uhlenbeckPullbackRmInFrame iota
          (uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
            (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a)))
          t x a b c d
          = ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
              iota t x a i * iota t x b j * iota t x c k * iota t x d l *
                uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
                  (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a))
                  t x i j k l := rfl
      _ = ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
              iota t x a i * iota t x b j * iota t x c k * iota t x d l *
                (∑ I0 : Fin 4 → Fin 3,
                  (∏ p : Fin 4, P (I0 p) (slots4 i j k l p)) * Bt Rf (I0 0) (I0 1) (I0 2) (I0 3)) := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
              Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
            have h := uhlenbeckBTensorInFrame_fixedFrame_pullback (I := I) (M := M) S t (hdim x)
              (fun a => basisAt x a) moving P (solutionInverseMetricComponents S basisAt)
              hP hmovingOrth hginv i j k l
            have hval : uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
                  (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a))
                  t x i j k l =
                (∑ I0 : Fin 4 → Fin 3,
                  (∏ p : Fin 4, P (I0 p) (slots4 i j k l p)) * Bt Rf (I0 0) (I0 1) (I0 2) (I0 3)) := by
              calc
                uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
                    (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a))
                    t x i j k l
                    = uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
                        (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a _ => e a))
                        t x i j k l := by
                      unfold uhlenbeckBTensorInFrame
                      refine Finset.sum_congr rfl fun e0 _ => Finset.sum_congr rfl fun g0 _ =>
                        Finset.sum_congr rfl fun f0 _ => Finset.sum_congr rfl fun r0 _ => ?_
                      simp [solutionRm04CompInFrame, rm04Comp, e]
                _ = (∑ I0 : Fin 4 → Fin 3,
                      (∏ p : Fin 4, P (I0 p) (slots4 i j k l p)) * Bt Rf (I0 0) (I0 1) (I0 2) (I0 3)) := by
                      simpa [Rf] using h
            rw [hval]
      _ = ∑ I0 : Fin 4 → Fin 3,
              Bt Rf (I0 0) (I0 1) (I0 2) (I0 3) *
                (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
                  iota t x a i * iota t x b j * iota t x c k * iota t x d l *
                    (∏ p : Fin 4, P (I0 p) (slots4 i j k l p))) := by
            have hstep1 : (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
                  iota t x a i * iota t x b j * iota t x c k * iota t x d l *
                    (∑ I0 : Fin 4 → Fin 3,
                      (∏ p : Fin 4, P (I0 p) (slots4 i j k l p)) * Bt Rf (I0 0) (I0 1) (I0 2) (I0 3))) =
                ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3, ∑ I0 : Fin 4 → Fin 3,
                  iota t x a i * iota t x b j * iota t x c k * iota t x d l *
                    (∏ p : Fin 4, P (I0 p) (slots4 i j k l p)) * Bt Rf (I0 0) (I0 1) (I0 2) (I0 3) := by
              refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
                Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun I0 _ => ?_
              ring
            have hstep2 : (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3, ∑ I0 : Fin 4 → Fin 3,
                  iota t x a i * iota t x b j * iota t x c k * iota t x d l *
                    (∏ p : Fin 4, P (I0 p) (slots4 i j k l p)) * Bt Rf (I0 0) (I0 1) (I0 2) (I0 3)) =
                ∑ I0 : Fin 4 → Fin 3, ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
                  iota t x a i * iota t x b j * iota t x c k * iota t x d l *
                    (∏ p : Fin 4, P (I0 p) (slots4 i j k l p)) * Bt Rf (I0 0) (I0 1) (I0 2) (I0 3) := by
              exact fiberRegion_sum5_swap (fun i j k l I0 =>
                iota t x a i * iota t x b j * iota t x c k * iota t x d l *
                  (∏ p : Fin 4, P (I0 p) (slots4 i j k l p)) * Bt Rf (I0 0) (I0 1) (I0 2) (I0 3))
            have hstep3 : (∑ I0 : Fin 4 → Fin 3, ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
                  iota t x a i * iota t x b j * iota t x c k * iota t x d l *
                    (∏ p : Fin 4, P (I0 p) (slots4 i j k l p)) * Bt Rf (I0 0) (I0 1) (I0 2) (I0 3)) =
                ∑ I0 : Fin 4 → Fin 3,
                  Bt Rf (I0 0) (I0 1) (I0 2) (I0 3) *
                    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
                      iota t x a i * iota t x b j * iota t x c k * iota t x d l *
                        (∏ p : Fin 4, P (I0 p) (slots4 i j k l p))) := by
              refine Finset.sum_congr rfl fun I0 _ => ?_
              rw [show (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
                    iota t x a i * iota t x b j * iota t x c k * iota t x d l *
                      (∏ p : Fin 4, P (I0 p) (slots4 i j k l p)) * Bt Rf (I0 0) (I0 1) (I0 2) (I0 3)) =
                  Bt Rf (I0 0) (I0 1) (I0 2) (I0 3) *
                    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
                      iota t x a i * iota t x b j * iota t x c k * iota t x d l *
                        (∏ p : Fin 4, P (I0 p) (slots4 i j k l p))) by
                calc
                  (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
                      iota t x a i * iota t x b j * iota t x c k * iota t x d l *
                        (∏ p : Fin 4, P (I0 p) (slots4 i j k l p)) * Bt Rf (I0 0) (I0 1) (I0 2) (I0 3))
                      = Bt Rf (I0 0) (I0 1) (I0 2) (I0 3) *
                          (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
                            iota t x a i * iota t x b j * iota t x c k * iota t x d l *
                              (∏ p : Fin 4, P (I0 p) (slots4 i j k l p))) := by
                        simp only [Finset.mul_sum]
                        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
                          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
                        ring]
            exact (hstep1.trans hstep2).trans hstep3
      _ = ∑ I0 : Fin 4 → Fin 3,
              Bt Rf (I0 0) (I0 1) (I0 2) (I0 3) *
                ((∑ i : Fin 3, iota t x a i * P (I0 0) i) *
                  (∑ j : Fin 3, iota t x b j * P (I0 1) j) *
                  (∑ k : Fin 3, iota t x c k * P (I0 2) k) *
                  (∑ l : Fin 3, iota t x d l * P (I0 3) l)) := by
            refine Finset.sum_congr rfl fun I0 _ => ?_
            rw [show (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
                  iota t x a i * iota t x b j * iota t x c k * iota t x d l *
                    (∏ p : Fin 4, P (I0 p) (slots4 i j k l p))) =
                (∑ i : Fin 3, iota t x a i * P (I0 0) i) *
                  (∑ j : Fin 3, iota t x b j * P (I0 1) j) *
                  (∑ k : Fin 3, iota t x c k * P (I0 2) k) *
                  (∑ l : Fin 3, iota t x d l * P (I0 3) l) by
              simp only [Fin.prod_univ_four, slots4, Fin.isValue, Fin.reduceEq, reduceIte]
              rw [show (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
                    iota t x a i * iota t x b j * iota t x c k * iota t x d l *
                      (P (I0 0) i * P (I0 1) j * P (I0 2) k * P (I0 3) l)) =
                  (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
                    (iota t x a i * P (I0 0) i) * (iota t x b j * P (I0 1) j) *
                      (iota t x c k * P (I0 2) k) * (iota t x d l * P (I0 3) l)) by
                refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
                  Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
                ring]
              exact fiberRegion_sum4_factor (fun i => iota t x a i * P (I0 0) i)
                (fun j => iota t x b j * P (I0 1) j)
                (fun k => iota t x c k * P (I0 2) k)
                (fun l => iota t x d l * P (I0 3) l)]
      _ = ∑ I0 : Fin 4 → Fin 3,
              Bt Rf (I0 0) (I0 1) (I0 2) (I0 3) *
                (kd a (I0 0) * kd b (I0 1) * kd c (I0 2) * kd d (I0 3)) := by
            refine Finset.sum_congr rfl fun I0 _ => ?_
            rw [hiotaP a (I0 0), hiotaP b (I0 1), hiotaP c (I0 2), hiotaP d (I0 3)]
      _ = Bt Rf a b c d := by
            rw [Finset.sum_eq_single (slots4 a b c d)]
            · simp [slots4, kd]
            · intro I0 _ hI0
              have hne : ∃ p : Fin 4, I0 p ≠ slots4 a b c d p := by
                by_contra h
                apply hI0
                funext p
                by_contra hne
                exact h ⟨p, hne⟩
              rcases hne with ⟨p, hp⟩
              have hzero : kd (slots4 a b c d p) (I0 p) = 0 := by
                rw [kd, if_neg]
                exact hp.symm
              calc
                Bt Rf (I0 0) (I0 1) (I0 2) (I0 3) *
                    (kd a (I0 0) * kd b (I0 1) * kd c (I0 2) * kd d (I0 3))
                    = Bt Rf (I0 0) (I0 1) (I0 2) (I0 3) *
                        (∏ q : Fin 4, kd (slots4 a b c d q) (I0 q)) := by
                      simp [Fin.prod_univ_four, slots4, Fin.isValue, Fin.reduceEq, reduceIte]
                _ = Bt Rf (I0 0) (I0 1) (I0 2) (I0 3) * 0 := by
                      rw [Finset.prod_eq_zero (f := fun q : Fin 4 => kd (slots4 a b c d q) (I0 q)) (by simp) hzero]
                _ = 0 := by ring
            · intro h
              exact absurd (Finset.mem_univ (slots4 a b c d)) h
  calc
    uhlenbeckPullbackRmInFrame iota
        (uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
          (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a)))
        t x a b c d
        = Bt Rf a b c d := hBpull
    _ = bTensorDown (fun a' b' c' d' => pulledRmComp S basisAt iota t x a' b' c' d') a b c d := by
          have hrm : ∀ u v w z : Fin 3,
              pulledRmComp S basisAt iota t x u v w z =
                rm Rf u v w z := by
            intro u v w z
            have h := fiberRegion_pulledRmComp_eq_rm (I := I) (M := M) hT S basisAt iota hiota0 hgram
              hdim horth0 ht x u v w z
            simpa [Rf, moving] using h
          unfold Bt bTensorDown
          refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ => ?_
          change rm Rf a e b f * rm Rf c e d f =
            pulledRmComp S basisAt iota t x a e b f * pulledRmComp S basisAt iota t x c e d f
          rw [hrm a e b f, hrm c e d f]

omit [I.Boundaryless] [IsManifold I 2 M] [IsManifold I 3 M] in
theorem fiberRegion_reaction_eq_reactionState
    (hiota0 : ∀ x : M, ∀ a k : Fin 3, iota 0 x a k = if a = k then 1 else 0)
    (hgram : ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Fin 3,
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota t x a b =
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota 0 x a b)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt x))
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) (x : M) :
    uhlenbeckCurvatureOperatorReaction
        (fun t' x' a b c d => uhlenbeckPullbackRmInFrame iota
          (uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
            (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a)))
          t' x' a b c d)
        t x =
      uhlenbeckCurvatureOperatorReactionState
        (uhlenbeckCurvatureOperatorMatrix (pulledRmComp S basisAt iota) t x) := by
  let moving : Module.Basis (Fin 3) Real (TangentSpace I x) :=
    uhlenbeckMovingBasis hT S basisAt iota hiota0 hgram t ht x
  let Rf : Fin 3 → Fin 3 → ℝ := fun i j => S.ricciAt t x (vec2 (I := I) (moving i) (moving j))
  have hR : ∀ i j : Fin 3, Rf i j = Rf j i := by
    intro i j
    unfold Rf
    exact ricciAt_symm (I := I) (M := M) S t x (moving i) (moving j)
  have hrm : ∀ a b c d : Fin 3,
      pulledRmComp S basisAt iota t x a b c d = rm Rf a b c d := by
    intro a b c d
    have h := fiberRegion_pulledRmComp_eq_rm (I := I) (M := M) hT S basisAt iota hiota0 hgram
      hdim horth0 ht x a b c d
    simpa [Rf, moving] using h
  have hB : ∀ a b c d : Fin 3,
      uhlenbeckPullbackRmInFrame iota
          (uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
            (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a)))
          t x a b c d =
        bTensorDown (fun a' b' c' d' => pulledRmComp S basisAt iota t x a' b' c' d') a b c d := by
    intro a b c d
    exact fiberRegion_pulledBTensor_eq_bTensorDown (I := I) (M := M) hT S basisAt iota hiota0 hgram
      hdim horth0 ht x a b c d
  exact uhlenbeckReaction_eq_reactionState_at (pulledRm := pulledRmComp S basisAt iota)
    (B := fun t' x' a b c d => uhlenbeckPullbackRmInFrame iota
      (uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
        (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a)))
      t' x' a b c d)
    t x Rf hR hrm hB

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [IsManifold I 1 M]
  [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
lemma fiberRegion_continuousMultilinearMap_update_sum
    {ι : Type*} [Fintype ι] {x : M}
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ)
    (m : Fin 4 → TangentSpace I x) (i : Fin 4)
    (c : ι → ℝ) (v : ι → TangentSpace I x) :
    f (Function.update m i (∑ p : ι, c p • v p)) =
      ∑ p : ι, c p * f (Function.update m i (v p)) := by
  classical
  have hsum : (∑ p : ι, c p • v p) = ∑ p ∈ Finset.univ, c p • v p := by simp
  have hsum2 : (∑ p : ι, c p * f (Function.update m i (v p))) =
      ∑ p ∈ Finset.univ, c p * f (Function.update m i (v p)) := by
    simp
  rw [hsum, hsum2]
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      rw [← zero_smul ℝ (0 : TangentSpace I x)]
      rw [ContinuousMultilinearMap.map_update_smul f m i (0 : ℝ) (0 : TangentSpace I x)]
      simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      rw [ContinuousMultilinearMap.map_update_add f m i (c a • v a) (∑ p ∈ s, c p • v p)]
      rw [ContinuousMultilinearMap.map_update_smul f m i (c a) (v a)]
      rw [ih]
      simp [Finset.sum_insert ha, smul_eq_mul]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
lemma fiberRegion_pulledTensor_apply_basis
    {x : M} (Q : Tensor04At (I := I) (M := M) x)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (iota : MatrixComp M (Fin 3)) (t : ℝ) (a b c d : Fin 3) :
    tensor04StdAt (I := I) (M := M)
        (Q.compContinuousLinearMap (fun _ : Fin 4 => uhlenbeckEndomorphismAt (basisAt x) iota t))
        (basisAt x a) (basisAt x b) (basisAt x c) (basisAt x d) =
      uhlenbeckPullbackRmInFrame iota
        (fun _s x a b c d => tensor04StdAt (I := I) (M := M) Q
          (basisAt x a) (basisAt x b) (basisAt x c) (basisAt x d))
        t x a b c d := by
  classical
  change (Q : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ)
      (fun i : Fin 4 =>
        uhlenbeckEndomorphismAt (basisAt x) iota t
          (vec4 (basisAt x a) (basisAt x b) (basisAt x c) (basisAt x d) i)) =
    uhlenbeckPullbackRmInFrame iota
      (fun s x a b c d => tensor04StdAt (I := I) (M := M) Q
        (basisAt x a) (basisAt x b) (basisAt x c) (basisAt x d))
      t x a b c d
  simp only [uhlenbeckPullbackRmInFrame, tensor04StdAt_apply]
  let g : Fin 4 → TangentSpace I x := fun _ => 0
  have harg : (fun i : Fin 4 =>
      uhlenbeckEndomorphismAt (basisAt x) iota t
        (vec4 (basisAt x a) (basisAt x b) (basisAt x c) (basisAt x d) i)) =
      Function.update (Function.update (Function.update (Function.update g 3
        (∑ l : Fin 3, iota t x d l • basisAt x l)) 2 (∑ k : Fin 3, iota t x c k • basisAt x k))
        1 (∑ j : Fin 3, iota t x b j • basisAt x j)) 0 (∑ i : Fin 3, iota t x a i • basisAt x i) := by
    funext i
    fin_cases i <;> simp [g, vec4, uhlenbeckEndomorphism_apply_basis]
  rw [harg]
  let m0 : Fin 4 → TangentSpace I x :=
    Function.update (Function.update (Function.update g 3
      (∑ l : Fin 3, iota t x d l • basisAt x l)) 2 (∑ k : Fin 3, iota t x c k • basisAt x k))
      1 (∑ j : Fin 3, iota t x b j • basisAt x j)
  have h0 : (Q : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ)
      (Function.update m0 0 (∑ p : Fin 3, iota t x a p • basisAt x p)) =
      ∑ p : Fin 3, iota t x a p * (Q : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ)
        (Function.update m0 0 (basisAt x p)) := by
    have h := fiberRegion_continuousMultilinearMap_update_sum (f := Q) m0 (0 : Fin 4)
      (fun p : Fin 3 => iota t x a p) (fun p : Fin 3 => basisAt x p)
    simpa [smul_eq_mul] using h
  rw [h0]
  have h1 : ∀ p : Fin 3,
      (Q : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ)
        (Function.update m0 0 (basisAt x p)) =
      ∑ j : Fin 3, iota t x b j * (Q : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ)
        (Function.update (Function.update m0 0 (basisAt x p)) 1 (basisAt x j)) := by
    intro p
    have h := fiberRegion_continuousMultilinearMap_update_sum (f := Q)
      (Function.update m0 0 (basisAt x p)) (1 : Fin 4)
      (fun j : Fin 3 => iota t x b j) (fun j : Fin 3 => basisAt x j)
    have hself : (Function.update (Function.update m0 0 (basisAt x p)) 1
        (∑ j : Fin 3, iota t x b j • basisAt x j)) = Function.update m0 0 (basisAt x p) := by
      funext n
      by_cases hn : n = 1
      · subst hn
        simp [m0]
      · simp [hn]
    simpa [hself, smul_eq_mul] using h
  have h2 : ∀ p q : Fin 3,
      (Q : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ)
        (Function.update (Function.update m0 0 (basisAt x p)) 1 (basisAt x q)) =
      ∑ k : Fin 3, iota t x c k * (Q : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ)
        (Function.update (Function.update (Function.update m0 0 (basisAt x p)) 1 (basisAt x q)) 2
          (basisAt x k)) := by
    intro p q
    have h := fiberRegion_continuousMultilinearMap_update_sum (f := Q)
      (Function.update (Function.update m0 0 (basisAt x p)) 1 (basisAt x q)) (2 : Fin 4)
      (fun k : Fin 3 => iota t x c k) (fun k : Fin 3 => basisAt x k)
    have hself : (Function.update (Function.update (Function.update m0 0 (basisAt x p)) 1 (basisAt x q)) 2
        (∑ k : Fin 3, iota t x c k • basisAt x k)) =
        Function.update (Function.update m0 0 (basisAt x p)) 1 (basisAt x q) := by
      funext n
      by_cases hn : n = 2
      · subst hn
        simp [m0]
      · simp [hn]
    simpa [hself, smul_eq_mul] using h
  have h3 : ∀ p q r : Fin 3,
      (Q : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ)
        (Function.update (Function.update (Function.update m0 0 (basisAt x p)) 1
          (basisAt x q)) 2 (basisAt x r)) =
      ∑ l : Fin 3, iota t x d l * (Q : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ)
        (Function.update (Function.update (Function.update (Function.update m0 0 (basisAt x p)) 1
          (basisAt x q)) 2 (basisAt x r)) 3 (basisAt x l)) := by
    intro p q r
    have h := fiberRegion_continuousMultilinearMap_update_sum (f := Q)
      (Function.update (Function.update (Function.update m0 0 (basisAt x p)) 1
        (basisAt x q)) 2 (basisAt x r)) (3 : Fin 4)
      (fun l : Fin 3 => iota t x d l) (fun l : Fin 3 => basisAt x l)
    have hself : (Function.update (Function.update (Function.update (Function.update m0 0 (basisAt x p)) 1
          (basisAt x q)) 2 (basisAt x r)) 3
        (∑ l : Fin 3, iota t x d l • basisAt x l)) =
        Function.update (Function.update (Function.update m0 0 (basisAt x p)) 1 (basisAt x q)) 2 (basisAt x r) := by
      funext n
      by_cases hn : n = 3
      · subst hn
        simp [m0]
      · simp [hn]
    simpa [hself, smul_eq_mul] using h
  have hbase : ∀ p q r l : Fin 3,
      (Q : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ)
        (Function.update (Function.update (Function.update (Function.update m0 0
          (basisAt x p)) 1 (basisAt x q)) 2 (basisAt x r)) 3 (basisAt x l)) =
      (Q : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ)
        (vec4 (basisAt x p) (basisAt x q) (basisAt x r) (basisAt x l)) := by
    intro p q r l
    congr 1
    funext n
    fin_cases n <;> simp [m0, vec4]
  calc
    ∑ p : Fin 3, iota t x a p * (Q : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ)
        (Function.update m0 0 (basisAt x p))
        = ∑ p : Fin 3, iota t x a p * (∑ j : Fin 3, iota t x b j *
            (Q : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ)
              (Function.update (Function.update m0 0 (basisAt x p)) 1 (basisAt x j))) := by
          refine Finset.sum_congr rfl ?_
          intro p hp
          rw [h1 p]
    _ = ∑ p : Fin 3, iota t x a p * (∑ j : Fin 3, iota t x b j * (∑ k : Fin 3, iota t x c k *
            (Q : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ)
              (Function.update (Function.update (Function.update m0 0 (basisAt x p)) 1
                (basisAt x j)) 2 (basisAt x k)))) := by
          refine Finset.sum_congr rfl ?_
          intro p hp
          apply congrArg
          refine Finset.sum_congr rfl ?_
          intro j hj
          rw [h2 p j]
    _ = ∑ p : Fin 3, iota t x a p * (∑ j : Fin 3, iota t x b j * (∑ k : Fin 3, iota t x c k * (∑ l : Fin 3,
            iota t x d l * (Q : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ)
              (Function.update (Function.update (Function.update
                (Function.update m0 0 (basisAt x p)) 1 (basisAt x j)) 2 (basisAt x k)) 3 (basisAt x l))))) := by
          refine Finset.sum_congr rfl ?_
          intro p hp
          apply congrArg
          refine Finset.sum_congr rfl ?_
          intro j hj
          apply congrArg
          refine Finset.sum_congr rfl ?_
          intro k hk
          rw [h3 p j k]
    _ = ∑ p : Fin 3, iota t x a p * (∑ j : Fin 3, iota t x b j * (∑ k : Fin 3, iota t x c k * (∑ l : Fin 3,
            iota t x d l * (Q : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ)
              (vec4 (basisAt x p) (basisAt x j) (basisAt x k) (basisAt x l))))) := by
          refine Finset.sum_congr rfl ?_
          intro p hp
          apply congrArg
          refine Finset.sum_congr rfl ?_
          intro j hj
          apply congrArg
          refine Finset.sum_congr rfl ?_
          intro k hk
          apply congrArg
          refine Finset.sum_congr rfl ?_
          intro l hl
          rw [hbase p j k l]
    _ = ∑ p : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
          iota t x a p * iota t x b j * iota t x c k * iota t x d l *
            (Q : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ)
              (vec4 (basisAt x p) (basisAt x j) (basisAt x k) (basisAt x l)) := by
          simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

theorem fiberRegionHeatReactionOn
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn (I := I) S)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt x))
    (iota : MatrixComp M (Fin 3))
    (hiota0 : ∀ x : M, ∀ a k : Fin 3, iota 0 x a k = if a = k then 1 else 0)
    (hgram : ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Fin 3,
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota t x a b =
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota 0 x a b)
    (hiotaCont : ∀ x : M, ContinuousOn (fun t : ℝ => iota t x) (Set.Icc 0 T))
    (hiotaODE : BundleIsomorphismODEInFrameOn (D := RealTimeInterval.closed 0 T hT.le) iota
      (solutionRicciOneUpInFrame (I := I) S (solutionInverseMetricComponents S basisAt)
        (fun a x => basisAt x a))) :
    (by
      letI : ∀ x : M, NormedAddCommGroup (Tensor04At (I := I) (M := M) x) :=
        fun x => @InnerProductSpace.Core.toNormedAddCommGroup ℝ (Tensor04At (I := I) (M := M) x)
          inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) (S.base.metric 0) x 4).toCore
      letI : ∀ x : M, InnerProductSpace ℝ (Tensor04At (I := I) (M := M) x) :=
        fun x => @InnerProductSpace.ofCore ℝ (Tensor04At (I := I) (M := M) x)
          inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) (S.base.metric 0) x 4).toCore.toCore
      letI : ∀ x : M, CompleteSpace (Tensor04At (I := I) (M := M) x) :=
        fun x => inferInstance
      exact IsBundleHeatReactionOn
        (V := fun x : M => Tensor04At (I := I) (M := M) x)
        (fiberRegionFlat (I := I) (M := M) S basisAt iota)
        (RealTimeInterval.closed 0 T hT.le) (flowG (I := I) S)
        (fun _ => fiberRegionSource hT (I := I) (M := M) S basisAt)
        (uhlenbeckPulledRm04At S basisAt iota)) := by
  classical
  letI : ∀ x : M, NormedAddCommGroup (Tensor04At (I := I) (M := M) x) :=
    fun x => @InnerProductSpace.Core.toNormedAddCommGroup ℝ (Tensor04At (I := I) (M := M) x)
      inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) (S.base.metric 0) x 4).toCore
  letI : ∀ x : M, InnerProductSpace ℝ (Tensor04At (I := I) (M := M) x) :=
    fun x => @InnerProductSpace.ofCore ℝ (Tensor04At (I := I) (M := M) x)
      inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) (S.base.metric 0) x 4).toCore.toCore
  letI : ∀ x : M, CompleteSpace (Tensor04At (I := I) (M := M) x) :=
    fun x => inferInstance
  classical
  let D : RealTimeInterval := RealTimeInterval.closed 0 T hT.le
  let u : Real → (x : M) → Tensor04At (I := I) (M := M) x := uhlenbeckPulledRm04At S basisAt iota
  let A : Real → M → EuclideanSpace ℝ (Fin 3 × Fin 3) :=
    fun t x => uhlenbeckCurvatureOperatorMatrix (pulledRmComp S basisAt iota) t x
  let w (x : M) (ν : Tensor04At (I := I) (M := M) x) : EuclideanSpace ℝ (Fin 3 × Fin 3) :=
    regionSupportVector (I := I) (S.base.metric 0) basisAt x ν
  have hAlg : ∀ (t : ℝ) (x : M), u t x ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x := by
    intro t x
    exact uhlenbeckPulledRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) (M := M) S basisAt iota t x
  have hscalar_eq : ∀ (s : ℝ) (x : M) (ν : Tensor04At (I := I) (M := M) x),
      inner ℝ (u s x) ν = 4 * inner ℝ (A s x) (w x ν) := by
    intro s x ν
    rw [tensor04_fiberInner_eq (I := I) (S.base.metric 0) x (u s x) ν]
    have hmain := pulledScalarization_eq (I := I) (S.base.metric 0) S basisAt iota s x (horth0 x)
      (hAlg s x) ν
    simpa [A, w, u] using hmain
  let roughLapRm04 : FourComp M (Fin 3) := fun t x a b c d =>
    metricTraceFirstTwo0SAt (I := I) (S.base.metric t) (nablaKRm04Field (I := I) S t 2 x)
      (vec4 (I := I) (basisAt x a) (basisAt x b) (basisAt x c) (basisAt x d))
  let Borig : FourComp M (Fin 3) :=
    uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
      (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a))
  have hrm := fiberRegion_solutionRm04FixedFrameEvolution (T := T) hT S hS hdim basisAt
  let roughLapD : FourComp M (Fin 3) := fun t x a b c d =>
    ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
      iota t x a i * iota t x b j * iota t x c k * iota t x d l * roughLapRm04 t x i j k l
  let Bpull : FourComp M (Fin 3) := fun t x a b c d =>
    ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
      iota t x a i * iota t x b j * iota t x c k * iota t x d l * Borig t x i j k l
  have hlap : UhlenbeckLaplacianPullbackComponents iota roughLapRm04 roughLapD := by
    intro t x a b c d
    rfl
  have hB : UhlenbeckPullbackBComponents iota Borig Bpull := by
    intro t x a b c d
    rfl
  have hU : UhlenbeckCurvatureEvolutionInFrameOn (D := D)
      (pulledRmComp S basisAt iota) roughLapD Bpull := by
    exact uhlenbeckCurvatureEvolutionInFrameOn_of_ricciFlow (D := D) iota
      (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a))
      (pulledRmComp S basisAt iota) roughLapRm04 roughLapD Borig Bpull
      (solutionRicciOneUpInFrame (I := I) S (solutionInverseMetricComponents S basisAt)
        (fun a x => basisAt x a))
      hiotaODE (pulledRmComp_pullback (I := I) (M := M) hT S basisAt iota) hlap hB hrm
  have hU_deriv : ∀ (t : ℝ) (ht : t ∈ D.regular) (x : M) (a b c d : Fin 3),
      HasDerivAt (fun s : ℝ => pulledRmComp S basisAt iota s x a b c d)
        (uhlenbeckCurvatureEvolutionRHSInFrame roughLapD Bpull t x a b c d) t := by
    intro t ht x a b c d
    have h := hU ⟨t, ht⟩ x a b c d
    exact h.hasDerivAt (D.regular_mem_nhds ht)
  refine ⟨?scalarJointCont, ?scalarSliceSmooth, ?equation⟩
  · intro ν t ht x hflat
    have hAcomp : ∀ ij : Fin 3 × Fin 3,
        ContinuousOn (fun s : ℝ => (A s x).ofLp ij) (Set.Icc 0 T) := by
      intro ij
      have h := fiberRegion_pulledComponent_continuousOn_time (I := I) (M := M) hT S hS basisAt iota
        hiotaCont x (bivectorIndex3 ij.1).1 (bivectorIndex3 ij.1).2 (bivectorIndex3 ij.2).2 (bivectorIndex3 ij.2).1
      simpa [A, uhlenbeckCurvatureOperatorMatrix] using h
    have hsum : ContinuousOn (fun s : ℝ => ∑ ij : Fin 3 × Fin 3,
        (A s x).ofLp ij * (w x (ν x)).ofLp ij) (Set.Icc 0 T) := by
      refine continuousOn_finset_sum Finset.univ ?_
      intro ij _
      exact (hAcomp ij).mul continuousOn_const
    have hinner_cont : ContinuousOn (fun s : ℝ => inner ℝ (A s x) (w x (ν x))) (Set.Icc 0 T) := by
      have hEq : (fun s : ℝ => inner ℝ (A s x) (w x (ν x))) =
          fun s : ℝ => ∑ ij : Fin 3 × Fin 3, (A s x).ofLp ij * (w x (ν x)).ofLp ij := by
        funext s
        rw [PiLp.inner_apply]
        simp [inner, mul_comm]
      simpa [hEq] using hsum
    have hmain : ContinuousOn (fun s : ℝ => bundleInnerScalarization u ν s x) (Set.Icc 0 T) := by
      have hfun : (fun s : ℝ => bundleInnerScalarization u ν s x) =
          fun s : ℝ => 4 * inner ℝ (A s x) (w x (ν x)) := by
        funext s
        unfold bundleInnerScalarization
        rw [hscalar_eq s x (ν x)]
      rw [hfun]
      exact hinner_cont.const_mul 4
    simpa [D] using hmain.continuousWithinAt ht
  · intro ν t ht x hflat
    rcases hflat with ⟨η, nablaη, nabla2η, basis, hOrth, heqν, hη, h2η, hflat1, hflat2⟩
    have hlocal : (fun y : M => bundleInnerScalarization u ν t y) =ᶠ[𝓝 x]
        fun y : M => inner0S (I := I) (S.base.metric t) y 4 (S.base.rm04 t y) (η y) := by
      filter_upwards [heqν] with y hy
      unfold bundleInnerScalarization
      rw [tensor04_fiberInner_eq (I := I) (S.base.metric 0) y (u t y) (ν y)]
      have hiso := fiberInner_compUhlenbeck_isometry_general (I := I) (M := M) hT S basisAt iota hiota0 hgram
        horth0 ht y (S.base.rm04 t y) (η y)
      have hu : u t y = (S.base.rm04 t y).compContinuousLinearMap
          (fun _ : Fin 4 => uhlenbeckEndomorphismAt (basisAt y) iota t) := rfl
      rw [hu, hy]
      simpa [uhlenbeckPullbackTensorAt] using hiso
    have hsm : ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun y : M => inner0S (I := I) (S.base.metric t) y 4 (S.base.rm04 t y) (η y)) x :=
      (inner0S_contMDiff (I := I) (S.base.metric t) (S.base.rm04 t) η).contMDiffAt
    exact hsm.congr_of_eventuallyEq hlocal
  · intro ν t ht x hflat
    rcases hflat with ⟨η, nablaη, nabla2η, basis, hOrth, heqν, hη, h2η, hflat1, hflat2⟩
    let wv : EuclideanSpace ℝ (Fin 3 × Fin 3) := w x (ν x)
    have hscalar_fun : (fun s : ℝ => bundleInnerScalarization u ν s x) =
        fun s : ℝ => 4 * inner ℝ (A s x) wv := by
      funext s
      unfold bundleInnerScalarization
      rw [tensor04_fiberInner_eq (I := I) (S.base.metric 0) x (u s x) (ν x)]
      have hmain := pulledScalarization_eq (I := I) (S.base.metric 0) S basisAt iota s x (horth0 x)
        (hAlg s x) (ν x)
      simpa [A, w, wv, u] using hmain
    have hAderiv_comp : ∀ ij : Fin 3 × Fin 3,
        HasDerivAt (fun s : ℝ => (A s x).ofLp ij)
          ((uhlenbeckCurvatureOperatorMatrix roughLapD t x).ofLp ij +
            (uhlenbeckCurvatureOperatorReaction Bpull t x).ofLp ij) t := by
      intro ij
      let a : Fin 3 := (bivectorIndex3 ij.1).1
      let b : Fin 3 := (bivectorIndex3 ij.1).2
      let c : Fin 3 := (bivectorIndex3 ij.2).2
      let d : Fin 3 := (bivectorIndex3 ij.2).1
      have hd := hU_deriv t ht x a b c d
      have hA : (fun s : ℝ => (A s x).ofLp ij) = fun s : ℝ => pulledRmComp S basisAt iota s x a b c d := by
        funext s
        simp [A, uhlenbeckCurvatureOperatorMatrix, a, b, c, d]
      have hrhs : uhlenbeckCurvatureEvolutionRHSInFrame roughLapD Bpull t x a b c d =
          (uhlenbeckCurvatureOperatorMatrix roughLapD t x).ofLp ij +
            (uhlenbeckCurvatureOperatorReaction Bpull t x).ofLp ij := by
        simp [uhlenbeckCurvatureEvolutionRHSInFrame, uhlenbeckCurvatureOperatorMatrix,
          uhlenbeckCurvatureOperatorReaction, a, b, c, d]
        ring
      rw [hA]
      exact hd.congr_deriv hrhs
    have hscalar_deriv : HasDerivAt (fun s : ℝ => 4 * inner ℝ (A s x) wv)
        (4 * inner ℝ (uhlenbeckCurvatureOperatorMatrix roughLapD t x +
            uhlenbeckCurvatureOperatorReaction Bpull t x) wv) t := by
      have hinner : HasDerivAt (fun s : ℝ => inner ℝ (A s x) wv)
          (inner ℝ (uhlenbeckCurvatureOperatorMatrix roughLapD t x +
            uhlenbeckCurvatureOperatorReaction Bpull t x) wv) t := by
        have hsum : HasDerivAt (fun s : ℝ => ∑ ij : Fin 3 × Fin 3, (A s x).ofLp ij * wv.ofLp ij)
            (∑ ij : Fin 3 × Fin 3,
              ((uhlenbeckCurvatureOperatorMatrix roughLapD t x).ofLp ij +
                (uhlenbeckCurvatureOperatorReaction Bpull t x).ofLp ij) * wv.ofLp ij) t := by
          have hraw : HasDerivAt (fun s : ℝ => ∑ ij ∈ (Finset.univ : Finset (Fin 3 × Fin 3)),
                (A s x).ofLp ij * wv.ofLp ij)
              (∑ ij ∈ (Finset.univ : Finset (Fin 3 × Fin 3)),
                ((uhlenbeckCurvatureOperatorMatrix roughLapD t x).ofLp ij +
                  (uhlenbeckCurvatureOperatorReaction Bpull t x).ofLp ij) * wv.ofLp ij) t := by
            exact HasDerivAt.sum (u := Finset.univ) (fun ij hij => (hAderiv_comp ij).mul_const (wv.ofLp ij))
          simpa using hraw
        have hinner_eq : (fun s : ℝ => inner ℝ (A s x) wv) =
            fun s : ℝ => ∑ ij : Fin 3 × Fin 3, (A s x).ofLp ij * wv.ofLp ij := by
          funext s
          rw [PiLp.inner_apply]
          simp [inner, mul_comm]
        have hderiv_eq : (∑ ij : Fin 3 × Fin 3,
              ((uhlenbeckCurvatureOperatorMatrix roughLapD t x).ofLp ij +
                (uhlenbeckCurvatureOperatorReaction Bpull t x).ofLp ij) * wv.ofLp ij) =
            inner ℝ (uhlenbeckCurvatureOperatorMatrix roughLapD t x +
              uhlenbeckCurvatureOperatorReaction Bpull t x) wv := by
          rw [PiLp.inner_apply]
          simp [inner, mul_comm]
        simpa [hinner_eq, hderiv_eq] using hsum
      simpa [mul_add] using hinner.const_mul 4
    have hlapAt : laplacianAt (I := I) (flowG (I := I) S) t
          (bundleInnerScalarization u ν t) x =
        4 * inner ℝ (uhlenbeckCurvatureOperatorMatrix roughLapD t x) wv := by
      have hlocal : (fun y : M => bundleInnerScalarization u ν t y) =ᶠ[𝓝 x]
          fun y : M => inner0S (I := I) (S.base.metric t) y 4 (S.base.rm04 t y) (η y) := by
        filter_upwards [heqν] with y hy
        unfold bundleInnerScalarization
        rw [tensor04_fiberInner_eq (I := I) (S.base.metric 0) y (u t y) (ν y)]
        have hiso := fiberInner_compUhlenbeck_isometry_general (I := I) (M := M) hT S basisAt iota hiota0 hgram
          horth0 (D.regular_subset ht) y (S.base.rm04 t y) (η y)
        have hu : u t y = (S.base.rm04 t y).compContinuousLinearMap
            (fun _ : Fin 4 => uhlenbeckEndomorphismAt (basisAt y) iota t) := rfl
        rw [hu, hy]
        simpa [uhlenbeckPullbackTensorAt] using hiso
      have hsm : ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
          (fun y : M => inner0S (I := I) (S.base.metric t) y 4 (S.base.rm04 t y) (η y)) x :=
        (inner0S_contMDiff (I := I) (S.base.metric t) (S.base.rm04 t) η).contMDiffAt
      have hsm' : ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
          (bundleInnerScalarization u ν t) x := hsm.congr_of_eventuallyEq hlocal
      have hlap0 : laplacian (I := I) ((flowG (I := I) S).connection t) ((flowG (I := I) S).metric t)
            (fun y : M => inner0S (I := I) (S.base.metric t) y 4 (S.base.rm04 t y) (η y)) x =
          inner0S (I := I) (S.base.metric t) x 4
            (metricTrace0S2TensorInBasis (I := I) basis (identityInvMetric (Idx := Fin 3))
              (nablaKRm04Field (I := I) S t 2 x)) (η x) := by
        have hA1 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4
            (S.base.connection t) (S.base.rm04 t) (nablaKRm04Field (I := I) S t 1) := by
          simpa [nablaKRm04Field_zero] using (nablaKRm04Field_realizes (I := I) S t 0)
        have hA2 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5
            (S.base.connection t) (nablaKRm04Field (I := I) S t 1) (nablaKRm04Field (I := I) S t 2) := by
          simpa using (nablaKRm04Field_realizes (I := I) S t 1)
        have hinv : MetricInverseInBasis_gen (I := I) (S.base.metric t) x basis
            (identityInvMetric (Idx := Fin 3)) := by
          exact fiberRegion_metricInverseInBasis_identity_of_orthonormal (I := I)
            (S.base.metric t) basis (by
              intro i j
              simpa [delta3] using hOrth i j)
        have hlap1 := laplacianAt_inner0S_eq_inner_roughLap_flowG_of_flat (I := I) (M := M) S
          (S.base.rm04 t) (nablaKRm04Field (I := I) S t 1) (nablaKRm04Field (I := I) S t 2)
          η nablaη nabla2η hA1 hA2 hη h2η basis (identityInvMetric (Idx := Fin 3)) hinv
          hflat1 hflat2
        simpa [laplacianAt] using hlap1
      have hlap1 : laplacian (I := I) ((flowG (I := I) S).connection t) ((flowG (I := I) S).metric t)
          (bundleInnerScalarization u ν t) x =
          inner0S (I := I) (S.base.metric t) x 4
            (metricTrace0S2TensorInBasis (I := I) basis (identityInvMetric (Idx := Fin 3))
              (nablaKRm04Field (I := I) S t 2 x)) (η x) := by
        exact laplacian_congr_of_eventuallyEq (I := I) ((flowG (I := I) S).connection t)
          ((flowG (I := I) S).metric t) hsm' hsm hlocal |>.trans hlap0
      let R : Tensor04At (I := I) (M := M) x :=
        metricTrace0S2TensorInBasis (I := I) basis (identityInvMetric (Idx := Fin 3))
          (nablaKRm04Field (I := I) S t 2 x)
      have hR : R ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
        fiberRegion_roughLapRm04_mem_algebraicCurvatureTensorSubmodule (I := I) (M := M) hT S t x basis
      have hcomp : ∀ a b c d : Fin 3,
          roughLapD t x a b c d = tensor04StdAt (I := I) (M := M)
            (uhlenbeckPullbackTensorAt basisAt iota t x R)
            (basisAt x a) (basisAt x b) (basisAt x c) (basisAt x d) := by
        intro a b c d
        calc
          roughLapD t x a b c d
              = uhlenbeckPullbackRmInFrame iota roughLapRm04 t x a b c d := rfl
          _ = uhlenbeckPullbackRmInFrame iota
                (fun s y a' b' c' d' =>
                  metricTraceFirstTwo0SAt (I := I) (S.base.metric s) (nablaKRm04Field (I := I) S s 2 y)
                    (vec4 (I := I) (basisAt y a') (basisAt y b') (basisAt y c') (basisAt y d')))
                t x a b c d := rfl
          _ = uhlenbeckPullbackRmInFrame iota
                (fun s y a' b' c' d' =>
                  tensor04StdAt (I := I) (M := M)
                    (metricTrace0S2TensorInBasis (I := I) basis (identityInvMetric (Idx := Fin 3))
                      (nablaKRm04Field (I := I) S s 2 y))
                    (basisAt y a') (basisAt y b') (basisAt y c') (basisAt y d'))
                t x a b c d := by
                apply Finset.sum_congr rfl; intro i _
                apply Finset.sum_congr rfl; intro j _
                apply Finset.sum_congr rfl; intro k _
                apply Finset.sum_congr rfl; intro l _
                simpa using (congrArg (fun z : ℝ => iota t x a i * iota t x b j * iota t x c k * iota t x d l * z)
                  (fiberRegion_roughLapRm04_component_eq (I := I) (M := M) hT S basisAt x basis hOrth i j k l))
          _ = tensor04StdAt (I := I) (M := M) (uhlenbeckPullbackTensorAt basisAt iota t x R)
                (basisAt x a) (basisAt x b) (basisAt x c) (basisAt x d) := by
                rw [show uhlenbeckPullbackRmInFrame iota
                      (fun s y a' b' c' d' =>
                        tensor04StdAt (I := I) (M := M)
                          (metricTrace0S2TensorInBasis (I := I) basis (identityInvMetric (Idx := Fin 3))
                            (nablaKRm04Field (I := I) S s 2 y))
                          (basisAt y a') (basisAt y b') (basisAt y c') (basisAt y d'))
                      t x a b c d =
                    uhlenbeckPullbackRmInFrame iota
                      (fun s y a' b' c' d' =>
                        tensor04StdAt (I := I) (M := M) R
                          (basisAt y a') (basisAt y b') (basisAt y c') (basisAt y d'))
                      t x a b c d by
                    unfold uhlenbeckPullbackRmInFrame
                    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
                      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
                    simp [R]]
                exact (fiberRegion_pulledTensor_apply_basis (I := I) (M := M) R basisAt iota t a b c d).symm
      have hRalg : uhlenbeckPullbackTensorAt basisAt iota t x R ∈
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
        fiberRegion_compU_mem_algebraicCurvatureTensorSubmodule (I := I) (M := M) basisAt iota t x R hR
      have hiso := fiberInner_compUhlenbeck_isometry_general (I := I) (M := M) hT S basisAt iota hiota0 hgram
        horth0 (D.regular_subset ht) x R (η x)
      have hνx : ν x = uhlenbeckPullbackTensorAt basisAt iota t x (η x) := by
        exact heqν.self_of_nhds
      have hscal := fiberRegion_pulledTensor_scalarization_eq (I := I) (M := M)
        basisAt (S.base.metric 0) iota t x (horth0 x) R hRalg (ν x)
      have hmat : uhlenbeckCurvatureOperatorMatrix
            (fun t' x' a b c d => tensor04StdAt (I := I) (M := M)
              (uhlenbeckPullbackTensorAt basisAt iota t' x' R)
              (basisAt x' a) (basisAt x' b) (basisAt x' c) (basisAt x' d)) t x =
          uhlenbeckCurvatureOperatorMatrix roughLapD t x := by
        unfold uhlenbeckCurvatureOperatorMatrix
        apply congrArg
        funext ij
        exact (hcomp (bivectorIndex3 ij.1).1 (bivectorIndex3 ij.1).2 (bivectorIndex3 ij.2).2 (bivectorIndex3 ij.2).1).symm
      calc
        laplacianAt (I := I) (flowG (I := I) S) t (bundleInnerScalarization u ν t) x
            = inner0S (I := I) (S.base.metric t) x 4 R (η x) := hlap1
        _ = inner0S (I := I) (S.base.metric 0) x 4 (uhlenbeckPullbackTensorAt basisAt iota t x R) (ν x) := by
              calc
                inner0S (I := I) (S.base.metric t) x 4 R (η x)
                    = inner0S (I := I) (S.base.metric 0) x 4
                        (uhlenbeckPullbackTensorAt basisAt iota t x R)
                        (uhlenbeckPullbackTensorAt basisAt iota t x (η x)) := by
                          simpa [uhlenbeckPullbackTensorAt] using hiso.symm
                _ = inner0S (I := I) (S.base.metric 0) x 4
                      (uhlenbeckPullbackTensorAt basisAt iota t x R) (ν x) := by
                      rw [hνx]
        _ = 4 * inner ℝ (uhlenbeckCurvatureOperatorMatrix
              (fun t' x' a b c d => tensor04StdAt (I := I) (M := M)
                (uhlenbeckPullbackTensorAt basisAt iota t' x' R)
                (basisAt x' a) (basisAt x' b) (basisAt x' c) (basisAt x' d)) t x)
              (regionSupportVector (I := I) (S.base.metric 0) basisAt x (ν x)) := hscal
        _ = 4 * inner ℝ (uhlenbeckCurvatureOperatorMatrix roughLapD t x) wv := by
              rw [hmat]
    have hsource : fiberRegionSource hT (I := I) (M := M) S basisAt x (u t x) (ν x) =
        4 * inner ℝ (uhlenbeckCurvatureOperatorReactionState (A t x)) wv := by
      unfold fiberRegionSource
      have hmain := regionSource_at_pulled_eq (I := I) (S.base.metric 0) S basisAt iota t x
        (hAlg t x) (ν x)
      simpa [A, w, wv, u] using hmain
    have hreaction : uhlenbeckCurvatureOperatorReaction Bpull t x =
        uhlenbeckCurvatureOperatorReactionState (A t x) := by
      simpa [A, Bpull, Borig, uhlenbeckPullbackRmInFrame] using
        (fiberRegion_reaction_eq_reactionState (I := I) (M := M) hT S basisAt iota
          hiota0 hgram hdim horth0 (D.regular_subset ht) x)
    have htarget : laplacianAt (I := I) (flowG (I := I) S) t (bundleInnerScalarization u ν t) x +
          fiberRegionSource hT (I := I) (M := M) S basisAt x (u t x) (ν x) =
        4 * inner ℝ (uhlenbeckCurvatureOperatorMatrix roughLapD t x +
          uhlenbeckCurvatureOperatorReactionState (A t x)) wv := by
      rw [hlapAt, hsource]
      simp [inner_add_left, mul_add]
    have hfun : (fun s : ℝ => bundleInnerScalarization u ν s x) =
        fun s : ℝ => 4 * inner ℝ (A s x) wv := by
      funext s
      unfold bundleInnerScalarization
      rw [hscalar_eq s x (ν x)]
    have hderiv' : HasDerivAt (fun s : ℝ => 4 * inner ℝ (A s x) wv)
        (4 * inner ℝ (uhlenbeckCurvatureOperatorMatrix roughLapD t x +
          uhlenbeckCurvatureOperatorReactionState (A t x)) wv) t := by
      simpa [hreaction] using hscalar_deriv
    simpa [u, hfun] using (hderiv'.congr_deriv htarget.symm)
end Helpers

section FlatSectionHelpers

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem inner0S_four_orthonormalBasis_sq
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) g x basis)
    (A B : Tensor04At (I := I) (M := M) x) :
    inner0S (I := I) g x 4 A B =
      ∑ I0 : Fin 4 → Fin 3,
        A (fun a => basis (I0 a)) * B (fun a => basis (I0 a)) := by
  classical
  let gInv : Fin 3 → Fin 3 → ℝ := fun i j => if i = j then 1 else 0
  have hinv : MetricInverseInBasis (I := I) g x basis gInv := by
    intro i j
    constructor
    · calc
        (∑ k : Fin 3, gInv i k * g.inner x (basis k) (basis j))
            = g.inner x (basis i) (basis j) := by
              rw [Finset.sum_eq_single i]
              · simp [gInv]
              · intro k _ hk
                have hik : i ≠ k := Ne.symm hk
                simp [gInv, hik]
              · intro hi
                exact False.elim (hi (Finset.mem_univ i))
        _ = if i = j then 1 else 0 := by
              simpa [delta3] using horth i j
    · calc
        (∑ k : Fin 3, g.inner x (basis i) (basis k) * gInv k j)
            = g.inner x (basis i) (basis j) := by
              rw [Finset.sum_eq_single j]
              · simp [gInv]
              · intro k _ hk
                have hkj : k ≠ j := Ne.symm (Ne.symm hk)
                simp [gInv, hkj]
              · intro hj
                exact False.elim (hj (Finset.mem_univ j))
        _ = if i = j then 1 else 0 := by
              simpa [delta3] using horth i j
  have hdelta : ∀ I0 J0 : Fin 4 → Fin 3,
      (∏ a : Fin 4, gInv (I0 a) (J0 a)) = if I0 = J0 then 1 else 0 := by
    intro I0 J0
    by_cases hIJ : I0 = J0
    · subst J0
      simp [gInv]
    · have hne : ∃ a : Fin 4, I0 a ≠ J0 a := by
        by_contra h
        apply hIJ
        funext a
        by_contra hne'
        exact h ⟨a, hne'⟩
      rcases hne with ⟨a, hne⟩
      have hzero : gInv (I0 a) (J0 a) = 0 := by
        simp [gInv, hne]
      rw [Finset.prod_eq_zero (Finset.mem_univ a) hzero]
      rw [if_neg hIJ]
  calc
    inner0S (I := I) g x 4 A B
        = coordInner0S (I := I) (x := x) 4 gInv A B basis := by
            exact inner0S_eq_coord (I := I) g x 4 basis gInv hinv A B
    _ = ∑ I0 : Fin 4 → Fin 3, ∑ J0 : Fin 4 → Fin 3,
          (∏ a : Fin 4, gInv (I0 a) (J0 a)) * A (fun a => basis (I0 a)) *
            B (fun a => basis (J0 a)) := by
          unfold coordInner0S
          apply Finset.sum_congr rfl
          intro I0 _
          apply Finset.sum_congr rfl
          intro J0 _
          simp
    _ = ∑ I0 : Fin 4 → Fin 3, A (fun a => basis (I0 a)) * B (fun a => basis (I0 a)) := by
          apply Finset.sum_congr rfl
          intro I0 _
          simp_rw [hdelta I0]
          rw [Finset.sum_eq_single I0]
          · simp
          · intro J0 _ hJ0
            rw [if_neg (Ne.symm hJ0)]
            ring
          · intro hJ0
            exact False.elim (hJ0 (Finset.mem_univ I0))

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem symmEuclid_conj
    (O M : Matrix (Fin 3) (Fin 3) ℝ) :
    symmEuclid (matrixToEuclid (O.transpose * M * O)) =
      O.transpose * symmEuclid (matrixToEuclid M) * O := by
  unfold symmEuclid
  simp only [euclidToMatrix_matrixToEuclid]
  have hT : (O.transpose * M * O).transpose = O.transpose * M.transpose * O := by
    simp [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  calc
    (1 / 2 : ℝ) • (O.transpose * M * O + (O.transpose * M * O).transpose)
        = (1 / 2 : ℝ) • (O.transpose * M * O + O.transpose * M.transpose * O) := by rw [hT]
    _ = (1 / 2 : ℝ) • (O.transpose * (M * O) + O.transpose * (M.transpose * O)) := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc]
    _ = (1 / 2 : ℝ) • (O.transpose * (M * O + M.transpose * O)) := by
          rw [← Matrix.mul_add]
    _ = (1 / 2 : ℝ) • (O.transpose * ((M + M.transpose) * O)) := by
          rw [Matrix.add_mul]
    _ = (1 / 2 : ℝ) • (O.transpose * (M + M.transpose) * O) := by
          rw [← Matrix.mul_assoc]
    _ = ((1 / 2 : ℝ) • (O.transpose * (M + M.transpose))) * O := by
          rw [← Matrix.smul_mul]
    _ = (O.transpose * ((1 / 2 : ℝ) • (M + M.transpose))) * O := by
          rw [← Matrix.mul_smul]

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem charpoly_conj_of_orthogonal
    {S : Matrix (Fin 3) (Fin 3) ℝ}
    {O : Matrix (Fin 3) (Fin 3) ℝ} (hO : O * O.transpose = 1) :
    (O.transpose * S * O).charpoly = S.charpoly := by
  have hmul := Matrix.charpoly_mul_comm O.transpose (S * O)
  rw [show O.transpose * (S * O) = O.transpose * S * O by simp [Matrix.mul_assoc]] at hmul
  rw [hmul]
  rw [show (S * O) * O.transpose = S * (O * O.transpose) by simp [Matrix.mul_assoc]]
  rw [hO, Matrix.mul_one]

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem eigenvalues₀_conj_of_orthogonal
    {S : Matrix (Fin 3) (Fin 3) ℝ} (hS : S.IsHermitian)
    {O : Matrix (Fin 3) (Fin 3) ℝ} (hO : O * O.transpose = 1) :
    (show (O.transpose * S * O).IsHermitian from by
      have hconj : (O.conjTranspose * S * O).IsHermitian :=
        Matrix.isHermitian_conjTranspose_mul_mul O hS
      simpa using hconj).eigenvalues₀ = hS.eigenvalues₀ := by
  exact eigenvalues₀_eq_of_charpoly_eq_real
    (show (O.transpose * S * O).IsHermitian from by
      have hconj : (O.conjTranspose * S * O).IsHermitian :=
        Matrix.isHermitian_conjTranspose_mul_mul O hS
      simpa using hconj) hS (charpoly_conj_of_orthogonal hO)

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem symmEuclid_matrixToEuclid_conj_eigenvalues₀
    (M O : Matrix (Fin 3) (Fin 3) ℝ) (hO : O * O.transpose = 1) :
    (symmEuclid_isHermitian (matrixToEuclid (O.transpose * M * O))).eigenvalues₀ =
      (symmEuclid_isHermitian (matrixToEuclid M)).eigenvalues₀ := by
  exact eigenvalues₀_eq_of_charpoly_eq_real
    (symmEuclid_isHermitian (matrixToEuclid (O.transpose * M * O)))
    (symmEuclid_isHermitian (matrixToEuclid M))
    (by
      rw [symmEuclid_conj]
      exact charpoly_conj_of_orthogonal hO)

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem hamiltonIveyConvexMatrixRegionSupportEuclid_conj
    (K τ : ℝ) (M O : Matrix (Fin 3) (Fin 3) ℝ) (hO : O * O.transpose = 1) :
    hamiltonIveyConvexMatrixRegionSupportEuclid K τ (matrixToEuclid (O.transpose * M * O)) =
      hamiltonIveyConvexMatrixRegionSupportEuclid K τ (matrixToEuclid M) := by
  unfold hamiltonIveyConvexMatrixRegionSupportEuclid
  have heig := symmEuclid_matrixToEuclid_conj_eigenvalues₀ M O hO
  simp_rw [heig]

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem symmEuclid_matrixToEuclid_smul
    (c : ℝ) (X : Matrix (Fin 3) (Fin 3) ℝ) :
    symmEuclid (matrixToEuclid (c • X)) = c • symmEuclid (matrixToEuclid X) := by
  unfold symmEuclid
  ext i j
  simp only [euclidToMatrix_matrixToEuclid, Matrix.smul_apply, Matrix.add_apply,
    Matrix.transpose_apply, smul_eq_mul]
  ring

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem eigenvalues₀_smul_of_nonneg
    {S : Matrix (Fin 3) (Fin 3) ℝ} (hS : S.IsHermitian) {c : ℝ} (hc : 0 ≤ c)
    (hcS : (c • S).IsHermitian) :
    hcS.eigenvalues₀ = c • hS.eigenvalues₀ := by
  classical
  rcases hermitian_orthogonal_diagonalization hS with ⟨O, hO, hdiag⟩
  have hOt : O.transpose * O = 1 := matrixTransposeMul_orthogonal O hO
  let D₀ : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal hS.eigenvalues₀
  have hdiag' : O.transpose * S * O = D₀ := by simpa [D₀] using hdiag
  have hSrep : S = O * D₀ * O.transpose := by
    have h1 : S = (O * O.transpose) * S * (O * O.transpose) := by
      rw [hO]
      simp
    calc
      S = (O * O.transpose) * S * (O * O.transpose) := h1
      _ = O * (O.transpose * S * O) * O.transpose := by
            simp [Matrix.mul_assoc]
      _ = O * D₀ * O.transpose := by
            rw [hdiag']
  have hdiagc : O.transpose * (c • S) * O = Matrix.diagonal (c • hS.eigenvalues₀) := by
    calc
      O.transpose * (c • S) * O
          = O.transpose * (c • (O * D₀ * O.transpose)) * O := by
              rw [show c • S = c • (O * D₀ * O.transpose) from by rw [hSrep]]
      _ = O.transpose * (O * (c • D₀) * O.transpose) * O := by
              rw [← Matrix.smul_mul, ← Matrix.mul_smul]
      _ = c • D₀ := by
            calc
              O.transpose * (O * (c • D₀) * O.transpose) * O
                  = (O.transpose * O) * (c • D₀) * (O.transpose * O) := by
                      simp [Matrix.mul_assoc]
              _ = c • D₀ := by
                      simp [hOt]
      _ = Matrix.diagonal (c • hS.eigenvalues₀) := by
            ext i j
            simp [D₀, Matrix.diagonal, smul_eq_mul]
            rfl
  have hanti : Antitone (c • hS.eigenvalues₀) := by
    intro i j hij
    change c * hS.eigenvalues₀ j ≤ c * hS.eigenvalues₀ i
    exact mul_le_mul_of_nonneg_left (hS.eigenvalues₀_antitone hij) hc
  have hdiagE : (Matrix.isHermitian_diagonal (c • hS.eigenvalues₀)).eigenvalues₀ =
      c • hS.eigenvalues₀ :=
    diagonal_eigenvalues₀_eq_of_antitone (c • hS.eigenvalues₀) hanti
  have hOcS : (O.transpose * (c • S) * O).IsHermitian := by
    have hconj' : (O.conjTranspose * (c • S) * O).IsHermitian :=
      Matrix.isHermitian_conjTranspose_mul_mul O hcS
    simpa using hconj'
  have hStep1 : hcS.eigenvalues₀ = hOcS.eigenvalues₀ :=
    (eigenvalues₀_conj_of_orthogonal (S := c • S) hcS hO).symm
  have hStep2a : hOcS.eigenvalues₀ =
      (Matrix.isHermitian_diagonal (c • hS.eigenvalues₀)).eigenvalues₀ := by
    exact eigenvalues₀_eq_of_charpoly_eq_real hOcS
      (Matrix.isHermitian_diagonal (c • hS.eigenvalues₀))
      (by rw [hdiagc])
  have hStep2 : hOcS.eigenvalues₀ = c • hS.eigenvalues₀ := hStep2a.trans hdiagE
  exact hStep1.trans hStep2

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem regionNormalDirections_conj_scale_condition
    {M O : Matrix (Fin 3) (Fin 3) ℝ} {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hO : O * O.transpose = 1)
    (hM : (symmEuclid_isHermitian (matrixToEuclid M)).eigenvalues₀ 0 < 0 ∨
      symmEuclid (matrixToEuclid M) = 0) :
    (symmEuclid_isHermitian (matrixToEuclid (ρ • (O.transpose * M * O)))).eigenvalues₀ 0 < 0 ∨
      symmEuclid (matrixToEuclid (ρ • (O.transpose * M * O))) = 0 := by
  have hSM : symmEuclid (matrixToEuclid (ρ • (O.transpose * M * O))) =
      ρ • (O.transpose * symmEuclid (matrixToEuclid M) * O) := by
    calc
      symmEuclid (matrixToEuclid (ρ • (O.transpose * M * O)))
          = ρ • symmEuclid (matrixToEuclid (O.transpose * M * O)) := by
              exact symmEuclid_matrixToEuclid_smul ρ (O.transpose * M * O)
      _ = ρ • (O.transpose * symmEuclid (matrixToEuclid M) * O) := by
              rw [symmEuclid_conj]
  rcases hM with hneg | hzero
  · by_cases hρ₀ : ρ = 0
    · subst ρ
      right
      rw [hSM]
      simp
    · left
      have hρpos : 0 < ρ := lt_of_le_of_ne hρ (Ne.symm hρ₀)
      have hB : (O.transpose * symmEuclid (matrixToEuclid M) * O).IsHermitian := by
        have hc : (O.conjTranspose * symmEuclid (matrixToEuclid M) * O).IsHermitian :=
          Matrix.isHermitian_conjTranspose_mul_mul O (symmEuclid_isHermitian (matrixToEuclid M))
        simpa using hc
      have hρB : (ρ • (O.transpose * symmEuclid (matrixToEuclid M) * O)).IsHermitian := by
        unfold Matrix.IsHermitian
        rw [Matrix.conjTranspose_smul]
        rw [hB]
        simp [star_trivial]
      have hMain1 : (symmEuclid_isHermitian (matrixToEuclid (ρ • (O.transpose * M * O)))).eigenvalues₀ =
          hρB.eigenvalues₀ := by
        exact eigenvalues₀_eq_of_charpoly_eq_real
          (symmEuclid_isHermitian (matrixToEuclid (ρ • (O.transpose * M * O)))) hρB
          (by
            rw [hSM])
      have hMain2 : hρB.eigenvalues₀ = ρ • hB.eigenvalues₀ :=
        eigenvalues₀_smul_of_nonneg (hS := hB) hρ hρB
      have hMain3 : ρ • hB.eigenvalues₀ =
          ρ • (symmEuclid_isHermitian (matrixToEuclid M)).eigenvalues₀ := by
        have hconj : hB.eigenvalues₀ = (symmEuclid_isHermitian (matrixToEuclid M)).eigenvalues₀ :=
          eigenvalues₀_conj_of_orthogonal (S := symmEuclid (matrixToEuclid M))
            (symmEuclid_isHermitian (matrixToEuclid M)) hO
        rw [show hB.eigenvalues₀ = (symmEuclid_isHermitian (matrixToEuclid M)).eigenvalues₀ from hconj]
      have hMain : (symmEuclid_isHermitian (matrixToEuclid (ρ • (O.transpose * M * O)))).eigenvalues₀ =
          ρ • (symmEuclid_isHermitian (matrixToEuclid M)).eigenvalues₀ :=
        hMain1.trans (hMain2.trans hMain3)
      rw [hMain]
      have hlt : ρ * (symmEuclid_isHermitian (matrixToEuclid M)).eigenvalues₀ 0 < 0 :=
        mul_neg_of_pos_of_neg hρpos hneg
      simpa using hlt
  · right
    rw [hSM, hzero]
    simp

end FlatSectionHelpers
section FlatSectionProjection

omit [CompleteSpace E] [FiniteDimensional Real E] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem compLinearMap_mem_algebraicCurvatureTensorSubmodule
    {x : M} (L : TangentSpace I x →L[ℝ] TangentSpace I x)
    (X : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    (X : Tensor04At (I := I) (M := M) x).compContinuousLinearMap
        (fun _ : Fin 4 => L) ∈
      algebraicCurvatureTensorSubmodule (I := I) (M := M) x := by
  have hform : IsAlgCurvForm (tensor04StdAt (I := I) (M := M) (X : Tensor04At (I := I) (M := M) x)) :=
    (mem_algebraicCurvatureTensorSubmodule (I := I) (M := M)).mp X.2
  rw [show (X : Tensor04At (I := I) (M := M) x).compContinuousLinearMap
        (fun _ : Fin 4 => L) ∈
        algebraicCurvatureTensorSubmodule (I := I) (M := M) x ↔
      IsAlgCurvForm (tensor04StdAt (I := I) (M := M)
        ((X : Tensor04At (I := I) (M := M) x).compContinuousLinearMap
          (fun _ : Fin 4 => L))) from
    mem_algebraicCurvatureTensorSubmodule (I := I) (M := M)]
  change IsAlgCurvForm (fun v y z w =>
    tensor04StdAt (I := I) (M := M)
      ((X : Tensor04At (I := I) (M := M) x).compContinuousLinearMap
        (fun _ : Fin 4 => L)) v y z w)
  simp_rw [tensor04StdAt_compU_apply_all]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x₁ x₂ y z w
    rw [map_add (L : TangentSpace I x →L[ℝ] TangentSpace I x)]
    exact hform.add_left _ _ _ _ _
  · intro a u y z w
    rw [map_smul (L : TangentSpace I x →L[ℝ] TangentSpace I x)]
    exact hform.smul_left _ _ _ _ _
  · intro u v y z
    exact hform.anti_first _ _ _ _
  · intro u v y z
    exact hform.anti_last _ _ _ _
  · intro u v y z
    exact hform.bianchi _ _ _ _

omit [IsManifold I 2 M] [IsManifold I 3 M]
  [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem fiberProjW_compUhlenbeck_commute
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (iota : MatrixComp M (Fin 3))
    (hiota0 : ∀ x : M, ∀ a k : Fin 3, iota 0 x a k = if a = k then 1 else 0)
    (hgram : ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Fin 3,
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota t x a b =
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota 0 x a b)
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt x))
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) (x : M)
    (A : Tensor04At (I := I) (M := M) x) :
    (fiberProjW (I := I) (S.base.metric 0) x
        (A.compContinuousLinearMap (fun _ : Fin 4 => uhlenbeckEndomorphismAt (basisAt x) iota t))
      : Tensor04At (I := I) (M := M) x) =
      ContinuousMultilinearMap.compContinuousLinearMap
        (fiberProjW (I := I) (S.base.metric t) x A : Tensor04At (I := I) (M := M) x)
        (fun _ : Fin 4 => uhlenbeckEndomorphismAt (basisAt x) iota t) := by
  classical
  let U : TangentSpace I x →L[ℝ] TangentSpace I x := uhlenbeckEndomorphismAt (basisAt x) iota t
  let compU : Tensor04At (I := I) (M := M) x → Tensor04At (I := I) (M := M) x :=
    fun B => B.compContinuousLinearMap (fun _ : Fin 4 => U)
  let e : TangentSpace I x ≃ₗ[ℝ] TangentSpace I x :=
    LinearEquiv.ofBijective U.toLinearMap (uhlenbeckEndomorphism_invertible hT S basisAt iota hiota0 hgram ht x)
  let Uinv : TangentSpace I x →L[ℝ] TangentSpace I x := e.symm.toContinuousLinearMap
  let compUinv : Tensor04At (I := I) (M := M) x → Tensor04At (I := I) (M := M) x :=
    fun B => B.compContinuousLinearMap (fun _ : Fin 4 => Uinv)
  have hUinvU : ∀ v : TangentSpace I x, Uinv (U v) = v := by
    intro v
    change e.symm (e v) = v
    exact e.symm_apply_apply v
  have hcompUinv : ∀ B : Tensor04At (I := I) (M := M) x, compU (compUinv B) = B := by
    intro B
    apply tensor0SSpace_ext 4 x
    intro v
    change ContinuousMultilinearMap.compContinuousLinearMap
        (ContinuousMultilinearMap.compContinuousLinearMap B (fun _ : Fin 4 => Uinv))
        (fun _ : Fin 4 => U) v = B v
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
    funext i
    exact hUinvU (v i)
  have hchar : ∀ q : algebraicCurvatureTensorSubmodule (I := I) (M := M) x,
      inner0S (I := I) (S.base.metric 0) x 4
        (fiberProjW (I := I) (S.base.metric 0) x
          (A.compContinuousLinearMap (fun _ : Fin 4 => U))) q =
      inner0S (I := I) (S.base.metric 0) x 4
        (ContinuousMultilinearMap.compContinuousLinearMap
          (fiberProjW (I := I) (S.base.metric t) x A : Tensor04At (I := I) (M := M) x)
          (fun _ : Fin 4 => U)) q := by
    intro q
    let q' : Tensor04At (I := I) (M := M) x :=
      ContinuousMultilinearMap.compContinuousLinearMap
        (q : Tensor04At (I := I) (M := M) x) (fun _ : Fin 4 => Uinv)
    have hq' : q' ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x := by
      exact compLinearMap_mem_algebraicCurvatureTensorSubmodule (I := I) Uinv
        ⟨q, q.2⟩
    have hqU : q'.compContinuousLinearMap (fun _ : Fin 4 => U) = (q : Tensor04At (I := I) (M := M) x) := by
      dsimp [q']
      exact hcompUinv (q : Tensor04At (I := I) (M := M) x)
    have hiso := fiberInner_compUhlenbeck_isometry_full hT S basisAt iota hiota0 hgram horth0 ht x A q'
    calc
      inner0S (I := I) (S.base.metric 0) x 4
          (fiberProjW (I := I) (S.base.metric 0) x
            (A.compContinuousLinearMap (fun _ : Fin 4 => U))) q
          = inner0S (I := I) (S.base.metric 0) x 4
              (A.compContinuousLinearMap (fun _ : Fin 4 => U)) q := by
              exact fiberProjW_spec (I := I) (S.base.metric 0) x
                (A.compContinuousLinearMap (fun _ : Fin 4 => U)) q
      _ = inner0S (I := I) (S.base.metric 0) x 4
              (A.compContinuousLinearMap (fun _ : Fin 4 => U))
              (q'.compContinuousLinearMap (fun _ : Fin 4 => U)) := by
              rw [hqU]
      _ = inner0S (I := I) (S.base.metric t) x 4 A q' := by
              exact hiso
      _ = inner0S (I := I) (S.base.metric t) x 4
              (fiberProjW (I := I) (S.base.metric t) x A) q' := by
              rw [fiberProjW_spec (I := I) (S.base.metric t) x A ⟨q', hq'⟩]
      _ = inner0S (I := I) (S.base.metric 0) x 4
              (ContinuousMultilinearMap.compContinuousLinearMap
                (fiberProjW (I := I) (S.base.metric t) x A : Tensor04At (I := I) (M := M) x)
                (fun _ : Fin 4 => U)) q := by
              have hiso' := fiberInner_compUhlenbeck_isometry_full hT S basisAt iota hiota0 hgram horth0 ht x
                (fiberProjW (I := I) (S.base.metric t) x A : Tensor04At (I := I) (M := M) x) q'
              rw [← hqU]
              exact hiso'.symm
  let p : algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
    fiberProjW (I := I) (S.base.metric 0) x
      (A.compContinuousLinearMap (fun _ : Fin 4 => U))
  let u : algebraicCurvatureTensorSubmodule (I := I) (M := M) x := ⟨
    ContinuousMultilinearMap.compContinuousLinearMap
      (fiberProjW (I := I) (S.base.metric t) x A : Tensor04At (I := I) (M := M) x)
      (fun _ : Fin 4 => U),
    compLinearMap_mem_algebraicCurvatureTensorSubmodule (I := I) U
      (fiberProjW (I := I) (S.base.metric t) x A)⟩
  have hdiff : ∀ q : algebraicCurvatureTensorSubmodule (I := I) (M := M) x,
      inner0S (I := I) (S.base.metric 0) x 4 ((p - u) : Tensor04At (I := I) (M := M) x) q = 0 := by
    intro q
    have h1 := hchar q
    have h2 : inner0S (I := I) (S.base.metric 0) x 4 u q =
        inner0S (I := I) (S.base.metric 0) x 4
          (ContinuousMultilinearMap.compContinuousLinearMap
            (fiberProjW (I := I) (S.base.metric t) x A : Tensor04At (I := I) (M := M) x)
            (fun _ : Fin 4 => U)) q := by
      rfl
    have hsub : inner0S (I := I) (S.base.metric 0) x 4 ((p - u) : Tensor04At (I := I) (M := M) x) q =
        inner0S (I := I) (S.base.metric 0) x 4 (p : Tensor04At (I := I) (M := M) x) q -
          inner0S (I := I) (S.base.metric 0) x 4 (u : Tensor04At (I := I) (M := M) x) q := by
      change (tensor0SMetricData (I := I) (S.base.metric 0) x 4).flat
          ((p : Tensor04At (I := I) (M := M) x) - u) (q : Tensor04At (I := I) (M := M) x) =
        (tensor0SMetricData (I := I) (S.base.metric 0) x 4).flat
          (p : Tensor04At (I := I) (M := M) x) (q : Tensor04At (I := I) (M := M) x) -
        (tensor0SMetricData (I := I) (S.base.metric 0) x 4).flat
          (u : Tensor04At (I := I) (M := M) x) (q : Tensor04At (I := I) (M := M) x)
      simp [map_sub]
    rw [hsub]
    rw [h2] at h1
    linarith
  have hself : inner0S (I := I) (S.base.metric 0) x 4
      ((p - u) : Tensor04At (I := I) (M := M) x) (p - u) = 0 := by
    simpa using hdiff ⟨(p - u : Tensor04At (I := I) (M := M) x), by
      exact Submodule.sub_mem (algebraicCurvatureTensorSubmodule (I := I) (M := M) x) p.2 u.2⟩
  have hzero : (p - u : Tensor04At (I := I) (M := M) x) = 0 := by
    change (tensor0SMetricData (I := I) (S.base.metric 0) x 4).inner
        ((p - u : Tensor04At (I := I) (M := M) x)) (p - u) = 0 at hself
    exact ((tensor0SMetricData (I := I) (S.base.metric 0) x 4).inner_self_eq_zero_iff
      (p - u : Tensor04At (I := I) (M := M) x)).mp hself
  have hpeq : p = u := by
    apply Subtype.ext
    exact sub_eq_zero.mp hzero
  simpa [p, u] using congrArg Subtype.val hpeq

omit [IsManifold I 2 M] [IsManifold I 3 M]
  [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem regionProjMatrix_uhlenbeckPullback_eq_moving
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (iota : MatrixComp M (Fin 3))
    (hiota0 : ∀ x : M, ∀ a k : Fin 3, iota 0 x a k = if a = k then 1 else 0)
    (hgram : ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Fin 3,
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota t x a b =
        movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota 0 x a b)
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt x))
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) (x : M)
    (A : Tensor04At (I := I) (M := M) x) :
    regionProjMatrix (I := I) (S.base.metric 0) (basisAt x)
        (uhlenbeckPullbackTensorAt (I := I) basisAt iota t x A) =
      regionProjMatrix (I := I) (S.base.metric t)
        (uhlenbeckMovingBasis hT S basisAt iota hiota0 hgram t ht x) A := by
  unfold regionProjMatrix
  let pt : algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
    fiberProjW (I := I) (S.base.metric t) x A
  let p0 : algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
    fiberProjW (I := I) (S.base.metric 0) x
      (uhlenbeckPullbackTensorAt (I := I) basisAt iota t x A)
  let u : algebraicCurvatureTensorSubmodule (I := I) (M := M) x := ⟨
    ContinuousMultilinearMap.compContinuousLinearMap
      (pt : Tensor04At (I := I) (M := M) x)
      (fun _ : Fin 4 => uhlenbeckEndomorphismAt (basisAt x) iota t),
    compUhlenbeck_mem_algebraicCurvatureTensorSubmodule basisAt iota t pt⟩
  have hproj := fiberProjW_compUhlenbeck_commute
    (I := I) (M := M) hT S basisAt iota hiota0 hgram horth0 ht x A
  have hpu : p0 = u := by
    apply Subtype.ext
    simpa [p0, u, pt, uhlenbeckPullbackTensorAt] using hproj
  change curvatureOperatorMatrixAt (I := I) x (basisAt x) p0 = _
  rw [hpu]
  simpa [u, pt] using curvatureOperatorMatrixAt_compU_eq_moving
    (I := I) (M := M) hT S basisAt iota hiota0 hgram ht x
      (fiberProjW (I := I) (S.base.metric t) x A)

end FlatSectionProjection


































section RadialTransportLinear

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Connection

variable [NeZero (Module.finrank ℝ E)]
variable [T2Space (TangentBundle I M)]

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem radialParallelTransportSection_add [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (p : M)
    {X : TangentSpace I p} (hX : ‖(X : E)‖ < radialRadius (I := I) g p)
    (u w : TangentSpace I p) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    radialParallelTransportSection (I := I) g p hX (u + w) t =
      radialParallelTransportSection (I := I) g p hX u t +
        radialParallelTransportSection (I := I) g p hX w t := by
  classical
  let γ : ℝ → M := fun s => expMap (I := I) g p (s • X)
  let Puv : ∀ s, TangentSpace I (γ s) := radialParallelTransportSection (I := I) g p hX (u + w)
  let Pu : ∀ s, TangentSpace I (γ s) := radialParallelTransportSection (I := I) g p hX u
  let Pw : ∀ s, TangentSpace I (γ s) := radialParallelTransportSection (I := I) g p hX w
  let Y₁ : ℝ → E := chartRepAt (I := I) γ Puv 0
  let Y₂ : ℝ → E := chartRepAt (I := I) γ Pu 0 + chartRepAt (I := I) γ Pw 0
  have hIcc_sub : Set.Icc (0 : ℝ) 1 ⊆ Set.Icc (-1 : ℝ) 2 := by
    intro s hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  let U : Set ℝ := {s : ℝ | ‖s • (X : E)‖ < expMapC2Radius (I := I) g p}
  have hsub : Set.Icc (0 : ℝ) 1 ⊆ U := by
    intro s hs
    exact norm_smul_lt_expMapC2Radius_of_lt_radialRadius (I := I) g p hX (hIcc_sub hs)
  have hcd : ContDiffOn ℝ 2 (chartCurve (I := I) p γ) U := by
    simpa [γ, U] using (radialCurve_chartCurve_contDiffOn (I := I) g p (v := X))
  have hcd1 : ContDiffOn ℝ 1 (chartCurve (I := I) p γ) U :=
    hcd.of_le (WithTop.coe_le_coe.2 (by norm_num : (1 : ℕ∞) ≤ (2 : ℕ∞)))
  have hu : ContinuousOn (fun τ : ℝ => deriv (chartCurve (I := I) p γ) τ) (Set.Icc 0 1) := by
    have hd : ContDiffOn ℝ 0 (deriv (chartCurve (I := I) p γ)) U :=
      hcd1.deriv_of_isOpen (radialCurve_domain_isOpen (I := I) g p X)
        (by norm_num : (0 : WithTop ℕ∞) + 1 ≤ (1 : WithTop ℕ∞))
    exact (hd.continuousOn).mono hsub
  have hγ : ContinuousOn (chartCurve (I := I) p γ) (Set.Icc 0 1) := by
    have hφ : ContinuousOn (extChartAt I p) (extChartAt I p).source :=
      continuousOn_extChartAt (I := I) p
    have hmaps : Set.MapsTo γ (Set.Icc 0 1) (extChartAt I p).source := by
      intro s hs
      rw [extChartAt_source]
      exact radialCurve_mem_chartAt_source_of_lt_radialRadius (I := I) g p hX (hIcc_sub hs)
    have hγcont : ContinuousOn γ U :=
      (radialCurve_contMDiffOn_two (I := I) g p (v := X)).continuousOn
    exact hφ.comp (hγcont.mono hsub) hmaps
  have hsrc : ∀ τ ∈ Set.Icc (0 : ℝ) 1, γ τ ∈ (chartAt H p).source := by
    intro τ hτ
    exact radialCurve_mem_chartAt_source_of_lt_radialRadius (I := I) g p hX (hIcc_sub hτ)
  have hODE : ∀ (η₀ : TangentSpace I p), ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt (chartRepAt (I := I) γ (radialParallelTransportSection (I := I) g p hX η₀) 0)
        (- chartChristoffelContraction (I := I) g p
          (deriv (chartCurve (I := I) p γ) τ)
          (chartRepAt (I := I) γ (radialParallelTransportSection (I := I) g p hX η₀) 0 τ)
          (chartCurve (I := I) p γ τ))
        (Set.Icc (0 : ℝ) 1) τ := by
    intro η₀ τ hτ
    have hd := radialParallelTransportSection_ode (I := I) g p hX η₀ (hIcc_sub hτ)
    exact hd.mono (by intro s hs; exact hIcc_sub hs)
  have hY₁ : ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Y₁
      (- chartChristoffelContraction (I := I) g p
        (deriv (chartCurve (I := I) p γ) τ) (Y₁ τ) (chartCurve (I := I) p γ τ))
      (Set.Icc (0 : ℝ) 1) τ := by
    intro τ hτ
    have hd := hODE (u + w) τ hτ
    simpa [Y₁, Puv] using hd
  have hY₂ : ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Y₂
      (- chartChristoffelContraction (I := I) g p
        (deriv (chartCurve (I := I) p γ) τ) (Y₂ τ) (chartCurve (I := I) p γ τ))
      (Set.Icc (0 : ℝ) 1) τ := by
    intro τ hτ
    have hdu := hODE u τ hτ
    have hdw := hODE w τ hτ
    have hsum := hdu.add hdw
    have hfun : (chartRepAt (I := I) γ (radialParallelTransportSection (I := I) g p hX u) 0 +
          chartRepAt (I := I) γ (radialParallelTransportSection (I := I) g p hX w) 0) = Y₂ := by
      rfl
    have hderiv : - chartChristoffelContraction (I := I) g p
          (deriv (chartCurve (I := I) p γ) τ)
          (chartRepAt (I := I) γ (radialParallelTransportSection (I := I) g p hX u) 0 τ)
          (chartCurve (I := I) p γ τ) +
        - chartChristoffelContraction (I := I) g p
          (deriv (chartCurve (I := I) p γ) τ)
          (chartRepAt (I := I) γ (radialParallelTransportSection (I := I) g p hX w) 0 τ)
          (chartCurve (I := I) p γ τ) =
        - chartChristoffelContraction (I := I) g p
          (deriv (chartCurve (I := I) p γ) τ) (Y₂ τ) (chartCurve (I := I) p γ τ) := by
        rw [show Y₂ τ = chartRepAt (I := I) γ Pu 0 τ + chartRepAt (I := I) γ Pw 0 τ by rfl]
        rw [show chartRepAt (I := I) γ Pu 0 τ = chartRepAt (I := I) γ (radialParallelTransportSection (I := I) g p hX u) 0 τ by rfl]
        rw [show chartRepAt (I := I) γ Pw 0 τ = chartRepAt (I := I) γ (radialParallelTransportSection (I := I) g p hX w) 0 τ by rfl]
        rw [ChartChristoffel.contraction_add_right]
        abel
    convert hsum using 1
    · exact hderiv.symm
  have h0eq : Y₁ 0 = Y₂ 0 := by
    dsimp [Y₁, Y₂]
    have h1 : (trivializationAt E (TangentSpace I) (γ 0)).continuousLinearMapAt ℝ (γ 0)
        (radialParallelTransportSection (I := I) g p hX (u + w) 0) =
      (trivializationAt E (TangentSpace I) (γ 0)).continuousLinearMapAt ℝ (γ 0) u +
        (trivializationAt E (TangentSpace I) (γ 0)).continuousLinearMapAt ℝ (γ 0) w := by
      rw [radialParallelTransportSection_initial (I := I) g p hX (u + w)]
      exact map_add ((trivializationAt E (TangentSpace I) (γ 0)).continuousLinearMapAt ℝ (γ 0)) u w
    simpa [Puv, Pu, Pw, radialParallelTransportSection_initial] using h1
  have hEq01 : Set.EqOn Y₁ Y₂ (Set.Icc (0 : ℝ) 1) :=
    parallel_local_uniqueness_on_Icc (I := I) g p γ
      (fun τ => deriv (chartCurve (I := I) p γ) τ) (by norm_num) ⟨le_rfl, by norm_num⟩
      hu hγ hsrc hY₁ hY₂ h0eq
  have hEq_t : Y₁ t = Y₂ t := hEq01 ht
  have hchart : chartRepAt (I := I) γ Puv 0 t = chartRepAt (I := I) γ Pu 0 t + chartRepAt (I := I) γ Pw 0 t := by
    simpa [Y₁, Y₂] using hEq_t
  have hmem : γ t ∈ (trivializationAt E (TangentSpace I) p).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hsrc t ht
  have hsec : Puv t = Pu t + Pw t := by
    change (trivializationAt E (TangentSpace I) (γ 0)).continuousLinearMapAt ℝ (γ t) (Puv t) =
      (trivializationAt E (TangentSpace I) (γ 0)).continuousLinearMapAt ℝ (γ t) (Pu t) +
        (trivializationAt E (TangentSpace I) (γ 0)).continuousLinearMapAt ℝ (γ t) (Pw t) at hchart
    rw [show γ 0 = p from (radialCurve_zero (I := I) g p X)] at hchart
    have hround_l : (trivializationAt E (TangentSpace I) p).symmL ℝ (γ t)
        ((trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ (γ t) (Puv t)) = Puv t :=
      (trivializationAt E (TangentSpace I) p).symmL_continuousLinearMapAt (R := ℝ) hmem (Puv t)
    have hround_r : (trivializationAt E (TangentSpace I) p).symmL ℝ (γ t)
        ((trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ (γ t) (Pu t) +
          (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ (γ t) (Pw t)) = Pu t + Pw t := by
      rw [map_add]
      rw [(trivializationAt E (TangentSpace I) p).symmL_continuousLinearMapAt (R := ℝ) hmem (Pu t)]
      rw [(trivializationAt E (TangentSpace I) p).symmL_continuousLinearMapAt (R := ℝ) hmem (Pw t)]
    exact hround_l.symm.trans ((congrArg ((trivializationAt E (TangentSpace I) p).symmL ℝ (γ t)) hchart).trans hround_r)
  simpa [Puv, Pu, Pw] using hsec

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem radialParallelTransportSection_smul [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (p : M)
    {X : TangentSpace I p} (hX : ‖(X : E)‖ < radialRadius (I := I) g p)
    (c : ℝ) (u : TangentSpace I p) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    radialParallelTransportSection (I := I) g p hX (c • u) t =
      c • radialParallelTransportSection (I := I) g p hX u t := by
  classical
  by_cases hc : c = 0
  · subst c
    have hz : radialParallelTransportSection (I := I) g p hX 0 t = 0 := by
      have hadd : radialParallelTransportSection (I := I) g p hX (0 + 0) t =
          radialParallelTransportSection (I := I) g p hX 0 t + radialParallelTransportSection (I := I) g p hX 0 t :=
        radialParallelTransportSection_add (I := I) g p hX 0 0 ht
      have hleft : radialParallelTransportSection (I := I) g p hX (0 + 0) t =
          radialParallelTransportSection (I := I) g p hX 0 t := by
        congr 1
        abel
      exact add_left_cancel (a := radialParallelTransportSection (I := I) g p hX 0 t)
        (b := radialParallelTransportSection (I := I) g p hX 0 t)
        (c := (0 : TangentSpace I (expMap (I := I) g p (t • X)))) (by
          rw [add_zero]
          exact (hadd.symm.trans hleft))
    rw [show (0 : ℝ) • u = 0 by exact zero_smul ℝ u]
    rw [show (0 : ℝ) • radialParallelTransportSection (I := I) g p hX u t = 0 by
      exact zero_smul ℝ (radialParallelTransportSection (I := I) g p hX u t)]
    exact hz
  · let γ : ℝ → M := fun s => expMap (I := I) g p (s • X)
    let Pcu : ∀ s, TangentSpace I (γ s) := radialParallelTransportSection (I := I) g p hX (c • u)
    let Pu : ∀ s, TangentSpace I (γ s) := radialParallelTransportSection (I := I) g p hX u
    let Y₁ : ℝ → E := chartRepAt (I := I) γ Pcu 0
    let Y₂ : ℝ → E := c • chartRepAt (I := I) γ Pu 0
    have hIcc_sub : Set.Icc (0 : ℝ) 1 ⊆ Set.Icc (-1 : ℝ) 2 := by
      intro s hs
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    let U : Set ℝ := {s : ℝ | ‖s • (X : E)‖ < expMapC2Radius (I := I) g p}
    have hsub : Set.Icc (0 : ℝ) 1 ⊆ U := by
      intro s hs
      exact norm_smul_lt_expMapC2Radius_of_lt_radialRadius (I := I) g p hX (hIcc_sub hs)
    have hcd : ContDiffOn ℝ 2 (chartCurve (I := I) p γ) U := by
      simpa [γ, U] using (radialCurve_chartCurve_contDiffOn (I := I) g p (v := X))
    have hcd1 : ContDiffOn ℝ 1 (chartCurve (I := I) p γ) U :=
      hcd.of_le (WithTop.coe_le_coe.2 (by norm_num : (1 : ℕ∞) ≤ (2 : ℕ∞)))
    have hu : ContinuousOn (fun τ : ℝ => deriv (chartCurve (I := I) p γ) τ) (Set.Icc 0 1) := by
      have hd : ContDiffOn ℝ 0 (deriv (chartCurve (I := I) p γ)) U :=
        hcd1.deriv_of_isOpen (radialCurve_domain_isOpen (I := I) g p X)
          (by norm_num : (0 : WithTop ℕ∞) + 1 ≤ (1 : WithTop ℕ∞))
      exact (hd.continuousOn).mono hsub
    have hγ : ContinuousOn (chartCurve (I := I) p γ) (Set.Icc 0 1) := by
      have hφ : ContinuousOn (extChartAt I p) (extChartAt I p).source :=
        continuousOn_extChartAt (I := I) p
      have hmaps : Set.MapsTo γ (Set.Icc 0 1) (extChartAt I p).source := by
        intro s hs
        rw [extChartAt_source]
        exact radialCurve_mem_chartAt_source_of_lt_radialRadius (I := I) g p hX (hIcc_sub hs)
      have hγcont : ContinuousOn γ U :=
        (radialCurve_contMDiffOn_two (I := I) g p (v := X)).continuousOn
      exact hφ.comp (hγcont.mono hsub) hmaps
    have hsrc : ∀ τ ∈ Set.Icc (0 : ℝ) 1, γ τ ∈ (chartAt H p).source := by
      intro τ hτ
      exact radialCurve_mem_chartAt_source_of_lt_radialRadius (I := I) g p hX (hIcc_sub hτ)
    have hODE : ∀ (η₀ : TangentSpace I p), ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt (chartRepAt (I := I) γ (radialParallelTransportSection (I := I) g p hX η₀) 0)
          (- chartChristoffelContraction (I := I) g p
            (deriv (chartCurve (I := I) p γ) τ)
            (chartRepAt (I := I) γ (radialParallelTransportSection (I := I) g p hX η₀) 0 τ)
            (chartCurve (I := I) p γ τ))
          (Set.Icc (0 : ℝ) 1) τ := by
      intro η₀ τ hτ
      have hd := radialParallelTransportSection_ode (I := I) g p hX η₀ (hIcc_sub hτ)
      exact hd.mono (by intro s hs; exact hIcc_sub hs)
    have hY₁ : ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Y₁
        (- chartChristoffelContraction (I := I) g p
          (deriv (chartCurve (I := I) p γ) τ) (Y₁ τ) (chartCurve (I := I) p γ τ))
        (Set.Icc (0 : ℝ) 1) τ := by
      intro τ hτ
      have hd := hODE (c • u) τ hτ
      simpa [Y₁, Pcu] using hd
    have hY₂ : ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Y₂
        (- chartChristoffelContraction (I := I) g p
          (deriv (chartCurve (I := I) p γ) τ) (Y₂ τ) (chartCurve (I := I) p γ τ))
        (Set.Icc (0 : ℝ) 1) τ := by
      intro τ hτ
      have hdu := hODE u τ hτ
      have hsmul := hdu.const_smul c
      have hfun : (c • chartRepAt (I := I) γ (radialParallelTransportSection (I := I) g p hX u) 0) = Y₂ := by
        rfl
      have hderiv : c • (- chartChristoffelContraction (I := I) g p
            (deriv (chartCurve (I := I) p γ) τ)
            (chartRepAt (I := I) γ (radialParallelTransportSection (I := I) g p hX u) 0 τ)
            (chartCurve (I := I) p γ τ)) =
          - chartChristoffelContraction (I := I) g p
            (deriv (chartCurve (I := I) p γ) τ) (Y₂ τ) (chartCurve (I := I) p γ τ) := by
        rw [show Y₂ τ = c • chartRepAt (I := I) γ Pu 0 τ by rfl]
        rw [show chartRepAt (I := I) γ Pu 0 τ = chartRepAt (I := I) γ (radialParallelTransportSection (I := I) g p hX u) 0 τ by rfl]
        rw [ChartChristoffel.contraction_smul_right]
        rw [smul_neg]
      convert hsmul using 1
      · exact hderiv.symm
    have h0eq : Y₁ 0 = Y₂ 0 := by
      dsimp [Y₁, Y₂]
      have h1 : (trivializationAt E (TangentSpace I) (γ 0)).continuousLinearMapAt ℝ (γ 0)
          (radialParallelTransportSection (I := I) g p hX (c • u) 0) =
          c • (trivializationAt E (TangentSpace I) (γ 0)).continuousLinearMapAt ℝ (γ 0)
            (radialParallelTransportSection (I := I) g p hX u 0) := by
        rw [radialParallelTransportSection_initial (I := I) g p hX (c • u)]
        rw [radialParallelTransportSection_initial (I := I) g p hX u]
        exact map_smul ((trivializationAt E (TangentSpace I) (γ 0)).continuousLinearMapAt ℝ (γ 0)) c u
      simpa [Pcu, Pu, radialParallelTransportSection_initial] using h1
    have hEq01 : Set.EqOn Y₁ Y₂ (Set.Icc (0 : ℝ) 1) :=
      parallel_local_uniqueness_on_Icc (I := I) g p γ
        (fun τ => deriv (chartCurve (I := I) p γ) τ) (by norm_num) ⟨le_rfl, by norm_num⟩
        hu hγ hsrc hY₁ hY₂ h0eq
    have hEq_t : Y₁ t = Y₂ t := hEq01 ht
    have hchart : chartRepAt (I := I) γ Pcu 0 t = c • chartRepAt (I := I) γ Pu 0 t := by
      simpa [Y₁, Y₂] using hEq_t
    have hmem : γ t ∈ (trivializationAt E (TangentSpace I) p).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]
      exact hsrc t ht
    have hsec : Pcu t = c • Pu t := by
      change (trivializationAt E (TangentSpace I) (γ 0)).continuousLinearMapAt ℝ (γ t) (Pcu t) =
        c • (trivializationAt E (TangentSpace I) (γ 0)).continuousLinearMapAt ℝ (γ t) (Pu t) at hchart
      rw [show γ 0 = p from (radialCurve_zero (I := I) g p X)] at hchart
      have hround_l : (trivializationAt E (TangentSpace I) p).symmL ℝ (γ t)
          ((trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ (γ t) (Pcu t)) = Pcu t :=
        (trivializationAt E (TangentSpace I) p).symmL_continuousLinearMapAt (R := ℝ) hmem (Pcu t)
      have hround_r : (trivializationAt E (TangentSpace I) p).symmL ℝ (γ t)
          (c • (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ (γ t) (Pu t)) = c • Pu t := by
        rw [map_smul]
        rw [(trivializationAt E (TangentSpace I) p).symmL_continuousLinearMapAt (R := ℝ) hmem (Pu t)]
      exact hround_l.symm.trans ((congrArg ((trivializationAt E (TangentSpace I) p).symmL ℝ (γ t)) hchart).trans hround_r)
    simpa [Pcu, Pu] using hsec

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem radialTransportSection_linear_add [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (p : M)
    (u w : TangentSpace I p) (y : M) :
    radialTransportSection g p (u + w) y =
      radialTransportSection g p u y + radialTransportSection g p w y := by
  classical
  by_cases hy : y ∈ radialTransportSectionDomain (I := I) g p
  · rw [radialTransportSection]
    have hcond : y ∈ (normalChartAt (I := I) g p).source ∧
        ‖normalChartAt (I := I) g p y‖ < radialRadius (I := I) g p := by
      simpa [radialTransportSectionDomain] using hy
    simp_rw [radialTransportSection, dif_pos hcond]
    exact radialParallelTransportSection_add (I := I) g p hcond.2 u w (t := 1)
      ⟨by norm_num, by norm_num⟩
  · have hnot : ¬(y ∈ (normalChartAt (I := I) g p).source ∧
        ‖normalChartAt (I := I) g p y‖ < radialRadius (I := I) g p) := by
      simpa [radialTransportSectionDomain] using hy
    simp_rw [radialTransportSection, dif_neg hnot]
    simp

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem radialTransportSection_linear_smul [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (p : M)
    (c : ℝ) (u : TangentSpace I p) (y : M) :
    radialTransportSection g p (c • u) y = c • radialTransportSection g p u y := by
  classical
  by_cases hy : y ∈ radialTransportSectionDomain (I := I) g p
  · rw [radialTransportSection]
    have hcond : y ∈ (normalChartAt (I := I) g p).source ∧
        ‖normalChartAt (I := I) g p y‖ < radialRadius (I := I) g p := by
      simpa [radialTransportSectionDomain] using hy
    simp_rw [radialTransportSection, dif_pos hcond]
    exact radialParallelTransportSection_smul (I := I) g p hcond.2 c u (t := 1)
      ⟨by norm_num, by norm_num⟩
  · have hnot : ¬(y ∈ (normalChartAt (I := I) g p).source ∧
        ‖normalChartAt (I := I) g p y‖ < radialRadius (I := I) g p) := by
      simpa [radialTransportSectionDomain] using hy
    simp_rw [radialTransportSection, dif_neg hnot]
    simp



set_option linter.unusedSectionVars false in
omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
lemma radialParallelTransportSection_chartGram_hasDerivAt_zero [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (p : M)
    {X : TangentSpace I p} (hX : ‖(X : E)‖ < radialRadius (I := I) g p)
    (u w : TangentSpace I p) {t : ℝ} (ht : t ∈ Set.Ioo (-1 : ℝ) 2) :
    HasDerivAt (fun τ : ℝ =>
      chartGramAlongCurve (I := I) g p (fun τ0 : ℝ => expMap (I := I) g p (τ0 • X))
        (chartRepAt (I := I) (fun τ0 : ℝ => expMap (I := I) g p (τ0 • X))
          (radialParallelTransportSection (I := I) g p hX u) 0)
        (chartRepAt (I := I) (fun τ0 : ℝ => expMap (I := I) g p (τ0 • X))
          (radialParallelTransportSection (I := I) g p hX w) 0) τ) 0 t := by
  classical
  let γ : ℝ → M := fun t0 => expMap (I := I) g p (t0 • X)
  let Pu : ∀ t0, TangentSpace I (γ t0) := radialParallelTransportSection (I := I) g p hX u
  let Pw : ∀ t0, TangentSpace I (γ t0) := radialParallelTransportSection (I := I) g p hX w
  let V : ℝ → E := chartRepAt (I := I) γ Pu 0
  let W : ℝ → E := chartRepAt (I := I) γ Pw 0
  let uPrime : ℝ → E := fun t0 => deriv (chartCurve (I := I) p γ) t0
  let o : Set ℝ := Set.Ioo (-1 : ℝ) 2
  have hdom : ∀ t0 : ℝ, t0 ∈ o → ‖t0 • (X : E)‖ < expMapC2Radius (I := I) g p := by
    intro t0 ht0
    exact norm_smul_lt_expMapC2Radius_of_lt_radialRadius (I := I) g p hX ⟨ht0.1.le, ht0.2.le⟩
  have hIcc : ∀ t0 : ℝ, t0 ∈ o → t0 ∈ Set.Icc (-1 : ℝ) 2 := by
    intro t0 ht0
    exact ⟨ht0.1.le, ht0.2.le⟩
  have hγdiff : ∀ t0 : ℝ, t0 ∈ o → DifferentiableAt ℝ (chartCurve (I := I) p γ) t0 := by
    intro t0 ht0
    let U : Set ℝ := {u0 : ℝ | ‖u0 • (X : E)‖ < expMapC2Radius (I := I) g p}
    have hcd : ContDiffOn ℝ 2 (chartCurve (I := I) p γ) U := by
      simpa [γ, U] using (radialCurve_chartCurve_contDiffOn (I := I) g p (v := X))
    have hUnhd : U ∈ 𝓝 t0 := (radialCurve_domain_isOpen (I := I) g p X).mem_nhds (hdom t0 ht0)
    exact (hcd.contDiffAt hUnhd).differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have hsrc_o : ∀ t0 ∈ o, γ t0 ∈ (chartAt H p).source := by
    intro t0 ht0
    exact radialCurve_mem_chartAt_source_of_lt_radialRadius (I := I) g p hX (hIcc t0 ht0)
  have hmem : ∀ t0 ∈ o, chartCurve (I := I) p γ t0 ∈ interior (extChartAt I p).target := by
    intro t0 ht0
    have hxsrc : γ t0 ∈ (extChartAt I p).source := by
      rw [extChartAt_source]
      exact hsrc_o t0 ht0
    have hxtarget : chartCurve (I := I) p γ t0 ∈ (extChartAt I p).target :=
      (extChartAt I p).map_source hxsrc
    exact extChartAt_target_subset_interior_of_boundaryless (I := I) p hxtarget
  have hVpar : IsParallelChart (I := I) g p γ uPrime V o := by
    constructor
    · intro t0 ht0
      exact (hγdiff t0 ht0).hasDerivAt
    · intro t0 ht0
      have hd := radialParallelTransportSection_ode (I := I) g p hX u (hIcc t0 ht0)
      have hd' : HasDerivAt (chartRepAt (I := I) γ (radialParallelTransportSection (I := I) g p hX u) 0)
          (- chartChristoffelContraction (I := I) g p (uPrime t0)
            (chartRepAt (I := I) γ (radialParallelTransportSection (I := I) g p hX u) 0 t0)
            (chartCurve (I := I) p γ t0)) t0 :=
        hd.hasDerivAt (Icc_mem_nhds ht0.1 ht0.2)
      simpa [V, Pu] using hd'
  have hWpar : IsParallelChart (I := I) g p γ uPrime W o := by
    constructor
    · intro t0 ht0
      exact (hγdiff t0 ht0).hasDerivAt
    · intro t0 ht0
      have hd := radialParallelTransportSection_ode (I := I) g p hX w (hIcc t0 ht0)
      have hd' : HasDerivAt (chartRepAt (I := I) γ (radialParallelTransportSection (I := I) g p hX w) 0)
          (- chartChristoffelContraction (I := I) g p (uPrime t0)
            (chartRepAt (I := I) γ (radialParallelTransportSection (I := I) g p hX w) 0 t0)
            (chartCurve (I := I) p γ t0)) t0 :=
        hd.hasDerivAt (Icc_mem_nhds ht0.1 ht0.2)
      simpa [W, Pw] using hd'
  have hderiv : ∀ t0 ∈ o, HasDerivAt
      (fun τ : ℝ => chartGramAlongCurve (I := I) g p γ V W τ) 0 t0 := by
    intro t0 ht0
    let Vprime : ℝ → E := fun _ => - chartChristoffelContraction (I := I) g p (uPrime t0) (V t0)
      (chartCurve (I := I) p γ t0)
    let Wprime : ℝ → E := fun _ => - chartChristoffelContraction (I := I) g p (uPrime t0) (W t0)
      (chartCurve (I := I) p γ t0)
    have hV : HasDerivAt V (Vprime t0) t0 := by
      simpa [Vprime] using (hVpar.hasDerivAt ht0)
    have hW : HasDerivAt W (Wprime t0) t0 := by
      simpa [Wprime] using (hWpar.hasDerivAt ht0)
    have hmain := chartGramAlongCurve_hasDerivAt_covariant (I := I) g p γ V W
      (uPrime := uPrime) (Vprime := Vprime) (Wprime := Wprime) (t := t0)
      ((hγdiff t0 ht0).hasDerivAt) (hmem t0 ht0) hV hW
    have hVzero : Vprime t0 + chartChristoffelContraction (I := I) g p (uPrime t0) (V t0)
        (chartCurve (I := I) p γ t0) = 0 := by
      simp [Vprime]
    have hWzero : Wprime t0 + chartChristoffelContraction (I := I) g p (uPrime t0) (W t0)
        (chartCurve (I := I) p γ t0) = 0 := by
      simp [Wprime]
    rw [hVzero, hWzero] at hmain
    simpa [hVzero, hWzero] using hmain
  have hgoal : HasDerivAt (fun τ : ℝ =>
      chartGramAlongCurve (I := I) g p γ V W τ) 0 t := hderiv t ht
  simpa [γ, Pu, Pw, V, W] using hgoal

set_option linter.unusedSectionVars false in
omit [CompleteSpace E] [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M]
  [T2Space M] [I.Boundaryless] [NeZero (Module.finrank ℝ E)]
  [T2Space (TangentBundle I M)] in
lemma chartGramAlongCurve_eq_inner
    (g : SmoothRiemannianMetric I M) (p : M)
    (γ : ℝ → M) (V W : ℝ → E) (t : ℝ)
    (hsrc : γ t ∈ (chartAt H p).source) :
    chartGramAlongCurve (I := I) g p γ V W t =
      g.inner (γ t) ((trivializationAt E (TangentSpace I) p).symmL ℝ (γ t) (V t))
        ((trivializationAt E (TangentSpace I) p).symmL ℝ (γ t) (W t)) := by
  rw [chartGramAlongCurve_def]
  have hgram : ∀ i j : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g p i j (chartCurve (I := I) p γ t) =
        chartGramMatrix (I := I) g p (γ t) i j := by
    intro i j
    rw [chartGramOnE_def]
    rw [chartCurve_def]
    rw [(extChartAt I p).left_inv (by rw [extChartAt_source]; exact hsrc)]
  simp_rw [hgram]
  have hmain := inner_eq_chartGramOnE_bilinear_on_baseSet (I := I) g p (x := γ t) (V t) (W t)
  exact hmain.symm


omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem radialParallelTransportSection_inner_eq [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (p : M)
    {X : TangentSpace I p} (hX : ‖(X : E)‖ < radialRadius (I := I) g p)
    (u w : TangentSpace I p) {s : ℝ} (hs : s ∈ Set.Ioo (-1 : ℝ) 2) :
    g.inner (expMap (I := I) g p (s • X))
      (radialParallelTransportSection (I := I) g p hX u s)
      (radialParallelTransportSection (I := I) g p hX w s) = g.inner p u w := by
  classical
  let γ : ℝ → M := fun t => expMap (I := I) g p (t • X)
  let Pu : ∀ t, TangentSpace I (γ t) := radialParallelTransportSection (I := I) g p hX u
  let Pw : ∀ t, TangentSpace I (γ t) := radialParallelTransportSection (I := I) g p hX w
  let V : ℝ → E := chartRepAt (I := I) γ Pu 0
  let W : ℝ → E := chartRepAt (I := I) γ Pw 0
  let f : ℝ → ℝ := fun t => chartGramAlongCurve (I := I) g p γ V W t
  let o : Set ℝ := Set.Ioo (-1 : ℝ) 2
  have hγ0 : γ 0 = p := by
    dsimp [γ]
    exact radialCurve_zero (I := I) g p X
  have hsrc_o : ∀ t ∈ o, γ t ∈ (chartAt H p).source := by
    intro t ht
    exact radialCurve_mem_chartAt_source_of_lt_radialRadius (I := I) g p hX ⟨ht.1.le, ht.2.le⟩
  have hderiv : ∀ t ∈ o, HasDerivAt f 0 t := by
    intro t ht
    have h := radialParallelTransportSection_chartGram_hasDerivAt_zero (I := I) g p hX u w ht
    simpa [f, γ, Pu, Pw, V, W] using h
  have hconst : f s = f 0 :=
    isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun t ht => (hderiv t ht).differentiableAt.differentiableWithinAt)
      (fun t ht => (hderiv t ht).deriv) hs ⟨by norm_num, by norm_num⟩
  have hfs : f s = g.inner (expMap (I := I) g p (s • X))
      (radialParallelTransportSection (I := I) g p hX u s)
      (radialParallelTransportSection (I := I) g p hX w s) := by
    have hb : (γ s) ∈ (trivializationAt E (TangentSpace I) p).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]
      exact hsrc_o s hs
    have hV₀ : (trivializationAt E (TangentSpace I) p).symmL ℝ (γ s) (V s) = radialParallelTransportSection (I := I) g p hX u s := by
      change (trivializationAt E (TangentSpace I) p).symmL ℝ (γ s)
          ((trivializationAt E (TangentSpace I) (γ 0)).continuousLinearMapAt ℝ (γ s)
            (radialParallelTransportSection (I := I) g p hX u s)) =
        radialParallelTransportSection (I := I) g p hX u s
      rw [hγ0]
      exact (trivializationAt E (TangentSpace I) p).symmL_continuousLinearMapAt (R := ℝ) hb
        (radialParallelTransportSection (I := I) g p hX u s)
    have hW₀ : (trivializationAt E (TangentSpace I) p).symmL ℝ (γ s) (W s) = radialParallelTransportSection (I := I) g p hX w s := by
      change (trivializationAt E (TangentSpace I) p).symmL ℝ (γ s)
          ((trivializationAt E (TangentSpace I) (γ 0)).continuousLinearMapAt ℝ (γ s)
            (radialParallelTransportSection (I := I) g p hX w s)) =
        radialParallelTransportSection (I := I) g p hX w s
      rw [hγ0]
      exact (trivializationAt E (TangentSpace I) p).symmL_continuousLinearMapAt (R := ℝ) hb
        (radialParallelTransportSection (I := I) g p hX w s)
    unfold f
    rw [← hV₀, ← hW₀]
    exact chartGramAlongCurve_eq_inner (I := I) g p γ V W s (hsrc_o s hs)
  have hf0 : f 0 = g.inner p u w := by
    have hb : p ∈ (trivializationAt E (TangentSpace I) p).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]
      exact mem_chart_source H p
    have hV₀ : (trivializationAt E (TangentSpace I) p).symmL ℝ p (V 0) = u := by
      change (trivializationAt E (TangentSpace I) p).symmL ℝ p
          ((trivializationAt E (TangentSpace I) (γ 0)).continuousLinearMapAt ℝ (γ 0)
            (radialParallelTransportSection (I := I) g p hX u 0)) = u
      rw [hγ0]
      rw [radialParallelTransportSection_initial (I := I) g p hX u]
      exact (trivializationAt E (TangentSpace I) p).symmL_continuousLinearMapAt (R := ℝ) hb u
    have hW₀ : (trivializationAt E (TangentSpace I) p).symmL ℝ p (W 0) = w := by
      change (trivializationAt E (TangentSpace I) p).symmL ℝ p
          ((trivializationAt E (TangentSpace I) (γ 0)).continuousLinearMapAt ℝ (γ 0)
            (radialParallelTransportSection (I := I) g p hX w 0)) = w
      rw [hγ0]
      rw [radialParallelTransportSection_initial (I := I) g p hX w]
      exact (trivializationAt E (TangentSpace I) p).symmL_continuousLinearMapAt (R := ℝ) hb w
    unfold f
    rw [← hV₀, ← hW₀]
    have h := chartGramAlongCurve_eq_inner (I := I) g p γ V W 0 (hsrc_o 0 ⟨by norm_num, by norm_num⟩)
    rw [hγ0] at h
    exact h
  rw [← hfs, ← hf0]
  exact hconst

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem radialTransportSection_inner_eq [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (p : M) (u w : TangentSpace I p) (y : M)
    (hy : y ∈ radialTransportSectionDomain (I := I) g p) :
    g.inner y (radialTransportSection g p u y) (radialTransportSection g p w y) = g.inner p u w := by
  classical
  have hcond : y ∈ (normalChartAt (I := I) g p).source ∧
      ‖normalChartAt (I := I) g p y‖ < radialRadius (I := I) g p := by
    simpa [radialTransportSectionDomain] using hy
  let x : E := normalChartAt (I := I) g p y
  have hEq : y = expMap (I := I) g p ((1 : ℝ) • x) := by
    have hsymm : (normalChartAt (I := I) g p).symm x = y := by
      rw [show x = normalChartAt (I := I) g p y by rfl]
      exact normalChartAt_left_inv (I := I) g p hcond.1
    have htgt : x ∈ (normalChartAt (I := I) g p).symm.source := by
      rw [show x = normalChartAt (I := I) g p y by rfl]
      have hmap : normalChartAt (I := I) g p y ∈ (normalChartAt (I := I) g p).target :=
        (normalChartAt (I := I) g p).map_source hcond.1
      simpa using hmap
    have hexp : (normalChartAt (I := I) g p).symm x = expMap (I := I) g p x :=
      normalChartAt_symm_apply (I := I) g p htgt
    rw [← hsymm, hexp]
    simp
  have hval_u : radialTransportSection g p u y = radialParallelTransportSection (I := I) g p hcond.2 u 1 := by
    simp_rw [radialTransportSection, dif_pos hcond]
  have hval_w : radialTransportSection g p w y = radialParallelTransportSection (I := I) g p hcond.2 w 1 := by
    simp_rw [radialTransportSection, dif_pos hcond]
  have hmain := radialParallelTransportSection_inner_eq (I := I) g p hcond.2 u w (s := 1)
    ⟨by norm_num, by norm_num⟩
  rw [hval_u, hval_w]
  have hbase : g.inner y (radialParallelTransportSection (I := I) g p hcond.2 u 1)
        (radialParallelTransportSection (I := I) g p hcond.2 w 1) =
      g.inner (expMap (I := I) g p ((1 : ℝ) • x))
        (radialParallelTransportSection (I := I) g p hcond.2 u 1)
        (radialParallelTransportSection (I := I) g p hcond.2 w 1) := by
    exact congrArg (fun z : M => g.inner z (radialParallelTransportSection (I := I) g p hcond.2 u 1)
      (radialParallelTransportSection (I := I) g p hcond.2 w 1)) hEq
  rw [hbase]
  simpa [x] using hmain

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem radialTransportSection_injective [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (p : M) (y : M)
    (hy : y ∈ radialTransportSectionDomain (I := I) g p) :
    Function.Injective (fun v : TangentSpace I p => radialTransportSection g p v y) := by
  intro v w hvw
  have hmain := radialTransportSection_inner_eq (I := I) g p (v - w) (v - w) y hy
  have hv : radialTransportSection g p (v - w) y = 0 := by
    have hlin : radialTransportSection g p (v - w) y = radialTransportSection g p v y - radialTransportSection g p w y := by
      have h1 := radialTransportSection_linear_add (I := I) g p v (-w) y
      have h2 := radialTransportSection_linear_smul (I := I) g p (-1) w y
      rw [show -w = (-1 : ℝ) • w by simp] at h1
      rw [h2] at h1
      simpa [sub_eq_add_neg] using h1
    simpa [sub_eq_add_neg, hvw] using hlin
  have hzero : g.inner p (v - w) (v - w) = 0 := by
    rw [← hmain]
    rw [hv]
    simp
  exact sub_eq_zero.mp (by
    by_contra hne
    have hpos' : 0 < g.inner p (v - w) (v - w) := g.pos p (v - w) hne
    linarith)


section TensorTransport

noncomputable def radialTransportLinearMapAt (g : SmoothRiemannianMetric I M) (p y : M) :
    E →ₗ[ℝ] E :=
  { toFun := fun v => radialTransportSection g p v y
    map_add' := by
      intro a b
      exact radialTransportSection_linear_add (I := I) g p a b y
    map_smul' := by
      intro a b
      exact radialTransportSection_linear_smul (I := I) g p a b y }

noncomputable def radialTransportInverseAt [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (p y : M)
    (hy : y ∈ radialTransportSectionDomain (I := I) g p) : E →L[ℝ] E :=
  let T : E →ₗ[ℝ] E := radialTransportLinearMapAt g p y
  let hT : Function.Injective T := by
    intro a b hab
    exact radialTransportSection_injective (I := I) g p y hy (by simpa [radialTransportLinearMapAt] using hab)
  let hsurj : Function.Surjective T :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K := ℝ) (V := E) (V₂ := E) rfl).mp hT
  let e : E ≃ₗ[ℝ] E := LinearEquiv.ofBijective T ⟨hT, hsurj⟩
  (e.symm.toContinuousLinearEquiv).toContinuousLinearMap

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem radialTransportInverseAt_apply
    (g : SmoothRiemannianMetric I M) (p y : M)
    (hy : y ∈ radialTransportSectionDomain (I := I) g p) (v : E) :
    radialTransportInverseAt g p y hy v =
      (LinearEquiv.ofBijective (radialTransportLinearMapAt g p y)
        (by
          have hT : Function.Injective (radialTransportLinearMapAt g p y) := by
            intro a b hab
            exact radialTransportSection_injective (I := I) g p y hy (by simpa [radialTransportLinearMapAt] using hab)
          have hsurj : Function.Surjective (radialTransportLinearMapAt g p y) :=
            (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K := ℝ) (V := E) (V₂ := E) rfl).mp hT
          exact ⟨hT, hsurj⟩)).symm v := by
  rfl

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
theorem radialTransportInverseAt_left_inverse
    (g : SmoothRiemannianMetric I M) (p y : M)
    (hy : y ∈ radialTransportSectionDomain (I := I) g p) (v : E) :
    radialTransportInverseAt g p y hy (radialTransportLinearMapAt g p y v) = v := by
  rw [radialTransportInverseAt_apply]
  exact (LinearEquiv.ofBijective (radialTransportLinearMapAt g p y) (by
    have hT : Function.Injective (radialTransportLinearMapAt g p y) := by
      intro a b hab
      exact radialTransportSection_injective (I := I) g p y hy (by simpa [radialTransportLinearMapAt] using hab)
    have hsurj : Function.Surjective (radialTransportLinearMapAt g p y) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K := ℝ) (V := E) (V₂ := E) rfl).mp hT
    exact ⟨hT, hsurj⟩)).symm_apply_apply v

noncomputable def radialTransportSectionTensor [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (p : M)
    (η₀ : Tensor04At (I := I) (M := M) p) : ∀ y : M, Tensor04At (I := I) (M := M) y := by
  classical
  exact fun y =>
    if h : y ∈ radialTransportSectionDomain (I := I) g p then
      η₀.compContinuousLinearMap (fun _ : Fin 4 => (radialTransportInverseAt g p y h : E →L[ℝ] E))
    else 0


set_option linter.unusedSectionVars false in
omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
@[nolint unusedArguments]
lemma mem_radialTransportSectionDomain_expMap
    (g : SmoothRiemannianMetric I M) (p : M)
    {X : TangentSpace I p} (hX : ‖(X : E)‖ < radialRadius (I := I) g p)
    {s : ℝ} (hs : s ∈ Set.Ioo (-1 : ℝ) 1) :
    expMap (I := I) g p (s • X) ∈ radialTransportSectionDomain (I := I) g p := by
  classical
  have hs_norm : ‖s • (X : E)‖ < expMapC2Radius (I := I) g p :=
    norm_smul_lt_expMapC2Radius_of_lt_radialRadius (I := I) g p hX ⟨hs.1.le, by linarith [hs.2]⟩
  have hs_rad : ‖s • (X : E)‖ < radialRadius (I := I) g p := by
    have hnorm : ‖s • (X : E)‖ ≤ ‖(X : E)‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      have habs : |s| ≤ 1 := by
        rw [abs_le]
        exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
      exact (mul_le_mul_of_nonneg_right habs (norm_nonneg (X : E))).trans_eq (one_mul _)
    exact lt_of_le_of_lt hnorm hX
  unfold radialTransportSectionDomain
  constructor
  · exact expMap_mem_normalChartAt_source_of_norm_lt_radialRadius (I := I) g p hs_norm
  · have hv : normalChartAt (I := I) g p (expMap (I := I) g p (s • X)) = s • (X : E) :=
      normalChartAt_expMap_smul (I := I) g p (X : E) s (ball_subset_normalChartAt_target
        (I := I) g p hs_norm)
    rw [hv]
    exact hs_rad

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
theorem radialTransportInverseAt_transport_eq
    (g : SmoothRiemannianMetric I M) (p : M)
    {X : TangentSpace I p} (hX : ‖(X : E)‖ < radialRadius (I := I) g p)
    {s : ℝ} (hs : s ∈ Set.Ioo (-1 : ℝ) 1)
    (v : E) :
    radialTransportInverseAt g p (expMap (I := I) g p (s • X))
      (mem_radialTransportSectionDomain_expMap (I := I) g p hX hs)
      (radialParallelTransportSection (I := I) g p hX v s) = v := by
  classical
  let y : M := expMap (I := I) g p (s • X)
  have hmem : y ∈ radialTransportSectionDomain (I := I) g p :=
    mem_radialTransportSectionDomain_expMap (I := I) g p hX hs
  have h := radialTransportInverseAt_left_inverse (I := I) g p y hmem v
  have hval : radialTransportLinearMapAt g p y v = radialParallelTransportSection (I := I) g p hX v s := by
    dsimp [radialTransportLinearMapAt, y]
    exact radialTransportSection_pullback_eq (I := I) g p v hX hs
  rw [hval] at h
  exact h

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
theorem radialTransportSectionTensor_initial
    (g : SmoothRiemannianMetric I M) (p : M)
    (η₀ : Tensor04At (I := I) (M := M) p) :
    radialTransportSectionTensor g p η₀ p = η₀ := by
  classical
  have hmem : p ∈ radialTransportSectionDomain (I := I) g p :=
    mem_radialTransportSectionDomain_self (I := I) g p
  rw [radialTransportSectionTensor]
  rw [dif_pos hmem]
  have hid : (radialTransportInverseAt g p p hmem : E →L[ℝ] E) = ContinuousLinearMap.id ℝ E := by
    ext v
    have hc : radialTransportSection g p v p = v :=
      radialTransportSection_center (I := I) g p v 0 (by
        rw [norm_zero]
        exact radialRadius_pos (I := I) g p)
    have hlin : radialTransportLinearMapAt g p p v = v := by
      simpa [radialTransportLinearMapAt] using hc
    have h := radialTransportInverseAt_left_inverse (I := I) g p p hmem v
    simpa [hlin] using h
  rw [hid]
  apply ContinuousMultilinearMap.ext
  intro v
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rfl

omit [CompleteSpace E] [IsManifold I ∞ M] [IsManifold I 2 M] [IsManifold I 3 M]
  [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] [NeZero (Module.finrank ℝ E)]
  [T2Space (TangentBundle I M)] in
private theorem tensor04Field_sum_apply
    {ι : Type*} [Fintype ι]
    (A : ι → Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := ∞) 4)
    (y : M) :
    (∑ i, A i) y = ∑ i, A i y := by
  let L :
      Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 4 →+
        ((z : M) → Tensor0SSpace 4 I z) :=
    { toFun := fun B z => B z
      map_zero' := by rfl
      map_add' := by intro B C; rfl }
  have h := congrFun (map_sum L A Finset.univ) y
  change (∑ i, A i) y = (∑ i, fun z => A i z) y at h
  rw [Finset.sum_apply] at h
  exact h

noncomputable def radialTransportTensorExtension
    (g : SmoothRiemannianMetric I M) (p : M)
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I p))
    (η₀ : Tensor04At (I := I) (M := M) p)
    (W : Fin 3 → ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) :
    Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 4 :=
  ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
    η₀ (fun a => basis (slots4 i j k l a)) •
      metricFormSection (I := I) (M := M) g 4 (fun a => W (slots4 i j k l a))

omit [CompleteSpace E] [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M]
  [T2Space M] [I.Boundaryless] [NeZero (Module.finrank ℝ E)]
  [T2Space (TangentBundle I M)] in
theorem radialTransportTensorExtension_apply
    (g : SmoothRiemannianMetric I M) (p : M)
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I p))
    (η₀ : Tensor04At (I := I) (M := M) p)
    (W : Fin 3 → ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (y : M) (v : Fin 4 → TangentSpace I y) :
    radialTransportTensorExtension g p basis η₀ W y v =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
        η₀ (fun a => basis (slots4 i j k l a)) *
          ∏ a : Fin 4, g.inner y (W (slots4 i j k l a) y) (v a) := by
  rw [radialTransportTensorExtension, tensor04Field_sum_apply, tensor0SSpace_sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [tensor04Field_sum_apply, tensor0SSpace_sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [tensor04Field_sum_apply, tensor0SSpace_sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [tensor04Field_sum_apply, tensor0SSpace_sum_apply]
  apply Finset.sum_congr rfl
  intro l _
  change (η₀ (fun a => basis (slots4 i j k l a)) •
    metricFormSection (I := I) (M := M) g 4
      (fun a => W (slots4 i j k l a)) y) v = _
  rw [Tensor0SSpace.smul_apply]
  change η₀ (fun a => basis (slots4 i j k l a)) * Tensor0SSpace.toModel
    (metricFormSection (I := I) (M := M) g 4
      (fun a => W (slots4 i j k l a)) y) v = _
  rw [toModel_metricFormSection,
    DifferentialGeometry.Integral.L2.separableFormAt_apply]

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
theorem radialTransportSectionTensor_apply_eq_sum
    (g : SmoothRiemannianMetric I M) (p : M)
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I p))
    (horth : OrthonormalBasisAt (I := I) g p basis)
    (η₀ : Tensor04At (I := I) (M := M) p) (y : M)
    (hy : y ∈ radialTransportSectionDomain (I := I) g p)
    (v : Fin 4 → TangentSpace I y) :
    radialTransportSectionTensor g p η₀ y v =
      ∑ J : Fin 4 → Fin 3,
        η₀ (fun a => basis (J a)) *
          ∏ a : Fin 4, g.inner y
            (radialTransportSection (I := I) g p (basis (J a)) y) (v a) := by
  classical
  let T : E ≃ₗ[ℝ] E := LinearEquiv.ofBijective (radialTransportLinearMapAt g p y) (by
    have hT : Function.Injective (radialTransportLinearMapAt g p y) := by
      intro a b hab
      exact radialTransportSection_injective (I := I) g p y hy
        (by simpa [radialTransportLinearMapAt] using hab)
    have hsurj : Function.Surjective (radialTransportLinearMapAt g p y) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (K := ℝ) (V := E) (V₂ := E) rfl).mp hT
    exact ⟨hT, hsurj⟩)
  let basisY : Module.Basis (Fin 3) ℝ (TangentSpace I y) := basis.map T
  have horthY : OrthonormalBasisAt (I := I) g y basisY := by
    intro a b
    have hinner := radialTransportSection_inner_eq (I := I) g p (basis a) (basis b) y hy
    have hTa : (basisY a : TangentSpace I y) =
        radialTransportSection (I := I) g p (basis a) y := by
      dsimp [basisY]
      change (T (basis a) : TangentSpace I y) = _
      rfl
    have hTb : (basisY b : TangentSpace I y) =
        radialTransportSection (I := I) g p (basis b) y := by
      dsimp [basisY]
      change (T (basis b) : TangentSpace I y) = _
      rfl
    rw [hTa, hTb]
    simpa [horth a b] using hinner
  rw [tensor0S_apply_eq_sum (I := I) basisY (radialTransportSectionTensor g p η₀ y) v]
  apply Finset.sum_congr rfl
  intro J _
  have hcoeff : radialTransportSectionTensor g p η₀ y (fun a => basisY (J a)) =
      η₀ (fun a => basis (J a)) := by
    rw [radialTransportSectionTensor, dif_pos hy]
    change η₀ (fun a => radialTransportInverseAt g p y hy (basisY (J a))) = _
    congr 1
    funext a
    change radialTransportInverseAt g p y hy
        (radialTransportLinearMapAt g p y (basis (J a))) = basis (J a)
    exact radialTransportInverseAt_left_inverse (I := I) g p y hy (basis (J a))
  rw [component0S_apply, hcoeff]
  congr 1
  apply Finset.prod_congr rfl
  intro a _
  have hinv : MetricInverseInBasis (I := I) g y basisY
      (identityInvMetric (Idx := Fin 3)) :=
    fiberRegion_metricInverseInBasis_identity_of_orthonormal (I := I) g basisY horthY
  rw [DifferentialGeometry.Geometry.Curvature.basis_coord_eq_sum_inv_inner
    (I := I) g basisY (identityInvMetric (Idx := Fin 3)) hinv]
  rw [Finset.sum_eq_single (J a)]
  · rw [identityInvMetric_apply_self, one_mul]
    rfl
  · intro b _ hba
    rw [identityInvMetric, diagonalInvMetric_eq_zero_of_ne hba.symm, zero_mul]
  · intro ha
    exact absurd (Finset.mem_univ (J a)) ha

private def fin4SlotsEquiv : (Fin 4 → Fin 3) ≃ (((Fin 3 × Fin 3) × Fin 3) × Fin 3) where
  toFun f := (((f 0, f 1), f 2), f 3)
  invFun p := slots4 p.1.1.1 p.1.1.2 p.1.2 p.2
  left_inv f := by
    funext a
    fin_cases a <;> simp [slots4]
  right_inv p := by
    rcases p with ⟨⟨⟨i, j⟩, k⟩, l⟩
    simp [slots4]

private lemma sum_fin_four_fun {α : Type*} [AddCommMonoid α]
    (F : (Fin 4 → Fin 3) → α) :
    (∑ I0 : Fin 4 → Fin 3, F I0) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
        F (slots4 i j k l) := by
  classical
  rw [Fintype.sum_equiv fin4SlotsEquiv F
    (fun p : (((Fin 3 × Fin 3) × Fin 3) × Fin 3) =>
      F (slots4 p.1.1.1 p.1.1.2 p.1.2 p.2))]
  · repeat rw [Fintype.sum_prod_type]
  · intro I0
    congr
    funext a
    fin_cases a <;> simp [fin4SlotsEquiv, slots4]

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
theorem radialTransportTensorExtension_eq_smul
    (g : SmoothRiemannianMetric I M) (p : M)
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I p))
    (horth : OrthonormalBasisAt (I := I) g p basis)
    (η₀ : Tensor04At (I := I) (M := M) p)
    (χ : SmoothBumpFunction I p)
    (W : Fin 3 → ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (hsupport : tsupport (χ : M → ℝ) ⊆ radialTransportSectionDomain (I := I) g p)
    (hW : ∀ i y, W i y = χ y • radialTransportSection (I := I) g p (basis i) y)
    (y : M) :
    radialTransportTensorExtension g p basis η₀ W y =
      (χ y) ^ 4 • radialTransportSectionTensor g p η₀ y := by
  classical
  apply tensor0SSpace_ext
  intro v
  rw [radialTransportTensorExtension_apply, Tensor0SSpace.smul_apply]
  by_cases hχ : χ y = 0
  · simp_rw [hW]
    simp [hχ]
  · have hySupport : y ∈ Function.support (χ : M → ℝ) := hχ
    have hyTsupport : y ∈ tsupport (χ : M → ℝ) := subset_closure hySupport
    have hy : y ∈ radialTransportSectionDomain (I := I) g p := hsupport hyTsupport
    rw [radialTransportSectionTensor_apply_eq_sum g p basis horth η₀ y hy v]
    rw [sum_fin_four_fun]
    simp_rw [hW, map_smul (g.inner y), ContinuousLinearMap.smul_apply, smul_eq_mul,
      Fin.prod_univ_four]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
theorem radialTransportTensorExtension_eventually_eq
    (g : SmoothRiemannianMetric I M) (p : M)
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I p))
    (horth : OrthonormalBasisAt (I := I) g p basis)
    (η₀ : Tensor04At (I := I) (M := M) p)
    (χ : SmoothBumpFunction I p)
    (W : Fin 3 → ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (hsupport : tsupport (χ : M → ℝ) ⊆ radialTransportSectionDomain (I := I) g p)
    (hW : ∀ i y, W i y = χ y • radialTransportSection (I := I) g p (basis i) y) :
    ∀ᶠ y in 𝓝 p,
      radialTransportTensorExtension g p basis η₀ W y =
        radialTransportSectionTensor g p η₀ y := by
  filter_upwards [χ.eventuallyEq_one] with y hy
  rw [radialTransportTensorExtension_eq_smul g p basis horth η₀ χ W hsupport hW y]
  simp [hy]

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
theorem radialTransportTensorExtension_initial
    (g : SmoothRiemannianMetric I M) (p : M)
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I p))
    (horth : OrthonormalBasisAt (I := I) g p basis)
    (η₀ : Tensor04At (I := I) (M := M) p)
    (χ : SmoothBumpFunction I p)
    (W : Fin 3 → ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (hsupport : tsupport (χ : M → ℝ) ⊆ radialTransportSectionDomain (I := I) g p)
    (hW : ∀ i y, W i y = χ y • radialTransportSection (I := I) g p (basis i) y) :
    radialTransportTensorExtension g p basis η₀ W p = η₀ := by
  rw [radialTransportTensorExtension_eq_smul g p basis horth η₀ χ W hsupport hW p,
    χ.eq_one, one_pow, one_smul, radialTransportSectionTensor_initial]

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
theorem radialTransportSectionTensor_inner_eq
    (g : SmoothRiemannianMetric I M) (p : M)
    (hdim : Module.finrank Real (TangentSpace I p) = 3)
    (A B : Tensor04At (I := I) (M := M) p) (y : M)
    (hy : y ∈ radialTransportSectionDomain (I := I) g p) :
    inner0S (I := I) g y 4 (radialTransportSectionTensor g p A y)
        (radialTransportSectionTensor g p B y) =
      inner0S (I := I) g p 4 A B := by
  classical
  let basis₀ : Module.Basis (Fin 3) Real (TangentSpace I p) :=
    Classical.choose (exists_orthonormalBasisAt (I := I) g p hdim)
  have horth₀ : OrthonormalBasisAt (I := I) g p basis₀ :=
    Classical.choose_spec (exists_orthonormalBasisAt (I := I) g p hdim)
  let T : E ≃ₗ[ℝ] E := LinearEquiv.ofBijective (radialTransportLinearMapAt g p y) (by
    have hT : Function.Injective (radialTransportLinearMapAt g p y) := by
      intro a b hab
      exact radialTransportSection_injective (I := I) g p y hy (by simpa [radialTransportLinearMapAt] using hab)
    have hsurj : Function.Surjective (radialTransportLinearMapAt g p y) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K := ℝ) (V := E) (V₂ := E) rfl).mp hT
    exact ⟨hT, hsurj⟩)
  let basisY : Module.Basis (Fin 3) Real (TangentSpace I y) := basis₀.map T
  have horthY : OrthonormalBasisAt (I := I) g y basisY := by
    intro a b
    have hinner := radialTransportSection_inner_eq (I := I) g p (basis₀ a) (basis₀ b) y hy
    have hTa : (basisY a : TangentSpace I y) = radialTransportSection g p (basis₀ a) y := by
      dsimp [basisY]
      change (T (basis₀ a) : TangentSpace I y) = radialTransportSection g p (basis₀ a) y
      dsimp [T]
      rfl
    have hTb : (basisY b : TangentSpace I y) = radialTransportSection g p (basis₀ b) y := by
      dsimp [basisY]
      change (T (basis₀ b) : TangentSpace I y) = radialTransportSection g p (basis₀ b) y
      dsimp [T]
      rfl
    rw [hTa, hTb]
    simpa [horth₀ a b] using hinner
  have hcomponent : ∀ C : Tensor04At (I := I) (M := M) p, ∀ J : Fin 4 → Fin 3,
      (radialTransportSectionTensor g p C y) (fun a => basisY (J a)) =
        C (fun a => basis₀ (J a)) := by
    intro C J
    rw [radialTransportSectionTensor]
    rw [dif_pos hy]
    have hTval : ∀ a : Fin 4,
        (basisY (J a) : E) = radialTransportLinearMapAt g p y (basis₀ (J a)) := by
      intro a
      dsimp [basisY]
      change (T (basis₀ (J a)) : E) = radialTransportLinearMapAt g p y (basis₀ (J a))
      dsimp [T]
    change C (fun a => radialTransportInverseAt g p y hy (basisY (J a))) =
      C (fun a => basis₀ (J a))
    congr 1
    funext a
    rw [hTval a]
    exact radialTransportInverseAt_left_inverse (I := I) g p y hy (basis₀ (J a))
  rw [inner0S_four_orthonormalBasis_sq (I := I) g y basisY horthY
    (radialTransportSectionTensor g p A y) (radialTransportSectionTensor g p B y)]
  rw [inner0S_four_orthonormalBasis_sq (I := I) g p basis₀ horth₀ A B]
  apply Finset.sum_congr rfl
  intro J _
  rw [hcomponent A J, hcomponent B J]

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
theorem radialTransportSectionTensor_isometry
    (g : SmoothRiemannianMetric I M) (p : M)
    (hdim : Module.finrank Real (TangentSpace I p) = 3)
    (η₀ : Tensor04At (I := I) (M := M) p) (y : M)
    (hy : y ∈ radialTransportSectionDomain (I := I) g p) :
    inner0S (I := I) g y 4 (radialTransportSectionTensor g p η₀ y)
        (radialTransportSectionTensor g p η₀ y) =
      inner0S (I := I) g p 4 η₀ η₀ :=
  radialTransportSectionTensor_inner_eq (I := I) g p hdim η₀ η₀ y hy

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
theorem fiberProjW_radialTransport_commute
    (g : SmoothRiemannianMetric I M) (p : M)
    (hdim : Module.finrank Real (TangentSpace I p) = 3)
    (A : Tensor04At (I := I) (M := M) p) (y : M)
    (hy : y ∈ radialTransportSectionDomain (I := I) g p) :
    (fiberProjW (I := I) g y (radialTransportSectionTensor g p A y) :
        Tensor04At (I := I) (M := M) y) =
      radialTransportSectionTensor g p
        (fiberProjW (I := I) g p A : Tensor04At (I := I) (M := M) p) y := by
  classical
  let Tlin : E →ₗ[ℝ] E := radialTransportLinearMapAt g p y
  have hTbij : Function.Bijective Tlin := by
    have hTinj : Function.Injective Tlin := by
      intro a b hab
      exact radialTransportSection_injective (I := I) g p y hy
        (by simpa [Tlin, radialTransportLinearMapAt] using hab)
    have hTsurj : Function.Surjective Tlin :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (K := ℝ) (V := E) (V₂ := E) rfl).mp hTinj
    exact ⟨hTinj, hTsurj⟩
  let e : E ≃ₗ[ℝ] E := LinearEquiv.ofBijective Tlin hTbij
  let T : E →L[ℝ] E := e.toContinuousLinearEquiv.toContinuousLinearMap
  let Tinv : E →L[ℝ] E := radialTransportInverseAt g p y hy
  have hTinvT : ∀ v : TangentSpace I p, Tinv (T v) = v := by
    intro v
    change radialTransportInverseAt g p y hy (radialTransportLinearMapAt g p y v) = v
    exact radialTransportInverseAt_left_inverse (I := I) g p y hy v
  have hTTinv : ∀ v : TangentSpace I y, T (Tinv v) = v := by
    intro v
    obtain ⟨w, rfl⟩ := hTbij.2 v
    change T (Tinv (T w)) = T w
    rw [hTinvT]
  let pY : algebraicCurvatureTensorSubmodule (I := I) (M := M) y :=
    fiberProjW (I := I) g y (radialTransportSectionTensor g p A y)
  let p0 : algebraicCurvatureTensorSubmodule (I := I) (M := M) p :=
    fiberProjW (I := I) g p A
  have hp0transport : radialTransportSectionTensor g p
        (p0 : Tensor04At (I := I) (M := M) p) y ∈
      algebraicCurvatureTensorSubmodule (I := I) (M := M) y := by
    rw [radialTransportSectionTensor, dif_pos hy]
    exact compLinearMap_mem_algebraicCurvatureTensorSubmodule (I := I) Tinv p0
  let uY : algebraicCurvatureTensorSubmodule (I := I) (M := M) y :=
    ⟨radialTransportSectionTensor g p
      (p0 : Tensor04At (I := I) (M := M) p) y, hp0transport⟩
  have hchar : ∀ q : algebraicCurvatureTensorSubmodule (I := I) (M := M) y,
      inner0S (I := I) g y 4 (pY : Tensor04At (I := I) (M := M) y) q =
        inner0S (I := I) g y 4 (uY : Tensor04At (I := I) (M := M) y) q := by
    intro q
    let q0 : algebraicCurvatureTensorSubmodule (I := I) (M := M) p := ⟨
      (q : Tensor04At (I := I) (M := M) y).compContinuousLinearMap
        (fun _ : Fin 4 => T),
      compLinearMap_mem_algebraicCurvatureTensorSubmodule (I := I) T q⟩
    have hqtransport : radialTransportSectionTensor g p
        (q0 : Tensor04At (I := I) (M := M) p) y =
        (q : Tensor04At (I := I) (M := M) y) := by
      rw [radialTransportSectionTensor, dif_pos hy]
      apply tensor0SSpace_ext 4 y
      intro v
      change (q : Tensor04At (I := I) (M := M) y)
        (fun i => T (Tinv (v i))) = (q : Tensor04At (I := I) (M := M) y) v
      congr 1
      funext i
      exact hTTinv (v i)
    calc
      inner0S (I := I) g y 4 (pY : Tensor04At (I := I) (M := M) y) q
          = inner0S (I := I) g y 4 (radialTransportSectionTensor g p A y)
              (q : Tensor04At (I := I) (M := M) y) := by
                exact fiberProjW_spec (I := I) g y (radialTransportSectionTensor g p A y) q
      _ = inner0S (I := I) g y 4 (radialTransportSectionTensor g p A y)
              (radialTransportSectionTensor g p
                (q0 : Tensor04At (I := I) (M := M) p) y) := by rw [hqtransport]
      _ = inner0S (I := I) g p 4 A (q0 : Tensor04At (I := I) (M := M) p) :=
            radialTransportSectionTensor_inner_eq (I := I) g p hdim A q0 y hy
      _ = inner0S (I := I) g p 4 (p0 : Tensor04At (I := I) (M := M) p) q0 := by
            exact (fiberProjW_spec (I := I) g p A q0).symm
      _ = inner0S (I := I) g y 4
              (radialTransportSectionTensor g p
                (p0 : Tensor04At (I := I) (M := M) p) y)
              (radialTransportSectionTensor g p
                (q0 : Tensor04At (I := I) (M := M) p) y) :=
            (radialTransportSectionTensor_inner_eq (I := I) g p hdim p0 q0 y hy).symm
      _ = inner0S (I := I) g y 4 (uY : Tensor04At (I := I) (M := M) y) q := by
            rw [hqtransport]
  have hdiff : ∀ q : algebraicCurvatureTensorSubmodule (I := I) (M := M) y,
      inner0S (I := I) g y 4
        ((pY - uY : algebraicCurvatureTensorSubmodule (I := I) (M := M) y) :
          Tensor04At (I := I) (M := M) y) q = 0 := by
    intro q
    rw [show ((pY - uY : algebraicCurvatureTensorSubmodule (I := I) (M := M) y) :
        Tensor04At (I := I) (M := M) y) =
      (pY : Tensor04At (I := I) (M := M) y) -
        (uY : Tensor04At (I := I) (M := M) y) by rfl]
    rw [inner0S_sub_left (I := I) g y 4]
    exact sub_eq_zero.mpr (hchar q)
  have hself := hdiff (pY - uY)
  have hzero : ((pY - uY : algebraicCurvatureTensorSubmodule (I := I) (M := M) y) :
      Tensor04At (I := I) (M := M) y) = 0 := by
    exact ((tensor0SMetricData (I := I) g y 4).inner_self_eq_zero_iff
      (((pY - uY : algebraicCurvatureTensorSubmodule (I := I) (M := M) y) :
        Tensor04At (I := I) (M := M) y))).mp hself
  have hpu : pY = uY := by
    apply Subtype.ext
    exact sub_eq_zero.mp hzero
  exact congrArg Subtype.val hpu

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
private theorem radialTransportTensorExtension_regionProjMatrix_eq_conj
    (g : SmoothRiemannianMetric I M) (p : M)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I p))
    (horth : OrthonormalBasisAt (I := I) g p basis)
    (η₀ : Tensor04At (I := I) (M := M) p)
    (χ : SmoothBumpFunction I p)
    (W : Fin 3 → ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (hsupport : tsupport (χ : M → Real) ⊆ radialTransportSectionDomain (I := I) g p)
    (hW : ∀ i y, W i y = χ y • radialTransportSection (I := I) g p (basis i) y)
    (y : M) (hy : y ∈ radialTransportSectionDomain (I := I) g p)
    (basis' : Module.Basis (Fin 3) Real (TangentSpace I y))
    (horth' : OrthonormalBasisAt (I := I) g y basis') :
    ∃ O : Matrix (Fin 3) (Fin 3) Real,
      O * O.transpose = 1 ∧
      regionProjMatrix (I := I) g basis'
          (radialTransportTensorExtension g p basis η₀ W y) =
        (χ y) ^ 4 •
          (O.transpose * regionProjMatrix (I := I) g basis η₀ * O) := by
  classical
  let Tlin : E →ₗ[Real] E := radialTransportLinearMapAt g p y
  have hTbij : Function.Bijective Tlin := by
    have hTinj : Function.Injective Tlin := by
      intro a b hab
      exact radialTransportSection_injective (I := I) g p y hy
        (by simpa [Tlin, radialTransportLinearMapAt] using hab)
    have hTsurj : Function.Surjective Tlin :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (K := Real) (V := E) (V₂ := E) rfl).mp hTinj
    exact ⟨hTinj, hTsurj⟩
  let e : E ≃ₗ[Real] E := LinearEquiv.ofBijective Tlin hTbij
  let basisY : Module.Basis (Fin 3) Real (TangentSpace I y) := basis.map e
  have horthY : OrthonormalBasisAt (I := I) g y basisY := by
    intro a b
    have hinner := radialTransportSection_inner_eq (I := I) g p (basis a) (basis b) y hy
    have hTa : (basisY a : TangentSpace I y) =
        radialTransportSection (I := I) g p (basis a) y := by
      dsimp [basisY]
      change (e (basis a) : TangentSpace I y) = _
      rfl
    have hTb : (basisY b : TangentSpace I y) =
        radialTransportSection (I := I) g p (basis b) y := by
      dsimp [basisY]
      change (e (basis b) : TangentSpace I y) = _
      rfl
    rw [hTa, hTb]
    simpa [horth a b] using hinner
  let O : Matrix (Fin 3) (Fin 3) Real :=
    intrinsicFrameChangeMatrix (I := I) g basisY basis'
  have hO : O * O.transpose = 1 :=
    intrinsicFrameChangeMatrix_orthogonal (I := I) (M := M) g basisY basis' horthY horth'
  refine ⟨O, hO, ?_⟩
  let A₀ : algebraicCurvatureTensorSubmodule (I := I) (M := M) p :=
    fiberProjW (I := I) g p η₀
  let AY : algebraicCurvatureTensorSubmodule (I := I) (M := M) y :=
    fiberProjW (I := I) g y (radialTransportSectionTensor g p η₀ y)
  have hAY : (AY : Tensor04At (I := I) (M := M) y) =
      radialTransportSectionTensor g p
        (A₀ : Tensor04At (I := I) (M := M) p) y := by
    exact fiberProjW_radialTransport_commute (I := I) g p
      (Module.finrank_eq_card_basis basis) η₀ y hy
  have hmatrixY : curvatureOperatorMatrixAt (I := I) y basisY AY =
      curvatureOperatorMatrixAt (I := I) p basis A₀ := by
    ext i j
    rw [show curvatureOperatorMatrixAt (I := I) y basisY AY i j =
        intrinsicFiberCurvatureOperatorMatrix (I := I) basisY
          (AY : Tensor04At (I := I) (M := M) y) i j by rfl]
    rw [hAY]
    simp only [intrinsicFiberCurvatureOperatorMatrix_apply]
    rw [radialTransportSectionTensor, dif_pos hy]
    change (A₀ : Tensor04At (I := I) (M := M) p)
        (fun a ↦ radialTransportInverseAt g p y hy
          (vec4 (basisY (bivectorIndex3 i).1) (basisY (bivectorIndex3 i).2)
            (basisY (bivectorIndex3 j).2) (basisY (bivectorIndex3 j).1) a)) =
      (A₀ : Tensor04At (I := I) (M := M) p)
        (vec4 (basis (bivectorIndex3 i).1) (basis (bivectorIndex3 i).2)
          (basis (bivectorIndex3 j).2) (basis (bivectorIndex3 j).1))
    congr 1
    funext a
    fin_cases a <;>
      change radialTransportInverseAt g p y hy
        (radialTransportLinearMapAt g p y _) = _ <;>
      exact radialTransportInverseAt_left_inverse (I := I) g p y hy _
  have hconj : curvatureOperatorMatrixAt (I := I) y basis' AY =
      O.transpose * curvatureOperatorMatrixAt (I := I) y basisY AY * O := by
    simpa [O] using intrinsicFiberCurvatureOperatorMatrix_conj_of_orthonormal
      (I := I) (M := M) g basisY basis' horthY AY
  rw [radialTransportTensorExtension_eq_smul g p basis horth η₀ χ W hsupport hW y]
  unfold regionProjMatrix
  have hproj := fiberProjW_smul (I := I) g y ((χ y) ^ 4)
    (radialTransportSectionTensor g p η₀ y)
  ext i j
  change tensor04StdAt (I := I) (M := M)
      (fiberProjW (I := I) g y
        ((χ y) ^ 4 • radialTransportSectionTensor g p η₀ y) :
          Tensor04At (I := I) (M := M) y) _ _ _ _ = _
  rw [hproj]
  change (χ y) ^ 4 * curvatureOperatorMatrixAt (I := I) y basis' AY i j = _
  rw [hconj, hmatrixY]
  rfl

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
theorem radialTransportTensorExtension_inner_self_le
    (g : SmoothRiemannianMetric I M) (p : M)
    (hdim : Module.finrank ℝ (TangentSpace I p) = 3)
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I p))
    (horth : OrthonormalBasisAt (I := I) g p basis)
    (η₀ : Tensor04At (I := I) (M := M) p)
    (χ : SmoothBumpFunction I p)
    (W : Fin 3 → ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (hsupport : tsupport (χ : M → ℝ) ⊆ radialTransportSectionDomain (I := I) g p)
    (hW : ∀ i y, W i y = χ y • radialTransportSection (I := I) g p (basis i) y)
    (y : M) :
    inner0S (I := I) g y 4 (radialTransportTensorExtension g p basis η₀ W y)
        (radialTransportTensorExtension g p basis η₀ W y) ≤
      inner0S (I := I) g p 4 η₀ η₀ := by
  classical
  rw [radialTransportTensorExtension_eq_smul g p basis horth η₀ χ W hsupport hW y]
  by_cases hχ : χ y = 0
  · have hinner : 0 ≤ inner0S (I := I) g p 4 η₀ η₀ :=
      MetricFiberData.inner_nonneg (tensor0SMetricData (I := I) g p 4) η₀
    simpa [hχ, inner0S, MetricFiberData.inner] using hinner
  · have hySupport : y ∈ Function.support (χ : M → ℝ) := hχ
    have hyTsupport : y ∈ tsupport (χ : M → ℝ) := subset_closure hySupport
    have hy : y ∈ radialTransportSectionDomain (I := I) g p := hsupport hyTsupport
    let c : ℝ := (χ y) ^ 4
    have hscale : inner0S (I := I) g y 4
          (c • radialTransportSectionTensor g p η₀ y)
          (c • radialTransportSectionTensor g p η₀ y) =
        c * c * inner0S (I := I) g y 4
          (radialTransportSectionTensor g p η₀ y)
          (radialTransportSectionTensor g p η₀ y) := by
      unfold inner0S MetricFiberData.inner
      simp [map_smul, smul_eq_mul]
      ring
    rw [show (χ y) ^ 4 = c by rfl, hscale,
      radialTransportSectionTensor_isometry (I := I) g p hdim η₀ y hy]
    have hc0 : 0 ≤ c := pow_nonneg (χ.nonneg : 0 ≤ χ y) 4
    have hc1 : c ≤ 1 := by
      dsimp [c]
      exact pow_le_one₀ (χ.nonneg : 0 ≤ χ y) (χ.le_one : χ y ≤ 1)
    have hcc : c * c ≤ 1 := by nlinarith
    have hinner : 0 ≤ inner0S (I := I) g p 4 η₀ η₀ :=
      MetricFiberData.inner_nonneg (tensor0SMetricData (I := I) g p 4) η₀
    calc
      c * c * inner0S (I := I) g p 4 η₀ η₀ ≤
          1 * inner0S (I := I) g p 4 η₀ η₀ :=
        mul_le_mul_of_nonneg_right hcc hinner
      _ = inner0S (I := I) g p 4 η₀ η₀ := one_mul _

omit [IsManifold I 2 M] [IsManifold I 3 M]
  [SigmaCompactSpace M] in
private theorem localizedRadialTransportSection_nabla_center_zero
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p)
    (W : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (hW : (fun y => W y) =ᶠ[𝓝 p] radialTransportSection (I := I) g p v)
    (X : TangentSpace I p) :
    (LeviCivita (I := I) g).toFun (fun y => W y) p X = 0 := by
  have hWtotal : (T% fun y => W y) =ᶠ[𝓝 p]
      (T% fun y => radialTransportSection (I := I) g p v y) := by
    filter_upwards [hW] with y hy
    rw [hy]
  have hRsm : ContMDiffAt I I.tangent ∞
      (T% fun y => radialTransportSection (I := I) g p v y) p :=
    W.contMDiff.contMDiffAt.congr_of_eventuallyEq hWtotal.symm
  have hWmd : MDiffAt (T% fun y => W y) p :=
    W.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hRmd : MDiffAt (T% fun y => radialTransportSection (I := I) g p v y) p :=
    hRsm.mdifferentiableAt (by simp)
  have heq := (LeviCivita (I := I) g).isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    hWmd hRmd Filter.univ_mem hW
  rw [heq]
  exact radialTransportSection_nabla_center_zero (I := I) g p v X hRmd

omit [IsManifold I 2 M] [IsManifold I 3 M]
  [SigmaCompactSpace M] in
private theorem localizedRadialTransportSection_nabla2_center_zero
    (g : SmoothRiemannianMetric I M) (p : M) (v w : TangentSpace I p)
    (W : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (hW : (fun y => W y) =ᶠ[𝓝 p] radialTransportSection (I := I) g p v) :
    (LeviCivita (I := I) g).toFun
      (covApply (LeviCivita (I := I) g) (linearExtensionTangent (I := I) p w)
        (fun y => W y)) p w = 0 := by
  let X := linearExtensionTangent (I := I) p w
  let R := radialTransportSection (I := I) g p v
  let D := covApply (LeviCivita (I := I) g) X (fun y => W y)
  let D0 := fun y => (LeviCivita (I := I) g).toFun R y
    (coordExtensionTangent (I := I) p w y)
  have hWtotal : (T% fun y => W y) =ᶠ[𝓝 p] (T% fun y => R y) := by
    filter_upwards [hW] with y hy
    rw [hy]
  have hRsm : ContMDiffAt I I.tangent ∞ (T% fun y => R y) p :=
    W.contMDiff.contMDiffAt.congr_of_eventuallyEq hWtotal.symm
  have hXsm : ContMDiff I I.tangent ∞ (T% X) :=
    linearExtensionTangent_smooth (I := I) p w
  have hDsm : ContMDiff I I.tangent ∞ (T% D) := by
    rw [← contMDiffOn_univ]
    apply covApply_contMDiffOn (cov := LeviCivita (I := I) g) hXsm
    rw [show ((∞ : WithTop ℕ∞) + 1) = ∞ by rw [ENat.coe_top_add_one]]
    exact W.contMDiff
  have hXeq : X =ᶠ[𝓝 p] coordExtensionTangent (I := I) p w := by
    filter_upwards [(linExtBump (I := I) p).eventuallyEq_one] with y hy
    simp [X, linearExtensionTangent_apply, hy]
  have hEqSet : {y : M | W y = R y} ∈ 𝓝 p := by
    simpa only [R] using hW
  obtain ⟨U, hUsub, hUopen, hpU⟩ := mem_nhds_iff.mp hEqSet
  have hUnhds : U ∈ 𝓝 p := hUopen.mem_nhds hpU
  have hD : D =ᶠ[𝓝 p] D0 := by
    filter_upwards [hUnhds, hXeq] with y hyU hXy
    have hWRy : (fun z => W z) =ᶠ[𝓝 y] R := by
      filter_upwards [hUopen.mem_nhds hyU] with z hz
      exact hUsub hz
    have hWRtotal_y : (T% fun z => W z) =ᶠ[𝓝 y] (T% fun z => R z) := by
      filter_upwards [hWRy] with z hz
      rw [hz]
    have hWmd_y : MDiffAt (T% fun z => W z) y :=
      W.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
    have hRsm_y : ContMDiffAt I I.tangent ∞ (T% fun z => R z) y :=
      W.contMDiff.contMDiffAt.congr_of_eventuallyEq hWRtotal_y.symm
    have hRmd_y : MDiffAt (T% fun z => R z) y :=
      hRsm_y.mdifferentiableAt (by simp)
    have hcov_y := (LeviCivita (I := I) g).isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      hWmd_y hRmd_y Filter.univ_mem hWRy
    simp only [D, D0, covApply_apply]
    rw [hcov_y, hXy]
  have hDtotal : (T% D) =ᶠ[𝓝 p] (T% D0) := by
    filter_upwards [hD] with y hy
    rw [hy]
  have hD0sm : ContMDiffAt I I.tangent ∞ (T% D0) p :=
    hDsm.contMDiffAt.congr_of_eventuallyEq hDtotal.symm
  have hDmd : MDiffAt (T% D) p :=
    hDsm.contMDiffAt.mdifferentiableAt (by simp)
  have hD0md : MDiffAt (T% D0) p := hD0sm.mdifferentiableAt (by simp)
  have heq := (LeviCivita (I := I) g).isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    hDmd hD0md Filter.univ_mem hD
  change (LeviCivita (I := I) g).toFun D p w = 0
  rw [heq]
  exact radialTransportSection_nabla2_center_zero (I := I) g p v w hRsm

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
private theorem radialTransportTensorExtension_eval_eventually_eq
    (g : SmoothRiemannianMetric I M) (p : M)
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I p))
    (horth : OrthonormalBasisAt (I := I) g p basis)
    (η₀ : Tensor04At (I := I) (M := M) p)
    (χ : SmoothBumpFunction I p)
    (W : Fin 3 → ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (hsupport : tsupport (χ : M → ℝ) ⊆ radialTransportSectionDomain (I := I) g p)
    (hW : ∀ i y, W i y = χ y • radialTransportSection (I := I) g p (basis i) y)
    (J : Fin 4 → Fin 3) :
    (fun y => radialTransportTensorExtension g p basis η₀ W y
      (fun a => W (J a) y)) =ᶠ[𝓝 p]
      fun _ => η₀ (fun a => basis (J a)) := by
  have hA := radialTransportTensorExtension_eventually_eq
    (I := I) g p basis horth η₀ χ W hsupport hW
  have hD : radialTransportSectionDomain (I := I) g p ∈ 𝓝 p :=
    (radialTransportSectionDomain_isOpen (I := I) g p).mem_nhds
      (mem_radialTransportSectionDomain_self (I := I) g p)
  filter_upwards [hA, χ.eventuallyEq_one, hD] with y hAy hχy hy
  simp only [Pi.one_apply] at hχy
  rw [hAy, radialTransportSectionTensor, dif_pos hy]
  change η₀ (fun a => radialTransportInverseAt g p y hy (W (J a) y)) = _
  congr 1
  funext a
  rw [hW, hχy, one_smul]
  change radialTransportInverseAt g p y hy
      (radialTransportLinearMapAt g p y (basis (J a))) = basis (J a)
  exact radialTransportInverseAt_left_inverse (I := I) g p y hy (basis (J a))

omit [IsManifold I 3 M] [SigmaCompactSpace M] in
theorem radialTransportTensorExtension_nabla_center_zero
    (g : SmoothRiemannianMetric I M) (p : M)
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I p))
    (horth : OrthonormalBasisAt (I := I) g p basis)
    (η₀ : Tensor04At (I := I) (M := M) p)
    (χ : SmoothBumpFunction I p)
    (W : Fin 3 → ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (hsupport : tsupport (χ : M → ℝ) ⊆ radialTransportSectionDomain (I := I) g p)
    (hW : ∀ i y, W i y = χ y • radialTransportSection (I := I) g p (basis i) y)
    (d : CanonicalSpatialDerivs0S (I := I) (M := M) (LeviCivita (I := I) g)
      (radialTransportTensorExtension g p basis η₀ W)) :
    d.nablaA p = 0 := by
  apply ext0S_basis (I := I) basis
  intro idx
  change d.nablaA p (fun a => basis (idx a)) = 0
  let X : ContMDiffSection I E ∞ (TangentSpace I : M → Type _) := W (idx 0)
  let V : Fin 4 → ContMDiffSection I E ∞ (TangentSpace I : M → Type _) :=
    fun a => W (idx a.succ)
  have hWp : ∀ i : Fin 3, W i p = basis i := by
    intro i
    rw [hW, χ.eq_one, one_smul]
    exact radialTransportSection_center (I := I) g p (basis i) 0 (by
      rw [norm_zero]
      exact radialRadius_pos (I := I) g p)
  have hslots : (fun a : Fin 5 => basis (idx a)) =
      Fin.cons (X p) (fun a : Fin 4 => V a p) := by
    funext a
    refine Fin.cases ?_ (fun j => ?_) a
    · simp [X, hWp]
    · simp [V, hWp]
  have hfirst := d.first.eval_smooth_slots (I := I) X V p
  have hscalar := radialTransportTensorExtension_eval_eventually_eq
    (I := I) g p basis horth η₀ χ W hsupport hW (fun a => idx a.succ)
  have hderiv : extDerivFun (I := I)
      (fun y : M => radialTransportTensorExtension g p basis η₀ W y
        (fun a : Fin 4 => V a y)) p (X p) = 0 := by
    rw [DifferentialGeometry.Tensor.Coordinates.extDerivFun_congr_eventually
      (I := I) (v := X p) (by simpa [V] using hscalar)]
    simp [extDerivFun]
  have hconn : ∀ a : Fin 4,
      (LeviCivita (I := I) g).toFun (fun y => V a y) p (X p) = 0 := by
    intro a
    have hVi : (fun y => V a y) =ᶠ[𝓝 p]
        radialTransportSection (I := I) g p (basis (idx a.succ)) := by
      filter_upwards [χ.eventuallyEq_one] with y hy
      simp only [Pi.one_apply] at hy
      simp [V, hW, hy]
    exact localizedRadialTransportSection_nabla_center_zero
      (I := I) g p (basis (idx a.succ)) (V a) hVi (X p)
  rw [hslots, hfirst, hderiv]
  have hsum : (∑ a : Fin 4,
      radialTransportTensorExtension g p basis η₀ W p
        (Function.update (fun b : Fin 4 => V b p) a
          ((LeviCivita (I := I) g).toFun (fun y => V a y) p (X p)))) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    rw [hconn a]
    exact (radialTransportTensorExtension g p basis η₀ W p).toMultilinearMap.map_update_zero
      (fun b => V b p) a
  rw [hsum, sub_zero]

omit [IsManifold I 3 M] [SigmaCompactSpace M] in
private theorem radialTransportTensorExtension_nabla2_diagonal_center_zero
    (g : SmoothRiemannianMetric I M) (p : M)
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I p))
    (horth : OrthonormalBasisAt (I := I) g p basis)
    (η₀ : Tensor04At (I := I) (M := M) p)
    (χ : SmoothBumpFunction I p)
    (W : Fin 3 → ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (hsupport : tsupport (χ : M → ℝ) ⊆ radialTransportSectionDomain (I := I) g p)
    (hW : ∀ i y, W i y = χ y • radialTransportSection (I := I) g p (basis i) y)
    (d : CanonicalSpatialDerivs0S (I := I) (M := M) (LeviCivita (I := I) g)
      (radialTransportTensorExtension g p basis η₀ W))
    (a : Fin 3) (J : Fin 4 → Fin 3) :
    d.nabla2A p (Fin.cons (basis a) (Fin.cons (basis a) (fun j => basis (J j)))) = 0 := by
  let A := radialTransportTensorExtension g p basis η₀ W
  let X : ContMDiffSection I E ∞ (TangentSpace I : M → Type _) :=
    ⟨linearExtensionTangent (I := I) p (basis a),
      linearExtensionTangent_smooth (I := I) p (basis a)⟩
  let V : Fin 4 → ContMDiffSection I E ∞ (TangentSpace I : M → Type _) :=
    fun j => W (J j)
  have hXp : X p = basis a := by
    exact linearExtensionTangent_eq (I := I) p (basis a)
  have hWp : ∀ i : Fin 3, W i p = basis i := by
    intro i
    rw [hW, χ.eq_one, one_smul]
    exact radialTransportSection_center (I := I) g p (basis i) 0 (by
      rw [norm_zero]
      exact radialRadius_pos (I := I) g p)
  have hVp : ∀ j : Fin 4, V j p = basis (J j) := by
    intro j
    exact hWp (J j)
  have hVi : ∀ j : Fin 4, (fun y => V j y) =ᶠ[𝓝 p]
      radialTransportSection (I := I) g p (basis (J j)) := by
    intro j
    filter_upwards [χ.eventuallyEq_one] with y hy
    simp only [Pi.one_apply] at hy
    simp [V, hW, hy]
  let D : Fin 4 → ContMDiffSection I E ∞ (TangentSpace I : M → Type _) := fun j =>
    ⟨covApply (LeviCivita (I := I) g) (fun y => X y) (fun y => V j y), by
      rw [← contMDiffOn_univ]
      apply covApply_contMDiffOn (cov := LeviCivita (I := I) g) X.contMDiff
      rw [show ((∞ : WithTop ℕ∞) + 1) = ∞ by rw [ENat.coe_top_add_one]]
      exact (V j).contMDiff⟩
  have hD0 : ∀ j : Fin 4, D j p = 0 := by
    intro j
    change (LeviCivita (I := I) g).toFun (fun y => V j y) p (X p) = 0
    exact localizedRadialTransportSection_nabla_center_zero
      (I := I) g p (basis (J j)) (V j) (hVi j) (X p)
  have hD2 : ∀ j : Fin 4,
      (LeviCivita (I := I) g).toFun (fun y => D j y) p (X p) = 0 := by
    intro j
    have hmain := localizedRadialTransportSection_nabla2_center_zero
      (I := I) g p (basis (J j)) (basis a) (V j) (hVi j)
    change (LeviCivita (I := I) g).toFun
      (covApply (LeviCivita (I := I) g)
        (linearExtensionTangent (I := I) p (basis a)) (fun y => V j y)) p (X p) = 0
    rw [hXp]
    exact hmain
  have hnabla : d.nablaA p = 0 :=
    radialTransportTensorExtension_nabla_center_zero
      (I := I) g p basis horth η₀ χ W hsupport hW d
  let q : Fin 4 → M → ℝ := fun j y =>
    A y (fun b => (Function.update V j (D j)) b y)
  have hqsm : ∀ j : Fin 4, ContMDiff I 𝓘(ℝ, ℝ) ∞ (q j) := by
    intro j
    let Vj : Fin 4 → ContMDiffSection I E ∞ (TangentSpace I : M → Type _) :=
      Function.update V j (D j)
    have hsm := DifferentialGeometry.TensorMultilinear.contMDiff_tensor0SField_apply
      (I := I) (M := M) A Vj
    simpa only [q, Vj] using hsm
  have hqderiv : ∀ j : Fin 4, extDerivFun (I := I) (q j) p (X p) = 0 := by
    intro j
    let Vj : Fin 4 → ContMDiffSection I E ∞ (TangentSpace I : M → Type _) :=
      Function.update V j (D j)
    have hfirst := d.first.eval_smooth_slots (I := I) X Vj p
    have hsum : (∑ k : Fin 4, A p
        (Function.update (fun b : Fin 4 => Vj b p) k
          ((LeviCivita (I := I) g).toFun (fun y => Vj k y) p (X p)))) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      by_cases hkj : k = j
      · subst k
        have hcov : (LeviCivita (I := I) g).toFun (fun y => Vj j y) p (X p) = 0 := by
          simpa [Vj] using hD2 j
        rw [hcov]
        exact (A p).map_update_zero (fun b => Vj b p) j
      · apply (A p).map_coord_zero j
        rw [Function.update_of_ne (Ne.symm hkj)]
        simp [Vj, hD0]
    rw [hnabla] at hfirst
    simp only [Tensor0SSpace.zero_apply] at hfirst
    rw [hsum, sub_zero] at hfirst
    simpa [q, Vj] using hfirst.symm
  let f : M → ℝ := fun y => A y (fun j => V j y)
  have hfconst : f =ᶠ[𝓝 p] fun _ => η₀ (fun j => basis (J j)) := by
    simpa [f, A, V] using radialTransportTensorExtension_eval_eventually_eq
      (I := I) g p basis horth η₀ χ W hsupport hW J
  have hEqSet : {y : M | f y = η₀ (fun j => basis (J j))} ∈ 𝓝 p := by
    simpa only [Filter.EventuallyEq, Pi.one_apply] using hfconst
  obtain ⟨U, hUsub, hUopen, hpU⟩ := mem_nhds_iff.mp hEqSet
  have hzeroFirst : (fun y => extDerivFun (I := I) f y (X y)) =ᶠ[𝓝 p] 0 := by
    filter_upwards [hUopen.mem_nhds hpU] with y hy
    have hfy : f =ᶠ[𝓝 y] fun _ => η₀ (fun j => basis (J j)) := by
      filter_upwards [hUopen.mem_nhds hy] with z hz
      exact hUsub hz
    rw [DifferentialGeometry.Tensor.Coordinates.extDerivFun_congr_eventually
      (I := I) (v := X y) hfy]
    simp [extDerivFun]
  let V5 : Fin 5 → ContMDiffSection I E ∞ (TangentSpace I : M → Type _) := Fin.cons X V
  let G : M → ℝ := fun y => d.nablaA y (fun j => V5 j y)
  have hG : G =ᶠ[𝓝 p] fun y => -(∑ j : Fin 4, q j y) := by
    filter_upwards [hzeroFirst] with y hy
    simp only [Pi.zero_apply] at hy
    have hfirst := d.first.eval_smooth_slots (I := I) X V y
    have hXV : (fun j : Fin 5 => V5 j y) =
        Fin.cons (X y) (fun j => V j y) := by
      funext j
      refine Fin.cases ?_ (fun k => ?_) j <;> rfl
    change d.nablaA y (fun j : Fin 5 => V5 j y) = _
    rw [hXV]
    rw [hfirst, hy, zero_sub]
    simp only [q, A]
    apply congrArg Neg.neg
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    funext b
    by_cases hbj : b = j
    · subst b
      simp [D, covApply_apply]
    · simp [Function.update_of_ne hbj]
  have hsumqmd : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => ∑ j : Fin 4, q j y) p := by
    change MDifferentiableAt I 𝓘(ℝ, ℝ) (Finset.univ.sum q) p
    apply DifferentialGeometry.Tensor.RicciIdentity.mdiffAt_finset_sum
    intro j _
    exact (hqsm j).contMDiffAt.mdifferentiableAt (by simp)
  have hGderiv : extDerivFun (I := I) G p (X p) = 0 := by
    rw [DifferentialGeometry.Tensor.Coordinates.extDerivFun_congr_eventually
      (I := I) (v := X p) hG]
    rw [DifferentialGeometry.Tensor.RicciIdentity.extDerivFun_neg_at
      (I := I) (x := p) (X p) hsumqmd]
    change -extDerivFun (I := I) (Finset.univ.sum q) p (X p) = 0
    rw [DifferentialGeometry.Tensor.RicciIdentity.extDerivFun_finset_sum_at
      (I := I) Finset.univ q (X p) (fun j _ =>
        (hqsm j).contMDiffAt.mdifferentiableAt (by simp))]
    simp [hqderiv]
  have hV5p : ∀ j : Fin 5,
      V5 j p = Fin.cases (basis a) (fun k => basis (J k)) j := by
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · simpa [V5] using hXp
    · simpa [V5] using hVp k
  have hslots :
      (Fin.cons (basis a) (Fin.cons (basis a) (fun j => basis (J j))) :
        Fin 6 → TangentSpace I p) =
      (Fin.cons (X p) (fun j : Fin 5 => V5 j p) : Fin 6 → TangentSpace I p) := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · simpa using hXp.symm
    · simpa using (hV5p k).symm
  have hsecond := d.second.eval_smooth_slots (I := I) X V5 p
  have hsum2 : (∑ k : Fin 5, d.nablaA p
      (Function.update (fun b : Fin 5 => V5 b p) k
        ((LeviCivita (I := I) g).toFun (fun y => V5 k y) p (X p)))) = 0 := by
    rw [hnabla]
    simp
  rw [hslots, hsecond]
  change extDerivFun (I := I) G p (X p) - _ = 0
  rw [hGderiv, hsum2, sub_zero]

omit [IsManifold I 3 M] [SigmaCompactSpace M] in
theorem radialTransportTensorExtension_metricTrace_center_zero
    (g : SmoothRiemannianMetric I M) (p : M)
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I p))
    (horth : OrthonormalBasisAt (I := I) g p basis)
    (η₀ : Tensor04At (I := I) (M := M) p)
    (χ : SmoothBumpFunction I p)
    (W : Fin 3 → ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (hsupport : tsupport (χ : M → ℝ) ⊆ radialTransportSectionDomain (I := I) g p)
    (hW : ∀ i y, W i y = χ y • radialTransportSection (I := I) g p (basis i) y)
    (d : CanonicalSpatialDerivs0S (I := I) (M := M) (LeviCivita (I := I) g)
      (radialTransportTensorExtension g p basis η₀ W)) :
    metricTrace0S2TensorInBasis (I := I) basis
      (identityInvMetric (Idx := Fin 3)) (d.nabla2A p) = 0 := by
  apply ext0S_basis (I := I) basis
  intro J
  change metricTrace0S2TensorInBasis (I := I) basis
    (identityInvMetric (Idx := Fin 3)) (d.nabla2A p)
      (fun a => basis (J a)) = 0
  rw [metricTrace0S2TensorInBasis_apply]
  unfold metricTrace0S2InBasis
  apply Finset.sum_eq_zero
  intro i _
  rw [Finset.sum_eq_single i]
  · rw [identityInvMetric_apply_self, one_mul]
    exact radialTransportTensorExtension_nabla2_diagonal_center_zero
      (I := I) g p basis horth η₀ χ W hsupport hW d i J
  · intro j _ hji
    rw [identityInvMetric, diagonalInvMetric_eq_zero_of_ne hji.symm, zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

open DifferentialGeometry.Analysis.Parabolic

omit [IsManifold I 3 M] [SigmaCompactSpace M] [NeZero (Module.finrank Real E)]
  [T2Space (TangentBundle I M)] [I.Boundaryless] in
theorem fiberRegion_hasFlatSupportSectionsOn
    {T : Real} (hT : 0 < T) [I.Boundaryless]
    [NeZero (Module.finrank Real E)] [T2Space (TangentBundle I M)]
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt x))
    (iota : MatrixComp M (Fin 3))
    (hiota0 : ∀ x : M, ∀ a k : Fin 3, iota 0 x a k = if a = k then 1 else 0)
    (hgram : ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Fin 3,
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x ↦ basisAt x a)) iota t x a b =
        movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x ↦ basisAt x a)) iota 0 x a b)
    (K : Real) :
    (by
      letI : ∀ x : M, NormedAddCommGroup (Tensor04At (I := I) (M := M) x) :=
        fun x ↦ @InnerProductSpace.Core.toNormedAddCommGroup Real
          (Tensor04At (I := I) (M := M) x) inferInstance inferInstance inferInstance
          (tensor0SMetricData (I := I) (S.base.metric 0) x 4).toCore
      letI : ∀ x : M, InnerProductSpace Real (Tensor04At (I := I) (M := M) x) :=
        fun x ↦ @InnerProductSpace.ofCore Real (Tensor04At (I := I) (M := M) x)
          inferInstance inferInstance inferInstance
          (tensor0SMetricData (I := I) (S.base.metric 0) x 4).toCore.toCore
      letI : ∀ x : M, CompleteSpace (Tensor04At (I := I) (M := M) x) :=
        fun _ ↦ inferInstance
      exact HasFlatSupportSectionsOn (I := I) (Set.Icc 0 T)
        (V := fun x : M ↦ Tensor04At (I := I) (M := M) x)
        (fiberRegionFlat (I := I) (M := M) S basisAt iota)
        (regionNormalDirections (I := I) (S.base.metric 0) basisAt)
        (fiberRegionSupport hT (I := I) (M := M) S basisAt K)) := by
  classical
  letI : ∀ x : M, NormedAddCommGroup (Tensor04At (I := I) (M := M) x) :=
    fun x ↦ @InnerProductSpace.Core.toNormedAddCommGroup Real
      (Tensor04At (I := I) (M := M) x) inferInstance inferInstance inferInstance
      (tensor0SMetricData (I := I) (S.base.metric 0) x 4).toCore
  letI : ∀ x : M, InnerProductSpace Real (Tensor04At (I := I) (M := M) x) :=
    fun x ↦ @InnerProductSpace.ofCore Real (Tensor04At (I := I) (M := M) x)
      inferInstance inferInstance inferInstance
      (tensor0SMetricData (I := I) (S.base.metric 0) x 4).toCore.toCore
  letI : ∀ x : M, CompleteSpace (Tensor04At (I := I) (M := M) x) :=
    fun _ ↦ inferInstance
  refine ⟨?_⟩
  intro t ht x₀ ν' hν'
  let U : TangentSpace I x₀ →L[Real] TangentSpace I x₀ :=
    uhlenbeckEndomorphismAt (basisAt x₀) iota t
  let e : TangentSpace I x₀ ≃ₗ[Real] TangentSpace I x₀ :=
    LinearEquiv.ofBijective U.toLinearMap
      (uhlenbeckEndomorphism_invertible hT S basisAt iota hiota0 hgram ht x₀)
  let Uinv : TangentSpace I x₀ →L[Real] TangentSpace I x₀ :=
    e.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hUinvU : ∀ v : TangentSpace I x₀, Uinv (U v) = v := by
    intro v
    change e.symm (e v) = v
    exact e.symm_apply_apply v
  let η₀ : Tensor04At (I := I) (M := M) x₀ :=
    ν'.compContinuousLinearMap (fun _ : Fin 4 ↦ Uinv)
  have hpull : uhlenbeckPullbackTensorAt (I := I) basisAt iota t x₀ η₀ = ν' := by
    apply tensor0SSpace_ext 4 x₀
    intro v
    change ν' (fun a ↦ Uinv (U (v a))) = ν' v
    congr 1
    funext a
    exact hUinvU (v a)
  let basis : Module.Basis (Fin 3) Real (TangentSpace I x₀) :=
    uhlenbeckMovingBasis hT S basisAt iota hiota0 hgram t ht x₀
  have horth : OrthonormalBasisAt (I := I) (S.base.metric t) x₀ basis :=
    uhlenbeckMovingBasis_orthonormalBasisAt (I := I) (M := M)
      hT S basisAt iota hiota0 hgram x₀ (horth0 x₀) ht
  obtain ⟨χ, W, hsupport, hW, _⟩ :=
    exists_localized_radial_transport_sections (I := I) (S.base.metric t) x₀
      (fun i ↦ basis i)
  let η : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4 :=
    radialTransportTensorExtension (S.base.metric t) x₀ basis η₀ W
  have hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (S.base.connection t) (∞ : WithTop ℕ∞) := by
    simpa [SolutionFamily.connection, metricCov] using
      metricCov_smooth (I := I) (M := M) (S.base.metric t)
  let d : CanonicalSpatialDerivs0S (I := I) (M := M) (S.base.connection t) η :=
    CanonicalSpatialDerivs0S.of_smooth_connection
      (E := E) (H := H) (I := I) (M := M) (S.base.connection t) hcov η
  let ν : (x : M) → Tensor04At (I := I) (M := M) x := fun y ↦
    uhlenbeckPullbackTensorAt (I := I) basisAt iota t y (η y)
  refine ⟨ν, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨η, d.nablaA, d.nabla2A, basis, horth, ?_, d.first, d.second, ?_, ?_⟩
    · exact Filter.Eventually.of_forall (fun _ ↦ rfl)
    · exact radialTransportTensorExtension_nabla_center_zero
        (I := I) (S.base.metric t) x₀ basis horth η₀ χ W hsupport hW d
    · exact radialTransportTensorExtension_metricTrace_center_zero
        (I := I) (S.base.metric t) x₀ basis horth η₀ χ W hsupport hW d
  · dsimp [ν, η]
    rw [radialTransportTensorExtension_initial
      (I := I) (S.base.metric t) x₀ basis horth η₀ χ W hsupport hW]
    exact hpull
  · intro y
    by_cases hχ : χ y = 0
    · have hηy : η y = 0 := by
        dsimp [η]
        rw [radialTransportTensorExtension_eq_smul
          (I := I) (S.base.metric t) x₀ basis horth η₀ χ W hsupport hW y]
        simp [hχ]
      have hνy : ν y = 0 := by
        dsimp [ν]
        rw [hηy]
        apply tensor0SSpace_ext 4 y
        intro v
        rfl
      rw [hνy, regionNormalDirections]
      right
      have hproj0 : (fiberProjW (I := I) (S.base.metric 0) y
          (0 : Tensor04At (I := I) (M := M) y) :
          Tensor04At (I := I) (M := M) y) = 0 := by
        simpa using fiberProjW_smul (I := I) (S.base.metric 0) y 0
          (0 : Tensor04At (I := I) (M := M) y)
      unfold regionProjMatrix
      rw [show fiberProjW (I := I) (S.base.metric 0) y
          (0 : Tensor04At (I := I) (M := M) y) = 0 by
        apply Subtype.ext
        exact hproj0]
      have hmatrix0 : curvatureOperatorMatrixAt (I := I) y (basisAt y)
          (0 : algebraicCurvatureTensorSubmodule (I := I) (M := M) y) = 0 := by
        ext i j
        rfl
      rw [hmatrix0]
      ext i j
      simp [symmEuclid, matrixToEuclid, euclidToMatrix]
    · have hy : y ∈ radialTransportSectionDomain (I := I) (S.base.metric t) x₀ :=
        hsupport (subset_closure (show y ∈ Function.support (χ : M → Real) from hχ))
      let basisY : Module.Basis (Fin 3) Real (TangentSpace I y) :=
        uhlenbeckMovingBasis hT S basisAt iota hiota0 hgram t ht y
      have horthY : OrthonormalBasisAt (I := I) (S.base.metric t) y basisY :=
        uhlenbeckMovingBasis_orthonormalBasisAt (I := I) (M := M)
          hT S basisAt iota hiota0 hgram y (horth0 y) ht
      obtain ⟨O, hO, hmatrix⟩ :=
        radialTransportTensorExtension_regionProjMatrix_eq_conj
          (I := I) (S.base.metric t) x₀ basis horth η₀ χ W hsupport hW y hy basisY horthY
      have hpullY := regionProjMatrix_uhlenbeckPullback_eq_moving
        (I := I) (M := M) hT S basisAt iota hiota0 hgram horth0 ht y (η y)
      have hcenter := regionProjMatrix_uhlenbeckPullback_eq_moving
        (I := I) (M := M) hT S basisAt iota hiota0 hgram horth0 ht x₀ η₀
      have hcenterEq : regionProjMatrix (I := I) (S.base.metric t) basis η₀ =
          regionProjMatrix (I := I) (S.base.metric 0) (basisAt x₀) ν' := by
        rw [← hpull]
        simpa [basis] using hcenter.symm
      have hmatrixTotal :
          regionProjMatrix (I := I) (S.base.metric 0) (basisAt y) (ν y) =
            (χ y) ^ 4 •
              (O.transpose *
                regionProjMatrix (I := I) (S.base.metric 0) (basisAt x₀) ν' * O) := by
        calc
          regionProjMatrix (I := I) (S.base.metric 0) (basisAt y) (ν y) =
              regionProjMatrix (I := I) (S.base.metric t) basisY (η y) := by
                simpa [ν, basisY] using hpullY
          _ = (χ y) ^ 4 •
                (O.transpose * regionProjMatrix (I := I) (S.base.metric t) basis η₀ * O) :=
              hmatrix
          _ = (χ y) ^ 4 •
                (O.transpose *
                  regionProjMatrix (I := I) (S.base.metric 0) (basisAt x₀) ν' * O) := by
              rw [hcenterEq]
      rw [regionNormalDirections] at hν' ⊢
      simp only [Set.mem_setOf_eq] at hν' ⊢
      have hρ : 0 ≤ (χ y) ^ 4 := pow_nonneg (χ.nonneg : 0 ≤ χ y) 4
      have hmain := regionNormalDirections_conj_scale_condition
        (M := regionProjMatrix (I := I) (S.base.metric 0) (basisAt x₀) ν')
        (O := O) (ρ := (χ y) ^ 4) hρ hO hν'
      simpa only [hmatrixTotal] using hmain
  · intro y
    have hisoY := fiberInner_compUhlenbeck_isometry_full
      (I := I) (M := M) hT S basisAt iota hiota0 hgram horth0 ht y (η y) (η y)
    have hrad := radialTransportTensorExtension_inner_self_le
      (I := I) (S.base.metric t) x₀ (hdim x₀) basis horth η₀ χ W hsupport hW y
    have hiso0 := fiberInner_compUhlenbeck_isometry_full
      (I := I) (M := M) hT S basisAt iota hiota0 hgram horth0 ht x₀ η₀ η₀
    have hinner : inner Real (ν y) (ν y) ≤ inner Real ν' ν' := by
      rw [tensor04_fiberInner_eq (I := I) (S.base.metric 0) y (ν y) (ν y)]
      rw [show inner0S (I := I) (S.base.metric 0) y 4 (ν y) (ν y) =
          inner0S (I := I) (S.base.metric t) y 4 (η y) (η y) by
        simpa [ν, uhlenbeckPullbackTensorAt] using hisoY]
      apply hrad.trans_eq
      calc
        inner0S (I := I) (S.base.metric t) x₀ 4 η₀ η₀ =
            inner0S (I := I) (S.base.metric 0) x₀ 4
              (uhlenbeckPullbackTensorAt (I := I) basisAt iota t x₀ η₀)
              (uhlenbeckPullbackTensorAt (I := I) basisAt iota t x₀ η₀) := by
                simpa [uhlenbeckPullbackTensorAt] using hiso0.symm
        _ = inner0S (I := I) (S.base.metric 0) x₀ 4 ν' ν' := by rw [hpull]
        _ = inner Real ν' ν' :=
          (tensor04_fiberInner_eq (I := I) (S.base.metric 0) x₀ ν' ν').symm
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hinner
    nlinarith [norm_nonneg (ν y), norm_nonneg ν']
  · have hevent : ∀ᶠ y in nhds x₀,
        fiberRegionSupport hT (I := I) (M := M) S basisAt K t y (ν y) =
          fiberRegionSupport hT (I := I) (M := M) S basisAt K t x₀ ν' := by
      have hdomain : radialTransportSectionDomain (I := I) (S.base.metric t) x₀ ∈ nhds x₀ :=
        (radialTransportSectionDomain_isOpen (I := I) (S.base.metric t) x₀).mem_nhds
          (mem_radialTransportSectionDomain_self (I := I) (S.base.metric t) x₀)
      filter_upwards [χ.eventuallyEq_one, hdomain] with y hχ hy
      simp only [Pi.one_apply] at hχ
      let basisY : Module.Basis (Fin 3) Real (TangentSpace I y) :=
        uhlenbeckMovingBasis hT S basisAt iota hiota0 hgram t ht y
      have horthY : OrthonormalBasisAt (I := I) (S.base.metric t) y basisY :=
        uhlenbeckMovingBasis_orthonormalBasisAt (I := I) (M := M)
          hT S basisAt iota hiota0 hgram y (horth0 y) ht
      obtain ⟨O, hO, hmatrix⟩ :=
        radialTransportTensorExtension_regionProjMatrix_eq_conj
          (I := I) (S.base.metric t) x₀ basis horth η₀ χ W hsupport hW y hy basisY horthY
      have hpullY := regionProjMatrix_uhlenbeckPullback_eq_moving
        (I := I) (M := M) hT S basisAt iota hiota0 hgram horth0 ht y (η y)
      have hcenter := regionProjMatrix_uhlenbeckPullback_eq_moving
        (I := I) (M := M) hT S basisAt iota hiota0 hgram horth0 ht x₀ η₀
      unfold fiberRegionSupport regionSupport
      rw [show regionProjMatrix (I := I) (S.base.metric 0) (basisAt y) (ν y) =
          regionProjMatrix (I := I) (S.base.metric t) basisY (η y) by
        simpa [ν, basisY] using hpullY]
      rw [hmatrix, hχ, one_pow, one_smul]
      rw [show regionProjMatrix (I := I) (S.base.metric t) basis η₀ =
          regionProjMatrix (I := I) (S.base.metric 0) (basisAt x₀) ν' by
        rw [← hpull]
        simpa [basis] using hcenter.symm]
      rw [hamiltonIveyConvexMatrixRegionSupportEuclid_conj K (max t 0)
        (regionProjMatrix (I := I) (S.base.metric 0) (basisAt x₀) ν') O hO]
    have hset : {y : M |
        fiberRegionSupport hT (I := I) (M := M) S basisAt K t y (ν y) =
          fiberRegionSupport hT (I := I) (M := M) S basisAt K t x₀ ν'} ∈ nhds x₀ :=
      hevent
    obtain ⟨V, hVsub, hVopen, hx₀V⟩ := mem_nhds_iff.mp hset
    exact ⟨V, hVopen, hx₀V, fun y hy ↦ hVsub hy⟩

omit [NeZero (Module.finrank Real E)] [T2Space (TangentBundle I M)] [I.Boundaryless] in
theorem fiberRegionPropagationOn_of_bundleMaximumPrinciple
    {T : Real} (hT : 0 < T) [I.Boundaryless] [CompactSpace M]
    [NeZero (Module.finrank Real E)] [T2Space (TangentBundle I M)]
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn (I := I) S)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt x))
    (iota : MatrixComp M (Fin 3))
    (hiota0 : ∀ x : M, ∀ a k : Fin 3, iota 0 x a k = if a = k then 1 else 0)
    (hgram : ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Fin 3,
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x ↦ basisAt x a)) iota t x a b =
        movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x ↦ basisAt x a)) iota 0 x a b)
    {K : Real} (hK : 0 < K)
    (hinit : ∀ x : M,
      uhlenbeckPulledRm04At S basisAt iota 0 x ∈ fiberHamiltonIveyRegion basisAt K 0 x)
    (hsol : by
      letI : ∀ x : M, NormedAddCommGroup (Tensor04At (I := I) (M := M) x) :=
        fun x ↦ @InnerProductSpace.Core.toNormedAddCommGroup Real
          (Tensor04At (I := I) (M := M) x) inferInstance inferInstance inferInstance
          (tensor0SMetricData (I := I) (S.base.metric 0) x 4).toCore
      letI : ∀ x : M, InnerProductSpace Real (Tensor04At (I := I) (M := M) x) :=
        fun x ↦ @InnerProductSpace.ofCore Real (Tensor04At (I := I) (M := M) x)
          inferInstance inferInstance inferInstance
          (tensor0SMetricData (I := I) (S.base.metric 0) x 4).toCore.toCore
      letI : ∀ x : M, CompleteSpace (Tensor04At (I := I) (M := M) x) :=
        fun _ ↦ inferInstance
      exact IsBundleHeatReactionOn
        (V := fun x : M ↦ Tensor04At (I := I) (M := M) x)
        (fiberRegionFlat (I := I) (M := M) S basisAt iota)
        (RealTimeInterval.closed 0 T hT.le) (flowG (I := I) S)
        (fun _ => fiberRegionSource hT (I := I) (M := M) S basisAt)
        (uhlenbeckPulledRm04At S basisAt iota)) :
    ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M,
      uhlenbeckPulledRm04At S basisAt iota t x ∈ fiberHamiltonIveyRegion basisAt K t x := by
  apply fiberRegionPropagationOn_of_flatSupport
    (I := I) (M := M) hT S hS hdim basisAt horth0 iota hiota0 hgram hK hinit hsol
  exact fiberRegion_hasFlatSupportSectionsOn
    (I := I) (M := M) hT S hdim basisAt horth0 iota hiota0 hgram K

end TensorTransport


end RadialTransportLinear

omit [I.Boundaryless] in
private theorem curvatureOperatorRegionPropagationOn_zero_aux
    {T : Real} (hT : 0 < T) [I.Boundaryless] [CompactSpace M] [Nonempty M]
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn (I := I) S)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    {K : Real} (hK : 0 < K)
    (hinit : ∀ x : M,
      CurvatureOperatorLowerBoundAt (I := I) (S.base.metric 0) x
        ⟨S.base.rm04 0 x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) (S.base.metric 0) x⟩ K) :
    CurvatureOperatorRegionPropagationOn (I := I) (M := M) S K 0 T := by
  classical
  letI : NeZero (Module.finrank Real E) := ⟨by
    intro hzero
    have hthree := hdim (Classical.choice (inferInstance : Nonempty M))
    have hthree' : Module.finrank Real E = 3 := by
      simpa only [TangentSpace] using hthree
    omega⟩
  let basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x) :=
    fun x ↦ Classical.choose
      (exists_orthonormalBasisAt (I := I) (S.base.metric 0) x (hdim x))
  have horth0 : ∀ x : M,
      OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt x) := by
    intro x
    exact Classical.choose_spec
      (exists_orthonormalBasisAt (I := I) (S.base.metric 0) x (hdim x))
  let iota : MatrixComp M (Fin 3) := intrinsicUhlenbeckIota hT S hS basisAt
  have hspec := intrinsicUhlenbeckIota_spec (I := I) (M := M) hT S hS basisAt
  have hiota0 : ∀ x : M, ∀ a k : Fin 3,
      iota 0 x a k = if a = k then 1 else 0 := by
    simpa [iota] using hspec.1
  have hiotaCont : ∀ x : M,
      ContinuousOn (fun t : Real ↦ iota t x) (Set.Icc 0 T) := by
    simpa [iota] using hspec.2.1
  have hiotaODE : BundleIsomorphismODEInFrameOn
      (D := RealTimeInterval.closed 0 T hT.le) iota
      (solutionRicciOneUpInFrame (I := I) S (solutionInverseMetricComponents S basisAt)
        (fun a x ↦ basisAt x a)) := by
    simpa [iota, BundleIsomorphismODEInFrameOn, uhlenbeckRupOfSolution,
      solutionRicciOneUpInFrame] using hspec.2.2.1
  have hgram : ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Fin 3,
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x ↦ basisAt x a))
          iota t x a b =
        movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x ↦ basisAt x a))
          iota 0 x a b := by
    simpa [iota] using hspec.2.2.2
  have hsol := fiberRegionHeatReactionOn (I := I) (M := M) hT S hS hdim
    basisAt horth0 iota hiota0 hgram hiotaCont hiotaODE
  have hinitFiber : ∀ x : M,
      uhlenbeckPulledRm04At S basisAt iota 0 x ∈
        fiberHamiltonIveyRegion basisAt K 0 x := by
    intro x
    exact pulledCurvature_initial_mem_fiberRegion (I := I) (M := M) hT S basisAt iota
      hiota0 horth0 hK x (hinit x)
  have hfiber := fiberRegionPropagationOn_of_bundleMaximumPrinciple
    (I := I) (M := M) hT S hS hdim basisAt horth0 iota hiota0 hgram hK hinitFiber hsol
  have hprop := curvatureOperatorRegionPropagationOn_of_fiberRegion_mem
    (I := I) (M := M) hT S basisAt iota hiota0 hgram horth0 hfiber
  simpa [CurvatureOperatorRegionPropagationOn] using hprop

omit [I.Boundaryless] in
theorem curvatureOperatorRegionPropagationOn_of_initial_lower_bound
    [I.Boundaryless] [CompactSpace M]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {t0 T K : Real} (hT : 0 < T) (hK : 0 < K)
    (hslab : Set.Icc t0 (t0 + T) ⊆ D.carrier)
    (hreg : Set.Ioo t0 (t0 + T) ⊆ D.regular)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (hinit : ∀ x : M,
      CurvatureOperatorLowerBoundAt (I := I) (S.base.metric t0) x
        ⟨S.base.rm04 t0 x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) (S.base.metric t0) x⟩ K) :
    CurvatureOperatorRegionPropagationOn (I := I) (M := M) S K t0 T := by
  classical
  cases isEmpty_or_nonempty M with
  | inl hM =>
      letI := hM
      intro t ht x
      exact isEmptyElim x
  | inr hM =>
      letI := hM
      let Sshift : SolutionOn (I := I) (M := M) (D.timeShift t0) := S.timeShift t0
      let D0 : RealTimeInterval := RealTimeInterval.closed 0 T hT.le
      let S0 : SolutionOn (I := I) (M := M) D0 := Sshift.timeRestrict D0
      have hSshift : IsSolutionOn (I := I) Sshift := by
        exact isSolutionOn_timeShift (I := I) hS t0
      have hS0 : IsSolutionOn (I := I) S0 := by
        apply isSoln_timeRestrict (I := I) hSshift
        · intro t ht
          change t + t0 ∈ D.carrier
          exact hslab ⟨by linarith [ht.1], by linarith [ht.2]⟩
        · intro t ht
          change t + t0 ∈ D.regular
          exact hreg ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have hinit0 : ∀ x : M,
          CurvatureOperatorLowerBoundAt (I := I) (S0.base.metric 0) x
            ⟨S0.base.rm04 0 x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
              (I := I) (S0.base.metric 0) x⟩ K := by
        intro x
        simpa [S0, Sshift, SolutionOn.timeRestrict, SolutionOn.timeShift,
          SolutionFamily.timeShift, SolutionFamily.rm04] using hinit x
      have hprop0 := curvatureOperatorRegionPropagationOn_zero_aux
        (I := I) (M := M) hT S0 hS0 hdim hK hinit0
      have hpropShift : CurvatureOperatorRegionPropagationOn
          (I := I) (M := M) Sshift K 0 T := by
        simpa [S0, SolutionOn.timeRestrict] using hprop0
      exact curvatureOperatorRegionPropagationOn_timeShift
        (I := I) (M := M) S hpropShift

omit [I.Boundaryless] in
theorem hamilton_ivey_pinching
    [I.Boundaryless] [CompactSpace M]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {t0 T K : Real} (hT : 0 < T) (hK : 0 < K)
    (hslab : Set.Icc t0 (t0 + T) ⊆ D.carrier)
    (hreg : Set.Ioo t0 (t0 + T) ⊆ D.regular)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (hinit : ∀ x : M,
      CurvatureOperatorLowerBoundAt (I := I) (S.base.metric t0) x
        ⟨S.base.rm04 t0 x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) (S.base.metric t0) x⟩ K) :
    (∀ t : Real, t ∈ Set.Icc t0 (t0 + T) → ∀ x : M,
      -6 * K / (1 + 4 * K * (t - t0)) ≤ S.scalar t x) ∧
    (∀ t : Real, t ∈ Set.Icc t0 (t0 + T) → ∀ x : M,
      ∀ basis : Module.Basis (Fin 3) Real (TangentSpace I x),
        OrthonormalBasisAt (I := I) (S.base.metric t) x basis →
        orderedSectionalCurvaturesAt (I := I) x basis
            ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
              (I := I) (S.base.metric t) x⟩ 2 < 0 →
          S.scalar t x ≥
            2 * (-orderedSectionalCurvaturesAt (I := I) x basis
              ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
                (I := I) (S.base.metric t) x⟩ 2) *
              (Real.log ((-orderedSectionalCurvaturesAt (I := I) x basis
                ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
                  (I := I) (S.base.metric t) x⟩ 2) / K) +
                Real.log (1 + 2 * K * (t - t0)) - 3)) := by
  have hprop := curvatureOperatorRegionPropagationOn_of_initial_lower_bound
    (I := I) (M := M) S hS hT hK hslab hreg hdim hinit
  exact hamilton_ivey_pinching_of_curvatureOperatorRegionPropagation
    (I := I) (M := M) S hslab hprop

omit [I.Boundaryless] in
theorem hamilton_ivey_pinching_one
    [I.Boundaryless] [CompactSpace M]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {t0 T : Real} (hT : 0 < T)
    (hslab : Set.Icc t0 (t0 + T) ⊆ D.carrier)
    (hreg : Set.Ioo t0 (t0 + T) ⊆ D.regular)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (hinit : ∀ x : M,
      CurvatureOperatorLowerBoundAt (I := I) (S.base.metric t0) x
        ⟨S.base.rm04 t0 x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) (S.base.metric t0) x⟩ 1) :
    (∀ t : Real, t ∈ Set.Icc t0 (t0 + T) → ∀ x : M,
      -6 / (1 + 4 * (t - t0)) ≤ S.scalar t x) ∧
    (∀ t : Real, t ∈ Set.Icc t0 (t0 + T) → ∀ x : M,
      ∀ basis : Module.Basis (Fin 3) Real (TangentSpace I x),
        OrthonormalBasisAt (I := I) (S.base.metric t) x basis →
        orderedSectionalCurvaturesAt (I := I) x basis
            ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
              (I := I) (S.base.metric t) x⟩ 2 < 0 →
          S.scalar t x ≥
            2 * (-orderedSectionalCurvaturesAt (I := I) x basis
              ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
                (I := I) (S.base.metric t) x⟩ 2) *
              (Real.log (-orderedSectionalCurvaturesAt (I := I) x basis
                ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
                  (I := I) (S.base.metric t) x⟩ 2) +
                Real.log (1 + 2 * (t - t0)) - 3)) := by
  have hmain := hamilton_ivey_pinching (I := I) (M := M) S hS hT
    (by norm_num : 0 < (1 : Real)) hslab hreg hdim hinit
  constructor
  · intro t ht x
    have h := hmain.1 t ht x
    norm_num at h ⊢
    simpa [one_mul] using h
  · intro t ht x basis horth hneg
    have h := hmain.2 t ht x basis horth hneg
    norm_num at h ⊢
    simpa [one_mul] using h

omit [I.Boundaryless] in
theorem hamilton_ivey_asymptotic_pinching
    [I.Boundaryless] [CompactSpace M]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {t0 T K delta : Real} (hT : 0 < T) (hK : 0 < K) (hdelta : 0 < delta)
    (hslab : Set.Icc t0 (t0 + T) ⊆ D.carrier)
    (hreg : Set.Ioo t0 (t0 + T) ⊆ D.regular)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (hinit : ∀ x : M,
      CurvatureOperatorLowerBoundAt (I := I) (S.base.metric t0) x
        ⟨S.base.rm04 t0 x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) (S.base.metric t0) x⟩ K) :
    ∀ t : Real, t ∈ Set.Icc t0 (t0 + T) → ∀ x : M,
      ∀ basis : Module.Basis (Fin 3) Real (TangentSpace I x),
        OrthonormalBasisAt (I := I) (S.base.metric t) x basis →
        pinchHeight3 (orderedSectionalCurvaturesAt (I := I) x basis
            ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
              (I := I) (S.base.metric t) x⟩ 2) ≤
          delta * S.scalar t x +
            2 * delta * K * Real.exp (2 + (2 * delta)⁻¹) := by
  have hprop := curvatureOperatorRegionPropagationOn_of_initial_lower_bound
    (I := I) (M := M) S hS hT hK hslab hreg hdim hinit
  exact hamilton_ivey_asymptotic_pinching_of_curvatureOperatorRegionPropagation
    (I := I) (M := M) S hK hdelta hprop
































end DifferentialGeometry.PDE.RicciFlow

end
