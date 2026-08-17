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
open DifferentialGeometry.Analysis.Convex
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Geometry.Operator
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
        fiberHamiltonIveySupport g basisAt K τ x ν := by
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
  have hsup : fiberHamiltonIveySupport g basisAt K τ x
        (fiberProjW (I := I) g x ν : Tensor04At (I := I) (M := M) x) =
      regionSupport (I := I) g basisAt K τ x ν := by
    unfold regionSupport fiberHamiltonIveySupport
    rw [dif_pos hν₀alg]
    rw [← hreg]
    rw [regionProjMatrix_eq_curvatureOperatorMatrixAt (I := I) g (basisAt x) hν₀alg]
  calc
    regionSupport (I := I) g basisAt K τ x ν
        = fiberHamiltonIveySupport g basisAt K τ x
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
    fiberHamiltonIveyRegion_normal (I := I) g basisAt horth0 hK hτ x hp hν₀alg hnormal'
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
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (_horth0 : ∀ x : M, OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt x)) :
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
      intrinsicUhlenbeckIota hT S hS basisAt horth0 0 x a k = if a = k then 1 else 0) ∧
    (∀ x : M, ContinuousOn (fun t : ℝ => intrinsicUhlenbeckIota hT S hS basisAt horth0 t x)
      (Set.Icc 0 T)) ∧
    FrameRicciODEInFrameOn (D := RealTimeInterval.closed 0 T hT.le)
      (intrinsicUhlenbeckIota hT S hS basisAt horth0)
      (uhlenbeckRupOfSolution (I := I) S (solutionInverseMetricComponents S basisAt)
        (fun a x => basisAt x a)) ∧
    (∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Fin 3,
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a))
        (intrinsicUhlenbeckIota hT S hS basisAt horth0) t x a b =
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a))
        (intrinsicUhlenbeckIota hT S hS basisAt horth0) 0 x a b) := by
  classical
  let iota : MatrixComp M (Fin 3) := intrinsicUhlenbeckIota hT S hS basisAt horth0
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
    (_t : ℝ) (x : M) (p ν : Tensor04At (I := I) (M := M) x) : ℝ :=
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
theorem fiberRegionPropagationOn_of_bundleMaximumPrinciple
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
        (fiberRegionSource hT (I := I) (M := M) S basisAt)
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
      exact HasFlatSupportSections (I := I)
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
        fiberRegionSource hT (I := I) (M := M) S basisAt t x p ν ≤
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
      (fiberRegionSource hT (I := I) (M := M) S basisAt)
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

end DifferentialGeometry.PDE.RicciFlow

end
