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

end PulledScalarization


end DifferentialGeometry.PDE.RicciFlow

end
