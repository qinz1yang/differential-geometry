import DifferentialGeometry.Geometry.Curvature.DimensionTwo.RicciScalar
import DifferentialGeometry.Geometry.Curvature.Algebraic.CurvatureOperatorCone
import DifferentialGeometry.Geometry.Curvature.Algebraic.TensorMetric
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetric

/-!
# Curvature algebra of surfaces for the U1 curvature bound

Chapter 7, packet P8, surface lemma U1, route (a), lane a3. On a surface (`finrank = 2`) the
curvature tensor is `Rm(v, w, z, u) = (R / 2) (⟨v, u⟩⟨w, z⟩ - ⟨v, z⟩⟨w, u⟩)`
(`metricRm04StdAt_eq_scalar_div_two_of_finrank_eq_two`).

* `exists_orthonormalBasis_of_finrank_two`, `inner_eq_sum_repr_of_orthonormal`: an orthonormal
  basis of a tangent plane and the Parseval formula in its coordinates.
* `mem_curvatureOperatorNonnegativeCone_of_finrank_two`: nonnegative scalar curvature puts the
  curvature tensor in the nonnegative curvature operator cone (the Harnack input), since the
  quadratic form equals `(R / 2) (∑ cᵢ det (vᵢ, wᵢ))²` in orthonormal coordinates.
* `normSq0S_metricRm04At_eq_sq_of_finrank_two`: `|Rm|² = R²` (the non-collapsing input).
-/

set_option autoImplicit false

noncomputable section

open Bundle DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff BigOperators

namespace GC.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

omit [I.Boundaryless] [T2Space M] in
theorem exists_orthonormalBasis_of_finrank_two (g : SmoothRiemannianMetric I M) (x : M)
    (hdim : Module.finrank ℝ E = 2) :
    ∃ basis : Module.Basis (Fin 2) ℝ (TangentSpace I x),
      ∀ i j : Fin 2, g.inner x (basis i) (basis j) = if i = j then 1 else 0 := by
  have hdimT : Module.finrank ℝ (TangentSpace I x) = 2 :=
    (show Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E from rfl).trans hdim
  let D := (tangentMetricData (I := I) g x).metric
  let _ : InnerProductSpace.Core ℝ (TangentSpace I x) := D.toCore
  let _ : NormedAddCommGroup (TangentSpace I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℝ (TangentSpace I x) _ _ _ D.toCore
  let _ : InnerProductSpace ℝ (TangentSpace I x) :=
    @InnerProductSpace.ofCore ℝ (TangentSpace I x) _ _ _ D.toCore.toCore
  let ob : OrthonormalBasis (Fin 2) ℝ (TangentSpace I x) :=
    (stdOrthonormalBasis ℝ (TangentSpace I x)).reindex (finCongr hdimT)
  refine ⟨ob.toBasis, fun i j => ?_⟩
  have hinner : Inner.inner ℝ (ob i) (ob j) = D.inner (ob i) (ob j) :=
    MetricFiberData.toCore_inner D (ob i) (ob j)
  change D.inner (ob i) (ob j) = if i = j then 1 else 0
  rw [← hinner]
  exact ob.inner_eq_ite i j

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
theorem inner_eq_sum_repr_of_orthonormal (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 2) ℝ (TangentSpace I x))
    (horth : ∀ i j : Fin 2, g.inner x (basis i) (basis j) = if i = j then 1 else 0)
    (u u' : TangentSpace I x) :
    g.inner x u u' = basis.repr u 0 * basis.repr u' 0 + basis.repr u 1 * basis.repr u' 1 := by
  have h00 := horth 0 0
  have h01 := horth 0 1
  have h10 := horth 1 0
  have h11 := horth 1 1
  simp only [Fin.isValue, ite_true, show (0 : Fin 2) ≠ 1 by decide,
    show (1 : Fin 2) ≠ 0 by decide, ite_false] at h00 h01 h10 h11
  conv_lhs => rw [← basis.sum_repr u, ← basis.sum_repr u']
  simp only [Fin.sum_univ_two, map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
  rw [h00, h01, h10, h11]
  ring

theorem mem_curvatureOperatorNonnegativeCone_of_finrank_two (hdim : Module.finrank ℝ E = 2)
    (g : SmoothRiemannianMetric I M) (x : M) (hR : 0 ≤ metricScalarAt g x) :
    metricAlgebraicCurvatureTensorAt g x ∈ algebraicCurvatureOperatorNonnegativeCone (I := I) := by
  obtain ⟨basis, horth⟩ := exists_orthonormalBasis_of_finrank_two g x hdim
  apply mem_algebraicCurvatureOperatorNonnegativeCone.mpr
  intro n c v w
  let d : Fin n → ℝ := fun i => basis.repr (v i) 0 * basis.repr (w i) 1 -
    basis.repr (v i) 1 * basis.repr (w i) 0
  have hterm : ∀ i j, tensor04StandardAt
      (metricAlgebraicCurvatureTensorAt g x : Tensor04At (I := I) (M := M) x)
      (v i) (w i) (w j) (v j) = metricScalarAt g x / 2 * (d i * d j) := by
    intro i j
    have h := metricRm04StdAt_eq_scalar_div_two_of_finrank_eq_two g hdim x (v i) (w i) (w j) (v j)
    simp only [metricRm04StandardAt_apply] at h
    change metricRm04At g x (vec4 (v i) (w i) (w j) (v j)) = _
    rw [h]
    simp only [inner_eq_sum_repr_of_orthonormal g basis horth, d]
    ring
  have hsum : algebraicCurvatureOperatorQuadraticEval (metricAlgebraicCurvatureTensorAt g x) c v w
      = metricScalarAt g x / 2 * (∑ i, c i * d i) ^ 2 := by
    unfold algebraicCurvatureOperatorQuadraticEval
    simp only [hterm, sq, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum]
  positivity

private theorem sum_fin_succ_fun {Idx : Type*} [Fintype Idx] {α : Type*} [AddCommMonoid α]
    (s : ℕ) (F : (Fin (s + 1) → Idx) → α) :
    (∑ I0 : Fin (s + 1) → Idx, F I0) = ∑ i : Idx, ∑ tail : Fin s → Idx, F (Fin.cons i tail) := by
  classical
  rw [Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (s + 1) => Idx)).symm F
    (fun p : Idx × (Fin s → Idx) => F (Fin.cons p.1 p.2))]
  · rw [Fintype.sum_prod_type]
  · intro I0
    congr 1
    exact (Fin.cons_self_tail I0).symm

private theorem sum_fin_zero_fun' {Idx : Type*} {α : Type*} [AddCommMonoid α]
    (F : (Fin 0 → Idx) → α) (c : α) (h : ∀ f, F f = c) : (∑ I0 : Fin 0 → Idx, F I0) = c := by
  classical
  rw [Fintype.sum_unique]
  exact h _

private theorem sum_fin_four_fun (φ : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ) :
    (∑ I0 : Fin 4 → Fin 2, φ (I0 0) (I0 1) (I0 2) (I0 3)) =
      ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2, ∑ l : Fin 2, φ i j k l := by
  rw [sum_fin_succ_fun]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_fin_succ_fun]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sum_fin_succ_fun]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sum_fin_succ_fun]
  refine Finset.sum_congr rfl fun l _ => ?_
  exact sum_fin_zero_fun' _ _ fun _ => rfl

theorem normSq0S_metricRm04At_eq_sq_of_finrank_two (hdim : Module.finrank ℝ E = 2)
    (g : SmoothRiemannianMetric I M) (x : M) :
    normSq0S g x 4 (metricRm04At g x) = metricScalarAt g x ^ 2 := by
  classical
  obtain ⟨basis, horth⟩ := exists_orthonormalBasis_of_finrank_two g x hdim
  let δ : Fin 2 → Fin 2 → ℝ := fun i j => if i = j then 1 else 0
  have hinv : MetricInverseInBasis (I := I) g x basis δ := by
    intro i j
    constructor <;> simp [δ, horth]
  rw [normSq0S_eq_coord g x 4 basis δ hinv]
  unfold coordInner0S
  have hcontract : ∀ I0 : Fin 4 → Fin 2,
      (∑ J0 : Fin 4 → Fin 2, (∏ a : Fin 4, δ (I0 a) (J0 a)) *
        tensor0SComponent (I := I) (metricRm04At g x) (fun i => basis i) I0 *
        tensor0SComponent (I := I) (metricRm04At g x) (fun i => basis i) J0) =
      tensor0SComponent (I := I) (metricRm04At g x) (fun i => basis i) I0 ^ 2 := by
    intro I0
    rw [Finset.sum_eq_single I0]
    · simp [δ, sq]
    · intro J0 _ hJ
      have hne : ∃ a, I0 a ≠ J0 a := by
        by_contra hall
        push Not at hall
        exact hJ (funext fun a => (hall a).symm)
      obtain ⟨a, ha⟩ := hne
      rw [Finset.prod_eq_zero (Finset.mem_univ a) (by simp [δ, ha])]
      ring
    · intro h
      exact absurd (Finset.mem_univ I0) h
  simp only [hcontract]
  have hcomp : ∀ I0 : Fin 4 → Fin 2,
      tensor0SComponent (I := I) (metricRm04At g x) (fun i => basis i) I0 =
        metricScalarAt g x / 2 * (δ (I0 0) (I0 3) * δ (I0 1) (I0 2) -
          δ (I0 0) (I0 2) * δ (I0 1) (I0 3)) := by
    intro I0
    have h := metricRm04StdAt_eq_scalar_div_two_of_finrank_eq_two g hdim x
      (basis (I0 0)) (basis (I0 1)) (basis (I0 2)) (basis (I0 3))
    simp only [metricRm04StandardAt_apply, horth] at h
    unfold tensor0SComponent
    have hv : (fun a : Fin 4 => basis (I0 a)) =
        vec4 (basis (I0 0)) (basis (I0 1)) (basis (I0 2)) (basis (I0 3)) := by
      funext a
      fin_cases a <;> rfl
    rw [hv, h]
  simp only [hcomp]
  rw [sum_fin_four_fun
    (fun i j k l => (metricScalarAt g x / 2 * (δ i l * δ j k - δ i k * δ j l)) ^ 2)]
  simp only [Fin.sum_univ_two, δ]
  simp
  ring

end GC.Geometry
