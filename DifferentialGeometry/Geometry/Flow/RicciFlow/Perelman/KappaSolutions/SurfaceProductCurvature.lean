import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RiemannianProduct
import DifferentialGeometry.Geometry.Curvature.Bounds.RicciOperatorNorm
import DifferentialGeometry.Geometry.Curvature.Algebraic.CurvatureOperatorConeMetric
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison
import Mathlib.LinearAlgebra.Basis.Prod

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private def surfaceProduct_basis {Idx : Type*} {y : M}
    (b : Module.Basis Idx ℝ (TangentSpace I y)) (s : ℝ) :
    Module.Basis (Idx ⊕ Unit) ℝ (TangentSpace (I.prod 𝓘(ℝ, ℝ)) (y, s)) := by
  with_unfolding_all exact b.prod (Module.Basis.singleton Unit ℝ)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private theorem surfaceProduct_basis_inl {Idx : Type*} {y : M}
    (b : Module.Basis Idx ℝ (TangentSpace I y)) (s : ℝ) (i : Idx) :
    surfaceProduct_basis b s (Sum.inl i) = (b i, 0) := by
  exact Prod.ext (b.prod_apply_inl_fst (Module.Basis.singleton Unit ℝ) i)
    (b.prod_apply_inl_snd (Module.Basis.singleton Unit ℝ) i)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private theorem surfaceProduct_basis_inr {Idx : Type*} {y : M}
    (b : Module.Basis Idx ℝ (TangentSpace I y)) (s : ℝ) (i : Unit) :
    surfaceProduct_basis b s (Sum.inr i) = (0, 1) := by
  exact Prod.ext (b.prod_apply_inr_fst (Module.Basis.singleton Unit ℝ) i)
    ((b.prod_apply_inr_snd (Module.Basis.singleton Unit ℝ) i).trans
      (Module.Basis.singleton_apply Unit ℝ i))

omit [FiniteDimensional ℝ E] in
private theorem surfaceProduct_basis_orthonormal {Idx : Type*} [DecidableEq Idx]
    (h : SmoothRiemannianMetric I M)
    (gP : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))
    (hproduct : ∀ (y : M) (s : ℝ) (v w : TangentSpace I y) (a c : ℝ),
      gP.inner (y, s) (v, a) (w, c) = h.inner y v w + a * c)
    {y : M} (b : Module.Basis Idx ℝ (TangentSpace I y))
    (hb : ∀ i j, h.inner y (b i) (b j) = if i = j then (1 : ℝ) else 0)
    (s : ℝ) :
    ∀ i j, gP.inner (y, s) (surfaceProduct_basis b s i) (surfaceProduct_basis b s j) =
      if i = j then (1 : ℝ) else 0 := by
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · simp only [surfaceProduct_basis_inl, Sum.inl.injEq]
    exact (hproduct y s (b i) (b j) 0 0).trans
      (by simpa only [zero_mul, add_zero] using hb i j)
  · simp only [surfaceProduct_basis_inl, surfaceProduct_basis_inr,
      Sum.inl_ne_inr, ↓reduceIte]
    exact (hproduct y s (b i) 0 0 1).trans (by simp)
  · simp only [surfaceProduct_basis_inl, surfaceProduct_basis_inr,
      Sum.inr_ne_inl, ↓reduceIte]
    exact (hproduct y s 0 (b j) 1 0).trans (by simp)
  · simp only [surfaceProduct_basis_inr, Subsingleton.elim i j, ↓reduceIte]
    exact (hproduct y s 0 0 1 1).trans (by simp)

variable [CompleteSpace E]

private theorem surfaceProduct_curvature_fst
    (h : SmoothRiemannianMetric I M)
    (gP : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))
    (hproduct : ∀ (y : M) (s : ℝ) (v w : TangentSpace I y) (a c : ℝ),
      gP.inner (y, s) (v, a) (w, c) = h.inner y v w + a * c)
    (y : M) (s : ℝ)
    (v : Fin 4 → TangentSpace (I.prod 𝓘(ℝ, ℝ)) (y, s)) :
    metricRm04At (I := I.prod 𝓘(ℝ, ℝ)) gP (y, s) v =
      metricRm04At (I := I) h y (fun a => (v a).1) := by
  have hpair : (fun a : Fin 4 => ((v a).1, (v a).2)) = v := by
    funext a
    exact Prod.eta (v a)
  exact (congrArg (fun w : Fin 4 → TangentSpace (I.prod 𝓘(ℝ, ℝ)) (y, s) =>
    metricRm04At (I := I.prod 𝓘(ℝ, ℝ)) gP (y, s) w) hpair).symm.trans
    (metricRm04At_product_real_of_inner_eq h gP hproduct y s
      (fun a => (v a).1) (fun a => (v a).2))

theorem metricRmNormSq_product_real_of_inner_eq
    (h : SmoothRiemannianMetric I M)
    (gP : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))
    (hproduct : ∀ (y : M) (s : ℝ) (v w : TangentSpace I y) (a c : ℝ),
      gP.inner (y, s) (v, a) (w, c) = h.inner y v w + a * c)
    (y : M) (s : ℝ) :
    normSq0S (I := I.prod 𝓘(ℝ, ℝ)) gP (y, s) 4
        (metricRm04At (I := I.prod 𝓘(ℝ, ℝ)) gP (y, s)) =
      normSq0S (I := I) h y 4 (metricRm04At (I := I) h y) := by
  classical
  obtain ⟨b, hb⟩ := exists_orthonormal_basis (I := I) h y
  let Idx := Fin (Module.finrank ℝ (TangentSpace I y))
  let bP := surfaceProduct_basis b s
  have hbP := surfaceProduct_basis_orthonormal h gP hproduct b hb s
  have hinv := metricInverseInBasis_identity_of_orthonormal (I := I) h b hb
  have hinvP := metricInverseInBasis_identity_of_orthonormal
    (I := I.prod 𝓘(ℝ, ℝ)) gP bP hbP
  rw [normSq0S_identity_eq_sum_sq (I := I.prod 𝓘(ℝ, ℝ)) gP (y, s) 4 bP hinvP,
    normSq0S_identity_eq_sum_sq (I := I) h y 4 b hinv]
  have hcomp (slots : Fin 4 → Idx ⊕ Unit) :
      component0S (I := I.prod 𝓘(ℝ, ℝ)) bP
          (metricRm04At (I := I.prod 𝓘(ℝ, ℝ)) gP (y, s)) slots =
        metricRm04At (I := I) h y (fun a => (bP (slots a)).1) := by
    rw [component0S_apply]
    exact surfaceProduct_curvature_fst h gP hproduct y s (fun a => bP (slots a))
  let e : (Fin 4 → Idx) → (Fin 4 → Idx ⊕ Unit) :=
    fun slots a => Sum.inl (slots a)
  have he : Function.Injective e := by
    intro v w hvw
    funext a
    exact Sum.inl_injective (congrFun hvw a)
  symm
  refine Fintype.sum_of_injective e he _ _ ?_ ?_
  · intro slots hnot
    have hright : ∃ a : Fin 4, ∃ u : Unit, slots a = Sum.inr u := by
      by_contra hno
      push Not at hno
      have hleft : ∀ a : Fin 4, ∃ i : Idx, Sum.inl i = slots a := by
        intro a
        cases hs : slots a with
        | inl i => exact ⟨i, rfl⟩
        | inr u => exact False.elim (hno a u hs)
      choose f hf using hleft
      apply hnot
      exact ⟨f, funext hf⟩
    obtain ⟨a, u, ha⟩ := hright
    rw [hcomp]
    have hz : metricRm04At (I := I) h y (fun q => (bP (slots q)).1) = 0 := by
      apply (metricRm04At (I := I) h y).map_coord_zero a
      change (bP (slots a)).1 = (0 : TangentSpace I y)
      rw [ha]
      exact congrArg (fun z : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (y, s) => z.1)
        (surfaceProduct_basis_inr b s u)
    rw [hz, zero_pow (by decide : 2 ≠ 0)]
  · intro slots
    rw [hcomp, component0S_apply]
    simp only [e, bP, surfaceProduct_basis_inl]

theorem metricAlgebraicCurvatureTensorAt_product_real_mem_operatorCone_iff
    [T2Space M]
    (h : SmoothRiemannianMetric I M)
    (gP : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))
    (hproduct : ∀ (y : M) (s : ℝ) (v w : TangentSpace I y) (a c : ℝ),
      gP.inner (y, s) (v, a) (w, c) = h.inner y v w + a * c)
    (y : M) (s : ℝ) :
    metricAlgebraicCurvatureTensorAt (I := I.prod 𝓘(ℝ, ℝ)) gP (y, s) ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I.prod 𝓘(ℝ, ℝ)) ↔
      metricAlgebraicCurvatureTensorAt (I := I) h y ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) := by
  have hRm (v w z u : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (y, s)) :
      metricRm04StandardAt (I := I.prod 𝓘(ℝ, ℝ)) gP (y, s) v w z u =
        metricRm04StandardAt (I := I) h y v.1 w.1 z.1 u.1 := by
    have hslots : (fun a : Fin 4 => (vec4 (I := I.prod 𝓘(ℝ, ℝ)) v w z u a).1) =
        vec4 (I := I) (M := M) (x := y) v.1 w.1 z.1 u.1 := by
      funext a
      fin_cases a <;> rfl
    exact (surfaceProduct_curvature_fst h gP hproduct y s
      (vec4 (I := I.prod 𝓘(ℝ, ℝ)) v w z u)).trans
      (congrArg (fun slots : Fin 4 → TangentSpace I y =>
        metricRm04At (I := I) h y slots) hslots)
  rw [metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff,
    metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff]
  constructor
  · intro hp n c v w
    have ht := hp n c (fun i => (v i, 0)) (fun i => (w i, 0))
    apply ht.trans_eq
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    exact congrArg (fun r : ℝ => c i * c j * r)
      (hRm (v i, 0) (w i, 0) (w j, 0) (v j, 0))
  · intro hh n c v w
    have ht := hh n c (fun i => (v i).1) (fun i => (w i).1)
    with_unfolding_all simpa only [hRm] using ht

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
