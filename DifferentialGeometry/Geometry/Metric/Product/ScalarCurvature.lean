import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceProductCurvature

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private local instance productScalarC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

theorem metricScalarAt_eq_sum_sum_rm04_of_orthonormal
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (b : Module.Basis Idx ℝ (TangentSpace I x))
    (hb : ∀ i j, g.inner x (b i) (b j) = if i = j then (1 : ℝ) else 0) :
    metricScalarAt (I := I) g x =
      ∑ i : Idx, ∑ j : Idx,
        metricRm04At (I := I) g x (vec4 (b j) (b i) (b i) (b j)) := by
  let curvature := metricCurvatureSections (I := I) g
  have hLower : Rm04LowersRm13At (I := I) g x
      (metricRm13 (I := I) g x) (metricRm04 (I := I) g x) :=
    rm04LowersRm13At_of_realizes (I := I) g (metricCov (I := I) g)
      (metricRm13 (I := I) g) (metricRm04 (I := I) g)
      curvature.rm13Realizes curvature.rm04Realizes x
  have hRic := ricci_diag_eq_sum_rm04_diag_of_orthonormal
    (I := I) g b (metricRicci (I := I) g) (metricRm13 (I := I) g)
      (metricRm04 (I := I) g) curvature.ricciRealizes hLower hb
  have hinv := metricInverseInBasis_of_orthonormal (I := I) g b hb
  rw [metricScalarAt_def,
    metricTracePair0SAt_eq_sum_basis (I := I) g b _ hinv]
  calc
    _ = ∑ i : Idx, metricRicciAt (I := I) g x (vec2 (b i) (b i)) := by
      simp [identityInvMetric, diagonalInvMetric]
    _ = _ := Finset.sum_congr rfl (fun i _ => hRic i i)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [T2Space M] in
private def productScalar_basis {Idx : Type*} {x : M}
    (b : Module.Basis Idx ℝ (TangentSpace I x)) (s : ℝ) :
    Module.Basis (Idx ⊕ Unit) ℝ (TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, s)) := by
  with_unfolding_all exact b.prod (Module.Basis.singleton Unit ℝ)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [T2Space M] in
private theorem productScalar_basis_inl {Idx : Type*} {x : M}
    (b : Module.Basis Idx ℝ (TangentSpace I x)) (s : ℝ) (i : Idx) :
    productScalar_basis b s (Sum.inl i) = (b i, 0) :=
  Prod.ext (b.prod_apply_inl_fst (Module.Basis.singleton Unit ℝ) i)
    (b.prod_apply_inl_snd (Module.Basis.singleton Unit ℝ) i)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [T2Space M] in
private theorem productScalar_basis_inr {Idx : Type*} {x : M}
    (b : Module.Basis Idx ℝ (TangentSpace I x)) (s : ℝ) (i : Unit) :
    productScalar_basis b s (Sum.inr i) = (0, 1) :=
  Prod.ext (b.prod_apply_inr_fst (Module.Basis.singleton Unit ℝ) i)
    ((b.prod_apply_inr_snd (Module.Basis.singleton Unit ℝ) i).trans
      (Module.Basis.singleton_apply Unit ℝ i))

variable [I.Boundaryless]

theorem metricScalarAt_product_real_of_inner_eq
    (h : SmoothRiemannianMetric I M)
    (gP : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))
    (hproduct : ∀ (x : M) (s : ℝ) (v w : TangentSpace I x) (a b : ℝ),
      gP.inner (x, s) (v, a) (w, b) = h.inner x v w + a * b)
    (x : M) (s : ℝ) :
    metricScalarAt (I := I.prod 𝓘(ℝ, ℝ)) gP (x, s) =
      metricScalarAt (I := I) h x := by
  classical
  obtain ⟨b, hb⟩ := exists_orthonormal_basis (I := I) h x
  let Idx := Fin (Module.finrank ℝ (TangentSpace I x))
  let bP := productScalar_basis b s
  have hbP : ∀ i j, gP.inner (x, s) (bP i) (bP j) =
      if i = j then (1 : ℝ) else 0 := by
    intro i j
    rcases i with i | i <;> rcases j with j | j
    · simp only [bP, productScalar_basis_inl, Sum.inl.injEq]
      exact (hproduct x s (b i) (b j) 0 0).trans
        (by simpa only [zero_mul, add_zero] using hb i j)
    · simp only [bP, productScalar_basis_inl, productScalar_basis_inr,
        Sum.inl_ne_inr, ↓reduceIte]
      exact (hproduct x s (b i) 0 0 1).trans (by simp)
    · simp only [bP, productScalar_basis_inl, productScalar_basis_inr,
        Sum.inr_ne_inl, ↓reduceIte]
      exact (hproduct x s 0 (b j) 1 0).trans (by simp)
    · simp only [bP, productScalar_basis_inr, Subsingleton.elim i j, ↓reduceIte]
      exact (hproduct x s 0 0 1 1).trans (by simp)
  have hRm (i j : Idx ⊕ Unit) :
      metricRm04At (I := I.prod 𝓘(ℝ, ℝ)) gP (x, s)
          (vec4 (bP j) (bP i) (bP i) (bP j)) =
        metricRm04At (I := I) h x
          (vec4 (bP j).1 (bP i).1 (bP i).1 (bP j).1) := by
    let slots := vec4 (I := I.prod 𝓘(ℝ, ℝ)) (bP j) (bP i) (bP i) (bP j)
    have hslots : (fun a : Fin 4 => ((slots a).1, (slots a).2)) = slots := by
      funext a
      exact Prod.eta (slots a)
    have hhorizontal : (fun a : Fin 4 => (slots a).1) =
        vec4 (I := I) (M := M) (x := x) (bP j).1 (bP i).1 (bP i).1 (bP j).1 := by
      funext a
      fin_cases a <;> rfl
    have h := metricRm04At_product_real_of_inner_eq h gP hproduct x s
      (fun a => (slots a).1) (fun a => (slots a).2)
    rw [hslots, hhorizontal] at h
    exact h
  rw [metricScalarAt_eq_sum_sum_rm04_of_orthonormal gP bP hbP,
    metricScalarAt_eq_sum_sum_rm04_of_orthonormal h b hb]
  rw [← Fintype.sum_prod_type (fun q : (Idx ⊕ Unit) × (Idx ⊕ Unit) =>
    metricRm04At (I := I.prod 𝓘(ℝ, ℝ)) gP (x, s)
      (vec4 (bP q.2) (bP q.1) (bP q.1) (bP q.2))),
    ← Fintype.sum_prod_type (fun q : Idx × Idx =>
      metricRm04At (I := I) h x (vec4 (b q.2) (b q.1) (b q.1) (b q.2)))]
  let e : Idx × Idx → (Idx ⊕ Unit) × (Idx ⊕ Unit) :=
    fun q => (Sum.inl q.1, Sum.inl q.2)
  have he : Function.Injective e := by
    intro p q hpq
    exact Prod.ext (Sum.inl_injective (congrArg Prod.fst hpq))
      (Sum.inl_injective (congrArg Prod.snd hpq))
  symm
  refine Fintype.sum_of_injective e he _ _ ?_ ?_
  · rintro ⟨i, j⟩ hnot
    rw [hRm]
    rcases i with i | i <;> rcases j with j | j
    · exact False.elim (hnot ⟨(i, j), rfl⟩)
    · apply (metricRm04At (I := I) h x).map_coord_zero 0
      change (productScalar_basis b s (Sum.inr j)).1 = (0 : TangentSpace I x)
      rw [productScalar_basis_inr]
      rfl
    · apply (metricRm04At (I := I) h x).map_coord_zero 1
      change (productScalar_basis b s (Sum.inr i)).1 = (0 : TangentSpace I x)
      rw [productScalar_basis_inr]
      rfl
    · apply (metricRm04At (I := I) h x).map_coord_zero 0
      change (productScalar_basis b s (Sum.inr j)).1 = (0 : TangentSpace I x)
      rw [productScalar_basis_inr]
      rfl
  · intro p
    rw [hRm]
    simp only [e, bP, productScalar_basis_inl]

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
