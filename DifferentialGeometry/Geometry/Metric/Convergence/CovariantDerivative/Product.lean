import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Algebra
import DifferentialGeometry.Geometry.Curvature.Product
import DifferentialGeometry.Geometry.Connection.Product
import DifferentialGeometry.Geometry.VectorField.Product
import DifferentialGeometry.Tensor.Multilinear.Bundle.Evaluation

noncomputable section
open Bundle Manifold Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.VectorField
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [CompleteSpace F]
variable {K : Type*} [TopologicalSpace K] {J : ModelWithCorners ℝ F K}
variable {N : Type*} [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N] [SigmaCompactSpace N]

omit [CompleteSpace E] [CompleteSpace F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [IsManifold J ∞ N] [T2Space N]
    [SigmaCompactSpace N] in
theorem mvfderiv_comp_fst (f : M → ℝ) (x : M × N) (v : TangentSpace (I.prod J) x)
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x.1) :
    mvfderiv (I.prod J) (fun y : M × N => f y.1) x v = mvfderiv I f x.1 v.1 := by
  have h := mvfderiv_comp (I := I) (I' := I.prod J) (M := M) (M' := M × N)
    (f := Prod.fst) (g := f) x hf (mdifferentiableAt_fst (I := I) (I' := J))
  simp only [mfderiv_fst] at h
  exact congrArg (fun L : TangentSpace (I.prod J) x →L[ℝ] ℝ => L v) h

omit [SigmaCompactSpace M] [SigmaCompactSpace N] in
theorem iterCov_prod_flat_apply [I.Boundaryless] [J.Boundaryless]
    [BoundarylessManifold I M] [BoundarylessManifold J N]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (hflat : ∀ (y : N) (w : Fin 4 → TangentSpace J y), metricRm04At h y w = 0) :
    ∀ (m : ℕ) (x : M × N) (v : Fin (4 + m) → TangentSpace (I.prod J) x),
      iterCov (g.prod h) 4 (metricRm04 (g.prod h)) m x v =
        iterCov g 4 (metricRm04 g) m x.1 (fun i => (v i).1) := by
  intro m
  induction m with
  | zero =>
      intro x v
      have h0L : iterCov (g.prod h) 4 (metricRm04 (g.prod h)) 0 = metricRm04 (g.prod h) := rfl
      have h0R : iterCov g 4 (metricRm04 g) 0 = metricRm04 g := rfl
      rw [h0L, h0R, metricRm04_apply, metricRm04_apply, metricRm04At_productMetric_apply,
        hflat x.2 (fun k => (v k).2), add_zero]
  | succ m ih =>
      intro x v
      obtain ⟨Xs, hXs⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
        (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x.1 (v 0).1
      obtain ⟨Zs, hZs⟩ := ContMDiffSection.exists_eq_at (I := J) (F := F)
        (V := (TangentSpace J : N → Type _)) (n := (⊤ : ℕ∞)) x.2 (v 0).2
      choose Ws hWs using fun q : Fin (4 + m) =>
        ContMDiffSection.exists_eq_at (I := I) (F := E)
          (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x.1 (v q.succ).1
      choose Ts hTs using fun q : Fin (4 + m) =>
        ContMDiffSection.exists_eq_at (I := J) (F := F)
          (V := (TangentSpace J : N → Type _)) (n := (⊤ : ℕ∞)) x.2 (v q.succ).2
      set X : ContMDiffSection (I.prod J) (E × F) ∞
          (TangentSpace (I.prod J) : M × N → Type _) := productVectorField Xs Zs with hXdef
      set V : Fin (4 + m) → ContMDiffSection (I.prod J) (E × F) ∞
          (TangentSpace (I.prod J) : M × N → Type _) :=
        fun q => productVectorField (Ws q) (Ts q) with hVdef
      have hX_eq : X x = v 0 := by
        rw [hXdef, productVectorField_apply]
        exact Prod.ext hXs hZs
      have hV_eq : ∀ q : Fin (4 + m), V q x = v q.succ := by
        intro q
        rw [hVdef, productVectorField_apply]
        exact Prod.ext (hWs q) (hTs q)
      have hv : v = Fin.cons (X x) (fun q : Fin (4 + m) => V q x) := by
        funext i
        refine Fin.cases ?_ ?_ i
        · exact hX_eq.symm
        · intro j
          exact (hV_eq j).symm
      have hcompR : (fun i : Fin (4 + (m + 1)) => (v i).1)
          = (Fin.cons (Xs x.1) (fun q : Fin (4 + m) => Ws q x.1) :
              Fin (4 + (m + 1)) → TangentSpace I x.1) := by
        funext i
        refine Fin.cases ?_ ?_ i
        · exact hXs.symm
        · intro j
          exact (hWs j).symm
      have hA : iterCov (g.prod h) 4 (metricRm04 (g.prod h)) (m + 1)
          = covStep (g.prod h) (4 + m)
              (iterCov (g.prod h) 4 (metricRm04 (g.prod h)) m) := rfl
      have hB : iterCov g 4 (metricRm04 g) (m + 1)
          = covStep g (4 + m) (iterCov g 4 (metricRm04 g) m) := rfl
      conv_lhs => rw [hv]
      rw [hA, hB, hcompR,
        covStep_eval_smooth_slots (I := I.prod J) (g₂ := g.prod h) (r := 4 + m)
          (A := iterCov (g.prod h) 4 (metricRm04 (g.prod h)) m) (X := X) (V := V) x,
        covStep_eval_smooth_slots (I := I) (g₂ := g) (r := 4 + m)
          (A := iterCov g 4 (metricRm04 g) m) (X := Xs) (V := Ws) x.1]
      congr 1
      · have hfun : (fun y : M × N =>
            iterCov (g.prod h) 4 (metricRm04 (g.prod h)) m y (fun q : Fin (4 + m) => V q y))
            = fun y : M × N => iterCov g 4 (metricRm04 g) m y.1
                (fun q : Fin (4 + m) => Ws q y.1) := by
          funext y
          exact ih y (fun q => V q y)
        rw [hfun]
        have hdiff : MDifferentiableAt I 𝓘(ℝ, ℝ)
            (fun y₁ : M => iterCov g 4 (metricRm04 g) m y₁ (fun q : Fin (4 + m) => Ws q y₁))
            x.1 :=
          (TensorMultilinear.contMDiff_tensor0SField_apply (I := I) (M := M) (𝕜 := ℝ)
            (n := 4 + m) (T := iterCov g 4 (metricRm04 g) m) Ws).mdifferentiableAt (by simp)
        have hXval : X x = (Xs x.1, Zs x.2) := by rw [hXdef, productVectorField_apply]
        rw [hXval]
        exact mvfderiv_comp_fst (I := I) (J := J) (N := N)
          (fun y₁ : M => iterCov g 4 (metricRm04 g) m y₁ (fun q : Fin (4 + m) => Ws q y₁))
          x (Xs x.1, Zs x.2) hdiff
      · refine Finset.sum_congr rfl (fun q _ => ?_)
        rw [ih x (Function.update (fun b : Fin (4 + m) => V b x) q
          (((leviCivitaConnectionOfMetric (g.prod h)) (fun y => V q y) x) (X x)))]
        congr 1
        funext i
        by_cases hi : i = q
        · rw [hi]
          rw [Function.update_self, Function.update_self]
          have hwval : ((leviCivitaConnectionOfMetric (g.prod h)) (fun y => V q y) x) (X x)
              = leviCivitaConnectionOfMetric (g.prod h) (productVectorField (Ws q) (Ts q)) x
                  (productVectorField Xs Zs x) := by rw [hVdef, hXdef]
          rw [hwval]
          rw [leviCivita_productVectorField_apply]
          simp only [productVectorField_apply]
          rfl
        · rw [Function.update_of_ne hi, Function.update_of_ne hi]
          rw [hVdef, productVectorField_apply]

omit [SigmaCompactSpace M] [SigmaCompactSpace N] in
theorem iterCov_ricci_prod_flat_apply [I.Boundaryless] [J.Boundaryless]
    [BoundarylessManifold I M] [BoundarylessManifold J N]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (hflat : ∀ (y : N) (w : Fin 2 → TangentSpace J y), metricRicciAt h y w = 0) :
    ∀ (m : ℕ) (x : M × N) (v : Fin (2 + m) → TangentSpace (I.prod J) x),
      iterCov (g.prod h) 2 (metricRicci (g.prod h)) m x v =
        iterCov g 2 (metricRicci g) m x.1 (fun i => (v i).1) := by
  intro m
  induction m with
  | zero =>
      intro x v
      have h0L : iterCov (g.prod h) 2 (metricRicci (g.prod h)) 0 = metricRicci (g.prod h) := rfl
      have h0R : iterCov g 2 (metricRicci g) 0 = metricRicci g := rfl
      rw [h0L, h0R, metricRicci_apply, metricRicci_apply, metricRicciAt_productMetric_apply,
        hflat x.2 (fun k => (v k).2), add_zero]
  | succ m ih =>
      intro x v
      obtain ⟨Xs, hXs⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
        (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x.1 (v 0).1
      obtain ⟨Zs, hZs⟩ := ContMDiffSection.exists_eq_at (I := J) (F := F)
        (V := (TangentSpace J : N → Type _)) (n := (⊤ : ℕ∞)) x.2 (v 0).2
      choose Ws hWs using fun q : Fin (2 + m) =>
        ContMDiffSection.exists_eq_at (I := I) (F := E)
          (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x.1 (v q.succ).1
      choose Ts hTs using fun q : Fin (2 + m) =>
        ContMDiffSection.exists_eq_at (I := J) (F := F)
          (V := (TangentSpace J : N → Type _)) (n := (⊤ : ℕ∞)) x.2 (v q.succ).2
      set X : ContMDiffSection (I.prod J) (E × F) ∞
          (TangentSpace (I.prod J) : M × N → Type _) := productVectorField Xs Zs with hXdef
      set V : Fin (2 + m) → ContMDiffSection (I.prod J) (E × F) ∞
          (TangentSpace (I.prod J) : M × N → Type _) :=
        fun q => productVectorField (Ws q) (Ts q) with hVdef
      have hX_eq : X x = v 0 := by
        rw [hXdef, productVectorField_apply]
        exact Prod.ext hXs hZs
      have hV_eq : ∀ q : Fin (2 + m), V q x = v q.succ := by
        intro q
        rw [hVdef, productVectorField_apply]
        exact Prod.ext (hWs q) (hTs q)
      have hv : v = Fin.cons (X x) (fun q : Fin (2 + m) => V q x) := by
        funext i
        refine Fin.cases ?_ ?_ i
        · exact hX_eq.symm
        · intro j
          exact (hV_eq j).symm
      have hcompR : (fun i : Fin (2 + (m + 1)) => (v i).1)
          = (Fin.cons (Xs x.1) (fun q : Fin (2 + m) => Ws q x.1) :
              Fin (2 + (m + 1)) → TangentSpace I x.1) := by
        funext i
        refine Fin.cases ?_ ?_ i
        · exact hXs.symm
        · intro j
          exact (hWs j).symm
      have hA : iterCov (g.prod h) 2 (metricRicci (g.prod h)) (m + 1)
          = covStep (g.prod h) (2 + m)
              (iterCov (g.prod h) 2 (metricRicci (g.prod h)) m) := rfl
      have hB : iterCov g 2 (metricRicci g) (m + 1)
          = covStep g (2 + m) (iterCov g 2 (metricRicci g) m) := rfl
      conv_lhs => rw [hv]
      rw [hA, hB, hcompR,
        covStep_eval_smooth_slots (I := I.prod J) (g₂ := g.prod h) (r := 2 + m)
          (A := iterCov (g.prod h) 2 (metricRicci (g.prod h)) m) (X := X) (V := V) x,
        covStep_eval_smooth_slots (I := I) (g₂ := g) (r := 2 + m)
          (A := iterCov g 2 (metricRicci g) m) (X := Xs) (V := Ws) x.1]
      congr 1
      · have hfun : (fun y : M × N =>
            iterCov (g.prod h) 2 (metricRicci (g.prod h)) m y (fun q : Fin (2 + m) => V q y))
            = fun y : M × N => iterCov g 2 (metricRicci g) m y.1
                (fun q : Fin (2 + m) => Ws q y.1) := by
          funext y
          exact ih y (fun q => V q y)
        rw [hfun]
        have hdiff : MDifferentiableAt I 𝓘(ℝ, ℝ)
            (fun y₁ : M => iterCov g 2 (metricRicci g) m y₁ (fun q : Fin (2 + m) => Ws q y₁))
            x.1 :=
          (TensorMultilinear.contMDiff_tensor0SField_apply (I := I) (M := M) (𝕜 := ℝ)
            (n := 2 + m) (T := iterCov g 2 (metricRicci g) m) Ws).mdifferentiableAt (by simp)
        have hXval : X x = (Xs x.1, Zs x.2) := by rw [hXdef, productVectorField_apply]
        rw [hXval]
        exact mvfderiv_comp_fst (I := I) (J := J) (N := N)
          (fun y₁ : M => iterCov g 2 (metricRicci g) m y₁ (fun q : Fin (2 + m) => Ws q y₁))
          x (Xs x.1, Zs x.2) hdiff
      · refine Finset.sum_congr rfl (fun q _ => ?_)
        rw [ih x (Function.update (fun b : Fin (2 + m) => V b x) q
          (((leviCivitaConnectionOfMetric (g.prod h)) (fun y => V q y) x) (X x)))]
        congr 1
        funext i
        by_cases hi : i = q
        · rw [hi]
          rw [Function.update_self, Function.update_self]
          have hwval : ((leviCivitaConnectionOfMetric (g.prod h)) (fun y => V q y) x) (X x)
              = leviCivitaConnectionOfMetric (g.prod h) (productVectorField (Ws q) (Ts q)) x
                  (productVectorField Xs Zs x) := by rw [hVdef, hXdef]
          rw [hwval]
          rw [leviCivita_productVectorField_apply]
          simp only [productVectorField_apply]
          rfl
        · rw [Function.update_of_ne hi, Function.update_of_ne hi]
          rw [hVdef, productVectorField_apply]

set_option backward.isDefEq.respectTransparency false in
omit [CompleteSpace E] [CompleteSpace F] [SigmaCompactSpace M] [SigmaCompactSpace N] in
theorem normSq0S_prod_of_forall_fst [I.Boundaryless] [J.Boundaryless]
    [BoundarylessManifold I M] [BoundarylessManifold J N]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (x : M × N) (s : ℕ) (T : Tensor0SSpace s (I.prod J) x) (T' : Tensor0SSpace s I x.1)
    (hT : ∀ slots : Fin s → TangentSpace (I.prod J) x, T slots = T' (fun i => (slots i).1)) :
    normSq0S (g.prod h) x s T = normSq0S g x.1 s T' := by
  classical
  obtain ⟨b₁, hb₁⟩ := exists_orthonormal_basis g x.1
  obtain ⟨b₂, hb₂⟩ := exists_orthonormal_basis h x.2
  let b : Module.Basis
      (Fin (Module.finrank ℝ (TangentSpace I x.1)) ⊕
        Fin (Module.finrank ℝ (TangentSpace J x.2))) ℝ
      (TangentSpace (I.prod J) x) := b₁.prod b₂
  have b_inl (i : Fin (Module.finrank ℝ (TangentSpace I x.1))) :
      b (Sum.inl i) = (b₁ i, 0) := by
    apply Prod.ext
    · exact Module.Basis.prod_apply_inl_fst b₁ b₂ i
    · exact Module.Basis.prod_apply_inl_snd b₁ b₂ i
  have b_inr (i : Fin (Module.finrank ℝ (TangentSpace J x.2))) :
      b (Sum.inr i) = (0, b₂ i) := by
    apply Prod.ext
    · exact Module.Basis.prod_apply_inr_fst b₁ b₂ i
    · exact Module.Basis.prod_apply_inr_snd b₁ b₂ i
  have hb : ∀ i j, (g.prod h).inner x (b i) (b j) = if i = j then (1 : ℝ) else 0 := by
    intro i j
    rcases i with i | i
    · rcases j with j | j
      · rw [b_inl, b_inl, SmoothRiemannianMetric.prod_inner]
        change g.inner x.1 (b₁ i) (b₁ j) + h.inner x.2 0 0 = _
        rw [hb₁]
        simp
      · rw [b_inl, b_inr, SmoothRiemannianMetric.prod_inner]
        change g.inner x.1 (b₁ i) 0 + h.inner x.2 0 (b₂ j) = _
        simp
    · rcases j with j | j
      · rw [b_inr, b_inl, SmoothRiemannianMetric.prod_inner]
        change g.inner x.1 0 (b₁ j) + h.inner x.2 (b₂ i) 0 = _
        simp
      · rw [b_inr, b_inr, SmoothRiemannianMetric.prod_inner]
        change g.inner x.1 0 0 + h.inner x.2 (b₂ i) (b₂ j) = _
        rw [hb₂]
        simp
  rw [normSq0S_identity_eq_sum_sq (g.prod h) x s b
      (metricInverseInBasis_identity_of_orthonormal (g.prod h) b hb),
    normSq0S_identity_eq_sum_sq g x.1 s b₁
      (metricInverseInBasis_identity_of_orthonormal g b₁ hb₁)]
  simp only [component0S_apply]
  let e : (Fin s → Fin (Module.finrank ℝ (TangentSpace I x.1))) →
      (Fin s → Fin (Module.finrank ℝ (TangentSpace I x.1)) ⊕
        Fin (Module.finrank ℝ (TangentSpace J x.2))) :=
    fun t k => Sum.inl (t k)
  have he : Function.Injective e := by
    intro a c hac
    funext k
    exact Sum.inl.inj (congrFun hac k)
  symm
  apply Fintype.sum_of_injective e he
  · intro t ht
    have hz : ∃ k j, t k = Sum.inr j := by
      by_contra hz
      have hl : ∀ k, ∃ i, t k = Sum.inl i := by
        intro k
        cases htk : t k with
        | inl i => exact ⟨i, rfl⟩
        | inr j => exact absurd ⟨k, j, htk⟩ hz
      choose u hu using hl
      exact ht ⟨u, funext (fun k => (hu k).symm)⟩
    obtain ⟨k, j, hkj⟩ := hz
    have hzero : T (fun a => b (t a)) = 0 := by
      rw [hT]
      exact T'.map_coord_zero k (by rw [hkj, b_inr])
    rw [hzero]
    simp
  · intro t
    have h1 : T (fun k => b (e t k)) = T' (fun k => b₁ (t k)) := by
      rw [hT]
      congr 1
      funext k
      simp only [e]
      exact congrArg Prod.fst (b_inl (t k))
    rw [h1]

end DifferentialGeometry.CheegerGromovCompactness
