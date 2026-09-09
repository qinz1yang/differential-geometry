import DifferentialGeometry.Geometry.Metric.Product
import DifferentialGeometry.Geometry.Metric.Euclidean
import DifferentialGeometry.Geometry.Curvature.DimensionOne.Flat
import DifferentialGeometry.Geometry.Curvature.RicciOperatorNormBound
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Nullity

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [T2Space N]

set_option backward.isDefEq.respectTransparency false in
theorem metricRm04At_prod_apply
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (x : M × N) (v : Fin 4 → TangentSpace (I.prod J) x) :
    metricRm04At (g.prod h) x v =
      metricRm04At g x.1 (fun k => (v k).1) +
        metricRm04At h x.2 (fun k => (v k).2) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : CompleteSpace F := FiniteDimensional.complete ℝ F
  have hv : v = vec4 (I := I.prod J) (x := x) (v 0) (v 1) (v 2) (v 3) := by
    ext k
    fin_cases k <;> rfl
  have hv₁ : (fun k => (v k).1) = vec4 (I := I) (x := x.1) (v 0).1 (v 1).1 (v 2).1 (v 3).1 := by
    ext k
    fin_cases k <;> rfl
  have hv₂ : (fun k => (v k).2) = vec4 (I := J) (x := x.2) (v 0).2 (v 1).2 (v 2).2 (v 3).2 := by
    ext k
    fin_cases k <;> rfl
  rw [hv₁, hv₂, hv]
  change metricRm04StdAt (g.prod h) x (v 0) (v 1) (v 2) (v 3) =
    metricRm04StdAt g x.1 (v 0).1 (v 1).1 (v 2).1 (v 3).1 +
      metricRm04StdAt h x.2 (v 0).2 (v 1).2 (v 2).2 (v 3).2
  rw [rm04_eq_inner_riem, rm04_eq_inner_riem, rm04_eq_inner_riem,
    riemannOp_prod, SmoothRiemannianMetric.prod_inner, mfderiv_fst, mfderiv_snd]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem normSq0S_metricRm04At_prod_of_eq_zero
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (x : M × N) (hflat : metricRm04At h x.2 = 0) :
    normSq0S (g.prod h) x 4 (metricRm04At (g.prod h) x) =
      normSq0S g x.1 4 (metricRm04At g x.1) := by
  classical
  obtain ⟨b₁, hb₁⟩ := exists_gOrthonormalBasis g x.1
  obtain ⟨b₂, hb₂⟩ := exists_gOrthonormalBasis h x.2
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
  have hb : ∀ i j, (g.prod h).inner x (b i) (b j) =
      if i = j then (1 : ℝ) else 0 := by
    intro i j
    rcases i with i | i
    · rcases j with j | j
      · rw [b_inl, b_inl, SmoothRiemannianMetric.prod_inner, mfderiv_fst, mfderiv_snd]
        change g.inner x.1 (b₁ i) (b₁ j) + h.inner x.2 0 0 = _
        rw [hb₁]
        simp
      · rw [b_inl, b_inr, SmoothRiemannianMetric.prod_inner, mfderiv_fst, mfderiv_snd]
        change g.inner x.1 (b₁ i) 0 + h.inner x.2 0 (b₂ j) = _
        simp
    · rcases j with j | j
      · rw [b_inr, b_inl, SmoothRiemannianMetric.prod_inner, mfderiv_fst, mfderiv_snd]
        change g.inner x.1 0 (b₁ j) + h.inner x.2 (b₂ i) 0 = _
        simp
      · rw [b_inr, b_inr, SmoothRiemannianMetric.prod_inner, mfderiv_fst, mfderiv_snd]
        change g.inner x.1 0 0 + h.inner x.2 (b₂ i) (b₂ j) = _
        rw [hb₂]
        simp
  have hflat_eval (v : Fin 4 → TangentSpace J x.2) : metricRm04At h x.2 v = 0 := by
    rw [hflat]
    rfl
  rw [normSq0S_identity_eq_sum_sq (g.prod h) x 4 b
      (metricInverseInBasis_identity_of_orthonormal (g.prod h) b hb),
    normSq0S_identity_eq_sum_sq g x.1 4 b₁
      (metricInverseInBasis_identity_of_orthonormal g b₁ hb₁)]
  simp only [component0S_apply, metricRm04At_prod_apply, hflat_eval, add_zero]
  let e : (Fin 4 → Fin (Module.finrank ℝ (TangentSpace I x.1))) →
      (Fin 4 → Fin (Module.finrank ℝ (TangentSpace I x.1)) ⊕
        Fin (Module.finrank ℝ (TangentSpace J x.2))) :=
    fun s k => Sum.inl (s k)
  have he : Function.Injective e := by
    intro s t hst
    funext k
    exact Sum.inl.inj (congrFun hst k)
  symm
  apply Fintype.sum_of_injective e he
  · intro s hs
    have hz : ∃ k j, s k = Sum.inr j := by
      by_contra hz
      have hl : ∀ k, ∃ i, s k = Sum.inl i := by
        intro k
        cases hsk : s k with
        | inl i => exact ⟨i, rfl⟩
        | inr j => exact False.elim (hz ⟨k, j, hsk⟩)
      choose u hu using hl
      exact hs ⟨u, funext (fun k => (hu k).symm)⟩
    obtain ⟨k, j, hkj⟩ := hz
    have hzero : metricRm04At g x.1 (fun a => (b (s a)).1) = 0 := by
      apply (metricRm04At g x.1).map_coord_zero k
      rw [hkj, b_inr]
    simp only [hzero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  · intro s
    congr 1
    congr 1
    funext k
    exact (congrArg Prod.fst (b_inl (s k))).symm

theorem normSq0S_metricRm04At_prod_real
    (g : SmoothRiemannianMetric I M) (x : M × ℝ) :
    normSq0S (g.prod (euclideanMetric (E := ℝ))) x 4
        (metricRm04At (g.prod (euclideanMetric (E := ℝ))) x) =
      normSq0S g x.1 4 (metricRm04At g x.1) := by
  exact normSq0S_metricRm04At_prod_of_eq_zero g (euclideanMetric (E := ℝ)) x
    (metricRm04At_eq_zero_of_finrank_le_one (euclideanMetric (E := ℝ)) (by simp) x.2)

theorem riemannOp_prod_real_vertical_eq_zero
    (g : SmoothRiemannianMetric I M) (x : M × ℝ)
    (u v : TangentSpace (I.prod 𝓘(ℝ, ℝ)) x) (r : ℝ) :
    riemannOp (Connection.LeviCivita (g.prod (euclideanMetric (E := ℝ))))
      x u v (0, r) = 0 := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have h := riemannOp_prod g (euclideanMetric (E := ℝ)) x u v
    (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) x from (0, r))
  apply h.trans
  apply Prod.ext
  · exact (riemannOp (Connection.LeviCivita g) x.1 u.1 v.1).map_zero
  · exact riemannOp_eq_zero_of_finrank_le_one _
      (by simp : Module.finrank ℝ ℝ ≤ 1) _ _ _ _

theorem prod_real_vertical_mem_curvatureOperatorImageAnnihilatorAt
    (g : SmoothRiemannianMetric I M) (x : M × ℝ) (r : ℝ) :
    (0, r) ∈ curvatureOperatorImageAnnihilatorAt
      (g.prod (euclideanMetric (E := ℝ))) x
      ⟨metricRm04At (g.prod (euclideanMetric (E := ℝ))) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (g.prod (euclideanMetric (E := ℝ))) x⟩ := by
  apply (mem_curvatureOperatorImageAnnihilatorAt_iff_tensor04StdAt_eq_zero _ _ _ _).mpr
  intro a b w
  change metricRm04StdAt (g.prod (euclideanMetric (E := ℝ))) x a b (0, r) w = 0
  have h := DifferentialGeometry.rm04_eq_inner_riem
    (g.prod (euclideanMetric (E := ℝ))) x a b
      (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) x from (0, r)) w
  rw [riemannOp_prod_real_vertical_eq_zero] at h
  simpa only [map_zero] using h

theorem ricciTensor_prod_real_vertical_eq_zero
    (g : SmoothRiemannianMetric I M) (x : M × ℝ) (r : ℝ)
    (w : TangentSpace (I.prod 𝓘(ℝ, ℝ)) x) :
    ricciTensor (g.prod (euclideanMetric (E := ℝ))) x (0, r) w = 0 := by
  exact ricciTensor_eq_zero_of_mem_curvatureOperatorImageAnnihilatorAt _ _
    (prod_real_vertical_mem_curvatureOperatorImageAnnihilatorAt g x r) w

end DifferentialGeometry.Geometry.Curvature
