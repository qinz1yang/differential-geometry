import DifferentialGeometry.Geometry.Connection.Product
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Ricci.Basic
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Nullity
import DifferentialGeometry.Geometry.Curvature.DimensionOne.Flat
import DifferentialGeometry.Geometry.Curvature.ScalarTrace

noncomputable section
open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Geometry.VectorField DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Tensor0SBundle

namespace DifferentialGeometry.Geometry.Curvature

private def covariantField
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    [BoundarylessManifold I M]
    (g : SmoothRiemannianMetric I M)
    (X Y : ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) :
    ContMDiffSection I E ∞ (TangentSpace I : M → Type _) where
  toFun := covApply (LeviCivita g) X Y
  contMDiff_toFun := contMDiffOn_univ.mp (covApply_contMDiffOn
    (cov := LeviCivita g) X.contMDiff (by simpa using Y.contMDiff))

variable {E H M F K N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [BoundarylessManifold I M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace K] {J : ModelWithCorners ℝ F K}
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N]
  [BoundarylessManifold J N]

private theorem riemannSec_product
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (X Y Z : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (X' Y' Z' : ContMDiffSection J F ∞ (TangentSpace J : N → Type _)) (x : M × N) :
    riemannSec (LeviCivita (g.prod h)) (productVectorField X X')
      (productVectorField Y Y') (productVectorField Z Z') x =
        (riemannSec (LeviCivita g) X Y Z x.1, riemannSec (LeviCivita h) X' Y' Z' x.2) := by
  have hc (A B : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
      (A' B' : ContMDiffSection J F ∞ (TangentSpace J : N → Type _)) :
      covApply (LeviCivita (g.prod h)) (productVectorField A A')
          (productVectorField B B') =
        (productVectorField (covariantField g A B) (covariantField h A' B') :
          ∀ y, TangentSpace (I.prod J) y) := by
    funext y
    exact leviCivita_productVectorField g h A B A' B' y
  unfold riemannSec
  rw [hc Y Z Y' Z', hc X Z X' Z']
  change
    leviCivitaConnectionOfMetric (g.prod h)
        (productVectorField (covariantField g Y Z) (covariantField h Y' Z')) x
        (productVectorField X X' x) -
      leviCivitaConnectionOfMetric (g.prod h)
        (productVectorField (covariantField g X Z) (covariantField h X' Z')) x
        (productVectorField Y Y' x) -
      leviCivitaConnectionOfMetric (g.prod h) (productVectorField Z Z') x
        (_root_.VectorField.mlieBracket (I.prod J) (productVectorField X X')
          (productVectorField Y Y') x) = _
  rw [leviCivita_productVectorField, leviCivita_productVectorField,
    leviCivita_productVectorField_apply]
  rw [mlieBracket_productVectorField]
  rfl

theorem riemannOp_productMetric
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (x : M × N) (v w z : TangentSpace (I.prod J) x) :
    riemannOp (LeviCivita (g.prod h)) x v w z =
      (riemannOp (LeviCivita g) x.1 v.1 w.1 z.1,
        riemannOp (LeviCivita h) x.2 v.2 w.2 z.2) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : CompleteSpace F := FiniteDimensional.complete ℝ F
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x.1 v.1
  obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x.1 w.1
  obtain ⟨Z, hZ⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x.1 z.1
  obtain ⟨X', hX'⟩ := ContMDiffSection.exists_eq_at (I := J) (F := F)
    (V := (TangentSpace J : N → Type _)) (n := (⊤ : ℕ∞)) x.2 v.2
  obtain ⟨Y', hY'⟩ := ContMDiffSection.exists_eq_at (I := J) (F := F)
    (V := (TangentSpace J : N → Type _)) (n := (⊤ : ℕ∞)) x.2 w.2
  obtain ⟨Z', hZ'⟩ := ContMDiffSection.exists_eq_at (I := J) (F := F)
    (V := (TangentSpace J : N → Type _)) (n := (⊤ : ℕ∞)) x.2 z.2
  have hv : productVectorField X X' x = v := Prod.ext hX hX'
  have hw : productVectorField Y Y' x = w := Prod.ext hY hY'
  have hz : productVectorField Z Z' x = z := Prod.ext hZ hZ'
  have hp := riemannOp_apply_smooth (LeviCivita (g.prod h))
    (x := x) (productVectorField X X').contMDiff
    (productVectorField Y Y').contMDiff (productVectorField Z Z').contMDiff
  rw [hv, hw, hz, riemannSec_product] at hp
  have hg := riemannOp_apply_smooth (LeviCivita g) (x := x.1)
    X.contMDiff Y.contMDiff Z.contMDiff
  have hh := riemannOp_apply_smooth (LeviCivita h) (x := x.2)
    X'.contMDiff Y'.contMDiff Z'.contMDiff
  rw [hX, hY, hZ] at hg
  rw [hX', hY', hZ'] at hh
  exact hp.trans (congrArg₂ Prod.mk hg.symm hh.symm)

theorem ricciTensor_productMetric
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (x : M × N) (v w : TangentSpace (I.prod J) x) :
    ricciTensor (g.prod h) x v w =
      ricciTensor g x.1 v.1 w.1 + ricciTensor h x.2 v.2 w.2 := by
  have he : (ricciEndo (g.prod h) x v w : (E × F) →ₗ[ℝ] (E × F)) =
      LinearMap.prodMap (ricciEndo g x.1 v.1 w.1) (ricciEndo h x.2 v.2 w.2) := by
    apply LinearMap.ext
    intro u
    exact riemannOp_productMetric g h x u v w
  have ht := congrArg (LinearMap.trace ℝ (E × F)) he
  exact ht.trans (LinearMap.trace_prodMap' (ricciEndo g x.1 v.1 w.1)
    (ricciEndo h x.2 v.2 w.2))

set_option backward.isDefEq.respectTransparency false in
theorem metricRm04At_productMetric_apply
    [I.Boundaryless] [J.Boundaryless]
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
  have hv₁ : (fun k => (v k).1) =
      vec4 (I := I) (x := x.1) (v 0).1 (v 1).1 (v 2).1 (v 3).1 := by
    ext k
    fin_cases k <;> rfl
  have hv₂ : (fun k => (v k).2) =
      vec4 (I := J) (x := x.2) (v 0).2 (v 1).2 (v 2).2 (v 3).2 := by
    ext k
    fin_cases k <;> rfl
  rw [hv₁, hv₂, hv]
  change metricRm04StandardAt (g.prod h) x (v 0) (v 1) (v 2) (v 3) =
    metricRm04StandardAt g x.1 (v 0).1 (v 1).1 (v 2).1 (v 3).1 +
      metricRm04StandardAt h x.2 (v 0).2 (v 1).2 (v 2).2 (v 3).2
  rw [rm04_eq_inner_riem, rm04_eq_inner_riem, rm04_eq_inner_riem,
    riemannOp_productMetric, SmoothRiemannianMetric.prod_inner]

set_option backward.isDefEq.respectTransparency false in
theorem normSq0S_metricRm04At_productMetric_of_eq_zero
    [I.Boundaryless] [J.Boundaryless]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (x : M × N) (hflat : metricRm04At h x.2 = 0) :
    normSq0S (g.prod h) x 4 (metricRm04At (g.prod h) x) =
      normSq0S g x.1 4 (metricRm04At g x.1) := by
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
  have hb : ∀ i j, (g.prod h).inner x (b i) (b j) =
      if i = j then (1 : ℝ) else 0 := by
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
  have hflat_eval (v : Fin 4 → TangentSpace J x.2) : metricRm04At h x.2 v = 0 := by
    rw [hflat]
    rfl
  rw [normSq0S_identity_eq_sum_sq (g.prod h) x 4 b
      (metricInverseInBasis_identity_of_orthonormal (g.prod h) b hb),
    normSq0S_identity_eq_sum_sq g x.1 4 b₁
      (metricInverseInBasis_identity_of_orthonormal g b₁ hb₁)]
  simp only [component0S_apply, metricRm04At_productMetric_apply, hflat_eval, add_zero]
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

theorem normSq0S_metricRm04At_productReal
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M × ℝ) :
    normSq0S (g.prod (euclideanMetric (E := ℝ))) x 4
        (metricRm04At (g.prod (euclideanMetric (E := ℝ))) x) =
      normSq0S g x.1 4 (metricRm04At g x.1) := by
  exact normSq0S_metricRm04At_productMetric_of_eq_zero g
    (euclideanMetric (E := ℝ)) x
    (metricRm04At_eq_zero_of_finrank_le_one (euclideanMetric (E := ℝ)) (by simp) x.2)

theorem riemannOp_productReal_vertical_eq_zero
    (g : SmoothRiemannianMetric I M) (x : M × ℝ)
    (u v : TangentSpace (I.prod 𝓘(ℝ, ℝ)) x) (r : ℝ) :
    riemannOp (LeviCivita (g.prod (euclideanMetric (E := ℝ)))) x u v (0, r) = 0 := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hprod := riemannOp_productMetric g (euclideanMetric (E := ℝ)) x u v
    (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) x from (0, r))
  apply hprod.trans
  apply Prod.ext
  · exact (riemannOp (LeviCivita g) x.1 u.1 v.1).map_zero
  · exact riemannOp_eq_zero_of_finrank_le_one _
      (by simp : Module.finrank ℝ ℝ ≤ 1) _ _ _ _

theorem productReal_vertical_mem_curvatureOperatorImageAnnihilatorAt
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M × ℝ) (r : ℝ) :
    (0, r) ∈ curvatureOperatorImageAnnihilatorAt
      (g.prod (euclideanMetric (E := ℝ))) x
      ⟨metricRm04At (g.prod (euclideanMetric (E := ℝ))) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (g.prod (euclideanMetric (E := ℝ))) x⟩ := by
  apply (mem_curvatureOperatorImageAnnihilatorAt_iff_tensor04StandardAt_eq_zero _ _ _ _).mpr
  intro a b w
  change metricRm04StandardAt (g.prod (euclideanMetric (E := ℝ))) x a b (0, r) w = 0
  have hinner := DifferentialGeometry.rm04_eq_inner_riem
    (g.prod (euclideanMetric (E := ℝ))) x a b
      (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) x from (0, r)) w
  rw [riemannOp_productReal_vertical_eq_zero] at hinner
  simpa only [map_zero] using hinner

theorem ricciTensor_productReal_vertical_eq_zero
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M × ℝ) (r : ℝ)
    (w : TangentSpace (I.prod 𝓘(ℝ, ℝ)) x) :
    ricciTensor (g.prod (euclideanMetric (E := ℝ))) x (0, r) w = 0 := by
  exact ricciTensor_eq_zero_of_mem_curvatureOperatorImageAnnihilatorAt _ _
    (productReal_vertical_mem_curvatureOperatorImageAnnihilatorAt g x r) w

set_option backward.isDefEq.respectTransparency false in
theorem metricScalarAt_productMetric
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (x : M × N) :
    metricScalarAt (g.prod h) x = metricScalarAt g x.1 + metricScalarAt h x.2 := by
  have hsharp :
      (ricciSharp (g.prod h) x).toLinearMap =
        LinearMap.prodMap (ricciSharp g x.1).toLinearMap (ricciSharp h x.2).toLinearMap := by
    apply LinearMap.ext
    intro v
    apply SmoothRiemannianMetric.eq_of_inner_eq (I := I.prod J) (g.prod h)
    intro w
    change (g.prod h).inner x (ricciSharp (g.prod h) x v) w =
      (g.prod h).inner x (ricciSharp g x.1 v.1, ricciSharp h x.2 v.2) w
    rw [inner_ricciSharp, ricciTensor_productMetric,
      ← inner_ricciSharp, ← inner_ricciSharp]
    exact (SmoothRiemannianMetric.prod_inner g h x
      (ricciSharp g x.1 v.1, ricciSharp h x.2 v.2) w).symm
  rw [metricScalar_eq_trace_ricciSharp, metricScalar_eq_trace_ricciSharp,
    metricScalar_eq_trace_ricciSharp, hsharp]
  change LinearMap.trace ℝ (E × F)
      (LinearMap.prodMap (ricciSharp g x.1).toLinearMap (ricciSharp h x.2).toLinearMap) =
    LinearMap.trace ℝ E (ricciSharp g x.1).toLinearMap +
      LinearMap.trace ℝ F (ricciSharp h x.2).toLinearMap
  exact LinearMap.trace_prodMap' _ _

theorem metricRicciAt_productMetric_apply [I.Boundaryless] [J.Boundaryless]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (x : M × N) (v : Fin 2 → TangentSpace (I.prod J) x) :
    metricRicciAt (g.prod h) x v =
      metricRicciAt g x.1 (fun k => (v k).1) + metricRicciAt h x.2 (fun k => (v k).2) := by
  have hv : v = (vec2 (I := I.prod J) (x := x) (v 0) (v 1) :
      Fin 2 → TangentSpace (I.prod J) x) := by
    funext i
    fin_cases i <;> rfl
  have hv₁ : (fun k => (v k).1) = vec2 (I := I) (x := x.1) (v 0).1 (v 1).1 := by
    funext i
    fin_cases i <;> rfl
  have hv₂ : (fun k => (v k).2) = vec2 (I := J) (x := x.2) (v 0).2 (v 1).2 := by
    funext i
    fin_cases i <;> rfl
  conv_lhs => rw [hv]
  rw [hv₁, hv₂,
    DifferentialGeometry.metricRicciAt_apply_eq_ricciTensor (g := g.prod h) x (v 0) (v 1),
    DifferentialGeometry.metricRicciAt_apply_eq_ricciTensor (g := g) x.1 (v 0).1 (v 1).1,
    DifferentialGeometry.metricRicciAt_apply_eq_ricciTensor (g := h) x.2 (v 0).2 (v 1).2,
    ricciTensor_productMetric]

end DifferentialGeometry.Geometry.Curvature
