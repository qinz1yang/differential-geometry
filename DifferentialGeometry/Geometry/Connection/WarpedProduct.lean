import DifferentialGeometry.Geometry.Metric.WarpedProduct
import DifferentialGeometry.Geometry.Connection.Product
import DifferentialGeometry.Geometry.Connection.ChartBridge.Scalar.Gradient

set_option autoImplicit false
noncomputable section
open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.VectorField DifferentialGeometry.Geometry.Operator

namespace DifferentialGeometry.Geometry.Connection

variable {E H M F K N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace K] {J : ModelWithCorners ℝ F K}
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M]
    [FiniteDimensional ℝ F] [IsManifold J ∞ N] [T2Space N] in
private theorem warped_scalar_deriv
    {a f : M → ℝ} {b : N → ℝ} (p : M × N)
    (ha : MDifferentiableAt I 𝓘(ℝ) a p.1)
    (hf : MDifferentiableAt I 𝓘(ℝ) f p.1)
    (hb : MDifferentiableAt J 𝓘(ℝ) b p.2)
    (v : TangentSpace (I.prod J) p) :
    mvfderiv (I.prod J) (fun z : M × N => a z.1 + f z.1 ^ 2 * b z.2) p v =
      mvfderiv I a p.1 v.1 + f p.1 ^ 2 * mvfderiv J b p.2 v.2 +
        2 * f p.1 * mvfderiv I f p.1 v.1 * b p.2 := by
  have hA := ha.comp p (mdifferentiableAt_fst (I := I) (I' := J))
  have hF := hf.comp p (mdifferentiableAt_fst (I := I) (I' := J))
  have hB := hb.comp p (mdifferentiableAt_snd (I := I) (I' := J))
  have hda := mvfderiv_comp p ha (mdifferentiableAt_fst (I := I) (I' := J))
  have hdf := mvfderiv_comp p hf (mdifferentiableAt_fst (I := I) (I' := J))
  have hdb := mvfderiv_comp p hb (mdifferentiableAt_snd (I := I) (I' := J))
  rw [mfderiv_fst] at hda hdf
  rw [mfderiv_snd] at hdb
  simp only [pow_two]
  erw [mvfderiv_add hA ((hF.mul hF).mul hB),
    _root_.mvfderiv_fun_mul (hF.mul hF) hB, _root_.mvfderiv_fun_mul hF hF,
    hda, hdf, hdb]
  change mvfderiv I a p.1 v.1 +
    ((f p.1 * f p.1) * mvfderiv J b p.2 v.2 +
    b p.2 * (f p.1 * mvfderiv I f p.1 v.1 + f p.1 * mvfderiv I f p.1 v.1)) = _
  ring

private theorem koszulScalar_warpedProduct
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hpos : ∀ x, 0 < f x)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (U V W : Cₛ^∞⟮J; F, (TangentSpace J : N → Type _)⟯) (p : M × N) :
    koszulScalar (g.warpedProduct h f hf hpos) (productVectorField X U)
        (productVectorField Y V) (productVectorField Z W) p =
      koszulScalar g X Y Z p.1 + f p.1 ^ 2 * koszulScalar h U V W p.2 +
        2 * f p.1 * (mvfderiv I f p.1 (X p.1) * h.inner p.2 (V p.2) (W p.2) +
          mvfderiv I f p.1 (Y p.1) * h.inner p.2 (W p.2) (U p.2) -
          mvfderiv I f p.1 (Z p.1) * h.inner p.2 (U p.2) (V p.2)) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : CompleteSpace F := FiniteDimensional.complete ℝ F
  have hm (A B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :=
    (contMDiff_metric_inner g A B).mdifferentiable (by simp) p.1
  have hn (A B : Cₛ^∞⟮J; F, (TangentSpace J : N → Type _)⟯) :=
    (contMDiff_metric_inner h A B).mdifferentiable (by simp) p.2
  simp only [koszulScalar, directionalDerivAlong]
  simp only [SmoothRiemannianMetric.warpedProduct_inner]
  simp only [mlieBracket_productVectorField, productVectorField_apply]
  linear_combination (norm := ring!)
    warped_scalar_deriv p (hm Y Z) (hf.mdifferentiable (by simp) p.1) (hn V W)
      (X p.1, U p.2) +
    warped_scalar_deriv p (hm Z X) (hf.mdifferentiable (by simp) p.1) (hn W U)
      (Y p.1, V p.2) -
    warped_scalar_deriv p (hm X Y) (hf.mdifferentiable (by simp) p.1) (hn U V)
      (Z p.1, W p.2)

theorem leviCivita_warpedProduct_productVectorField
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hpos : ∀ x, 0 < f x)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (V : Cₛ^∞⟮J; F, (TangentSpace J : N → Type _)⟯)
    (p : M × N) (v : TangentSpace (I.prod J) p) :
    (LeviCivita (g.warpedProduct h f hf hpos)) (productVectorField Y V) p v =
      ((LeviCivita g) Y p.1 v.1 -
          (f p.1 * h.inner p.2 v.2 (V p.2)) • gradFun g f p.1,
        @HAdd.hAdd F F F _
          (@HAdd.hAdd F F F _ ((LeviCivita h) V p.2 v.2)
            ((mvfderiv I f p.1 v.1 / f p.1) • V p.2))
          ((mvfderiv I f p.1 (Y p.1) / f p.1) • v.2)) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : CompleteSpace F := FiniteDimensional.complete ℝ F
  let G := g.warpedProduct h f hf hpos
  apply DifferentialGeometry.Geometry.Connection.SmoothRiemannianMetric.eq_of_inner_eq G
  intro w
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) p.1 v.1
  obtain ⟨U, hU⟩ := ContMDiffSection.exists_eq_at (I := J) (F := F)
    (V := (TangentSpace J : N → Type _)) (n := (⊤ : ℕ∞)) p.2 v.2
  obtain ⟨Z, hZ⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) p.1 w.1
  obtain ⟨W, hW⟩ := ContMDiffSection.exists_eq_at (I := J) (F := F)
    (V := (TangentSpace J : N → Type _)) (n := (⊤ : ℕ∞)) p.2 w.2
  have hv : productVectorField X U p = v := Prod.ext hX hU
  have hw : productVectorField Z W p = w := Prod.ext hZ hW
  have hk := leviCivitaConnectionOfMetric_inner_eq_koszulScalar G
    (productVectorField X U) (productVectorField Y V) (productVectorField Z W) p
    (productVectorField X U).mdifferentiableAt
    (productVectorField Y V).mdifferentiableAt
    (productVectorField Z W).mdifferentiableAt
  rw [hv, hw] at hk
  change G.inner p ((LeviCivita G) (productVectorField Y V) p v) w = _ at hk
  rw [hk]
  change (1 / 2 : ℝ) * koszulScalar (g.warpedProduct h f hf hpos) _ _ _ p = _
  rw [koszulScalar_warpedProduct]
  have hb := leviCivitaConnectionOfMetric_inner_eq_koszulScalar g X Y Z p.1
    X.mdifferentiableAt Y.mdifferentiableAt Z.mdifferentiableAt
  have ht := leviCivitaConnectionOfMetric_inner_eq_koszulScalar h U V W p.2
    U.mdifferentiableAt V.mdifferentiableAt W.mdifferentiableAt
  rw [hX, hZ] at hb
  rw [hU, hW] at ht
  change g.inner p.1 ((LeviCivita g) Y p.1 v.1) w.1 = _ at hb
  change h.inner p.2 ((LeviCivita h) V p.2 v.2) w.2 = _ at ht
  erw [hX, hZ, hU, hW, show G = g.warpedProduct h f hf hpos from rfl,
    SmoothRiemannianMetric.warpedProduct_inner]
  have hgExpand (a b z : TangentSpace I p.1) (c : ℝ) :
      g.inner p.1 (a - c • b) z = g.inner p.1 a z - c * g.inner p.1 b z := by
    simp only [map_sub, sub_apply, map_smul, smul_apply, smul_eq_mul]
  have hhExpand (a b c z : TangentSpace J p.2) (s t : ℝ) :
      h.inner p.2 (a + s • b + t • c) z =
        h.inner p.2 a z + s * h.inner p.2 b z + t * h.inner p.2 c z := by
    simp only [map_add, add_apply, map_smul, smul_apply, smul_eq_mul]
  erw [hgExpand, hhExpand, gradFun_metricDual_mvfderiv, hb, ht,
    h.symm p.2 w.2 v.2]
  field_simp [ne_of_gt (hpos p.1)]
  ring

theorem leviCivita_warpedProduct_horizontal_vertical (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hpos : ∀ x, 0 < f x)
    (V : Cₛ^∞⟮J; F, (TangentSpace J : N → Type _)⟯)
    (p : M × N) (v : TangentSpace I p.1) :
    (LeviCivita (g.warpedProduct h f hf hpos)) (productVectorField 0 V) p (v, 0) =
      (0, (mvfderiv I f p.1 v / f p.1) • V p.2) := by
  erw [leviCivita_warpedProduct_productVectorField]
  have hm : h.inner p.2 (0 : TangentSpace J p.2) (V p.2) = 0 := by
    rw [map_zero]
    rfl
  erw [hm, map_zero ((LeviCivita h) V p.2)]
  simp only [ContMDiffSection.coe_zero, CovariantDerivative.zero, Pi.zero_apply, zero_apply,
    mul_zero, gradFun_def, zero_smul, sub_self, map_zero, zero_div, smul_zero, add_zero]
  erw [zero_add]
  rfl

theorem leviCivita_warpedProduct_vertical_vertical (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hpos : ∀ x, 0 < f x)
    (V : Cₛ^∞⟮J; F, (TangentSpace J : N → Type _)⟯)
    (p : M × N) (v : TangentSpace J p.2) :
    (LeviCivita (g.warpedProduct h f hf hpos)) (productVectorField 0 V) p (0, v) =
      (-(f p.1 * h.inner p.2 v (V p.2)) • gradFun g f p.1,
        (LeviCivita h) V p.2 v) := by
  erw [leviCivita_warpedProduct_productVectorField]
  have hd : mvfderiv I f p.1 (0 : TangentSpace I p.1) = 0 := map_zero _
  have hz : (LeviCivita g) (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
      p.1 (0 : TangentSpace I p.1) = 0 := map_zero _
  erw [hd, hz]
  simp only [gradFun_def, zero_sub, zero_div, zero_smul, neg_smul]
  erw [add_zero, zero_smul, add_zero]
  rfl

end DifferentialGeometry.Geometry.Connection
