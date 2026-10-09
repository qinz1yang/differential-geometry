import DifferentialGeometry.Geometry.Metric.WarpedProduct
import DifferentialGeometry.Geometry.Metric.Euclidean
import DifferentialGeometry.Geometry.Connection.Product
import DifferentialGeometry.Geometry.Curvature.Coordinates.RiemannTensorBridge
import DifferentialGeometry.Geometry.Connection.ChartBridge.Scalar.Hessian
import DifferentialGeometry.Bundle.PartialMfderiv.Basic

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.VectorField

namespace DifferentialGeometry.Geometry.Curvature

private def realConst (c : ℝ) :
    Cₛ^∞⟮𝓘(ℝ, ℝ); ℝ, (TangentSpace 𝓘(ℝ, ℝ) : ℝ → Type _)⟯ where
  toFun _ := c
  contMDiff_toFun := by
    apply (contMDiff_vectorSpace_iff_contDiff (𝕜 := ℝ)).mpr
    exact contDiff_const

private theorem mlieBracket_realConst (a b x : ℝ) :
    _root_.VectorField.mlieBracket 𝓘(ℝ, ℝ) (realConst a) (realConst b) x = 0 := by
  rw [← _root_.VectorField.mlieBracketWithin_univ,
    _root_.VectorField.mlieBracketWithin_eq_lieBracketWithin]
  change (fderivWithin ℝ (fun _ : ℝ => b) univ x) a -
    (fderivWithin ℝ (fun _ : ℝ => a) univ x) b = 0
  simp

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private def realProductField (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (b : ℝ) :=
  productVectorField Y (realConst b)

omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem realProductField_apply (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (b : ℝ) (p : M × ℝ) : realProductField Y b p = (Y p.1, b) := rfl

set_option backward.isDefEq.respectTransparency false in
private theorem mlieBracket_realProductField
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (a b : ℝ) (p : M × ℝ) :
    _root_.VectorField.mlieBracket (I.prod 𝓘(ℝ, ℝ))
        (realProductField X a) (realProductField Y b) p =
      (_root_.VectorField.mlieBracket I X Y p.1, 0) := by
  rw [realProductField, realProductField, mlieBracket_productVectorField,
    mlieBracket_realConst]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] in
private theorem mvfderiv_fst_apply {f : M → ℝ} (p : M × ℝ)
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f p.1)
    (v : TangentSpace (I.prod 𝓘(ℝ, ℝ)) p) :
    mvfderiv (I.prod 𝓘(ℝ, ℝ)) (fun z : M × ℝ => f z.1) p v =
      mvfderiv I f p.1 v.1 := by
  have h := mvfderiv_comp p hf
    (mdifferentiableAt_fst (I := I) (I' := 𝓘(ℝ, ℝ)))
  rw [mfderiv_fst] at h
  exact congrArg (fun L => L v) h

set_option backward.isDefEq.respectTransparency false in
private theorem warped_real_inner
    (g : SmoothRiemannianMetric I M) (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hpos : ∀ x, 0 < f x)
    (p : M × ℝ) (v w : TangentSpace (I.prod 𝓘(ℝ, ℝ)) p) :
    (g.warpedProduct (euclideanMetric (E := ℝ)) f hf hpos).inner p v w =
      g.inner p.1 v.1 w.1 + f p.1 ^ 2 * (w.2 * v.2) := by
  rw [SmoothRiemannianMetric.warpedProduct_inner]
  rfl

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] in
private theorem mvfderiv_sq_mul_mul
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (b c : ℝ) (x : M) (v : TangentSpace I x) :
    mvfderiv I (fun y => f y ^ 2 * b * c) x v =
      2 * f x * mvfderiv I f x v * b * c := by
  have hd : HasDerivAt (fun t : ℝ => t ^ 2 * b * c) (2 * f x * b * c) (f x) := by
    simpa using (((hasDerivAt_id (f x)).pow 2).mul_const b).mul_const c
  have hc := mvfderiv_comp x hd.differentiableAt.mdifferentiableAt
    (hf.mdifferentiable (by simp) x)
  have hD : mvfderiv 𝓘(ℝ, ℝ) (fun t : ℝ => t ^ 2 * b * c) (f x) =
      (1 : ℝ →L[ℝ] ℝ).smulRight (2 * f x * b * c) := by
    change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) _ _ = _
    rw [mfderiv_eq_fderiv]
    exact hd.hasFDerivAt.fderiv
  rw [hD] at hc
  have he := congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L v) hc
  change mvfderiv I (fun y => f y ^ 2 * b * c) x v =
    mvfderiv I f x v * (2 * f x * b * c) at he
  exact he.trans (by ring)

set_option backward.isDefEq.respectTransparency false in
private theorem warped_inner_deriv
    (g : SmoothRiemannianMetric I M) (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hpos : ∀ x, 0 < f x)
    (Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (b c : ℝ) (p : M × ℝ)
    (v : TangentSpace (I.prod 𝓘(ℝ, ℝ)) p) :
    mvfderiv (I.prod 𝓘(ℝ, ℝ))
        (fun z => (g.warpedProduct (euclideanMetric (E := ℝ)) f hf hpos).inner z
          (realProductField Y b z) (realProductField Z c z)) p v =
      mvfderiv I (fun x => g.inner x (Y x) (Z x)) p.1 v.1 +
        2 * f p.1 * mvfderiv I f p.1 v.1 * b * c := by
  have heq : (fun z => (g.warpedProduct (euclideanMetric (E := ℝ)) f hf hpos).inner z
      (realProductField Y b z) (realProductField Z c z)) =
      (fun z : M × ℝ => g.inner z.1 (Y z.1) (Z z.1) + f z.1 ^ 2 * b * c) := by
    funext z
    rw [realProductField_apply, realProductField_apply,
      warped_real_inner]
    ring
  rw [heq]
  have hg : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun x => g.inner x (Y x) (Z x)) p.1 :=
    (contMDiff_metric_inner g Y Z).mdifferentiable (by simp) p.1
  have hfc : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun x => f x ^ 2 * b * c) p.1 :=
    (((hf.pow 2).mul contMDiff_const).mul contMDiff_const).mdifferentiable (by simp) p.1
  have hfirst := mvfderiv_fst_apply p (hg.add hfc) v
  change mvfderiv (I.prod 𝓘(ℝ, ℝ))
      (fun z : M × ℝ => g.inner z.1 (Y z.1) (Z z.1) + f z.1 ^ 2 * b * c) p v =
    mvfderiv I (fun x => g.inner x (Y x) (Z x) + f x ^ 2 * b * c) p.1 v.1 at hfirst
  rw [hfirst]
  have hadd := congrArg (fun L : TangentSpace I p.1 →L[ℝ] ℝ => L v.1)
    (mvfderiv_add hg hfc)
  change mvfderiv I (fun x => g.inner x (Y x) (Z x) + f x ^ 2 * b * c) p.1 v.1 =
    mvfderiv I (fun x => g.inner x (Y x) (Z x)) p.1 v.1 +
      mvfderiv I (fun x => f x ^ 2 * b * c) p.1 v.1 at hadd
  rw [hadd]
  exact congrArg (fun q : ℝ =>
    mvfderiv I (fun x => g.inner x (Y x) (Z x)) p.1 v.1 + q)
    (mvfderiv_sq_mul_mul f hf b c p.1 v.1)

set_option backward.isDefEq.respectTransparency false in
private theorem koszulScalar_warped_real
    (g : SmoothRiemannianMetric I M) (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hpos : ∀ x, 0 < f x)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (a b c : ℝ) (p : M × ℝ) :
    koszulScalar (g.warpedProduct (euclideanMetric (E := ℝ)) f hf hpos)
        (realProductField X a) (realProductField Y b) (realProductField Z c) p =
      koszulScalar g X Y Z p.1 +
        2 * f p.1 * (mvfderiv I f p.1 (X p.1) * b * c +
          mvfderiv I f p.1 (Y p.1) * a * c - mvfderiv I f p.1 (Z p.1) * a * b) := by
  simp only [koszulScalar, directionalDerivAlong]
  rw [warped_inner_deriv, warped_inner_deriv, warped_inner_deriv]
  simp only [mlieBracket_realProductField, realProductField_apply,
    warped_real_inner, mul_zero, zero_mul, add_zero]
  ring

set_option backward.isDefEq.respectTransparency false in
private theorem leviCivita_warped_real_productField
    (g : SmoothRiemannianMetric I M) (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hpos : ∀ x, 0 < f x)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (b : ℝ)
    (p : M × ℝ) (v : TangentSpace (I.prod 𝓘(ℝ, ℝ)) p) :
    (LeviCivita (g.warpedProduct (euclideanMetric (E := ℝ)) f hf hpos))
        (realProductField Y b) p v =
      ((LeviCivita g) Y p.1 v.1 - (f p.1 * v.2 * b) • gradFun g f p.1,
        (b * mvfderiv I f p.1 v.1 + v.2 * mvfderiv I f p.1 (Y p.1)) / f p.1) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let G := g.warpedProduct (euclideanMetric (E := ℝ)) f hf hpos
  apply DifferentialGeometry.Geometry.Connection.SmoothRiemannianMetric.eq_of_inner_eq G
  intro w
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) p.1 v.1
  obtain ⟨Z, hZ⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) p.1 w.1
  have hv : realProductField X v.2 p = v := Prod.ext hX rfl
  have hw : realProductField Z w.2 p = w := Prod.ext hZ rfl
  have hk := leviCivitaConnectionOfMetric_inner_eq_koszulScalar G
    (realProductField X v.2) (realProductField Y b) (realProductField Z w.2) p
    (realProductField X v.2).mdifferentiableAt
    (realProductField Y b).mdifferentiableAt
    (realProductField Z w.2).mdifferentiableAt
  rw [hv, hw] at hk
  change G.inner p ((LeviCivita G) (realProductField Y b) p v) w = _ at hk
  rw [hk]
  change (1 / 2 : ℝ) * koszulScalar
    (g.warpedProduct (euclideanMetric (E := ℝ)) f hf hpos) _ _ _ p = _
  rw [koszulScalar_warped_real]
  have hbase := leviCivitaConnectionOfMetric_inner_eq_koszulScalar g X Y Z p.1
    X.mdifferentiableAt Y.mdifferentiableAt Z.mdifferentiableAt
  rw [hX, hZ] at hbase
  change g.inner p.1 ((LeviCivita g) Y p.1 v.1) w.1 = _ at hbase
  rw [hX, hZ, show G = g.warpedProduct (euclideanMetric (E := ℝ)) f hf hpos from rfl,
    warped_real_inner]
  simp only [map_sub, sub_apply,
    map_smul, smul_apply, smul_eq_mul, gradFun_metricDual_mvfderiv]
  rw [hbase]
  field_simp [ne_of_gt (hpos p.1)]
  ring

set_option backward.isDefEq.respectTransparency false in
private theorem riemannSec_warped_real_vertical [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hpos : ∀ x, 0 < f x)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (p : M × ℝ) :
    riemannSec (LeviCivita (g.warpedProduct (euclideanMetric (E := ℝ)) f hf hpos))
        (realProductField Y 0) (realProductField 0 1) (realProductField 0 1) p =
      (-(f p.1) • (LeviCivita g) (gradFun g f) p.1 (Y p.1), 0) := by
  let C := LeviCivita (g.warpedProduct (euclideanMetric (E := ℝ)) f hf hpos)
  let U := realProductField (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) 1
  let X := realProductField Y 0
  let V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨gradFun g f, gradFun_contMDiff_total g hf⟩
  let W := realProductField V 0
  let a : M × ℝ → ℝ := fun z => -f z.1
  let q : M × ℝ → ℝ := fun z => mvfderiv I f z.1 (Y z.1) / f z.1
  have ha : MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) a p :=
    (hf.neg.comp contMDiff_fst).mdifferentiable (by simp) p
  have hdfY : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => mvfderiv I f x (Y x)) := by
    apply (contMDiff_metric_inner g V Y).congr
    intro x
    exact (gradFun_metricDual_mvfderiv g f x (Y x)).symm
  have hqbase : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => mvfderiv I f x (Y x) / f x) := by
    exact hdfY.div₀ hf (fun x => ne_of_gt (hpos x))
  have hq : MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) q p :=
    (hqbase.comp contMDiff_fst).mdifferentiable (by simp) p
  have hUU : covApply C U U = a • (fun z => W z) := by
    funext z
    change C U z (0, 1) = _
    rw [show C = LeviCivita (g.warpedProduct (euclideanMetric (E := ℝ)) f hf hpos) from rfl,
      leviCivita_warped_real_productField]
    simp [a, W, V, realProductField_apply, (LeviCivita g).zero]
  have hXU : covApply C X U = q • (fun z => U z) := by
    funext z
    change C U z (Y z.1, 0) = _
    rw [show C = LeviCivita (g.warpedProduct (euclideanMetric (E := ℝ)) f hf hpos) from rfl,
      leviCivita_warped_real_productField]
    simp [U, q, realProductField_apply, (LeviCivita g).zero]
  have hbracket : _root_.VectorField.mlieBracket (I.prod 𝓘(ℝ, ℝ)) X U p = 0 := by
    rw [show X = realProductField Y 0 from rfl,
      show U = realProductField (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) 1 from rfl,
      mlieBracket_realProductField]
    change (_root_.VectorField.mlieBracket I Y 0 p.1, (0 : ℝ)) = 0
    rw [_root_.VectorField.mlieBracket_zero_right]
    rfl
  have hda : mvfderiv (I.prod 𝓘(ℝ, ℝ)) a p (X p) =
      -mvfderiv I f p.1 (Y p.1) := by
    rw [show a = fun z : M × ℝ => -f z.1 from rfl,
      mvfderiv_fst_apply p (hf.neg.mdifferentiable (by simp) p.1)]
    change mvfderiv I (-f) p.1 (Y p.1) = _
    rw [mvfderiv_neg, neg_apply]
  have hdq : mvfderiv (I.prod 𝓘(ℝ, ℝ)) q p (U p) = 0 := by
    rw [show q = fun z : M × ℝ => mvfderiv I f z.1 (Y z.1) / f z.1 from rfl,
      mvfderiv_fst_apply p (hqbase.mdifferentiable (by simp) p.1)]
    exact map_zero _
  change riemannSec C X U U p = _
  rw [riemannSec_def, hUU, hXU, hbracket, map_zero, sub_zero]
  rw [C.isCovariantDerivativeOnUniv.leibniz W.mdifferentiableAt ha,
    C.isCovariantDerivativeOnUniv.leibniz U.mdifferentiableAt hq]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    hda, hdq, zero_smul, add_zero]
  have hWX : C W p (X p) = ((LeviCivita g) V p.1 (Y p.1), 0) := by
    change (LeviCivita (g.warpedProduct (euclideanMetric (E := ℝ)) f hf hpos))
      (realProductField V 0) p (Y p.1, 0) = _
    rw [leviCivita_warped_real_productField]
    simp
  have hUUp : C U p (U p) = (-(f p.1) • V p.1, 0) := by
    have h := congrFun hUU p
    change C U p (U p) = (-f p.1) • (V p.1, (0 : ℝ)) at h
    exact h.trans (Prod.ext rfl (smul_zero _))
  rw [hWX, hUUp]
  change a p • ((LeviCivita g) V p.1 (Y p.1), 0) +
      (-mvfderiv I f p.1 (Y p.1)) • (V p.1, 0) -
      q p • (-(f p.1) • V p.1, 0) = _
  have hcancel : q p * (-f p.1) = -mvfderiv I f p.1 (Y p.1) := by
    dsimp [q]
    field_simp [ne_of_gt (hpos p.1)]
  apply Prod.ext
  · change (-f p.1) • ((LeviCivita g) V p.1 (Y p.1)) +
      (-mvfderiv I f p.1 (Y p.1)) • V p.1 -
      q p • (-(f p.1) • V p.1) = _
    rw [smul_smul, hcancel, add_sub_cancel_right]
    rfl
  · change a p * 0 + _ * 0 - q p * 0 = 0
    ring

set_option backward.isDefEq.respectTransparency false in
theorem metricRm04StandardAt_warpedProduct_real_mixed [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hpos : ∀ x, 0 < f x)
    (x : M) (r : ℝ) (u : TangentSpace I x) :
    metricRm04StandardAt (g.warpedProduct (euclideanMetric (E := ℝ)) f hf hpos)
      (x, r) (u, 0) (0, 1) (0, 1) (u, 0) = -f x * hessFun g f x u u := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x u
  let U := realProductField (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) 1
  let X := realProductField Y 0
  have hR := riemannOp_apply_smooth
    (LeviCivita (g.warpedProduct (euclideanMetric (E := ℝ)) f hf hpos))
    X.contMDiff U.contMDiff U.contMDiff (x := (x, r))
  rw [riemannSec_warped_real_vertical] at hR
  rw [rm04_eq_inner_riem]
  have hX : X (x, r) = (u, 0) := Prod.ext hY rfl
  have hU : U (x, r) = (0, 1) := rfl
  rw [hX, hU, hY] at hR
  rw [hR, warped_real_inner]
  simp only [map_smul, smul_eq_mul,
    mul_zero, add_zero]
  rw [g.symm x u, ← hessFun_eq_cov_grad g hf x u u]

end DifferentialGeometry.Geometry.Curvature
