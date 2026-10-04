import DifferentialGeometry.Geometry.Connection.WarpedProduct
import DifferentialGeometry.Geometry.Curvature.Metric.Defs
import DifferentialGeometry.Geometry.Operator.WithBoundary.GradientGlobalSection
import DifferentialGeometry.Geometry.Curvature.Riemann.Basic.Sections
import DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.CovariantDerivative

set_option autoImplicit false
noncomputable section
open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.VectorField DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Connection

namespace DifferentialGeometry.Geometry.Curvature

variable {E H M F K N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace K] {J : ModelWithCorners ℝ F K}
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N]

private theorem horizontal_horizontal
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hpos : ∀ x, 0 < f x)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (p : M × N) (v : TangentSpace I p.1) :
    (LeviCivita (g.warpedProduct h f hf hpos)) (productVectorField Y 0) p (v, 0) =
      ((LeviCivita g) Y p.1 v, 0) := by
  erw [leviCivita_warpedProduct_productVectorField]
  have hm : h.inner p.2 (0 : TangentSpace J p.2) 0 = 0 := by
    rw [map_zero]
  have hz : (LeviCivita h) (0 : Cₛ^∞⟮J; F, (TangentSpace J : N → Type _)⟯)
      p.2 (0 : TangentSpace J p.2) = 0 := map_zero _
  erw [hm, hz]
  simp only [mul_zero, zero_smul, sub_zero, ContMDiffSection.coe_zero, Pi.zero_apply]
  erw [smul_zero, smul_zero, zero_add, zero_add]

end DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.Geometry.Curvature

variable {E H M F K N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace K] {J : ModelWithCorners ℝ F K}
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M]
    [FiniteDimensional ℝ F] [IsManifold J ∞ N] [T2Space N] in
private theorem derivative_fst {f : M → ℝ} (p : M × N)
    (hf : MDifferentiableAt I 𝓘(ℝ) f p.1)
    (v : TangentSpace (I.prod J) p) :
    mvfderiv (I.prod J) (fun z : M × N => f z.1) p v =
      mvfderiv I f p.1 v.1 := by
  have hc := mvfderiv_comp p hf (mdifferentiableAt_fst (I := I) (I' := J))
  rw [mfderiv_fst] at hc
  exact congrArg (fun L => L v) hc

private theorem mixed_curvature
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hpos : ∀ x, 0 < f x)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (U V : Cₛ^∞⟮J; F, (TangentSpace J : N → Type _)⟯) (p : M × N) :
    connectionRiemannCurvatureField (LeviCivita (g.warpedProduct h f hf hpos))
        (productVectorField Y 0) (productVectorField 0 U) (productVectorField 0 V) p =
      (-(f p.1 * h.inner p.2 (U p.2) (V p.2)) •
        (LeviCivita g) (gradFun g f) p.1 (Y p.1), 0) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : CompleteSpace F := FiniteDimensional.complete ℝ F
  let C := LeviCivita (g.warpedProduct h f hf hpos)
  let X := productVectorField Y (0 : Cₛ^∞⟮J; F, (TangentSpace J : N → Type _)⟯)
  let A := productVectorField (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) U
  let B := productVectorField (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) V
  let G : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨gradFun g f, DifferentialGeometry.Geometry.Operator.WithBoundary.gradFun_contMDiff_total g hf⟩
  let W := productVectorField G (0 : Cₛ^∞⟮J; F, (TangentSpace J : N → Type _)⟯)
  let T : Cₛ^∞⟮J; F, (TangentSpace J : N → Type _)⟯ :=
    ⟨fun y => (LeviCivita h) V y (U y), fun y => by
      apply CovariantDerivative.cov_smooth_apply_contMDiffAt
      rw [LeviCivita_eq_leviCivitaConnectionOfMetric]
      exact leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally h⟩
  let D := productVectorField (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) T
  let a : M × N → ℝ := fun z => -f z.1 * h.inner z.2 (U z.2) (V z.2)
  let q : M × N → ℝ := fun z => mvfderiv I f z.1 (Y z.1) / f z.1
  have hi := contMDiff_metric_inner h U V
  have ha : MDifferentiableAt (I.prod J) 𝓘(ℝ) a p :=
    ((hf.neg.comp contMDiff_fst).mul (hi.comp contMDiff_snd)).mdifferentiable (by simp) p
  have hdfY : ContMDiff I 𝓘(ℝ) ∞ (fun x => mvfderiv I f x (Y x)) := by
    apply (contMDiff_metric_inner g G Y).congr
    intro x
    exact (gradFun_metricDual_mvfderiv g f x (Y x)).symm
  have hqbase := hdfY.div₀ hf (fun x => ne_of_gt (hpos x))
  have hq : MDifferentiableAt (I.prod J) 𝓘(ℝ) q p :=
    (hqbase.comp contMDiff_fst).mdifferentiable (by simp) p
  have hAB : (fun z => C B z (A z)) = a • (fun z => W z) + (fun z => D z) := by
    funext z
    change (LeviCivita (g.warpedProduct h f hf hpos)) (productVectorField 0 V) z
      (0, U z.2) = _
    erw [leviCivita_warpedProduct_vertical_vertical]
    apply Prod.ext
    · change -(f z.1 * h.inner z.2 (U z.2) (V z.2)) • gradFun g f z.1 =
        (-f z.1 * h.inner z.2 (U z.2) (V z.2)) • gradFun g f z.1 + 0
      rw [neg_mul, add_zero]
    · have hc (c : ℝ) (t : F) : t = c • (0 : F) + t := by simp
      exact hc (a z) ((LeviCivita h) V z.2 (U z.2))
  have hXB : (fun z => C B z (X z)) = q • (fun z => B z) := by
    funext z
    change (LeviCivita (g.warpedProduct h f hf hpos)) (productVectorField 0 V) z
      (Y z.1, 0) = _
    erw [leviCivita_warpedProduct_horizontal_vertical]
    exact Prod.ext (smul_zero _).symm rfl
  have hbr : _root_.VectorField.mlieBracket (I.prod J) X A p = 0 := by
    change _root_.VectorField.mlieBracket (I.prod J) (productVectorField Y 0)
      (productVectorField 0 U) p = 0
    rw [mlieBracket_productVectorField]
    simp only [ContMDiffSection.coe_zero, _root_.VectorField.mlieBracket_zero_right,
      _root_.VectorField.mlieBracket_zero_left, Pi.zero_apply]
    rfl
  have hda : mvfderiv (I.prod J) a p (X p) =
      -mvfderiv I f p.1 (Y p.1) * h.inner p.2 (U p.2) (V p.2) := by
    have hc := mvfderiv_comp p (hi.mdifferentiable (by simp) p.2)
      (mdifferentiableAt_snd (I := I) (I' := J))
    rw [mfderiv_snd] at hc
    change mvfderiv (I.prod J)
      ((fun z : M × N => -f z.1) * (fun z => h.inner z.2 (U z.2) (V z.2))) p (X p) = _
    erw [_root_.mvfderiv_fun_mul
      ((hf.neg.comp contMDiff_fst).mdifferentiable (by simp) p)
      ((hi.comp contMDiff_snd).mdifferentiable (by simp) p)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    erw [derivative_fst p (hf.neg.mdifferentiable (by simp) p.1), hc]
    change -f p.1 * mvfderiv J (fun y => h.inner y (U y) (V y)) p.2 0 +
      h.inner p.2 (U p.2) (V p.2) * mvfderiv I (-f) p.1 (Y p.1) = _
    rw [map_zero, mvfderiv_neg, neg_apply]
    ring
  have hdq : mvfderiv (I.prod J) q p (A p) = 0 := by
    erw [show q = fun z : M × N => mvfderiv I f z.1 (Y z.1) / f z.1 from rfl,
      derivative_fst p (hqbase.mdifferentiable (by simp) p.1)]
    exact map_zero _
  change connectionRiemannCurvatureField C X A B p = _
  unfold connectionRiemannCurvatureField
  rw [hAB, hXB, hbr, map_zero, sub_zero]
  rw [C.isCovariantDerivativeOnUniv.add
    (ha.smul_section W.mdifferentiableAt) D.mdifferentiableAt,
    C.isCovariantDerivativeOnUniv.leibniz W.mdifferentiableAt ha,
    C.isCovariantDerivativeOnUniv.leibniz B.mdifferentiableAt hq]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, hda, hdq,
    zero_smul, add_zero]
  have hWX : C W p (X p) = ((LeviCivita g) G p.1 (Y p.1), 0) :=
    horizontal_horizontal g h f hf hpos G p (Y p.1)
  have hDX : C D p (X p) = (0, q p • T p.2) :=
    leviCivita_warpedProduct_horizontal_vertical g h f hf hpos T p (Y p.1)
  have hBA : C B p (A p) =
      (-(f p.1 * h.inner p.2 (U p.2) (V p.2)) • G p.1, T p.2) :=
    leviCivita_warpedProduct_vertical_vertical g h f hf hpos V p (U p.2)
  rw [hWX, hDX, hBA]
  have hcancel : q p * (-(f p.1 * h.inner p.2 (U p.2) (V p.2))) =
      -mvfderiv I f p.1 (Y p.1) * h.inner p.2 (U p.2) (V p.2) := by
    dsimp [q]
    field_simp [ne_of_gt (hpos p.1)]
  apply Prod.ext
  · change a p • ((LeviCivita g) G p.1 (Y p.1)) +
      (-mvfderiv I f p.1 (Y p.1) * h.inner p.2 (U p.2) (V p.2)) • G p.1 + 0 -
      q p • (-(f p.1 * h.inner p.2 (U p.2) (V p.2)) • G p.1) = _
    rw [add_zero, smul_smul, hcancel, add_sub_cancel_right]
    change (-f p.1 * _) • _ = (-(f p.1 * _)) • _
    rw [neg_mul]
    rfl
  · have hc (a b c : ℝ) (t : F) :
        a • (0 : F) + b • (0 : F) + c • t - c • t = 0 := by simp
    exact hc (a p) (-mvfderiv I f p.1 (Y p.1) * h.inner p.2 (U p.2) (V p.2))
      (q p) (T p.2)

theorem metricRm04StandardAt_warpedProduct_mixed
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hpos : ∀ x, 0 < f x)
    (p : M × N) (u z : TangentSpace I p.1) (v w : TangentSpace J p.2) :
    metricRm04StandardAt (g.warpedProduct h f hf hpos) p
      (u, 0) (0, v) (0, w) (z, 0) =
      -(f p.1 * h.inner p.2 v w) *
        g.inner p.1 z ((LeviCivita g) (gradFun g f) p.1 u) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : CompleteSpace F := FiniteDimensional.complete ℝ F
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) p.1 u
  obtain ⟨Z, hZ⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) p.1 z
  obtain ⟨U, hU⟩ := ContMDiffSection.exists_eq_at (I := J) (F := F)
    (V := (TangentSpace J : N → Type _)) (n := (⊤ : ℕ∞)) p.2 v
  obtain ⟨V, hV⟩ := ContMDiffSection.exists_eq_at (I := J) (F := F)
    (V := (TangentSpace J : N → Type _)) (n := (⊤ : ℕ∞)) p.2 w
  let G := g.warpedProduct h f hf hpos
  have hc := CovariantDerivative.riemannCurvature04At_apply_smooth G
    (metricCov G) (metricCov_smooth G)
    (productVectorField X 0) (productVectorField 0 U)
    (productVectorField 0 V) (productVectorField Z 0) p
  change metricRm04StandardAt G p (productVectorField X 0 p)
    (productVectorField 0 U p) (productVectorField 0 V p) (productVectorField Z 0 p) = _ at hc
  have hm := mixed_curvature g h f hf hpos X U V p
  change connectionRiemannCurvatureField (metricCov G)
    (productVectorField X 0) (productVectorField 0 U) (productVectorField 0 V) p = _ at hm
  rw [hm] at hc
  simp only [productVectorField_apply, ContMDiffSection.coe_zero, Pi.zero_apply,
    hX, hZ, hU, hV] at hc
  erw [hc]
  change (g.warpedProduct h f hf hpos).inner p (z, 0)
    (-(f p.1 * h.inner p.2 v w) • (LeviCivita g) (gradFun g f) p.1 u, 0) = _
  erw [SmoothRiemannianMetric.warpedProduct_inner]
  have hz : h.inner p.2 (0 : TangentSpace J p.2) 0 = 0 := by rw [map_zero]
  erw [hz]
  simp only [map_smul, smul_eq_mul, mul_zero, add_zero]

end DifferentialGeometry.Geometry.Curvature
