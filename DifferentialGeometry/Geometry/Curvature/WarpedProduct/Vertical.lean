import DifferentialGeometry.Geometry.Curvature.Metric.Defs
import DifferentialGeometry.Geometry.Connection.WarpedProduct
import DifferentialGeometry.Geometry.Connection.LeviCivita.Characterization.Torsion
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

omit [T2Space N] in
private theorem vertical_metric_identity
    (h : SmoothRiemannianMetric J N)
    (U V W : Cₛ^∞⟮J; F, (TangentSpace J : N → Type _)⟯) (x : N) :
    mvfderiv J (fun y => h.inner y (V y) (W y)) x (U x) +
        h.inner x (U x) ((LeviCivita h) W x (V x)) -
      mvfderiv J (fun y => h.inner y (U y) (W y)) x (V x) -
        h.inner x (V x) ((LeviCivita h) W x (U x)) -
        h.inner x (_root_.VectorField.mlieBracket J U V x) (W x) = 0 := by
  let : CompleteSpace F := FiniteDimensional.complete ℝ F
  have hfirst := (leviCivitaConnectionOfMetric_isMetricCompatible h).mvfderiv_inner
    (U x) V.mdifferentiableAt W.mdifferentiableAt
  have hsecond := (leviCivitaConnectionOfMetric_isMetricCompatible h).mvfderiv_inner
    (V x) U.mdifferentiableAt W.mdifferentiableAt
  have ht := torsion_free_at_apply (leviCivitaConnectionOfMetric_isTorsionFree h x)
    U.mdifferentiableAt V.mdifferentiableAt
  have hp := congrArg (fun v => h.inner x v (W x)) ht
  rw [map_sub, sub_apply] at hp
  change h.inner x ((LeviCivita h) V x (U x)) (W x) -
    h.inner x ((LeviCivita h) U x (V x)) (W x) = _ at hp
  change mvfderiv J (fun y => h.inner y (V y) (W y)) x (U x) =
    h.inner x ((LeviCivita h) V x (U x)) (W x) +
      h.inner x (V x) ((LeviCivita h) W x (U x)) at hfirst
  change mvfderiv J (fun y => h.inner y (U y) (W y)) x (V x) =
    h.inner x ((LeviCivita h) U x (V x)) (W x) +
      h.inner x (U x) ((LeviCivita h) W x (V x)) at hsecond
  rw [hfirst, hsecond]
  linarith

private theorem vertical_horizontal
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hpos : ∀ x, 0 < f x)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (p : M × N) (v : TangentSpace J p.2) :
    (LeviCivita (g.warpedProduct h f hf hpos)) (productVectorField Y 0) p (0, v) =
      (0, (mvfderiv I f p.1 (Y p.1) / f p.1) • v) := by
  erw [leviCivita_warpedProduct_productVectorField]
  have hm : h.inner p.2 v (0 : TangentSpace J p.2) = 0 := map_zero _
  have hz : (LeviCivita h) (0 : Cₛ^∞⟮J; F, (TangentSpace J : N → Type _)⟯)
      p.2 v = 0 := by
    change (LeviCivita h) 0 p.2 v = 0
    rw [CovariantDerivative.zero]
    rfl
  erw [hm, hz, map_zero ((LeviCivita g) Y p.1)]
  simp only [mul_zero, zero_smul, sub_self, ContMDiffSection.coe_zero,
    Pi.zero_apply, smul_zero]
  erw [zero_add, zero_add]
  rfl

private theorem vertical_second_derivative
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hpos : ∀ x, 0 < f x)
    (U V W : Cₛ^∞⟮J; F, (TangentSpace J : N → Type _)⟯) (p : M × N) :
    (LeviCivita (g.warpedProduct h f hf hpos))
      (fun z => (LeviCivita (g.warpedProduct h f hf hpos))
        (productVectorField 0 W) z (0, V z.2)) p (0, U p.2) =
      ((-f p.1 * (mvfderiv J (fun y => h.inner y (V y) (W y)) p.2 (U p.2) +
          h.inner p.2 (U p.2) ((LeviCivita h) W p.2 (V p.2)))) • gradFun g f p.1,
        (LeviCivita h) (fun y => (LeviCivita h) W y (V y)) p.2 (U p.2) -
          (h.inner p.2 (V p.2) (W p.2) *
            g.inner p.1 (gradFun g f p.1) (gradFun g f p.1)) • U p.2) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : CompleteSpace F := FiniteDimensional.complete ℝ F
  let C := LeviCivita (g.warpedProduct h f hf hpos)
  let A := productVectorField (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) U
  let G : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨gradFun g f, DifferentialGeometry.Geometry.Operator.WithBoundary.gradFun_contMDiff_total g hf⟩
  let T : Cₛ^∞⟮J; F, (TangentSpace J : N → Type _)⟯ :=
    ⟨fun y => (LeviCivita h) W y (V y), fun y => by
      apply CovariantDerivative.cov_smooth_apply_contMDiffAt
      rw [LeviCivita_eq_leviCivitaConnectionOfMetric]
      exact leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally h⟩
  let P := productVectorField G (0 : Cₛ^∞⟮J; F, (TangentSpace J : N → Type _)⟯)
  let Q := productVectorField (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) T
  let a : M × N → ℝ := fun z => -f z.1 * h.inner z.2 (V z.2) (W z.2)
  have hi := contMDiff_metric_inner h V W
  have ha : MDifferentiableAt (I.prod J) 𝓘(ℝ) a p :=
    ((hf.neg.comp contMDiff_fst).mul (hi.comp contMDiff_snd)).mdifferentiable (by simp) p
  have hfield : (fun z => C (productVectorField 0 W) z (0, V z.2)) =
      a • (fun z => P z) + (fun z => Q z) := by
    funext z
    erw [leviCivita_warpedProduct_vertical_vertical]
    apply Prod.ext
    · change -(f z.1 * h.inner z.2 (V z.2) (W z.2)) • gradFun g f z.1 =
        (-f z.1 * h.inner z.2 (V z.2) (W z.2)) • gradFun g f z.1 + 0
      rw [neg_mul, add_zero]
    · have hc (c : ℝ) (t : F) : t = c • (0 : F) + t := by simp
      exact hc (a z) (T z.2)
  have hda : mvfderiv (I.prod J) a p (A p) =
      -f p.1 * mvfderiv J (fun y => h.inner y (V y) (W y)) p.2 (U p.2) := by
    have hb := mvfderiv_comp p (hf.neg.mdifferentiable (by simp) p.1)
      (mdifferentiableAt_fst (I := I) (I' := J))
    have hc := mvfderiv_comp p (hi.mdifferentiable (by simp) p.2)
      (mdifferentiableAt_snd (I := I) (I' := J))
    rw [mfderiv_fst] at hb
    rw [mfderiv_snd] at hc
    change mvfderiv (I.prod J)
      ((fun z : M × N => -f z.1) * (fun z => h.inner z.2 (V z.2) (W z.2))) p
        (A p) = _
    erw [_root_.mvfderiv_fun_mul
      ((hf.neg.comp contMDiff_fst).mdifferentiable (by simp) p)
      ((hi.comp contMDiff_snd).mdifferentiable (by simp) p)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    erw [hb, hc]
    change -f p.1 * mvfderiv J (fun y => h.inner y (V y) (W y)) p.2 (U p.2) +
      h.inner p.2 (V p.2) (W p.2) * mvfderiv I (-f) p.1 0 = _
    rw [map_zero, mul_zero, add_zero]
  change C (fun z => C (productVectorField 0 W) z (0, V z.2)) p (A p) = _
  rw [hfield, C.isCovariantDerivativeOnUniv.add
    (ha.smul_section P.mdifferentiableAt) Q.mdifferentiableAt,
    C.isCovariantDerivativeOnUniv.leibniz P.mdifferentiableAt ha]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, hda]
  have hP := vertical_horizontal g h f hf hpos G p (U p.2)
  have hQ := leviCivita_warpedProduct_vertical_vertical g h f hf hpos T p (U p.2)
  change C P p (A p) = _ at hP
  change C Q p (A p) = _ at hQ
  erw [hP, hQ]
  have hnorm : mvfderiv I f p.1 (G p.1) = g.inner p.1 (G p.1) (G p.1) :=
    (gradFun_metricDual_mvfderiv g f p.1 (G p.1)).symm
  have hc : a p * (mvfderiv I f p.1 (G p.1) / f p.1) =
      -(h.inner p.2 (V p.2) (W p.2) * g.inner p.1 (G p.1) (G p.1)) := by
    rw [hnorm]
    dsimp [a]
    field_simp [ne_of_gt (hpos p.1)]
  apply Prod.ext
  · change a p • (0 : TangentSpace I p.1) +
      (-f p.1 * mvfderiv J (fun y => h.inner y (V y) (W y)) p.2 (U p.2)) • G p.1 +
      (-(f p.1 * h.inner p.2 (U p.2) (T p.2))) • G p.1 = _
    rw [smul_zero, zero_add, ← add_smul]
    have hs : -f p.1 * mvfderiv J (fun y => h.inner y (V y) (W y)) p.2 (U p.2) +
        -(f p.1 * h.inner p.2 (U p.2) (T p.2)) =
        -f p.1 * (mvfderiv J (fun y => h.inner y (V y) (W y)) p.2 (U p.2) +
          h.inner p.2 (U p.2) (T p.2)) := by ring
    rw [hs]
    rfl
  · change a p • ((mvfderiv I f p.1 (G p.1) / f p.1) • U p.2) +
      (-f p.1 * mvfderiv J (fun y => h.inner y (V y) (W y)) p.2 (U p.2)) •
        (0 : TangentSpace J p.2) + (LeviCivita h) T p.2 (U p.2) = _
    rw [smul_smul, hc, smul_zero, add_zero, neg_smul]
    change -((h.inner p.2 (V p.2) (W p.2) *
        g.inner p.1 (G p.1) (G p.1)) • U p.2) +
      (LeviCivita h) T p.2 (U p.2) =
      (LeviCivita h) T p.2 (U p.2) -
        (h.inner p.2 (V p.2) (W p.2) *
          g.inner p.1 (G p.1) (G p.1)) • U p.2
    abel

private theorem warpedProduct_vertical_curvature
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hpos : ∀ x, 0 < f x)
    (U V W : Cₛ^∞⟮J; F, (TangentSpace J : N → Type _)⟯) (p : M × N) :
    connectionRiemannCurvatureField (LeviCivita (g.warpedProduct h f hf hpos))
      (productVectorField 0 U) (productVectorField 0 V) (productVectorField 0 W) p =
      (0, connectionRiemannCurvatureField (LeviCivita h) U V W p.2 -
        (h.inner p.2 (V p.2) (W p.2) *
          g.inner p.1 (gradFun g f p.1) (gradFun g f p.1)) • U p.2 +
        (h.inner p.2 (U p.2) (W p.2) *
          g.inner p.1 (gradFun g f p.1) (gradFun g f p.1)) • V p.2) := by
  have hbr : _root_.VectorField.mlieBracket (I.prod J)
      (productVectorField 0 U) (productVectorField 0 V) p =
      (0, _root_.VectorField.mlieBracket J U V p.2) := by
    rw [mlieBracket_productVectorField]
    simp only [ContMDiffSection.coe_zero, _root_.VectorField.mlieBracket_zero_left,
      Pi.zero_apply]
    rfl
  let C := LeviCivita (g.warpedProduct h f hf hpos)
  let A := productVectorField (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) U
  let B := productVectorField (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) V
  let D := productVectorField (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) W
  have hUV := vertical_second_derivative g h f hf hpos U V W p
  have hVU := vertical_second_derivative g h f hf hpos V U W p
  have hB := leviCivita_warpedProduct_vertical_vertical g h f hf hpos W p
    (_root_.VectorField.mlieBracket J U V p.2)
  change C (fun z => C D z (B z)) p (A p) = _ at hUV
  change C (fun z => C D z (A z)) p (B p) = _ at hVU
  change C D p (0, _root_.VectorField.mlieBracket J U V p.2) = _ at hB
  change connectionRiemannCurvatureField C A B D p = _
  rw [connectionRiemannCurvatureField]
  rw [hUV, hVU]
  change _root_.VectorField.mlieBracket (I.prod J) A B p = _ at hbr
  rw [hbr]
  erw [hB]
  apply Prod.ext
  · change (-f p.1 * (mvfderiv J (fun y => h.inner y (V y) (W y)) p.2 (U p.2) +
        h.inner p.2 (U p.2) ((LeviCivita h) W p.2 (V p.2)))) • gradFun g f p.1 -
      (-f p.1 * (mvfderiv J (fun y => h.inner y (U y) (W y)) p.2 (V p.2) +
        h.inner p.2 (V p.2) ((LeviCivita h) W p.2 (U p.2)))) • gradFun g f p.1 -
      (-(f p.1 * h.inner p.2 (_root_.VectorField.mlieBracket J U V p.2) (W p.2))) •
        gradFun g f p.1 = 0
    rw [← sub_smul, ← sub_smul]
    have hid := vertical_metric_identity h U V W p.2
    have hc : (-f p.1 * (mvfderiv J (fun y => h.inner y (V y) (W y)) p.2 (U p.2) +
        h.inner p.2 (U p.2) ((LeviCivita h) W p.2 (V p.2)))) -
      (-f p.1 * (mvfderiv J (fun y => h.inner y (U y) (W y)) p.2 (V p.2) +
        h.inner p.2 (V p.2) ((LeviCivita h) W p.2 (U p.2)))) -
      (-(f p.1 * h.inner p.2 (_root_.VectorField.mlieBracket J U V p.2) (W p.2))) = 0 := by
      linear_combination (norm := ring) (-f p.1) * hid
    rw [hc, zero_smul]
  · change ((LeviCivita h) (fun y => (LeviCivita h) W y (V y)) p.2 (U p.2) -
        (h.inner p.2 (V p.2) (W p.2) *
          g.inner p.1 (gradFun g f p.1) (gradFun g f p.1)) • U p.2) -
      ((LeviCivita h) (fun y => (LeviCivita h) W y (U y)) p.2 (V p.2) -
        (h.inner p.2 (U p.2) (W p.2) *
          g.inner p.1 (gradFun g f p.1) (gradFun g f p.1)) • V p.2) -
      (LeviCivita h) W p.2 (_root_.VectorField.mlieBracket J U V p.2) = _
    unfold connectionRiemannCurvatureField
    module


theorem metricRm04StandardAt_warpedProduct_vertical
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hpos : ∀ x, 0 < f x)
    (p : M × N) (u v w t : TangentSpace J p.2) (z : TangentSpace I p.1) :
    metricRm04StandardAt (g.warpedProduct h f hf hpos) p
      (0, u) (0, v) (0, w) (z, t) =
      f p.1 ^ 2 * (metricRm04StandardAt h p.2 u v w t -
        (h.inner p.2 v w * g.inner p.1 (gradFun g f p.1) (gradFun g f p.1)) *
          h.inner p.2 t u +
        (h.inner p.2 u w * g.inner p.1 (gradFun g f p.1) (gradFun g f p.1)) *
          h.inner p.2 t v) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : CompleteSpace F := FiniteDimensional.complete ℝ F
  obtain ⟨U, hU⟩ := ContMDiffSection.exists_eq_at (I := J) (F := F)
    (V := (TangentSpace J : N → Type _)) (n := (⊤ : ℕ∞)) p.2 u
  obtain ⟨V, hV⟩ := ContMDiffSection.exists_eq_at (I := J) (F := F)
    (V := (TangentSpace J : N → Type _)) (n := (⊤ : ℕ∞)) p.2 v
  obtain ⟨W, hW⟩ := ContMDiffSection.exists_eq_at (I := J) (F := F)
    (V := (TangentSpace J : N → Type _)) (n := (⊤ : ℕ∞)) p.2 w
  obtain ⟨T, hT⟩ := ContMDiffSection.exists_eq_at (I := J) (F := F)
    (V := (TangentSpace J : N → Type _)) (n := (⊤ : ℕ∞)) p.2 t
  obtain ⟨Z, hZ⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) p.1 z
  let G := g.warpedProduct h f hf hpos
  have hc := CovariantDerivative.riemannCurvature04At_apply_smooth G
    (metricCov G) (metricCov_smooth G)
    (productVectorField 0 U) (productVectorField 0 V)
    (productVectorField 0 W) (productVectorField Z T) p
  change metricRm04StandardAt G p (productVectorField 0 U p)
    (productVectorField 0 V p) (productVectorField 0 W p) (productVectorField Z T p) = _ at hc
  have hm := warpedProduct_vertical_curvature g h f hf hpos U V W p
  change connectionRiemannCurvatureField (metricCov G)
    (productVectorField 0 U) (productVectorField 0 V) (productVectorField 0 W) p = _ at hm
  rw [hm] at hc
  simp only [productVectorField_apply, ContMDiffSection.coe_zero, Pi.zero_apply,
    hU, hV, hW, hT, hZ] at hc
  have hh := CovariantDerivative.riemannCurvature04At_apply_smooth h
    (metricCov h) (metricCov_smooth h) U V W T p.2
  change metricRm04StandardAt h p.2 (U p.2) (V p.2) (W p.2) (T p.2) = _ at hh
  rw [hU, hV, hW, hT] at hh
  erw [hc, SmoothRiemannianMetric.warpedProduct_inner]
  simp only [map_add, map_sub, map_smul, smul_eq_mul]
  have hz : g.inner p.1 z (0 : TangentSpace I p.1) = 0 := map_zero _
  erw [hz, zero_add]
  exact congrArg (fun c : ℝ => f p.1 ^ 2 *
    (c - (h.inner p.2 v w * g.inner p.1 (gradFun g f p.1) (gradFun g f p.1)) *
      h.inner p.2 t u +
      (h.inner p.2 u w * g.inner p.1 (gradFun g f p.1) (gradFun g f p.1)) *
        h.inner p.2 t v)) hh.symm

end DifferentialGeometry.Geometry.Curvature
