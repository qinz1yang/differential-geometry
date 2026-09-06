import DifferentialGeometry.Analysis.Parabolic.Dirichlet.MovingMassTrace

noncomputable section

open Manifold MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Manifold NNReal
  RealInnerProductSpace Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem two_mul_dirichletWeakForm_smoothScalarDirichletMul_le
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (X : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a : ℝ) (φ : C^∞⟮I_half n, M; ℝ⟯)
    {δ Cφ Cx Cgrad : ℝ} (hδ : 0 < δ)
    (hφ : ∀ x : M, δ ≤ φ x ∧ φ x ≤ Cφ)
    (hX : ∀ x : M, h.inner x (X x) (X x) ≤ Cx)
    (hgrad : ∀ x : M,
      h.inner x (gradientFun (I := I_half n) h φ x)
        (gradientFun (I := I_half n) h φ x) ≤ Cgrad)
    (u : SmoothScalarDirichlet q) :
    2 * dirichletWeakForm h X a u (smoothScalarDirichletMul q φ u) ≤
      ((2 * Cφ ^ 2 * Cx + 2 * Cgrad) / δ + 2 * |a| * Cφ) *
        dirichletMass h u u := by
  let μ := riemannianVolumeMeasure (I := I_half n) (M := M) h
  let v := smoothScalarDirichletMul q φ u
  let C := (2 * Cφ ^ 2 * Cx + 2 * Cgrad) / δ + 2 * |a| * Cφ
  have hpoint (x : M) :
      2 * (-h.inner x
          (gradFun (I := I_half n) h u.toFun x)
          (gradFun (I := I_half n) h v.toFun x) +
        h.inner x (X x) (gradFun (I := I_half n) h u.toFun x) * v.toFun x -
        a * (u.toFun x * v.toFun x)) ≤ C * (u.toFun x * u.toFun x) := by
    let A := gradientFun (I := I_half n) h u.toFun x
    let P := gradientFun (I := I_half n) h φ x
    let Y := φ x • X x - P
    have hA : 0 ≤ h.inner x A A := metric_inner_self_nonneg h x A
    have hCx : 0 ≤ Cx := (metric_inner_self_nonneg h x (X x)).trans (hX x)
    have hφpos : 0 < φ x := hδ.trans_le (hφ x).1
    have hCφ : 0 < Cφ := hφpos.trans_le (hφ x).2
    have hφsq : φ x ^ 2 ≤ Cφ ^ 2 :=
      sq_le_sq₀ hφpos.le hCφ.le |>.2 (hφ x).2
    have hsum := metric_inner_self_nonneg h x (φ x • X x + P)
    have hY : h.inner x Y Y ≤ 2 * Cφ ^ 2 * Cx + 2 * Cgrad := by
      have hXX := mul_le_mul_of_nonneg_left (hX x) (sq_nonneg (φ x))
      have hXX' := mul_le_mul_of_nonneg_right hφsq hCx
      have hP := hgrad x
      dsimp only [Y]
      simp only [map_sub, sub_apply, map_smul, smul_apply, smul_eq_mul]
      simp only [map_add, add_apply, map_smul, smul_apply, smul_eq_mul] at hsum
      rw [h.symm x (X x) P] at hsum ⊢
      nlinarith
    have hsq := metric_inner_self_nonneg h x (δ • A - u.toFun x • Y)
    simp only [map_sub, sub_apply, map_smul, smul_apply, smul_eq_mul] at hsq
    rw [h.symm x Y A] at hsq
    have hweighted :
        -2 * φ x * h.inner x A A + 2 * u.toFun x * h.inner x A Y ≤
          ((2 * Cφ ^ 2 * Cx + 2 * Cgrad) / δ) * (u.toFun x * u.toFun x) := by
      apply (mul_le_mul_iff_right₀ hδ).mp
      rw [show δ * (((2 * Cφ ^ 2 * Cx + 2 * Cgrad) / δ) *
        (u.toFun x * u.toFun x)) =
          (2 * Cφ ^ 2 * Cx + 2 * Cgrad) * (u.toFun x * u.toFun x) by
            field_simp]
      have hYmul := mul_le_mul_of_nonneg_right hY (mul_self_nonneg (u.toFun x))
      have hneg := mul_nonneg hδ.le
        (mul_nonneg (show 0 ≤ 2 * φ x - δ by linarith [(hφ x).1]) hA)
      nlinarith
    have hpotential : -2 * a * φ x * (u.toFun x * u.toFun x) ≤
        (2 * |a| * Cφ) * (u.toFun x * u.toFun x) := by
      have h₁ := mul_le_mul_of_nonneg_right (neg_le_abs a) hφpos.le
      have h₂ := mul_le_mul_of_nonneg_left (hφ x).2 (abs_nonneg a)
      have h₃ := mul_le_mul_of_nonneg_right (h₁.trans h₂)
        (mul_self_nonneg (u.toFun x))
      nlinarith
    have hmul : gradFun (I := I_half n) h v.toFun x = φ x • A + u.toFun x • P := by
      exact gradientFun_mul h (φ.contMDiff.mdifferentiable (by simp) x)
        (u.smooth.mdifferentiable (by simp) x)
    rw [hmul]
    change 2 * (-h.inner x A (φ x • A + u.toFun x • P) +
      h.inner x (X x) A * (φ x * u.toFun x) -
      a * (u.toFun x * (φ x * u.toFun x))) ≤ C * (u.toFun x * u.toFun x)
    simp only [map_add, map_smul, smul_eq_mul]
    dsimp only [Y] at hweighted
    simp only [map_sub, map_smul, smul_eq_mul] at hweighted
    rw [h.symm x (X x) A]
    dsimp only [C]
    nlinarith
  have hE := dirichletEnergy_integrable h u v
  have hD := dirichletDrift_integrable h X u v
  have hM := dirichletMass_integrable h u v
  have hC := (dirichletMass_integrable h u u).const_mul C
  have hEn : Integrable (fun x : M =>
      -h.inner x (gradFun (I := I_half n) h u.toFun x)
        (gradFun (I := I_half n) h v.toFun x)) μ := hE.neg
  have hED : Integrable (fun x : M =>
      -h.inner x (gradFun (I := I_half n) h u.toFun x)
        (gradFun (I := I_half n) h v.toFun x) +
      h.inner x (X x) (gradFun (I := I_half n) h u.toFun x) * v.toFun x) μ :=
    hE.neg.add hD
  have hMa : Integrable (fun x : M => a * (u.toFun x * v.toFun x)) μ :=
    hM.const_mul a
  have hint := integral_mono ((hED.sub hMa).const_mul 2) hC hpoint
  simp only [Pi.sub_apply] at hint
  rw [integral_const_mul, integral_sub hED hMa,
    integral_add hEn hD, integral_neg, integral_const_mul, integral_const_mul] at hint
  exact hint

theorem two_mul_dirichletWeakFormCompl_smoothMulH1ComplDirichlet_le
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (X : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a Cx : ℝ) (hX : ∀ x : M, h.inner x (X x) (X x) ≤ Cx)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ v : TangentSpace (I_half n) x,
      Cg⁻¹ * q.inner x v v ≤ h.inner x v v ∧
        h.inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) h ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q)
    (φ : C^∞⟮I_half n, M; ℝ⟯)
    {δ Cφ Cgrad : ℝ} (hδ : 0 < δ)
    (hφ : ∀ x : M, δ ≤ φ x ∧ φ x ≤ Cφ)
    (hgrad : ∀ x : M,
      h.inner x (gradientFun (I := I_half n) h φ x)
        (gradientFun (I := I_half n) h φ x) ≤ Cgrad)
    (u : H1ComplDirichlet q) :
    2 * dirichletWeakFormCompl h X a Cx hX hCg hequiv Cv hCv0 hCvtop hvol u
        (smoothMulH1ComplDirichlet q φ u) ≤
      max ((2 * Cφ ^ 2 * Cx + 2 * Cgrad) / δ + 2 * |a| * Cφ) 0 * Cv.toReal *
        ‖H1ComplDirichletToLp q u‖ ^ 2 := by
  let F := dirichletWeakFormCompl h X a Cx hX hCg hequiv Cv hCv0 hCvtop hvol
  let S := smoothMulH1ComplDirichlet q φ
  let K := (2 * Cφ ^ 2 * Cx + 2 * Cgrad) / δ + 2 * |a| * Cφ
  refine (denseRange_smoothToH1ComplDirichlet q).induction_on u
    (isClosed_le (continuous_const.mul
      ((F.continuous.comp continuous_id).clm_apply S.continuous))
      (continuous_const.mul ((H1ComplDirichletToLp q).continuous.norm.pow 2))) ?_
  intro v
  rw [smoothMulH1ComplDirichlet_smoothToH1ComplDirichlet,
    dirichletWeakFormCompl_apply_smooth,
    H1ComplDirichletToLp_smoothToH1ComplDirichlet]
  have hbound := two_mul_dirichletWeakForm_smoothScalarDirichletMul_le
    h X a φ hδ hφ hX hgrad v
  have hmass := dirichletMass_self_le_of_volume h Cv hCv0 hCvtop hvol v
  have hnorm : dirichletMass q v v = ‖smoothToLpDirichlet q v‖ ^ 2 := by
    rw [← dirichletMassLp_apply_smooth q 1 ENNReal.one_ne_top
      (by simp only [one_smul, le_refl]), dirichletMassLp_self_apply,
      real_inner_self_eq_norm_sq]
  calc
    _ ≤ K * dirichletMass h v v := hbound
    _ ≤ max K 0 * dirichletMass h v v :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (dirichletMass_self_nonneg h v)
    _ ≤ max K 0 * (Cv.toReal * dirichletMass q v v) :=
      mul_le_mul_of_nonneg_left hmass (le_max_right _ _)
    _ = _ := by rw [hnorm]; ring

theorem abs_dirichletMassVariationCompl_smoothMulH1ComplDirichlet_le
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_half n) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_half n) (M := M) D G.metric)
    {t : ℝ} (ht : t ∈ D.regular) (B : ℝ)
    (htrace : ∀ x : M,
      |traceTimeDerivMetric (I := I_half n) G.metric t x| ≤ B)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ v : TangentSpace (I_half n) x,
      Cg⁻¹ * q.inner x v v ≤ (G.metric t).inner x v v ∧
        (G.metric t).inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) (G.metric t) ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q)
    (φ : C^∞⟮I_half n, M; ℝ⟯) {Cφ : ℝ}
    (hφ : ∀ x : M, |φ x| ≤ Cφ)
    (u : H1ComplDirichlet q) :
    |dirichletMassVariationCompl hG ht B htrace hCg hequiv Cv hCv0 hCvtop hvol u
        (smoothMulH1ComplDirichlet q φ u)| ≤
      max ((1 / 2) * B * Cφ) 0 * Cv.toReal * ‖H1ComplDirichletToLp q u‖ ^ 2 := by
  let F := dirichletMassVariationCompl hG ht B htrace hCg hequiv Cv hCv0 hCvtop hvol
  let S := smoothMulH1ComplDirichlet q φ
  let K := (1 / 2) * B * Cφ
  refine (denseRange_smoothToH1ComplDirichlet q).induction_on u
    (isClosed_le ((F.continuous.comp continuous_id).clm_apply S.continuous).abs
      (continuous_const.mul ((H1ComplDirichletToLp q).continuous.norm.pow 2))) ?_
  intro v
  rw [smoothMulH1ComplDirichlet_smoothToH1ComplDirichlet,
    dirichletMassVariationCompl_apply_smooth,
    H1ComplDirichletToLp_smoothToH1ComplDirichlet]
  have hbound := abs_dirichletMassVariation_smoothScalarDirichletMul_le
    G.metric t B htrace φ hφ v
  have hmass := dirichletMass_self_le_of_volume (G.metric t) Cv hCv0 hCvtop hvol v
  have hnorm : dirichletMass q v v = ‖smoothToLpDirichlet q v‖ ^ 2 := by
    rw [← dirichletMassLp_apply_smooth q 1 ENNReal.one_ne_top
      (by simp only [one_smul, le_refl]), dirichletMassLp_self_apply,
      real_inner_self_eq_norm_sq]
  calc
    _ ≤ K * dirichletMass (G.metric t) v v := hbound
    _ ≤ max K 0 * dirichletMass (G.metric t) v v :=
      mul_le_mul_of_nonneg_right (le_max_left _ _)
        (dirichletMass_self_nonneg (G.metric t) v)
    _ ≤ max K 0 * (Cv.toReal * dirichletMass q v v) :=
      mul_le_mul_of_nonneg_left hmass (le_max_right _ _)
    _ = _ := by rw [hnorm]; ring

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
