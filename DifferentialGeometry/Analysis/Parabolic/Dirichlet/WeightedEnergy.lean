import DifferentialGeometry.Analysis.ODE.IntegralGronwall
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.MovingMassTrace

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal InnerProductSpace Manifold NNReal
  RealInnerProductSpace Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
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

theorem exists_uniform_volumeDensity_energy_bound
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_half n) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_half n) (M := M) D G.metric)
    {T : ℝ} (hreg : Icc (0 : ℝ) T ⊆ D.regular)
    (X : ℝ → Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a : ℝ → ℝ) (hacont : ContinuousOn a (Icc (0 : ℝ) T))
    (Bx Bv : ℝ)
    (hX : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      (G.metric t).inner x (X t x) (X t x) ≤ Bx)
    (htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_half n) G.metric t x| ≤ Bv)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      ∀ v : TangentSpace (I_half n) x,
        Cg⁻¹ * q.inner x v v ≤ (G.metric t).inner x v v ∧
          (G.metric t).inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : ∀ t ∈ Icc (0 : ℝ) T,
      riemannianVolumeMeasure (I := I_half n) (M := M) (G.metric t) ≤
        Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ico (0 : ℝ) T, ∀ u : H1ComplDirichlet q,
      2 * (dirichletMassVariationComplOnIco hG hreg Bv htrace
          hCg hequiv Cv hCv0 hCvtop hvol t u
          (smoothMulH1ComplDirichlet q
            (riemannianVolumeDensitySmoothMap q (G.metric t)) u) +
        dirichletWeakFormComplOnIco G.metric X a Bx hX
          hCg hequiv Cv hCv0 hCvtop hvol t u
          (smoothMulH1ComplDirichlet q
            (riemannianVolumeDensitySmoothMap q (G.metric t)) u)) ≤
        C * ‖smoothMulLp q (riemannianVolumeDensitySmoothMap q (G.metric t))
          (H1ComplDirichletToLp q u)‖ ^ 2 := by
  let K : Set (ℝ × M) := Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)
  have hK : IsCompact K := isCompact_Icc.prod isCompact_univ
  have hρ := riemannianVolumeDensity_contMDiffOn_of_metricFamilySmoothOn hG q
  have hσ := riemannianVolumeDensity_swap_contMDiffOn_of_metricFamilySmoothOn hG q
  have hρcont := hρ.continuousOn.mono (Set.prod_mono hreg Set.Subset.rfl)
  have hσcont := hσ.continuousOn.mono (Set.prod_mono hreg Set.Subset.rfl)
  have hgrad := gradSq_joint (I := I_half n) G.metric D.regular_isOpen
    (fun α i j => hG.chartGramMatrix_contDiffOn (Set.Subset.rfl) α i j)
    (fun t x => riemannianVolumeDensity q (G.metric t) x) hρ
  have hgradcont := hgrad.continuousOn.mono (Set.prod_mono hreg Set.Subset.rfl)
  obtain ⟨Cρ, hCρ⟩ := hK.exists_bound_of_continuousOn hρcont
  obtain ⟨Cσ, hCσ⟩ := hK.exists_bound_of_continuousOn hσcont
  obtain ⟨Cgrad, hCgrad⟩ := hK.exists_bound_of_continuousOn hgradcont
  obtain ⟨Ca, hCa⟩ := isCompact_Icc.exists_bound_of_continuousOn hacont
  let L := max 1 (max Cρ (max Cσ Cgrad))
  have hL : 1 ≤ L := le_max_left _ _
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hδ : 0 < L⁻¹ := inv_pos.mpr hLpos
  have hbounds : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      L⁻¹ ≤ riemannianVolumeDensity q (G.metric t) x ∧
      riemannianVolumeDensity q (G.metric t) x ≤ L ∧
      (G.metric t).inner x
        (gradientFun (I := I_half n) (G.metric t)
          (riemannianVolumeDensity q (G.metric t)) x)
        (gradientFun (I := I_half n) (G.metric t)
          (riemannianVolumeDensity q (G.metric t)) x) ≤ L := by
    intro t ht x
    have hρbound := hCρ (t, x) ⟨ht, Set.mem_univ x⟩
    have hσbound := hCσ (t, x) ⟨ht, Set.mem_univ x⟩
    have hgbound := hCgrad (t, x) ⟨ht, Set.mem_univ x⟩
    rw [Real.norm_eq_abs] at hρbound hσbound hgbound
    have hρpos := riemannianVolumeDensity_pos q (G.metric t) x
    have hσle : riemannianVolumeDensity (G.metric t) q x ≤ L :=
      (le_abs_self _).trans (hσbound.trans
        ((le_max_left Cσ Cgrad).trans ((le_max_right Cρ _).trans (le_max_right 1 _))))
    have hρσ := riemannianVolumeDensity_mul_swap (G.metric t) q x
    have hmul := mul_le_mul_of_nonneg_right hσle hρpos.le
    have hlo : L⁻¹ ≤ riemannianVolumeDensity q (G.metric t) x := by
      rw [← one_div]
      apply (div_le_iff₀ hLpos).2
      nlinarith
    refine ⟨hlo, (le_abs_self _).trans (hρbound.trans
      ((le_max_left Cρ _).trans (le_max_right 1 _))), ?_⟩
    exact (le_abs_self _).trans (hgbound.trans
      ((le_max_right Cσ Cgrad).trans ((le_max_right Cρ _).trans (le_max_right 1 _))))
  let Kw := max ((2 * L ^ 2 * Bx + 2 * L) / L⁻¹ + 2 * max Ca 0 * L) 0
  let Kv := max ((1 / 2) * Bv * L) 0
  let B := (2 * Kv + Kw) * Cv.toReal
  have hB : 0 ≤ B :=
    mul_nonneg (add_nonneg (mul_nonneg (by norm_num) (le_max_right _ _))
      (le_max_right _ _)) ENNReal.toReal_nonneg
  refine ⟨B * L ^ 2, mul_nonneg hB (sq_nonneg _), fun t ht u => ?_⟩
  have htc : t ∈ Icc (0 : ℝ) T := ⟨ht.1, ht.2.le⟩
  let φ := riemannianVolumeDensitySmoothMap q (G.metric t)
  have hφ : ∀ x : M, L⁻¹ ≤ φ x ∧ φ x ≤ L :=
    fun x => ⟨(hbounds t htc x).1, (hbounds t htc x).2.1⟩
  have hφabs : ∀ x : M, |φ x| ≤ L := by
    intro x
    rw [abs_of_nonneg (hδ.le.trans (hφ x).1)]
    exact (hφ x).2
  have hgφ : ∀ x : M, (G.metric t).inner x
      (gradientFun (I := I_half n) (G.metric t) φ x)
      (gradientFun (I := I_half n) (G.metric t) φ x) ≤ L :=
    fun x => (hbounds t htc x).2.2
  have hv := abs_dirichletMassVariationCompl_smoothMulH1ComplDirichlet_le
    hG (hreg htc) Bv (htrace t ht) hCg (hequiv t htc)
    Cv hCv0 hCvtop (hvol t htc) φ hφabs u
  have hw := two_mul_dirichletWeakFormCompl_smoothMulH1ComplDirichlet_le
    (G.metric t) (X t) (a t) Bx (hX t ht) hCg (hequiv t htc)
    Cv hCv0 hCvtop (hvol t htc) φ hδ hφ hgφ u
  have hCa' : |a t| ≤ max Ca 0 := by
    have h := hCa t htc
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_left _ _)
  have hcoeff : max ((2 * L ^ 2 * Bx + 2 * L) / L⁻¹ + 2 * |a t| * L) 0 ≤ Kw := by
    apply max_le_max _ le_rfl
    gcongr
  have hw' : 2 * dirichletWeakFormCompl (G.metric t) (X t) (a t) Bx (hX t ht)
      hCg (hequiv t htc) Cv hCv0 hCvtop (hvol t htc) u
      (smoothMulH1ComplDirichlet q φ u) ≤ Kw * Cv.toReal * ‖H1ComplDirichletToLp q u‖ ^ 2 :=
    hw.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoeff ENNReal.toReal_nonneg) (sq_nonneg _))
  have hnorm : ‖H1ComplDirichletToLp q u‖ ≤
      L * ‖smoothMulLp q φ (H1ComplDirichletToLp q u)‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [smoothMulLp_apply_coeFn q φ (H1ComplDirichletToLp q u)] with x hx
    rw [hx, norm_mul, Real.norm_of_nonneg (hδ.le.trans (hφ x).1)]
    have hlo := (hφ x).1
    have hmul : 1 ≤ L * φ x := by
      have h := mul_le_mul_of_nonneg_left hlo hLpos.le
      rw [mul_inv_cancel₀ hLpos.ne'] at h
      exact h
    nlinarith [mul_nonneg (sub_nonneg.mpr hmul) (norm_nonneg (H1ComplDirichletToLp q u x))]
  rw [dirichletMassVariationComplOnIco, dif_pos ht,
    dirichletWeakFormComplOnIco, dif_pos ht]
  have hv' := (le_abs_self _).trans hv
  calc
    _ ≤ B * ‖H1ComplDirichletToLp q u‖ ^ 2 := by
      dsimp only [B, Kv]
      nlinarith
    _ ≤ B * (L * ‖smoothMulLp q φ (H1ComplDirichletToLp q u)‖) ^ 2 :=
      mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ (norm_nonneg _) (mul_nonneg hLpos.le (norm_nonneg _))).2 hnorm) hB
    _ = _ := by ring

theorem IsWeakEvolutionSolution.exists_continuous_l2_representative_with_energy_bound
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_half n) (M := M) D}
    {hG : MetricFamilySmoothOn (I := I_half n) (M := M) D G.metric}
    {T : ℝ} {hT : 0 ≤ T} {hreg : Icc (0 : ℝ) T ⊆ D.regular}
    {X : ℝ → Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯}
    (hXcont : ContinuousOn
      (fun p : ℝ × M =>
        (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2) :
          TangentBundle (I_half n) M))
      (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    {a : ℝ → ℝ} (hacont : ContinuousOn a (Icc (0 : ℝ) T))
    {Bx Bv : ℝ}
    {hX : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      (G.metric t).inner x (X t x) (X t x) ≤ Bx}
    {htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_half n) G.metric t x| ≤ Bv}
    {f₀ : Lp ℝ 2
      (riemannianVolumeMeasure (I := I_half n) (M := M) q)}
    {u : timeL2 (H1ComplDirichlet q) T}
    (hu : IsWeakEvolutionSolution hG hT hreg X a Bx Bv
      hX htrace f₀ u) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∃ U : ℝ → Lp ℝ 2
          (riemannianVolumeMeasure (I := I_half n) (M := M) q),
        ContinuousOn U (Icc (0 : ℝ) T) ∧
        (U =ᵐ[timeMeasure T] fun t => H1ComplDirichletToLp q (u t)) ∧
        U 0 = f₀ ∧
        ∀ t ∈ Icc (0 : ℝ) T,
          ‖smoothMulLp q (riemannianVolumeDensitySmoothMap q (G.metric t)) (U t)‖ ^ 2 ≤
            ‖smoothMulLp q (riemannianVolumeDensitySmoothMap q (G.metric 0)) f₀‖ ^ 2 *
              Real.exp (C * t) := by
  obtain ⟨Cg, Cv, hCg, hequiv, hCv0, hCvtop, hvol,
      U, hUcont, hUae, hUzero, henergy⟩ :=
    hu.exists_continuous_l2_representative_with_mass_energy hXcont hacont
  obtain ⟨C, hC, hbound⟩ := exists_uniform_volumeDensity_energy_bound
    hG hreg X a hacont Bx Bv hX htrace hCg hequiv Cv hCv0 hCvtop hvol
  let S : ℝ → ℝ := fun t => 2 * (
    dirichletMassVariationComplOnIco hG hreg Bv htrace
      hCg hequiv Cv hCv0 hCvtop hvol t (u t)
      (smoothMulH1ComplDirichlet q
        (riemannianVolumeDensitySmoothMap q (G.metric t)) (u t)) +
    dirichletWeakFormComplOnIco G.metric X a Bx hX
      hCg hequiv Cv hCv0 hCvtop hvol t (u t)
      (smoothMulH1ComplDirichlet q
        (riemannianVolumeDensitySmoothMap q (G.metric t)) (u t)))
  let E : ℝ → ℝ := fun t =>
    ‖smoothMulLp q (riemannianVolumeDensitySmoothMap q (G.metric t)) (U t)‖ ^ 2
  have hS : Integrable S (timeMeasure T) :=
    hu.integrable_volumeDensity_energy hXcont hacont hCg hequiv Cv hCv0 hCvtop hvol
  have hρcont : ContinuousOn
      (fun p : ℝ × M => riemannianVolumeDensity q (G.metric p.1) p.2)
      (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)) :=
    (riemannianVolumeDensity_contMDiffOn_of_metricFamilySmoothOn hG q).continuousOn.mono
      (Set.prod_mono hreg Set.Subset.rfl)
  have hEcont : ContinuousOn E (Icc (0 : ℝ) T) :=
    (continuousOn_smoothMulLp_apply q
      (fun t => riemannianVolumeDensitySmoothMap q (G.metric t)) hρcont hUcont).norm.pow 2
  have hneT : ∀ᵐ t ∂(timeMeasure T), t ≠ T :=
    ae_restrict_of_ae (ae_iff.mpr (by simp))
  have hSbound : S ≤ᵐ[timeMeasure T] fun t => C * E t := by
    filter_upwards [hUae, ae_restrict_mem measurableSet_Icc, hneT] with t hUt ht htne
    have hti : t ∈ Ico (0 : ℝ) T := ⟨ht.1, lt_of_le_of_ne ht.2 htne⟩
    simpa only [S, E, hUt] using hbound t hti (u t)
  have hEint : ∀ t ∈ Icc (0 : ℝ) T,
      E t ≤ E 0 + C * ∫ s in (0 : ℝ)..t, E s := by
    intro t ht
    have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
    have hSon : IntegrableOn S (Icc (0 : ℝ) T) volume := hS
    have hSt : IntervalIntegrable S volume 0 t :=
      (hSon.mono_set (uIcc_subset_Icc hzero ht)).intervalIntegrable
    have hCEt : IntervalIntegrable (fun t => C * E t) volume 0 t :=
      ContinuousOn.intervalIntegrable_of_Icc ht.1
        (continuousOn_const.mul (hEcont.mono (Icc_subset_Icc le_rfl ht.2)))
    have hSb := hSbound.filter_mono
      (ae_mono (Measure.restrict_mono (Icc_subset_Icc le_rfl ht.2) le_rfl))
    have hle := intervalIntegral.integral_mono_ae_restrict ht.1 hSt hCEt hSb
    rw [intervalIntegral.integral_const_mul C] at hle
    have hid : E t - E 0 = ∫ s in (0 : ℝ)..t, S s := henergy 0 t hzero ht
    linarith
  have hgronwall := DifferentialGeometry.Analysis.ODE.gronwall_integral_le hT hC hEcont hEint
  refine ⟨C, hC, U, hUcont, hUae, hUzero, fun t ht => ?_⟩
  simpa only [E, hUzero] using hgronwall t ht

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
