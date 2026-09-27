import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletFormCompletion
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.FormBounds

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal InnerProductSpace Manifold RealInnerProductSpace Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
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

private local instance smoothDualSeminormedAddCommGroup (q : SmoothRiemannianMetric (I_half n) M) :
    SeminormedAddCommGroup (SmoothScalarDirichlet q →L[ℝ] ℝ) :=
  ContinuousLinearMap.toSeminormedAddCommGroup (𝕜 := ℝ) (E := SmoothScalarDirichlet q) (F := ℝ)

private local instance smoothBilinearNorm (q : SmoothRiemannianMetric (I_half n) M) :
    Norm (SmoothScalarDirichlet q →L[ℝ] SmoothScalarDirichlet q →L[ℝ] ℝ) :=
  ContinuousLinearMap.hasOpNorm (𝕜 := ℝ) (𝕜₂ := ℝ) (σ₁₂ := RingHom.id ℝ) (E := SmoothScalarDirichlet q) (F := SmoothScalarDirichlet q →L[ℝ] ℝ)

private local instance completedDualSeminormedAddCommGroup (q : SmoothRiemannianMetric (I_half n) M) :
    SeminormedAddCommGroup (H1ComplDirichlet q →L[ℝ] ℝ) :=
  ContinuousLinearMap.toSeminormedAddCommGroup (𝕜 := ℝ) (E := H1ComplDirichlet q) (F := ℝ)

private local instance completedBilinearNorm (q : SmoothRiemannianMetric (I_half n) M) :
    Norm (H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q →L[ℝ] ℝ) :=
  ContinuousLinearMap.hasOpNorm (𝕜 := ℝ) (𝕜₂ := ℝ) (σ₁₂ := RingHom.id ℝ) (E := H1ComplDirichlet q) (F := H1ComplDirichlet q →L[ℝ] ℝ)

noncomputable def dirichletMassVariationSmooth
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
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q) :
    SmoothScalarDirichlet q →L[ℝ] SmoothScalarDirichlet q →L[ℝ] ℝ := by
  refine LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ
      (fun u v => dirichletMassVariation G.metric t u v)
      (dirichletMassVariation_add_left hG ht)
      (dirichletMassVariation_smul_left hG ht)
      (dirichletMassVariation_add_right hG ht)
      (dirichletMassVariation_smul_right hG ht))
    ((1 / 2) * max B 0 * (Cv.toReal * Cg)) ?_
  intro u v
  rw [Real.norm_eq_abs]
  exact abs_dirichletMassVariation_le_of_metric_and_volume G.metric t B htrace
    hCg hequiv Cv hCv0 hCvtop hvol u v

theorem dirichletMassVariationSmooth_apply
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
    (u v : SmoothScalarDirichlet q) :
    dirichletMassVariationSmooth hG ht B htrace hCg hequiv
        Cv hCv0 hCvtop hvol u v =
      dirichletMassVariation G.metric t u v := rfl

theorem norm_dirichletMassVariationSmooth_le
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
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q) :
    ‖dirichletMassVariationSmooth hG ht B htrace hCg hequiv
      Cv hCv0 hCvtop hvol‖ ≤
        (1 / 2) * max B 0 * (Cv.toReal * Cg) := by
  apply LinearMap.mkContinuous₂_norm_le
  exact mul_nonneg
    (mul_nonneg (by norm_num) (le_max_right B 0))
    (mul_nonneg ENNReal.toReal_nonneg (zero_le_one.trans hCg))

noncomputable def dirichletMassVariationCompl
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
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q) :
    H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q →L[ℝ] ℝ :=
  DifferentialGeometry.Analysis.bilinearFromCompletion (X := SmoothScalarDirichlet q)
    (dirichletMassVariationSmooth hG ht B htrace hCg hequiv
      Cv hCv0 hCvtop hvol)

theorem dirichletMassVariationCompl_apply_smooth
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
    (u v : SmoothScalarDirichlet q) :
    dirichletMassVariationCompl hG ht B htrace hCg hequiv
        Cv hCv0 hCvtop hvol
        (smoothToH1ComplDirichlet q u) (smoothToH1ComplDirichlet q v) =
      dirichletMassVariation G.metric t u v := by
  change DifferentialGeometry.Analysis.bilinearFromCompletion
      (dirichletMassVariationSmooth hG ht B htrace hCg hequiv Cv hCv0 hCvtop hvol)
      (u : UniformSpace.Completion (SmoothScalarDirichlet q))
      (v : UniformSpace.Completion (SmoothScalarDirichlet q)) = _
  rw [DifferentialGeometry.Analysis.bilinearFromCompletion_apply_coe,
    dirichletMassVariationSmooth_apply]

theorem norm_dirichletMassVariationCompl_le
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
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q) :
    ‖dirichletMassVariationCompl hG ht B htrace hCg hequiv
      Cv hCv0 hCvtop hvol‖ ≤
        (1 / 2) * max B 0 * (Cv.toReal * Cg) := by
  rw [dirichletMassVariationCompl]
  apply DifferentialGeometry.Analysis.norm_bilinearFromCompletion_le
  · exact mul_nonneg
      (mul_nonneg (by norm_num) (le_max_right B 0))
      (mul_nonneg ENNReal.toReal_nonneg (zero_le_one.trans hCg))
  · intro u v
    rw [dirichletMassVariationSmooth_apply, Real.norm_eq_abs]
    exact abs_dirichletMassVariation_le_of_metric_and_volume G.metric t B htrace
      hCg hequiv Cv hCv0 hCvtop hvol u v

end DifferentialGeometry.Analysis.Parabolic.Dirichlet

end
