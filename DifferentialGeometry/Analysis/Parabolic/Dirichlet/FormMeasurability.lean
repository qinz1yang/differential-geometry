import DifferentialGeometry.Analysis.Parabolic.Dirichlet.FormCompletion
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.BochnerL2

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal InnerProductSpace Manifold RealInnerProductSpace Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
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

noncomputable def dirichletMassComplOnIcc
    {q : SmoothRiemannianMetric (I_half n) M}
    (g : ℝ → SmoothRiemannianMetric (I_half n) M)
    {T Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      ∀ v : TangentSpace (I_half n) x,
        Cg⁻¹ * q.inner x v v ≤ (g t).inner x v v ∧
          (g t).inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : ∀ t ∈ Icc (0 : ℝ) T,
      riemannianVolumeMeasure (I := I_half n) (M := M) (g t) ≤
        Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q) :
    ℝ → H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q →L[ℝ] ℝ :=
  fun t ↦ if ht : t ∈ Icc (0 : ℝ) T then
    dirichletMassCompl (g t) hCg (hequiv t ht) Cv hCv0 hCvtop (hvol t ht)
  else 0

theorem dirichletMassComplOnIcc_apply_smooth
    {q : SmoothRiemannianMetric (I_half n) M}
    (g : ℝ → SmoothRiemannianMetric (I_half n) M)
    {T Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      ∀ v : TangentSpace (I_half n) x,
        Cg⁻¹ * q.inner x v v ≤ (g t).inner x v v ∧
          (g t).inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : ∀ t ∈ Icc (0 : ℝ) T,
      riemannianVolumeMeasure (I := I_half n) (M := M) (g t) ≤
        Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (u v : SmoothScalarDirichlet q) :
    dirichletMassComplOnIcc g hCg hequiv Cv hCv0 hCvtop hvol t
        (smoothToH1ComplDirichlet q u) (smoothToH1ComplDirichlet q v) =
      dirichletMass (g t) u v := by
  rw [dirichletMassComplOnIcc, dif_pos ht,
    dirichletMassCompl_apply_smooth]

theorem norm_dirichletMassComplOnIcc_le
    {q : SmoothRiemannianMetric (I_half n) M}
    (g : ℝ → SmoothRiemannianMetric (I_half n) M)
    {T Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      ∀ v : TangentSpace (I_half n) x,
        Cg⁻¹ * q.inner x v v ≤ (g t).inner x v v ∧
          (g t).inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : ∀ t ∈ Icc (0 : ℝ) T,
      riemannianVolumeMeasure (I := I_half n) (M := M) (g t) ≤
        Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q)
    (t : ℝ) :
    ‖dirichletMassComplOnIcc g hCg hequiv Cv hCv0 hCvtop hvol t‖ ≤
      Cv.toReal * Cg := by
  by_cases ht : t ∈ Icc (0 : ℝ) T
  · rw [dirichletMassComplOnIcc, dif_pos ht]
    exact norm_dirichletMassCompl_le (g t) hCg (hequiv t ht)
      Cv hCv0 hCvtop (hvol t ht)
  · rw [dirichletMassComplOnIcc, dif_neg ht, norm_zero]
    exact mul_nonneg ENNReal.toReal_nonneg (zero_le_one.trans hCg)

theorem dirichletMassComplOnIcc_aestronglyMeasurable
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_half n) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_half n) (M := M) D G.metric)
    {T Cg : ℝ} (hreg : Icc (0 : ℝ) T ⊆ D.regular)
    (hCg : 1 ≤ Cg)
    (hequiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      ∀ v : TangentSpace (I_half n) x,
        Cg⁻¹ * q.inner x v v ≤ (G.metric t).inner x v v ∧
          (G.metric t).inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : ∀ t ∈ Icc (0 : ℝ) T,
      riemannianVolumeMeasure (I := I_half n) (M := M) (G.metric t) ≤
        Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q)
    (u v : H1ComplDirichlet q) :
    AEStronglyMeasurable
      (fun t ↦ dirichletMassComplOnIcc G.metric hCg hequiv
        Cv hCv0 hCvtop hvol t u v) (timeMeasure T) := by
  apply AEStronglyMeasurable.clm_apply₂_of_denseRange
    (denseRange_smoothToH1ComplDirichlet q)
    (denseRange_smoothToH1ComplDirichlet q)
  intro u₀ v₀
  unfold timeMeasure
  have hraw := dirichletMass_time_cont G.metric isCompact_Icc
    (fun x₀ i j ↦ hG.chartGramMatrix_continuousOn hreg x₀ i j) u₀ v₀
  refine (hraw.aestronglyMeasurable measurableSet_Icc).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact (dirichletMassComplOnIcc_apply_smooth G.metric hCg hequiv
    Cv hCv0 hCvtop hvol ht u₀ v₀).symm

noncomputable def dirichletMassVariationComplOnIco
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_half n) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_half n) (M := M) D G.metric)
    {T : ℝ} (hreg : Icc (0 : ℝ) T ⊆ D.regular)
    (B : ℝ)
    (htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_half n) G.metric t x| ≤ B)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      ∀ v : TangentSpace (I_half n) x,
        Cg⁻¹ * q.inner x v v ≤ (G.metric t).inner x v v ∧
          (G.metric t).inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : ∀ t ∈ Icc (0 : ℝ) T,
      riemannianVolumeMeasure (I := I_half n) (M := M) (G.metric t) ≤
        Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q) :
    ℝ → H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q →L[ℝ] ℝ :=
  fun t ↦ if ht : t ∈ Ico (0 : ℝ) T then
    dirichletMassVariationCompl hG (hreg ⟨ht.1, ht.2.le⟩) B
      (htrace t ht) hCg (hequiv t ⟨ht.1, ht.2.le⟩)
      Cv hCv0 hCvtop (hvol t ⟨ht.1, ht.2.le⟩)
  else 0

theorem dirichletMassVariationComplOnIco_apply_smooth
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_half n) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_half n) (M := M) D G.metric)
    {T : ℝ} (hreg : Icc (0 : ℝ) T ⊆ D.regular)
    (B : ℝ)
    (htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_half n) G.metric t x| ≤ B)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      ∀ v : TangentSpace (I_half n) x,
        Cg⁻¹ * q.inner x v v ≤ (G.metric t).inner x v v ∧
          (G.metric t).inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : ∀ t ∈ Icc (0 : ℝ) T,
      riemannianVolumeMeasure (I := I_half n) (M := M) (G.metric t) ≤
        Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T)
    (u v : SmoothScalarDirichlet q) :
    dirichletMassVariationComplOnIco hG hreg B htrace hCg hequiv
        Cv hCv0 hCvtop hvol t
        (smoothToH1ComplDirichlet q u) (smoothToH1ComplDirichlet q v) =
      dirichletMassVariation G.metric t u v := by
  rw [dirichletMassVariationComplOnIco, dif_pos ht,
    dirichletMassVariationCompl_apply_smooth]

theorem norm_dirichletMassVariationComplOnIco_le
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_half n) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_half n) (M := M) D G.metric)
    {T : ℝ} (hreg : Icc (0 : ℝ) T ⊆ D.regular)
    (B : ℝ)
    (htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_half n) G.metric t x| ≤ B)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      ∀ v : TangentSpace (I_half n) x,
        Cg⁻¹ * q.inner x v v ≤ (G.metric t).inner x v v ∧
          (G.metric t).inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : ∀ t ∈ Icc (0 : ℝ) T,
      riemannianVolumeMeasure (I := I_half n) (M := M) (G.metric t) ≤
        Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q)
    (t : ℝ) :
    ‖dirichletMassVariationComplOnIco hG hreg B htrace hCg hequiv
      Cv hCv0 hCvtop hvol t‖ ≤
        (1 / 2) * max B 0 * (Cv.toReal * Cg) := by
  by_cases ht : t ∈ Ico (0 : ℝ) T
  · rw [dirichletMassVariationComplOnIco, dif_pos ht]
    exact norm_dirichletMassVariationCompl_le hG
      (hreg ⟨ht.1, ht.2.le⟩) B (htrace t ht) hCg
      (hequiv t ⟨ht.1, ht.2.le⟩) Cv hCv0 hCvtop
      (hvol t ⟨ht.1, ht.2.le⟩)
  · rw [dirichletMassVariationComplOnIco, dif_neg ht, norm_zero]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (le_max_right B 0))
      (mul_nonneg ENNReal.toReal_nonneg (zero_le_one.trans hCg))

theorem dirichletMassVariationComplOnIco_aestronglyMeasurable
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_half n) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_half n) (M := M) D G.metric)
    {T : ℝ} (hreg : Icc (0 : ℝ) T ⊆ D.regular)
    (B : ℝ)
    (htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_half n) G.metric t x| ≤ B)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      ∀ v : TangentSpace (I_half n) x,
        Cg⁻¹ * q.inner x v v ≤ (G.metric t).inner x v v ∧
          (G.metric t).inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : ∀ t ∈ Icc (0 : ℝ) T,
      riemannianVolumeMeasure (I := I_half n) (M := M) (G.metric t) ≤
        Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q)
    (u v : H1ComplDirichlet q) :
    AEStronglyMeasurable
      (fun t ↦ dirichletMassVariationComplOnIco hG hreg B htrace
        hCg hequiv Cv hCv0 hCvtop hvol t u v) (timeMeasure T) := by
  apply AEStronglyMeasurable.clm_apply₂_of_denseRange
    (denseRange_smoothToH1ComplDirichlet q)
    (denseRange_smoothToH1ComplDirichlet q)
  intro u₀ v₀
  unfold timeMeasure
  have hIco : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)),
      t ∈ Ico (0 : ℝ) T := by
    refine (ae_restrict_iff' measurableSet_Icc).2 ?_
    filter_upwards [(Ico_ae_eq_Icc :
      Ico (0 : ℝ) T =ᵐ[volume] Icc (0 : ℝ) T)] with t ht
    intro htIcc
    exact Eq.mpr ht htIcc
  let f : ℝ → ℝ := fun t ↦ dirichletMass (G.metric t) u₀ v₀
  refine (aestronglyMeasurable_deriv f
    (volume.restrict (Icc (0 : ℝ) T))).congr ?_
  filter_upwards [hIco] with t ht
  have hderiv := (hasDerivAt_dirichletMass hG
    (hreg ⟨ht.1, ht.2.le⟩) u₀ v₀).deriv
  rw [show deriv f t = dirichletMassVariation G.metric t u₀ v₀ from hderiv]
  exact (dirichletMassVariationComplOnIco_apply_smooth hG hreg B htrace
    hCg hequiv Cv hCv0 hCvtop hvol ht u₀ v₀).symm

noncomputable def dirichletWeakFormComplOnIco
    {q : SmoothRiemannianMetric (I_half n) M}
    (g : ℝ → SmoothRiemannianMetric (I_half n) M)
    {T : ℝ}
    (X : ℝ → Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a : ℝ → ℝ) (B : ℝ)
    (hX : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      (g t).inner x (X t x) (X t x) ≤ B)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      ∀ v : TangentSpace (I_half n) x,
        Cg⁻¹ * q.inner x v v ≤ (g t).inner x v v ∧
          (g t).inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : ∀ t ∈ Icc (0 : ℝ) T,
      riemannianVolumeMeasure (I := I_half n) (M := M) (g t) ≤
        Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q) :
    ℝ → H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q →L[ℝ] ℝ :=
  fun t ↦ if ht : t ∈ Ico (0 : ℝ) T then
    dirichletWeakFormCompl (g t) (X t) (a t) B (hX t ht)
      hCg (hequiv t ⟨ht.1, ht.2.le⟩) Cv hCv0 hCvtop
      (hvol t ⟨ht.1, ht.2.le⟩)
  else 0

theorem dirichletWeakFormComplOnIco_apply_smooth
    {q : SmoothRiemannianMetric (I_half n) M}
    (g : ℝ → SmoothRiemannianMetric (I_half n) M)
    {T : ℝ}
    (X : ℝ → Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a : ℝ → ℝ) (B : ℝ)
    (hX : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      (g t).inner x (X t x) (X t x) ≤ B)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      ∀ v : TangentSpace (I_half n) x,
        Cg⁻¹ * q.inner x v v ≤ (g t).inner x v v ∧
          (g t).inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : ∀ t ∈ Icc (0 : ℝ) T,
      riemannianVolumeMeasure (I := I_half n) (M := M) (g t) ≤
        Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T)
    (u v : SmoothScalarDirichlet q) :
    dirichletWeakFormComplOnIco g X a B hX hCg hequiv
        Cv hCv0 hCvtop hvol t
        (smoothToH1ComplDirichlet q u) (smoothToH1ComplDirichlet q v) =
      dirichletWeakForm (g t) (X t) (a t) u v := by
  rw [dirichletWeakFormComplOnIco, dif_pos ht,
    dirichletWeakFormCompl_apply_smooth]

theorem norm_dirichletWeakFormComplOnIco_le
    {q : SmoothRiemannianMetric (I_half n) M}
    (g : ℝ → SmoothRiemannianMetric (I_half n) M)
    {T : ℝ}
    (X : ℝ → Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a : ℝ → ℝ) (A B : ℝ)
    (hA : 0 ≤ A)
    (ha : ∀ t ∈ Ico (0 : ℝ) T, |a t| ≤ A)
    (hX : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      (g t).inner x (X t x) (X t x) ≤ B)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      ∀ v : TangentSpace (I_half n) x,
        Cg⁻¹ * q.inner x v v ≤ (g t).inner x v v ∧
          (g t).inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : ∀ t ∈ Icc (0 : ℝ) T,
      riemannianVolumeMeasure (I := I_half n) (M := M) (g t) ≤
        Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q)
    (t : ℝ) :
    ‖dirichletWeakFormComplOnIco g X a B hX hCg hequiv
      Cv hCv0 hCvtop hvol t‖ ≤
        (1 + Real.sqrt (max B 0) + A) * (Cv.toReal * Cg) := by
  by_cases ht : t ∈ Ico (0 : ℝ) T
  · rw [dirichletWeakFormComplOnIco, dif_pos ht]
    exact (norm_dirichletWeakFormCompl_le (g t) (X t) (a t) B
      (hX t ht) hCg (hequiv t ⟨ht.1, ht.2.le⟩)
      Cv hCv0 hCvtop (hvol t ⟨ht.1, ht.2.le⟩)).trans (by
        gcongr
        exact ha t ht)
  · rw [dirichletWeakFormComplOnIco, dif_neg ht, norm_zero]
    exact mul_nonneg
      (add_nonneg
        (add_nonneg zero_le_one (Real.sqrt_nonneg (max B 0)))
        hA)
      (mul_nonneg ENNReal.toReal_nonneg (zero_le_one.trans hCg))

theorem dirichletWeakFormComplOnIco_aestronglyMeasurable
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_half n) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_half n) (M := M) D G.metric)
    {T : ℝ} (hreg : Icc (0 : ℝ) T ⊆ D.regular)
    (X : ℝ → Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (hXcont : ContinuousOn
      (fun p : ℝ × M ↦
        (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2) :
          TangentBundle (I_half n) M))
      (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    (a : ℝ → ℝ) (hacont : ContinuousOn a (Icc (0 : ℝ) T))
    (B : ℝ)
    (hX : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      (G.metric t).inner x (X t x) (X t x) ≤ B)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      ∀ v : TangentSpace (I_half n) x,
        Cg⁻¹ * q.inner x v v ≤ (G.metric t).inner x v v ∧
          (G.metric t).inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : ∀ t ∈ Icc (0 : ℝ) T,
      riemannianVolumeMeasure (I := I_half n) (M := M) (G.metric t) ≤
        Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q)
    (u v : H1ComplDirichlet q) :
    AEStronglyMeasurable
      (fun t ↦ dirichletWeakFormComplOnIco G.metric X a B hX
        hCg hequiv Cv hCv0 hCvtop hvol t u v) (timeMeasure T) := by
  apply AEStronglyMeasurable.clm_apply₂_of_denseRange
    (denseRange_smoothToH1ComplDirichlet q)
    (denseRange_smoothToH1ComplDirichlet q)
  intro u₀ v₀
  unfold timeMeasure
  have hIco : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)),
      t ∈ Ico (0 : ℝ) T := by
    refine (ae_restrict_iff' measurableSet_Icc).2 ?_
    filter_upwards [(Ico_ae_eq_Icc :
      Ico (0 : ℝ) T =ᵐ[volume] Icc (0 : ℝ) T)] with t ht
    intro htIcc
    exact Eq.mpr ht htIcc
  have hraw := dirichletWeakForm_time_cont hG isCompact_Icc hreg
    X hXcont a hacont u₀ v₀
  refine (hraw.aestronglyMeasurable measurableSet_Icc).congr ?_
  filter_upwards [hIco] with t ht
  exact (dirichletWeakFormComplOnIco_apply_smooth G.metric X a B hX
    hCg hequiv Cv hCv0 hCvtop hvol ht u₀ v₀).symm

end DifferentialGeometry.Analysis.Parabolic.Dirichlet

end
