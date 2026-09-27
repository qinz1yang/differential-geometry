import DifferentialGeometry.Analysis.DenseExtension
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletFormBounds

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

noncomputable def dirichletMassLp
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (Cv : ℝ≥0∞) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) h ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) q) →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) q) →L[ℝ] ℝ :=
  let L := Lp.LpToLpOfMeasureLeSMul (E := ℝ) (p := 2) hCvtop hvol
  (innerSL ℝ).bilinearComp L L

theorem dirichletMassLp_apply_eq_integral
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (Cv : ℝ≥0∞) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) h ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q)
    (u v : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) q)) :
    dirichletMassLp h Cv hCvtop hvol u v =
      ∫ x, u x * v x ∂(riemannianVolumeMeasure (I := I_half n) (M := M) h) := by
  rw [dirichletMassLp, ContinuousLinearMap.bilinearComp_apply, innerSL_apply_apply,
    L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_LpToLpOfMeasureLeSMul hCvtop hvol u,
    Lp.coeFn_LpToLpOfMeasureLeSMul hCvtop hvol v] with x hu hv
  rw [hu, hv, Real.inner_apply]

theorem dirichletMassLp_apply_smooth
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (Cv : ℝ≥0∞) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) h ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q)
    (u v : SmoothScalarDirichlet q) :
    dirichletMassLp h Cv hCvtop hvol
        (smoothToLpDirichlet q u) (smoothToLpDirichlet q v) =
      dirichletMass h u v := by
  rw [dirichletMassLp_apply_eq_integral]
  apply integral_congr_ae
  have hac : riemannianVolumeMeasure (I := I_half n) (M := M) h ≪
      riemannianVolumeMeasure (I := I_half n) (M := M) q :=
    Measure.absolutelyContinuous_of_le_smul hvol
  have hu : (smoothToLpDirichlet q u : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I_half n) (M := M) q] u.toFun :=
    MemLp.coeFn_toLp u.memLp_two
  have hv : (smoothToLpDirichlet q v : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I_half n) (M := M) q] v.toFun :=
    MemLp.coeFn_toLp v.memLp_two
  filter_upwards [hac.ae_eq hu, hac.ae_eq hv] with x hux hvx
  rw [hux, hvx]

theorem dirichletMassLp_self_apply
    {q : SmoothRiemannianMetric (I_half n) M}
    (Cv : ℝ≥0∞) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) q ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q)
    (u v : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) q)) :
    dirichletMassLp q Cv hCvtop hvol u v = inner ℝ u v := by
  let L := Lp.LpToLpOfMeasureLeSMul (E := ℝ) (p := 2) hCvtop hvol
  change inner ℝ (L u) (L v) = inner ℝ u v
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_LpToLpOfMeasureLeSMul hCvtop hvol u,
    Lp.coeFn_LpToLpOfMeasureLeSMul hCvtop hvol v] with x hu hv
  rw [hu, hv]

theorem dirichletMassLp_self_riesz_eq_resolventDirichlet
    {q : SmoothRiemannianMetric (I_half n) M}
    (Cv : ℝ≥0∞) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) q ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q)
    (u : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) q)) :
    (InnerProductSpace.toDual ℝ (H1ComplDirichlet q)).symm
        ((dirichletMassLp q Cv hCvtop hvol u).comp
          (H1ComplDirichletToLp q)) =
      resolventDirichlet q u := by
  apply ext_inner_right ℝ
  intro v
  rw [InnerProductSpace.toDual_symm_apply,
    ContinuousLinearMap.comp_apply,
    dirichletMassLp_self_apply,
    resolventDirichlet_inner_eq_lpFunctional,
    real_inner_comm u]

private noncomputable def dirichletExtend
    (q : SmoothRiemannianMetric (I_half n) M)
    (F : SmoothScalarDirichlet q →L[ℝ] SmoothScalarDirichlet q →L[ℝ] ℝ) :
    H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q →L[ℝ] ℝ :=
  DifferentialGeometry.Analysis.bilinearFromCompletion
    (X := SmoothScalarDirichlet q) F

private theorem dirichletExtend_apply_smooth
    (q : SmoothRiemannianMetric (I_half n) M)
    (F : SmoothScalarDirichlet q →L[ℝ] SmoothScalarDirichlet q →L[ℝ] ℝ)
    (u v : SmoothScalarDirichlet q) :
    dirichletExtend q F (smoothToH1ComplDirichlet q u)
        (smoothToH1ComplDirichlet q v) = F u v := by
  change dirichletExtend q F
      (u : UniformSpace.Completion (SmoothScalarDirichlet q))
      (v : UniformSpace.Completion (SmoothScalarDirichlet q)) = F u v
  exact DifferentialGeometry.Analysis.bilinearFromCompletion_apply_coe
    (X := SmoothScalarDirichlet q) F u v

noncomputable def dirichletMassSmooth
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ v : TangentSpace (I_half n) x,
      Cg⁻¹ * q.inner x v v ≤ h.inner x v v ∧
        h.inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) h ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q) :
    SmoothScalarDirichlet q →L[ℝ] SmoothScalarDirichlet q →L[ℝ] ℝ := by
  refine LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ
      (fun u v => dirichletMass h u v)
      (dirichletMass_add_left h)
      (dirichletMass_smul_left h)
      (dirichletMass_add_right h)
      (dirichletMass_smul_right h))
    (Cv.toReal * Cg) ?_
  intro u v
  rw [Real.norm_eq_abs]
  exact abs_dirichletMass_le_of_metric_and_volume h hCg hequiv
    Cv hCv0 hCvtop hvol u v

theorem dirichletMassSmooth_apply
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ v : TangentSpace (I_half n) x,
      Cg⁻¹ * q.inner x v v ≤ h.inner x v v ∧
        h.inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) h ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q)
    (u v : SmoothScalarDirichlet q) :
    dirichletMassSmooth h hCg hequiv Cv hCv0 hCvtop hvol u v =
      dirichletMass h u v := rfl

theorem norm_dirichletMassSmooth_le
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ v : TangentSpace (I_half n) x,
      Cg⁻¹ * q.inner x v v ≤ h.inner x v v ∧
        h.inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) h ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q) :
    ‖dirichletMassSmooth h hCg hequiv Cv hCv0 hCvtop hvol‖ ≤
      Cv.toReal * Cg := by
  apply LinearMap.mkContinuous₂_norm_le
  exact mul_nonneg ENNReal.toReal_nonneg (zero_le_one.trans hCg)

noncomputable def dirichletMassCompl
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ v : TangentSpace (I_half n) x,
      Cg⁻¹ * q.inner x v v ≤ h.inner x v v ∧
        h.inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) h ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q) :
    H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q →L[ℝ] ℝ :=
  dirichletExtend q
    (dirichletMassSmooth h hCg hequiv Cv hCv0 hCvtop hvol)

theorem dirichletMassCompl_apply_smooth
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ v : TangentSpace (I_half n) x,
      Cg⁻¹ * q.inner x v v ≤ h.inner x v v ∧
        h.inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) h ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q)
    (u v : SmoothScalarDirichlet q) :
    dirichletMassCompl h hCg hequiv Cv hCv0 hCvtop hvol
        (smoothToH1ComplDirichlet q u) (smoothToH1ComplDirichlet q v) =
      dirichletMass h u v := by
  rw [dirichletMassCompl, dirichletExtend_apply_smooth,
    dirichletMassSmooth_apply]

theorem dirichletMassCompl_self_apply
    {q : SmoothRiemannianMetric (I_half n) M}
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ v : TangentSpace (I_half n) x,
      Cg⁻¹ * q.inner x v v ≤ q.inner x v v ∧
        q.inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) q ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q)
    (u v : H1ComplDirichlet q) :
    dirichletMassCompl q hCg hequiv Cv hCv0 hCvtop hvol u v =
      inner ℝ (H1ComplDirichletToLp q u) (H1ComplDirichletToLp q v) := by
  let mass := dirichletMassCompl q hCg hequiv Cv hCv0 hCvtop hvol
  have hsmooth (u₀ : SmoothScalarDirichlet q) :
      (fun v => mass (smoothToH1ComplDirichlet q u₀) v) =
        fun v => inner ℝ (H1ComplDirichletToLp q
          (smoothToH1ComplDirichlet q u₀))
          (H1ComplDirichletToLp q v) := by
    apply DenseRange.equalizer (denseRange_smoothToH1ComplDirichlet q)
      (mass (smoothToH1ComplDirichlet q u₀)).continuous
      (continuous_const.inner (H1ComplDirichletToLp q).continuous)
    funext v₀
    simp only [Function.comp_apply]
    dsimp only [mass]
    rw [H1ComplDirichletToLp_smoothToH1ComplDirichlet,
      H1ComplDirichletToLp_smoothToH1ComplDirichlet,
      dirichletMassCompl_apply_smooth, MeasureTheory.L2.inner_def]
    unfold dirichletMass
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp u₀.memLp_two,
      MemLp.coeFn_toLp v₀.memLp_two] with x hu hv
    rw [smoothToLpDirichlet,
      DifferentialGeometry.Analysis.Laplacian.WithBoundary.smoothToLpInterior_apply q u₀,
      DifferentialGeometry.Analysis.Laplacian.WithBoundary.smoothToLpInterior_apply q v₀,
      hu, hv]
    simp only [RCLike.inner_apply, conj_trivial, mul_comm]
  have hall : (fun u => mass u v) =
      fun u => inner ℝ (H1ComplDirichletToLp q u)
        (H1ComplDirichletToLp q v) := by
    apply DenseRange.equalizer (denseRange_smoothToH1ComplDirichlet q)
      (mass.flip v).continuous
      ((H1ComplDirichletToLp q).continuous.inner continuous_const)
    funext u₀
    exact congrFun (hsmooth u₀) v
  exact congrFun hall u

theorem dirichletMassCompl_self_riesz_eq_resolventDirichlet
    {q : SmoothRiemannianMetric (I_half n) M}
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ v : TangentSpace (I_half n) x,
      Cg⁻¹ * q.inner x v v ≤ q.inner x v v ∧
        q.inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) q ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q)
    (u : H1ComplDirichlet q) :
    (InnerProductSpace.toDual ℝ (H1ComplDirichlet q)).symm
        (dirichletMassCompl q hCg hequiv Cv hCv0 hCvtop hvol u) =
      resolventDirichlet q (H1ComplDirichletToLp q u) := by
  apply ext_inner_right ℝ
  intro v
  rw [InnerProductSpace.toDual_symm_apply,
    dirichletMassCompl_self_apply,
    resolventDirichlet_inner_eq_lpFunctional,
    real_inner_comm (H1ComplDirichletToLp q u)]

theorem norm_dirichletMassCompl_le
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ v : TangentSpace (I_half n) x,
      Cg⁻¹ * q.inner x v v ≤ h.inner x v v ∧
        h.inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) h ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q) :
    ‖dirichletMassCompl h hCg hequiv Cv hCv0 hCvtop hvol‖ ≤
      Cv.toReal * Cg := by
  rw [dirichletMassCompl, dirichletExtend]
  apply DifferentialGeometry.Analysis.norm_bilinearFromCompletion_le
  · exact mul_nonneg ENNReal.toReal_nonneg (zero_le_one.trans hCg)
  · intro u v
    rw [dirichletMassSmooth_apply, Real.norm_eq_abs]
    exact abs_dirichletMass_le_of_metric_and_volume h hCg hequiv
      Cv hCv0 hCvtop hvol u v

noncomputable def dirichletWeakFormSmooth
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (X : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a B : ℝ) (hX : ∀ x : M, h.inner x (X x) (X x) ≤ B)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ v : TangentSpace (I_half n) x,
      Cg⁻¹ * q.inner x v v ≤ h.inner x v v ∧
        h.inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) h ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q) :
    SmoothScalarDirichlet q →L[ℝ] SmoothScalarDirichlet q →L[ℝ] ℝ := by
  refine LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ
      (fun u v => dirichletWeakForm h X a u v)
      (dirichletWeakForm_add_left h X a)
      (dirichletWeakForm_smul_left h X a)
      (dirichletWeakForm_add_right h X a)
      (dirichletWeakForm_smul_right h X a))
    ((1 + Real.sqrt (max B 0) + |a|) * (Cv.toReal * Cg)) ?_
  intro u v
  rw [Real.norm_eq_abs]
  exact abs_dirichletWeakForm_le_of_metric_and_volume h X a B hX
    hCg hequiv Cv hCv0 hCvtop hvol u v

theorem dirichletWeakFormSmooth_apply
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (X : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a B : ℝ) (hX : ∀ x : M, h.inner x (X x) (X x) ≤ B)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ v : TangentSpace (I_half n) x,
      Cg⁻¹ * q.inner x v v ≤ h.inner x v v ∧
        h.inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) h ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q)
    (u v : SmoothScalarDirichlet q) :
    dirichletWeakFormSmooth h X a B hX hCg hequiv Cv hCv0 hCvtop hvol u v =
      dirichletWeakForm h X a u v := rfl

theorem norm_dirichletWeakFormSmooth_le
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (X : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a B : ℝ) (hX : ∀ x : M, h.inner x (X x) (X x) ≤ B)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ v : TangentSpace (I_half n) x,
      Cg⁻¹ * q.inner x v v ≤ h.inner x v v ∧
        h.inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) h ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q) :
    ‖dirichletWeakFormSmooth h X a B hX hCg hequiv Cv hCv0 hCvtop hvol‖ ≤
      (1 + Real.sqrt (max B 0) + |a|) * (Cv.toReal * Cg) := by
  apply LinearMap.mkContinuous₂_norm_le
  exact mul_nonneg
    (add_nonneg
      (add_nonneg zero_le_one (Real.sqrt_nonneg (max B 0))) (abs_nonneg a))
    (mul_nonneg ENNReal.toReal_nonneg (zero_le_one.trans hCg))

noncomputable def dirichletWeakFormCompl
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (X : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a B : ℝ) (hX : ∀ x : M, h.inner x (X x) (X x) ≤ B)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ v : TangentSpace (I_half n) x,
      Cg⁻¹ * q.inner x v v ≤ h.inner x v v ∧
        h.inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) h ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q) :
    H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q →L[ℝ] ℝ :=
  dirichletExtend q
    (dirichletWeakFormSmooth h X a B hX hCg hequiv Cv hCv0 hCvtop hvol)

theorem dirichletWeakFormCompl_apply_smooth
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (X : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a B : ℝ) (hX : ∀ x : M, h.inner x (X x) (X x) ≤ B)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ v : TangentSpace (I_half n) x,
      Cg⁻¹ * q.inner x v v ≤ h.inner x v v ∧
        h.inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) h ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q)
    (u v : SmoothScalarDirichlet q) :
    dirichletWeakFormCompl h X a B hX hCg hequiv Cv hCv0 hCvtop hvol
        (smoothToH1ComplDirichlet q u) (smoothToH1ComplDirichlet q v) =
      dirichletWeakForm h X a u v := by
  rw [dirichletWeakFormCompl, dirichletExtend_apply_smooth,
    dirichletWeakFormSmooth_apply]

theorem norm_dirichletWeakFormCompl_le
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (X : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a B : ℝ) (hX : ∀ x : M, h.inner x (X x) (X x) ≤ B)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ v : TangentSpace (I_half n) x,
      Cg⁻¹ * q.inner x v v ≤ h.inner x v v ∧
        h.inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) h ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q) :
    ‖dirichletWeakFormCompl h X a B hX hCg hequiv Cv hCv0 hCvtop hvol‖ ≤
      (1 + Real.sqrt (max B 0) + |a|) * (Cv.toReal * Cg) := by
  rw [dirichletWeakFormCompl, dirichletExtend]
  apply DifferentialGeometry.Analysis.norm_bilinearFromCompletion_le
  · exact mul_nonneg
      (add_nonneg
        (add_nonneg zero_le_one (Real.sqrt_nonneg (max B 0))) (abs_nonneg a))
      (mul_nonneg ENNReal.toReal_nonneg (zero_le_one.trans hCg))
  · intro u v
    rw [dirichletWeakFormSmooth_apply, Real.norm_eq_abs]
    exact abs_dirichletWeakForm_le_of_metric_and_volume h X a B hX
      hCg hequiv Cv hCv0 hCvtop hvol u v

end DifferentialGeometry.Analysis.Parabolic.Dirichlet

end

noncomputable section

open Manifold MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Manifold RealInnerProductSpace Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary
open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem dirichletWeakFormCompl_self_zero_apply
    (q : SmoothRiemannianMetric I_hs M)
    (B : ℝ) (hX : ∀ x : M, q.inner x (0 : TangentSpace I_hs x) 0 ≤ B)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ v : TangentSpace I_hs x,
      Cg⁻¹ * q.inner x v v ≤ q.inner x v v ∧
        q.inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_hs) (M := M) q ≤
      Cv • riemannianVolumeMeasure (I := I_hs) (M := M) q)
    (u v : H1ComplDirichlet q) :
    dirichletWeakFormCompl q 0 0 B hX hCg hequiv Cv hCv0 hCvtop hvol u v =
      ⟪H1ComplDirichletToLp q u, H1ComplDirichletToLp q v⟫_ℝ - ⟪u, v⟫_ℝ := by
  let F := dirichletWeakFormCompl q 0 0 B hX hCg hequiv Cv hCv0 hCvtop hvol
  have hsmooth (u₀ : SmoothScalarDirichlet q) :
      (fun v => F (smoothToH1ComplDirichlet q u₀) v) =
        fun v => ⟪H1ComplDirichletToLp q (smoothToH1ComplDirichlet q u₀),
          H1ComplDirichletToLp q v⟫_ℝ - ⟪smoothToH1ComplDirichlet q u₀, v⟫_ℝ := by
    apply DenseRange.equalizer (denseRange_smoothToH1ComplDirichlet q)
      (F (smoothToH1ComplDirichlet q u₀)).continuous
      ((continuous_const.inner (H1ComplDirichletToLp q).continuous).sub
        (continuous_const.inner continuous_id))
    funext v₀
    simp only [Function.comp_apply, Pi.sub_apply, id_eq]
    dsimp only [F]
    rw [dirichletWeakFormCompl_apply_smooth,
      H1ComplDirichletToLp_smoothToH1ComplDirichlet,
      H1ComplDirichletToLp_smoothToH1ComplDirichlet]
    have hm := dirichletMassLp_apply_smooth q Cv hCvtop hvol u₀ v₀
    rw [dirichletMassLp_self_apply] at hm
    rw [hm]
    have hi : ⟪smoothToH1ComplDirichlet q u₀,
        smoothToH1ComplDirichlet q v₀⟫_ℝ = interiorSmoothScalarH1Inner u₀ v₀ :=
      inner_smoothToH1ComplInterior_smoothToH1ComplInterior u₀ v₀
    rw [hi]
    simp [dirichletWeakForm, dirichletDrift, dirichletMass, dirichletEnergy,
      interiorSmoothScalarH1Inner]
  have hall : (fun u => F u v) = fun u =>
      ⟪H1ComplDirichletToLp q u, H1ComplDirichletToLp q v⟫_ℝ - ⟪u, v⟫_ℝ := by
    apply DenseRange.equalizer (denseRange_smoothToH1ComplDirichlet q)
      (F.flip v).continuous
      (((H1ComplDirichletToLp q).continuous.inner continuous_const).sub
        (continuous_id.inner continuous_const))
    funext u₀
    exact congrFun (hsmooth u₀) v
  exact congrFun hall u

end DifferentialGeometry.Analysis.Parabolic.Dirichlet

end
