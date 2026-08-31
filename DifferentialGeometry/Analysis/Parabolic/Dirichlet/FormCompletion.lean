import DifferentialGeometry.Analysis.DenseExtension
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletSmoothMul
import DifferentialGeometry.Analysis.Integration.Measure.VolumeDensity
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.FormBounds
import DifferentialGeometry.Analysis.Sobolev.DirichletHs.EnergyDuality

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal InnerProductSpace Manifold RealInnerProductSpace Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Laplacian.WithBoundary
open DifferentialGeometry.Analysis.Sobolev.Hs
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

private local instance smoothScalarDirichletBilinearSeminormed
    {q : SmoothRiemannianMetric (I_half n) M} :
    SeminormedAddCommGroup
      (SmoothScalarDirichlet q →L[ℝ] SmoothScalarDirichlet q →L[ℝ] ℝ) :=
  @ContinuousLinearMap.toSeminormedAddCommGroup ℝ ℝ
    (SmoothScalarDirichlet q) (SmoothScalarDirichlet q →L[ℝ] ℝ)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (RingHom.id ℝ) inferInstance

private local instance h1ComplDirichletBilinearSeminormed
    {q : SmoothRiemannianMetric (I_half n) M} :
    SeminormedAddCommGroup
      (H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q →L[ℝ] ℝ) :=
  @ContinuousLinearMap.toSeminormedAddCommGroup ℝ ℝ
    (H1ComplDirichlet q) (H1ComplDirichlet q →L[ℝ] ℝ)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (RingHom.id ℝ) inferInstance

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
  let μq := riemannianVolumeMeasure (I := I_half n) (M := M) q
  let μh := riemannianVolumeMeasure (I := I_half n) (M := M) h
  let L := Lp.LpToLpOfMeasureLeSMul (E := ℝ) (p := 2) hCvtop hvol
  change inner ℝ (L (smoothToLpDirichlet q u))
      (L (smoothToLpDirichlet q v)) = dirichletMass h u v
  rw [MeasureTheory.L2.inner_def]
  unfold dirichletMass
  refine integral_congr_ae ?_
  have hac : μh ≪ μq := Measure.absolutelyContinuous_of_le_smul hvol
  have huq : smoothToLpDirichlet q u =ᵐ[μq] u.toFun :=
    MemLp.coeFn_toLp u.memLp_two
  have hvq : smoothToLpDirichlet q v =ᵐ[μq] v.toFun :=
    MemLp.coeFn_toLp v.memLp_two
  filter_upwards [Lp.coeFn_LpToLpOfMeasureLeSMul hCvtop hvol
      (smoothToLpDirichlet q u),
    Lp.coeFn_LpToLpOfMeasureLeSMul hCvtop hvol
      (smoothToLpDirichlet q v), hac.ae_eq huq, hac.ae_eq hvq] with x huL hvL hu hv
  rw [huL, hvL, hu, hv]
  simp only [RCLike.inner_apply, conj_trivial, mul_comm]

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

noncomputable def dirichletEnergySmooth
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
      (fun u v => dirichletEnergy h u v)
      (dirichletEnergy_add_left h)
      (dirichletEnergy_smul_left h)
      (dirichletEnergy_add_right h)
      (dirichletEnergy_smul_right h))
    (Cv.toReal * Cg) ?_
  intro u v
  rw [Real.norm_eq_abs]
  have hzero : ∀ x : M,
      h.inner x
        ((0 : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
          (TangentSpace (I_half n) : M → Type _)⟯) x)
        ((0 : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
          (TangentSpace (I_half n) : M → Type _)⟯) x) ≤ 0 := by
    intro x
    simp
  have hbound := abs_dirichletWeakForm_le_of_metric_and_volume
    h 0 0 0 hzero hCg hequiv Cv hCv0 hCvtop hvol u v
  simpa [dirichletWeakForm, dirichletDrift] using hbound

theorem dirichletEnergySmooth_apply
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
    dirichletEnergySmooth h hCg hequiv Cv hCv0 hCvtop hvol u v =
      dirichletEnergy h u v := rfl

theorem norm_dirichletEnergySmooth_le
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ v : TangentSpace (I_half n) x,
      Cg⁻¹ * q.inner x v v ≤ h.inner x v v ∧
        h.inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) h ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q) :
    ‖dirichletEnergySmooth h hCg hequiv Cv hCv0 hCvtop hvol‖ ≤
      Cv.toReal * Cg := by
  apply LinearMap.mkContinuous₂_norm_le
  exact mul_nonneg ENNReal.toReal_nonneg (zero_le_one.trans hCg)

noncomputable def dirichletEnergyCompl
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
    (dirichletEnergySmooth h hCg hequiv Cv hCv0 hCvtop hvol)

theorem dirichletEnergyCompl_apply_smooth
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
    dirichletEnergyCompl h hCg hequiv Cv hCv0 hCvtop hvol
        (smoothToH1ComplDirichlet q u) (smoothToH1ComplDirichlet q v) =
      dirichletEnergy h u v := by
  rw [dirichletEnergyCompl, dirichletExtend_apply_smooth,
    dirichletEnergySmooth_apply]

theorem norm_dirichletEnergyCompl_le
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ v : TangentSpace (I_half n) x,
      Cg⁻¹ * q.inner x v v ≤ h.inner x v v ∧
        h.inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) h ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q) :
    ‖dirichletEnergyCompl h hCg hequiv Cv hCv0 hCvtop hvol‖ ≤
      Cv.toReal * Cg := by
  rw [dirichletEnergyCompl, dirichletExtend]
  apply DifferentialGeometry.Analysis.norm_bilinearFromCompletion_le
  · exact mul_nonneg ENNReal.toReal_nonneg (zero_le_one.trans hCg)
  · intro u v
    rw [dirichletEnergySmooth_apply, Real.norm_eq_abs]
    have hzero : ∀ x : M,
        h.inner x
          ((0 : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
            (TangentSpace (I_half n) : M → Type _)⟯) x)
          ((0 : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
            (TangentSpace (I_half n) : M → Type _)⟯) x) ≤ 0 := by
      intro x
      simp
    have hbound := abs_dirichletWeakForm_le_of_metric_and_volume
      h 0 0 0 hzero hCg hequiv Cv hCv0 hCvtop hvol u v
    simpa [dirichletWeakForm, dirichletDrift] using hbound

noncomputable def dirichletFixedVolumeEnergyCompl
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
  (dirichletEnergyCompl h hCg hequiv Cv hCv0 hCvtop hvol).bilinearComp
    (ContinuousLinearMap.id ℝ (H1ComplDirichlet q))
    (smoothMulH1ComplDirichlet q (riemannianVolumeDensitySmoothMap h q))

@[simp] theorem dirichletFixedVolumeEnergyCompl_apply
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ v : TangentSpace (I_half n) x,
      Cg⁻¹ * q.inner x v v ≤ h.inner x v v ∧
        h.inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) h ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q)
    (u v : H1ComplDirichlet q) :
    dirichletFixedVolumeEnergyCompl h hCg hequiv Cv hCv0 hCvtop hvol u v =
      dirichletEnergyCompl h hCg hequiv Cv hCv0 hCvtop hvol u
        (smoothMulH1ComplDirichlet q
          (riemannianVolumeDensitySmoothMap h q) v) := rfl

theorem dirichletFixedVolumeEnergyCompl_apply_smooth
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
    dirichletFixedVolumeEnergyCompl h hCg hequiv Cv hCv0 hCvtop hvol
        (smoothToH1ComplDirichlet q u) (smoothToH1ComplDirichlet q v) =
      dirichletEnergy h u
        (smoothScalarDirichletMul q (riemannianVolumeDensitySmoothMap h q) v) := by
  rw [dirichletFixedVolumeEnergyCompl_apply,
    smoothMulH1ComplDirichlet_smoothToH1ComplDirichlet,
    dirichletEnergyCompl_apply_smooth]

theorem dirichletEnergyForm_apply_smooth
    (q : SmoothRiemannianMetric (I_half n) M)
    (u v : SmoothScalarDirichlet q) :
    dirichletEnergyForm q
        (smoothToH1ComplDirichlet q u) (smoothToH1ComplDirichlet q v) =
      dirichletEnergy q u v := by
  have hselfEquiv : ∀ x : M, ∀ z : TangentSpace (I_half n) x,
      (1 : ℝ)⁻¹ * q.inner x z z ≤ q.inner x z z ∧
        q.inner x z z ≤ (1 : ℝ) * q.inner x z z := by
    intro x z
    simp only [inv_one, one_mul, le_refl, and_self]
  have hselfVol :
      riemannianVolumeMeasure (I := I_half n) (M := M) q ≤
        (1 : ℝ≥0∞) • riemannianVolumeMeasure (I := I_half n) (M := M) q := by
    simp only [one_smul, le_refl]
  have hmass : inner ℝ
      (H1ComplDirichletToLp q (smoothToH1ComplDirichlet q u))
      (H1ComplDirichletToLp q (smoothToH1ComplDirichlet q v)) =
      dirichletMass q u v := by
    rw [← dirichletMassCompl_self_apply
      (show (1 : ℝ) ≤ 1 from le_rfl) hselfEquiv
      1 one_ne_zero ENNReal.one_ne_top hselfVol]
    exact dirichletMassCompl_apply_smooth q
      (show (1 : ℝ) ≤ 1 from le_rfl) hselfEquiv
      1 one_ne_zero ENNReal.one_ne_top hselfVol u v
  rw [dirichletEnergyForm_apply, hmass]
  change inner ℝ
      (u : UniformSpace.Completion (SmoothScalarDirichlet q))
      (v : UniformSpace.Completion (SmoothScalarDirichlet q)) -
      dirichletMass q u v = dirichletEnergy q u v
  rw [UniformSpace.Completion.inner_coe]
  rw [InteriorSmoothScalar.inner_def]
  unfold interiorSmoothScalarH1Inner dirichletMass dirichletEnergy
  simp only [grad_g_with_boundary_section_apply']
  ring

theorem dirichletEnergyCompl_self_eq_energyForm
    (q : SmoothRiemannianMetric (I_half n) M)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ v : TangentSpace (I_half n) x,
      Cg⁻¹ * q.inner x v v ≤ q.inner x v v ∧
        q.inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) q ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q) :
    dirichletEnergyCompl q hCg hequiv Cv hCv0 hCvtop hvol =
      dirichletEnergyForm q := by
  let B := dirichletEnergyCompl q hCg hequiv Cv hCv0 hCvtop hvol
  have hsmooth (u₀ : SmoothScalarDirichlet q) :
      (fun v => B (smoothToH1ComplDirichlet q u₀) v) =
        fun v => dirichletEnergyForm q
          (smoothToH1ComplDirichlet q u₀) v := by
    apply DenseRange.equalizer (denseRange_smoothToH1ComplDirichlet q)
      (B (smoothToH1ComplDirichlet q u₀)).continuous
      (dirichletEnergyForm q
        (smoothToH1ComplDirichlet q u₀)).continuous
    funext v₀
    simp only [Function.comp_apply]
    dsimp only [B]
    rw [dirichletEnergyCompl_apply_smooth,
      dirichletEnergyForm_apply_smooth]
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  have hall : (fun z => B z v) =
      fun z => dirichletEnergyForm q z v := by
    apply DenseRange.equalizer (denseRange_smoothToH1ComplDirichlet q)
      (B.flip v).continuous
      ((dirichletEnergyForm q).flip v).continuous
    funext u₀
    exact congrFun (hsmooth u₀) v
  exact congrFun hall u

theorem dirichletFixedVolumeEnergyCompl_self_eq_energyForm
    (q : SmoothRiemannianMetric (I_half n) M)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ v : TangentSpace (I_half n) x,
      Cg⁻¹ * q.inner x v v ≤ q.inner x v v ∧
        q.inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) q ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q) :
    dirichletFixedVolumeEnergyCompl q hCg hequiv Cv hCv0 hCvtop hvol =
      dirichletEnergyForm q := by
  rw [dirichletFixedVolumeEnergyCompl,
    dirichletEnergyCompl_self_eq_energyForm q hCg hequiv
      Cv hCv0 hCvtop hvol]
  have hdensity : riemannianVolumeDensitySmoothMap q q = 1 := by
    ext x
    exact riemannianVolumeDensity_self q x
  rw [hdensity, smoothMulH1ComplDirichlet_one]
  rfl

noncomputable def dirichletFixedVolumeLaplacian
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ v : TangentSpace (I_half n) x,
      Cg⁻¹ * q.inner x v v ≤ h.inner x v v ∧
        h.inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) h ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q) :
    dirichletHs q 1 →L[ℝ] dirichletHs q (-1) :=
  dirichletBilinearFormToHs q
    (-dirichletFixedVolumeEnergyCompl h hCg hequiv Cv hCv0 hCvtop hvol)

@[simp] theorem dirichletFixedVolumeLaplacian_apply
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ v : TangentSpace (I_half n) x,
      Cg⁻¹ * q.inner x v v ≤ h.inner x v v ∧
        h.inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) h ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q)
    (u : dirichletHs q 1) :
    dirichletFixedVolumeLaplacian h hCg hequiv Cv hCv0 hCvtop hvol u =
      (dirichletHsNegOneEquivH1Dual q).symm
        (-dirichletFixedVolumeEnergyCompl h hCg hequiv Cv hCv0 hCvtop hvol
          (dirichletHsOneEquivH1Compl q u)) := rfl

theorem dirichletHsNegOneEquivH1Dual_fixedVolumeLaplacian
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ v : TangentSpace (I_half n) x,
      Cg⁻¹ * q.inner x v v ≤ h.inner x v v ∧
        h.inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) h ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q)
    (u : dirichletHs q 1) :
    dirichletHsNegOneEquivH1Dual q
        (dirichletFixedVolumeLaplacian h hCg hequiv
          Cv hCv0 hCvtop hvol u) =
      -dirichletFixedVolumeEnergyCompl h hCg hequiv Cv hCv0 hCvtop hvol
        (dirichletHsOneEquivH1Compl q u) := by
  exact dirichletHsNegOneEquivH1Dual_bilinearFormToHs q
    (-dirichletFixedVolumeEnergyCompl h hCg hequiv Cv hCv0 hCvtop hvol) u

theorem norm_dirichletFixedVolumeLaplacian_le
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ v : TangentSpace (I_half n) x,
      Cg⁻¹ * q.inner x v v ≤ h.inner x v v ∧
        h.inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) h ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q) :
    ‖dirichletFixedVolumeLaplacian h hCg hequiv Cv hCv0 hCvtop hvol‖ ≤
      ‖dirichletFixedVolumeEnergyCompl h hCg hequiv
        Cv hCv0 hCvtop hvol‖ := by
  simpa only [dirichletFixedVolumeLaplacian, norm_neg] using
    dirichletBilinearFormToHs_norm_le q
      (-dirichletFixedVolumeEnergyCompl h hCg hequiv Cv hCv0 hCvtop hvol)

theorem dirichletFixedVolumeLaplacian_self_eq
    (q : SmoothRiemannianMetric (I_half n) M)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ v : TangentSpace (I_half n) x,
      Cg⁻¹ * q.inner x v v ≤ q.inner x v v ∧
        q.inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) q ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q) :
    dirichletFixedVolumeLaplacian q hCg hequiv Cv hCv0 hCvtop hvol =
      dirichletHsLaplacianNegOne q := by
  rw [dirichletFixedVolumeLaplacian,
    dirichletFixedVolumeEnergyCompl_self_eq_energyForm q hCg hequiv
      Cv hCv0 hCvtop hvol,
    dirichletBilinearFormToHs_neg_energyForm_eq_laplacian]

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
  dirichletExtend q
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
  rw [dirichletMassVariationCompl, dirichletExtend_apply_smooth,
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
  rw [dirichletMassVariationCompl, dirichletExtend]
  apply DifferentialGeometry.Analysis.norm_bilinearFromCompletion_le
  · exact mul_nonneg
      (mul_nonneg (by norm_num) (le_max_right B 0))
      (mul_nonneg ENNReal.toReal_nonneg (zero_le_one.trans hCg))
  · intro u v
    rw [dirichletMassVariationSmooth_apply, Real.norm_eq_abs]
    exact abs_dirichletMassVariation_le_of_metric_and_volume G.metric t B htrace
      hCg hequiv Cv hCv0 hCvtop hvol u v

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
