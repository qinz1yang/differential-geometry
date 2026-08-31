import DifferentialGeometry.Analysis.DenseExtension
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletSeparability
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletSmoothMul
import DifferentialGeometry.Analysis.Integration.Measure.CompactParametricIntegral
import DifferentialGeometry.Analysis.Integration.Measure.VolumeDensityFamily
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.BochnerL2
import DifferentialGeometry.Geometry.Operator.NormGradSqTime

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped ContDiff InnerProductSpace Manifold RealInnerProductSpace Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Laplacian.WithBoundary
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

private theorem continuousOn_norm_sq_smoothScalarDirichlet_family
    (q : SmoothRiemannianMetric (I_half n) M)
    {J : Set ℝ} (hJ : IsOpen J) {T : ℝ}
    (hIcc : Icc (0 : ℝ) T ⊆ J)
    (v : ℝ → SmoothScalarDirichlet q)
    (hv : ContMDiffOn (𝓘(ℝ, ℝ).prod (I_half n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (v p.1).toFun p.2)
      (J ×ˢ (Set.univ : Set M))) :
    ContinuousOn (fun t : ℝ => ‖v t‖ ^ 2) (Icc (0 : ℝ) T) := by
  have hgram : ∀ (α : M)
      (i j : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))),
      ContMDiffOn (𝓘(ℝ, ℝ).prod (I_half n)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I_half n) q α p.2 i j)
        (J ×ˢ
          (trivializationAt (EuclideanSpace ℝ (Fin n))
            (TangentSpace (I_half n)) α).baseSet) := by
    intro α i j
    exact (chartGramMatrix_entry_contMDiffOn (I := I_half n) q α i j).comp
      contMDiffOn_snd (fun p hp => hp.2)
  have hgrad := gradSq_joint (I := I_half n) (fun _ : ℝ => q)
    hJ hgram (fun t x => (v t).toFun x) hv
  have hvI := hv.continuousOn.mono (Set.prod_mono hIcc Set.Subset.rfl)
  have hgradI := hgrad.continuousOn.mono
    (Set.prod_mono hIcc Set.Subset.rfl)
  let μ := riemannianVolumeMeasure (I := I_half n) (M := M) q
  let _ : IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I_half n) (M := M) q
  have hvalue : ContinuousOn
      (fun t : ℝ => ∫ x, (v t).toFun x ^ 2 ∂μ) (Icc (0 : ℝ) T) :=
    integral_contOn_cpt μ (fun t x => (v t).toFun x ^ 2)
      isCompact_Icc (hvI.pow 2)
  have hgradient : ContinuousOn
      (fun t : ℝ => ∫ x, q.inner x
        (gradientFun (I := I_half n) q (v t).toFun x)
        (gradientFun (I := I_half n) q (v t).toFun x) ∂μ)
      (Icc (0 : ℝ) T) :=
    integral_contOn_cpt μ (fun t x => q.inner x
      (gradientFun (I := I_half n) q (v t).toFun x)
      (gradientFun (I := I_half n) q (v t).toFun x))
      isCompact_Icc hgradI
  convert hvalue.add hgradient using 1
  funext t
  rw [InteriorSmoothScalar.norm_sq_eq_inner_self]
  unfold interiorSmoothScalarH1Inner
  simp only [grad_g_with_boundary_section_apply', sq]
  change
    (∫ x, (v t).toFun x * (v t).toFun x ∂μ) +
        ∫ x, q.inner x
          (gradientFun (I := I_half n) q (v t).toFun x)
          (gradientFun (I := I_half n) q (v t).toFun x) ∂μ = _
  rfl

private theorem continuousOn_inner_smoothMulH1ComplDirichlet
    {q : SmoothRiemannianMetric (I_half n) M}
    {J : Set ℝ} (hJ : IsOpen J) {T : ℝ}
    (hIcc : Icc (0 : ℝ) T ⊆ J)
    (φ : ℝ → C^∞⟮I_half n, M; ℝ⟯)
    (hφ : ContMDiffOn (𝓘(ℝ, ℝ).prod (I_half n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => φ p.1 p.2) (J ×ˢ (Set.univ : Set M)))
    (u v : SmoothScalarDirichlet q) :
    ContinuousOn (fun t : ℝ => inner ℝ
      (smoothToH1ComplDirichlet q u)
      (smoothMulH1ComplDirichlet q (φ t)
        (smoothToH1ComplDirichlet q v))) (Icc (0 : ℝ) T) := by
  let w : ℝ → SmoothScalarDirichlet q := fun t =>
    smoothScalarDirichletMul q (φ t) v
  have hv : ContMDiffOn (𝓘(ℝ, ℝ).prod (I_half n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => v.toFun p.2)
      (J ×ˢ (Set.univ : Set M)) := by
    have hvSmooth : ContMDiff (I_half n) 𝓘(ℝ, ℝ) ∞ v.toFun := v.smooth
    exact (hvSmooth.comp contMDiff_snd).contMDiffOn
  have hw : ContMDiffOn (𝓘(ℝ, ℝ).prod (I_half n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (w p.1).toFun p.2)
      (J ×ˢ (Set.univ : Set M)) := by
    change ContMDiffOn (𝓘(ℝ, ℝ).prod (I_half n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => φ p.1 p.2 * v.toFun p.2)
      (J ×ˢ (Set.univ : Set M))
    exact hφ.mul hv
  have hu : ContMDiffOn (𝓘(ℝ, ℝ).prod (I_half n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u.toFun p.2)
      (J ×ˢ (Set.univ : Set M)) := by
    have huSmooth : ContMDiff (I_half n) 𝓘(ℝ, ℝ) ∞ u.toFun := u.smooth
    exact (huSmooth.comp contMDiff_snd).contMDiffOn
  have huw : ContMDiffOn (𝓘(ℝ, ℝ).prod (I_half n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (u + w p.1).toFun p.2)
      (J ×ˢ (Set.univ : Set M)) := by
    change ContMDiffOn (𝓘(ℝ, ℝ).prod (I_half n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u.toFun p.2 + (w p.1).toFun p.2)
      (J ×ˢ (Set.univ : Set M))
    exact hu.add hw
  have hwNorm := continuousOn_norm_sq_smoothScalarDirichlet_family
    q hJ hIcc w hw
  have huwNorm := continuousOn_norm_sq_smoothScalarDirichlet_family
    q hJ hIcc (fun t => u + w t) huw
  have hinner : ContinuousOn (fun t : ℝ => inner ℝ
      (smoothToH1ComplDirichlet q u)
      (smoothToH1ComplDirichlet q (w t))) (Icc (0 : ℝ) T) := by
    have hformula : (fun t : ℝ => inner ℝ
        (smoothToH1ComplDirichlet q u)
        (smoothToH1ComplDirichlet q (w t))) =
        fun t => (‖u + w t‖ ^ 2 - ‖u‖ ^ 2 - ‖w t‖ ^ 2) / 2 := by
      funext t
      change inner ℝ
        (u : UniformSpace.Completion (SmoothScalarDirichlet q))
        (w t : UniformSpace.Completion (SmoothScalarDirichlet q)) = _
      rw [UniformSpace.Completion.inner_coe]
      simpa only [pow_two] using
        real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two
          u (w t)
    rw [hformula]
    exact ((huwNorm.sub continuousOn_const).sub hwNorm).div_const 2
  refine hinner.congr ?_
  intro t _
  change inner ℝ (smoothToH1ComplDirichlet q u)
      (smoothMulH1ComplDirichlet q (φ t)
        (smoothToH1ComplDirichlet q v)) =
    inner ℝ (smoothToH1ComplDirichlet q u)
      (smoothToH1ComplDirichlet q (w t))
  rw [smoothMulH1ComplDirichlet_smoothToH1ComplDirichlet]

theorem smoothMulH1ComplDirichlet_aestronglyMeasurable_of_contMDiffOn
    {q : SmoothRiemannianMetric (I_half n) M}
    {J : Set ℝ} (hJ : IsOpen J) {T : ℝ}
    (hIcc : Icc (0 : ℝ) T ⊆ J)
    (φ : ℝ → C^∞⟮I_half n, M; ℝ⟯)
    (hφ : ContMDiffOn (𝓘(ℝ, ℝ).prod (I_half n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => φ p.1 p.2) (J ×ˢ (Set.univ : Set M)))
    (u : H1ComplDirichlet q) :
    AEStronglyMeasurable
      (fun t : ℝ => smoothMulH1ComplDirichlet q (φ t) u)
      (timeMeasure T) := by
  let A : ℝ → H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q := fun t =>
    smoothMulH1ComplDirichlet q (φ t)
  apply AEStronglyMeasurable.clm_apply_of_denseRange
    (denseRange_smoothToH1ComplDirichlet q) (F := A) (x := u)
  intro v
  let F : ℝ → H1ComplDirichlet q →L[ℝ] ℝ := fun t =>
    InnerProductSpace.toDual ℝ (H1ComplDirichlet q)
      (A t (smoothToH1ComplDirichlet q v))
  have hFsmooth (z : SmoothScalarDirichlet q) :
      ContinuousOn (fun t => F t (smoothToH1ComplDirichlet q z))
        (Icc (0 : ℝ) T) := by
    have hpair := continuousOn_inner_smoothMulH1ComplDirichlet
      hJ hIcc φ hφ z v
    refine hpair.congr ?_
    intro t _
    change F t (smoothToH1ComplDirichlet q z) = inner ℝ
      (smoothToH1ComplDirichlet q z)
      (A t (smoothToH1ComplDirichlet q v))
    rw [show F t (smoothToH1ComplDirichlet q z) = inner ℝ
        (A t (smoothToH1ComplDirichlet q v))
        (smoothToH1ComplDirichlet q z) from rfl,
      real_inner_comm]
  have hF (z : H1ComplDirichlet q) :
      AEStronglyMeasurable (fun t => F t z) (timeMeasure T) := by
    apply AEStronglyMeasurable.clm_apply_of_denseRange
      (denseRange_smoothToH1ComplDirichlet q)
    intro z₀
    unfold timeMeasure
    exact (hFsmooth z₀).aestronglyMeasurable measurableSet_Icc
  have hrep :=
    dualRepresentative_aestronglyMeasurable_of_apply_aestronglyMeasurable F hF
  refine hrep.congr (Eventually.of_forall fun t => ?_)
  change (InnerProductSpace.toDual ℝ (H1ComplDirichlet q)).symm (F t) =
    A t (smoothToH1ComplDirichlet q v)
  exact (InnerProductSpace.toDual ℝ (H1ComplDirichlet q)).symm_apply_apply _

theorem exists_uniform_norm_smoothMulH1ComplDirichlet_of_contMDiffOn
    {q : SmoothRiemannianMetric (I_half n) M}
    {J : Set ℝ} (hJ : IsOpen J) {T : ℝ}
    (hIcc : Icc (0 : ℝ) T ⊆ J)
    (φ : ℝ → C^∞⟮I_half n, M; ℝ⟯)
    (hφ : ContMDiffOn (𝓘(ℝ, ℝ).prod (I_half n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => φ p.1 p.2) (J ×ˢ (Set.univ : Set M))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) T,
      ‖smoothMulH1ComplDirichlet q (φ t)‖ ≤ Real.sqrt (3 * C) := by
  have hgram : ∀ (α : M)
      (i j : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))),
      ContMDiffOn (𝓘(ℝ, ℝ).prod (I_half n)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I_half n) q α p.2 i j)
        (J ×ˢ
          (trivializationAt (EuclideanSpace ℝ (Fin n))
            (TangentSpace (I_half n)) α).baseSet) := by
    intro α i j
    exact (chartGramMatrix_entry_contMDiffOn (I := I_half n) q α i j).comp
      contMDiffOn_snd (fun p hp => hp.2)
  have hgrad := gradSq_joint (I := I_half n) (fun _ : ℝ => q)
    hJ hgram (fun t x => φ t x) hφ
  let K : Set (ℝ × M) := Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)
  have hK : IsCompact K := isCompact_Icc.prod isCompact_univ
  have hφsq : ContinuousOn (fun p : ℝ × M => φ p.1 p.2 ^ 2) K :=
    (hφ.continuousOn.mono (Set.prod_mono hIcc Set.Subset.rfl)).pow 2
  have hgradK : ContinuousOn (fun p : ℝ × M =>
      q.inner p.2
        (gradientFun (I := I_half n) q (φ p.1) p.2)
        (gradientFun (I := I_half n) q (φ p.1) p.2)) K :=
    hgrad.continuousOn.mono (Set.prod_mono hIcc Set.Subset.rfl)
  obtain ⟨Cφ, hCφ⟩ := hK.exists_bound_of_continuousOn hφsq
  obtain ⟨Cgrad, hCgrad⟩ := hK.exists_bound_of_continuousOn hgradK
  let C := max 0 (max Cφ Cgrad)
  have hC : 0 ≤ C := le_max_left 0 (max Cφ Cgrad)
  refine ⟨C, hC, ?_⟩
  intro t ht
  apply norm_smoothMulH1ComplDirichlet_le_of_bound q (φ t) hC
  · intro x
    have hbound := hCφ (t, x) ⟨ht, Set.mem_univ x⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (φ t x))] at hbound
    exact hbound.trans ((le_max_left Cφ Cgrad).trans (le_max_right 0 _))
  · intro x
    have hbound := hCgrad (t, x) ⟨ht, Set.mem_univ x⟩
    have hnonneg : 0 ≤ q.inner x
        (gradientFun (I := I_half n) q (φ t) x)
        (gradientFun (I := I_half n) q (φ t) x) :=
      SmoothRiemannianMetric_inner_self_nonneg q x _
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg] at hbound
    exact hbound.trans ((le_max_right Cφ Cgrad).trans (le_max_right 0 _))

theorem smoothMulH1ComplDirichlet_volumeDensity_swap_aestronglyMeasurable
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_half n) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_half n) (M := M) D G.metric)
    {T : ℝ} (hreg : Icc (0 : ℝ) T ⊆ D.regular)
    (u : H1ComplDirichlet q) :
    AEStronglyMeasurable (fun t : ℝ =>
      smoothMulH1ComplDirichlet q
        (riemannianVolumeDensitySmoothMap (G.metric t) q) u)
      (timeMeasure T) := by
  exact smoothMulH1ComplDirichlet_aestronglyMeasurable_of_contMDiffOn
    D.regular_isOpen hreg
    (fun t => riemannianVolumeDensitySmoothMap (G.metric t) q)
    (riemannianVolumeDensity_swap_contMDiffOn_of_metricFamilySmoothOn hG q) u

theorem exists_uniform_norm_smoothMulH1ComplDirichlet_volumeDensity_swap
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_half n) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_half n) (M := M) D G.metric)
    {T : ℝ} (hreg : Icc (0 : ℝ) T ⊆ D.regular) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) T,
      ‖smoothMulH1ComplDirichlet q
        (riemannianVolumeDensitySmoothMap (G.metric t) q)‖ ≤
          Real.sqrt (3 * C) := by
  exact exists_uniform_norm_smoothMulH1ComplDirichlet_of_contMDiffOn
    D.regular_isOpen hreg
    (fun t => riemannianVolumeDensitySmoothMap (G.metric t) q)
    (riemannianVolumeDensity_swap_contMDiffOn_of_metricFamilySmoothOn hG q)

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
