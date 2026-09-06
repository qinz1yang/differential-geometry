import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletSmoothMul
import DifferentialGeometry.Analysis.Integration.Measure.CompactParametricIntegral
import DifferentialGeometry.Analysis.Integration.Measure.VolumeDensityFamily
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.WeakEvolution
import DifferentialGeometry.Geometry.Operator.NormGradSqTime

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal InnerProductSpace Manifold NNReal
  RealInnerProductSpace Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Laplacian.WithBoundary
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

private theorem continuousOn_norm_sq_smoothScalarDirichlet_family
    (q : SmoothRiemannianMetric (I_half n) M)
    {D : RealTimeInterval} {T : ℝ}
    (hreg : Icc (0 : ℝ) T ⊆ D.regular)
    (v : ℝ → SmoothScalarDirichlet q)
    (hv : ContMDiffOn (𝓘(ℝ, ℝ).prod (I_half n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (v p.1).toFun p.2)
      (D.regular ×ˢ (Set.univ : Set M))) :
    ContinuousOn (fun t : ℝ => ‖v t‖ ^ 2) (Icc (0 : ℝ) T) := by
  have hgram : ∀ (α : M)
      (i j : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))),
      ContMDiffOn (𝓘(ℝ, ℝ).prod (I_half n)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I_half n) q α p.2 i j)
        (D.regular ×ˢ
          (trivializationAt (EuclideanSpace ℝ (Fin n))
            (TangentSpace (I_half n)) α).baseSet) := by
    intro α i j
    exact (chartGramMatrix_entry_contMDiffOn (I := I_half n) q α i j).comp
      contMDiffOn_snd (fun p hp => hp.2)
  have hgrad := gradSq_joint (I := I_half n) (fun _ : ℝ => q)
    D.regular_isOpen hgram (fun t x => (v t).toFun x) hv
  have hvI := hv.continuousOn.mono (Set.prod_mono hreg Set.Subset.rfl)
  have hgradI := hgrad.continuousOn.mono (Set.prod_mono hreg Set.Subset.rfl)
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

private theorem continuousOn_inner_smoothMul_volumeDensity
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_half n) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_half n) (M := M) D G.metric)
    {T : ℝ} (hreg : Icc (0 : ℝ) T ⊆ D.regular)
    (u v : SmoothScalarDirichlet q) :
    ContinuousOn (fun t : ℝ => inner ℝ
      (smoothToH1ComplDirichlet q u)
      (smoothMulH1ComplDirichlet q
        (riemannianVolumeDensitySmoothMap q (G.metric t))
        (smoothToH1ComplDirichlet q v))) (Icc (0 : ℝ) T) := by
  let ρ : ℝ → C^∞⟮I_half n, M; ℝ⟯ := fun t =>
    riemannianVolumeDensitySmoothMap q (G.metric t)
  let w : ℝ → SmoothScalarDirichlet q := fun t =>
    smoothScalarDirichletMul q (ρ t) v
  have hρ := riemannianVolumeDensity_contMDiffOn_of_metricFamilySmoothOn
    (I := I_half n) hG q
  have hv : ContMDiffOn (𝓘(ℝ, ℝ).prod (I_half n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => v.toFun p.2)
      (D.regular ×ˢ (Set.univ : Set M)) := by
    have hvSmooth : ContMDiff (I_half n) 𝓘(ℝ, ℝ) ∞ v.toFun := v.smooth
    exact (hvSmooth.comp contMDiff_snd).contMDiffOn
  have hw : ContMDiffOn (𝓘(ℝ, ℝ).prod (I_half n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (w p.1).toFun p.2)
      (D.regular ×ˢ (Set.univ : Set M)) := by
    change ContMDiffOn (𝓘(ℝ, ℝ).prod (I_half n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M =>
        riemannianVolumeDensity q (G.metric p.1) p.2 * v.toFun p.2)
      (D.regular ×ˢ (Set.univ : Set M))
    exact hρ.mul hv
  have hu : ContMDiffOn (𝓘(ℝ, ℝ).prod (I_half n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u.toFun p.2)
      (D.regular ×ˢ (Set.univ : Set M)) := by
    have huSmooth : ContMDiff (I_half n) 𝓘(ℝ, ℝ) ∞ u.toFun := u.smooth
    exact (huSmooth.comp contMDiff_snd).contMDiffOn
  have huw : ContMDiffOn (𝓘(ℝ, ℝ).prod (I_half n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (u + w p.1).toFun p.2)
      (D.regular ×ˢ (Set.univ : Set M)) := by
    change ContMDiffOn (𝓘(ℝ, ℝ).prod (I_half n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u.toFun p.2 + (w p.1).toFun p.2)
      (D.regular ×ˢ (Set.univ : Set M))
    exact hu.add hw
  have hwNorm := continuousOn_norm_sq_smoothScalarDirichlet_family
    q hreg w hw
  have huwNorm := continuousOn_norm_sq_smoothScalarDirichlet_family
    q hreg (fun t => u + w t) huw
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
      (smoothMulH1ComplDirichlet q (ρ t)
        (smoothToH1ComplDirichlet q v)) =
    inner ℝ (smoothToH1ComplDirichlet q u)
      (smoothToH1ComplDirichlet q (w t))
  rw [smoothMulH1ComplDirichlet_smoothToH1ComplDirichlet]

theorem smoothMulH1ComplDirichlet_volumeDensity_aestronglyMeasurable
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_half n) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_half n) (M := M) D G.metric)
    {T : ℝ} (hreg : Icc (0 : ℝ) T ⊆ D.regular)
    (u : H1ComplDirichlet q) :
    AEStronglyMeasurable (fun t : ℝ =>
      smoothMulH1ComplDirichlet q
        (riemannianVolumeDensitySmoothMap q (G.metric t)) u)
      (timeMeasure T) := by
  let A : ℝ → H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q := fun t =>
    smoothMulH1ComplDirichlet q
      (riemannianVolumeDensitySmoothMap q (G.metric t))
  apply AEStronglyMeasurable.clm_apply_of_denseRange
    (denseRange_smoothToH1ComplDirichlet q) (F := A) (x := u)
  intro v
  let F : ℝ → H1ComplDirichlet q →L[ℝ] ℝ := fun t =>
    InnerProductSpace.toDual ℝ (H1ComplDirichlet q)
      (A t (smoothToH1ComplDirichlet q v))
  have hFsmooth (z : SmoothScalarDirichlet q) :
      ContinuousOn (fun t => F t (smoothToH1ComplDirichlet q z))
        (Icc (0 : ℝ) T) := by
    have hpair := continuousOn_inner_smoothMul_volumeDensity
      hG hreg z v
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

theorem exists_uniform_norm_smoothMulH1ComplDirichlet_volumeDensity
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_half n) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_half n) (M := M) D G.metric)
    {T : ℝ} (hreg : Icc (0 : ℝ) T ⊆ D.regular) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) T,
      ‖smoothMulH1ComplDirichlet q
        (riemannianVolumeDensitySmoothMap q (G.metric t))‖ ≤
          Real.sqrt (3 * C) := by
  have hρ := riemannianVolumeDensity_contMDiffOn_of_metricFamilySmoothOn
    (I := I_half n) hG q
  have hgram : ∀ (α : M)
      (i j : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))),
      ContMDiffOn (𝓘(ℝ, ℝ).prod (I_half n)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I_half n) q α p.2 i j)
        (D.regular ×ˢ
          (trivializationAt (EuclideanSpace ℝ (Fin n))
            (TangentSpace (I_half n)) α).baseSet) := by
    intro α i j
    exact (chartGramMatrix_entry_contMDiffOn (I := I_half n) q α i j).comp
      contMDiffOn_snd (fun p hp => hp.2)
  have hgrad := gradSq_joint (I := I_half n) (fun _ : ℝ => q)
    D.regular_isOpen hgram
    (fun t x => riemannianVolumeDensity q (G.metric t) x) hρ
  let K : Set (ℝ × M) := Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)
  have hK : IsCompact K := isCompact_Icc.prod isCompact_univ
  have hρsq : ContinuousOn (fun p : ℝ × M =>
      riemannianVolumeDensity q (G.metric p.1) p.2 ^ 2) K :=
    (hρ.continuousOn.mono (Set.prod_mono hreg Set.Subset.rfl)).pow 2
  have hgradK : ContinuousOn (fun p : ℝ × M =>
      q.inner p.2
        (gradientFun (I := I_half n) q
          (riemannianVolumeDensity q (G.metric p.1)) p.2)
        (gradientFun (I := I_half n) q
          (riemannianVolumeDensity q (G.metric p.1)) p.2)) K :=
    hgrad.continuousOn.mono (Set.prod_mono hreg Set.Subset.rfl)
  obtain ⟨Cρ, hCρ⟩ := hK.exists_bound_of_continuousOn hρsq
  obtain ⟨Cgrad, hCgrad⟩ := hK.exists_bound_of_continuousOn hgradK
  let C := max 0 (max Cρ Cgrad)
  have hC : 0 ≤ C := le_max_left 0 (max Cρ Cgrad)
  refine ⟨C, hC, ?_⟩
  intro t ht
  apply norm_smoothMulH1ComplDirichlet_le_of_bound q
    (riemannianVolumeDensitySmoothMap q (G.metric t)) hC
  · intro x
    have hbound := hCρ (t, x) ⟨ht, Set.mem_univ x⟩
    rw [Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg (riemannianVolumeDensity q (G.metric t) x))]
      at hbound
    exact hbound.trans ((le_max_left Cρ Cgrad).trans (le_max_right 0 _))
  · intro x
    have hbound := hCgrad (t, x) ⟨ht, Set.mem_univ x⟩
    have hnonneg : 0 ≤ q.inner x
        (gradientFun (I := I_half n) q
          (riemannianVolumeDensity q (G.metric t)) x)
        (gradientFun (I := I_half n) q
          (riemannianVolumeDensity q (G.metric t)) x) :=
      WithBoundary.SmoothRiemannianMetric_inner_self_nonneg q x _
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg] at hbound
    exact hbound.trans ((le_max_right Cρ Cgrad).trans (le_max_right 0 _))

theorem exists_timeL2_smoothMulH1ComplDirichlet_volumeDensity
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_half n) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_half n) (M := M) D G.metric)
    {T : ℝ} (hreg : Icc (0 : ℝ) T ⊆ D.regular)
    (u : timeL2 (H1ComplDirichlet q) T) :
    ∃ w : timeL2 (H1ComplDirichlet q) T,
      w =ᵐ[timeMeasure T] fun t =>
        smoothMulH1ComplDirichlet q
          (riemannianVolumeDensitySmoothMap q (G.metric t)) (u t) := by
  let A : ℝ → H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q := fun t =>
    smoothMulH1ComplDirichlet q
      (riemannianVolumeDensitySmoothMap q (G.metric t))
  have hA (v : H1ComplDirichlet q) :
      AEStronglyMeasurable (fun t => A t v) (timeMeasure T) :=
    smoothMulH1ComplDirichlet_volumeDensity_aestronglyMeasurable
      hG hreg v
  have hmeas : AEStronglyMeasurable (fun t => A t (u t)) (timeMeasure T) :=
    AEStronglyMeasurable.clm_apply_of_apply_aestronglyMeasurable
      A hA u (Lp.aestronglyMeasurable u)
  obtain ⟨C, hC, hbound⟩ :=
    exists_uniform_norm_smoothMulH1ComplDirichlet_volumeDensity hG hreg
  have hmem : MemLp (fun t => A t (u t)) 2 (timeMeasure T) := by
    refine MemLp.of_le_mul (c := Real.sqrt (3 * C)) (Lp.memLp u) hmeas ?_
    unfold timeMeasure
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    calc
      ‖A t (u t)‖ ≤ ‖A t‖ * ‖u t‖ := (A t).le_opNorm (u t)
      _ ≤ Real.sqrt (3 * C) * ‖u t‖ := by
        gcongr
        exact hbound t ht
  exact ⟨hmem.toLp (fun t => A t (u t)), hmem.coeFn_toLp⟩

theorem dirichletMassComplOnIcc_apply_eq_inner_smoothMul_volumeDensity
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
    (u v : H1ComplDirichlet q) :
    dirichletMassComplOnIcc g hCg hequiv Cv hCv0 hCvtop hvol t u v =
      inner ℝ
        (H1ComplDirichletToLp q
          (smoothMulH1ComplDirichlet q
            (riemannianVolumeDensitySmoothMap q (g t)) u))
        (H1ComplDirichletToLp q v) := by
  let ρ := riemannianVolumeDensitySmoothMap q (g t)
  let A := smoothMulH1ComplDirichlet q ρ
  have hselfEquiv : ∀ x : M, ∀ z : TangentSpace (I_half n) x,
      (1 : ℝ)⁻¹ * q.inner x z z ≤ q.inner x z z ∧
        q.inner x z z ≤ (1 : ℝ) * q.inner x z z := by
    intro x z
    simp only [inv_one, one_mul, le_refl, and_self]
  have hselfVol :
      riemannianVolumeMeasure (I := I_half n) (M := M) q ≤
        (1 : ℝ≥0∞) • riemannianVolumeMeasure (I := I_half n) (M := M) q := by
    simp only [one_smul, le_refl]
  let mass := dirichletMassComplOnIcc g hCg hequiv
    Cv hCv0 hCvtop hvol t
  let fixedMass := dirichletMassCompl q (show (1 : ℝ) ≤ 1 from le_rfl)
    hselfEquiv 1 one_ne_zero ENNReal.one_ne_top hselfVol
  have hsmooth (u₀ : SmoothScalarDirichlet q) :
      (fun z => mass (smoothToH1ComplDirichlet q u₀) z) =
        fun z => fixedMass (A (smoothToH1ComplDirichlet q u₀)) z := by
    apply DenseRange.equalizer (denseRange_smoothToH1ComplDirichlet q)
      (mass (smoothToH1ComplDirichlet q u₀)).continuous
      (fixedMass (A (smoothToH1ComplDirichlet q u₀))).continuous
    funext v₀
    simp only [Function.comp_apply]
    dsimp only [mass]
    rw [dirichletMassComplOnIcc_apply_smooth g hCg hequiv
      Cv hCv0 hCvtop hvol ht u₀ v₀]
    change dirichletMass (g t) u₀ v₀ =
      fixedMass (A (smoothToH1ComplDirichlet q u₀))
        (smoothToH1ComplDirichlet q v₀)
    rw [show A (smoothToH1ComplDirichlet q u₀) =
        smoothToH1ComplDirichlet q (smoothScalarDirichletMul q ρ u₀) by
      exact smoothMulH1ComplDirichlet_smoothToH1ComplDirichlet q ρ u₀]
    dsimp only [fixedMass]
    rw [dirichletMassCompl_apply_smooth]
    unfold dirichletMass
    rw [integral_riemannianVolumeMeasure_eq_integral_volumeDensity_smul
      (I := I_half n) q (g t)]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [smul_eq_mul, smoothScalarDirichletMul_toFun]
    change riemannianVolumeDensity q (g t) x * (u₀.toFun x * v₀.toFun x) =
      (riemannianVolumeDensity q (g t) x * u₀.toFun x) * v₀.toFun x
    ring
  have hall : (fun y => mass y v) = fun y => fixedMass (A y) v := by
    apply DenseRange.equalizer (denseRange_smoothToH1ComplDirichlet q)
      (mass.flip v).continuous
      ((fixedMass.flip v).comp A).continuous
    funext u₀
    exact congrFun (hsmooth u₀) v
  rw [show mass u v = fixedMass (A u) v from congrFun hall u]
  exact dirichletMassCompl_self_apply
    (show (1 : ℝ) ≤ 1 from le_rfl) hselfEquiv
    1 one_ne_zero ENNReal.one_ne_top hselfVol (A u) v

theorem dirichletMassComplOnIcc_riesz_eq_resolvent_smoothMul_volumeDensity
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
    (u : H1ComplDirichlet q) :
    (InnerProductSpace.toDual ℝ (H1ComplDirichlet q)).symm
        (dirichletMassComplOnIcc g hCg hequiv
          Cv hCv0 hCvtop hvol t u) =
      resolventDirichlet q
        (H1ComplDirichletToLp q
          (smoothMulH1ComplDirichlet q
            (riemannianVolumeDensitySmoothMap q (g t)) u)) := by
  apply ext_inner_right ℝ
  intro v
  rw [InnerProductSpace.toDual_symm_apply,
    dirichletMassComplOnIcc_apply_eq_inner_smoothMul_volumeDensity
      g hCg hequiv Cv hCv0 hCvtop hvol ht,
    resolventDirichlet_inner_eq_lpFunctional,
    real_inner_comm]

theorem dirichletMassLp_riesz_eq_resolvent_smoothMul_volumeDensity
    {q h : SmoothRiemannianMetric (I_half n) M}
    (Cv : ℝ≥0∞) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) h ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q)
    (f : Lp ℝ 2
      (riemannianVolumeMeasure (I := I_half n) (M := M) q)) :
    (InnerProductSpace.toDual ℝ (H1ComplDirichlet q)).symm
        ((dirichletMassLp h Cv hCvtop hvol f).comp
          (H1ComplDirichletToLp q)) =
      resolventDirichlet q
        (smoothMulLp q (riemannianVolumeDensitySmoothMap q h) f) := by
  let ρ := riemannianVolumeDensitySmoothMap q h
  let B := dirichletMassLp h Cv hCvtop hvol
  let S := smoothMulLp q ρ
  have hsmooth (u₀ : SmoothScalarDirichlet q) :
      (fun v => B (smoothToLpDirichlet q u₀) (H1ComplDirichletToLp q v)) =
        fun v => inner ℝ (H1ComplDirichletToLp q v)
          (S (smoothToLpDirichlet q u₀)) := by
    apply DenseRange.equalizer (denseRange_smoothToH1ComplDirichlet q)
      ((B (smoothToLpDirichlet q u₀)).comp
        (H1ComplDirichletToLp q)).continuous
      ((H1ComplDirichletToLp q).continuous.inner continuous_const)
    funext v₀
    simp only [Function.comp_apply, ContinuousLinearMap.comp_apply]
    dsimp only [B]
    rw [H1ComplDirichletToLp_smoothToH1ComplDirichlet]
    rw [dirichletMassLp_apply_smooth]
    rw [MeasureTheory.L2.inner_def]
    unfold dirichletMass
    rw [integral_riemannianVolumeMeasure_eq_integral_volumeDensity_smul
      (I := I_half n) q h]
    apply integral_congr_ae
    have hu := MemLp.coeFn_toLp u₀.memLp_two
    have hv := MemLp.coeFn_toLp v₀.memLp_two
    have hmul := smoothMulLp_apply_coeFn q ρ (smoothToLpDirichlet q u₀)
    filter_upwards [hu, hv, hmul] with x hux hvx hmulx
    rw [hmulx]
    rw [show (smoothToLpDirichlet q v₀ : M → ℝ) x = v₀.toFun x from hvx]
    rw [show (smoothToLpDirichlet q u₀ : M → ℝ) x = u₀.toFun x from hux]
    simp only [RCLike.inner_apply, conj_trivial]
    dsimp only [ρ]
    rw [smul_eq_mul]
    rw [show (riemannianVolumeDensitySmoothMap q h : M → ℝ) x =
      riemannianVolumeDensity q h x from rfl]
    ring
  have hall (v : H1ComplDirichlet q) :
      (fun z => B z (H1ComplDirichletToLp q v)) =
        fun z => inner ℝ (H1ComplDirichletToLp q v) (S z) := by
    apply DenseRange.equalizer (denseRange_smoothToLpDirichlet q)
      (B.flip (H1ComplDirichletToLp q v)).continuous
      (continuous_const.inner S.continuous)
    funext u₀
    exact congrFun (hsmooth u₀) v
  apply ext_inner_right ℝ
  intro v
  rw [InnerProductSpace.toDual_symm_apply]
  simp only [ContinuousLinearMap.comp_apply]
  rw [
    show B f (H1ComplDirichletToLp q v) =
      inner ℝ (H1ComplDirichletToLp q v) (S f) from congrFun (hall v) f,
    resolventDirichlet_inner_eq_lpFunctional]

private theorem smoothMulLp_volumeDensity_swap_apply
    (q h k : SmoothRiemannianMetric (I_half n) M)
    (f : Lp ℝ 2
      (riemannianVolumeMeasure (I := I_half n) (M := M) q)) :
    smoothMulLp q (riemannianVolumeDensitySmoothMap h k)
        (smoothMulLp q (riemannianVolumeDensitySmoothMap k h) f) = f := by
  rw [← ContinuousLinearMap.comp_apply, smoothMulLp_mul]
  have hmul : riemannianVolumeDensitySmoothMap h k *
      riemannianVolumeDensitySmoothMap k h = 1 := by
    ext x
    change riemannianVolumeDensity h k x *
      riemannianVolumeDensity k h x = 1
    exact riemannianVolumeDensity_mul_swap h k x
  rw [hmul, smoothMulLp_one, ContinuousLinearMap.id_apply]

theorem exists_continuous_l2_representative_of_volumeDensity_mass_timeH1
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_half n) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_half n) (M := M) D G.metric)
    {T : ℝ} (hT : 0 ≤ T) (hreg : Icc (0 : ℝ) T ⊆ D.regular)
    (u : timeL2 (H1ComplDirichlet q) T)
    (w : timeH1 (H1ComplDirichlet q) T)
    (f₀ : Lp ℝ 2
      (riemannianVolumeMeasure (I := I_half n) (M := M) q))
    (hmass : (fun t => resolventDirichlet q
      (H1ComplDirichletToLp q
        (smoothMulH1ComplDirichlet q
          (riemannianVolumeDensitySmoothMap q (G.metric t)) (u t))))
      =ᵐ[timeMeasure T] w.toFun)
    (hinit : w.init = resolventDirichlet q
      (smoothMulLp q (riemannianVolumeDensitySmoothMap q (G.metric 0)) f₀)) :
    ∃ U : ℝ → Lp ℝ 2
        (riemannianVolumeMeasure (I := I_half n) (M := M) q),
      ContinuousOn U (Icc (0 : ℝ) T) ∧
      (U =ᵐ[timeMeasure T] fun t => H1ComplDirichletToLp q (u t)) ∧
      U 0 = f₀ ∧
      ∀ a b, a ∈ Icc (0 : ℝ) T → b ∈ Icc (0 : ℝ) T →
        ‖smoothMulLp q (riemannianVolumeDensitySmoothMap q (G.metric b))
          (U b)‖ ^ 2 -
        ‖smoothMulLp q (riemannianVolumeDensitySmoothMap q (G.metric a))
          (U a)‖ ^ 2 =
          ∫ t in a..b, 2 * inner ℝ
            (smoothMulH1ComplDirichlet q
              (riemannianVolumeDensitySmoothMap q (G.metric t)) (u t))
            (w.deriv t) := by
  obtain ⟨z, hz⟩ :=
    exists_timeL2_smoothMulH1ComplDirichlet_volumeDensity hG hreg u
  have hmassz : (fun t => resolventDirichlet q
      (H1ComplDirichletToLp q (z t))) =ᵐ[timeMeasure T] w.toFun := by
    filter_upwards [hz, hmass] with t hzt ht
    simpa only [hzt] using ht
  obtain ⟨V, hVcont, hVae, hVzero, hVenergy⟩ :=
    exists_continuous_l2_representative_of_mass_timeH1
      q hT z w
        (smoothMulLp q
          (riemannianVolumeDensitySmoothMap q (G.metric 0)) f₀)
        hmassz hinit
  let σ : ℝ → C^∞⟮I_half n, M; ℝ⟯ := fun t =>
    riemannianVolumeDensitySmoothMap (G.metric t) q
  let U : ℝ → Lp ℝ 2
      (riemannianVolumeMeasure (I := I_half n) (M := M) q) := fun t =>
    smoothMulLp q (σ t) (V t)
  have hσ : ContinuousOn (fun p : ℝ × M => σ p.1 p.2)
      (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)) := by
    exact
      (riemannianVolumeDensity_swap_contMDiffOn_of_metricFamilySmoothOn
        hG q).continuousOn.mono (Set.prod_mono hreg Set.Subset.rfl)
  have hUcont : ContinuousOn U (Icc (0 : ℝ) T) :=
    continuousOn_smoothMulLp_apply q σ hσ hVcont
  have hUae : U =ᵐ[timeMeasure T]
      fun t => H1ComplDirichletToLp q (u t) := by
    filter_upwards [hVae, hz] with t hVt hzt
    dsimp only [U, σ]
    rw [hVt, hzt, H1ComplDirichletToLp_smoothMulH1ComplDirichlet]
    exact smoothMulLp_volumeDensity_swap_apply q (G.metric t) q
      (H1ComplDirichletToLp q (u t))
  have hUzero : U 0 = f₀ := by
    dsimp only [U, σ]
    rw [hVzero]
    exact smoothMulLp_volumeDensity_swap_apply q (G.metric 0) q f₀
  refine ⟨U, hUcont, hUae, hUzero, fun a b ha hb => ?_⟩
  have hρU (t : ℝ) :
      smoothMulLp q (riemannianVolumeDensitySmoothMap q (G.metric t))
        (U t) = V t :=
    smoothMulLp_volumeDensity_swap_apply q q (G.metric t) (V t)
  rw [hρU a, hρU b, hVenergy a b ha hb]
  apply intervalIntegral.integral_congr_ae_restrict
  have hsub : uIoc a b ⊆ Icc (0 : ℝ) T :=
    uIoc_subset_uIcc.trans (uIcc_subset_Icc ha hb)
  have hzi := hz.filter_mono
    (ae_mono (Measure.restrict_mono hsub le_rfl))
  filter_upwards [hzi] with t ht
  rw [ht]

theorem IsWeakEvolutionSolution.exists_continuous_l2_representative_with_mass_energy
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
    ∃ Cg : ℝ, ∃ Cv : ℝ≥0∞,
      ∃ hCg : 1 ≤ Cg,
      ∃ hequiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
        ∀ v : TangentSpace (I_half n) x,
          Cg⁻¹ * q.inner x v v ≤ (G.metric t).inner x v v ∧
            (G.metric t).inner x v v ≤ Cg * q.inner x v v,
      ∃ hCv0 : Cv ≠ 0, ∃ hCvtop : Cv ≠ ⊤,
      ∃ hvol : ∀ t ∈ Icc (0 : ℝ) T,
        riemannianVolumeMeasure (I := I_half n) (M := M) (G.metric t) ≤
          Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q,
      ∃ U : ℝ → Lp ℝ 2
          (riemannianVolumeMeasure (I := I_half n) (M := M) q),
        ContinuousOn U (Icc (0 : ℝ) T) ∧
        (U =ᵐ[timeMeasure T] fun t => H1ComplDirichletToLp q (u t)) ∧
        U 0 = f₀ ∧
        ∀ r s, r ∈ Icc (0 : ℝ) T → s ∈ Icc (0 : ℝ) T →
          ‖smoothMulLp q (riemannianVolumeDensitySmoothMap q (G.metric s))
            (U s)‖ ^ 2 -
          ‖smoothMulLp q (riemannianVolumeDensitySmoothMap q (G.metric r))
            (U r)‖ ^ 2 =
            ∫ t in r..s, 2 * (
              dirichletMassVariationComplOnIco hG hreg Bv htrace
                hCg hequiv Cv hCv0 hCvtop hvol t (u t)
                (smoothMulH1ComplDirichlet q
                  (riemannianVolumeDensitySmoothMap q (G.metric t)) (u t)) +
              dirichletWeakFormComplOnIco G.metric X a Bx hX
                hCg hequiv Cv hCv0 hCvtop hvol t (u t)
                (smoothMulH1ComplDirichlet q
                  (riemannianVolumeDensitySmoothMap q (G.metric t)) (u t))) := by
  obtain ⟨Cg, Cv, hCg, hequiv, hCv0, hCvtop, hvol,
      w, hwinit, hwmass, hwderiv⟩ := hu.exists_mass_timeH1 hXcont hacont
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
  have hmass : (fun t => resolventDirichlet q
      (H1ComplDirichletToLp q
        (smoothMulH1ComplDirichlet q
          (riemannianVolumeDensitySmoothMap q (G.metric t)) (u t))))
      =ᵐ[timeMeasure T] w.toFun := by
    filter_upwards [hwmass, ae_restrict_mem measurableSet_Icc]
      with t hwt ht
    exact (dirichletMassComplOnIcc_riesz_eq_resolvent_smoothMul_volumeDensity
      G.metric hCg hequiv Cv hCv0 hCvtop hvol ht (u t)).symm.trans hwt
  have hinit : w.init = resolventDirichlet q
      (smoothMulLp q
        (riemannianVolumeDensitySmoothMap q (G.metric 0)) f₀) :=
    hwinit.trans (dirichletMassLp_riesz_eq_resolvent_smoothMul_volumeDensity
      Cv hCvtop (hvol 0 hzero) f₀)
  obtain ⟨U, hUcont, hUae, hUzero, henergy⟩ :=
    exists_continuous_l2_representative_of_volumeDensity_mass_timeH1
      hG hT hreg u w f₀ hmass hinit
  refine ⟨Cg, Cv, hCg, hequiv, hCv0, hCvtop, hvol,
    U, hUcont, hUae, hUzero, fun r s hr hs => ?_⟩
  rw [henergy r s hr hs]
  apply intervalIntegral.integral_congr_ae_restrict
  have hsub : uIoc r s ⊆ Icc (0 : ℝ) T :=
    uIoc_subset_uIcc.trans (uIcc_subset_Icc hr hs)
  have hwi := hwderiv.filter_mono
    (ae_mono (Measure.restrict_mono hsub le_rfl))
  filter_upwards [hwi] with t ht
  rw [ht, real_inner_comm, InnerProductSpace.toDual_symm_apply]
  rfl


theorem IsWeakEvolutionSolution.exists_continuous_l2_representative
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
    ∃ U : ℝ → Lp ℝ 2
        (riemannianVolumeMeasure (I := I_half n) (M := M) q),
      ContinuousOn U (Icc (0 : ℝ) T) ∧
      (U =ᵐ[timeMeasure T] fun t => H1ComplDirichletToLp q (u t)) ∧
      U 0 = f₀ := by
  obtain ⟨_, _, _, _, _, _, _, U, hUcont, hUae, hUzero, _⟩ :=
    hu.exists_continuous_l2_representative_with_mass_energy hXcont hacont
  exact ⟨U, hUcont, hUae, hUzero⟩

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
