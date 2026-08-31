import DifferentialGeometry.Analysis.Integration.Measure.CompactParametricIntegral
import DifferentialGeometry.Analysis.Integration.Measure.VolumeDensityFamily
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.TimeDependentSmoothMul
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.WeakEvolution

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
  exact smoothMulH1ComplDirichlet_aestronglyMeasurable_of_contMDiffOn
    D.regular_isOpen hreg
    (fun t => riemannianVolumeDensitySmoothMap q (G.metric t))
    (riemannianVolumeDensity_contMDiffOn_of_metricFamilySmoothOn hG q) u

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
  exact exists_uniform_norm_smoothMulH1ComplDirichlet_of_contMDiffOn
    D.regular_isOpen hreg
    (fun t => riemannianVolumeDensitySmoothMap q (G.metric t))
    (riemannianVolumeDensity_contMDiffOn_of_metricFamilySmoothOn hG q)

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
    (q h : SmoothRiemannianMetric (I_half n) M)
    (f : Lp ℝ 2
      (riemannianVolumeMeasure (I := I_half n) (M := M) q)) :
    smoothMulLp q (riemannianVolumeDensitySmoothMap h q)
        (smoothMulLp q (riemannianVolumeDensitySmoothMap q h) f) = f := by
  rw [← ContinuousLinearMap.comp_apply, smoothMulLp_mul]
  have hmul : riemannianVolumeDensitySmoothMap h q *
      riemannianVolumeDensitySmoothMap q h = 1 := by
    ext x
    change riemannianVolumeDensity h q x *
      riemannianVolumeDensity q h x = 1
    exact riemannianVolumeDensity_mul_swap h q x
  rw [hmul, smoothMulLp_one, ContinuousLinearMap.id_apply]

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
  obtain ⟨Cg, Cv, hCg, hequiv, hCv0, hCvtop, hvol,
      w, hwinit, hwmass, _⟩ := hu.exists_mass_timeH1 hXcont hacont
  obtain ⟨z, hz⟩ :=
    exists_timeL2_smoothMulH1ComplDirichlet_volumeDensity hG hreg u
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
  have hmass : (fun t => resolventDirichlet q
      (H1ComplDirichletToLp q (z t))) =ᵐ[timeMeasure T] w.toFun := by
    filter_upwards [hz, hwmass, ae_restrict_mem measurableSet_Icc]
      with t hzt hwt ht
    rw [hzt]
    exact (dirichletMassComplOnIcc_riesz_eq_resolvent_smoothMul_volumeDensity
      G.metric hCg hequiv Cv hCv0 hCvtop hvol ht (u t)).symm.trans hwt
  have hinit : w.init = resolventDirichlet q
      (smoothMulLp q
        (riemannianVolumeDensitySmoothMap q (G.metric 0)) f₀) :=
    hwinit.trans (dirichletMassLp_riesz_eq_resolvent_smoothMul_volumeDensity
      Cv hCvtop (hvol 0 hzero) f₀)
  obtain ⟨V, hVcont, hVae, hVzero, _⟩ :=
    exists_continuous_l2_representative_of_mass_timeH1
      q hT z w
        (smoothMulLp q
          (riemannianVolumeDensitySmoothMap q (G.metric 0)) f₀)
        hmass hinit
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
    exact smoothMulLp_volumeDensity_swap_apply q (G.metric t)
      (H1ComplDirichletToLp q (u t))
  have hUzero : U 0 = f₀ := by
    dsimp only [U, σ]
    rw [hVzero]
    exact smoothMulLp_volumeDensity_swap_apply q (G.metric 0) f₀
  exact ⟨U, hUcont, hUae, hUzero⟩

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
