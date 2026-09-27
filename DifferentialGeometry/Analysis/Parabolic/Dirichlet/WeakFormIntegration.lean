import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletWeakFormIntegration
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.WeakEvolution
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletWeakDerivative
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletSmoothMul
import DifferentialGeometry.Analysis.Integration.Measure.VolumeDensity
import DifferentialGeometry.Analysis.Integration.Lp.Pairing

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal InnerProductSpace Manifold RealInnerProductSpace Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Operator.WithBoundary
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

omit [T2Space M] [CompactSpace M] in
private theorem traceTimeDerivMetric_continuous
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_half n) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_half n) (M := M) D G.metric)
    {t : ℝ} (ht : t ∈ D.regular) :
    Continuous (fun x : M => traceTimeDerivMetric (I := I_half n) G.metric t x) := by
  have hj : ContinuousOn
      (fun p : ℝ × M => traceTimeDerivMetric (I := I_half n) G.metric p.1 p.2)
      (D.regular ×ˢ (Set.univ : Set M)) := by
    apply continuousOn_traceTimeDerivMetric_of_chartGram_contMDiffOn
      (I := I_half n) (M := M) (g := G.metric) D.regular_isOpen
    intro α i j
    exact hG.chartGramMatrix_contDiffOn (Set.Subset.rfl) α i j
  simpa only [Function.comp_def] using hj.comp_continuous
    (f := fun x : M => (t, x)) (continuous_const.prodMk continuous_id)
    (fun x => ⟨ht, Set.mem_univ x⟩)

private theorem dirichletMassVariationTest_memLp
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_half n) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_half n) (M := M) D G.metric)
    {t : ℝ} (ht : t ∈ D.regular) (v : SmoothScalarDirichlet q) :
    MemLp (fun x => (1 / 2 : ℝ) * traceTimeDerivMetric (I := I_half n) G.metric t x * v.toFun x)
      2 (riemannianVolumeMeasure (I := I_half n) (M := M) q) := by
  let _ : IsFiniteMeasureOnCompacts
      (riemannianVolumeMeasure (I := I_half n) (M := M) q) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I_half n) (M := M) q
  exact (((traceTimeDerivMetric_continuous hG ht).const_mul (1 / 2 : ℝ)).mul
    v.smooth.continuous).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem dirichletMassVariationCompl_apply_eq_integral
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_half n) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_half n) (M := M) D G.metric)
    {t : ℝ} (ht : t ∈ D.regular) (B : ℝ)
    (htrace : ∀ x : M, |traceTimeDerivMetric (I := I_half n) G.metric t x| ≤ B)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ w : TangentSpace (I_half n) x,
      Cg⁻¹ * q.inner x w w ≤ (G.metric t).inner x w w ∧
        (G.metric t).inner x w w ≤ Cg * q.inner x w w)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) (G.metric t) ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q)
    (u : H1ComplDirichlet q) (v : SmoothScalarDirichlet q) :
    dirichletMassVariationCompl hG ht B htrace hCg hequiv Cv hCv0 hCvtop hvol
        u (smoothToH1ComplDirichlet q v) =
      ∫ x, (1 / 2 : ℝ) * traceTimeDerivMetric (I := I_half n) G.metric t x *
        (H1ComplDirichletToLp q u x * v.toFun x)
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) (G.metric t)) := by
  let F := (dirichletMassVariationTest_memLp hG ht v).toLp
    (fun x => (1 / 2 : ℝ) * traceTimeDerivMetric (I := I_half n) G.metric t x * v.toFun x)
  have hac : riemannianVolumeMeasure (I := I_half n) (M := M) (G.metric t) ≪
      riemannianVolumeMeasure (I := I_half n) (M := M) q :=
    Measure.absolutelyContinuous_of_le_smul hvol
  have hF : (F : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I_half n) (M := M) (G.metric t)]
      fun x => (1 / 2 : ℝ) * traceTimeDerivMetric (I := I_half n) G.metric t x * v.toFun x :=
    hac.ae_eq (MemLp.coeFn_toLp (dirichletMassVariationTest_memLp hG ht v))
  have heq : ∀ w : H1ComplDirichlet q,
      dirichletMassVariationCompl hG ht B htrace hCg hequiv Cv hCv0 hCvtop hvol
          w (smoothToH1ComplDirichlet q v) =
        dirichletMassLp (G.metric t) Cv hCvtop hvol (H1ComplDirichletToLp q w) F := by
    intro w
    refine UniformSpace.Completion.induction_on (α := SmoothScalarDirichlet q) w
      (isClosed_eq (by fun_prop) (by fun_prop)) ?_
    intro w
    change dirichletMassVariationCompl hG ht B htrace hCg hequiv Cv hCv0 hCvtop hvol
        (smoothToH1ComplDirichlet q w) (smoothToH1ComplDirichlet q v) =
      dirichletMassLp (G.metric t) Cv hCvtop hvol
        (H1ComplDirichletToLp q (smoothToH1ComplDirichlet q w)) F
    rw [dirichletMassVariationCompl_apply_smooth, H1ComplDirichletToLp_smoothToH1ComplDirichlet,
      dirichletMassLp_apply_eq_integral]
    have hw : (smoothToLpDirichlet q w : M → ℝ) =ᵐ[
        riemannianVolumeMeasure (I := I_half n) (M := M) q] w.toFun :=
      MemLp.coeFn_toLp w.memLp_two
    apply integral_congr_ae
    filter_upwards [hac.ae_eq hw, hF] with x hwx hFx
    rw [hwx, hFx]
    ring
  rw [heq u, dirichletMassLp_apply_eq_integral]
  apply integral_congr_ae
  filter_upwards [hF] with x hx
  rw [hx]
  ring

theorem IsWeakEvolutionSolution.exists_timeH1_integral
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_half n) (M := M) D}
    {hG : MetricFamilySmoothOn (I := I_half n) (M := M) D G.metric}
    {T : ℝ} {hT : 0 ≤ T} {hreg : Icc (0 : ℝ) T ⊆ D.regular}
    {X : ℝ → Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯}
    {a : ℝ → ℝ} {Bx Bv : ℝ}
    {hX : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      (G.metric t).inner x (X t x) (X t x) ≤ Bx}
    {htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_half n) G.metric t x| ≤ Bv}
    {f₀ : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) q)}
    {u : timeL2 (H1ComplDirichlet q) T}
    (hu : IsWeakEvolutionSolution hG hT hreg X a Bx Bv hX htrace f₀ u)
    (v : SmoothScalarDirichlet q) :
    ∃ w : timeH1 ℝ T,
      w.initial = ∫ x, f₀ x * v.toFun x
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) (G.metric 0)) ∧
      (fun t => ∫ x, H1ComplDirichletToLp q (u t) x * v.toFun x
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) (G.metric t))) =ᵐ[
          timeMeasure T] w.toFun ∧
      w.deriv =ᵐ[timeMeasure T] fun t =>
        (∫ x, (1 / 2 : ℝ) * traceTimeDerivMetric (I := I_half n) G.metric t x *
          (H1ComplDirichletToLp q (u t) x * v.toFun x)
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) (G.metric t))) +
        ∫ x, H1ComplDirichletToLp q (u t) x *
          (ΔGWithBoundary (I := I_half n) (G.metric t) v.smooth v.interior_support x -
            tangentSectionAction (I := I_half n) (X t) v.toFun x -
            divergence (I := I_half n)
              (leviCivitaConnectionOfMetric (I := I_half n) (G.metric t)) (X t) x *
                v.toFun x - a t * v.toFun x)
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) (G.metric t)) := by
  obtain ⟨Cg, Cv, hCg, hequiv, hCv0, hCvtop, hvol, hsol⟩ := hu
  obtain ⟨w, hwinit, hwmass, hwderiv⟩ := hsol (smoothToH1ComplDirichlet q v)
  have hv : (smoothToLpDirichlet q v : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I_half n) (M := M) q] v.toFun :=
    MemLp.coeFn_toLp v.memLp_two
  have hmem : ∀ᵐ t ∂(timeMeasure T), t ∈ Ico (0 : ℝ) T := by
    unfold timeMeasure
    rw [← restrict_Ico_eq_restrict_Icc]
    exact ae_restrict_mem measurableSet_Ico
  refine ⟨w, ?_, ?_, ?_⟩
  · rw [hwinit, H1ComplDirichletToLp_smoothToH1ComplDirichlet,
      dirichletMassLp_apply_eq_integral]
    have hac : riemannianVolumeMeasure (I := I_half n) (M := M) (G.metric 0) ≪
        riemannianVolumeMeasure (I := I_half n) (M := M) q :=
      Measure.absolutelyContinuous_of_le_smul (hvol 0 ⟨le_rfl, hT⟩)
    apply integral_congr_ae
    filter_upwards [hac.ae_eq hv] with x hx
    rw [hx]
  · filter_upwards [hwmass, hmem] with t ht htc
    rw [dirichletMassComplOnIcc, dif_pos ⟨htc.1, htc.2.le⟩,
      dirichletMassCompl_apply_eq_integral,
      H1ComplDirichletToLp_smoothToH1ComplDirichlet] at ht
    refine Eq.trans ?_ ht
    have hac : riemannianVolumeMeasure (I := I_half n) (M := M) (G.metric t) ≪
        riemannianVolumeMeasure (I := I_half n) (M := M) q :=
      Measure.absolutelyContinuous_of_le_smul (hvol t ⟨htc.1, htc.2.le⟩)
    apply integral_congr_ae
    filter_upwards [hac.ae_eq hv] with x hx
    rw [hx]
  · filter_upwards [hwderiv, hmem] with t ht htc
    rw [ht, dirichletMassVariationComplOnIco, dif_pos htc,
      dirichletMassVariationCompl_apply_eq_integral,
      dirichletWeakFormComplOnIco, dif_pos htc,
      dirichletWeakFormCompl_apply_eq_integral_adjoint]

theorem dirichletMassVariationCompl_apply_eq_integral_volumeDensity
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := (I_half n)) (M := M) D}
    (hG : MetricFamilySmoothOn (I := (I_half n)) (M := M) D G.metric)
    {t : ℝ} (ht : t ∈ D.regular) (B : ℝ)
    (htrace : ∀ x : M, |traceTimeDerivMetric (I := (I_half n)) G.metric t x| ≤ B)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ w : TangentSpace (I_half n) x,
      Cg⁻¹ * q.inner x w w ≤ (G.metric t).inner x w w ∧
        (G.metric t).inner x w w ≤ Cg * q.inner x w w)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := (I_half n)) (M := M) (G.metric t) ≤
      Cv • riemannianVolumeMeasure (I := (I_half n)) (M := M) q)
    (u v : H1ComplDirichlet q) :
    dirichletMassVariationCompl hG ht B htrace hCg hequiv Cv hCv0 hCvtop hvol u v =
      ∫ x, H1ComplDirichletToLp q u x *
        (riemannianVolumeDensity q (G.metric t) x * ((1 / 2) *
          traceTimeDerivMetric (I := (I_half n)) G.metric t x)) * H1ComplDirichletToLp q v x
        ∂(riemannianVolumeMeasure (I := (I_half n)) (M := M) q) := by
  have htracej := continuousOn_traceTimeDerivMetric_of_chartGram_contMDiffOn
    D.regular_isOpen (fun α i j => hG.chartGramMatrix_contDiffOn Subset.rfl α i j)
  have htracec : Continuous (fun x : M => traceTimeDerivMetric (I := (I_half n)) G.metric t x) := by
    simpa only [Function.comp_def] using htracej.comp_continuous
      (f := fun x : M => (t, x)) (continuous_const.prodMk continuous_id)
      (fun x => ⟨ht, mem_univ x⟩)
  let c : M → ℝ := fun x => riemannianVolumeDensity q (G.metric t) x *
    ((1 / 2) * traceTimeDerivMetric (I := (I_half n)) G.metric t x)
  have hc : MemLp c ∞ (riemannianVolumeMeasure (I := (I_half n)) (M := M) q) :=
    ((riemannianVolumeDensitySmoothMap q (G.metric t)).contMDiff.continuous.mul
      ((continuous_const (y := (1 / 2 : ℝ))).mul htracec)).memLp_top_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _) (riemannianVolumeMeasure (I := (I_half n)) (M := M) q)
  refine (denseRange_smoothToH1ComplDirichlet q).induction_on v
    (isClosed_eq (dirichletMassVariationCompl hG ht B htrace hCg hequiv Cv hCv0 hCvtop hvol u).continuous
      ((continuous_integral_weight_mul_lp c hc (H1ComplDirichletToLp q u)).comp
        (H1ComplDirichletToLp q).continuous)) ?_
  intro v₀
  rw [dirichletMassVariationCompl_apply_eq_integral,
    integral_riemannianVolumeMeasure_eq_integral_volumeDensity_smul q (G.metric t),
    H1ComplDirichletToLp_smoothToH1ComplDirichlet]
  apply integral_congr_ae
  have hv₀ : (smoothToLpDirichlet q v₀ : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := (I_half n)) (M := M) q] v₀.toFun := MemLp.coeFn_toLp v₀.memLp_two
  filter_upwards [hv₀] with x hx
  rw [hx, smul_eq_mul]
  ring


end DifferentialGeometry.Analysis.Parabolic.Dirichlet
