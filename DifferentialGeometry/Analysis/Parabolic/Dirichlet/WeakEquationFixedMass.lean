import DifferentialGeometry.Analysis.Parabolic.Dirichlet.WeakEquationTimeTest
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.SmoothTimeMultiplier
import DifferentialGeometry.Analysis.Integration.Lp.Pairing

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

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

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private theorem dirichletMassCompl_volumeDensity_integrable
    (q h : SmoothRiemannianMetric I_hs M) (u v : H1ComplDirichlet q) :
    Integrable (fun x => riemannianVolumeDensity q h x *
      (H1ComplDirichletToLp q u x * H1ComplDirichletToLp q v x))
      (riemannianVolumeMeasure (I := I_hs) (M := M) q) := by
  have hc : MemLp (riemannianVolumeDensity q h) ∞
      (riemannianVolumeMeasure (I := I_hs) (M := M) q) :=
    (riemannianVolumeDensitySmoothMap q h).contMDiff.continuous.memLp_top_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _) _
  exact (integrable_weight_mul_lp _ hc (H1ComplDirichletToLp q u)
    (H1ComplDirichletToLp q v)).congr (Filter.Eventually.of_forall fun x => by ring)

private theorem dirichletMassVariationCompl_volumeDensity_integrable
    {q : SmoothRiemannianMetric I_hs M}
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric)
    {t : ℝ} (ht : t ∈ D.regular) (u v : H1ComplDirichlet q) :
    Integrable (fun x => H1ComplDirichletToLp q u x *
      (riemannianVolumeDensity q (G.metric t) x * ((1 / 2) *
        traceTimeDerivMetric (I := I_hs) G.metric t x)) * H1ComplDirichletToLp q v x)
      (riemannianVolumeMeasure (I := I_hs) (M := M) q) := by
  have htracej := continuousOn_traceTimeDerivMetric_of_chartGram_contMDiffOn
    D.regular_isOpen (fun α i j => hG.chartGramMatrix_contDiffOn Subset.rfl α i j)
  have htracec : Continuous (fun x : M => traceTimeDerivMetric (I := I_hs) G.metric t x) := by
    simpa only [Function.comp_def] using htracej.comp_continuous
      (f := fun x : M => (t, x)) (continuous_const.prodMk continuous_id)
      (fun x => ⟨ht, mem_univ x⟩)
  apply integrable_weight_mul_lp
  exact ((riemannianVolumeDensitySmoothMap q (G.metric t)).contMDiff.continuous.mul
    ((continuous_const (y := (1 / 2 : ℝ))).mul htracec)).memLp_top_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _) _

private theorem dirichletMassCompl_add_massVariationCompl_eq_inner_of_volumeDensity_swap
    {q : SmoothRiemannianMetric I_hs M}
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric)
    {t : ℝ} (ht : t ∈ D.regular) (B : ℝ)
    (htrace : ∀ x : M, |traceTimeDerivMetric (I := I_hs) G.metric t x| ≤ B)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ w : TangentSpace I_hs x,
      Cg⁻¹ * q.inner x w w ≤ (G.metric t).inner x w w ∧
        (G.metric t).inner x w w ≤ Cg * q.inner x w w)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_hs) (M := M) (G.metric t) ≤
      Cv • riemannianVolumeMeasure (I := I_hs) (M := M) q)
    (u z z' v d : H1ComplDirichlet q)
    (hv : v = smoothMulH1ComplDirichlet q (riemannianVolumeDensitySmoothMap (G.metric t) q) z)
    (hd : H1ComplDirichletToLp q d =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
      (fun x => -(1 / 2) * traceTimeDerivMetric (I := I_hs) G.metric t x *
        riemannianVolumeDensity (G.metric t) q x * H1ComplDirichletToLp q z x +
        riemannianVolumeDensity (G.metric t) q x * H1ComplDirichletToLp q z' x)) :
    dirichletMassCompl (G.metric t) hCg hequiv Cv hCv0 hCvtop hvol u d +
      dirichletMassVariationCompl hG ht B htrace hCg hequiv Cv hCv0 hCvtop hvol u v =
      inner ℝ (H1ComplDirichletToLp q u) (H1ComplDirichletToLp q z') := by
  rw [dirichletMassCompl_apply_eq_integral,
    integral_riemannianVolumeMeasure_eq_integral_volumeDensity_smul q (G.metric t),
    dirichletMassVariationCompl_apply_eq_integral_volumeDensity]
  simp only [smul_eq_mul]
  rw [← integral_add (dirichletMassCompl_volumeDensity_integrable q (G.metric t) u d)
    (dirichletMassVariationCompl_volumeDensity_integrable hG ht u v), L2.inner_def]
  have hvlp : H1ComplDirichletToLp q v =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
      fun x => riemannianVolumeDensity (G.metric t) q x * H1ComplDirichletToLp q z x := by
    rw [hv, H1ComplDirichletToLp_smoothMulH1ComplDirichlet]
    exact smoothMulLp_apply_coeFn q _ _
  apply integral_congr_ae
  filter_upwards [hd, hvlp] with x hdx hvx
  rw [hdx, hvx]
  simp only [Real.inner_apply]
  have hρ := riemannianVolumeDensity_mul_swap q (G.metric t) x
  calc
    _ = (riemannianVolumeDensity q (G.metric t) x * riemannianVolumeDensity (G.metric t) q x) *
        (H1ComplDirichletToLp q z' x * H1ComplDirichletToLp q u x) := by ring
    _ = _ := by rw [hρ, one_mul]; ring

theorem IsWeakEvolutionSolution.integral_timeH1_test_volumeDensity_swap
    {q : SmoothRiemannianMetric I_hs M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    {hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric}
    {T : ℝ} {hT : 0 ≤ T} {hreg : Icc (0 : ℝ) T ⊆ D.regular}
    {X : ℝ → Cₛ^∞⟮I_hs; EuclideanSpace ℝ (Fin n),
      (TangentSpace I_hs : M → Type _)⟯}
    (hXcont : ContinuousOn
      (fun p : ℝ × M ↦
        (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2) :
          TangentBundle I_hs M))
      (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    {a : ℝ → ℝ} (hacont : ContinuousOn a (Icc (0 : ℝ) T))
    {Bx Bv : ℝ}
    {hX : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      (G.metric t).inner x (X t x) (X t x) ≤ Bx}
    {htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_hs) G.metric t x| ≤ Bv}
    {f₀ : Lp ℝ 2
      (riemannianVolumeMeasure (I := I_hs) (M := M) q)}
    {u : timeL2 (H1ComplDirichlet q) T}
    (hu : IsWeakEvolutionSolution hG hT hreg X a Bx Bv
      hX htrace f₀ u) :
    ∃ Cg : ℝ, ∃ Cv : ℝ≥0∞,
      ∃ hCg : 1 ≤ Cg,
      ∃ hequiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
        ∀ v : TangentSpace I_hs x,
          Cg⁻¹ * q.inner x v v ≤ (G.metric t).inner x v v ∧
            (G.metric t).inner x v v ≤ Cg * q.inner x v v,
      ∃ hCv0 : Cv ≠ 0, ∃ hCvtop : Cv ≠ ⊤,
      ∃ hvol : ∀ t ∈ Icc (0 : ℝ) T,
        riemannianVolumeMeasure (I := I_hs) (M := M) (G.metric t) ≤
          Cv • riemannianVolumeMeasure (I := I_hs) (M := M) q,
      ∀ z : timeH1 (H1ComplDirichlet q) T, z.toFun T = 0 →
        (∫ t, inner ℝ (H1ComplDirichletToLp q (u t))
          (H1ComplDirichletToLp q (z.deriv t)) ∂timeMeasure T) +
        (∫ t, dirichletWeakFormComplOnIco G.metric X a Bx hX
          hCg hequiv Cv hCv0 hCvtop hvol t (u t)
            (smoothMulH1ComplDirichlet q
              (riemannianVolumeDensitySmoothMap (G.metric t) q) (z.toFun t))
          ∂timeMeasure T) = -inner ℝ f₀ (H1ComplDirichletToLp q z.init) := by
  obtain ⟨Cg, Cv, hCg, hequiv, hCv0, hCvtop, hvol, htest⟩ :=
    hu.integral_timeH1_test hXcont hacont
  refine ⟨Cg, Cv, hCg, hequiv, hCv0, hCvtop, hvol, ?_⟩
  intro z hzT
  obtain ⟨w, hwi, hw, hwd⟩ :=
    exists_timeH1_smoothMulH1ComplDirichlet_volumeDensity_swap q hG hT hreg z
  have hwT : w.toFun T = 0 := by
    rw [hw T ⟨hT, le_rfl⟩, hzT, map_zero]
  have htestw := htest w hwT
  let massForm := dirichletMassComplOnIcc G.metric hCg hequiv Cv hCv0 hCvtop hvol
  let variationForm := dirichletMassVariationComplOnIco hG hreg Bv htrace
    hCg hequiv Cv hCv0 hCvtop hvol
  let weakForm := dirichletWeakFormComplOnIco G.metric X a Bx hX
    hCg hequiv Cv hCv0 hCvtop hvol
  have hmmeas : ∀ y z, AEStronglyMeasurable
      (fun t => massForm t y z) (timeMeasure T) :=
    dirichletMassComplOnIcc_aestronglyMeasurable hG hreg hCg hequiv
      Cv hCv0 hCvtop hvol
  have hvmeas : ∀ y z, AEStronglyMeasurable
      (fun t => variationForm t y z) (timeMeasure T) :=
    dirichletMassVariationComplOnIco_aestronglyMeasurable hG hreg
      Bv htrace hCg hequiv Cv hCv0 hCvtop hvol
  have hfmeas : ∀ y z, AEStronglyMeasurable
      (fun t => weakForm t y z) (timeMeasure T) :=
    dirichletWeakFormComplOnIco_aestronglyMeasurable hG hreg X
      hXcont a hacont Bx hX hCg hequiv Cv hCv0 hCvtop hvol
  have hwLp : MemLp w.toFun 2 (timeMeasure T) :=
    memLp_of_continuousOn w.continuousOn_toFun
  have hmint : Integrable (fun t => massForm t (u t) (w.deriv t)) (timeMeasure T) :=
    MeasureTheory.integrable_bilinear_of_apply_aestronglyMeasurable massForm hmmeas
      (Eventually.of_forall fun t => norm_dirichletMassComplOnIcc_le
        G.metric hCg hequiv Cv hCv0 hCvtop hvol t) (Lp.memLp u) (Lp.memLp w.deriv)
  have hvint : Integrable (fun t => variationForm t (u t) (w.toFun t)) (timeMeasure T) :=
    MeasureTheory.integrable_bilinear_of_apply_aestronglyMeasurable variationForm hvmeas
      (Eventually.of_forall fun t => norm_dirichletMassVariationComplOnIco_le
        hG hreg Bv htrace hCg hequiv Cv hCv0 hCvtop hvol t) (Lp.memLp u) hwLp
  obtain ⟨A, hAbound⟩ := isCompact_Icc.exists_bound_of_continuousOn hacont
  have hA : 0 ≤ A := (norm_nonneg (a 0)).trans (hAbound 0 ⟨le_rfl, hT⟩)
  have haBound : ∀ t ∈ Ico (0 : ℝ) T, |a t| ≤ A := by
    intro t ht
    rw [← Real.norm_eq_abs]
    exact hAbound t ⟨ht.1, ht.2.le⟩
  have hfint : Integrable (fun t => weakForm t (u t) (w.toFun t)) (timeMeasure T) :=
    MeasureTheory.integrable_bilinear_of_apply_aestronglyMeasurable weakForm hfmeas
      (Eventually.of_forall fun t => norm_dirichletWeakFormComplOnIco_le
        G.metric X a A Bx hA haBound hX hCg hequiv Cv hCv0 hCvtop hvol t)
      (Lp.memLp u) hwLp
  have hmem : ∀ᵐ t ∂timeMeasure T, t ∈ Ico (0 : ℝ) T := by
    unfold timeMeasure
    rw [← restrict_Ico_eq_restrict_Icc]
    exact ae_restrict_mem measurableSet_Ico
  have hcancel : (fun t => massForm t (u t) (w.deriv t) +
      variationForm t (u t) (w.toFun t)) =ᵐ[timeMeasure T]
      (fun t => inner ℝ (H1ComplDirichletToLp q (u t))
        (H1ComplDirichletToLp q (z.deriv t))) := by
    filter_upwards [hwd, hmem] with t hdt ht
    have htc : t ∈ Icc (0 : ℝ) T := ⟨ht.1, ht.2.le⟩
    dsimp only [massForm, variationForm]
    rw [dirichletMassComplOnIcc, dif_pos htc,
      dirichletMassVariationComplOnIco, dif_pos ht]
    exact dirichletMassCompl_add_massVariationCompl_eq_inner_of_volumeDensity_swap
      hG (hreg htc) Bv (htrace t ht) hCg (hequiv t htc) Cv hCv0 hCvtop (hvol t htc)
      (u t) (z.toFun t) (z.deriv t) (w.toFun t) (w.deriv t) (hw t htc) hdt
  have hcint := integral_congr_ae hcancel
  rw [integral_add hmint hvint] at hcint
  have hfintEq : (∫ t, weakForm t (u t) (w.toFun t) ∂timeMeasure T) =
      ∫ t, weakForm t (u t) (smoothMulH1ComplDirichlet q
        (riemannianVolumeDensitySmoothMap (G.metric t) q) (z.toFun t)) ∂timeMeasure T := by
    apply integral_congr_ae
    filter_upwards [hmem] with t ht
    rw [hw t ⟨ht.1, ht.2.le⟩]
  have hinit : dirichletMassLp (G.metric 0) Cv hCvtop (hvol 0 ⟨le_rfl, hT⟩)
      f₀ (H1ComplDirichletToLp q w.init) = inner ℝ f₀ (H1ComplDirichletToLp q z.init) := by
    rw [hwi, H1ComplDirichletToLp_smoothMulH1ComplDirichlet,
      dirichletMassLp_smoothMul_volumeDensity_swap]
  change (∫ t, massForm t (u t) (w.deriv t) ∂timeMeasure T) +
    (∫ t, variationForm t (u t) (w.toFun t) + weakForm t (u t) (w.toFun t)
      ∂timeMeasure T) = _ at htestw
  rw [integral_add hvint hfint, hinit] at htestw
  change (∫ t, inner ℝ (H1ComplDirichletToLp q (u t))
      (H1ComplDirichletToLp q (z.deriv t)) ∂timeMeasure T) +
    (∫ t, weakForm t (u t) (smoothMulH1ComplDirichlet q
      (riemannianVolumeDensitySmoothMap (G.metric t) q) (z.toFun t)) ∂timeMeasure T) = _
  rw [← hcint, ← hfintEq, add_assoc]
  exact htestw

theorem IsWeakEvolutionSolution.integral_cutoff_steklovAverage_test_volumeDensity_swap
    {q : SmoothRiemannianMetric I_hs M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    {hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric}
    {T : ℝ} {hT : 0 ≤ T} {hreg : Icc (0 : ℝ) T ⊆ D.regular}
    {X : ℝ → Cₛ^∞⟮I_hs; EuclideanSpace ℝ (Fin n),
      (TangentSpace I_hs : M → Type _)⟯}
    (hXcont : ContinuousOn
      (fun p : ℝ × M ↦
        (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2) :
          TangentBundle I_hs M))
      (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    {a : ℝ → ℝ} (hacont : ContinuousOn a (Icc (0 : ℝ) T))
    {Bx Bv : ℝ}
    {hX : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      (G.metric t).inner x (X t x) (X t x) ≤ Bx}
    {htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_hs) G.metric t x| ≤ Bv}
    {f₀ : Lp ℝ 2
      (riemannianVolumeMeasure (I := I_hs) (M := M) q)}
    {u : timeL2 (H1ComplDirichlet q) T}
    (hu : IsWeakEvolutionSolution hG hT hreg X a Bx Bv
      hX htrace f₀ u) :
    ∃ Cg : ℝ, ∃ Cv : ℝ≥0∞,
      ∃ hCg : 1 ≤ Cg,
      ∃ hequiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
        ∀ v : TangentSpace I_hs x,
          Cg⁻¹ * q.inner x v v ≤ (G.metric t).inner x v v ∧
            (G.metric t).inner x v v ≤ Cg * q.inner x v v,
      ∃ hCv0 : Cv ≠ 0, ∃ hCvtop : Cv ≠ ⊤,
      ∃ hvol : ∀ t ∈ Icc (0 : ℝ) T,
        riemannianVolumeMeasure (I := I_hs) (M := M) (G.metric t) ≤
          Cv • riemannianVolumeMeasure (I := I_hs) (M := M) q,
      ∀ (L : H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q) (s : ℝ)
        (ζ : ℝ → ℝ), ContDiffOn ℝ 1 ζ (Icc (0 : ℝ) T) → ζ 0 = 0 → ζ T = 0 →
        let U := (Icc (0 : ℝ) T).indicator (fun t => u t)
        (∫ t, inner ℝ (H1ComplDirichletToLp q (u t))
          (H1ComplDirichletToLp q (L
            (_root_.deriv ζ t • steklovAverage s U t +
              ζ t • (s⁻¹ • (U (t + s) - U t))))) ∂timeMeasure T) +
        (∫ t, dirichletWeakFormComplOnIco G.metric X a Bx hX
          hCg hequiv Cv hCv0 hCvtop hvol t (u t)
            (smoothMulH1ComplDirichlet q
              (riemannianVolumeDensitySmoothMap (G.metric t) q)
              (L (ζ t • steklovAverage s U t))) ∂timeMeasure T) = 0 := by
  obtain ⟨Cg, Cv, hCg, hequiv, hCv0, hCvtop, hvol, htest⟩ :=
    hu.integral_timeH1_test_volumeDensity_swap hXcont hacont
  refine ⟨Cg, Cv, hCg, hequiv, hCv0, hCvtop, hvol, ?_⟩
  intro L s ζ hζ hζ0 hζT
  obtain ⟨v, hvi, hv, hvd, hvT⟩ :=
    exists_timeH1_cutoff_steklovAverage_timeL2 hT u s hζ hζ0 hζT
  let : NormedAddCommGroup (H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q) :=
    ContinuousLinearMap.toNormedAddCommGroup
  obtain ⟨w, hwi, hw, hwd⟩ := exists_timeH1_clm_apply_of_contDiffOn hT
    (contDiffOn_const (c := L)) v
  have hwT : w.toFun T = 0 := by rw [hw T ⟨hT, le_rfl⟩, hvT, map_zero]
  have h := htest w hwT
  have hinit : w.init = 0 := by rw [hwi, hvi, map_zero]
  rw [hinit, map_zero, inner_zero_right, neg_zero] at h
  refine Eq.trans ?_ h
  apply congrArg₂ (fun a b : ℝ => a + b)
  · apply integral_congr_ae
    filter_upwards [hwd, hvd] with t hwt hvt
    rw [hwt, deriv_const, zero_apply, zero_add, hvt]
  · apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [hw t ht, hv t ht]

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
