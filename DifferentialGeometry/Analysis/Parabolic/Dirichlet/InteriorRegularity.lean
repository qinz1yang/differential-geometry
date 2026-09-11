import DifferentialGeometry.Analysis.Sobolev.WeakDerivativeCommutation
import DifferentialGeometry.Analysis.Sobolev.Euclidean.DivergenceForm
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.WeakPartial
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.NirenbergEnergy
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.NirenbergEstimate
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.WeakEquationLocal
import DifferentialGeometry.Analysis.Parabolic.Energy.TimeCutoff
import DifferentialGeometry.Analysis.Sobolev.Tools.CutoffDiffQuotLp
import DifferentialGeometry.Analysis.Sobolev.Tools.DifferenceQuotientProductWeakLimitLocal
import DifferentialGeometry.Analysis.Sobolev.Chart.ChartDensityCutoff

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold NNReal Topology

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

theorem exists_uniform_integral_cutoff_diffQuot_weakPartial_le
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
    {hX : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      (G.metric t).inner x (X t x) (X t x) ≤ Bx}
    {htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_hs) G.metric t x| ≤ Bv}
    (α : M) {Ω Ω' Ω'' : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuclideanSpace ℝ (Fin n)) '' interior (extChartAt I_hs α).target)
    (hΩ' : IsOpen Ω') (hΩ'' : IsOpen Ω'')
    (hΩ'c : IsCompact (closure Ω')) (hΩ'Ω : closure Ω' ⊆ Ω)
    (hΩ''c : IsCompact (closure Ω''))
    {η : EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))) → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Ω'') {r : ℝ} (hr : 0 < r)
    (hroom : Metric.cthickening r (closure Ω'') ⊆ Ω')
    (φ : C^∞⟮I_hs, M; ℝ⟯)
    (hφ : ∀ z ∈ Ω, chartDensity (I := I_hs) q α
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuclideanSpace ℝ (Fin n))).symm z)) *
        φ ((extChartAt I_hs α).symm ((toEuclidean (E := EuclideanSpace ℝ (Fin n))).symm z)) = 1)
    (hXsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) ((I_hs).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2))
      (D.regular ×ˢ (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I_hs) α).baseSet))
    (hηb : ∀ z, |η z| ≤ 1)
    {lam : ℝ} (hlam : 0 < lam)
    (hcoer : ∀ t ∈ Icc (0 : ℝ) T, ∀ y ∈ Ω,
      ∀ ξ : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) → ℝ,
      lam * ∑ i, (ξ i)^2 ≤ ∑ i, ∑ j,
        DifferentialGeometry.Analysis.Laplacian.MetricExtension.invGramOnEuclid (I := I_hs)
          (G.metric t) α i j y * ξ i * ξ j) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀
      (f₀ : Lp ℝ 2
      (riemannianVolumeMeasure (I := I_hs) (M := M) q))
      (u : timeL2 (H1ComplDirichlet q) T), IsWeakEvolutionSolution hG hT hreg X a Bx Bv
        (fun t ht => hX t ⟨ht.1, ht.2.le⟩) htrace f₀ u →
      ∀ (k : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))) (h : ℝ), |h| ≤ δ →
        ∀ (ζ : ℝ → ℝ) (K : ℝ≥0), ContDiff ℝ 1 ζ → MemLp ζ ∞ volume →
        (∀ t, 0 ≤ ζ t) → (∀ t, ζ t ≤ 1) → LipschitzWith K ζ → ζ 0 = 0 → ζ T = 0 →
        (∫ t, ζ t * (∑ i, ∫ z, (η z * DifferentialGeometry.Analysis.Sobolev.diffQuot k h
          (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) z)^2) ∂timeMeasure T) ≤
          C * ((K : ℝ) + 1) * ∫ t, ‖u t‖ ^ 2 ∂timeMeasure T := by
  obtain ⟨CE, hCE, hEnergy⟩ :=
    exists_uniform_integral_cutoff_volumeDensity_nirenbergTest_le
      (hG := hG) (hT := hT) (hreg := hreg)
      (hX := fun t ht => hX t ⟨ht.1, ht.2.le⟩) (htrace := htrace)
      hXcont hacont α hΩ hΩc hΩs hΩ' hΩ'' hΩ'c hΩ'Ω hΩ''c hη hηc hηs hr hroom φ hφ
  have hηΩ := hηs.trans (subset_closure.trans
    ((Metric.self_subset_cthickening (δ := r) (closure Ω'')).trans
      (hroom.trans (subset_closure.trans hΩ'Ω))))
  obtain ⟨δ, hδ, CF, hCF, hδroom, hpoint⟩ :=
    exists_dirichletWeakFormCompl_nirenberg_lower_bound hG isCompact_Icc hreg q α
      hΩ hΩc hΩs X hXsmooth a hacont Bx hX
      φ hφ hη hηc hηΩ hηb hlam hcoer
  refine ⟨min δ r, lt_min hδ hr, 2 * (CE + CF) / lam, by positivity, ?_⟩
  intro f₀ u hu
  obtain ⟨Cg, Cv, hCg, hequiv, hCv0, hCvtop, hvol, hE⟩ := hEnergy f₀ u hu
  have hpoint' := hpoint Cg hCg hequiv Cv hCv0 hCvtop hvol
  intro k h hh ζ K hζsmooth hζ hζpos hζone hζlip hζ0 hζT
  have hhδ := hh.trans (min_le_left _ _)
  have hhr := hh.trans (min_le_right _ _)
  have htest := hE k h hhr ζ K hζsmooth hζ
    (Eventually.of_forall hζpos) hζlip hζ0 hζT
  let N := dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k h
    ((Metric.cthickening_mono hhδ _).trans hδroom)
  let F₀ := dirichletWeakFormComplOnIco G.metric X a Bx
    (fun t ht => hX t ⟨ht.1, ht.2.le⟩) hCg hequiv Cv hCv0 hCvtop hvol
  let S := fun t => smoothMulH1ComplDirichlet q
    (riemannianVolumeDensitySmoothMap (G.metric t) q)
  let L := (smoothMulH1ComplDirichlet q φ).comp N
  let W := fun t => F₀ t (u t) (S t (L (u t)))
  let E := fun t => ∑ i, ∫ z, (η z * DifferentialGeometry.Analysis.Sobolev.diffQuot k h
    (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) z)^2
  have hS : ContinuousOn S (Icc (0 : ℝ) T) := by
    let : NormedAddCommGroup (H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q) :=
      ContinuousLinearMap.toNormedAddCommGroup
    exact ((contDiffOn_one_smoothMulH1ComplDirichlet q _ D.regular_isOpen
      (riemannianVolumeDensity_swap_contMDiffOn_of_metricFamilySmoothOn hG q)).mono hreg).continuousOn
  have hF₀ : ∀ y z, AEStronglyMeasurable (fun t => F₀ t y z) (timeMeasure T) :=
    dirichletWeakFormComplOnIco_aestronglyMeasurable hG hreg X hXcont a hacont Bx
      (fun t ht => hX t ⟨ht.1, ht.2.le⟩) hCg hequiv Cv hCv0 hCvtop hvol
  obtain ⟨Ca, hCa⟩ := isCompact_Icc.exists_bound_of_continuousOn hacont
  have hCa0 : 0 ≤ Ca := (norm_nonneg (a 0)).trans (hCa 0 ⟨le_rfl, hT⟩)
  have haB : ∀ t ∈ Ico (0 : ℝ) T, |a t| ≤ Ca := by
    intro t ht
    simpa only [Real.norm_eq_abs] using hCa t ⟨ht.1, ht.2.le⟩
  have hFbound : ∀ᵐ t ∂timeMeasure T, ‖F₀ t‖ ≤
      (1 + Real.sqrt (max Bx 0) + Ca) * (Cv.toReal * Cg) :=
    Eventually.of_forall fun t => norm_dirichletWeakFormComplOnIco_le G.metric X a Ca Bx
      hCa0 haB (fun t ht => hX t ⟨ht.1, ht.2.le⟩) hCg hequiv Cv hCv0 hCvtop hvol t
  have hWI : Integrable W (timeMeasure T) :=
    integrable_bilinear_clm_apply_right F₀ hF₀ hFbound S hS L u u
  have hηLp : MemLp η ∞ volume := hη.continuous.memLp_of_hasCompactSupport hηc
  have hEI : Integrable E (timeMeasure T) := by
    apply integrable_finsetSum _
    intro i _
    exact DifferentialGeometry.Analysis.Sobolev.integrable_integral_sq_cutoff_diffQuot_comp
      hΩ.measurableSet hηLp k h ((Metric.cthickening_mono hhδ _).trans hδroom)
      (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i) (Lp.memLp u)
  have huI : Integrable (fun t => ‖u t‖ ^ 2) (timeMeasure T) := (Lp.memLp u).norm.integrable_sq
  have hζI : MemLp ζ ∞ (timeMeasure T) := hζ.restrict _
  have hζWI : Integrable (fun t => ζ t * W t) (timeMeasure T) :=
    (hWI.mul_of_top_right hζI).congr (Eventually.of_forall fun _ => rfl)
  have hζEI : Integrable (fun t => ζ t * E t) (timeMeasure T) :=
    (hEI.mul_of_top_right hζI).congr (Eventually.of_forall fun _ => rfl)
  have hpair (t : ℝ) : S t (L (u t)) = smoothMulH1ComplDirichlet q
      (riemannianVolumeDensitySmoothMap (G.metric t) q * φ) (N (u t)) := by
    change ((smoothMulH1ComplDirichlet q (riemannianVolumeDensitySmoothMap (G.metric t) q)).comp
      (smoothMulH1ComplDirichlet q φ)) _ = _
    rw [smoothMulH1ComplDirichlet_mul]
    rfl
  have hpointAE : ∀ᵐ t ∂timeMeasure T, lam / 2 * E t ≤ W t + CF * ‖u t‖^2 := by
    have hmem : ∀ᵐ t ∂timeMeasure T, t ∈ Ico (0 : ℝ) T := by
      unfold timeMeasure
      rw [← restrict_Ico_eq_restrict_Icc]
      exact ae_restrict_mem measurableSet_Ico
    filter_upwards [hmem] with t ht
    have hb := hpoint' t ⟨ht.1, ht.2.le⟩ k h hhδ (u t)
    change lam / 2 * E t ≤ F₀ t (u t) (S t (L (u t))) + _
    rw [hpair]
    dsimp only [F₀]
    rw [dirichletWeakFormComplOnIco, dif_pos ht]
    exact hb
  have hInt : lam / 2 * (∫ t, ζ t * E t ∂timeMeasure T) ≤
      (∫ t, ζ t * W t ∂timeMeasure T) + CF * ∫ t, ‖u t‖^2 ∂timeMeasure T := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add hζWI (huI.const_mul CF)]
    apply integral_mono_ae (hζEI.const_mul _) (hζWI.add (huI.const_mul CF))
    filter_upwards [hpointAE] with t ht
    have hb := mul_le_mul_of_nonneg_left ht (hζpos t)
    have herr := mul_le_mul_of_nonneg_right (hζone t) (mul_nonneg hCF (sq_nonneg ‖u t‖))
    change lam / 2 * (ζ t * E t) ≤ ζ t * W t + CF * ‖u t‖ ^ 2
    nlinarith
  have htest' : (∫ t, ζ t * W t ∂timeMeasure T) ≤ CE * (K : ℝ) * ∫ t, ‖u t‖^2 ∂timeMeasure T := by
    change (∫ t, ζ t * F₀ t (u t) (S t (L (u t))) ∂timeMeasure T) ≤ _
    simp_rw [hpair]
    exact htest
  have hnormpos : 0 ≤ ∫ t, ‖u t‖^2 ∂timeMeasure T := integral_nonneg fun _ => sq_nonneg _
  have hcoef : CE * (K : ℝ) + CF ≤ (CE + CF) * ((K : ℝ) + 1) := by nlinarith [K.coe_nonneg]
  have hb := hInt.trans (add_le_add htest' le_rfl)
  have hc := mul_le_mul_of_nonneg_right hcoef hnormpos
  have htarget : lam / 2 * (∫ t, ζ t * E t ∂timeMeasure T) ≤
      (CE + CF) * ((K : ℝ) + 1) * ∫ t, ‖u t‖ ^ 2 ∂timeMeasure T := by nlinarith
  have hfinal : (∫ t, ζ t * E t ∂timeMeasure T) ≤
      ((CE + CF) * ((K : ℝ) + 1) * ∫ t, ‖u t‖ ^ 2 ∂timeMeasure T) / (lam / 2) := by
    apply (le_div_iff₀ (show 0 < lam / 2 by positivity)).mpr
    rw [mul_comm]
    exact htarget
  convert hfinal using 1
  field_simp

theorem IsWeakEvolutionSolution.exists_integral_cutoff_diffQuot_weakPartial_le
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
    {hX : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      (G.metric t).inner x (X t x) (X t x) ≤ Bx}
    {htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_hs) G.metric t x| ≤ Bv}
    {f₀ : Lp ℝ 2
      (riemannianVolumeMeasure (I := I_hs) (M := M) q)}
    {u : timeL2 (H1ComplDirichlet q) T}
    (α : M) {Ω Ω' Ω'' : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuclideanSpace ℝ (Fin n)) '' interior (extChartAt I_hs α).target)
    (hΩ' : IsOpen Ω') (hΩ'' : IsOpen Ω'')
    (hΩ'c : IsCompact (closure Ω')) (hΩ'Ω : closure Ω' ⊆ Ω)
    (hΩ''c : IsCompact (closure Ω''))
    {η : EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))) → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Ω'') {r : ℝ} (hr : 0 < r)
    (hroom : Metric.cthickening r (closure Ω'') ⊆ Ω')
    (φ : C^∞⟮I_hs, M; ℝ⟯)
    (hφ : ∀ z ∈ Ω, chartDensity (I := I_hs) q α
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuclideanSpace ℝ (Fin n))).symm z)) *
        φ ((extChartAt I_hs α).symm ((toEuclidean (E := EuclideanSpace ℝ (Fin n))).symm z)) = 1)
    (hu : IsWeakEvolutionSolution hG hT hreg X a Bx Bv
      (fun t ht => hX t ⟨ht.1, ht.2.le⟩) htrace f₀ u)
    (hXsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) ((I_hs).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2))
      (D.regular ×ˢ (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I_hs) α).baseSet))
    (hηb : ∀ z, |η z| ≤ 1)
    {lam : ℝ} (hlam : 0 < lam)
    (hcoer : ∀ t ∈ Icc (0 : ℝ) T, ∀ y ∈ Ω,
      ∀ ξ : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) → ℝ,
      lam * ∑ i, (ξ i)^2 ≤ ∑ i, ∑ j,
        DifferentialGeometry.Analysis.Laplacian.MetricExtension.invGramOnEuclid (I := I_hs)
          (G.metric t) α i j y * ξ i * ξ j) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (k : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))) (h : ℝ), |h| ≤ δ →
        ∀ (ζ : ℝ → ℝ) (K : ℝ≥0), ContDiff ℝ 1 ζ → MemLp ζ ∞ volume →
        (∀ t, 0 ≤ ζ t) → (∀ t, ζ t ≤ 1) → LipschitzWith K ζ → ζ 0 = 0 → ζ T = 0 →
        (∫ t, ζ t * (∑ i, ∫ z, (η z * DifferentialGeometry.Analysis.Sobolev.diffQuot k h
          (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) z)^2) ∂timeMeasure T) ≤
          C * ((K : ℝ) + 1) * ∫ t, ‖u t‖ ^ 2 ∂timeMeasure T := by
  obtain ⟨δ, hδ, C, hC, hbound⟩ := exists_uniform_integral_cutoff_diffQuot_weakPartial_le
    (hG := hG) (hT := hT) (hreg := hreg) (hX := hX) (htrace := htrace)
    hXcont hacont α hΩ hΩc hΩs hΩ' hΩ'' hΩ'c hΩ'Ω hΩ''c
      hη hηc hηs hr hroom φ hφ hXsmooth hηb hlam hcoer
  exact ⟨δ, hδ, C, hC, hbound f₀ u hu⟩

theorem exists_uniform_integral_Icc_diffQuot_weakPartial_le
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
    {hX : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      (G.metric t).inner x (X t x) (X t x) ≤ Bx}
    {htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_hs) G.metric t x| ≤ Bv}
    (α : M) {Ω Ω' Ω'' : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuclideanSpace ℝ (Fin n)) '' interior (extChartAt I_hs α).target)
    (hΩ' : IsOpen Ω') (hΩ'' : IsOpen Ω'')
    (hΩ'c : IsCompact (closure Ω')) (hΩ'Ω : closure Ω' ⊆ Ω)
    (hΩ''c : IsCompact (closure Ω''))
    {η : EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))) → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Ω'') {r : ℝ} (hr : 0 < r)
    (hroom : Metric.cthickening r (closure Ω'') ⊆ Ω')
    (φ : C^∞⟮I_hs, M; ℝ⟯)
    (hφ : ∀ z ∈ Ω, chartDensity (I := I_hs) q α
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuclideanSpace ℝ (Fin n))).symm z)) *
        φ ((extChartAt I_hs α).symm ((toEuclidean (E := EuclideanSpace ℝ (Fin n))).symm z)) = 1)
    (hXsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) ((I_hs).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2))
      (D.regular ×ˢ (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I_hs) α).baseSet))
    (hηb : ∀ z, |η z| ≤ 1)
    {lam : ℝ} (hlam : 0 < lam)
    (hcoer : ∀ t ∈ Icc (0 : ℝ) T, ∀ y ∈ Ω,
      ∀ ξ : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) → ℝ,
      lam * ∑ i, (ξ i)^2 ≤ ∑ i, ∑ j,
        DifferentialGeometry.Analysis.Laplacian.MetricExtension.invGramOnEuclid (I := I_hs)
          (G.metric t) α i j y * ξ i * ξ j)
    {t₀ t₁ : ℝ} (ht₀ : 0 < t₀) (ht₁ : t₁ < T) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀
      (f₀ : Lp ℝ 2
      (riemannianVolumeMeasure (I := I_hs) (M := M) q))
      (u : timeL2 (H1ComplDirichlet q) T), IsWeakEvolutionSolution hG hT hreg X a Bx Bv
        (fun t ht => hX t ⟨ht.1, ht.2.le⟩) htrace f₀ u →
      ∀ (k : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))) (h : ℝ), |h| ≤ δ →
        (∫ t in Icc t₀ t₁, (∑ i, ∫ z, (η z * DifferentialGeometry.Analysis.Sobolev.diffQuot k h
          (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) z)^2) ∂timeMeasure T) ≤
          C * ∫ t, ‖u t‖ ^ 2 ∂timeMeasure T := by
  obtain ⟨δ, hδ, C, hC, hbound⟩ :=
    exists_uniform_integral_cutoff_diffQuot_weakPartial_le
      (hG := hG) (hT := hT) (hreg := hreg) (hX := hX) (htrace := htrace) hXcont hacont α hΩ hΩc hΩs
      hΩ' hΩ'' hΩ'c hΩ'Ω hΩ''c hη hηc hηs hr hroom φ hφ hXsmooth hηb hlam hcoer
  obtain ⟨ζ, K, hζsmooth, hζc, hζpos, hζb, hζlip, hζ0, hζT, hζone⟩ :=
    DifferentialGeometry.Analysis.Parabolic.Energy.exists_smooth_timeCutoff_eq_one_on_Icc ht₀ ht₁
  have hζ : MemLp ζ ∞ volume := hζsmooth.continuous.memLp_of_hasCompactSupport hζc
  refine ⟨min δ r, lt_min hδ hr, C * ((K : ℝ) + 1), by positivity, ?_⟩
  intro f₀ u hu
  have hbound' := hbound f₀ u hu
  intro k h hh
  have hhδ : |h| ≤ δ := hh.trans (min_le_left _ _)
  have hhr : |h| ≤ r := hh.trans (min_le_right _ _)
  have hroom' : Metric.cthickening |h| (tsupport η) ⊆ Ω :=
    (Metric.cthickening_mono hhr _).trans
      ((Metric.cthickening_subset_of_subset r (hηs.trans subset_closure)).trans
        (hroom.trans (subset_closure.trans hΩ'Ω)))
  let E := fun t => ∑ i, ∫ z, (η z * DifferentialGeometry.Analysis.Sobolev.diffQuot k h
    (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) z)^2
  have hEI : Integrable E (timeMeasure T) := by
    apply integrable_finsetSum _
    intro i _
    exact DifferentialGeometry.Analysis.Sobolev.integrable_integral_sq_cutoff_diffQuot_comp
      hΩ.measurableSet (hη.continuous.memLp_of_hasCompactSupport hηc) k h hroom'
      (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i) (Lp.memLp u)
  have hEpos : ∀ t, 0 ≤ E t := fun _ => Finset.sum_nonneg fun _ _ =>
    integral_nonneg fun _ => sq_nonneg _
  exact (DifferentialGeometry.Analysis.Parabolic.Energy.integral_Icc_le_integral_mul_cutoff
    hEI hEpos (hζ.restrict _) hζpos hζone).trans
      (hbound' k h hhδ ζ K (hζsmooth.of_le (by simp)) hζ hζpos hζb hζlip hζ0 hζT)

theorem IsWeakEvolutionSolution.exists_integral_Icc_diffQuot_weakPartial_le
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
    {hX : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      (G.metric t).inner x (X t x) (X t x) ≤ Bx}
    {htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_hs) G.metric t x| ≤ Bv}
    {f₀ : Lp ℝ 2
      (riemannianVolumeMeasure (I := I_hs) (M := M) q)}
    {u : timeL2 (H1ComplDirichlet q) T}
    (α : M) {Ω Ω' Ω'' : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuclideanSpace ℝ (Fin n)) '' interior (extChartAt I_hs α).target)
    (hΩ' : IsOpen Ω') (hΩ'' : IsOpen Ω'')
    (hΩ'c : IsCompact (closure Ω')) (hΩ'Ω : closure Ω' ⊆ Ω)
    (hΩ''c : IsCompact (closure Ω''))
    {η : EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))) → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Ω'') {r : ℝ} (hr : 0 < r)
    (hroom : Metric.cthickening r (closure Ω'') ⊆ Ω')
    (φ : C^∞⟮I_hs, M; ℝ⟯)
    (hφ : ∀ z ∈ Ω, chartDensity (I := I_hs) q α
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuclideanSpace ℝ (Fin n))).symm z)) *
        φ ((extChartAt I_hs α).symm ((toEuclidean (E := EuclideanSpace ℝ (Fin n))).symm z)) = 1)
    (hu : IsWeakEvolutionSolution hG hT hreg X a Bx Bv
      (fun t ht => hX t ⟨ht.1, ht.2.le⟩) htrace f₀ u)
    (hXsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) ((I_hs).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2))
      (D.regular ×ˢ (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I_hs) α).baseSet))
    (hηb : ∀ z, |η z| ≤ 1)
    {lam : ℝ} (hlam : 0 < lam)
    (hcoer : ∀ t ∈ Icc (0 : ℝ) T, ∀ y ∈ Ω,
      ∀ ξ : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) → ℝ,
      lam * ∑ i, (ξ i)^2 ≤ ∑ i, ∑ j,
        DifferentialGeometry.Analysis.Laplacian.MetricExtension.invGramOnEuclid (I := I_hs)
          (G.metric t) α i j y * ξ i * ξ j)
    {t₀ t₁ : ℝ} (ht₀ : 0 < t₀) (ht₁ : t₁ < T) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (k : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))) (h : ℝ), |h| ≤ δ →
        (∫ t in Icc t₀ t₁, (∑ i, ∫ z, (η z * DifferentialGeometry.Analysis.Sobolev.diffQuot k h
          (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) z)^2) ∂timeMeasure T) ≤
          C * ∫ t, ‖u t‖ ^ 2 ∂timeMeasure T := by
  obtain ⟨δ, hδ, C, hC, hbound⟩ := exists_uniform_integral_Icc_diffQuot_weakPartial_le
    (hG := hG) (hT := hT) (hreg := hreg) (hX := hX) (htrace := htrace)
    hXcont hacont α hΩ hΩc hΩs hΩ' hΩ'' hΩ'c hΩ'Ω hΩ''c
      hη hηc hηs hr hroom φ hφ hXsmooth hηb hlam hcoer ht₀ ht₁
  exact ⟨δ, hδ, C, hC, hbound f₀ u hu⟩

theorem IsWeakEvolutionSolution.exists_ae_hasWeakPartialDeriv_localWeakPartial
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
    {hX : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      (G.metric t).inner x (X t x) (X t x) ≤ Bx}
    {htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_hs) G.metric t x| ≤ Bv}
    {f₀ : Lp ℝ 2
      (riemannianVolumeMeasure (I := I_hs) (M := M) q)}
    {u : timeL2 (H1ComplDirichlet q) T}
    (α : M) {Ω Ω' Ω'' : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuclideanSpace ℝ (Fin n)) '' interior (extChartAt I_hs α).target)
    (hΩ' : IsOpen Ω') (hΩ'' : IsOpen Ω'')
    (hΩ'c : IsCompact (closure Ω')) (hΩ'Ω : closure Ω' ⊆ Ω)
    (hΩ''c : IsCompact (closure Ω''))
    {η : EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))) → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Ω'') {r : ℝ} (hr : 0 < r)
    (hroom : Metric.cthickening r (closure Ω'') ⊆ Ω')
    (φ : C^∞⟮I_hs, M; ℝ⟯)
    (hφ : ∀ z ∈ Ω, chartDensity (I := I_hs) q α
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuclideanSpace ℝ (Fin n))).symm z)) *
        φ ((extChartAt I_hs α).symm ((toEuclidean (E := EuclideanSpace ℝ (Fin n))).symm z)) = 1)
    (hu : IsWeakEvolutionSolution hG hT hreg X a Bx Bv
      (fun t ht => hX t ⟨ht.1, ht.2.le⟩) htrace f₀ u)
    (hXsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) ((I_hs).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2))
      (D.regular ×ˢ (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I_hs) α).baseSet))
    (hηb : ∀ z, |η z| ≤ 1)
    {lam : ℝ} (hlam : 0 < lam)
    (hcoer : ∀ t ∈ Icc (0 : ℝ) T, ∀ y ∈ Ω,
      ∀ ξ : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) → ℝ,
      lam * ∑ i, (ξ i)^2 ≤ ∑ i, ∑ j,
        DifferentialGeometry.Analysis.Laplacian.MetricExtension.invGramOnEuclid (I := I_hs)
          (G.metric t) α i j y * ξ i * ξ j)
    {t₀ t₁ : ℝ} (ht₀ : 0 < t₀) (ht₁ : t₁ < T)
    {Ω₀ : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩ₀ : IsOpen Ω₀) (hηone : ∀ z ∈ Ω₀, η z = 1) :
    ∀ i k : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))),
      ∃ v : Lp ℝ 2 (((timeMeasure T).restrict (Icc t₀ t₁)).prod (volume.restrict Ω₀)),
        ∀ᵐ t ∂(timeMeasure T).restrict (Icc t₀ t₁), DeGiorgi.HasWeakPartialDeriv k
          (fun z => v (t, z)) (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) Ω₀ := by
  obtain ⟨δ, hδ, C, hC, hbound⟩ :=
    hu.exists_integral_Icc_diffQuot_weakPartial_le hXcont hacont α hΩ hΩc hΩs
      hΩ' hΩ'' hΩ'c hΩ'Ω hΩ''c hη hηc hηs hr hroom φ hφ hXsmooth hηb hlam hcoer ht₀ ht₁
  let μ := (timeMeasure T).restrict (Icc t₀ t₁)
  have huμ : MemLp u 2 μ := (Lp.memLp u).mono_measure Measure.restrict_le_self
  let uμ : Lp (H1ComplDirichlet q) 2 μ := huμ.toLp u
  have huμeq : uμ =ᵐ[μ] u := huμ.coeFn_toLp
  intro i k
  let A := dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i
  let w := dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs μ i uμ
  have hw : MemLp w 2 (μ.prod (volume.restrict Ω)) := Lp.memLp w
  obtain ⟨L, hL, hinverse⟩ :=
    DifferentialGeometry.Analysis.Sobolev.exists_ae_hasWeakPartialDeriv_of_integral_sq_diffQuot_cutoff_le
      (μ := μ) (hη.of_le (by simp)) hηc
  have hroom' : Metric.cthickening (min δ r) (tsupport η) ⊆ Ω :=
    (Metric.cthickening_mono (min_le_right δ r) _).trans
      ((Metric.cthickening_subset_of_subset r (hηs.trans subset_closure)).trans
        (hroom.trans (subset_closure.trans hΩ'Ω)))
  have hnorm : ∀ h : ℝ, 0 < |h| → |h| ≤ min δ r →
      (∫ t, (∫ z, (η z * DifferentialGeometry.Analysis.Sobolev.diffQuot k h
        (fun y => w (t, y)) z)^2) ∂μ) ≤ C * ∫ t, ‖u t‖ ^ 2 ∂timeMeasure T := by
    intro h hhpos hh
    have hroomh : Metric.cthickening |h| (tsupport η) ⊆ Ω :=
      (Metric.cthickening_mono hh _).trans hroom'
    have heq := DifferentialGeometry.Analysis.Sobolev.integral_sq_cutoff_diffQuot_uncurry_compLpL
      hΩ.measurableSet A uμ η k h hroomh
    change (∫ t, (∫ z, (η z * DifferentialGeometry.Analysis.Sobolev.diffQuot k h
      (fun y => Lp.uncurry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (A.compLpL 2 μ uμ) (t,y)) z)^2) ∂μ) ≤ _
    rw [heq]
    have hcoe : (∫ t, (∫ z, (η z * DifferentialGeometry.Analysis.Sobolev.diffQuot k h
        (A (uμ t)) z)^2) ∂μ) =
        ∫ t, (∫ z, (η z * DifferentialGeometry.Analysis.Sobolev.diffQuot k h
        (A (u t)) z)^2) ∂μ := by
      apply integral_congr_ae
      filter_upwards [huμeq] with t ht
      rw [ht]
    rw [hcoe]
    have hηLp : MemLp η ∞ volume := hη.continuous.memLp_of_hasCompactSupport hηc
    have hI (j) : Integrable (fun t => ∫ z, (η z * DifferentialGeometry.Analysis.Sobolev.diffQuot k h
      (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j (u t)) z)^2) μ :=
      DifferentialGeometry.Analysis.Sobolev.integrable_integral_sq_cutoff_diffQuot_comp
        hΩ.measurableSet hηLp k h hroomh
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j) huμ
    have hmono : (∫ t, (∫ z, (η z * DifferentialGeometry.Analysis.Sobolev.diffQuot k h
        (A (u t)) z)^2) ∂μ) ≤ ∫ t, (∑ j, ∫ z,
          (η z * DifferentialGeometry.Analysis.Sobolev.diffQuot k h
            (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j (u t)) z)^2) ∂μ := by
      apply integral_mono (hI i) (integrable_finsetSum _ fun j _ => hI j)
      intro t
      dsimp only
      let f := fun j => ∫ z, (η z * DifferentialGeometry.Analysis.Sobolev.diffQuot k h
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j (u t)) z)^2
      have hf : ∀ j ∈ Finset.univ, 0 ≤ f j := fun _ _ => integral_nonneg fun z => sq_nonneg _
      exact Finset.single_le_sum (s := Finset.univ) hf (Finset.mem_univ i)
    exact hmono.trans (hbound k h (hh.trans (min_le_left _ _)))
  obtain ⟨v, hv, hvweak⟩ := hinverse hΩ.measurableSet hΩ₀ hηone hw k
    (lt_min hδ hr) hroom' hnorm
  refine ⟨v, ?_⟩
  filter_upwards [hvweak, dirichletLocalSpacetimeWeakPartialLp_coeFn q α hΩ hΩc hΩs μ i uμ,
    huμeq] with t ht hwt hut
  have hΩ₀Ω : Ω₀ ⊆ Ω := by
    intro z hz
    apply hroom'
    exact Metric.self_subset_cthickening _ (subset_tsupport η (by change η z ≠ 0; rw [hηone z hz]; norm_num))
  have hsource : (fun z => w (t,z)) =ᵐ[volume.restrict Ω₀]
      (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t) : _ → ℝ) := by
    have hm := hwt.filter_mono (ae_mono (Measure.restrict_mono hΩ₀Ω le_rfl))
    simpa only [hut] using hm
  intro ψ hψ hψc hψs
  have he := ht ψ hψ hψc hψs
  have heq : (∫ z in Ω₀, w (t,z) * fderiv ℝ ψ z (EuclideanSpace.single k 1)) =
      ∫ z in Ω₀, dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t) z *
        fderiv ℝ ψ z (EuclideanSpace.single k 1) := by
    apply integral_congr_ae
    filter_upwards [hsource] with z hz
    rw [hz]
  exact heq.symm.trans he

theorem IsWeakEvolutionSolution.exists_ae_hasWeakPartialDeriv_localWeakPartial_on
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
    {hX : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      (G.metric t).inner x (X t x) (X t x) ≤ Bx}
    {htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_hs) G.metric t x| ≤ Bv}
    {f₀ : Lp ℝ 2
      (riemannianVolumeMeasure (I := I_hs) (M := M) q)}
    {u : timeL2 (H1ComplDirichlet q) T}
    (α : M) {Ω : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuclideanSpace ℝ (Fin n)) '' interior (extChartAt I_hs α).target)
    (hu : IsWeakEvolutionSolution hG hT hreg X a Bx Bv
      (fun t ht => hX t ⟨ht.1, ht.2.le⟩) htrace f₀ u)
    (hXsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) ((I_hs).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2))
      (D.regular ×ˢ (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I_hs) α).baseSet))
    {t₀ t₁ : ℝ} (ht₀ : 0 < t₀) (ht₁ : t₁ < T)
    {Ω₀ : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω) :
    ∀ i k : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))),
      ∃ v : Lp ℝ 2 (((timeMeasure T).restrict (Icc t₀ t₁)).prod (volume.restrict Ω₀)),
        ∀ᵐ t ∂(timeMeasure T).restrict (Icc t₀ t₁), DeGiorgi.HasWeakPartialDeriv k
          (fun z => v (t, z)) (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) Ω₀ := by
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  obtain ⟨Ω', hΩ', hKΩ', hΩ'Ω, hΩ'c⟩ :=
    exists_open_between_and_isCompact_closure hΩ₀c hΩ hΩ₀Ω
  obtain ⟨Ω'', hΩ'', hKΩ'', hΩ''Ω', hΩ''c⟩ :=
    exists_open_between_and_isCompact_closure hΩ₀c hΩ' hKΩ'
  obtain ⟨r, hr, hroom⟩ := hΩ''c.exists_cthickening_subset_open hΩ' hΩ''Ω'
  obtain ⟨ε, η, hε, _, hη, hηc, hηrange, hηone, hηs⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_smooth_cutoff_with_neighborhood
      hΩ₀c hΩ'' hKΩ''
  have hηb : ∀ z, |η z| ≤ 1 := by
    intro z
    have hz := hηrange (mem_range_self z)
    exact (abs_le.mpr ⟨by linarith [hz.1], hz.2⟩)
  let U := toEuclidean (E := EuclideanSpace ℝ (Fin n)) '' interior (extChartAt I_hs α).target
  have hU : IsOpen U := (toEuclidean (E := EuclideanSpace ℝ (Fin n))).isOpenMap _ isOpen_interior
  obtain ⟨φ, _, hφ⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Chart.exists_smoothMap_mul_chartDensity_eq_one
      q α hU (Subset.rfl : U ⊆ U) hΩc hΩs
  obtain ⟨lam, hlam, hcoer⟩ :=
    DifferentialGeometry.Analysis.Laplacian.MetricExtension.exists_uniform_inv_gram_quadratic_lower_bound
      hG isCompact_Icc hreg α hΩc (hΩs.trans (image_mono interior_subset))
  have hcoer' : ∀ t ∈ Icc (0 : ℝ) T, ∀ y ∈ Ω,
      ∀ ξ : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) → ℝ,
      lam * ∑ i, (ξ i)^2 ≤ ∑ i, ∑ j,
        DifferentialGeometry.Analysis.Laplacian.MetricExtension.invGramOnEuclid (I := I_hs)
          (G.metric t) α i j y * ξ i * ξ j := by
    intro t ht y hy ξ
    have hb := hcoer t ht y (subset_closure hy) (WithLp.toLp 2 ξ)
    simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs,
      PiLp.inner_apply, DeGiorgi.matMulE_apply, Matrix.mulVec, dotProduct, Matrix.of_apply,
      Real.inner_apply] at hb
    convert hb using 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  exact hu.exists_ae_hasWeakPartialDeriv_localWeakPartial hXcont hacont α hΩ hΩc hΩs
    hΩ' hΩ'' hΩ'c hΩ'Ω hΩ''c hη hηc hηs hr hroom φ
    (fun z hz => hφ z (subset_closure hz)) hXsmooth hηb hlam hcoer' ht₀ ht₁ hΩ₀
      (fun z hz => hηone z (Metric.self_subset_cthickening _ (subset_closure hz)))

theorem IsWeakEvolutionSolution.ae_memWkp_two_chartInverse
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
    {hX : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      (G.metric t).inner x (X t x) (X t x) ≤ Bx}
    {htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_hs) G.metric t x| ≤ Bv}
    {f₀ : Lp ℝ 2
      (riemannianVolumeMeasure (I := I_hs) (M := M) q)}
    {u : timeL2 (H1ComplDirichlet q) T}
    (α : M) {Ω : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuclideanSpace ℝ (Fin n)) '' interior (extChartAt I_hs α).target)
    (hu : IsWeakEvolutionSolution hG hT hreg X a Bx Bv
      (fun t ht => hX t ⟨ht.1, ht.2.le⟩) htrace f₀ u)
    (hXsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) ((I_hs).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2))
      (D.regular ×ˢ (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I_hs) α).baseSet))
    {t₀ t₁ : ℝ} (ht₀ : 0 < t₀) (ht₁ : t₁ < T)
    {Ω₀ : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω) :
    ∀ᵐ t ∂(timeMeasure T).restrict (Icc t₀ t₁),
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp 2 2
        (fun z => H1ComplDirichletToLp q (u t)
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuclideanSpace ℝ (Fin n))).symm z))) Ω₀ := by
  obtain hsecond := hu.exists_ae_hasWeakPartialDeriv_localWeakPartial_on hXcont hacont
    α hΩ hΩc hΩs hXsmooth ht₀ ht₁ hΩ₀ hΩ₀Ω
  choose v hv using hsecond
  have hsecond' := ae_all_iff.mpr (fun i => ae_all_iff.mpr (hv i))
  have hvLp := ae_all_iff.mpr (fun i => ae_all_iff.mpr
    (fun k => (Lp.memLp (v i k)).prodMk_left (by norm_num)))
  filter_upwards [hsecond', hvLp] with t hwt hvt
  let g := fun i => dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  apply DifferentialGeometry.Analysis.Sobolev.Euclidean.memWkp_two_of_hasWeakPartialDeriv
    (by norm_num) hΩ₀
    ((memWkp_chartInverse_H1ComplDirichletToLp q α hΩ hΩc hΩs (u t)).memLp.mono_measure
      (Measure.restrict_mono hsub le_rfl)) (g := fun i z => g i z)
  · intro i
    refine ⟨(Lp.memLp (g i)).mono_measure (Measure.restrict_mono hsub le_rfl), ?_⟩
    intro k
    exact ⟨fun z => v i k (t,z), hvt i k, hwt i k⟩
  · intro i
    exact DeGiorgi.HasWeakPartialDeriv.restrict hΩ₀ hsub
      (hasWeakPartialDeriv_dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t))


theorem IsWeakEvolutionSolution.exists_lp_divergence_localWeakPartial
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
    {hX : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      (G.metric t).inner x (X t x) (X t x) ≤ Bx}
    {htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_hs) G.metric t x| ≤ Bv}
    {f₀ : Lp ℝ 2
      (riemannianVolumeMeasure (I := I_hs) (M := M) q)}
    {u : timeL2 (H1ComplDirichlet q) T}
    (α : M) {Ω : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuclideanSpace ℝ (Fin n)) '' interior (extChartAt I_hs α).target)
    (hu : IsWeakEvolutionSolution hG hT hreg X a Bx Bv
      (fun t ht => hX t ⟨ht.1, ht.2.le⟩) htrace f₀ u)
    (hXsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) ((I_hs).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2))
      (D.regular ×ˢ (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I_hs) α).baseSet))
    {t₀ t₁ : ℝ} (ht₀ : 0 < t₀) (ht₁ : t₁ < T)
    {Ω₀ : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω) :
    let μ := (timeMeasure T).restrict (Icc t₀ t₁)
    let A := fun i j (p : ℝ × EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))))) =>
      MetricExtension.weightedInvGramOnEuclid (I := I_hs) (G.metric p.1) α i j p.2
    let V := fun i => dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) i u
    ∃ F : Lp ℝ 2 (μ.prod (volume.restrict Ω₀)),
      ∀ (φ : ℝ × EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))) → ℝ),
        ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ univ ×ˢ Ω₀ →
        (∫ p, F p * φ p ∂μ.prod (volume.restrict Ω₀)) =
          -∑ i, ∑ j, ∫ p, A i j p * V i p *
            fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂μ.prod (volume.restrict Ω₀) := by
  intro μ A V
  classical
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  have hΩ₀s := hΩ₀Ω.trans (subset_closure.trans hΩs)
  have hmeasure : μ.prod (volume.restrict Ω₀) ≤
      (timeMeasure T).prod (volume.restrict Ω) :=
    Measure.prod_mono Measure.restrict_le_self (Measure.restrict_mono hsub le_rfl)
  have hV (i) : MemLp (V i) 2 (μ.prod (volume.restrict Ω₀)) :=
    (Lp.memLp (V i)).mono_measure hmeasure
  let W := fun i => (hV i).toLp (V i)
  have hW (i) : W i =ᵐ[μ.prod (volume.restrict Ω₀)] V i := (hV i).coeFn_toLp
  choose DV hDV using hu.exists_ae_hasWeakPartialDeriv_localWeakPartial_on hXcont hacont
    α hΩ hΩc hΩs hXsmooth ht₀ ht₁ hΩ₀ hΩ₀Ω
  have hA (i j) : MemLp (A i j) ∞ (μ.prod (volume.restrict Ω₀)) := by
    have hb := MetricExtension.weightedInvGramOnEuclid_family_memLp_top hG isCompact_Icc hreg α
      hΩ₀.measurableSet hΩ₀c (hΩ₀s.trans (image_mono interior_subset)) i j (volume.prod volume)
    rw [← Measure.prod_restrict] at hb
    exact hb.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hDA (i j) : MemLp
      (fun p => fderiv ℝ (fun x => A i j (p.1, x)) p.2 (EuclideanSpace.single j 1))
      ∞ (μ.prod (volume.restrict Ω₀)) := by
    have hb := MetricExtension.weightedInvGramOnEuclid_family_fderiv_memLp_top hG isCompact_Icc
      hreg α hΩ₀.measurableSet hΩ₀c hΩ₀s i j j (volume.prod volume)
    rw [← Measure.prod_restrict] at hb
    exact hb.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hAsmooth (i j) : ∀ᵐ t ∂μ,
      ContDiffOn ℝ (⊤ : ℕ∞) (fun x => A i j (t, x)) Ω₀ :=
    Filter.Eventually.of_forall fun t =>
      (MetricExtension.weightedInvGramOnEuclid_contDiffOn (G.metric t) α i j).mono
        (hsub.trans (subset_closure.trans (hΩs.trans (image_mono interior_subset))))
  have hweak (i j) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
      (fun x => DV i j (t, x)) (fun x => W i (t, x)) Ω₀ := by
    have hc := ae_restrict_of_ae (s := Icc t₀ t₁)
      (dirichletLocalSpacetimeWeakPartialLp_coeFn q α hΩ hΩc hΩs (timeMeasure T) i u)
    filter_upwards [hDV i j, Measure.ae_ae_of_ae_prod (hW i), hc] with t ht hwt hct
    have he : (fun x => W i (t, x)) =ᵐ[volume.restrict Ω₀]
        dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t) :=
      Filter.EventuallyEq.trans hwt (ae_restrict_of_ae_restrict_of_subset hsub hct)
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.hasWeakPartialDeriv_congr_ae
      hΩ₀ j he.symm ht
  obtain ⟨F, _, hF⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_lp_divergence_of_weakPartials
      (by norm_num) hΩ₀ W DV hA hDA hAsmooth hweak
  refine ⟨F, ?_⟩
  intro φ hφ hφc hφs
  rw [hF φ hφ hφc hφs]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply integral_congr_ae
  filter_upwards [hW i] with p hp
  rw [hp]


theorem IsWeakEvolutionSolution.exists_lp_symmetric_weak_second_deriv
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
    {hX : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      (G.metric t).inner x (X t x) (X t x) ≤ Bx}
    {htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_hs) G.metric t x| ≤ Bv}
    {f₀ : Lp ℝ 2
      (riemannianVolumeMeasure (I := I_hs) (M := M) q)}
    {u : timeL2 (H1ComplDirichlet q) T}
    (α : M) {Ω : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuclideanSpace ℝ (Fin n)) '' interior (extChartAt I_hs α).target)
    (hu : IsWeakEvolutionSolution hG hT hreg X a Bx Bv
      (fun t ht => hX t ⟨ht.1, ht.2.le⟩) htrace f₀ u)
    (hXsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) ((I_hs).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2))
      (D.regular ×ˢ (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I_hs) α).baseSet))
    {t₀ t₁ : ℝ} (ht₀ : 0 < t₀) (ht₁ : t₁ < T)
    {Ω₀ : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω) :
    ∃ v : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) →
        Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) →
        Lp ℝ 2 (((timeMeasure T).restrict (Icc t₀ t₁)).prod (volume.restrict Ω₀)),
      (∀ i k, ∀ᵐ t ∂(timeMeasure T).restrict (Icc t₀ t₁), DeGiorgi.HasWeakPartialDeriv k
        (fun z => v i k (t, z)) (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) Ω₀) ∧
      ∀ i k, v i k = v k i := by
  classical
  choose v hv using hu.exists_ae_hasWeakPartialDeriv_localWeakPartial_on hXcont hacont
    α hΩ hΩc hΩs hXsmooth ht₀ ht₁ hΩ₀ hΩ₀Ω
  refine ⟨v, hv, ?_⟩
  intro i k
  apply Lp.ext
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_eq_fun (Lp.stronglyMeasurable (v i k)).measurable
      (Lp.stronglyMeasurable (v k i)).measurable)).mpr
  filter_upwards [hv i k, hv k i, (Lp.memLp (v i k)).prodMk_left (by norm_num),
    (Lp.memLp (v k i)).prodMk_left (by norm_num)] with t hik hki hikLp hkiLp
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hi := DeGiorgi.HasWeakPartialDeriv.restrict hΩ₀ hsub
    (hasWeakPartialDeriv_dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t))
  have hk := DeGiorgi.HasWeakPartialDeriv.restrict hΩ₀ hsub
    (hasWeakPartialDeriv_dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k (u t))
  exact DifferentialGeometry.Analysis.Sobolev.ae_eq_of_weak_second_deriv_comm hΩ₀
    (ae_restrict_mem hΩ₀.measurableSet) (EuclideanSpace.single i 1) (EuclideanSpace.single k 1)
    hi hk hik hki (hikLp.locallyIntegrable (by norm_num))
      (hkiLp.locallyIntegrable (by norm_num))


end DifferentialGeometry.Analysis.Parabolic.Dirichlet
