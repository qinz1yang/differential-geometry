import DifferentialGeometry.Analysis.Parabolic.Dirichlet.WeakEquationFixedMass
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.SteklovEnergy
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletNirenbergEstimate

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

theorem IsWeakEvolutionSolution.integral_cutoff_volumeDensity_test_le
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
      ∀ L : H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q,
        let B := -(innerSL ℝ).bilinearComp (H1ComplDirichletToLp q)
          ((H1ComplDirichletToLp q).comp L)
        B.flip = B → (∀ v, 0 ≤ B v v) →
        ∀ (ζ : ℝ → ℝ) (K : ℝ≥0), ContDiff ℝ 1 ζ → MemLp ζ ∞ volume →
          (∀ᵐ t ∂volume, 0 ≤ ζ t) → LipschitzWith K ζ → ζ 0 = 0 → ζ T = 0 →
        (∫ t, ζ t * dirichletWeakFormComplOnIco G.metric X a Bx hX
          hCg hequiv Cv hCv0 hCvtop hvol t (u t)
            (smoothMulH1ComplDirichlet q
              (riemannianVolumeDensitySmoothMap (G.metric t) q) (L (u t))) ∂timeMeasure T) ≤
          (3 * (K : ℝ) / 2) * ∫ t, B (u t) (u t) ∂timeMeasure T := by
  obtain ⟨Cg, Cv, hCg, hequiv, hCv0, hCvtop, hvol, htest⟩ :=
    hu.integral_cutoff_steklovAverage_test_volumeDensity_swap hXcont hacont
  refine ⟨Cg, Cv, hCg, hequiv, hCv0, hCvtop, hvol, ?_⟩
  intro L B hB hBpos ζ K hζsmooth hζ hζpos hζlip hζ0 hζT
  let : NormedAddCommGroup (H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let S : ℝ → H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q := fun t =>
    smoothMulH1ComplDirichlet q (riemannianVolumeDensitySmoothMap (G.metric t) q)
  have hSc : ContinuousOn S (Icc (0 : ℝ) T) :=
    ((contDiffOn_one_smoothMulH1ComplDirichlet q _ D.regular_isOpen
      (riemannianVolumeDensity_swap_contMDiffOn_of_metricFamilySmoothOn hG q)).mono hreg).continuousOn
  obtain ⟨CS, hCS⟩ := isCompact_Icc.exists_bound_of_continuousOn hSc
  let F₀ := dirichletWeakFormComplOnIco G.metric X a Bx hX
    hCg hequiv Cv hCv0 hCvtop hvol
  have hF₀ : ∀ y z, AEStronglyMeasurable (fun t => F₀ t y z) (timeMeasure T) :=
    dirichletWeakFormComplOnIco_aestronglyMeasurable hG hreg X hXcont a hacont Bx hX
      hCg hequiv Cv hCv0 hCvtop hvol
  obtain ⟨Ca, hCa⟩ := isCompact_Icc.exists_bound_of_continuousOn hacont
  have hCa0 : 0 ≤ Ca := (norm_nonneg (a 0)).trans (hCa 0 ⟨le_rfl, hT⟩)
  have ha : ∀ t ∈ Ico (0 : ℝ) T, |a t| ≤ Ca := by
    intro t ht
    simpa only [Real.norm_eq_abs] using hCa t ⟨ht.1, ht.2.le⟩
  let C₀ := (1 + Real.sqrt (max Bx 0) + Ca) * (Cv.toReal * Cg)
  have hF₀b (t : ℝ) : ‖F₀ t‖ ≤ C₀ :=
    norm_dirichletWeakFormComplOnIco_le G.metric X a Ca Bx hCa0 ha hX
      hCg hequiv Cv hCv0 hCvtop hvol t
  let F : ℝ → H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q →L[ℝ] ℝ :=
    fun t => (F₀ t).bilinearComp (ContinuousLinearMap.id ℝ _) ((S t).comp L)
  have hF : ∀ y z, AEStronglyMeasurable (fun t => F t y z) (timeMeasure T) := by
    intro y z
    apply DifferentialGeometry.Analysis.Parabolic.TimeSobolev.AEStronglyMeasurable.clm_apply_of_apply_aestronglyMeasurable
      (fun t => F₀ t y) (hF₀ y) (fun t => S t (L z))
    exact (memLp_of_continuousOn (hSc.clm_apply continuousOn_const)).aestronglyMeasurable
  have hFb : ∀ᵐ t ∂timeMeasure T, ‖F t‖ ≤ max C₀ 0 * (max CS 0 * ‖L‖) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    dsimp only [F]
    rw [ContinuousLinearMap.bilinearComp, ContinuousLinearMap.comp_id, ContinuousLinearMap.opNorm_flip]
    calc
      _ ≤ ‖(F₀ t).flip‖ * ‖(S t).comp L‖ := ((F₀ t).flip).opNorm_comp_le _
      _ = ‖F₀ t‖ * ‖(S t).comp L‖ := by rw [ContinuousLinearMap.opNorm_flip]
      _ ≤ max C₀ 0 * (max CS 0 * ‖L‖) := by
        apply mul_le_mul ((hF₀b t).trans (le_max_left _ _)) _ (norm_nonneg _) (le_max_right _ _)
        exact ((S t).opNorm_comp_le L).trans
          (mul_le_mul_of_nonneg_right ((hCS t ht).trans (le_max_left _ _)) (norm_nonneg _))
  apply u.integral_mul_bilinear_le_of_cutoff_steklov_identity F hF hFb B hB hBpos
    hζsmooth hζ hζpos hζlip
  intro s hs
  let U : ℝ → H1ComplDirichlet q := (Icc (0 : ℝ) T).indicator u
  let W : ℝ → H1ComplDirichlet q := fun t => steklovAverage s U t
  let Q : ℝ → H1ComplDirichlet q := fun t => s⁻¹ • (U (t + s) - U t)
  have hW : MemLp W 2 (timeMeasure T) :=
    (memLp_congr_ae (timeL2.coeFn_steklovAverage s u)).mp (Lp.memLp (u.steklovAverage s))
  have hU : MemLp U 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_Icc).mpr (Lp.memLp u)
  have hQ : MemLp Q 2 (timeMeasure T) :=
    (((hU.comp_measurePreserving (measurePreserving_add_right volume s)).sub hU).const_smul s⁻¹).restrict _
  have hintB (v : ℝ → H1ComplDirichlet q) (hv : MemLp v 2 (timeMeasure T)) :
      Integrable (fun t => B (u t) (v t)) (timeMeasure T) :=
    MeasureTheory.integrable_bilinear_of_apply_aestronglyMeasurable (fun _ => B)
      (fun _ _ => aestronglyMeasurable_const) (Eventually.of_forall fun _ => le_rfl) (Lp.memLp u) hv
  have hβ : MemLp (_root_.deriv ζ) ∞ (timeMeasure T) :=
    memLp_top_of_bound hζsmooth.continuous_deriv_one.aestronglyMeasurable K
      (Eventually.of_forall fun _ => norm_deriv_le_of_lipschitz hζlip)
  have hI₁ := (hintB W hW).mul_of_top_right hβ
  have hI₂ := (hintB Q hQ).mul_of_top_right (hζ.restrict (Icc (0 : ℝ) T))
  have hI₁p : Integrable (fun t => _root_.deriv ζ t * B (u t) (W t)) (timeMeasure T) :=
    hI₁.congr (Eventually.of_forall fun _ => rfl)
  have hI₂p : Integrable (fun t => ζ t * B (u t) (Q t)) (timeMeasure T) :=
    hI₂.congr (Eventually.of_forall fun _ => rfl)
  have hpair (t : ℝ) : inner ℝ (H1ComplDirichletToLp q (u t))
      (H1ComplDirichletToLp q (L (_root_.deriv ζ t • W t + ζ t • Q t))) =
      -(_root_.deriv ζ t * B (u t) (W t) + ζ t * B (u t) (Q t)) := by
    change inner ℝ (H1ComplDirichletToLp q (u t))
      (H1ComplDirichletToLp q (L (_root_.deriv ζ t • W t + ζ t • Q t))) =
      -(_root_.deriv ζ t * -inner ℝ (H1ComplDirichletToLp q (u t))
        (H1ComplDirichletToLp q (L (W t))) + ζ t * -inner ℝ (H1ComplDirichletToLp q (u t))
        (H1ComplDirichletToLp q (L (Q t))))
    simp only [map_add, map_smul, inner_add_right, inner_smul_right]
    ring
  have h := htest L s ζ hζsmooth.contDiffOn hζ0 hζT
  have htime : (∫ t, inner ℝ (H1ComplDirichletToLp q (u t))
      (H1ComplDirichletToLp q (L (_root_.deriv ζ t • W t + ζ t • Q t))) ∂timeMeasure T) =
      -((∫ t, _root_.deriv ζ t * B (u t) (W t) ∂timeMeasure T) +
        ∫ t, ζ t * B (u t) (Q t) ∂timeMeasure T) := by
    rw [← integral_add hI₁p hI₂p, ← integral_neg]
    exact integral_congr_ae (Eventually.of_forall hpair)
  have hspace : (∫ t, F₀ t (u t) (S t (L (ζ t • W t))) ∂timeMeasure T) =
      ∫ t, ζ t * F t (u t) (W t) ∂timeMeasure T := by
    apply integral_congr_ae
    filter_upwards [] with t
    simp only [map_smul, smul_eq_mul, F, ContinuousLinearMap.bilinearComp_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply]
  change (∫ t, inner ℝ (H1ComplDirichletToLp q (u t))
      (H1ComplDirichletToLp q (L (_root_.deriv ζ t • W t + ζ t • Q t))) ∂timeMeasure T) +
      (∫ t, F₀ t (u t) (S t (L (ζ t • W t))) ∂timeMeasure T) = 0 at h
  rw [htime, hspace] at h
  change (∫ t, ζ t * F t (u t) (W t) ∂timeMeasure T) =
    (∫ t, _root_.deriv ζ t * B (u t) (W t) ∂timeMeasure T) +
      ∫ t, ζ t * B (u t) (Q t) ∂timeMeasure T
  linarith

end DifferentialGeometry.Analysis.Parabolic.Dirichlet

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

theorem exists_uniform_integral_cutoff_volumeDensity_nirenbergTest_le
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
        φ ((extChartAt I_hs α).symm ((toEuclidean (E := EuclideanSpace ℝ (Fin n))).symm z)) = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀
    (f₀ : Lp ℝ 2
      (riemannianVolumeMeasure (I := I_hs) (M := M) q))
    (u : timeL2 (H1ComplDirichlet q) T), IsWeakEvolutionSolution hG hT hreg X a Bx Bv hX htrace f₀ u →
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
      ∀ (k : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))))
        (h : ℝ) (hh : |h| ≤ r) (ζ : ℝ → ℝ) (K : ℝ≥0),
        ContDiff ℝ 1 ζ → MemLp ζ ∞ volume →
        (∀ᵐ t ∂volume, 0 ≤ ζ t) → LipschitzWith K ζ → ζ 0 = 0 → ζ T = 0 →
        (∫ t, ζ t * dirichletWeakFormComplOnIco G.metric X a Bx hX
          hCg hequiv Cv hCv0 hCvtop hvol t (u t)
          (smoothMulH1ComplDirichlet q (riemannianVolumeDensitySmoothMap (G.metric t) q * φ)
            (dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k h
              ((Metric.cthickening_mono hh _).trans
                ((Metric.cthickening_subset_of_subset r (hηs.trans subset_closure)).trans
                  (hroom.trans (subset_closure.trans hΩ'Ω)))) (u t))) ∂timeMeasure T) ≤
          C * (K : ℝ) * ∫ t, ‖u t‖ ^ 2 ∂timeMeasure T := by
  have hηr : Metric.cthickening r (tsupport η) ⊆ Ω :=
    (Metric.cthickening_subset_of_subset r (hηs.trans subset_closure)).trans
      (hroom.trans (subset_closure.trans hΩ'Ω))
  obtain ⟨C, hC, hCb⟩ := exists_integral_cutoff_sq_diffQuot_chartInverse_le q α hΩ hΩc hΩs
    hΩ' hΩ'' hΩ'c hΩ'Ω hΩ''c hη.continuous hηc hηs hr hroom
  refine ⟨3 * C / 2, by positivity, ?_⟩
  intro f₀ u hu
  obtain ⟨Cg, Cv, hCg, hequiv, hCv0, hCvtop, hvol, htest⟩ :=
    hu.integral_cutoff_volumeDensity_test_le hXcont hacont
  refine ⟨Cg, Cv, hCg, hequiv, hCv0, hCvtop, hvol, ?_⟩
  intro k h hh ζ K hζsmooth hζ hζpos hζlip hζ0 hζT
  let L := (smoothMulH1ComplDirichlet q φ).comp
    (dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k h
      ((Metric.cthickening_mono hh _).trans hηr))
  let B := -(innerSL ℝ).bilinearComp (H1ComplDirichletToLp q)
    ((H1ComplDirichletToLp q).comp L)
  obtain ⟨hB, hBpos, hpair⟩ := dirichletNirenbergTest_symmetric_nonpos_of_mul_chartDensity
    q α hΩ hΩc hΩs hη hηc φ k h ((Metric.cthickening_mono hh _).trans hηr)
    (fun z hz => hφ z (((Metric.cthickening_mono hh _).trans hηr) hz))
  have htime := htest L hB hBpos ζ K hζsmooth hζ hζpos hζlip hζ0 hζT
  have hBbound (v : H1ComplDirichlet q) : B v v ≤ C * ‖v‖ ^ 2 := by
    rw [hpair]
    have heq : (∫ z, η z ^ 2 * DifferentialGeometry.Analysis.Sobolev.diffQuot k h
        (fun z => H1ComplDirichletToLp q v
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuclideanSpace ℝ (Fin n))).symm z))) z *
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h
        (fun z => H1ComplDirichletToLp q v
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuclideanSpace ℝ (Fin n))).symm z))) z) =
      ∫ z, η z ^ 2 * (DifferentialGeometry.Analysis.Sobolev.diffQuot k h
        (fun z => H1ComplDirichletToLp q v
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuclideanSpace ℝ (Fin n))).symm z))) z) ^ 2 := by
      apply integral_congr_ae
      filter_upwards [] with z
      ring
    rw [heq]
    exact hCb k h hh v
  have hBI : Integrable (fun t => B (u t) (u t)) (timeMeasure T) :=
    MeasureTheory.integrable_bilinear_of_apply_aestronglyMeasurable (fun _ => B)
      (fun _ _ => aestronglyMeasurable_const) (Eventually.of_forall fun _ => le_rfl)
      (Lp.memLp u) (Lp.memLp u)
  have huI : Integrable (fun t => ‖u t‖ ^ 2) (timeMeasure T) := (Lp.memLp u).norm.integrable_sq
  have hBIb : (∫ t, B (u t) (u t) ∂timeMeasure T) ≤ C * ∫ t, ‖u t‖ ^ 2 ∂timeMeasure T := by
    rw [← integral_const_mul]
    exact integral_mono_ae hBI (huI.const_mul C) (Eventually.of_forall fun t => hBbound (u t))
  have hmul (v : H1ComplDirichlet q) (t : ℝ) :
      smoothMulH1ComplDirichlet q (riemannianVolumeDensitySmoothMap (G.metric t) q) (L v) =
      smoothMulH1ComplDirichlet q (riemannianVolumeDensitySmoothMap (G.metric t) q * φ)
        (dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k h
          ((Metric.cthickening_mono hh _).trans hηr) v) := by
    change ((smoothMulH1ComplDirichlet q (riemannianVolumeDensitySmoothMap (G.metric t) q)).comp
      (smoothMulH1ComplDirichlet q φ)) _ = _
    rw [smoothMulH1ComplDirichlet_mul]
    rfl
  simp_rw [hmul] at htime
  exact htime.trans ((mul_le_mul_of_nonneg_left hBIb (by positivity)).trans_eq (by ring))

theorem IsWeakEvolutionSolution.exists_integral_cutoff_volumeDensity_nirenbergTest_le
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
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))))
        (h : ℝ) (hh : |h| ≤ r) (ζ : ℝ → ℝ) (K : ℝ≥0),
        ContDiff ℝ 1 ζ → MemLp ζ ∞ volume →
        (∀ᵐ t ∂volume, 0 ≤ ζ t) → LipschitzWith K ζ → ζ 0 = 0 → ζ T = 0 →
        (∫ t, ζ t * dirichletWeakFormComplOnIco G.metric X a Bx hX
          hCg hequiv Cv hCv0 hCvtop hvol t (u t)
          (smoothMulH1ComplDirichlet q (riemannianVolumeDensitySmoothMap (G.metric t) q * φ)
            (dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k h
              ((Metric.cthickening_mono hh _).trans
                ((Metric.cthickening_subset_of_subset r (hηs.trans subset_closure)).trans
                  (hroom.trans (subset_closure.trans hΩ'Ω)))) (u t))) ∂timeMeasure T) ≤
          C * (K : ℝ) * ∫ t, ‖u t‖ ^ 2 ∂timeMeasure T := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_integral_cutoff_volumeDensity_nirenbergTest_le
    (hG := hG) (hT := hT) (hreg := hreg) (hX := hX) (htrace := htrace)
    hXcont hacont α hΩ hΩc hΩs hΩ' hΩ'' hΩ'c hΩ'Ω hΩ''c hη hηc hηs hr hroom φ hφ
  obtain ⟨Cg, Cv, hCg, hequiv, hCv0, hCvtop, hvol, htest⟩ := hbound f₀ u hu
  exact ⟨Cg, Cv, hCg, hequiv, hCv0, hCvtop, hvol, C, hC, htest⟩

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
