import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletWeakChartCutoff
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.HeatEvolution
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.HeatNirenbergEnergy
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.LocalDivergence
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletLocalSecondDerivative
import DifferentialGeometry.Analysis.Parabolic.Energy.TimeCutoff

noncomputable section

open Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]
local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem exists_local_second_weak_derivative_of_heat_timeH1
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I_hs M}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D g)
    {T : ℝ} (hT : 0 ≤ T) (hreg : Icc (0 : ℝ) T ⊆ D.regular)
    (q : SmoothRiemannianMetric I_hs M)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, ∀ w : TangentSpace I_hs x,
      Cg⁻¹ * q.inner x w w ≤ (g t).inner x w w ∧
        (g t).inner x w w ≤ Cg * q.inner x w w)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : ∀ t ∈ Icc (0 : ℝ) T,
      riemannianVolumeMeasure (I := I_hs) (M := M) (g t) ≤
        Cv • riemannianVolumeMeasure (I := I_hs) (M := M) q)
    (α : M) {Ω Ω₀ : Set EuStd} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hΩ₀ : IsOpen Ω₀) (hΩ₀c : IsCompact (closure Ω₀)) (hΩ₀Ω : closure Ω₀ ⊆ Ω)
    {a b : ℝ} (ha : 0 < a) (hb : b < T)
    (u : timeL2 (H1ComplDirichlet q) T)
    (f : timeL2 (Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q)) T)
    (w : timeH1 (H1ComplDirichlet q →L[ℝ] ℝ) T)
    (hwmass : ∀ᵐ t ∂timeMeasure T, ∀ z,
      w.toFun t z = inner ℝ (H1ComplDirichletToLp q (u t)) (H1ComplDirichletToLp q z))
    (hwderiv : ∀ᵐ t ∂timeMeasure T, ∀ ht : t ∈ Icc (0 : ℝ) T, ∀ z,
      w.deriv t z = dirichletWeakFormCompl (g t) 0 0 0 (by intro x; simp)
        hCg (hequiv t ht) Cv hCv0 hCvtop (hvol t ht) (u t)
        (smoothMulH1ComplDirichlet q (riemannianVolumeDensitySmoothMap (g t) q) z) +
          inner ℝ (f t) (H1ComplDirichletToLp q z)) :
    ∃ H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) →
        Lp ℝ 2 (((timeMeasure T).restrict (Icc a b)).prod (volume.restrict Ω₀)),
      (∀ i k, ∀ᵐ t ∂(timeMeasure T).restrict (Icc a b),
        DeGiorgi.HasWeakPartialDeriv k (fun z => H i k (t, z))
          (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) Ω₀) ∧
      ∀ᵐ t ∂(timeMeasure T).restrict (Icc a b), Sobolev.Euclidean.MemWkp 2 2
        (fun z => H1ComplDirichletToLp q (u t)
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) Ω₀ := by
  obtain ⟨r, η, _, _, hη, hηc, hηrange, hηone, hηs⟩ :=
    Sobolev.Euclidean.exists_smooth_cutoff_with_neighborhood hΩ₀c hΩ hΩ₀Ω
  have hηb : ∀ z, |η z| ≤ 1 := by
    intro z
    have hz := hηrange (mem_range_self z)
    exact abs_le.mpr ⟨by linarith [hz.1], hz.2⟩
  have hex := exists_integral_cutoff_diffQuot_weakPartial_le_of_heat_timeH1
    hG hT hreg q hCg hequiv Cv hCv0 hCvtop hvol α hΩ hΩc hΩs hη hηc hηs hηb
  let δ := hex.choose
  have hδ := hex.choose_spec.1
  let C := hex.choose_spec.2.choose
  have hroom := hex.choose_spec.2.choose_spec.2.1
  have henergy := hex.choose_spec.2.choose_spec.2.2 u f w hwmass hwderiv
  obtain ⟨ζ, K, hζsmooth, hζc, hζpos, _, hζlip, hζ0, hζT, hζone⟩ :=
    Energy.exists_smooth_timeCutoff_eq_one_on_Icc ha hb
  have hζ : MemLp ζ ∞ volume := hζsmooth.continuous.memLp_of_hasCompactSupport hζc
  let A := C * ((K : ℝ) * (∫ t, ‖u t‖^2 ∂timeMeasure T) +
    (∫ t, ζ t * ‖u t‖^2 ∂timeMeasure T) +
    (∫ t, ζ t * (∫ z in Ω, (f t
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)))^2) ∂timeMeasure T))
  have hbound : ∀ k h, 0 < |h| → |h| ≤ δ →
      (∫ t, (∑ i, ∫ z, (η z * Sobolev.diffQuot k h
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) z)^2)
        ∂(timeMeasure T).restrict (Icc a b)) ≤ A := by
    intro k h hhpos hh
    let E := fun t => ∑ i, ∫ z, (η z * Sobolev.diffQuot k h
      (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) z)^2
    have hEI : Integrable E (timeMeasure T) := by
      apply integrable_finsetSum _
      intro i _
      exact Sobolev.integrable_integral_sq_cutoff_diffQuot_comp hΩ.measurableSet
        (hη.continuous.memLp_of_hasCompactSupport hηc) k h
        ((Metric.cthickening_mono hh _).trans hroom)
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i) (Lp.memLp u)
    have hEpos (t) : 0 ≤ E t := Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _
    have hi := Energy.integral_Icc_le_integral_mul_cutoff hEI hEpos
      (hζ.restrict (Icc (0 : ℝ) T)) hζpos hζone
    exact hi.trans (henergy k h hh ζ K (hζsmooth.of_le (by simp)) hζ
      (Eventually.of_forall hζpos) hζlip hζ0 hζT)
  exact exists_lp_second_weak_derivative_of_local_diffQuot_bound_restrict
    q α hΩ hΩc hΩs (Icc a b) u (hη.of_le (by simp)) hηc hΩ₀
      (fun z hz => hηone z (Metric.self_subset_cthickening _ (subset_closure hz))) hδ hroom hbound

theorem exists_local_lp_divergence_of_heat_timeH1
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I_hs M}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D g)
    {T : ℝ} (hT : 0 ≤ T) (hreg : Icc (0 : ℝ) T ⊆ D.regular)
    (q : SmoothRiemannianMetric I_hs M)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, ∀ w : TangentSpace I_hs x,
      Cg⁻¹ * q.inner x w w ≤ (g t).inner x w w ∧
        (g t).inner x w w ≤ Cg * q.inner x w w)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : ∀ t ∈ Icc (0 : ℝ) T,
      riemannianVolumeMeasure (I := I_hs) (M := M) (g t) ≤
        Cv • riemannianVolumeMeasure (I := I_hs) (M := M) q)
    (α : M) {Ω Ω₀ : Set EuStd} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω)
    {a b : ℝ} (ha : 0 < a) (hb : b < T)
    (u : timeL2 (H1ComplDirichlet q) T)
    (f : timeL2 (Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q)) T)
    (w : timeH1 (H1ComplDirichlet q →L[ℝ] ℝ) T)
    (hwmass : ∀ᵐ t ∂timeMeasure T, ∀ z,
      w.toFun t z = inner ℝ (H1ComplDirichletToLp q (u t)) (H1ComplDirichletToLp q z))
    (hwderiv : ∀ᵐ t ∂timeMeasure T, ∀ ht : t ∈ Icc (0 : ℝ) T, ∀ z,
      w.deriv t z = dirichletWeakFormCompl (g t) 0 0 0 (by intro x; simp)
        hCg (hequiv t ht) Cv hCv0 hCvtop (hvol t ht) (u t)
        (smoothMulH1ComplDirichlet q (riemannianVolumeDensitySmoothMap (g t) q) z) +
          inner ℝ (f t) (H1ComplDirichletToLp q z)) :
    let μ := (timeMeasure T).restrict (Icc a b)
    let A := fun i j (p : ℝ × EuStd) =>
      Laplacian.MetricExtension.weightedInvGramOnEuclid (I := I_hs) (g p.1) α i j p.2
    let V := fun i => dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) i u
    ∃ F : Lp ℝ 2 (μ.prod (volume.restrict Ω₀)),
      ∀ (φ : ℝ × EuStd → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ univ ×ˢ Ω₀ →
        (∫ p, F p * φ p ∂μ.prod (volume.restrict Ω₀)) =
          -∑ i, ∑ j, ∫ p, A i j p * V i p *
            fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂μ.prod (volume.restrict Ω₀) := by
  intro μ A V
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  obtain ⟨H, hH, _⟩ := exists_local_second_weak_derivative_of_heat_timeH1 hG hT hreg q
    hCg hequiv Cv hCv0 hCvtop hvol α hΩ hΩc hΩs hΩ₀ hΩ₀c hΩ₀Ω ha hb u f w hwmass hwderiv
  obtain ⟨F, _, hF⟩ := exists_lp_divergence_localWeakPartial_of_hasWeakPartialDeriv
    hG isCompact_Icc hreg (ae_restrict_mem measurableSet_Icc) q u α hΩ hΩc hΩs hΩ₀
    (subset_closure.trans hΩ₀Ω) (Icc a b) H hH
  exact ⟨F, hF⟩

theorem exists_lp_h1_gradient_chartPullback_mul_of_heat_timeH1
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I_hs M}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D g)
    {T : ℝ} (hT : 0 ≤ T) (hreg : Icc (0 : ℝ) T ⊆ D.regular)
    (q : SmoothRiemannianMetric I_hs M)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, ∀ w : TangentSpace I_hs x,
      Cg⁻¹ * q.inner x w w ≤ (g t).inner x w w ∧
        (g t).inner x w w ≤ Cg * q.inner x w w)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : ∀ t ∈ Icc (0 : ℝ) T,
      riemannianVolumeMeasure (I := I_hs) (M := M) (g t) ≤
        Cv • riemannianVolumeMeasure (I := I_hs) (M := M) q)
    (α : M) {Ω : Set EuStd} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {a b : ℝ} (ha : 0 < a) (hb : b < T)
    (u : timeL2 (H1ComplDirichlet q) T)
    (f : timeL2 (Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q)) T)
    (w : timeH1 (H1ComplDirichlet q →L[ℝ] ℝ) T)
    (hwmass : ∀ᵐ t ∂timeMeasure T, ∀ z,
      w.toFun t z = inner ℝ (H1ComplDirichletToLp q (u t)) (H1ComplDirichletToLp q z))
    (hwderiv : ∀ᵐ t ∂timeMeasure T, ∀ ht : t ∈ Icc (0 : ℝ) T, ∀ z,
      w.deriv t z = dirichletWeakFormCompl (g t) 0 0 0 (by intro x; simp)
        hCg (hequiv t ht) Cv hCv0 hCvtop (hvol t ht) (u t)
        (smoothMulH1ComplDirichlet q (riemannianVolumeDensitySmoothMap (g t) q) z) +
          inner ℝ (f t) (H1ComplDirichletToLp q z))
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Ω) (k : Fin (Module.finrank ℝ EuN)) :
    ∃ v : Lp (H1ComplDirichlet q) 2 ((timeMeasure T).restrict (Icc a b)),
      ∀ᵐ t ∂(timeMeasure T).restrict (Icc a b),
        (H1ComplDirichletToLp q (v t) : M → ℝ) =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
          Sobolev.Chart.chartPullback I_hs α
            (fun z => η z * dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k (u t) z) := by
  let μ := (timeMeasure T).restrict (Icc a b)
  have hμle : μ ≤ timeMeasure T := Measure.restrict_le_self
  obtain ⟨Ω₀, hΩ₀, hKΩ₀, hΩ₀Ω, hΩ₀c⟩ :=
    exists_open_between_and_isCompact_closure hηc.isCompact hΩ hηs
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hΩ₀s : closure Ω₀ ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target :=
    hΩ₀Ω.trans (subset_closure.trans hΩs)
  let uμ : Lp (H1ComplDirichlet q) 2 μ := ((Lp.memLp u).mono_measure hμle).toLp u
  let A := dirichletLocalWeakPartialLp q α hΩ₀ hΩ₀c hΩ₀s k
  let P : Lp (Lp ℝ 2 (volume.restrict Ω₀)) 2 μ := A.compLpL 2 μ uμ
  obtain ⟨dv, hdv, _⟩ := exists_local_second_weak_derivative_of_heat_timeH1 hG hT hreg q
    hCg hequiv Cv hCv0 hCvtop hvol α hΩ hΩc hΩs hΩ₀ hΩ₀c hΩ₀Ω ha hb u f w hwmass hwderiv
  let W : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 (μ.prod (volume.restrict Ω₀)) := fun i => dv k i
  have hPae : ∀ᵐ t ∂μ, (P t : EuStd → ℝ) =ᵐ[volume.restrict Ω₀]
      (A (u t) : EuStd → ℝ) := by
    filter_upwards [A.coeFn_compLpL uμ, MemLp.coeFn_toLp ((Lp.memLp u).mono_measure hμle)] with t ht hu_t
    rw [show P t = A (uμ t) from ht, hu_t]
  have hgrad (t : ℝ) :
      (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k (u t) : EuStd → ℝ) =ᵐ[volume.restrict Ω₀]
        dirichletLocalWeakPartialLp q α hΩ₀ hΩ₀c hΩ₀s k (u t) :=
    dirichletLocalWeakPartialLp_restrict_ae q α hΩ hΩc hΩs hΩ₀ hΩ₀c hΩ₀s hsub k (u t)
  have hweak : ∀ i, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i (fun z => W i (t,z)) (P t) Ω₀ := by
    intro i
    filter_upwards [hdv k i, hPae] with t ht hp
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.hasWeakPartialDeriv_congr_ae
      hΩ₀ i ((hgrad t).trans hp.symm) ht
  obtain ⟨v, hv⟩ := exists_lp_h1ComplDirichlet_chartPullback_mul_of_weak_partials
    q α hΩ₀ hΩ₀c hΩ₀s hη hηc hKΩ₀ P W hweak
  refine ⟨v, ?_⟩
  filter_upwards [hv, hPae] with t ht hp
  have hfg : (P t : EuStd → ℝ) =ᵐ[volume.restrict Ω₀]
      dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k (u t) := hp.trans (hgrad t).symm
  have hall := (ae_restrict_iff' hΩ₀.measurableSet).mp hfg
  apply ht.trans
  apply DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback_ae_eq_of_ae_eq q α
  filter_upwards [hall] with z hz
  by_cases hz' : z ∈ tsupport η
  · exact congrArg (fun r => η z * r) (hz (hKΩ₀ hz'))
  · have he : η z = 0 := image_eq_zero_of_notMem_tsupport hz'
    simp [he]

theorem exists_local_dirichlet_heat_solution_with_interior_h2
    {D : RealTimeInterval}
    {g : ℝ → SmoothRiemannianMetric I_hs M}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D g)
    (h0reg : (0 : ℝ) ∈ D.regular)
    (a : ℝ → C^∞⟮I_hs, M; ℝ⟯)
    (ha : ContinuousOn (fun p : ℝ × M => a p.1 p.2)
      (D.regular ×ˢ (Set.univ : Set M))) :
    let q := g 0
    ∃ T : ℝ, 0 < T ∧ Icc (0 : ℝ) T ⊆ D.regular ∧
      ∃ Cg : ℝ, ∃ Cv : ℝ≥0∞, ∃ hCg : 1 ≤ Cg,
      ∃ hequiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, ∀ w : TangentSpace I_hs x,
        Cg⁻¹ * q.inner x w w ≤ (g t).inner x w w ∧
          (g t).inner x w w ≤ Cg * q.inner x w w,
      ∃ hCv0 : Cv ≠ 0, ∃ hCvtop : Cv ≠ ⊤,
      ∃ hvol : ∀ t ∈ Icc (0 : ℝ) T,
        riemannianVolumeMeasure (I := I_hs) (M := M) (g t) ≤
          Cv • riemannianVolumeMeasure (I := I_hs) (M := M) q,
      ∀ (u₀ : Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q))
        (f₀ : timeL2 (Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q)) T),
        ∃ (w : timeH1 (H1ComplDirichlet q →L[ℝ] ℝ) T)
          (V : timeL2 (H1ComplDirichlet q) T)
          (U : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q)),
          ContinuousOn U (Icc (0 : ℝ) T) ∧ U 0 = u₀ ∧
          (fun t => H1ComplDirichletToLp q (V t)) =ᵐ[timeMeasure T] U ∧
          (∀ t ∈ Icc (0 : ℝ) T, ∀ v : H1ComplDirichlet q,
            w.toFun t v = inner ℝ (U t) (H1ComplDirichletToLp q v)) ∧
          (∀ᵐ t ∂timeMeasure T, ∀ ht : t ∈ Icc (0 : ℝ) T, ∀ v : H1ComplDirichlet q,
            w.deriv t v =
              dirichletWeakFormCompl (g t) 0 0 0 (by intro x; simp)
                hCg (hequiv t ht) Cv hCv0 hCvtop (hvol t ht) (V t)
                (smoothMulH1ComplDirichlet q (riemannianVolumeDensitySmoothMap (g t) q) v) -
              inner ℝ (Laplacian.smoothMulLp q (a t) (U t)) (H1ComplDirichletToLp q v) +
                inner ℝ (f₀ t) (H1ComplDirichletToLp q v)) ∧
          ∀ (α : M) (Ω Ω₀ : Set EuStd) (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
            (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target),
            IsOpen Ω₀ → IsCompact (closure Ω₀) → closure Ω₀ ⊆ Ω →
            ∀ c d : ℝ, 0 < c → d < T →
            ∃ H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) →
                Lp ℝ 2 (((timeMeasure T).restrict (Icc c d)).prod (volume.restrict Ω₀)),
              (∀ i k, ∀ᵐ t ∂(timeMeasure T).restrict (Icc c d),
                DeGiorgi.HasWeakPartialDeriv k (fun z => H i k (t, z))
                  (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (V t)) Ω₀) ∧
              ∀ᵐ t ∂(timeMeasure T).restrict (Icc c d), Sobolev.Euclidean.MemWkp 2 2
                (fun z => H1ComplDirichletToLp q (V t)
                  ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) Ω₀ := by
  intro q
  obtain ⟨T, hT, hreg, Cg, Cv, hCg, hequiv, hCv0, hCvtop, hvol, hsol⟩ :=
    exists_local_dirichlet_heat_variational_solution hG h0reg a ha
  refine ⟨T, hT, hreg, Cg, Cv, hCg, hequiv, hCv0, hCvtop, hvol, ?_⟩
  intro u₀ f₀
  let J := H1ComplDirichletToLp q
  let Q : Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q) →L[ℝ]
      H1ComplDirichlet q →L[ℝ] ℝ := (ContinuousLinearMap.precomp ℝ J).comp (innerSL ℝ)
  let β := Q.compLpL 2 (timeMeasure T) f₀
  obtain ⟨w, V, U, hcont, hinit, hfield, hpoint, heq⟩ := hsol u₀ β
  have hβ : ∀ᵐ t ∂timeMeasure T, β t = Q (f₀ t) := Q.coeFn_compLpL f₀
  have heq' : ∀ᵐ t ∂timeMeasure T, ∀ ht : t ∈ Icc (0 : ℝ) T, ∀ v : H1ComplDirichlet q,
      w.deriv t v = dirichletWeakFormCompl (g t) 0 0 0 (by intro x; simp)
        hCg (hequiv t ht) Cv hCv0 hCvtop (hvol t ht) (V t)
        (smoothMulH1ComplDirichlet q (riemannianVolumeDensitySmoothMap (g t) q) v) -
        inner ℝ (Laplacian.smoothMulLp q (a t) (U t)) (J v) + inner ℝ (f₀ t) (J v) := by
    filter_upwards [heq, hβ] with t ht hβt
    intro htm v
    rw [ht htm v, hβt]
    rfl
  let A := fun t => Laplacian.smoothMulLp q (a t) (U t)
  have hA : MemLp A 2 (timeMeasure T) := memLp_of_continuousOn
    (Laplacian.continuousOn_smoothMulLp_apply q a (ha.mono (prod_mono hreg Subset.rfl)) hcont)
  let f := f₀ - hA.toLp A
  have hf : ∀ᵐ t ∂timeMeasure T, f t = f₀ t - A t := by
    filter_upwards [Lp.coeFn_sub f₀ (hA.toLp A), hA.coeFn_toLp] with t ht hAt
    rw [ht, Pi.sub_apply, hAt]
  have hwmass : ∀ᵐ t ∂timeMeasure T, ∀ z,
      w.toFun t z = inner ℝ (J (V t)) (J z) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc, hfield] with t ht hft
    intro z
    rw [hpoint t ht z, hft]
  have hwderiv : ∀ᵐ t ∂timeMeasure T, ∀ ht : t ∈ Icc (0 : ℝ) T, ∀ z,
      w.deriv t z = dirichletWeakFormCompl (g t) 0 0 0 (by intro x; simp)
        hCg (hequiv t ht) Cv hCv0 hCvtop (hvol t ht) (V t)
        (smoothMulH1ComplDirichlet q (riemannianVolumeDensitySmoothMap (g t) q) z) +
          inner ℝ (f t) (J z) := by
    filter_upwards [heq', hf] with t ht hft
    intro htm z
    rw [ht htm z, hft, inner_sub_left]
    change _ - inner ℝ (A t) (J z) + inner ℝ (f₀ t) (J z) = _
    ring
  refine ⟨w, V, U, hcont, hinit, hfield, hpoint, heq', ?_⟩
  intro α Ω Ω₀ hΩ hΩc hΩs hΩ₀ hΩ₀c hΩ₀Ω c d hc hd
  exact exists_local_second_weak_derivative_of_heat_timeH1 hG hT.le hreg q
    hCg hequiv Cv hCv0 hCvtop hvol α hΩ hΩc hΩs hΩ₀ hΩ₀c hΩ₀Ω hc hd V f w hwmass hwderiv

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
