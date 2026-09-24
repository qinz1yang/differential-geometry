import DifferentialGeometry.Analysis.Parabolic.Dirichlet.HeatEvolution
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.SmoothTimeTest
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeWeakDual

noncomputable section

open Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Sobolev.Hs
open DifferentialGeometry.Geometry.Connection
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

theorem integral_spacetime_test_of_heat_weak_solution
    (q : SmoothRiemannianMetric I_hs M)
    (g : ℝ → SmoothRiemannianMetric I_hs M)
    (a : ℝ → M → ℝ)
    {T : ℝ} (hT : 0 ≤ T)
    (u : timeH1 (DirichletHs q (-1)) T) (U₀ f : ℝ → DirichletHs q 0)
    (hpoint : ∀ t ∈ Icc (0 : ℝ) T,
      dirichletHsInclusion (show (-1 : ℝ) ≤ 0 by norm_num) (U₀ t) = u.toFun t)
    (heq : ∀ᵐ t ∂timeMeasure T, ∀ v : SmoothScalarDirichlet q,
      dirichletHsNegOneEquivH1Dual q (u.deriv t) (smoothToH1ComplDirichlet q v) =
        (∫ x, dirichletHsZeroEquivL2 q (U₀ t) x *
          (riemannianVolumeDensity q (g t) x *
            laplacian (leviCivitaConnectionOfMetric (g t)) (g t)
              (fun y => v.toFun y / riemannianVolumeDensity q (g t) y) x -
            a t x * v.toFun x)
          ∂riemannianVolumeMeasure (I := I_hs) (M := M) q) +
        ∫ x, dirichletHsZeroEquivL2 q (f t) x * v.toFun x
          ∂riemannianVolumeMeasure (I := I_hs) (M := M) q)
    {φ : ℝ × M → ℝ} (hφ : ContMDiff (𝓘(ℝ).prod I_hs) 𝓘(ℝ) ∞ φ)
    (hφc : HasCompactSupport φ) (hφi : tsupport φ ⊆ univ ×ˢ (I_hs).interior M)
    (hφT : ∀ x, φ (T, x) = 0) :
    (∫ t, ∫ x, dirichletHsZeroEquivL2 q (U₀ t) x * deriv (fun s => φ (s, x)) t
      ∂riemannianVolumeMeasure (I := I_hs) (M := M) q ∂timeMeasure T) +
    (∫ t, (∫ x, dirichletHsZeroEquivL2 q (U₀ t) x *
        (riemannianVolumeDensity q (g t) x *
          laplacian (leviCivitaConnectionOfMetric (g t)) (g t)
            (fun y => φ (t, y) / riemannianVolumeDensity q (g t) y) x - a t x * φ (t, x))
        ∂riemannianVolumeMeasure (I := I_hs) (M := M) q) +
      ∫ x, dirichletHsZeroEquivL2 q (f t) x * φ (t, x)
        ∂riemannianVolumeMeasure (I := I_hs) (M := M) q ∂timeMeasure T) =
      -(∫ x, dirichletHsZeroEquivL2 q (U₀ 0) x * φ (0, x)
        ∂riemannianVolumeMeasure (I := I_hs) (M := M) q) := by
  let v : ℝ → SmoothScalarDirichlet q := fun t =>
    ⟨fun x => φ (t, x), hφ.comp (contMDiff_const.prodMk contMDiff_id), by
      intro x hx
      exact (hφi ((tsupport_comp_subset_preimage φ (f := fun y : M => (t, y))
        (continuous_const.prodMk continuous_id)) hx)).2⟩
  have hvT : v T = 0 := by ext x; exact hφT x
  obtain ⟨z, _, hz, hzd⟩ :=
    exists_timeH1_comp_clm (dirichletHsNegOneEquivH1Dual q).toContinuousLinearMap u
  simp only [ContinuousLinearEquiv.coe_coe] at hz hzd
  have hmass : ∀ᵐ t ∂timeMeasure T, ∀ y,
      z.toFun t y = inner ℝ (dirichletHsZeroEquivL2 q (U₀ t)) (H1ComplDirichletToLp q y) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    intro y
    rw [hz t ht, ← hpoint t ht]
    exact dirichletHsNegOneEquivH1Dual_inclusion_zero_apply q (U₀ t) y
  have h := integral_smooth_test_of_timeH1_mass_dual q hT
    (fun t => dirichletHsZeroEquivL2 q (U₀ t)) z hmass v hφ hφc hφi hvT
  have hz0 : z.toFun 0 (smoothToH1ComplDirichlet q (v 0)) =
      ∫ x, dirichletHsZeroEquivL2 q (U₀ 0) x * φ (0, x)
        ∂riemannianVolumeMeasure (I := I_hs) (M := M) q := by
    rw [hz 0 ⟨le_rfl, hT⟩, ← hpoint 0 ⟨le_rfl, hT⟩]
    exact dirichletHsNegOneEquivH1Dual_inclusion_zero_apply_smooth q (U₀ 0) (v 0)
  rw [hz0] at h
  refine Eq.trans ?_ h
  apply congrArg₂ (fun b c : ℝ => b + c) rfl
  apply integral_congr_ae
  filter_upwards [heq, hzd] with t heqt hzdt
  rw [hzdt]
  exact (heqt (v t)).symm


private theorem contMDiff_mul_volumeDensity_of_tsupport_subset
    (q : SmoothRiemannianMetric I_hs M) (g : ℝ → SmoothRiemannianMetric I_hs M)
    {D : RealTimeInterval} (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D g)
    {φ : ℝ × M → ℝ} (hφ : ContMDiff (𝓘(ℝ).prod I_hs) 𝓘(ℝ) ∞ φ)
    (hφi : tsupport φ ⊆ D.regular ×ˢ (univ : Set M)) :
    ContMDiff (𝓘(ℝ).prod I_hs) 𝓘(ℝ) ∞
      (fun p : ℝ × M => riemannianVolumeDensity q (g p.1) p.2 * φ p) := by
  let G : MetricConnectionFamilyOn (I := I_hs) (M := M) D :=
    { metric := g
      connection := fun t => leviCivitaConnectionOfMetric (g t)
      metricCompatible := fun t => leviCivitaConnectionOfMetric_isMetricCompatible (g t) }
  let ρ := fun p : ℝ × M => riemannianVolumeDensity q (g p.1) p.2
  let ψ := fun p : ℝ × M => ρ p * φ p
  have hρ := riemannianVolumeDensity_contMDiffOn_of_metricFamilySmoothOn (G := G) hG q
  have hψ : ContMDiff (𝓘(ℝ).prod I_hs) 𝓘(ℝ) ∞ ψ := by
    intro p
    by_cases hp : p.1 ∈ D.regular
    · exact (hρ.contMDiffAt ((D.regular_isOpen.prod isOpen_univ).mem_nhds
        ⟨hp, mem_univ _⟩)).mul (hφ p)
    · have hn : p ∉ tsupport φ := fun hs => hp (hφi hs).1
      apply (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hn] with z hz
      dsimp only [ψ]
      rw [image_eq_zero_of_notMem_tsupport hz, mul_zero]
  exact hψ

private theorem integral_heat_test_mul_volumeDensity
    (q : SmoothRiemannianMetric I_hs M) (g : ℝ → SmoothRiemannianMetric I_hs M)
    {D : RealTimeInterval} (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D g)
    {T : ℝ} (hreg : Icc (0 : ℝ) T ⊆ D.regular)
    (U f a : ℝ → M → ℝ)
    {φ : ℝ × M → ℝ} (hφ : ContMDiff (𝓘(ℝ).prod I_hs) 𝓘(ℝ) ∞ φ) :
    let ψ := fun p : ℝ × M => riemannianVolumeDensity q (g p.1) p.2 * φ p
    (∫ t, ∫ x, U t x *
      (deriv (fun s => φ (s, x)) t + (1 / 2) * traceTimeDerivMetric (I := I_hs) g t x * φ (t, x))
      ∂riemannianVolumeMeasure (I := I_hs) (M := M) (g t) ∂timeMeasure T) +
    (∫ t, (∫ x, U t x *
        (laplacian (leviCivitaConnectionOfMetric (g t)) (g t) (fun y => φ (t, y)) x - a t x * φ (t, x))
        ∂riemannianVolumeMeasure (I := I_hs) (M := M) (g t)) +
      ∫ x, f t x * φ (t, x)
        ∂riemannianVolumeMeasure (I := I_hs) (M := M) (g t) ∂timeMeasure T) =
    (∫ t, ∫ x, U t x * deriv (fun s => ψ (s, x)) t
      ∂riemannianVolumeMeasure (I := I_hs) (M := M) q ∂timeMeasure T) +
    (∫ t, (∫ x, U t x *
        (riemannianVolumeDensity q (g t) x * laplacian (leviCivitaConnectionOfMetric (g t)) (g t)
          (fun y => ψ (t, y) / riemannianVolumeDensity q (g t) y) x - a t x * ψ (t, x))
        ∂riemannianVolumeMeasure (I := I_hs) (M := M) q) +
      ∫ x, f t x * ψ (t, x)
        ∂riemannianVolumeMeasure (I := I_hs) (M := M) q ∂timeMeasure T) := by
  intro ψ
  let G : MetricConnectionFamilyOn (I := I_hs) (M := M) D :=
    { metric := g
      connection := fun t => leviCivitaConnectionOfMetric (g t)
      metricCompatible := fun t => leviCivitaConnectionOfMetric_isMetricCompatible (g t) }
  have hgram := fun α i j => MetricFamilySmoothOn.chartGramMatrix_contDiffOn (G := G)
    hG (J := D.regular) Subset.rfl α i j
  apply congrArg₂ (fun b c : ℝ => b + c)
  · apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [integral_riemannianVolumeMeasure_eq_integral_volumeDensity_smul q (g t)]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      have hdρ := hasDerivAt_riemannianVolumeDensity_of_chartGram_contMDiffOn q
        D.regular_isOpen hgram (hreg ht) x
      have hdφ : HasDerivAt (fun s => φ (s, x)) (deriv (fun s => φ (s, x)) t) t :=
        ((hφ.comp (contMDiff_id.prodMk contMDiff_const)).contDiff.differentiable
          (by simp) t).hasDerivAt
      have hd := (hdρ.fun_mul hdφ).deriv
      dsimp only [G] at hd
      dsimp only [ψ, smul_eq_mul]
      rw [hd]
      ring
  · apply integral_congr_ae
    exact Eventually.of_forall fun t => by
      dsimp only
      have hquot : (fun y => ψ (t, y) / riemannianVolumeDensity q (g t) y) =
          fun y => φ (t, y) := by
        funext y
        exact mul_div_cancel_left₀ _ (ne_of_gt (riemannianVolumeDensity_pos q (g t) y))
      rw [hquot, integral_riemannianVolumeMeasure_eq_integral_volumeDensity_smul q (g t),
        integral_riemannianVolumeMeasure_eq_integral_volumeDensity_smul q (g t)]
      apply congrArg₂ (fun b c : ℝ => b + c)
      · apply integral_congr_ae
        exact Eventually.of_forall fun x => by dsimp only [ψ, smul_eq_mul]; ring
      · apply integral_congr_ae
        exact Eventually.of_forall fun x => by dsimp only [ψ, smul_eq_mul]; ring


theorem integral_spacetime_test_evolving_volume_of_heat_weak_solution
    (q : SmoothRiemannianMetric I_hs M)
    (g : ℝ → SmoothRiemannianMetric I_hs M)
    {D : RealTimeInterval}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D g)
    (a : ℝ → M → ℝ)
    {T : ℝ} (hT : 0 ≤ T) (hreg : Icc (0 : ℝ) T ⊆ D.regular)
    (u : timeH1 (DirichletHs q (-1)) T) (U₀ f : ℝ → DirichletHs q 0)
    (hpoint : ∀ t ∈ Icc (0 : ℝ) T,
      dirichletHsInclusion (show (-1 : ℝ) ≤ 0 by norm_num) (U₀ t) = u.toFun t)
    (heq : ∀ᵐ t ∂timeMeasure T, ∀ v : SmoothScalarDirichlet q,
      dirichletHsNegOneEquivH1Dual q (u.deriv t) (smoothToH1ComplDirichlet q v) =
        (∫ x, dirichletHsZeroEquivL2 q (U₀ t) x *
          (riemannianVolumeDensity q (g t) x *
            laplacian (leviCivitaConnectionOfMetric (g t)) (g t)
              (fun y => v.toFun y / riemannianVolumeDensity q (g t) y) x -
            a t x * v.toFun x)
          ∂riemannianVolumeMeasure (I := I_hs) (M := M) q) +
        ∫ x, dirichletHsZeroEquivL2 q (f t) x * v.toFun x
          ∂riemannianVolumeMeasure (I := I_hs) (M := M) q)
    {φ : ℝ × M → ℝ} (hφ : ContMDiff (𝓘(ℝ).prod I_hs) 𝓘(ℝ) ∞ φ)
    (hφc : HasCompactSupport φ) (hφi : tsupport φ ⊆ D.regular ×ˢ (I_hs).interior M)
    (hφT : ∀ x, φ (T, x) = 0) :
    (∫ t, ∫ x, dirichletHsZeroEquivL2 q (U₀ t) x *
      (deriv (fun s => φ (s, x)) t + (1 / 2) * traceTimeDerivMetric (I := I_hs) g t x * φ (t, x))
      ∂riemannianVolumeMeasure (I := I_hs) (M := M) (g t) ∂timeMeasure T) +
    (∫ t, (∫ x, dirichletHsZeroEquivL2 q (U₀ t) x *
        (laplacian (leviCivitaConnectionOfMetric (g t)) (g t) (fun y => φ (t, y)) x -
          a t x * φ (t, x))
        ∂riemannianVolumeMeasure (I := I_hs) (M := M) (g t)) +
      ∫ x, dirichletHsZeroEquivL2 q (f t) x * φ (t, x)
        ∂riemannianVolumeMeasure (I := I_hs) (M := M) (g t) ∂timeMeasure T) =
      -(∫ x, dirichletHsZeroEquivL2 q (U₀ 0) x * φ (0, x)
        ∂riemannianVolumeMeasure (I := I_hs) (M := M) (g 0)) := by
  let ψ := fun p : ℝ × M => riemannianVolumeDensity q (g p.1) p.2 * φ p
  have hψs : tsupport ψ ⊆ tsupport φ := tsupport_mul_subset_right
  have hψ : ContMDiff (𝓘(ℝ).prod I_hs) 𝓘(ℝ) ∞ ψ :=
    contMDiff_mul_volumeDensity_of_tsupport_subset q g hG hφ
      (hφi.trans (prod_mono Subset.rfl (subset_univ _)))
  have hψc : HasCompactSupport ψ := hφc.of_isClosed_subset (isClosed_tsupport _) hψs
  have hψi : tsupport ψ ⊆ univ ×ˢ (I_hs).interior M :=
    hψs.trans (hφi.trans (prod_mono (subset_univ _) Subset.rfl))
  have hψT (x : M) : ψ (T, x) = 0 := by simp only [ψ, hφT, mul_zero]
  have h := integral_spacetime_test_of_heat_weak_solution q g a hT u U₀ f hpoint heq
    hψ hψc hψi hψT
  have hzero : (∫ x, dirichletHsZeroEquivL2 q (U₀ 0) x * ψ (0, x)
      ∂riemannianVolumeMeasure (I := I_hs) (M := M) q) =
      ∫ x, dirichletHsZeroEquivL2 q (U₀ 0) x * φ (0, x)
        ∂riemannianVolumeMeasure (I := I_hs) (M := M) (g 0) := by
    rw [integral_riemannianVolumeMeasure_eq_integral_volumeDensity_smul q (g 0)]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by dsimp only [ψ, smul_eq_mul]; ring
  rw [hzero] at h
  exact (integral_heat_test_mul_volumeDensity q g hG hreg
    (fun t => dirichletHsZeroEquivL2 q (U₀ t))
    (fun t => dirichletHsZeroEquivL2 q (f t)) a hφ).trans h


theorem exists_local_dirichlet_heat_distribution_solution
    {D : RealTimeInterval}
    {g : ℝ → SmoothRiemannianMetric I_hs M}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D g)
    (h0reg : (0 : ℝ) ∈ D.regular)
    (a : ℝ → C^∞⟮I_hs, M; ℝ⟯)
    (ha : ContinuousOn (fun p : ℝ × M => a p.1 p.2)
      (D.regular ×ˢ (Set.univ : Set M))) :
    let q := g 0
    ∃ T : ℝ, 0 < T ∧ Icc (0 : ℝ) T ⊆ D.regular ∧
      ∀ (u₀ : DirichletHs q 0) (f₀ : timeL2 (DirichletHs q 0) T),
        ∃ (u : timeH1 (DirichletHs q (-1)) T)
          (U₂ : timeL2 (DirichletHs q 1) T) (U₀ : ℝ → DirichletHs q 0),
          ContinuousOn U₀ (Icc (0 : ℝ) T) ∧ U₀ 0 = u₀ ∧
          (fun t => dirichletHsInclusion (show (0 : ℝ) ≤ 1 by norm_num) (U₂ t))
            =ᵐ[timeMeasure T] U₀ ∧
          (∀ t ∈ Icc (0 : ℝ) T,
            dirichletHsInclusion (show (-1 : ℝ) ≤ 0 by norm_num) (U₀ t) = u.toFun t) ∧
          ∀ (φ : ℝ × M → ℝ), ContMDiff (𝓘(ℝ).prod I_hs) 𝓘(ℝ) ∞ φ →
            HasCompactSupport φ → tsupport φ ⊆ univ ×ˢ (I_hs).interior M →
            (∀ x, φ (T, x) = 0) →
              (∫ t, ∫ x, dirichletHsZeroEquivL2 q (U₀ t) x * deriv (fun s => φ (s, x)) t
                ∂riemannianVolumeMeasure (I := I_hs) (M := M) q ∂timeMeasure T) +
              (∫ t, (∫ x, dirichletHsZeroEquivL2 q (U₀ t) x *
                  (riemannianVolumeDensity q (g t) x *
                    laplacian (leviCivitaConnectionOfMetric (g t)) (g t)
                      (fun y => φ (t, y) / riemannianVolumeDensity q (g t) y) x - a t x * φ (t, x))
                  ∂riemannianVolumeMeasure (I := I_hs) (M := M) q) +
                ∫ x, dirichletHsZeroEquivL2 q (f₀ t) x * φ (t, x)
                  ∂riemannianVolumeMeasure (I := I_hs) (M := M) q ∂timeMeasure T) =
                -(∫ x, dirichletHsZeroEquivL2 q u₀ x * φ (0, x)
                  ∂riemannianVolumeMeasure (I := I_hs) (M := M) q) := by
  intro q
  obtain ⟨T, hT, hreg, hsol⟩ := exists_local_dirichlet_heat_weak_solution hG h0reg a ha
  refine ⟨T, hT, hreg, fun u₀ f₀ => ?_⟩
  let ι : DirichletHs q 0 →L[ℝ] DirichletHs q (-1) :=
    dirichletHsInclusion (show (-1 : ℝ) ≤ 0 by norm_num)
  obtain ⟨u, U₂, U₀, hcont, hinit, hfield, hpoint, heq⟩ :=
    hsol u₀ (ι.compLpL 2 (timeMeasure T) f₀)
  refine ⟨u, U₂, U₀, hcont, hinit, hfield, hpoint, ?_⟩
  intro φ hφ hφc hφi hφT
  have hsource := ι.coeFn_compLpL (p := 2) (μ := timeMeasure T) f₀
  have hspatial : ∀ᵐ t ∂timeMeasure T, ∀ v : SmoothScalarDirichlet q,
      dirichletHsNegOneEquivH1Dual q (u.deriv t) (smoothToH1ComplDirichlet q v) =
        (∫ x, dirichletHsZeroEquivL2 q (U₀ t) x *
          (riemannianVolumeDensity q (g t) x *
            laplacian (leviCivitaConnectionOfMetric (g t)) (g t)
              (fun y => v.toFun y / riemannianVolumeDensity q (g t) y) x -
            a t x * v.toFun x)
          ∂riemannianVolumeMeasure (I := I_hs) (M := M) q) +
        ∫ x, dirichletHsZeroEquivL2 q (f₀ t) x * v.toFun x
          ∂riemannianVolumeMeasure (I := I_hs) (M := M) q := by
    filter_upwards [heq, hsource] with t ht hft
    intro v
    rw [ht v, hft]
    congr 1
    exact dirichletHsNegOneEquivH1Dual_inclusion_zero_apply_smooth q (f₀ t) v
  simpa only [hinit] using integral_spacetime_test_of_heat_weak_solution q g (fun t x => a t x) hT.le
    u U₀ f₀ hpoint hspatial hφ hφc hφi hφT

theorem integral_spacetime_test_of_heat_timeH1
    (q : SmoothRiemannianMetric I_hs M) (g : ℝ → SmoothRiemannianMetric I_hs M)
    {T : ℝ} (hT : 0 ≤ T)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, ∀ w : TangentSpace I_hs x,
      Cg⁻¹ * q.inner x w w ≤ (g t).inner x w w ∧
        (g t).inner x w w ≤ Cg * q.inner x w w)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : ∀ t ∈ Icc (0 : ℝ) T,
      riemannianVolumeMeasure (I := I_hs) (M := M) (g t) ≤
        Cv • riemannianVolumeMeasure (I := I_hs) (M := M) q)
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
    {φ : ℝ × M → ℝ} (hφ : ContMDiff (𝓘(ℝ).prod I_hs) 𝓘(ℝ) ∞ φ)
    (hφc : HasCompactSupport φ) (hφi : tsupport φ ⊆ univ ×ˢ (I_hs).interior M)
    (hφ0 : ∀ x, φ (0, x) = 0) (hφT : ∀ x, φ (T, x) = 0) :
    (∫ t, ∫ x, H1ComplDirichletToLp q (u t) x * deriv (fun s => φ (s, x)) t
      ∂riemannianVolumeMeasure (I := I_hs) (M := M) q ∂timeMeasure T) +
      (∫ t, (∫ x, H1ComplDirichletToLp q (u t) x *
        (riemannianVolumeDensity q (g t) x * laplacian (leviCivitaConnectionOfMetric (g t))
          (g t) (fun y => φ (t, y) / riemannianVolumeDensity q (g t) y) x)
        ∂riemannianVolumeMeasure (I := I_hs) (M := M) q) +
          ∫ x, f t x * φ (t, x) ∂riemannianVolumeMeasure (I := I_hs) (M := M) q
            ∂timeMeasure T) = 0 := by
  let v : ℝ → SmoothScalarDirichlet q := fun t =>
    ⟨fun x => φ (t, x), hφ.comp (contMDiff_const.prodMk contMDiff_id), by
      intro x hx
      exact (hφi ((tsupport_comp_subset_preimage φ (f := fun y : M => (t, y))
        (continuous_const.prodMk continuous_id)) hx)).2⟩
  have hv0 : v 0 = 0 := by ext x; exact hφ0 x
  have hvT : v T = 0 := by ext x; exact hφT x
  have h := integral_smooth_test_of_timeH1_mass_dual q hT
    (fun t => H1ComplDirichletToLp q (u t)) w hwmass v hφ hφc hφi hvT
  simp only [hv0, map_zero, neg_zero] at h
  refine Eq.trans ?_ h
  apply congrArg₂ (fun a b : ℝ => a + b) rfl
  apply integral_congr_ae
  filter_upwards [hwderiv, ae_restrict_mem measurableSet_Icc] with t heqt ht
  rw [heqt ht (smoothToH1ComplDirichlet q (v t)),
    dirichletWeakFormCompl_volumeDensity_eq_integral_laplacian_adjoint]
  congr 1
  rw [H1ComplDirichletToLp_smoothToH1ComplDirichlet, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (v t).memLp_two] with x hx
  change (smoothToLpDirichlet q (v t) : M → ℝ) x = (v t).toFun x at hx
  rw [hx]
  simp only [Real.inner_apply, v, mul_comm]

theorem integral_spacetime_test_evolving_volume_of_heat_timeH1
    (q : SmoothRiemannianMetric I_hs M) (g : ℝ → SmoothRiemannianMetric I_hs M)
    {D : RealTimeInterval} (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D g)
    {T : ℝ} (hT : 0 ≤ T) (hreg : Icc (0 : ℝ) T ⊆ D.regular)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, ∀ w : TangentSpace I_hs x,
      Cg⁻¹ * q.inner x w w ≤ (g t).inner x w w ∧
        (g t).inner x w w ≤ Cg * q.inner x w w)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : ∀ t ∈ Icc (0 : ℝ) T,
      riemannianVolumeMeasure (I := I_hs) (M := M) (g t) ≤
        Cv • riemannianVolumeMeasure (I := I_hs) (M := M) q)
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
    {φ : ℝ × M → ℝ} (hφ : ContMDiff (𝓘(ℝ).prod I_hs) 𝓘(ℝ) ∞ φ)
    (hφc : HasCompactSupport φ) (hφi : tsupport φ ⊆ D.regular ×ˢ (I_hs).interior M)
    (hφ0 : ∀ x, φ (0, x) = 0) (hφT : ∀ x, φ (T, x) = 0) :
    (∫ t, ∫ x, H1ComplDirichletToLp q (u t) x *
      (deriv (fun s => φ (s, x)) t + (1 / 2) * traceTimeDerivMetric (I := I_hs) g t x * φ (t, x))
      ∂riemannianVolumeMeasure (I := I_hs) (M := M) (g t) ∂timeMeasure T) +
      (∫ t, (∫ x, H1ComplDirichletToLp q (u t) x *
        laplacian (leviCivitaConnectionOfMetric (g t)) (g t) (fun y => φ (t, y)) x
        ∂riemannianVolumeMeasure (I := I_hs) (M := M) (g t)) +
          ∫ x, f t x * φ (t, x) ∂riemannianVolumeMeasure (I := I_hs) (M := M) (g t)
            ∂timeMeasure T) = 0 := by
  let ψ := fun p : ℝ × M => riemannianVolumeDensity q (g p.1) p.2 * φ p
  have hψs : tsupport ψ ⊆ tsupport φ := tsupport_mul_subset_right
  have hψ : ContMDiff (𝓘(ℝ).prod I_hs) 𝓘(ℝ) ∞ ψ :=
    contMDiff_mul_volumeDensity_of_tsupport_subset q g hG hφ
      (hφi.trans (prod_mono Subset.rfl (subset_univ _)))
  have hψc : HasCompactSupport ψ := hφc.of_isClosed_subset (isClosed_tsupport _) hψs
  have hψi : tsupport ψ ⊆ univ ×ˢ (I_hs).interior M :=
    hψs.trans (hφi.trans (prod_mono (subset_univ _) Subset.rfl))
  have hψT (x : M) : ψ (T, x) = 0 := by simp only [ψ, hφT, mul_zero]
  have hψ0 (x : M) : ψ (0, x) = 0 := by simp only [ψ, hφ0, mul_zero]
  have h := integral_spacetime_test_of_heat_timeH1 q g hT hCg hequiv Cv hCv0 hCvtop hvol
    u f w hwmass hwderiv hψ hψc hψi hψ0 hψT
  have he := integral_heat_test_mul_volumeDensity q g hG hreg
    (fun t => H1ComplDirichletToLp q (u t)) (fun t => f t) (fun _ _ => 0) hφ
  simp only [zero_mul, sub_zero] at he
  exact he.trans h

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
