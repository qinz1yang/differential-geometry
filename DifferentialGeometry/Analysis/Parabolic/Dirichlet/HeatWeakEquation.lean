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

private theorem exists_smooth_dirichlet_time_test
    (q : SmoothRiemannianMetric I_hs M) {φ : ℝ × M → ℝ}
    (hφ : ContMDiff (𝓘(ℝ).prod I_hs) 𝓘(ℝ) ∞ φ)
    (hφc : HasCompactSupport φ) (hφi : tsupport φ ⊆ univ ×ˢ (I_hs).interior M)
    {T : ℝ} (hT : 0 ≤ T) (hφT : ∀ x, φ (T, x) = 0) :
    ∃ (v v' : ℝ → SmoothScalarDirichlet q) (w : timeH1 (H1ComplDirichlet q) T),
      (∀ t x, (v t).toFun x = φ (t, x)) ∧
      (∀ t x, (v' t).toFun x = deriv (fun s => φ (s, x)) t) ∧
      EqOn w.toFun (fun t => smoothToH1ComplDirichlet q (v t)) (Icc (0 : ℝ) T) ∧
      w.deriv =ᵐ[timeMeasure T] (fun t => smoothToH1ComplDirichlet q (v' t)) ∧
      w.toFun T = 0 := by
  let K := Prod.snd '' tsupport φ
  have hK : IsCompact K := hφc.image continuous_snd
  have hKi : K ⊆ (I_hs).interior M := by
    rintro x ⟨p, hp, rfl⟩
    exact (hφi hp).2
  have hφK (t : ℝ) : tsupport (fun x => φ (t, x)) ⊆ K := by
    have h := tsupport_comp_subset_preimage φ (f := fun x : M => (t, x))
      (continuous_const.prodMk continuous_id)
    exact h.trans fun x hx => ⟨(t, x), hx, rfl⟩
  let ψ : ℝ × M → ℝ := fun p => deriv (fun s => φ (s, p.2)) p.1
  have hψ : ContMDiff (𝓘(ℝ).prod I_hs) 𝓘(ℝ) ∞ ψ := by
    intro p
    exact timeDeriv_smoothAt (hφ p) (by simp)
  have hψK (t : ℝ) : tsupport (fun x => ψ (t, x)) ⊆ K := by
    apply closure_minimal ?_ hK.isClosed
    intro x hx
    by_contra hnot
    have hz : (fun s => φ (s, x)) = fun _ => 0 := by
      funext s
      apply image_eq_zero_of_notMem_tsupport
      intro hs
      exact hnot ⟨(s, x), hs, rfl⟩
    have : ψ (t, x) = 0 := by
      dsimp only [ψ]
      rw [hz, deriv_const]
    exact hx this
  let v : ℝ → SmoothScalarDirichlet q := fun t =>
    ⟨fun x => φ (t, x), hφ.comp (contMDiff_const.prodMk contMDiff_id), (hφK t).trans hKi⟩
  let v' : ℝ → SmoothScalarDirichlet q := fun t =>
    ⟨fun x => ψ (t, x), hψ.comp (contMDiff_const.prodMk contMDiff_id), (hψK t).trans hKi⟩
  have hd (t : ℝ) (_ht : t ∈ (univ : Set ℝ)) (x : M) :
      HasDerivAt (fun s => (v s).toFun x) ((v' t).toFun x) t := by
    exact ((hφ.comp (contMDiff_id.prodMk contMDiff_const)).contDiff.differentiable
      (by simp) t).hasDerivAt
  have hvT : v T = 0 := by
    ext x
    exact hφT x
  obtain ⟨w, hw, hwd, _, hwT⟩ := exists_timeH1_smoothToH1ComplDirichlet q v v'
    isOpen_univ hφ.contMDiffOn hψ.contMDiffOn hd hK.isClosed hKi
    (fun t _ => hψK t) hT (subset_univ _) hvT
  exact ⟨v, v', w, fun _ _ => rfl, fun _ _ => rfl, hw, hwd, hwT⟩

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
  obtain ⟨v, v', w, hv, hv', hw, hwd, hwT⟩ :=
    exists_smooth_dirichlet_time_test q hφ hφc hφi hT hφT
  obtain ⟨z, _, hz, hzd⟩ :=
    exists_timeH1_comp_clm (dirichletHsNegOneEquivH1Dual q).toContinuousLinearMap u
  simp only [ContinuousLinearEquiv.coe_coe] at hz hzd
  have h := timeH1.integral_dual_deriv_add_deriv_dual hT z w
  have hz0 : z.toFun 0 (w.toFun 0) =
      ∫ x, dirichletHsZeroEquivL2 q (U₀ 0) x * φ (0, x)
        ∂riemannianVolumeMeasure (I := I_hs) (M := M) q := by
    rw [hz 0 ⟨le_rfl, hT⟩, hw ⟨le_rfl, hT⟩, ← hpoint 0 ⟨le_rfl, hT⟩]
    simpa only [hv] using
      dirichletHsNegOneEquivH1Dual_inclusion_zero_apply_smooth q (U₀ 0) (v 0)
  rw [hwT, map_zero, hz0, zero_sub] at h
  refine Eq.trans ?_ h
  apply congrArg₂ (fun b c : ℝ => b + c)
  · apply integral_congr_ae
    filter_upwards [hwd, ae_restrict_mem measurableSet_Icc] with t hdt ht
    rw [hz t ht, hdt, ← hpoint t ht]
    simpa only [hv'] using
      (dirichletHsNegOneEquivH1Dual_inclusion_zero_apply_smooth q (U₀ t) (v' t)).symm
  · apply integral_congr_ae
    filter_upwards [heq, hzd, ae_restrict_mem measurableSet_Icc] with t heqt hzdt ht
    rw [hzdt, hw ht]
    simpa only [hv] using (heqt (v t)).symm

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
  let G : MetricConnectionFamilyOn (I := I_hs) (M := M) D :=
    { metric := g
      connection := fun t => leviCivitaConnectionOfMetric (g t)
      metricCompatible := fun t => leviCivitaConnectionOfMetric_isMetricCompatible (g t) }
  have hgram := fun α i j => MetricFamilySmoothOn.chartGramMatrix_contDiffOn (G := G)
    hG (J := D.regular) Subset.rfl α i j
  let ρ := fun p : ℝ × M => riemannianVolumeDensity q (g p.1) p.2
  let ψ := fun p : ℝ × M => ρ p * φ p
  have hρ := riemannianVolumeDensity_contMDiffOn_of_metricFamilySmoothOn (G := G) hG q
  have hψs : tsupport ψ ⊆ tsupport φ := tsupport_mul_subset_right
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
    exact Eventually.of_forall fun x => by dsimp only [ψ, ρ, smul_eq_mul]; ring
  rw [hzero] at h
  refine Eq.trans ?_ h
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
      dsimp only [ψ, ρ, smul_eq_mul]
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
        exact Eventually.of_forall fun x => by dsimp only [ψ, ρ, smul_eq_mul]; ring
      · apply integral_congr_ae
        exact Eventually.of_forall fun x => by dsimp only [ψ, ρ, smul_eq_mul]; ring

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

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
