import DifferentialGeometry.Analysis.Parabolic.Dirichlet.HessianScalarSource
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.LocalSecondDerivative
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeMeasureRestrict

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold NNReal Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
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

theorem IsWeakEvolutionSolution.exists_local_fourth_weak_derivative
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
    {t₀ t₁ : ℝ} (ht₀ : 0 < t₀) (ht₁ : t₁ < T) (ht₀₁ : t₀ ≤ t₁)
    {Ω₀ : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω) :
    let μ₀ := (timeMeasure T).restrict (Icc t₀ t₁)
    ∀ H₀ : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) →
        Lp ℝ 2 (μ₀.prod (volume.restrict Ω₀)),
      (∀ i j, ∀ᵐ t ∂μ₀, DeGiorgi.HasWeakPartialDeriv j
        (fun z => H₀ i j (t, z))
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) Ω₀) →
      ∀ K₀ : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) →
          Fin (Module.finrank ℝ EuN) → Lp ℝ 2 (μ₀.prod (volume.restrict Ω₀)),
        (∀ i j k, ∀ᵐ t ∂μ₀, DeGiorgi.HasWeakPartialDeriv k
          (fun z => K₀ i j k (t, z)) (fun z => H₀ i j (t, z)) Ω₀) →
        ∃ L : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) →
            Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) →
            Lp ℝ 2 (μ₀.prod (volume.restrict Ω₀)),
          ∀ i j k l, ∀ᵐ t ∂μ₀, DeGiorgi.HasWeakPartialDeriv l
            (fun z => L i j k l (t, z)) (fun z => K₀ i j k (t, z)) Ω₀ := by
  intro μ₀ H₀ hH₀ K₀ hK₀
  classical
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  obtain ⟨Ω₁, hΩ₁, hΩ₀₁, hΩ₁Ω, hΩ₁c⟩ :=
    exists_open_between_and_isCompact_closure hΩ₀c hΩ hΩ₀Ω
  have hΩ₁s := hΩ₁Ω.trans (subset_closure.trans hΩs)
  obtain ⟨δ, η, _, _, hη, hηc, _, hηone, hηs⟩ :=
    exists_smooth_cutoff_with_neighborhood hΩ₀c hΩ₁ hΩ₀₁
  have hηone' : ∀ z ∈ Ω₀, η z = 1 := fun z hz =>
    hηone z (Metric.self_subset_cthickening (closure Ω₀) (subset_closure hz))
  let s₀ := t₀ / 2
  let s₁ := (t₁ + T) / 2
  have hs₀ : 0 < s₀ := by dsimp [s₀]; linarith
  have hs₁ : s₁ < T := by dsimp [s₁]; linarith
  have hs₀t₀ : s₀ < t₀ := by dsimp [s₀]; linarith
  have ht₁s₁ : t₁ < s₁ := by dsimp [s₁]; linarith
  have hs₀₁ : s₀ < s₁ := lt_of_lt_of_le hs₀t₀ (ht₀₁.trans ht₁s₁.le)
  have hI : Icc s₀ s₁ ⊆ Icc (0 : ℝ) T :=
    Icc_subset_Icc hs₀.le hs₁.le
  have htarget : Icc t₀ t₁ ⊆ Icc s₀ s₁ :=
    Icc_subset_Icc hs₀t₀.le ht₁s₁.le
  let μ := (timeMeasure T).restrict (Icc s₀ s₁)
  have hμ : μ = volume.restrict (Icc s₀ s₁) :=
    timeMeasure_restrict_Icc_eq_volume_restrict_Icc hI
  have hex := hu.exists_timeH1_cutoff_hessian_scalar_source hXcont hacont α hΩ hΩc hΩs
    hXsmooth hs₀ hs₁ hs₀₁ hΩ₁ hΩ₁Ω hη hηs
  let H := hex.choose
  let K := hex.choose_spec.choose
  let S := hex.choose_spec.choose_spec.choose
  have hp := hex.choose_spec.choose_spec.choose_spec
  have hH := hp.1
  have hK := hp.2.2.1
  have hpacket := hp.2.2.2.2.2
  let v := hpacket.choose
  have hrep := hpacket.choose_spec.1
  have htime := hpacket.choose_spec.2
  choose ℓ w β f hwmass hwderiv hpair hf hsource using htime
  have hμ₀ : μ₀ = volume.restrict (Icc t₀ t₁) :=
    timeMeasure_restrict_Icc_eq_volume_restrict_Icc
      (Icc_subset_Icc ht₀.le ht₁.le)
  have hμrestrict : (volume.restrict (Icc s₀ s₁)).restrict (Icc t₀ t₁) = μ₀ := by
    rw [Measure.restrict_restrict_of_subset htarget, hμ₀]
  have hμrestrict' : μ.restrict (Icc t₀ t₁) = μ₀ := by
    rw [hμ, hμrestrict]
  have hLexist (i j) : ∃ L : Fin (Module.finrank ℝ EuN) →
        Fin (Module.finrank ℝ EuN) → Lp ℝ 2 (μ₀.prod (volume.restrict Ω₀)),
      ∀ k l, ∀ᵐ t ∂μ₀, DeGiorgi.HasWeakPartialDeriv l
        (fun z => L k l (t, z))
        (dirichletLocalWeakPartialLp q α hΩ₁ hΩ₁c hΩ₁s k (v i j t)) Ω₀ := by
    have hexL := exists_local_dirichlet_second_weak_derivative_of_timeH1_of_measure_eq_volume
      hG hs₀₁.le (hI.trans hreg) q α hΩ₁ hΩ₁c hΩ₁s hs₀t₀ ht₁s₁ hμ
      (v i j) (f i j) (ℓ i j) (β i j) (w i j) (hwmass i j) (hwderiv i j) (hpair i j)
      (hsource i j) hΩ₀ hΩ₀₁
    rw [hμrestrict] at hexL
    obtain ⟨L, hL, _⟩ := hexL
    exact ⟨L, hL⟩
  choose L hL using hLexist
  have hsub₀₁ : Ω₀ ⊆ Ω₁ := subset_closure.trans hΩ₀₁
  have hμle : μ₀ ≤ μ := by
    rw [← hμrestrict']
    exact Measure.restrict_le_self
  have hHeq (i j) : ∀ᵐ t ∂μ₀,
      (fun z => H i j (t, z)) =ᵐ[volume.restrict Ω₀] fun z => H₀ i j (t, z) := by
    filter_upwards [(hH i j).filter_mono (ae_mono hμle), hH₀ i j,
      ((Lp.memLp (H i j)).prodMk_left (by norm_num)).filter_mono (ae_mono hμle),
      (Lp.memLp (H₀ i j)).prodMk_left (by norm_num)] with t ht ht₀ hm hm₀
    exact DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ₀
      (DeGiorgi.HasWeakPartialDeriv.restrict hΩ₀ hsub₀₁ ht) ht₀
      ((hm.mono_measure (Measure.restrict_mono hsub₀₁ le_rfl)).locallyIntegrable (by norm_num))
      (hm₀.locallyIntegrable (by norm_num))
  have hKeq (i j k) : ∀ᵐ t ∂μ₀,
      (fun z => K i j k (t, z)) =ᵐ[volume.restrict Ω₀] fun z => K₀ i j k (t, z) := by
    filter_upwards [(hK i j k).filter_mono (ae_mono hμle), hK₀ i j k, hHeq i j,
      ((Lp.memLp (K i j k)).prodMk_left (by norm_num)).filter_mono (ae_mono hμle),
      (Lp.memLp (K₀ i j k)).prodMk_left (by norm_num)] with t ht ht₀ he hm hm₀
    exact DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ₀
      (hasWeakPartialDeriv_congr_ae hΩ₀ k he
        (DeGiorgi.HasWeakPartialDeriv.restrict hΩ₀ hsub₀₁ ht)) ht₀
      ((hm.mono_measure (Measure.restrict_mono hsub₀₁ le_rfl)).locallyIntegrable (by norm_num))
      (hm₀.locallyIntegrable (by norm_num))
  have hηderiv : ∀ z ∈ Ω₀, fderiv ℝ η z = 0 := by
    intro z hz
    have heq : η =ᶠ[𝓝 z] fun _ => (1 : ℝ) :=
      Filter.eventually_of_mem (hΩ₀.mem_nhds hz) fun y hy => hηone' y hy
    simpa only [fderiv_const_apply] using heq.fderiv_eq (𝕜 := ℝ)
  have halign (i j k) : ∀ᵐ t ∂μ₀,
      (dirichletLocalWeakPartialLp q α hΩ₁ hΩ₁c hΩ₁s k (v i j t) : EuStd → ℝ)
        =ᵐ[volume.restrict Ω₀] fun z => K i j k (t, z) := by
    have hformula := ae_dirichletLocalWeakPartialLp_eq_of_chartPullback_mul
      q α hΩ₁ hΩ₁c hΩ₁s (fun t => v i j t) (hrep i j)
      (Lp.memLp (H i j)) (Lp.memLp (K i j k)) k (hK i j k) hη
    filter_upwards [hformula.filter_mono (ae_mono hμle)] with t ht
    have ht' := ht.filter_mono (ae_mono (Measure.restrict_mono hsub₀₁ le_rfl))
    filter_upwards [ht', ae_restrict_mem hΩ₀.measurableSet] with z hz hzm
    simpa only [hηone' z hzm, hηderiv z hzm, zero_apply,
      one_mul, zero_mul, add_zero] using hz
  refine ⟨L, ?_⟩
  intro i j k l
  filter_upwards [hL i j k l, halign i j k, hKeq i j k] with t ht ha he
  exact hasWeakPartialDeriv_congr_ae hΩ₀ l (ha.trans he) ht

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
