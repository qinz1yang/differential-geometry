import DifferentialGeometry.Analysis.Parabolic.Dirichlet.MixedTimeSpatialRegularity
import DifferentialGeometry.Analysis.Integration.Lp.Curry

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold NNReal Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
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

private local instance : MeasurableSpace EuStd :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ EuN)) → ℝ)

theorem IsWeakEvolutionSolution.exists_timeH1_localWeakPartial
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
    (hΩs : closure Ω ⊆ toEuclidean (E := EuclideanSpace ℝ (Fin n)) ''
      interior (extChartAt I_hs α).target)
    (hu : IsWeakEvolutionSolution hG hT hreg X a Bx Bv
      (fun t ht => hX t ⟨ht.1, ht.2.le⟩) htrace f₀ u)
    (hXsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) ((I_hs).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2))
      (D.regular ×ˢ (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I_hs) α).baseSet))
    {t₀ t₁ : ℝ} (ht₀ : 0 < t₀) (ht₁ : t₁ < T) (ht₀₁ : t₀ < t₁)
    {Ω₀ : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω) :
    ∀ i, ∃ w : timeH1 (Lp ℝ 2 (volume.restrict Ω₀)) (t₁ - t₀),
      ∀ᵐ s ∂timeMeasure (t₁ - t₀),
        (w.toFun s : EuStd → ℝ) =ᵐ[volume.restrict Ω₀]
          dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u (t₀ + s)) := by
  let μ := volume.restrict (Icc t₀ t₁)
  let ν := μ.prod (volume.restrict Ω₀)
  have hI : Icc t₀ t₁ ⊆ Icc (0 : ℝ) T :=
    fun t ht => ⟨ht₀.le.trans ht.1, ht.2.trans ht₁.le⟩
  have hμ : (timeMeasure T).restrict (Icc t₀ t₁) = μ :=
    Measure.restrict_restrict_of_subset hI
  have hμle : μ ≤ timeMeasure T := by
    rw [← hμ]
    exact Measure.restrict_le_self
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  let U := dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
    (hΩs.trans (image_mono interior_subset)) (timeMeasure T) u
  let V := fun i => dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs
    (timeMeasure T) i u
  have hmeasure : ν ≤ (timeMeasure T).prod (volume.restrict Ω) :=
    Measure.prod_mono hμle (Measure.restrict_mono hsub le_rfl)
  have hU : LocallyIntegrable U ν :=
    ((Lp.memLp U).mono_measure hmeasure).locallyIntegrable (by norm_num)
  have hV (i) : MemLp (V i) 2 ν := (Lp.memLp (V i)).mono_measure hmeasure
  have hsource := hu.exists_lp_weak_time_deriv_and_spatial_weak_deriv hXcont hacont
    α hΩ hΩc hΩs hXsmooth ht₀ ht₁ ht₀₁.le hΩ₀ hΩ₀Ω
  dsimp only at hsource
  rw [hμ] at hsource
  obtain ⟨R, hR, DR, hDR, _, _⟩ := hsource
  let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  let : SecondCountableTopology (Lp ℝ 2 (volume.restrict Ω₀)) := Lp.SecondCountableTopology
  have hshift : MeasurePreserving (fun s : ℝ => t₀ + s)
      (timeMeasure (t₁ - t₀)) μ := by
    rw [← hμ]
    exact measurePreserving_add_right_timeMeasure_restrict hI
  intro i
  let V₀ : Lp ℝ 2 ν := (hV i).toLp (V i)
  let P := Lp.curry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) V₀
  have hfirst : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
      (fun z => V i (t, z)) (fun z => U (t, z)) Ω₀ := by
    filter_upwards [(hasWeakPartialDeriv_dirichletLocalSpacetimeWeakPartialLp q α
      hΩ hΩc hΩs (timeMeasure T) i u).filter_mono (ae_mono hμle)] with t ht
    exact ht.restrict hΩ₀ hsub
  have hspace : ∀ ψ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
      (∫ p, U p * fderiv ℝ ψ p (0, EuclideanSpace.single i 1) ∂ν) =
        -∫ p, V i p * ψ p ∂ν := by
    intro ψ hψ hψc hψs
    exact Sobolev.Euclidean.integral_fderiv_prod_eq_neg_of_hasWeakPartialDeriv
      hU ((hV i).locallyIntegrable (by norm_num)) i hfirst ψ hψ hψc
      (hψs.trans (Set.prod_mono (subset_univ _) Subset.rfl))
  have hweak : ∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
      (∫ p, (Lp.uncurry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) P) p *
        fderiv ℝ φ p (1, 0) ∂ν) = -∫ p, DR i p * φ p ∂ν := by
    intro φ hφ hφc hφs
    change (∫ p, (Lp.uncurry ℝ _ (Lp.curry ℝ _ V₀)) p *
      fderiv ℝ φ p (1, 0) ∂ν) = _
    rw [Lp.uncurry_curry]
    have hcomm := Sobolev.integral_weak_deriv_fderiv_comm
      (0, EuclideanSpace.single i 1) (1, 0) hspace hR hφ hφc hφs
    have hrspace := Sobolev.Euclidean.integral_fderiv_prod_eq_neg_of_hasWeakPartialDeriv
      ((Lp.memLp R).locallyIntegrable (by norm_num))
      ((Lp.memLp (DR i)).locallyIntegrable (by norm_num)) i (hDR i) φ hφ hφc
      (hφs.trans (Set.prod_mono (subset_univ _) Subset.rfl))
    refine (integral_congr_ae ?_).trans (hcomm.trans hrspace)
    filter_upwards [(hV i).coeFn_toLp] with p hp
    exact congrArg (fun v => v * fderiv ℝ φ p (1, 0)) hp
  obtain ⟨w, hw, _⟩ := exists_timeH1_of_spacetime_weak_deriv_on ht₀₁ hΩ₀ P (DR i) hweak
  have hP : ∀ᵐ t ∂μ, (P t : EuStd → ℝ) =ᵐ[volume.restrict Ω₀]
      dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t) := by
    have hc := (dirichletLocalSpacetimeWeakPartialLp_coeFn q α hΩ hΩc hΩs
      (timeMeasure T) i u).filter_mono (ae_mono hμle)
    filter_upwards [Lp.curry_coeFn (𝕜 := ℝ) (by norm_num) V₀,
      Measure.ae_ae_of_ae_prod ((hV i).coeFn_toLp), hc] with t ht hvt hct
    exact Filter.EventuallyEq.trans ht
      (Filter.EventuallyEq.trans hvt (ae_restrict_of_ae_restrict_of_subset hsub hct))
  refine ⟨w, ?_⟩
  filter_upwards [hw, hshift.quasiMeasurePreserving.ae hP] with s hs hsP
  rw [← hs]
  exact hsP

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
