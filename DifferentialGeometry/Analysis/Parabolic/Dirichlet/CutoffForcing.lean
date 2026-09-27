import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletLocalForm
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletChartSourceDual

noncomputable section

open Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

private theorem ae_eq_add_of_ae_ae_eq_sub
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [SFinite ν]
    (P : Lp ℝ 2 (μ.prod ν)) {Q E R : A × B → ℝ}
    (hQ : MemLp Q 2 (μ.prod ν)) (hE : MemLp E 2 (μ.prod ν))
    (hP : ∀ᵐ t ∂μ, ∀ᵐ x ∂ν, P (t, x) = R (t, x))
    (hR : ∀ᵐ t ∂μ, ∀ᵐ x ∂ν, Q (t, x) = R (t, x) - E (t, x)) :
    P =ᵐ[μ.prod ν] fun p => Q p + E p := by
  let Q' := hQ.toLp Q
  let E' := hE.toLp E
  have hmeas : MeasurableSet {p | P p = Q' p + E' p} :=
    (Lp.stronglyMeasurable P).measurableSet_eq_fun
      ((Lp.stronglyMeasurable Q').add (Lp.stronglyMeasurable E'))
  have heq : P =ᵐ[μ.prod ν] fun p => Q' p + E' p := by
    apply (Measure.ae_prod_iff_ae_ae hmeas).mpr
    filter_upwards [hP, hR, Measure.ae_ae_of_ae_prod hQ.coeFn_toLp,
      Measure.ae_ae_of_ae_prod hE.coeFn_toLp] with t hPt hRt hQt hEt
    filter_upwards [hPt, hRt, hQt, hEt] with x hPx hRx hQx hEx
    change P (t, x) = hQ.toLp Q (t, x) + hE.toLp E (t, x)
    rw [hQx, hEx, hRx]
    linarith
  filter_upwards [heq, hQ.coeFn_toLp, hE.coeFn_toLp] with p hp hQp hEp
  change P p = hQ.toLp Q p + hE.toLp E p at hp
  rwa [hQp, hEp] at hp

section

variable {A B X ι : Type*} [MeasurableSpace A] [MeasurableSpace B]
  {μ : Measure A} {ν : Measure B} [SFinite ν]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [Fintype ι]

private theorem integral_dual_add_eq_source_add
    (D : ι → X →L[ℝ] Lp ℝ 2 ν) {Q Mx Ex : ι → A × B → ℝ}
    (hQ : ∀ j, MemLp (Q j) 2 (μ.prod ν))
    (hE : ∀ j, MemLp (Ex j) 2 (μ.prod ν))
    (hME : ∀ j, Mx j =ᵐ[μ.prod ν] fun p => Q j p + Ex j p)
    (ℓ Lm : Lp (X →L[ℝ] ℝ) 2 μ) (S : Lp ℝ 2 μ → X → ℝ)
    (hℓ : ∀ (τ : Lp ℝ 2 μ) (v : X), (∫ t, τ t * ℓ t v ∂μ) = S τ v -
      ∑ j, ∫ p, τ p.1 * Q j p * D j v p.2 ∂μ.prod ν)
    (hLm : ∀ (τ : Lp ℝ 2 μ) (v : X), (∫ t, τ t * Lm t v ∂μ) =
      ∑ j, ∫ p, τ p.1 * Mx j p * D j v p.2 ∂μ.prod ν)
    (τ : Lp ℝ 2 μ) (v : X) :
    (∫ t, τ t * (ℓ + Lm) t v ∂μ) = S τ v +
      ∑ j, ∫ p, τ p.1 * Ex j p * D j v p.2 ∂μ.prod ν := by
  have h1 : Integrable (fun t => τ t * ℓ t v) μ :=
    (Lp.memLp τ).integrable_mul ((ContinuousLinearMap.apply ℝ ℝ v).comp_memLp ℓ)
  have h2 : Integrable (fun t => τ t * Lm t v) μ :=
    (Lp.memLp τ).integrable_mul ((ContinuousLinearMap.apply ℝ ℝ v).comp_memLp Lm)
  have hparts (j) : (∫ p, τ p.1 * Mx j p * D j v p.2 ∂μ.prod ν) =
      (∫ p, τ p.1 * Q j p * D j v p.2 ∂μ.prod ν) +
      ∫ p, τ p.1 * Ex j p * D j v p.2 ∂μ.prod ν := by
    rw [← integral_add (MemLp.integrable_mul_tensor (hQ j) τ (D j v))
      (MemLp.integrable_mul_tensor (hE j) τ (D j v))]
    apply integral_congr_ae
    filter_upwards [hME j] with p hp
    rw [hp]
    ring
  have hadd : (∫ t, τ t * (ℓ + Lm) t v ∂μ) =
      (∫ t, τ t * ℓ t v ∂μ) + ∫ t, τ t * Lm t v ∂μ := by
    rw [← integral_add h1 h2]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add ℓ Lm] with t ht
    rw [ht]
    change τ t * (ℓ t v + Lm t v) = _
    ring
  rw [hadd, hℓ, hLm]
  simp_rw [hparts, Finset.sum_add_distrib]
  ring

end

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

private local instance h1ComplDirichletBilinearSeminormed
    {q : SmoothRiemannianMetric I_hs M} :
    SeminormedAddCommGroup (H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q →L[ℝ] ℝ) :=
  @ContinuousLinearMap.toSeminormedAddCommGroup ℝ ℝ
    (H1ComplDirichlet q) (H1ComplDirichlet q →L[ℝ] ℝ)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (RingHom.id ℝ) inferInstance

omit [T2Space M] [CompactSpace M] in
private theorem memLp_cutoff_gradient_flux_error
    (q : SmoothRiemannianMetric I_hs M)
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric)
    {J : Set ℝ} (hJc : IsCompact J) (hJ : J ⊆ D.regular)
    (α : M) {Ω : Set EuStd} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {μ : Measure ℝ} (hμ : μ ≤ volume.restrict J)
    {V : ℝ × EuStd → ℝ} (hV : MemLp V 2 (μ.prod (volume.restrict Ω)))
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) :
    ∀ j, MemLp (fun p : ℝ × EuStd => ∑ i,
      (MetricExtension.densityOnEuclid q α p.2 * MetricExtension.invGramOnEuclid (G.metric p.1) α i j p.2) *
        fderiv ℝ η p.2 (EuclideanSpace.single i 1) * V p) 2 (μ.prod (volume.restrict Ω)) := by
  have htarget : closure Ω ⊆ MetricExtension.chartTargetEuclid (I := I_hs) α :=
    hΩs.trans (image_mono interior_subset)
  have hcjoint (i j) : ContinuousOn (fun p : ℝ × EuStd =>
      MetricExtension.densityOnEuclid q α p.2 * MetricExtension.invGramOnEuclid (G.metric p.1) α i j p.2)
        (J ×ˢ closure Ω) :=
    (((MetricExtension.densityOnEuclid_contDiffOn q α).comp contDiff_snd.contDiffOn
      (fun p hp => htarget hp.2)).mul
        (MetricExtension.invGramOnEuclid_family_contDiffOn hG hJ α hΩs i j)).continuousOn
  have hcoeff (i j) : MemLp (fun p : ℝ × EuStd =>
      (MetricExtension.densityOnEuclid q α p.2 * MetricExtension.invGramOnEuclid (G.metric p.1) α i j p.2) *
        fderiv ℝ η p.2 (EuclideanSpace.single i 1)) ∞ (μ.prod (volume.restrict Ω)) := by
    have hdiff : Continuous (fun p : ℝ × EuStd => fderiv ℝ η p.2 (EuclideanSpace.single i 1)) :=
      ((hη.continuous_fderiv (by simp)).clm_apply continuous_const).comp continuous_snd
    have h := ((hcjoint i j).mul hdiff.continuousOn).memLp_top_of_subset_isCompact
      (hJc.prod hΩc) (hJc.measurableSet.prod hΩ.measurableSet) (prod_mono Subset.rfl subset_closure)
      (μ := (volume : Measure ℝ).prod volume)
    rw [← Measure.prod_restrict] at h
    exact h.mono_measure (Measure.prod_mono hμ le_rfl)
  intro j
  exact memLp_finsetSum Finset.univ fun i _ => hV.mul (r := 2) (hcoeff i j)

private theorem exists_local_dirichlet_main_flux_dual
    (q : SmoothRiemannianMetric I_hs M)
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric)
    {J : Set ℝ} (hJc : IsCompact J) (hJ : J ⊆ D.regular)
    (α : M) {Ω : Set EuStd} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (F : ℝ → H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q →L[ℝ] ℝ)
    (hF : ∀ t u v, F t u v = ∑ i, ∑ j, ∫ x,
      dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i u x *
        (MetricExtension.densityOnEuclid q α x * MetricExtension.invGramOnEuclid (G.metric t) α i j x) *
          dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j v x ∂volume.restrict Ω)
    {μ : Measure ℝ} [SFinite μ] (hμ : μ ≤ volume.restrict J)
    (v : Lp (H1ComplDirichlet q) 2 μ) :
    ∃ P : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 (μ.prod (volume.restrict Ω)),
      ∃ ℓ : Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ,
      (∀ j, ∀ᵐ t ∂μ, (fun x => P j (t, x)) =ᵐ[volume.restrict Ω]
        fun x => ∑ i, (MetricExtension.densityOnEuclid q α x * MetricExtension.invGramOnEuclid (G.metric t) α i j x) *
          dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t) x) ∧
      (∀ (τ : Lp ℝ 2 μ) (z : H1ComplDirichlet q),
        (∫ t, τ t * ℓ t z ∂μ) =
          ∑ j, ∫ p, τ p.1 * P j p * dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j z p.2
            ∂μ.prod (volume.restrict Ω)) ∧
      ∀ z : Lp (H1ComplDirichlet q) 2 μ,
        Integrable (fun t => F t (v t) (z t)) μ ∧
        (∫ t, ℓ t (z t) ∂μ) = ∫ t, F t (v t) (z t) ∂μ := by
  let c := fun i j (p : ℝ × EuStd) => MetricExtension.densityOnEuclid q α p.2 *
    MetricExtension.invGramOnEuclid (G.metric p.1) α i j p.2
  have hc (i j) : MemLp (c i j) ∞ (μ.prod (volume.restrict Ω)) := by
    have hcont : ContinuousOn (c i j) (J ×ˢ closure Ω) :=
      (((MetricExtension.densityOnEuclid_contDiffOn q α).comp contDiff_snd.contDiffOn
        (fun p hp => (hΩs.trans (image_mono interior_subset)) hp.2)).mul
        (MetricExtension.invGramOnEuclid_family_contDiffOn hG hJ α hΩs i j)).continuousOn
    have h := hcont.memLp_top_of_subset_isCompact (hJc.prod hΩc)
      (hJc.measurableSet.prod hΩ.measurableSet) (prod_mono Subset.rfl subset_closure)
      (μ := (volume : Measure ℝ).prod volume)
    rw [← Measure.prod_restrict] at h
    exact h.mono_measure (Measure.prod_mono hμ le_rfl)
  obtain ⟨P, hP, hp⟩ := MeasureTheory.exists_lp_flux_of_bilinear_integral
    (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs) c hc F hF v
  obtain ⟨ℓ, hℓ, _, hℓv⟩ := exists_lp_chart_divergence_dual_integral_integral α hΩ hΩc hΩs P
  exact ⟨P, ℓ, hP, hℓ, fun z => ⟨(hp z).1, (hℓv z).trans (hp z).2.symm⟩⟩

theorem exists_cutoff_forcing_dual
    (q : SmoothRiemannianMetric I_hs M)
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric)
    {J : Set ℝ} (hJc : IsCompact J) (hJ : J ⊆ D.regular)
    (α : M) {Ω : Set EuStd} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {μ : Measure ℝ} (hμ : μ ≤ volume.restrict J)
    (V : ℝ × EuStd → ℝ) (hV : MemLp V 2 (μ.prod (volume.restrict Ω)))
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (v : Lp (H1ComplDirichlet q) 2 μ)
    (ℓ : Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ)
    (F : ℝ → H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q →L[ℝ] ℝ)
    (hF : ∀ t u z, F t u z = ∑ i, ∑ j, ∫ x in Ω,
      dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i u x *
        (MetricExtension.densityOnEuclid q α x * MetricExtension.invGramOnEuclid (G.metric t) α i j x) *
          dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j z x)
    (Q : Fin (Module.finrank ℝ EuN) → ℝ × EuStd → ℝ) (B : ℝ × EuStd → ℝ)
    (hQ : ∀ j, MemLp (Q j) 2 (μ.prod (volume.restrict Ω)))
    (hℓ : ∀ (τ : Lp ℝ 2 μ) (z : H1ComplDirichlet q),
      (∫ t, τ t * ℓ t z ∂μ) =
        (∫ p, τ p.1 * B p * H1ComplDirichletToLp q z
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2)) ∂μ.prod (volume.restrict Ω)) -
          ∑ j, ∫ p, τ p.1 * Q j p * dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j z p.2
            ∂μ.prod (volume.restrict Ω)) :
    let c := fun i j (p : ℝ × EuStd) => MetricExtension.densityOnEuclid q α p.2 *
      MetricExtension.invGramOnEuclid (G.metric p.1) α i j p.2
    let E := fun j (p : ℝ × EuStd) => ∑ i, c i j p * fderiv ℝ η p.2 (EuclideanSpace.single i 1) * V p
    (∀ j, ∀ᵐ t ∂μ, ∀ᵐ x ∂volume.restrict Ω,
      Q j (t, x) = (∑ i, c i j (t, x) * dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t) x) - E j (t, x)) →
    ∃ Lm : Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ,
      (∀ (τ : Lp ℝ 2 μ) (z : H1ComplDirichlet q),
        (∫ t, τ t * (ℓ + Lm) t z ∂μ) =
          (∫ p, τ p.1 * B p * H1ComplDirichletToLp q z
            ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2)) ∂μ.prod (volume.restrict Ω)) +
            ∑ j, ∫ p, τ p.1 * E j p * dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j z p.2
              ∂μ.prod (volume.restrict Ω)) ∧
      ∀ z : Lp (H1ComplDirichlet q) 2 μ,
        (∫ t, Lm t (z t) ∂μ) = ∫ t, F t (v t) (z t) ∂μ := by
  let : IsLocallyFiniteMeasure μ := Measure.isLocallyFiniteMeasure_of_le hμ
  intro c E hflux
  have hE : ∀ j, MemLp (E j) 2 (μ.prod (volume.restrict Ω)) :=
    memLp_cutoff_gradient_flux_error q hG hJc hJ α hΩ hΩc hΩs hμ hV hη
  obtain ⟨P, Lm, hP, hLm, hpair⟩ := exists_local_dirichlet_main_flux_dual q hG hJc hJ α hΩ hΩc hΩs F hF hμ v
  have hPE (j) : P j =ᵐ[μ.prod (volume.restrict Ω)] fun p => Q j p + E j p :=
    ae_eq_add_of_ae_ae_eq_sub (μ := μ) (ν := volume.restrict Ω) (P j)
      (Q := Q j) (E := E j)
      (R := fun p => ∑ i, c i j p * dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v p.1) p.2)
      (hQ j) (hE j) (hP j) (hflux j)
  exact ⟨Lm, integral_dual_add_eq_source_add
    (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs) hQ hE hPE ℓ Lm _ hℓ hLm,
    fun z => (hpair z).2⟩

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
