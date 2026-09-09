import DifferentialGeometry.Analysis.Parabolic.Dirichlet.ThirdWeakDerivative
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.WeakTimeDerivativeBound
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakPartialSource
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.LocalCoefficientDerivativeBounds

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [OpensMeasurableSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem memLp_top_and_spatial_fderiv_of_contDiffOn
    {S J : Set ℝ} (hS : IsOpen S) (hJ : IsCompact J) (hJS : J ⊆ S)
    {U Ω : Set E} (hU : IsOpen U) (hΩ : MeasurableSet Ω)
    (hΩc : IsCompact (closure Ω)) (hΩU : closure Ω ⊆ U)
    {A : ℝ → E → F}
    (hA : ContDiffOn ℝ ∞ (fun p : ℝ × E => A p.1 p.2) (S ×ˢ U))
    (μ : Measure (ℝ × E)) :
    MemLp (fun p : ℝ × E => A p.1 p.2) ∞ (μ.restrict (J ×ˢ Ω)) ∧
      (∀ v : E, MemLp (fun p : ℝ × E => fderiv ℝ (A p.1) p.2 v)
        ∞ (μ.restrict (J ×ˢ Ω))) := by
  constructor
  · exact (hA.continuousOn.mono (prod_mono hJS hΩU)).memLp_top_of_subset_isCompact
      (hJ.prod hΩc) (hJ.measurableSet.prod hΩ) (prod_mono Subset.rfl subset_closure)
  · intro v
    have hD := (spatialFDeriv_contDiffOn hS.uniqueDiffOn hU hA).clm_apply
      (contDiffOn_const (c := v))
    exact (hD.continuousOn.mono (prod_mono hJS hΩU)).memLp_top_of_subset_isCompact
      (hJ.prod hΩc) (hJ.measurableSet.prod hΩ) (prod_mono Subset.rfl subset_closure)

omit [MeasurableSpace E] [OpensMeasurableSpace E] in
private theorem contDiffOn_spatial_of_contDiffOn_prod
    {S : Set ℝ} {U : Set E} {A : ℝ → E → F}
    (hA : ContDiffOn ℝ ∞ (fun p : ℝ × E => A p.1 p.2) (S ×ˢ U))
    {t : ℝ} (ht : t ∈ S) : ContDiffOn ℝ ∞ (A t) U := by
  exact hA.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hz => ⟨ht, hz⟩)

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
private theorem memLp_top_time_coefficient
    {J : Set ℝ} (hJ : IsCompact J) {a : ℝ → F} (ha : ContinuousOn a J)
    {Ω : Set E} (hΩ : MeasurableSet Ω) (hΩc : IsCompact (closure Ω))
    (μ : Measure (ℝ × E)) :
    MemLp (fun p : ℝ × E => a p.1) ∞ (μ.restrict (J ×ˢ Ω)) := by
  have hc : ContinuousOn (fun p : ℝ × E => a p.1) (J ×ˢ closure Ω) :=
    ha.comp continuousOn_fst (fun _ hp => hp.1)
  exact hc.memLp_top_of_subset_isCompact (hJ.prod hΩc)
    (hJ.measurableSet.prod hΩ) (prod_mono Subset.rfl subset_closure)

end DifferentialGeometry.Analysis

namespace DifferentialGeometry.Analysis.Laplacian.MetricExtension

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private theorem inv_densityOnEuclid_family_contDiffOn
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set ℝ} (hJ : J ⊆ D.regular) (α : M) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × EuclN => (densityOnEuclid (I := I) (G.metric p.1) α p.2)⁻¹)
      (J ×ˢ chartTargetEuclid (I := I) α) := by
  exact (densityOnEuclid_family_contDiffOn hG hJ α).inv
    (fun p hp => (densityOnEuclid_pos (G.metric p.1) α hp.2).ne')

private theorem inv_density_mul_weightedInvGramOnEuclid_family_contDiffOn
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set ℝ} (hJ : J ⊆ D.regular) (α : M)
    {Ω : Set EuclN}
    (hΩs : Ω ⊆ toEuclidean (E := E) '' interior (extChartAt I α).target)
    (i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × EuclN =>
      (densityOnEuclid (I := I) (G.metric p.1) α p.2)⁻¹ *
        weightedInvGramOnEuclid (I := I) (G.metric p.1) α i j p.2) (J ×ˢ Ω) := by
  exact ((inv_densityOnEuclid_family_contDiffOn hG hJ α).mono
    (prod_mono Subset.rfl (hΩs.trans (image_mono interior_subset)))).mul
      (weightedInvGramOnEuclid_family_contDiffOn hG hJ α hΩs i j)

private theorem inv_density_mul_weightedInvGramOnEuclid_fderiv_family_contDiffOn
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set ℝ} (hJ : J ⊆ D.regular) (α : M)
    {Ω : Set EuclN} (hΩ : IsOpen Ω)
    (hΩs : Ω ⊆ toEuclidean (E := E) '' interior (extChartAt I α).target)
    (i j : Fin (Module.finrank ℝ E)) (v : EuclN) :
    ContDiffOn ℝ ∞ (fun p : ℝ × EuclN =>
      (densityOnEuclid (I := I) (G.metric p.1) α p.2)⁻¹ *
        fderiv ℝ (weightedInvGramOnEuclid (I := I) (G.metric p.1) α i j) p.2 v)
      (J ×ˢ Ω) := by
  exact ((inv_densityOnEuclid_family_contDiffOn hG hJ α).mono
    (prod_mono Subset.rfl (hΩs.trans (image_mono interior_subset)))).mul
      ((weightedInvGramOnEuclid_family_fderiv_contDiffOn hG hJ α hΩ hΩs i j).clm_apply
        (contDiffOn_const (c := v)))

private theorem inv_density_mul_weightedInvGramOnEuclid_fderiv_add_chartCoeff_family_contDiffOn
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set ℝ} (hJ : J ⊆ D.regular) (α : M)
    (X : ℝ → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' E p.2 (X p.1 p.2))
      (D.regular ×ˢ (trivializationAt E (TangentSpace I) α).baseSet))
    {Ω : Set EuclN} (hΩ : IsOpen Ω)
    (hΩs : Ω ⊆ toEuclidean (E := E) '' interior (extChartAt I α).target)
    (i : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × EuclN =>
      (∑ j, (densityOnEuclid (I := I) (G.metric p.1) α p.2)⁻¹ *
        fderiv ℝ (weightedInvGramOnEuclid (I := I) (G.metric p.1) α i j) p.2
          (EuclideanSpace.single j 1)) +
        chartCoeffOnE (I := I) α (X p.1) i ((toEuclidean (E := E)).symm p.2))
      (J ×ˢ Ω) := by
  apply ContDiffOn.add
  · exact ContDiffOn.sum fun j _ =>
      inv_density_mul_weightedInvGramOnEuclid_fderiv_family_contDiffOn
        hG hJ α hΩ hΩs i j (EuclideanSpace.single j 1)
  · exact (chartCoeffOnE_comp_toEuclidean_symm_family_contDiffOn X α hX i).mono
      (prod_mono hJ (hΩs.trans (image_mono interior_subset)))

private theorem densityOnEuclid_inv_mul_trace_sub_fderiv_time
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {t : ℝ} (ht : t ∈ D.regular) (α : M) {z : EuclN}
    (hz : z ∈ toEuclidean (E := E) '' interior (extChartAt I α).target)
    (a : ℝ) :
    (densityOnEuclid (I := I) (G.metric t) α z)⁻¹ *
      (densityOnEuclid (I := I) (G.metric t) α z *
        ((1 / 2 : ℝ) * traceTimeDerivMetric (I := I) G.metric t
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)) - a) -
        fderiv ℝ (fun p : ℝ × EuclN => densityOnEuclid (I := I) (G.metric p.1) α p.2)
          (t, z) (1, 0)) = -a := by
  rw [densityOnEuclid_family_fderiv_time_eq hG ht α hz]
  have hρne := ne_of_gt (densityOnEuclid_pos (G.metric t) α ((image_mono interior_subset) hz))
  field_simp
  ring

end DifferentialGeometry.Analysis.Laplacian.MetricExtension

open Filter
open scoped NNReal

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

private theorem normalize_source {ι : Type*} [Fintype ι]
    (r s u : ℝ) (a d h : ι → ι → ℝ) (b v : ι → ℝ) (hr : r ≠ 0) :
    r⁻¹ * ((∑ i, ∑ j, (a i j * h i j + d i j * v i)) +
      (∑ i, r * b i * v i) + s * u) =
    (∑ i, ∑ j, (r⁻¹ * a i j) * h i j) +
      (∑ i, ((∑ j, r⁻¹ * d i j) + b i) * v i) + (r⁻¹ * s) * u := by
  simp only [Finset.sum_add_distrib, mul_add, add_mul, Finset.mul_sum,
    Finset.sum_mul, mul_assoc, inv_mul_cancel_left₀ hr]
  simp only [add_assoc]

theorem IsWeakEvolutionSolution.exists_spatial_weak_derivative_time_derivative
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
    let μ := (timeMeasure T).restrict (Icc t₀ t₁)
    let ν := μ.prod (volume.restrict Ω₀)
    let U := dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) (timeMeasure T) u
    ∀ R : Lp ℝ 2 ν,
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
        (∫ p, U p * fderiv ℝ φ p (1, 0) ∂ν) = -∫ p, R p * φ p ∂ν) →
      ∃ DR : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
        (∀ k, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
          (fun x => DR k (t, x)) (fun x => R (t, x)) Ω₀) ∧
        (∀ᵐ t ∂μ, MemWkp 1 2 (fun x => R (t, x)) Ω₀) ∧
        MemLp (fun t => (iteratedWeakSobolevNorm 1 2 (fun x => R (t, x)) Ω₀).toReal) 2 μ := by
  intro μ ν U R hR
  classical
  obtain ⟨H, hH, _⟩ := hu.exists_lp_symmetric_weak_second_deriv hXcont hacont
    α hΩ hΩc hΩs hXsmooth ht₀ ht₁ hΩ₀ hΩ₀Ω
  obtain ⟨K, hK⟩ := hu.exists_local_third_weak_derivative hXcont hacont
    α hΩ hΩc hΩs hXsmooth ht₀ ht₁ ht₀₁ hΩ₀ hΩ₀Ω H hH
  have hformula := hu.weak_time_derivative_eq_source hXcont hacont
    α hΩ hΩc hΩs hXsmooth ht₀ ht₁ hΩ₀ hΩ₀Ω H hH R hR
  let V := fun i => dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) i u
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hmeasure : ν ≤ (timeMeasure T).prod (volume.restrict Ω) :=
    Measure.prod_mono Measure.restrict_le_self (Measure.restrict_mono hsub le_rfl)
  have hU : MemLp U 2 ν := (Lp.memLp U).mono_measure hmeasure
  have hV (i) : MemLp (V i) 2 ν := (Lp.memLp (V i)).mono_measure hmeasure
  let U₀ := hU.toLp U
  let V₀ := fun i => (hV i).toLp (V i)
  have hU₀ : U₀ =ᵐ[ν] U := hU.coeFn_toLp
  have hV₀ (i) : V₀ i =ᵐ[ν] V i := (hV i).coeFn_toLp
  have hVweak (i k) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
      (fun z => H i k (t, z)) (fun z => V₀ i (t, z)) Ω₀ := by
    have hVi := ae_restrict_of_ae (s := Icc t₀ t₁)
      (dirichletLocalSpacetimeWeakPartialLp_coeFn q α hΩ hΩc hΩs (timeMeasure T) i u)
    filter_upwards [hH i k, Measure.ae_ae_of_ae_prod (hV₀ i), hVi] with t ht he hv
    change (fun z => V₀ i (t,z)) =ᵐ[volume.restrict Ω₀] (fun z => V i (t,z)) at he
    exact hasWeakPartialDeriv_congr_ae hΩ₀ k
      (he.trans (hv.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl)))).symm ht
  have hUweak (k) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
      (fun z => V₀ k (t, z)) (fun z => U₀ (t, z)) Ω₀ := by
    have hbase := ae_restrict_of_ae (s := Icc t₀ t₁)
      (hasWeakPartialDeriv_dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) k u)
    filter_upwards [hbase, Measure.ae_ae_of_ae_prod hU₀,
      Measure.ae_ae_of_ae_prod (hV₀ k)] with t ht hu hv
    change (fun z => U₀ (t,z)) =ᵐ[volume.restrict Ω₀] (fun z => U (t,z)) at hu
    change (fun z => V₀ k (t,z)) =ᵐ[volume.restrict Ω₀] (fun z => V k (t,z)) at hv
    have ht' := DeGiorgi.HasWeakPartialDeriv.restrict hΩ₀ hsub ht
    have he := hasWeakPartialDeriv_congr_ae hΩ₀ k hu.symm ht'
    intro φ hφ hφc hφs
    rw [he φ hφ hφc hφs]
    congr 1
    apply integral_congr_ae
    filter_upwards [hv] with z hz
    rw [hz]
  let W := toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target
  have hW : IsOpen W := (toEuclidean (E := EuN)).isOpenMap _ isOpen_interior
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  have hΩ₀W : closure Ω₀ ⊆ W := hΩ₀Ω.trans (subset_closure.trans hΩs)
  let ρ := fun (p : ℝ × EuStd) => Laplacian.MetricExtension.densityOnEuclid (G.metric p.1) α p.2
  let A := fun i j (p : ℝ × EuStd) => Laplacian.MetricExtension.weightedInvGramOnEuclid (G.metric p.1) α i j p.2
  let P := fun i j p => (ρ p)⁻¹ * A i j p
  let Q := fun i (p : ℝ × EuStd) =>
    (∑ j, (ρ p)⁻¹ * fderiv ℝ (fun z => A i j (p.1,z)) p.2 (EuclideanSpace.single j 1)) +
      Integral.DivergenceTheorem.chartCoeffOnE (I := I_hs) α (X p.1) i ((toEuclidean (E := EuN)).symm p.2)
  have hP (i j) : ContDiffOn ℝ ∞ (P i j) (D.regular ×ˢ W) :=
    Laplacian.MetricExtension.inv_density_mul_weightedInvGramOnEuclid_family_contDiffOn
      hG Subset.rfl α Subset.rfl i j
  have hQ (i) : ContDiffOn ℝ ∞ (Q i) (D.regular ×ˢ W) :=
    Laplacian.MetricExtension.inv_density_mul_weightedInvGramOnEuclid_fderiv_add_chartCoeff_family_contDiffOn
      hG Subset.rfl α X hXsmooth hW Subset.rfl i
  have hbound (b : ℝ × EuStd → ℝ) (hb : ContDiffOn ℝ ∞ b (D.regular ×ˢ W)) :
      MemLp b ∞ ν ∧ ∀ k, MemLp (fun p =>
        fderiv ℝ (fun z => b (p.1,z)) p.2 (EuclideanSpace.single k 1)) ∞ ν := by
    have hb' := DifferentialGeometry.Analysis.memLp_top_and_spatial_fderiv_of_contDiffOn
      D.regular_isOpen isCompact_Icc hreg hW hΩ₀.measurableSet hΩ₀c hΩ₀W
      (A := fun t z => b (t,z)) hb (volume.prod volume)
    rw [← Measure.prod_restrict] at hb'
    refine ⟨hb'.1.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl), ?_⟩
    intro k
    exact (hb'.2 (EuclideanSpace.single k 1)).mono_measure
      (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hsmooth (b : ℝ × EuStd → ℝ) (hb : ContDiffOn ℝ ∞ b (D.regular ×ˢ W)) :
      ∀ᵐ t ∂μ, ContDiffOn ℝ ∞ (fun z => b (t,z)) Ω₀ := by
    filter_upwards [ae_restrict_of_ae (s := Icc t₀ t₁) (ae_restrict_mem measurableSet_Icc)] with t ht
    exact (DifferentialGeometry.Analysis.contDiffOn_spatial_of_contDiffOn_prod (A := fun t z => b (t,z)) hb (hreg ht)).mono
      (subset_closure.trans hΩ₀W)
  have ha : MemLp (fun p : ℝ × EuStd => -a p.1) ∞ ν := by
    have hb := DifferentialGeometry.Analysis.memLp_top_time_coefficient
      isCompact_Icc hacont.neg hΩ₀.measurableSet hΩ₀c (volume.prod volume)
    rw [← Measure.prod_restrict] at hb
    exact hb.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  let ι := (Fin (Module.finrank ℝ EuN) × Fin (Module.finrank ℝ EuN)) ⊕
    (Fin (Module.finrank ℝ EuN) ⊕ Unit)
  let Y : ι → Lp ℝ 2 ν := Sum.elim (fun ij => H ij.1 ij.2) (Sum.elim V₀ (fun _ => U₀))
  let DY : ι → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν :=
    Sum.elim (fun ij k => K ij.1 ij.2 k) (Sum.elim (fun i k => H i k) (fun _ k => V₀ k))
  let B : ι → ℝ × EuStd → ℝ :=
    Sum.elim (fun ij => P ij.1 ij.2) (Sum.elim Q (fun _ p => -a p.1))
  have hB (i) : MemLp (B i) ∞ ν := by
    rcases i with ⟨i,j⟩ | (i | i)
    · exact (hbound _ (hP i j)).1
    · exact (hbound _ (hQ i)).1
    · exact ha
  have hDB (i k) : MemLp (fun p => fderiv ℝ (fun z => B i (p.1,z)) p.2
      (EuclideanSpace.single k 1)) ∞ ν := by
    rcases i with ⟨i,j⟩ | (i | i)
    · exact (hbound _ (hP i j)).2 k
    · exact (hbound _ (hQ i)).2 k
    · change MemLp (fun p : ℝ × EuStd =>
        fderiv ℝ (fun _ : EuStd => -a p.1) p.2 (EuclideanSpace.single k 1)) ∞ ν
      simpa only [fderiv_const_apply, zero_apply] using (memLp_top_const (μ := ν) (0 : ℝ))
  have hBs (i) : ∀ᵐ t ∂μ, ContDiffOn ℝ ∞ (fun z => B i (t,z)) Ω₀ := by
    rcases i with ⟨i,j⟩ | (i | i)
    · exact hsmooth _ (hP i j)
    · exact hsmooth _ (hQ i)
    · apply Filter.Eventually.of_forall
      intro t
      change ContDiffOn ℝ ∞ (fun _ : EuStd => -a t) Ω₀
      exact contDiffOn_const
  have hY (i k) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
      (fun z => DY i k (t,z)) (fun z => Y i (t,z)) Ω₀ := by
    rcases i with ⟨i,j⟩ | (i | i)
    · exact hK i j k
    · exact hVweak i k
    · exact hUweak k
  have hsupport : ∀ᵐ p ∂ν, p.1 ∈ Icc (0 : ℝ) T ∧ p.2 ∈ Ω₀ := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Icc.prod hΩ₀.measurableSet)).mpr
    filter_upwards [ae_restrict_of_ae (s := Icc t₀ t₁) (ae_restrict_mem measurableSet_Icc)] with t ht
    exact (ae_restrict_mem hΩ₀.measurableSet).mono (fun _ hz => ⟨ht,hz⟩)
  have hRsum : R =ᵐ[ν] fun p => ∑ i, B i p * Y i p := by
    filter_upwards [hformula, hU₀, ae_all_iff.mpr hV₀, hsupport] with p hp hu hpv hpm
    have hρne : ρ p ≠ 0 :=
      (Laplacian.MetricExtension.densityOnEuclid_pos (G.metric p.1) α
        ((image_mono interior_subset) (hΩ₀W (subset_closure hpm.2)))).ne'
    have hcancel := Laplacian.MetricExtension.densityOnEuclid_inv_mul_trace_sub_fderiv_time
      hG (hreg hpm.1) α (hΩ₀W (subset_closure hpm.2)) (a p.1)
    change R p = ∑ i : (Fin (Module.finrank ℝ EuN) × Fin (Module.finrank ℝ EuN)) ⊕
      (Fin (Module.finrank ℝ EuN) ⊕ Unit), B i p * Y i p
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    change R p = (∑ ij : Fin (Module.finrank ℝ EuN) × Fin (Module.finrank ℝ EuN),
        P ij.1 ij.2 p * H ij.1 ij.2 p) +
      ((∑ i, Q i p * V₀ i p) + ∑ _ : Unit, -a p.1 * U₀ p)
    have hunit : (∑ _ : Unit, -a p.1 * U₀ p) = -a p.1 * U₀ p := by simp
    rw [Fintype.sum_prod_type, hunit, hu]
    simp_rw [hpv]
    rw [hp]
    change (ρ p)⁻¹ * ((∑ i, ∑ j, (A i j p * H i j p +
      fderiv ℝ (fun z => A i j (p.1,z)) p.2 (EuclideanSpace.single j 1) * V i p)) +
      (∑ i, ρ p * Integral.DivergenceTheorem.chartCoeffOnE (I := I_hs) α (X p.1) i
        ((toEuclidean (E := EuN)).symm p.2) * V i p) +
      (ρ p * ((1/2 : ℝ) * traceTimeDerivMetric (I := I_hs) G.metric p.1
        ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2)) - a p.1) -
        fderiv ℝ ρ p (1,0)) * U p) = _
    rw [normalize_source _ _ _ _ _ _ _ _ hρne]
    rw [hcancel]
    simp only [P, Q, add_assoc]
  obtain ⟨DR, hDR, _, _, hW1, hnorm⟩ :=
    exists_lp_spatial_weak_partials_of_ae_eq_finite_sum hΩ₀ R Y DY B hB hDB hBs hY hRsum
  exact ⟨DR, hDR, hW1, hnorm⟩

theorem IsWeakEvolutionSolution.exists_lp_weak_time_deriv_and_spatial_weak_deriv
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
    let μ := (timeMeasure T).restrict (Icc t₀ t₁)
    let ν := μ.prod (volume.restrict Ω₀)
    let U := dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) (timeMeasure T) u
    ∃ R : Lp ℝ 2 ν,
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
        (∫ p, U p * fderiv ℝ φ p (1, 0) ∂ν) = -∫ p, R p * φ p ∂ν) ∧
      ∃ DR : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
        (∀ k, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
          (fun x => DR k (t, x)) (fun x => R (t, x)) Ω₀) ∧
        (∀ᵐ t ∂μ, MemWkp 1 2 (fun x => R (t, x)) Ω₀) ∧
        MemLp (fun t => (iteratedWeakSobolevNorm 1 2 (fun x => R (t, x)) Ω₀).toReal) 2 μ := by
  intro μ ν U
  obtain ⟨R, hR⟩ := hu.exists_lp_weak_time_deriv hXcont hacont
    α hΩ hΩc hΩs hXsmooth ht₀ ht₁ hΩ₀ hΩ₀Ω
  exact ⟨R, hR, hu.exists_spatial_weak_derivative_time_derivative hXcont hacont
    α hΩ hΩc hΩs hXsmooth ht₀ ht₁ ht₀₁ hΩ₀ hΩ₀Ω R hR⟩

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
