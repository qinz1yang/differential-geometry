import DifferentialGeometry.Analysis.Parabolic.Dirichlet.FourthWeakDerivative
import DifferentialGeometry.Analysis.Sobolev.Euclidean.SliceWkp

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold NNReal Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
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

theorem IsWeakEvolutionSolution.ae_memWkp_four_and_memLp_wkpNorm_interior
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
    (∀ᵐ t ∂volume.restrict (Icc t₀ t₁),
      MemWkp 4 2
        (fun z => H1ComplDirichletToLp q (u t)
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) Ω₀) ∧
      MemLp (fun t => (iteratedWeakSobolevNorm 4 2
        (fun z => H1ComplDirichletToLp q (u t)
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) Ω₀).toReal)
        2 (volume.restrict (Icc t₀ t₁)) := by
  let μ := (timeMeasure T).restrict (Icc t₀ t₁)
  have hμ : μ = volume.restrict (Icc t₀ t₁) :=
    timeMeasure_restrict_Icc_eq_volume_restrict_Icc
      (Icc_subset_Icc ht₀.le ht₁.le)
  obtain ⟨H, hH, _⟩ := hu.exists_lp_symmetric_weak_second_deriv
    hXcont hacont α hΩ hΩc hΩs hXsmooth ht₀ ht₁ hΩ₀ hΩ₀Ω
  obtain ⟨K, hK⟩ := hu.exists_local_third_weak_derivative
    hXcont hacont α hΩ hΩc hΩs hXsmooth ht₀ ht₁ ht₀₁ hΩ₀ hΩ₀Ω H hH
  obtain ⟨L, hL⟩ := hu.exists_local_fourth_weak_derivative
    hXcont hacont α hΩ hΩc hΩs hXsmooth ht₀ ht₁ ht₀₁ hΩ₀ hΩ₀Ω H hH K hK
  have huLp : MemLp (fun t => u t) 2 μ :=
    (Lp.memLp u).mono_measure Measure.restrict_le_self
  let uLp := huLp.toLp (fun t => u t)
  let U := dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
    (hΩs.trans (image_mono interior_subset)) μ uLp
  let W := fun i => dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs μ i uLp
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hmeasure : μ.prod (volume.restrict Ω₀) ≤ μ.prod (volume.restrict Ω) :=
    Measure.prod_mono le_rfl (Measure.restrict_mono hsub le_rfl)
  have hU : MemLp (U : ℝ × EuStd → ℝ) 2 (μ.prod (volume.restrict Ω₀)) :=
    (Lp.memLp U).mono_measure hmeasure
  have hW : ∀ i, MemLp (W i : ℝ × EuStd → ℝ) 2 (μ.prod (volume.restrict Ω₀)) :=
    fun i => (Lp.memLp (W i)).mono_measure hmeasure
  have heqU : ∀ᵐ t ∂μ, (fun z => U (t, z)) =ᵐ[volume.restrict Ω₀]
      fun z => H1ComplDirichletToLp q (u t)
        ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)) := by
    filter_upwards [dirichletLocalSpacetimeLp_coeFn q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) μ uLp, huLp.coeFn_toLp] with t ht hut
    rw [hut] at ht
    exact ht.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  have heqW (i) : ∀ᵐ t ∂μ, (fun z => W i (t, z)) =ᵐ[volume.restrict Ω₀]
      dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t) := by
    filter_upwards [dirichletLocalSpacetimeWeakPartialLp_coeFn q α hΩ hΩc hΩs μ i uLp,
      huLp.coeFn_toLp] with t ht hut
    rw [hut] at ht
    exact ht.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  have hsecond (i j) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
      (fun z => H i j (t, z)) (fun z => W i (t, z)) Ω₀ := by
    filter_upwards [hH i j, heqW i] with t ht he
    exact hasWeakPartialDeriv_congr_ae hΩ₀ j he.symm ht
  have hKreg (i j k) := ae_memWkp_one_and_memLp_wkpNorm_of_weak_partials
    hΩ₀ (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num) (Lp.memLp (K i j k))
    (fun l => Lp.memLp (L i j k l)) (hL i j k)
  have hHreg (i j) := ae_memWkp_succ_and_memLp_wkpNorm_of_weak_partials
    hΩ₀ (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num) (Lp.memLp (H i j))
    (fun k => (hKreg i j k).1) (fun k => (hKreg i j k).2) (hK i j)
  have hWreg (i) := ae_memWkp_succ_and_memLp_wkpNorm_of_weak_partials
    hΩ₀ (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num) (hW i)
    (fun j => (hHreg i j).1) (fun j => (hHreg i j).2) (hsecond i)
  have hfirst (i) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
      (fun z => W i (t, z)) (fun z => U (t, z)) Ω₀ :=
    (hasWeakPartialDeriv_dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs μ i uLp).mono
      (fun _ ht => DeGiorgi.HasWeakPartialDeriv.restrict hΩ₀ hsub ht)
  obtain ⟨hmem, hnorm⟩ := ae_memWkp_succ_and_memLp_wkpNorm_of_weak_partials
    hΩ₀ (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num) hU
    (fun i => (hWreg i).1) (fun i => (hWreg i).2) hfirst
  rw [← hμ]
  constructor
  · filter_upwards [hmem, heqU] with t ht he
    exact (MemWkp_congr_ae (by norm_num) hΩ₀ he).mp ht
  · apply hnorm.ae_eq
    filter_upwards [heqU] with t ht
    exact congrArg ENNReal.toReal (wkpNorm_congr_ae (by norm_num) hΩ₀ ht)

theorem IsWeakEvolutionSolution.ae_memWkp_four_interior
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
    ∀ᵐ t ∂volume.restrict (Icc t₀ t₁),
      MemWkp 4 2
        (fun z => H1ComplDirichletToLp q (u t)
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) Ω₀ :=
  (hu.ae_memWkp_four_and_memLp_wkpNorm_interior hXcont hacont α hΩ hΩc hΩs
    hXsmooth ht₀ ht₁ ht₀₁ hΩ₀ hΩ₀Ω).1

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
