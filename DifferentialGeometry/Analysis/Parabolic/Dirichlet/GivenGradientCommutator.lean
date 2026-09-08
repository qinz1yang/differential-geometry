import DifferentialGeometry.Analysis.Parabolic.Dirichlet.WeakEquationProduct
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.InteriorRegularity
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.TimeRegularity
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.LocalCoefficientDerivativeBounds

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
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

theorem IsWeakEvolutionSolution.given_lp_weak_gradient_commutator
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
    let ν := μ.prod (volume.restrict Ω₀)
    let x := fun z : EuStd => (extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)
    let ρ := fun (p : ℝ × EuStd) => MetricExtension.densityOnEuclid (I := I_hs) (G.metric p.1) α p.2
    let A := fun i j (p : ℝ × EuStd) =>
      MetricExtension.weightedInvGramOnEuclid (I := I_hs) (G.metric p.1) α i j p.2
    let B := fun i (p : ℝ × EuStd) =>
      DifferentialGeometry.Integral.DivergenceTheorem.chartCoeffOnE (I := I_hs) α (X p.1) i
        ((toEuclidean (E := EuN)).symm p.2)
    let U := dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) (timeMeasure T) u
    let V := fun i => dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) i u
    let L := fun p => (∑ i, ρ p * B i p * V i p) +
      ρ p * ((1 / 2 : ℝ) * traceTimeDerivMetric (I := I_hs) G.metric p.1 (x p.2) - a p.1) * U p
    ∀ (R : Lp ℝ 2 ν)
      (H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν),
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
        (∫ p, U p * fderiv ℝ φ p (1, 0) ∂ν) = -∫ p, R p * φ p ∂ν) →
      (∀ i k, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k (fun z => H i k (t,z))
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) Ω₀) →
      (∀ i k, H i k = H k i) →
      ∀ k (φ : ℝ × EuStd → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
        (∫ p, ρ p * V k p * fderiv ℝ φ p (1, 0) ∂ν) =
          (∑ i, ∑ j, ∫ p, (A i j p * H k i p +
            fderiv ℝ (A i j) p (0, EuclideanSpace.single k 1) * V i p) *
              fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) +
          (∫ p, L p * fderiv ℝ φ p (0, EuclideanSpace.single k 1) ∂ν) +
          ∫ p, (fderiv ℝ ρ p (0, EuclideanSpace.single k 1) * R p +
            fderiv ℝ (fun y => fderiv ℝ ρ y (0, EuclideanSpace.single k 1)) p (1, 0) * U p) * φ p ∂ν := by
  intro μ ν x ρ A B U V L R H hR hH hHsym
  let _ := hXsmooth
  intro k φ hφ hφc hφs
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hmeasure : ν ≤ (timeMeasure T).prod (volume.restrict Ω) :=
    Measure.prod_mono Measure.restrict_le_self (Measure.restrict_mono hsub le_rfl)
  have hU : LocallyIntegrable U ν := ((Lp.memLp U).mono_measure hmeasure).locallyIntegrable (by norm_num)
  have hV (i) : LocallyIntegrable (V i) ν :=
    ((Lp.memLp (V i)).mono_measure hmeasure).locallyIntegrable (by norm_num)
  have hfirst (i) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i (fun z => V i (t,z))
      (fun z => U (t,z)) Ω₀ := by
    filter_upwards [(hasWeakPartialDeriv_dirichletLocalSpacetimeWeakPartialLp q α
      hΩ hΩc hΩs (timeMeasure T) i u).filter_mono (ae_mono Measure.restrict_le_self)] with t ht
    exact ht.restrict hΩ₀ hsub
  have hsecond (i) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k (fun z => H k i (t,z))
      (fun z => V i (t,z)) Ω₀ := by
    have hc := ae_restrict_of_ae (s := Icc t₀ t₁)
      (dirichletLocalSpacetimeWeakPartialLp_coeFn q α hΩ hΩc hΩs (timeMeasure T) i u)
    filter_upwards [hH i k, hc] with t ht hct
    have he : (fun z => V i (t, z)) =ᵐ[volume.restrict Ω₀]
        (fun z => dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t) z) := by
      exact ae_restrict_of_ae_restrict_of_subset hsub hct
    rw [← hHsym i k]
    exact Sobolev.Euclidean.hasWeakPartialDeriv_congr_ae hΩ₀ k he.symm ht
  have hspace : ∀ ψ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
      (∫ p, U p * fderiv ℝ ψ p (0, EuclideanSpace.single k 1) ∂ν) =
        -∫ p, V k p * ψ p ∂ν := by
    intro ψ hψ hψc hψs
    exact Sobolev.Euclidean.integral_fderiv_prod_eq_neg_of_hasWeakPartialDeriv
      hU (hV k) k (hfirst k) ψ hψ hψc
      (hψs.trans (Set.prod_mono (subset_univ _) Subset.rfl))
  have hflux (ij : Fin (Module.finrank ℝ EuN) × Fin (Module.finrank ℝ EuN)) :
      ∀ ψ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
      (∫ p, V ij.1 p * fderiv ℝ ψ p (0, EuclideanSpace.single k 1) ∂ν) =
        -∫ p, H k ij.1 p * ψ p ∂ν := by
    intro ψ hψ hψc hψs
    exact Sobolev.Euclidean.integral_fderiv_prod_eq_neg_of_hasWeakPartialDeriv
      (hV ij.1) ((Lp.memLp (H k ij.1)).locallyIntegrable (by norm_num)) k (hsecond ij.1)
      ψ hψ hψc (hψs.trans (Set.prod_mono (subset_univ _) Subset.rfl))
  have hJ : Ioo t₀ t₁ ⊆ D.regular := by
    intro t ht
    exact hreg ⟨ht₀.le.trans ht.1.le, ht.2.le.trans ht₁.le⟩
  have hΩs' := hsub.trans (subset_closure.trans hΩs)
  have hρ : ContDiffOn ℝ (⊤ : ℕ∞) ρ (Ioo t₀ t₁ ×ˢ Ω₀) :=
    (MetricExtension.densityOnEuclid_family_contDiffOn hG hJ α).mono
      (Set.prod_mono Subset.rfl (hΩs'.trans (image_mono interior_subset)))
  have hA (i j) : ContDiffOn ℝ (⊤ : ℕ∞) (A i j) (Ioo t₀ t₁ ×ˢ Ω₀) :=
    MetricExtension.weightedInvGramOnEuclid_family_contDiffOn hG hJ α hΩs' i j
  have hbase : ∀ ψ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
      (∫ p, ρ p * U p * fderiv ℝ ψ p (1, 0) ∂ν) =
        (∑ ij : Fin (Module.finrank ℝ EuN) × Fin (Module.finrank ℝ EuN), ∫ p,
          A ij.1 ij.2 p * V ij.1 p * fderiv ℝ ψ p (0, EuclideanSpace.single ij.2 1) ∂ν) -
          ∫ p, L p * ψ p ∂ν := by
    intro ψ hψ hψc hψs
    have hb := hu.integral_spacetime_test_divergence hXcont hacont α hΩ hΩc hΩs hψ hψc
      hΩ₀.measurableSet hsub ht₀ ht₁ hψs
    simpa only [Fintype.sum_prod_type] using hb
  have hcomm := Sobolev.integral_weak_deriv_weighted_divergence Finset.univ
    (isOpen_Ioo.prod hΩ₀) (0, EuclideanSpace.single k 1) (1, 0)
    (fun ij : Fin (Module.finrank ℝ EuN) × Fin (Module.finrank ℝ EuN) =>
      (0, EuclideanSpace.single ij.2 1)) hU (hV k)
    ((Lp.memLp R).locallyIntegrable (by norm_num))
    (fun ij _ => hV ij.1) (fun ij _ => (Lp.memLp (H k ij.1)).locallyIntegrable (by norm_num))
    hρ (fun ij _ => hA ij.1 ij.2) hspace hR (fun ij _ => hflux ij) hbase hφ hφc hφs
  simpa only [Fintype.sum_prod_type] using hcomm




end DifferentialGeometry.Analysis.Parabolic.Dirichlet
