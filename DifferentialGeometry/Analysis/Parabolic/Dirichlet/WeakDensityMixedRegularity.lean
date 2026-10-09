import DifferentialGeometry.Analysis.Parabolic.Dirichlet.WeakDensityThirdDerivative
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.WeakDensityMixedDerivative

noncomputable section

open Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Integral.Measure
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

private local instance : MeasurableSpace M := borel _
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : MeasurableSpace EuStd :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ EuN)) → ℝ)

theorem exists_local_lp_mixed_weak_derivative_of_weighted_weak_equation
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric)
    {a b : ℝ} (hab : a < b) (hreg : Icc a b ⊆ D.regular)
    (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (U F : Lp ℝ 2 ((volume.restrict (Icc a b)).prod (volume.restrict Ω)))
    (K : Fin (Module.finrank ℝ EuN) →
      Lp ℝ 2 ((volume.restrict (Icc a b)).prod (volume.restrict Ω)))
    (hspatial : ∀ k, ∀ᵐ t ∂volume.restrict (Icc a b), DeGiorgi.HasWeakPartialDeriv k
      (fun x => K k (t, x)) (fun x => U (t, x)) Ω)
    (hweak : ∀ φ : ℝ × EuStd → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b ×ˢ Ω →
      (∫ p, MetricExtension.densityOnEuclid (G.metric p.1) α p.2 * U p *
        fderiv ℝ φ p (1, 0) ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω)) =
        (∑ j, ∫ p, (∑ i, MetricExtension.weightedInvGramOnEuclid
            (G.metric p.1) α i j p.2 * K i p) *
          fderiv ℝ φ p (0, EuclideanSpace.single j 1)
            ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω)) -
        ∫ p, F p * φ p ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω))
    (DF : Fin (Module.finrank ℝ EuN) →
      Lp ℝ 2 ((volume.restrict (Icc a b)).prod (volume.restrict Ω)))
    (hFspatial : ∀ k, ∀ᵐ t ∂volume.restrict (Icc a b), DeGiorgi.HasWeakPartialDeriv k
      (fun x => DF k (t, x)) (fun x => F (t, x)) Ω)
    {c d : ℝ} (hac : a < c) (hdb : d < b)
    {Ω₀ : Set EuStd} (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω) :
    let ν := (volume.restrict (Icc c d)).prod (volume.restrict Ω₀)
    let ρ := fun p : ℝ × EuStd => MetricExtension.densityOnEuclid (G.metric p.1) α p.2
    let A := fun i j (p : ℝ × EuStd) =>
      MetricExtension.weightedInvGramOnEuclid (G.metric p.1) α i j p.2
    ∃ H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      ∃ R : Lp ℝ 2 ν,
      ∃ J : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) →
        Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      ∃ T : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
        (∀ i j, ∀ᵐ t ∂volume.restrict (Icc c d),
          DeGiorgi.HasWeakPartialDeriv j (fun x => H i j (t, x)) (fun x => K i (t, x)) Ω₀) ∧
        (∀ i j k, ∀ᵐ t ∂volume.restrict (Icc c d),
          DeGiorgi.HasWeakPartialDeriv k (fun x => J i j k (t, x)) (fun x => H i j (t, x)) Ω₀) ∧
        (∀ᵐ t ∂volume.restrict (Icc c d),
          Sobolev.Euclidean.MemWkp 3 2 (fun x => U (t, x)) Ω₀) ∧
        (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          tsupport φ ⊆ Ioo c d ×ˢ Ω₀ →
          (∫ p, U p * fderiv ℝ φ p (1, 0) ∂ν) = -∫ p, R p * φ p ∂ν) ∧
        (R =ᵐ[ν] fun p => (ρ p)⁻¹ *
          ((∑ i, ∑ j, (A i j p * H i j p +
            fderiv ℝ (fun x => A i j (p.1, x)) p.2 (EuclideanSpace.single j 1) * K i p)) +
              F p - fderiv ℝ ρ p (1, 0) * U p)) ∧
        (∀ k (φ : ℝ × EuStd → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          tsupport φ ⊆ Ioo c d ×ˢ Ω₀ →
          (∫ p, K k p * fderiv ℝ φ p (1, 0) ∂ν) = -∫ p, T k p * φ p ∂ν) ∧
        ∀ k, ∀ᵐ t ∂volume.restrict (Icc c d), DeGiorgi.HasWeakPartialDeriv k
          (fun x => T k (t, x)) (fun x => R (t, x)) Ω₀ := by
  intro ν ρ A
  classical
  obtain ⟨H, R, J, T, hH, hJ, hUthree, hUtime, hRformula, hKtime⟩ :=
    exists_local_lp_third_weak_derivative_of_weighted_weak_equation
      hG hab hreg α hΩ hΩc hΩs U F K hspatial hweak DF hFspatial hac hdb hΩ₀ hΩ₀Ω
  let μ := volume.restrict (Icc c d)
  have hI : Icc c d ⊆ Icc a b := fun _ ht => ⟨hac.le.trans ht.1, ht.2.trans hdb.le⟩
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hμ : μ ≤ volume.restrict (Icc a b) := Measure.restrict_mono hI le_rfl
  have hν : ν ≤ (volume.restrict (Icc a b)).prod (volume.restrict Ω) :=
    Measure.prod_mono hμ (Measure.restrict_mono hsub le_rfl)
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  have hΩ₀s : closure Ω₀ ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target :=
    hΩ₀Ω.trans (subset_closure.trans hΩs)
  have hUmem : MemLp U 2 ν := (Lp.memLp U).mono_measure hν
  have hFmem : MemLp F 2 ν := (Lp.memLp F).mono_measure hν
  have hKmem (k) : MemLp (K k) 2 ν := (Lp.memLp (K k)).mono_measure hν
  have hDFmem (k) : MemLp (DF k) 2 ν := (Lp.memLp (DF k)).mono_measure hν
  let U₀ := hUmem.toLp U
  let F₀ := hFmem.toLp F
  let K₀ := fun k => (hKmem k).toLp (K k)
  let DF₀ := fun k => (hDFmem k).toLp (DF k)
  have hUrep : U₀ =ᵐ[ν] U := hUmem.coeFn_toLp
  have hFrep : F₀ =ᵐ[ν] F := hFmem.coeFn_toLp
  have hKrep (k) : K₀ k =ᵐ[ν] K k := (hKmem k).coeFn_toLp
  have hDFrep (k) : DF₀ k =ᵐ[ν] DF k := (hDFmem k).coeFn_toLp
  have hspatial₀ (k) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
      (fun x => K₀ k (t, x)) (fun x => U₀ (t, x)) Ω₀ := by
    filter_upwards [(hspatial k).filter_mono (ae_mono hμ),
      Measure.ae_ae_of_ae_prod hUrep, Measure.ae_ae_of_ae_prod (hKrep k)] with t ht hu hk
    exact (DeGiorgi.HasWeakPartialDeriv.restrict hΩ₀ hsub ht).congr_ae
      (Filter.EventuallyEq.symm hu) (Filter.EventuallyEq.symm hk)
  have hH₀ (i j) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
      (fun x => H i j (t, x)) (fun x => K₀ i (t, x)) Ω₀ := by
    filter_upwards [hH i j, Measure.ae_ae_of_ae_prod (hKrep i)] with t ht hk
    exact ht.congr_ae (Filter.EventuallyEq.symm hk) Filter.EventuallyEq.rfl
  have hFspatial₀ (k) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
      (fun x => DF₀ k (t, x)) (fun x => F₀ (t, x)) Ω₀ := by
    filter_upwards [(hFspatial k).filter_mono (ae_mono hμ),
      Measure.ae_ae_of_ae_prod hFrep, Measure.ae_ae_of_ae_prod (hDFrep k)] with t ht hf hdf
    exact (DeGiorgi.HasWeakPartialDeriv.restrict hΩ₀ hsub ht).congr_ae
      (Filter.EventuallyEq.symm hf) (Filter.EventuallyEq.symm hdf)
  have hUtime₀ (φ : ℝ × EuStd → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ioo c d ×ˢ Ω₀) :
      (∫ p, U₀ p * fderiv ℝ φ p (1, 0) ∂ν) = -∫ p, R p * φ p ∂ν := by
    calc
      _ = ∫ p, U p * fderiv ℝ φ p (1, 0) ∂ν := by
        apply integral_congr_ae
        filter_upwards [hUrep] with p hp
        rw [hp]
      _ = _ := hUtime φ hφ hφc hφs
  have hKtime₀ (k) (φ : ℝ × EuStd → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ioo c d ×ˢ Ω₀) :
      (∫ p, K₀ k p * fderiv ℝ φ p (1, 0) ∂ν) = -∫ p, T k p * φ p ∂ν := by
    calc
      _ = ∫ p, K k p * fderiv ℝ φ p (1, 0) ∂ν := by
        apply integral_congr_ae
        filter_upwards [hKrep k] with p hp
        rw [hp]
      _ = _ := hKtime k φ hφ hφc hφs
  have hRformula₀ : R =ᵐ[ν] fun p => (ρ p)⁻¹ *
      ((∑ i, ∑ j, (A i j p * H i j p +
        fderiv ℝ (fun x => A i j (p.1, x)) p.2 (EuclideanSpace.single j 1) * K₀ i p)) +
          F₀ p - fderiv ℝ ρ p (1, 0) * U₀ p) := by
    filter_upwards [hRformula, hUrep, hFrep, ae_all_iff.mpr hKrep] with p hp hu hf hk
    simpa only [hu, hf, hk] using hp
  have hTR := ae_hasWeakPartialDeriv_time_derivative_of_weighted_source
    hG (hI.trans hreg) α hΩ₀ hΩ₀c hΩ₀s U₀ F₀ R K₀ T DF₀ H J
      hspatial₀ hH₀ hJ hFspatial₀ hUtime₀ hKtime₀ hRformula₀
  exact ⟨H, R, J, T, hH, hJ, hUthree, hUtime, hRformula, hKtime, hTR⟩

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
