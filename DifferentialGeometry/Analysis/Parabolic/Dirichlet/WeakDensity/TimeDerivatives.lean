import DifferentialGeometry.Analysis.Parabolic.Dirichlet.WeakDensity.SpatialTimeDerivatives
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakPartialTree.WeightedTimeDerivatives

noncomputable section

open Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Sobolev.Euclidean
  (exists_lp_time_weak_derivative_trees_of_homogeneous_weighted_divergence_equation)

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

theorem exists_local_lp_time_weak_partial_trees_of_homogeneous_weighted_weak_equation
    (m k : ℕ)
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric)
    {a b : ℝ} (hab : a < b) (hreg : Icc a b ⊆ D.regular)
    (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (U : Lp ℝ 2 ((volume.restrict (Icc a b)).prod (volume.restrict Ω)))
    (K : Fin (Module.finrank ℝ EuN) →
      Lp ℝ 2 ((volume.restrict (Icc a b)).prod (volume.restrict Ω)))
    (hspatial : ∀ k, ∀ᵐ t ∂volume.restrict (Icc a b), DeGiorgi.HasWeakPartialDeriv k
      (fun x => K k (t, x)) (fun x => U (t, x)) Ω)
    (hweak : ∀ φ : ℝ × EuStd → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b ×ˢ Ω →
      (∫ p, MetricExtension.densityOnEuclid (G.metric p.1) α p.2 * U p *
        fderiv ℝ φ p (1, 0) ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω)) =
        ∑ j, ∫ p, (∑ i, MetricExtension.weightedInvGramOnEuclid
            (G.metric p.1) α i j p.2 * K i p) *
          fderiv ℝ φ p (0, EuclideanSpace.single j 1)
            ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω))
    {c d : ℝ} (hac : a < c) (hdb : d < b)
    {Ω₀ : Set EuStd} (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω) :
    let ν := (volume.restrict (Icc c d)).prod (volume.restrict Ω₀)
    let e : Fin 0 → Fin (Module.finrank ℝ EuN) := fun i => Fin.elim0 i
    let ρ := fun q : ℝ × EuStd => MetricExtension.densityOnEuclid (G.metric q.1) α q.2
    let A := fun i j (q : ℝ × EuStd) =>
      MetricExtension.weightedInvGramOnEuclid (G.metric q.1) α i j q.2
    ∃ X : Fin (k + 2) → ∀ j : ℕ,
        (Fin j → Fin (Module.finrank ℝ EuN)) → Lp ℝ 2 ν,
      (X 0 0 e =ᵐ[ν] U) ∧
      (∀ i, X 0 1 (Fin.cons i e) =ᵐ[ν] K i) ∧
      (∀ j r, r < m + 2 * (k + 1 - j.val) → ∀ β i,
        ∀ᵐ t ∂volume.restrict (Icc c d), DeGiorgi.HasWeakPartialDeriv i
          (fun x => X j (r + 1) (Fin.cons i β) (t, x)) (fun x => X j r β (t, x)) Ω₀) ∧
      (X 1 0 e =ᵐ[ν] fun q => (ρ q)⁻¹ *
        ((∑ i, ∑ j, (A i j q * X 0 2 (Fin.cons j (Fin.cons i e)) q +
          fderiv ℝ (fun x => A i j (q.1, x)) q.2 (EuclideanSpace.single j 1) *
            X 0 1 (Fin.cons i e) q)) - fderiv ℝ ρ q (1, 0) * X 0 0 e q)) ∧
      ∀ j : Fin (k + 1), ∀ r, r ≤ m + 2 * (k - j.val) →
        ∀ β (φ : ℝ × EuStd → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ →
        HasCompactSupport φ → tsupport φ ⊆ Ioo c d ×ˢ Ω₀ →
        (∫ q, X j.castSucc r β q * fderiv ℝ φ q (1, 0) ∂ν) =
          -∫ q, X j.succ r β q * φ q ∂ν := by
  intro ν e ρ A
  classical
  let ν₀ := (volume.restrict (Icc a b)).prod (volume.restrict Ω)
  let F : Lp ℝ 2 ν₀ := 0
  let FTree : ∀ j : ℕ, (Fin j → Fin (Module.finrank ℝ EuN)) → Lp ℝ 2 ν₀ :=
    fun _ _ => F
  have hFzero : F =ᵐ[ν₀] fun _ => (0 : ℝ) := Lp.coeFn_zero ℝ 2 ν₀
  have hFweak (j : ℕ) (_hj : j < m + 2 * k) (β : Fin j → Fin (Module.finrank ℝ EuN))
      (i : Fin (Module.finrank ℝ EuN)) : ∀ᵐ t ∂volume.restrict (Icc a b),
      DeGiorgi.HasWeakPartialDeriv i
        (fun x => FTree (j + 1) (Fin.cons i β) (t, x)) (fun x => FTree j β (t, x)) Ω := by
    filter_upwards [Measure.ae_ae_of_ae_prod hFzero] with t ht
    have hzero : DeGiorgi.HasWeakPartialDeriv i (fun _ => 0) (fun _ => 0) Ω := by
      intro φ _ _ _
      simp only [zero_mul, integral_zero, neg_zero]
    exact hzero.congr_ae (Filter.EventuallyEq.symm ht) (Filter.EventuallyEq.symm ht)
  have hweakF (φ : ℝ × EuStd → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ioo a b ×ˢ Ω) :
      (∫ p, MetricExtension.densityOnEuclid (G.metric p.1) α p.2 * U p *
        fderiv ℝ φ p (1, 0) ∂ν₀) =
        (∑ j, ∫ p, (∑ i, MetricExtension.weightedInvGramOnEuclid
            (G.metric p.1) α i j p.2 * K i p) *
          fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν₀) - ∫ p, F p * φ p ∂ν₀ := by
    have hz : (∫ p, F p * φ p ∂ν₀) = 0 := by
      calc
        _ = ∫ p, (0 : ℝ) ∂ν₀ := by
          apply integral_congr_ae
          filter_upwards [hFzero] with p hp
          rw [hp, zero_mul]
        _ = 0 := integral_zero _ _
    simpa only [hz, sub_zero] using hweak φ hφ hφc hφs
  obtain ⟨V, R, hVzero, hVone, hVweak, hRweak, hRformula, htime⟩ :=
    exists_local_lp_spatial_time_weak_partial_trees_of_weighted_weak_equation
      (m + 2 * k) hG hab hreg α hΩ hΩc hΩs U F K hspatial hweakF FTree rfl hFweak
      hac hdb hΩ₀ hΩ₀Ω
  have hI : Icc c d ⊆ Icc a b := Icc_subset_Icc hac.le hdb.le
  have hΩsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hν : ν ≤ ν₀ := Measure.prod_mono (Measure.restrict_mono hI le_rfl)
    (Measure.restrict_mono hΩsub le_rfl)
  have hFzero₀ : F =ᵐ[ν] fun _ => (0 : ℝ) := hFzero.filter_mono (ae_mono hν)
  have hRformulaV : R 0 e =ᵐ[ν] fun q => (ρ q)⁻¹ *
      ((∑ i, ∑ j, (A i j q * V 2 (Fin.cons j (Fin.cons i e)) q +
        fderiv ℝ (fun x => A i j (q.1, x)) q.2 (EuclideanSpace.single j 1) *
          V 1 (Fin.cons i e) q)) - fderiv ℝ ρ q (1, 0) * V 0 e q) := by
    filter_upwards [hRformula, hVzero, ae_all_iff.mpr hVone, hFzero₀] with q hq hu hk hf
    simpa only [← hu, ← hk, hf, add_zero] using hq
  let O := toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target
  have hO : IsOpen O := (toEuclidean (E := EuN)).toHomeomorph.isOpenMap _ isOpen_interior
  have hOt : O ⊆ MetricExtension.chartTargetEuclid (I := I_hs) α := image_mono interior_subset
  have hAsmooth (i j) : ContDiffOn ℝ (⊤ : ℕ∞) (A i j) (D.regular ×ˢ O) :=
    MetricExtension.weightedInvGramOnEuclid_family_contDiffOn hG Subset.rfl α Subset.rfl i j
  have hρsmooth : ContDiffOn ℝ (⊤ : ℕ∞) ρ (D.regular ×ˢ O) :=
    (MetricExtension.densityOnEuclid_family_contDiffOn hG Subset.rfl α).mono
      (prod_mono Subset.rfl hOt)
  have hρne (q : ℝ × EuStd) (hq : q ∈ D.regular ×ˢ O) : ρ q ≠ 0 :=
    (MetricExtension.densityOnEuclid_pos (G.metric q.1) α (hOt hq.2)).ne'
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  have hΩ₀s := hΩ₀Ω.trans (subset_closure.trans hΩs)
  obtain ⟨X, hXzero, hXone, hXweak, hXtime⟩ :=
    exists_lp_time_weak_derivative_trees_of_homogeneous_weighted_divergence_equation
      (by norm_num) D.regular_isOpen (hI.trans hreg) hO hΩ₀ hΩ₀c hΩ₀s m k
      ρ A hρsmooth hρne hAsmooth V R
      (fun j hj => hVweak j (by omega)) hRweak (htime 0 (by omega) e) hRformulaV
  refine ⟨X, ?_, ?_, hXweak, ?_, hXtime⟩
  · simpa only [hXzero] using hVzero
  · simpa only [hXzero] using hVone
  · simpa only [hXzero, hXone] using hRformulaV

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
