import DifferentialGeometry.Analysis.Parabolic.Dirichlet.WeakDensity.SpatialDerivatives
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivativeProduct

noncomputable section

open Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

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

private local instance : MeasurableSpace EuStd :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ EuN)) → ℝ)

theorem exists_local_lp_spatial_time_weak_partial_trees_of_weighted_weak_equation
    (m : ℕ)
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
    (FTree : ∀ j : ℕ, (Fin j → Fin (Module.finrank ℝ EuN)) →
      Lp ℝ 2 ((volume.restrict (Icc a b)).prod (volume.restrict Ω)))
    (hFroot : FTree 0 (fun i => Fin.elim0 i) = F)
    (hFweak : ∀ j, j < m → ∀ β i, ∀ᵐ t ∂volume.restrict (Icc a b),
      DeGiorgi.HasWeakPartialDeriv i
        (fun x => FTree (j + 1) (Fin.cons i β) (t, x))
        (fun x => FTree j β (t, x)) Ω)
    {c d : ℝ} (hac : a < c) (hdb : d < b)
    {Ω₀ : Set EuStd} (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω) :
    let ν := (volume.restrict (Icc c d)).prod (volume.restrict Ω₀)
    let ρ := fun q : ℝ × EuStd => MetricExtension.densityOnEuclid (G.metric q.1) α q.2
    let A := fun i j (q : ℝ × EuStd) =>
      MetricExtension.weightedInvGramOnEuclid (G.metric q.1) α i j q.2
    ∃ V RTree : ∀ j : ℕ, (Fin j → Fin (Module.finrank ℝ EuN)) → Lp ℝ 2 ν,
      (V 0 (fun i => Fin.elim0 i) =ᵐ[ν] U) ∧
      (∀ k, V 1 (Fin.cons k (fun i => Fin.elim0 i)) =ᵐ[ν] K k) ∧
      (∀ j, j < m + 2 → ∀ β i, ∀ᵐ t ∂volume.restrict (Icc c d),
        DeGiorgi.HasWeakPartialDeriv i
          (fun x => V (j + 1) (Fin.cons i β) (t, x)) (fun x => V j β (t, x)) Ω₀) ∧
      (∀ j, j < m → ∀ β i, ∀ᵐ t ∂volume.restrict (Icc c d),
        DeGiorgi.HasWeakPartialDeriv i
          (fun x => RTree (j + 1) (Fin.cons i β) (t, x)) (fun x => RTree j β (t, x)) Ω₀) ∧
      (RTree 0 (fun i => Fin.elim0 i) =ᵐ[ν] fun q => (ρ q)⁻¹ *
        ((∑ i, ∑ j, (A i j q * V 2 (Fin.cons j (Fin.cons i (fun k => Fin.elim0 k))) q +
          fderiv ℝ (fun x => A i j (q.1, x)) q.2 (EuclideanSpace.single j 1) * K i q)) +
            F q - fderiv ℝ ρ q (1, 0) * U q)) ∧
      ∀ j, j ≤ m → ∀ β (φ : ℝ × EuStd → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ →
        HasCompactSupport φ → tsupport φ ⊆ Ioo c d ×ˢ Ω₀ →
        (∫ q, V j β q * fderiv ℝ φ q (1, 0) ∂ν) = -∫ q, RTree j β q * φ q ∂ν := by
  intro ν ρ A
  classical
  let e : Fin 0 → Fin (Module.finrank ℝ EuN) := fun i => Fin.elim0 i
  let μ := volume.restrict (Icc c d)
  have hI : Icc c d ⊆ Icc a b := Icc_subset_Icc hac.le hdb.le
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hμ : μ ≤ volume.restrict (Icc a b) := Measure.restrict_mono hI le_rfl
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  have hΩ₀s := hΩ₀Ω.trans (subset_closure.trans hΩs)
  obtain ⟨V, hVzero, hVone, hVweak⟩ :=
    exists_local_lp_spatial_weak_partial_tree_of_weighted_weak_equation
      m hG hab hreg α hΩ hΩc hΩs U F K hspatial hweak FTree hFroot hFweak
      hac hdb hΩ₀ hΩ₀Ω
  obtain ⟨H, R, hH, _, hRformula, htime⟩ :=
    exists_local_lp_time_weak_derivative_of_weighted_weak_equation
      hG hab hreg α hΩ hΩc hΩs U F K hspatial hweak hac hdb hΩ₀ hΩ₀Ω
  have hHmatch (i j) : H i j = V 2 (Fin.cons j (Fin.cons i e)) := by
    apply Sobolev.Euclidean.lp_eq_of_ae_hasWeakPartialDeriv hΩ₀ (by norm_num) j
      (fun t x => K i (t, x)) (H i j) (V 2 (Fin.cons j (Fin.cons i e))) (hH i j)
    filter_upwards [hVweak 1 (by omega) (Fin.cons i e) j,
      Measure.ae_ae_of_ae_prod (hVone i)] with t ht he
    exact ht.congr_ae he Filter.EventuallyEq.rfl
  obtain ⟨F₀, hF₀eq, hF₀weak⟩ :=
    Sobolev.Euclidean.exists_lp_weak_partial_tree_restrict hμ hΩ₀ hsub m FTree hFweak
  have hFroot' : FTree 0 e = F := hFroot
  have hF₀root : F₀ 0 e =ᵐ[ν] F := by
    simpa only [hFroot'] using hF₀eq 0 e
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
  have hRformulaV : R =ᵐ[ν] fun q => (ρ q)⁻¹ *
      ((∑ i, ∑ j, (A i j q * V 2 (Fin.cons j (Fin.cons i e)) q +
        fderiv ℝ (fun x => A i j (q.1, x)) q.2 (EuclideanSpace.single j 1) *
          V 1 (Fin.cons i e) q)) + F₀ 0 e q - fderiv ℝ ρ q (1, 0) * V 0 e q) := by
    filter_upwards [hRformula, hVzero, ae_all_iff.mpr hVone, hF₀root] with q hq hu hk hf
    simpa only [hHmatch, ← hu, ← hk, ← hf] using hq
  obtain ⟨RTree, hRroot, hRweak⟩ :=
    Sobolev.Euclidean.exists_lp_weak_partial_tree_of_weighted_divergence_source
      (by norm_num) D.regular_isOpen isCompact_Icc (hI.trans hreg) hO hΩ₀ hΩ₀c hΩ₀s m
      ρ A hρsmooth hρne hAsmooth V F₀ R hVweak hF₀weak hRformulaV
  have htimeRoot (φ : ℝ × EuStd → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ioo c d ×ˢ Ω₀) :
      (∫ q, V 0 (fun i => Fin.elim0 i) q * fderiv ℝ φ q (1, 0) ∂ν) =
        -∫ q, RTree 0 (fun i => Fin.elim0 i) q * φ q ∂ν := by
    rw [hRroot]
    calc
      _ = ∫ q, U q * fderiv ℝ φ q (1, 0) ∂ν := by
        apply integral_congr_ae
        filter_upwards [hVzero] with q hq
        rw [hq]
      _ = _ := htime φ hφ hφc hφs
  refine ⟨V, RTree, hVzero, hVone, hVweak, hRweak, ?_, ?_⟩
  · simpa only [hRroot, hHmatch] using hRformula
  · exact Sobolev.Euclidean.integral_fderiv_prod_left_eq_neg_of_finite_weak_partial_trees
      (Z := ℝ) (μ := μ) (W := Ioo c d) m (1 : ℝ)
      (fun j β q => V j β q) (fun j β q => RTree j β q)
      (fun j _ β => (Lp.memLp (V j β)).locallyIntegrable (by norm_num))
      (fun j _ β => (Lp.memLp (RTree j β)).locallyIntegrable (by norm_num))
      (fun j hj => hVweak j (by omega)) hRweak htimeRoot

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
