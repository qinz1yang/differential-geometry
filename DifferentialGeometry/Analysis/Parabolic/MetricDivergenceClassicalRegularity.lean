import DifferentialGeometry.Analysis.Parabolic.MetricDivergenceMixedRegularity
import DifferentialGeometry.Analysis.Parabolic.WeakEquationClassical

noncomputable section

open Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Geometry.Connection
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

theorem exists_local_contDiffOn_solution_of_homogeneous_metric_divergence_equation
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I_hs M}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D g)
    {a b : ℝ} (hab : a < b) (hreg : Icc a b ⊆ D.regular)
    (α : M) {Ω Ω₀ : Set EuStd} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω)
    {c d : ℝ} (hac : a < c) (hdb : d < b) (hcd : c < d) :
    let μ := volume.restrict (Icc a b)
    let ν := μ.prod (volume.restrict Ω)
    let ρ := fun p : ℝ × EuStd => densityOnEuclid (I := I_hs) (g p.1) α p.2
    let A := fun i j (p : ℝ × EuStd) => weightedInvGramOnEuclid (I := I_hs) (g p.1) α i j p.2
    ∀ U : Lp ℝ 2 ν, ∀ K : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      (∀ i, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
        (fun z => K i (t, z)) (fun z => U (t, z)) Ω) →
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ω →
        (∫ p, ρ p * U p * fderiv ℝ φ p (1, 0) ∂ν) =
          (∑ i, ∑ j, ∫ p, A i j p * K i p * fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν)) →
      let μ₀ := μ.restrict (Icc c d)
      let ν₀ := μ₀.prod (volume.restrict Ω₀)
      ∃ u : ℝ × EuStd → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) u (Ioo c d ×ˢ Ω₀) ∧
        (U =ᵐ[ν₀] u) ∧
        ∀ p ∈ Ioo c d ×ˢ Ω₀, fderiv ℝ (fun q => ρ q * u q) p (1, 0) =
          ∑ i, ∑ j, fderiv ℝ (fun q => A i j q * fderiv ℝ u q (0, EuclideanSpace.single i 1))
            p (0, EuclideanSpace.single j 1) := by
  intro μ ν ρ A U K hK hweak μ₀ ν₀
  obtain ⟨u, hu, hUu⟩ := exists_local_contDiffOn_ae_eq_of_homogeneous_metric_divergence_equation
    hG hab hreg α hΩ hΩc hΩs hΩ₀ hΩ₀Ω hac hdb hcd U K hK hweak
  refine ⟨u, hu, hUu, ?_⟩
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hμ₀ : μ₀ = volume.restrict (Ioo c d) := by
    change (volume.restrict (Icc a b)).restrict (Icc c d) = volume.restrict (Ioo c d)
    rw [Measure.restrict_restrict measurableSet_Icc,
      inter_eq_left.mpr (Icc_subset_Icc hac.le hdb.le)]
    exact Measure.restrict_congr_set Ioo_ae_eq_Icc.symm
  have hmeasure : ν₀ ≤ ν :=
    Measure.prod_mono Measure.restrict_le_self (Measure.restrict_mono hsub le_rfl)
  have hUm : MemLp U 2 ((volume.restrict (Ioo c d)).prod (volume.restrict Ω₀)) := by
    rw [← hμ₀]
    exact (Lp.memLp U).mono_measure hmeasure
  have hKm (i) : MemLp (K i) 2 ((volume.restrict (Ioo c d)).prod (volume.restrict Ω₀)) := by
    rw [← hμ₀]
    exact (Lp.memLp (K i)).mono_measure hmeasure
  have hKw (i) : ∀ᵐ t ∂volume.restrict (Ioo c d), DeGiorgi.HasWeakPartialDeriv i
      (fun z => K i (t, z)) (fun z => U (t, z)) Ω₀ := by
    rw [← hμ₀]
    filter_upwards [ae_restrict_of_ae (s := Icc c d) (hK i)] with t ht
    exact ht.restrict hΩ₀ hsub
  have hUu₀ : U =ᵐ[(volume.restrict (Ioo c d)).prod (volume.restrict Ω₀)] u := by
    rw [← hμ₀]
    exact hUu
  let W := toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target
  let G : MetricConnectionFamilyOn (I := I_hs) (M := M) D :=
    { metric := g
      connection := fun t => leviCivitaConnectionOfMetric (g t)
      metricCompatible := fun t => leviCivitaConnectionOfMetric_isMetricCompatible (g t) }
  have hregion : Ioo c d ×ˢ Ω₀ ⊆ D.regular ×ˢ W :=
    prod_mono (Ioo_subset_Icc_self.trans ((Icc_subset_Icc hac.le hdb.le).trans hreg))
      (hsub.trans (subset_closure.trans hΩs))
  have hρ : ContDiffOn ℝ 1 ρ (Ioo c d ×ˢ Ω₀) :=
    ((densityOnEuclid_family_contDiffOn (G := G) hG Subset.rfl α).mono
      (hregion.trans (prod_mono Subset.rfl (image_mono interior_subset)))).of_le (by simp)
  have hA (i j) : ContDiffOn ℝ 1 (A i j) (Ioo c d ×ˢ Ω₀) :=
    ((weightedInvGramOnEuclid_family_contDiffOn (G := G) hG Subset.rfl α Subset.rfl i j).mono
      hregion).of_le (by simp)
  have hweak₀ (φ : ℝ × EuStd → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ioo c d ×ˢ Ω₀) :
      (∫ p, ρ p * U p * fderiv ℝ φ p (1, 0)
        ∂(volume.restrict (Ioo c d)).prod (volume.restrict Ω₀)) =
      (∑ i, ∑ j, ∫ p, A i j p * K i p * fderiv ℝ φ p (0, EuclideanSpace.single j 1)
        ∂(volume.restrict (Ioo c d)).prod (volume.restrict Ω₀)) -
          ∫ p, (0 : ℝ) * φ p ∂(volume.restrict (Ioo c d)).prod (volume.restrict Ω₀) := by
    simp only [zero_mul, integral_zero, sub_zero]
    rw [← hμ₀]
    have hrestrict (v : ℝ × EuStd) (B : ℝ × EuStd → ℝ) :
        (∫ p, B p * fderiv ℝ φ p v ∂ν) = ∫ p, B p * fderiv ℝ φ p v ∂ν₀ := by
      apply integral_eq_integral_restrict_prod_of_support_subset hΩ₀.measurableSet hsub
      intro p hp
      rw [image_eq_zero_of_notMem_tsupport (f := fun p => fderiv ℝ φ p v)
        (fun hs => hp ((Set.prod_mono Ioo_subset_Icc_self Subset.rfl)
          (hφs (tsupport_fderiv_apply_subset ℝ v hs)))), mul_zero]
    have h := hweak φ hφ hφc (hφs.trans
      (prod_mono (fun t ht => ⟨hac.trans ht.1, ht.2.trans hdb⟩) hsub))
    simpa only [hrestrict] using h
  have h := weighted_divergence_eq_of_contDiffOn_ae_eq isOpen_Ioo hΩ₀
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hUm hKm hKw (hu.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))) hUu₀ hρ hA
    (continuousOn_const : ContinuousOn (fun _ => (0 : ℝ)) (Ioo c d ×ˢ Ω₀)) hweak₀
  simpa only [add_zero] using h

end DifferentialGeometry.Analysis.Parabolic
