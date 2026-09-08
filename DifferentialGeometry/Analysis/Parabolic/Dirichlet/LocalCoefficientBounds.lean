import DifferentialGeometry.Analysis.Integration.Lp.ContinuousOn
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.LocalCoefficientRegularity
import DifferentialGeometry.Analysis.Sobolev.Tools.DifferenceQuotientBounds

noncomputable section

namespace DifferentialGeometry.Analysis.Laplacian.MetricExtension

open Bundle Manifold Set
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Sobolev
open scoped ContDiff Manifold Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

theorem exists_uniform_chart_coefficients_translate_diffQuot_bound
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set ℝ} (hJc : IsCompact J) (hJ : J ⊆ D.regular)
    (q : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    (X : ℝ → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' E p.2 (X p.1 p.2))
      (D.regular ×ˢ (trivializationAt E (TangentSpace I) α).baseSet))
    {Ω K : Set EuclN} (hΩ : IsOpen Ω)
    (hΩs : Ω ⊆ toEuclidean (E := E) '' interior (extChartAt I α).target)
    (hK : IsCompact K) (hKs : K ⊆ Ω) :
    let A := fun t i j z => invGramOnEuclid (I := I) (G.metric t) α i j z
    let P := fun t z => (riemannianVolumeDensitySmoothMap (G.metric t) q * φ)
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))
    let R := fun t i j z => weightedInvGramOnEuclid (I := I) (G.metric t) α i j z *
      fderiv ℝ (P t) z (EuclideanSpace.single j 1)
    let B := fun t i z => chartCoeffOnE (I := I) α (X t) i ((toEuclidean (E := E)).symm z)
    ∃ δ : ℝ, 0 < δ ∧ ∃ L : ℝ, 0 ≤ L ∧ Metric.cthickening δ K ⊆ Ω ∧
      ∀ t ∈ J, ∀ (k : Fin (Module.finrank ℝ E)) (s : ℝ), |s| ≤ δ → ∀ z ∈ K,
        (∀ i j, (|translate k s (A t i j) z| ≤ L ∧ |diffQuot k s (A t i j) z| ≤ L) ∧
          (|translate k s (R t i j) z| ≤ L ∧ |diffQuot k s (R t i j) z| ≤ L)) ∧
        (∀ i, |translate k s (B t i) z| ≤ L ∧ |diffQuot k s (B t i) z| ≤ L) := by
  intro A P R B
  let Ix := Fin (Module.finrank ℝ E)
  let c : ((Ix × Ix) ⊕ ((Ix × Ix) ⊕ Ix)) → ℝ → EuclN → ℝ :=
    Sum.elim (fun p t => A t p.1 p.2)
      (Sum.elim (fun p t => R t p.1 p.2) (fun i t => B t i))
  have hc : ∀ i, ContDiffOn ℝ ∞ (fun p : ℝ × EuclN => c i p.1 p.2) (D.regular ×ˢ Ω) := by
    intro i
    rcases i with ij | ij | i
    · exact invGramOnEuclid_family_contDiffOn hG Subset.rfl α hΩs ij.1 ij.2
    · exact weightedInvGramOnEuclid_mul_fderiv_volumeDensity_family_contDiffOn
        hG Subset.rfl q α φ hΩ hΩs ij.1 ij.2
    · exact (chartCoeffOnE_comp_toEuclidean_symm_family_contDiffOn X α hX i).mono
        (prod_mono Subset.rfl (hΩs.trans (image_mono interior_subset)))
  have hDc : ∀ i, ContinuousOn (fun p : ℝ × EuclN => fderiv ℝ (c i p.1) p.2)
      (J ×ˢ Ω) := by
    intro i
    rcases i with ij | ij | i
    · exact (invGramOnEuclid_family_fderiv_contDiffOn hG hJ α hΩ hΩs ij.1 ij.2).continuousOn
    · exact (weightedInvGramOnEuclid_mul_fderiv_volumeDensity_family_fderiv_contDiffOn
        hG hJ q α φ hΩ hΩs ij.1 ij.2).continuousOn
    · exact ((chartCoeffOnE_comp_toEuclidean_symm_family_fderiv_contDiffOn X
        D.regular_isOpen.uniqueDiffOn α hX hΩ (hΩs.trans (image_mono interior_subset)) i).continuousOn).mono
          (prod_mono hJ Subset.rfl)
  have hdiff : ∀ i t, t ∈ J → DifferentiableOn ℝ (c i t) Ω := by
    intro i t ht
    exact ((hc i).comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun z hz => ⟨hJ ht, hz⟩)).differentiableOn (by simp)
  obtain ⟨δ, hδ, L, hL, hδΩ, hbound⟩ := exists_uniform_translate_diffQuot_bound_on_compact_family
    hJc hΩ hK hKs hdiff (fun i => (hc i).continuousOn.mono (prod_mono hJ Subset.rfl)) hDc
  refine ⟨δ, hδ, L, hL, hδΩ, ?_⟩
  intro t ht k s hs z hz
  refine ⟨?_, ?_⟩
  · intro i j
    exact ⟨hbound (Sum.inl (i, j)) t ht k s hs z hz,
      hbound (Sum.inr (Sum.inl (i, j))) t ht k s hs z hz⟩
  · intro i
    exact hbound (Sum.inr (Sum.inr i)) t ht k s hs z hz


omit [T2Space M] [SigmaCompactSpace M] in
open MeasureTheory in
open scoped ENNReal in
theorem weightedInvGramOnEuclid_family_fderiv_memLp_top
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set ℝ} (hJc : IsCompact J) (hJ : J ⊆ D.regular) (α : M)
    {Ω : Set EuclN} (hΩ : MeasurableSet Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := E) '' interior (extChartAt I α).target)
    (i j k : Fin (Module.finrank ℝ E)) (μ : Measure (ℝ × EuclN)) :
    MemLp (fun p : ℝ × EuclN => fderiv ℝ
      (weightedInvGramOnEuclid (I := I) (G.metric p.1) α i j) p.2 (EuclideanSpace.single k 1))
      ∞ (μ.restrict (J ×ˢ Ω)) := by
  let U := toEuclidean (E := E) '' interior (extChartAt I α).target
  have hU : IsOpen U := (toEuclidean (E := E)).isOpenMap _ isOpen_interior
  have hc := (weightedInvGramOnEuclid_family_fderiv_contDiffOn hG hJ α hU Subset.rfl i j).clm_apply (contDiffOn_const (c := EuclideanSpace.single k 1))
  exact (hc.continuousOn.mono (prod_mono Subset.rfl hΩs)).memLp_top_of_subset_isCompact (hJc.prod hΩc) (hJc.measurableSet.prod hΩ)
      (prod_mono Subset.rfl subset_closure)


end DifferentialGeometry.Analysis.Laplacian.MetricExtension
