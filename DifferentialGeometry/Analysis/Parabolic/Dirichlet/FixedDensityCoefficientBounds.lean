import DifferentialGeometry.Analysis.Parabolic.Dirichlet.LocalCoefficientRegularity
import DifferentialGeometry.Analysis.Sobolev.Tools.DifferenceQuotientBounds

noncomputable section

namespace DifferentialGeometry.Analysis.Laplacian.MetricExtension

open Manifold Set
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Analysis.Sobolev
open scoped ContDiff Manifold Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

theorem exists_uniform_fixed_density_nirenberg_coefficients_bound
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set ℝ} (hJc : IsCompact J) (hJ : J ⊆ D.regular)
    (q : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    {Ω K : Set EuclN} (hΩ : IsOpen Ω)
    (hΩs : Ω ⊆ toEuclidean (E := E) '' interior (extChartAt I α).target)
    (hK : IsCompact K) (hKs : K ⊆ Ω) :
    let A := fun t i j z => invGramOnEuclid (I := I) (G.metric t) α i j z
    let P := fun z => φ ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))
    let R := fun t i j z => (densityOnEuclid q α z * A t i j z) *
      fderiv ℝ P z (EuclideanSpace.single j 1)
    ∃ δ : ℝ, 0 < δ ∧ ∃ L : ℝ, 0 ≤ L ∧ Metric.cthickening δ K ⊆ Ω ∧
      ∀ t ∈ J, ∀ (k : Fin (Module.finrank ℝ E)) (s : ℝ), |s| ≤ δ → ∀ z ∈ K,
        ∀ i j,
          (|translate k s (A t i j) z| ≤ L ∧ |diffQuot k s (A t i j) z| ≤ L) ∧
          (|translate k s (R t i j) z| ≤ L ∧ |diffQuot k s (R t i j) z| ≤ L) := by
  intro A P R
  have htarget : Ω ⊆ chartTargetEuclid (I := I) α :=
    hΩs.trans (image_mono interior_subset)
  have hσ : ContDiffOn ℝ ∞ (fun p : ℝ × EuclN => densityOnEuclid q α p.2)
      (D.regular ×ˢ Ω) :=
    (densityOnEuclid_contDiffOn q α).comp contDiff_snd.contDiffOn
      (fun p hp => htarget hp.2)
  have hA (i j) : ContDiffOn ℝ ∞ (fun p : ℝ × EuclN => A p.1 i j p.2)
      (D.regular ×ˢ Ω) :=
    invGramOnEuclid_family_contDiffOn hG Subset.rfl α hΩs i j
  have hP : ContDiffOn ℝ ∞ (fun p : ℝ × EuclN => P p.2) (D.regular ×ˢ Ω) :=
    ((φ.contMDiff.comp_contMDiffOn (contMDiffOn_chart_symm (I := I) α)).contDiffOn).comp
      contDiff_snd.contDiffOn (fun p hp => htarget hp.2)
  have hPd : ContDiffOn ℝ ∞
      (fun p : ℝ × EuclN => fderiv ℝ P p.2) (D.regular ×ˢ Ω) :=
    DifferentialGeometry.Analysis.spatialFDeriv_contDiffOn
      (G := fun _ : ℝ => P) D.regular_isOpen.uniqueDiffOn hΩ hP
  have hR (i j) : ContDiffOn ℝ ∞ (fun p : ℝ × EuclN => R p.1 i j p.2)
      (D.regular ×ˢ Ω) :=
    (hσ.mul (hA i j)).mul (hPd.clm_apply contDiffOn_const)
  let Ix := Fin (Module.finrank ℝ E)
  let c : ((Ix × Ix) ⊕ (Ix × Ix)) → ℝ → EuclN → ℝ :=
    Sum.elim (fun p t => A t p.1 p.2) (fun p t => R t p.1 p.2)
  have hc (i) : ContDiffOn ℝ ∞ (fun p : ℝ × EuclN => c i p.1 p.2)
      (D.regular ×ˢ Ω) := by
    cases i with
    | inl ij => exact hA ij.1 ij.2
    | inr ij => exact hR ij.1 ij.2
  have hDc (i) : ContinuousOn (fun p : ℝ × EuclN => fderiv ℝ (c i p.1) p.2)
      (J ×ˢ Ω) :=
    ((DifferentialGeometry.Analysis.spatialFDeriv_contDiffOn
      (G := c i) D.regular_isOpen.uniqueDiffOn hΩ (hc i)).continuousOn).mono
      (prod_mono hJ Subset.rfl)
  have hdiff : ∀ i t, t ∈ J → DifferentiableOn ℝ (c i t) Ω := by
    intro i t ht
    exact ((hc i).comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun z hz => ⟨hJ ht, hz⟩)).differentiableOn (by simp)
  obtain ⟨δ, hδ, L, hL, hδΩ, hbound⟩ :=
    exists_uniform_translate_diffQuot_bound_on_compact_family hJc hΩ hK hKs hdiff
      (fun i => (hc i).continuousOn.mono (prod_mono hJ Subset.rfl)) hDc
  refine ⟨δ, hδ, L, hL, hδΩ, ?_⟩
  intro t ht k s hs z hz i j
  exact ⟨hbound (Sum.inl (i, j)) t ht k s hs z hz,
    hbound (Sum.inr (i, j)) t ht k s hs z hz⟩

end DifferentialGeometry.Analysis.Laplacian.MetricExtension
