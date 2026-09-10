import DifferentialGeometry.Geometry.Neck.CrossSectionGraph
import DifferentialGeometry.Topology.GraphBandChart

noncomputable section
open Set DifferentialGeometry
open scoped Manifold ContDiff
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry.Neck

private abbrev S := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
private instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
private instance : PathConnectedSpace S :=
  isPathConnected_iff_pathConnectedSpace.mp
    (isPathConnected_sphere (by simp [← Module.finrank_eq_rank] :
      1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 3))) _ zero_le_one)

theorem cylindricalChart.exists_strip_of_full_cross_sections_and_gradient_close
    {F H M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M] [T2Space M]
    (C₀ C₁ : cylindricalChart J (M := M)) (g : SmoothRiemannianMetric J M)
    (t₀ t₁ l r : ℝ)
    (hsection : ∀ p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, (p, t₀) ∈ C₀.domain)
    (htarget : ∀ p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      (C₀.chart ⟨(p, t₀), hsection p⟩ : M) ∈ C₁.target)
    {U : Set C₁.domain} (ε : ℝ) (hε : ε < 1) (hsmall : C₁.metricCloseOn g ε U)
    (hU : ∀ p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      C₁.chart.symm ⟨(C₀.chart ⟨(p, t₀), hsection p⟩ : M), htarget p⟩ ∈ U)
    (σ c δ B : ℝ) (hσ : σ = 1 ∨ σ = -1) (hδ : δ * Real.sqrt (1 + ε) < 1)
    (hgrad : ∀ p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      let y : M := C₀.chart ⟨(p, t₀), hsection p⟩
      Real.sqrt (g.inner y (gradFun g C₀.axial y - σ • gradFun g C₁.axial y)
        (gradFun g C₀.axial y - σ • gradFun g C₁.axial y)) ≤ δ)
    (hvalue : ∀ p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      let y : M := C₀.chart ⟨(p, t₀), hsection p⟩
      |C₀.axial y - σ * C₁.axial y - c| ≤ B)
    (htrunc : ∀ p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      ∀ t ∈ Icc l r, (p, t) ∈ C₁.domain)
    (ht₁ : t₁ ∈ Icc l r)
    (hcoord : ∀ p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      ((C₁.chart.symm ⟨(C₀.chart ⟨(p, t₀), hsection p⟩ : M), htarget p⟩ :
        Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ)).2 ∈ Icc l r)
    (hne : ∀ p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      ((C₁.chart.symm ⟨(C₀.chart ⟨(p, t₀), hsection p⟩ : M), htarget p⟩ :
        Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ)).2 ≠ t₁) :
    ∃ (η : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₘ⟮𝓡 2, 𝓡 2⟯
        Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
      (h : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ),
      ContMDiff (𝓡 2) 𝓘(ℝ) ∞ h ∧
      ∃ hmem : ∀ p, (p, h p) ∈ C₁.domain,
        (∀ p, (C₁.chart ⟨(p, h p), hmem p⟩ : M) =
          (C₀.chart ⟨(η p, t₀), hsection (η p)⟩ : M)) ∧
        (∀ p, |(Real.sqrt C₀.scale)⁻¹ * t₀ - σ * ((Real.sqrt C₁.scale)⁻¹ * h p) - c| ≤ B) ∧
        let A := {x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ |
          min (h x.1) t₁ ≤ x.2 ∧ x.2 ≤ max (h x.1) t₁}
        A ⊆ C₁.domain ∧
        ∃ D : Set M, D = C₁.region ((Subtype.val : C₁.domain →
          Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) ⁻¹' A) ∧
          IsCompact D ∧ closure (interior D) = D ∧ IsPreconnected (interior D) ∧
          frontier D =
            range (fun p ↦ (C₀.chart ⟨(p, t₀), hsection p⟩ : M)) ∪
            range (fun p ↦ (C₁.chart ⟨(p, t₁), htrunc p t₁ ht₁⟩ : M)) ∧
          D ⊆ C₁.region ((Subtype.val : C₁.domain →
            Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) ⁻¹'
              ((univ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) ×ˢ Icc l r)) := by
  obtain ⟨η, h, hh, hmem, heq, herr⟩ :=
    C₀.exists_graph_of_full_cross_section_and_gradient_close C₁ g t₀ hsection htarget
      ε hε hsmall hU σ c δ B hσ hδ hgrad hvalue
  have hinverse (p : S) :
      C₁.chart.symm ⟨(C₀.chart ⟨(η p, t₀), hsection (η p)⟩ : M), htarget (η p)⟩ =
        ⟨(p, h p), hmem p⟩ := by
    have hv : (⟨(C₀.chart ⟨(η p, t₀), hsection (η p)⟩ : M), htarget (η p)⟩ : C₁.target) =
        C₁.chart ⟨(p, h p), hmem p⟩ := Subtype.ext (heq p).symm
    rw [hv, C₁.chart.symm_apply_apply]
  have hb (p : S) : h p ∈ Icc l r := by
    have hp := hcoord (η p)
    rw [hinverse p] at hp
    exact hp
  have hn (p : S) : h p ≠ t₁ := by
    have hp := hne (η p)
    rw [hinverse p] at hp
    exact hp
  let a : S → ℝ := fun p ↦ min (h p) t₁
  let b : S → ℝ := fun p ↦ max (h p) t₁
  let A : Set (S × ℝ) := {x | a x.1 ≤ x.2 ∧ x.2 ≤ b x.1}
  let f : C₁.domain → M := fun x ↦ (C₁.chart x : M)
  let D := f '' ((Subtype.val : C₁.domain → S × ℝ) ⁻¹' A)
  have ha : Continuous a := hh.continuous.min continuous_const
  have hbcont : Continuous b := hh.continuous.max continuous_const
  have hab (p : S) : a p < b p := min_lt_max.mpr (hn p)
  have hAstrip : A ⊆ (univ : Set S) ×ˢ Icc l r := by
    intro x hx
    exact ⟨mem_univ _, (le_min (hb x.1).1 ht₁.1).trans hx.1,
      hx.2.trans (max_le (hb x.1).2 ht₁.2)⟩
  have hAO : A ⊆ C₁.domain := fun x hx ↦ htrunc x.1 x.2 (hAstrip hx).2
  have hcompact : IsCompact A := isCompact_graphBand a b ha hbcont hab
  have hreg : closure (interior A) = A := by
    rw [interior_graphBand a b ha hbcont hab]
    exact closure_openGraphBand a b ha hbcont hab
  have hconn : IsPreconnected (interior A) := by
    rw [interior_graphBand a b ha hbcont hab]
    exact isPreconnected_openGraphBand a b ha hbcont hab
  have hDregion : D = C₁.region ((Subtype.val : C₁.domain → S × ℝ) ⁻¹' A) := by
    rw [cylindricalChart.region, image_image]
  have hDcompact : IsCompact D :=
    (_root_.Topology.IsInducing.subtypeVal.isCompact_preimage' hcompact
      (fun x hx ↦ ⟨⟨x, hAO hx⟩, rfl⟩)).image
        (continuous_subtype_val.comp C₁.chart.toHomeomorph.continuous)
  have hDreg : closure (interior D) = D :=
    Embedding.closure_interior_opens_chart_image C₁.domain C₁.target C₁.chart.toHomeomorph
      hcompact hAO hreg
  have hDconn : IsPreconnected (interior D) :=
    Embedding.isPreconnected_interior_opens_chart_image C₁.domain C₁.target C₁.chart.toHomeomorph
      hconn (interior_subset.trans hAO)
  have hfront := frontier_graphBand_of_opens_product_chart C₁.domain C₁.target
    C₁.chart.toHomeomorph a b ha hbcont hab hAO
  have hfaces :
      range (fun p ↦ (C₁.chart ⟨(p, a p), hAO ⟨le_rfl, (hab p).le⟩⟩ : M)) ∪
        range (fun p ↦ (C₁.chart ⟨(p, b p), hAO ⟨(hab p).le, le_rfl⟩⟩ : M)) =
      range (fun p ↦ (C₁.chart ⟨(p, h p), hmem p⟩ : M)) ∪
        range (fun p ↦ (C₁.chart ⟨(p, t₁), htrunc p t₁ ht₁⟩ : M)) := by
    ext y
    constructor
    · rintro (⟨p, rfl⟩ | ⟨p, rfl⟩)
      · by_cases hp : h p ≤ t₁
        · exact Or.inl ⟨p, congrArg f (Subtype.ext (Prod.ext rfl (min_eq_left hp).symm))⟩
        · exact Or.inr ⟨p, congrArg f (Subtype.ext (Prod.ext rfl (min_eq_right (le_of_not_ge hp)).symm))⟩
      · by_cases hp : h p ≤ t₁
        · exact Or.inr ⟨p, congrArg f (Subtype.ext (Prod.ext rfl (max_eq_right hp).symm))⟩
        · exact Or.inl ⟨p, congrArg f (Subtype.ext (Prod.ext rfl (max_eq_left (le_of_not_ge hp)).symm))⟩
    · rintro (⟨p, rfl⟩ | ⟨p, rfl⟩)
      · by_cases hp : h p ≤ t₁
        · exact Or.inl ⟨p, congrArg f (Subtype.ext (Prod.ext rfl (min_eq_left hp)))⟩
        · exact Or.inr ⟨p, congrArg f (Subtype.ext (Prod.ext rfl (max_eq_left (le_of_not_ge hp))))⟩
      · by_cases hp : h p ≤ t₁
        · exact Or.inr ⟨p, congrArg f (Subtype.ext (Prod.ext rfl (max_eq_right hp)))⟩
        · exact Or.inl ⟨p, congrArg f (Subtype.ext (Prod.ext rfl (min_eq_right (le_of_not_ge hp))))⟩
  have hgraph_range : range (fun p ↦ (C₁.chart ⟨(p, h p), hmem p⟩ : M)) =
      range (fun p ↦ (C₀.chart ⟨(p, t₀), hsection p⟩ : M)) := by
    ext y
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨η p, (heq p).symm⟩
    · rintro ⟨p, rfl⟩
      exact ⟨η.symm p, (heq (η.symm p)).trans (by rw [η.apply_symm_apply])⟩
  refine ⟨η, h, hh, hmem, heq, herr, hAO, D, hDregion, hDcompact, hDreg, hDconn, ?_, ?_⟩
  · exact hfront.trans (hfaces.trans (congrArg (· ∪ _) hgraph_range))
  · rw [hDregion]
    unfold cylindricalChart.region
    exact image_mono (image_mono (preimage_mono hAstrip))

end DifferentialGeometry.Geometry.Neck
