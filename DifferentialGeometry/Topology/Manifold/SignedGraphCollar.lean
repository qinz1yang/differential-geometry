import DifferentialGeometry.Topology.Manifold.ProductChartCollar

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace G M]

theorem exists_smoothTwoSidedCollar_of_signed_partialDiffeomorph_graph [CompactSpace N]
    (Φ : PartialDiffeomorph (I.prod 𝓘(ℝ)) J (N × ℝ) M ∞)
    (a : N → ℝ) (ha : ContMDiff I 𝓘(ℝ) ∞ a)
    (hgraph : ∀ p, (p, a p) ∈ Φ.source) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    {r : ℝ} (hr : 0 < r) :
    ∃ c : SmoothTwoSidedCollar I J (fun p ↦ Φ (p, a p)),
      c.radius < r ∧
      (∀ p t, t ∈ Icc (-c.radius) c.radius → (p, a p + σ * t) ∈ Φ.source) ∧
      ∀ q : N × symmetricOpenInterval c.radius,
        c.toFun q = Φ (q.1, a q.1 + σ * (q.2 : ℝ)) := by
  let O : TopologicalSpace.Opens (N × ℝ) := ⟨Φ.source, Φ.open_source⟩
  have hO : (O : Set (N × ℝ)) ⊆ Φ.source := Subset.rfl
  let V : TopologicalSpace.Opens M :=
    ⟨Φ '' (O : Set (N × ℝ)), image_opens_isOpen Φ hO⟩
  let d : Diffeomorph (I.prod 𝓘(ℝ)) J O V ∞ :=
    PartialDiffeomorph.toOpensDiffeo Φ (show (O : Set (N × ℝ)) ⊆ Φ.source from Subset.rfl)
  obtain ⟨c, hcr, hstrip, hpoint⟩ := exists_smoothTwoSidedCollar_of_product_chart_graph
    O V d a ha hgraph hr
  change SmoothTwoSidedCollar I J (fun p ↦ Φ (p, a p)) at c
  have hstrip' (p : N) (t : ℝ) (ht : t ∈ Icc (-c.radius) c.radius) :
      (p, a p + t) ∈ Φ.source := hstrip p t ht
  have hpoint' (q : N × symmetricOpenInterval c.radius) :
      c.toFun q = Φ (q.1, a q.1 + (q.2 : ℝ)) := (hpoint q).choose_spec
  rcases hσ with rfl | rfl
  · refine ⟨c, hcr, ?_, ?_⟩
    · intro p t ht
      simpa only [one_mul] using hstrip' p t ht
    · intro q
      simpa only [one_mul] using hpoint' q
  · refine ⟨c.reverse, hcr, ?_, ?_⟩
    · intro p t ht
      change t ∈ Icc (-c.radius) c.radius at ht
      simpa only [neg_one_mul] using hstrip' p (-t) (by
        constructor <;> linarith [ht.1, ht.2])
    · intro q
      have hq : -c.radius < (q.2 : ℝ) ∧ (q.2 : ℝ) < c.radius := q.2.property
      change c.toFun (q.1, ⟨-(q.2 : ℝ), _⟩) = _
      simpa only [neg_one_mul] using hpoint'
        (q.1, ⟨-(q.2 : ℝ), by constructor <;> linarith [hq.1, hq.2]⟩)

end DifferentialGeometry.Topology
