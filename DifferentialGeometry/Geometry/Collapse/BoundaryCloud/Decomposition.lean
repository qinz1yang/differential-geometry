import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Order.Interval.Set.Infinite

/-!
# Actual boundary decomposition: row-local kernels (blueprint 207B, BCF01–BCF03, B:9642–9885)

* `exists_interval_cover_avoiding` / `exists_compact_interval_union_avoiding` (BCF01): in a
  one-dimensional base chart, a compact set inside an open set lies in the interior of a finite
  union `K₃` of nondegenerate closed intervals inside the open set, whose frontier avoids a
  prescribed finite set (the finite face set `∂D₃`). This is ZSP04's chartwise choice with the face
  set included; no quantitative tolerance is chosen from the endpoints.
* `subset_union_diff_relInterior`, `union_union_union_eq_univ` (BCF01–BCF02): set algebra of
  `M₂ = M₁ \ int_{M₁} S`, `R = M₂ \ int_{M₂} P`, giving `M = Z ∪ C ∪ S ∪ M₂` and `M₂ = P ∪ R`.
* `two_thirds_mul_infDist_lt`, `twenty_lt_infDist` (BCF02): the replacement strong witness stays at
  distance `> 20` from the external boundary.
* `subset_of_inter_eq_empty` (BCF03): a cusp torus with no horizontal disk lies in `R`.
-/

set_option autoImplicit false
open Set Metric

namespace DifferentialGeometry.Geometry.Collapse.BoundaryCloud

/-- BCF01, chartwise: finitely many nondegenerate closed intervals inside `U`, with endpoints off the
finite set `F`, whose open interiors cover the compact set `Q`. -/
theorem exists_interval_cover_avoiding {Q U F : Set ℝ} (hQ : IsCompact Q) (hU : IsOpen U)
    (hQU : Q ⊆ U) (hF : F.Finite) :
    ∃ I : Finset (ℝ × ℝ), (∀ ab ∈ I, ab.1 < ab.2 ∧ Icc ab.1 ab.2 ⊆ U ∧ ab.1 ∉ F ∧ ab.2 ∉ F) ∧
      Q ⊆ ⋃ ab ∈ I, Ioo ab.1 ab.2 := by
  have hloc : ∀ q ∈ Q, ∃ ab : ℝ × ℝ, ab.1 < q ∧ q < ab.2 ∧ Icc ab.1 ab.2 ⊆ U ∧
      ab.1 ∉ F ∧ ab.2 ∉ F := by
    intro q hq
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU q (hQU hq)
    obtain ⟨a, ⟨ha1, ha2⟩, haF⟩ :=
      ((Ioo_infinite (by linarith : q - ε / 2 < q)).sdiff hF).nonempty
    obtain ⟨b, ⟨hb1, hb2⟩, hbF⟩ :=
      ((Ioo_infinite (by linarith : q < q + ε / 2)).sdiff hF).nonempty
    refine ⟨(a, b), ha2, hb1, fun x hx => hball ?_, haF, hbF⟩
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hx.1, hx.2]
  choose g hg using hloc
  obtain ⟨t, ht⟩ := hQ.elim_finite_subcover (fun q : Q => Ioo (g q q.2).1 (g q q.2).2)
    (fun _ => isOpen_Ioo) (fun q hq => mem_iUnion.mpr ⟨⟨q, hq⟩, (hg q hq).1, (hg q hq).2.1⟩)
  refine ⟨t.image fun q : Q => g q q.2, ?_, ?_⟩
  · intro ab hab
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hab
    have h := hg q q.2
    exact ⟨h.1.trans h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  · intro x hx
    obtain ⟨q, hq, hxq⟩ := mem_iUnion₂.mp (ht hx)
    exact mem_iUnion₂.mpr ⟨g q q.2, Finset.mem_image_of_mem _ hq, hxq⟩

/-- BCF01, chartwise `K₃`: a compact finite union of nondegenerate closed intervals inside `U`,
containing `Q` in its interior, whose frontier misses the finite set `F` (so `∂K₃ ∩ ∂D₃ = ∅`). -/
theorem exists_compact_interval_union_avoiding {Q U F : Set ℝ} (hQ : IsCompact Q)
    (hU : IsOpen U) (hQU : Q ⊆ U) (hF : F.Finite) :
    ∃ I : Finset (ℝ × ℝ), (∀ ab ∈ I, ab.1 < ab.2) ∧
      IsCompact (⋃ ab ∈ I, Icc ab.1 ab.2) ∧ (⋃ ab ∈ I, Icc ab.1 ab.2) ⊆ U ∧
      Q ⊆ interior (⋃ ab ∈ I, Icc ab.1 ab.2) ∧
      Disjoint (frontier (⋃ ab ∈ I, Icc ab.1 ab.2)) F := by
  obtain ⟨I, hI, hcov⟩ := exists_interval_cover_avoiding hQ hU hQU hF
  set K := ⋃ ab ∈ I, Icc ab.1 ab.2 with hK
  have hIooK : ∀ ab ∈ I, Ioo ab.1 ab.2 ⊆ interior K := fun ab hab =>
    interior_maximal ((Ioo_subset_Icc_self).trans (subset_biUnion_of_mem (u := fun ab : ℝ × ℝ =>
      Icc ab.1 ab.2) hab)) isOpen_Ioo
  refine ⟨I, fun ab hab => (hI ab hab).1, I.isCompact_biUnion fun _ _ => isCompact_Icc,
    iUnion₂_subset fun ab hab => (hI ab hab).2.1, fun x hx => ?_, ?_⟩
  · obtain ⟨ab, hab, hxab⟩ := mem_iUnion₂.mp (hcov hx)
    exact hIooK ab hab hxab
  · rw [Set.disjoint_left]
    intro x hx hxF
    have hclosed : IsClosed K := isClosed_biUnion_finset fun _ _ => isClosed_Icc
    have hxK : x ∈ K := hclosed.closure_subset hx.1
    obtain ⟨ab, hab, hxab⟩ := mem_iUnion₂.mp hxK
    rcases eq_or_lt_of_le hxab.1 with h1 | h1
    · exact (hI ab hab).2.2.1 (h1 ▸ hxF)
    rcases eq_or_lt_of_le hxab.2 with h2 | h2
    · exact (hI ab hab).2.2.2 (h2 ▸ hxF)
    exact hx.2 (hIooK ab hab ⟨h1, h2⟩)

variable {M : Type*} [TopologicalSpace M]

/-- Relative removal: `A ⊆ S ∪ (A \ int_A S)` (gives `M₁ ⊆ S ∪ M₂` and `M₂ ⊆ P ∪ R`). -/
theorem subset_union_diff_relInterior (A S : Set M) :
    A ⊆ S ∪ (A \ (Subtype.val '' interior ((Subtype.val : A → M) ⁻¹' S))) := by
  intro x hx
  by_cases hxS : x ∈ S
  · exact Or.inl hxS
  · refine Or.inr ⟨hx, ?_⟩
    rintro ⟨y, hy, rfl⟩
    have hyS : y ∈ (Subtype.val : A → M) ⁻¹' S := interior_subset hy
    exact hxS hyS

/-- (BCF01.b), first identity: `M = Z ∪ C ∪ S ∪ M₂` with `M₁ = M \ int(Z ∪ C)` and
`M₂ = M₁ \ int_{M₁} S`. -/
theorem union_union_union_eq_univ (Z C S : Set M) :
    Z ∪ C ∪ S ∪ ((interior (Z ∪ C))ᶜ \
      (Subtype.val '' interior ((Subtype.val : ↥((interior (Z ∪ C))ᶜ) → M) ⁻¹' S))) = univ := by
  refine eq_univ_of_forall fun x => ?_
  by_cases hx : x ∈ interior (Z ∪ C)
  · exact Or.inl (Or.inl (interior_subset hx))
  · rcases subset_union_diff_relInterior (interior (Z ∪ C))ᶜ S hx with h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inr h

/-- BCF03's last step: a component `Y ⊆ P ∪ R` with no point in `P` lies in `R`. -/
theorem subset_of_inter_eq_empty {N : Type*} {Y P R : Set N} (hY : Y ⊆ P ∪ R) (hYP : Y ∩ P = ∅) : Y ⊆ R := by
  intro y hy
  rcases hY hy with h | h
  · have hyP : y ∈ Y ∩ P := ⟨hy, h⟩
    rw [hYP] at hyP
    exact hyP.elim
  · exact h

variable {X : Type*} [PseudoMetricSpace X]

/-- BCF02: `d(q,p) < 5ΔR`, `R < 2ρ(q)` and the uniform buffer `10Δρ(q) < d(q,∂M)/3` give
`d(p,∂M) > (2/3) d(q,∂M)`. -/
theorem two_thirds_mul_infDist_lt (A : Set X) {p q : X} {Δ R ρq : ℝ} (hΔ : 0 ≤ Δ)
    (hqp : dist q p < 5 * Δ * R) (hR : R < 2 * ρq) (hbuf : 10 * Δ * ρq < infDist q A / 3) :
    2 / 3 * infDist q A < infDist p A := by
  have htri := infDist_le_infDist_add_dist (x := q) (y := p) (s := A)
  have h1 : 5 * Δ * R ≤ 5 * Δ * (2 * ρq) := mul_le_mul_of_nonneg_left hR.le (by positivity)
  linarith

/-- BCF02: with `d(q,∂M) ≥ 35` the replacement witness has `d(p,∂M) > 70/3 > 20`. -/
theorem twenty_lt_infDist (A : Set X) {p q : X} {Δ R ρq : ℝ} (hΔ : 0 ≤ Δ)
    (hqp : dist q p < 5 * Δ * R) (hR : R < 2 * ρq) (hbuf : 10 * Δ * ρq < infDist q A / 3)
    (hq : 35 ≤ infDist q A) : 20 < infDist p A := by
  have := two_thirds_mul_infDist_lt A hΔ hqp hR hbuf
  linarith

end DifferentialGeometry.Geometry.Collapse.BoundaryCloud
