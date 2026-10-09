import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GRimCircleRegion

/-!
# FC39 GROUP G, RIMBOX G8a: consumer and the rim-chart conversions for G8

Lane FC39-RIMBOX-ROUND. For any circle region with a restriction link `L` to the row circle bundle:

* `CircleRestrictionLink.proj_eq_of_rowProj_GRND` — a point of the row domain whose row projection is
  `L.ι c` lies in the region's domain and projects to `c`;
* `CircleRestrictionLink.rim_proj_of_rowProj_GRND` — the `rim_proj` field of `RimChartLayer` from the
  row form `R.proj ∘ χ = κ ∘ snd` of a rim chart and the corner identification
  `L.ι (cornerChart k v) = κ v` (the shape of G6's output and of G8a's second clause);
* `CircleRestrictionLink.target_full_of_tube_GRND` — the `target_full` field of
  `LabelledCornerCompatibilityV2` from the row form `χ.target = R.tube (κ '' rimBox 2)` and G8a's third
  clause.

Consumer: `FC39PreparedV2.exists_circleRegion_safe_GRND` — the G8a circle region keeps the row circle
region, its rounding changes the cornered base only inside the unit corner boxes, and every corner
chart target lies over the safe corner base of its endpoint.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}

/-- A point of the row domain over `L.ι c` lies in the region's domain and projects to `c`. -/
theorem CircleRestrictionLink.proj_eq_of_rowProj_GRND {R : CircleBundle W} {circ : CircleRegion W}
    (L : CircleRestrictionLink R circ) {x : W.Carrier} (hx : x ∈ R.domain) {c : circ.Base}
    (h : R.proj ⟨x, hx⟩ = L.ι c) : ∃ hx' : x ∈ circ.domain, circ.proj ⟨x, hx'⟩ = c := by
  have hx' : x ∈ (circ.domain : Set W.Carrier) := by
    rw [L.domain_eq]
    exact ⟨⟨x, hx⟩, ⟨c, h.symm⟩, rfl⟩
  refine ⟨hx', L.ι_isOpenEmbedding.injective ?_⟩
  obtain ⟨hx'', h''⟩ := L.proj_eq ⟨x, hx'⟩
  rw [← h'', ← h]

/-- **`rim_proj` from the row form** of a rim chart over a corner chart. -/
theorem CircleRestrictionLink.rim_proj_of_rowProj_GRND {R : CircleBundle W}
    {circ : CircleRegion W} (L : CircleRestrictionLink R circ) {k : Fin circ.cornerCount}
    {κ : PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) (𝓡 2) (ℝ × ℝ) R.Base ∞}
    (hκ : ∀ v, v ∈ rimBox 2 → L.ι (circ.cornerChart k v) = κ v)
    {χ : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) W.model (Circle × (ℝ × ℝ)) W.Carrier ∞}
    (hsrc : ∀ p, p ∈ χ.source ↔ p.2 ∈ rimBox 2)
    (hproj : ∀ p ∈ χ.source, ∃ hx : χ p ∈ R.domain, R.proj ⟨χ p, hx⟩ = κ p.2) :
    ∀ p, p ∈ χ.source → ∃ hx : χ p ∈ circ.domain, circ.proj ⟨χ p, hx⟩ = circ.cornerChart k p.2 := by
  intro p hp
  obtain ⟨hx, hpr⟩ := hproj p hp
  exact L.proj_eq_of_rowProj_GRND hx (hpr.trans (hκ p.2 ((hsrc p).1 hp)).symm)

/-- **`target_full` from the row form** `χ.target = R.tube (κ '' rimBox 2)`. -/
theorem CircleRestrictionLink.target_full_of_tube_GRND {R : CircleBundle W}
    {circ : CircleRegion W} (L : CircleRestrictionLink R circ) {k : Fin circ.cornerCount}
    {κ : PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) (𝓡 2) (ℝ × ℝ) R.Base ∞}
    (hκ : ∀ v, v ∈ rimBox 2 → L.ι (circ.cornerChart k v) = κ v)
    (htarget : ∀ c, c ∈ (circ.cornerChart k).target ↔ L.ι c ∈ κ '' rimBox 2)
    {T : Set W.Carrier} (hT : T = R.tube (κ '' rimBox 2)) :
    T = Subtype.val '' (circ.proj ⁻¹' (circ.cornerChart k).target) := by
  rw [hT]
  ext x
  constructor
  · rintro ⟨y, ⟨v, hv, hyv⟩, rfl⟩
    obtain ⟨hx', hpr⟩ := L.proj_eq_of_rowProj_GRND y.2 (hyv.symm.trans (hκ v hv).symm)
    refine ⟨⟨y, hx'⟩, ?_, rfl⟩
    change circ.proj ⟨y, hx'⟩ ∈ (circ.cornerChart k).target
    rw [hpr, htarget, hκ v hv]
    exact ⟨v, hv, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨hz', hpr⟩ := L.proj_eq z
    refine ⟨⟨z, hz'⟩, ?_, rfl⟩
    change R.proj ⟨z, hz'⟩ ∈ κ '' rimBox 2
    rw [hpr]
    exact (htarget _).1 hz

/-- **Consumer of G8a.** The circle region of `exists_circleRegion_of_cornerCharts_GRND` keeps the
row circle region, its rounding changes the cornered base only inside the unit corner boxes, and every
corner chart target lies over the safe corner base of its endpoint. -/
theorem FC39PreparedV2.exists_circleRegion_safe_GRND (Pr : FC39PreparedV2 W E)
    (safe : ProducerSafeNeighbourhoods Pr.rows) (lam : Pr.rows.edge.EdgeEnd → ℝ)
    (κ : Pr.rows.edge.EdgeEnd → PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) (𝓡 2) (ℝ × ℝ) Pr.rows.circle.Base ∞)
    (hlam : ∀ e, 0 < lam e) (hsrc : ∀ e, (κ e).source = rimBox 3)
    (hcenter : ∀ e, κ e (0, 0) = Pr.rows.junctions.rimBase e.1)
    (htgt : ∀ e, (κ e).target ⊆ (safe.cornerBase e : Set _) ∩
      (Pr.globalFaces.base : Set Pr.rows.circle.Base))
    (hfirst : ∀ e, ∀ v ∈ rimBox 3,
      Pr.globalFaces.fn (Pr.globalFaces.actualFace.symm (.vertical e.component)) (κ e v) =
        -(lam e * v.1))
    (hsecond : ∀ e, ∀ v ∈ rimBox 3,
      Pr.globalFaces.fn (Pr.globalFaces.actualFace.symm
        (.horizontal (Pr.rows.junctions.horizontal e))) (κ e v) = -(lam e * v.2))
    (hother : ∀ e f v, f ≠ Pr.globalFaces.actualFace.symm (.vertical e.component) →
      f ≠ Pr.globalFaces.actualFace.symm (.horizontal (Pr.rows.junctions.horizontal e)) →
      v ∈ rimBox 3 → Pr.globalFaces.fn f (κ e v) < 0) :
    ∃ (circ : CircleRegion W) (L : CircleRestrictionLink Pr.rows.circle circ)
      (endOfCorner : Fin circ.cornerCount ≃ Pr.rows.edge.EdgeEnd),
      circ.region = Pr.rows.circle.region ∧
      symmDiff {c | circ.rounding c ≤ 0} circ.cornerBase ⊆
        ⋃ k, circ.cornerChart k '' rimBox 1 ∧
      ∀ k, L.ι '' (circ.cornerChart k).target ⊆ safe.cornerBase (endOfCorner k) := by
  obtain ⟨circ, L, -, eoc, -, -, htarget, -, -, -⟩ :=
    Pr.exists_circleRegion_of_cornerCharts_GRND safe lam κ hlam hsrc hcenter htgt hfirst hsecond
      hother
  refine ⟨circ, L, eoc, L.region_eq, circ.symmDiff_rounded_subset_GRND, fun k => ?_⟩
  rintro _ ⟨c, hc, rfl⟩
  obtain ⟨v, hv, hvc⟩ := (htarget k c).1 hc
  rw [← hvc]
  refine (htgt (eoc k) ((κ (eoc k)).toPartialEquiv.map_source ?_)).1
  rw [hsrc]
  exact rimBox_mono (by norm_num) hv

end GC.GraphManifold.Assembly.FC39P0
