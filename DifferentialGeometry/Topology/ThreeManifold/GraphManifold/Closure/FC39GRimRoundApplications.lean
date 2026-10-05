import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GRimRound
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0AdaptedV2

/-!
# FC39 GROUP G, RIMBOX G7: the rounding on the certificate objects (consumer and binding helpers)

Lane FC39-RIMBOX-ROUND, D62-4. Applications of the kernel `exists_rounding_relative_normalizedCorners_GRND`
and the remaining rounding facts that G8 needs:

* `CircleBundle.isOpenMap_proj_GRND`, `CircleBundle.secondCountableTopology_base_GRND`,
  `CircleBundle.sigmaCompactSpace_opens_GRND` — the base of a circle bundle is second countable (open
  quotient of the domain), so every open `O` of it — the final `circ.Base` — is σ-compact, as the
  kernel needs;
* `CircleRegion.exists_rounding_of_largerCorners_GRND` — the kernel on the fields of an actual circle
  region whose corner charts extend to `rimBox 3` (consumer): the five rounding fields in the verbatim
  certificate shapes;
* `CircleRegion.symmDiff_rounded_subset_GRND` — for every circle region the symmetric difference of
  `{rounding ≤ 0}` and the cornered base lies in the unit-box images (from `rounding_agree`);
* `LabelledCornerCompatibilityV2.rounding_in_safe_GRND` — the field `rounding_in_safe` of
  `AdaptedEdgeRimDataV2` from `rim_closure_in_safe` (`target_full`, `handleCorner_bijective`; review 62
  §5.3);
* rim pullbacks `CircleRegion.cornerChart_mem_cornerBase_iff_GRND`,
  `RimChartLayer.rimChart_mem_region_iff_GRND` (= the certificate field `rim_region`) and
  `RimChartLayer.rimChart_mem_rounded_iff_GRND` (the rounded region reads `{ψ_std ≥ 0}`).
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

/-! ## The base of a circle bundle is second countable -/

/-- The projection of a circle bundle is an open map (it is `fst` in every trivialization). -/
theorem CircleBundle.isOpenMap_proj_GRND (R : CircleBundle W) : IsOpenMap R.proj := by
  intro V hV
  rw [isOpen_iff_forall_mem_open]
  rintro _ ⟨x, hxV, rfl⟩
  let τ := (R.trivialization (R.proj x)).toHomeomorph
  let V' : Set (TopologicalSpace.Opens.comap R.proj (R.neighborhood (R.proj x))) :=
    Subtype.val ⁻¹' V
  have hV' : IsOpen V' := hV.preimage continuous_subtype_val
  have hfst : IsOpen (Prod.fst '' (τ '' V')) := isOpenMap_fst _ (τ.isOpenMap V' hV')
  have hxS : x ∈ TopologicalSpace.Opens.comap R.proj (R.neighborhood (R.proj x)) :=
    R.mem_neighborhood (R.proj x)
  refine ⟨Subtype.val '' (Prod.fst '' (τ '' V')), ?_,
    (R.neighborhood (R.proj x)).isOpen.isOpenMap_subtype_val _ hfst, ?_⟩
  · rintro _ ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
    exact ⟨y.val, hy, (R.projection_trivialization (R.proj x) y).symm⟩
  · exact ⟨(τ ⟨x, hxS⟩).1, ⟨τ ⟨x, hxS⟩, ⟨⟨x, hxS⟩, hxV, rfl⟩, rfl⟩,
      R.projection_trivialization (R.proj x) ⟨x, hxS⟩⟩

/-- **The base of a circle bundle is second countable**: an open quotient of the (second countable)
domain. -/
theorem CircleBundle.secondCountableTopology_base_GRND (R : CircleBundle W) :
    SecondCountableTopology R.Base :=
  _root_.Topology.IsOpenQuotientMap.secondCountableTopology
    ⟨R.proj_surjective_GGFF, R.proj.continuous, R.isOpenMap_proj_GRND⟩

/-- **Every open subset of the base of a circle bundle is σ-compact** (the final `circ.Base`). -/
theorem CircleBundle.sigmaCompactSpace_opens_GRND (R : CircleBundle W)
    (O : TopologicalSpace.Opens R.Base) : SigmaCompactSpace O := by
  have := R.secondCountableTopology_base_GRND
  have : LocallyCompactSpace O :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 2)) O
  infer_instance

/-! ## The kernel on an actual circle region (consumer) -/

/-- **Consumer of the kernel.** For a circle region whose corner charts are the restrictions of
larger charts `K k` on `rimBox 3` (disjoint targets, the corner equations on the whole larger box), on a
σ-compact base, there is a rounding function with the five rounding fields of `CircleRegion` in their
verbatim shapes. -/
theorem _root_.GC.GraphManifold.Assembly.CircleRegion.exists_rounding_of_largerCorners_GRND (circ : CircleRegion W)
    [SigmaCompactSpace circ.Base]
    (K : Fin circ.cornerCount → PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) (𝓡 2) (ℝ × ℝ) circ.Base ∞)
    (hK : ∀ k, (K k).source = rimBox 3)
    (hκK : ∀ k v, v ∈ rimBox 2 → circ.cornerChart k v = K k v)
    (hKdisj : Pairwise fun k k' => Disjoint (K k).target (K k').target)
    (hfirst : ∀ k v, v ∈ rimBox 3 →
      circ.defining (circ.cornerFirst k) (K k v) = -(circ.cornerScale k * v.1))
    (hsecond : ∀ k v, v ∈ rimBox 3 →
      circ.defining (circ.cornerSecond k) (K k v) = -(circ.cornerScale k * v.2))
    (hother : ∀ k l v, l ≠ circ.cornerFirst k → l ≠ circ.cornerSecond k → v ∈ rimBox 3 →
      circ.defining l (K k v) < 0) :
    ∃ r : circ.Base → ℝ, ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ r ∧
      (∀ b, r b = 0 → mfderiv (𝓡 2) 𝓘(ℝ, ℝ) r b ≠ 0) ∧
      (∀ k v, v ∈ rimBox 2 →
        r (circ.cornerChart k v) = -(circ.cornerScale k * standardRimRounding v)) ∧
      {b | r b ≤ 0} \ (⋃ k, circ.cornerChart k '' rimBox 1) =
        circ.cornerBase \ ⋃ k, circ.cornerChart k '' rimBox 1 ∧
      IsCompact {b | r b ≤ 0} ∧
      symmDiff {b | r b ≤ 0} circ.cornerBase ⊆ ⋃ k, circ.cornerChart k '' rimBox 1 :=
  exists_rounding_relative_normalizedCorners_GRND circ.defining circ.defining_smooth
    circ.defining_regular circ.cornerBase_eq circ.cornerBase_compact circ.cornerChart K hK hκK
    hKdisj circ.cornerFirst circ.cornerSecond circ.cornerScale circ.cornerScale_pos hfirst hsecond
    hother circ.corner_center

/-! ## The symmetric difference and `rounding_in_safe` -/

/-- For every circle region, `{rounding ≤ 0}` and the cornered base differ only inside the
unit-box images (`rounding_agree`). -/
theorem _root_.GC.GraphManifold.Assembly.CircleRegion.symmDiff_rounded_subset_GRND (circ : CircleRegion W) :
    symmDiff {c | circ.rounding c ≤ 0} circ.cornerBase ⊆ ⋃ k, circ.cornerChart k '' rimBox 1 := by
  intro c hc
  by_contra hn
  have hiff : c ∈ {c | circ.rounding c ≤ 0} \ ⋃ k, circ.cornerChart k '' rimBox 1 ↔
      c ∈ circ.cornerBase \ ⋃ k, circ.cornerChart k '' rimBox 1 := by
    rw [circ.rounding_agree]
  rcases mem_symmDiff.1 hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact h2 (hiff.1 ⟨h1, hn⟩).1
  · exact h2 (hiff.2 ⟨h1, hn⟩).1

/-- **`rounding_in_safe` (D62-4, review 62 §5.3).** The symmetric difference lies in the unit-box
images, whose full circle preimages lie in the rim-chart targets (`target_full`; every corner is a
rim by `handleCorner_bijective`), whose closures lie in the safe corner tubes. -/
theorem LabelledCornerCompatibilityV2.rounding_in_safe_GRND {Pr : FC39PreparedV2 W E}
    {H : EdgeLayer W} {circ : CircleRegion W} {K : RimChartLayer W H circ}
    (L : LabelledCornerCompatibilityV2 Pr H circ K) {safe : ProducerSafeNeighbourhoods Pr.rows}
    (hsafe : ∀ h b, closure (K.rimChart h b).target ⊆ safe.corner (L.edgeLink.endOfHandle h b)) :
    Subtype.val '' (circ.proj ⁻¹' symmDiff {c | circ.rounding c ≤ 0} circ.cornerBase) ⊆
      ⋃ e, safe.corner e := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨k, v, hv, hkv⟩ := mem_iUnion.1 (circ.symmDiff_rounded_subset_GRND hx)
  obtain ⟨⟨h, b⟩, hhb⟩ := K.handleCorner_bijective.2 k
  have hhb' : K.handleCorner h b = k := hhb
  have hvs : v ∈ (circ.cornerChart k).source := by
    rw [circ.cornerChart_source k]
    exact rimBox_mono (by norm_num) hv
  have htarget : (x : W.Carrier) ∈ (K.rimChart h b).target := by
    rw [L.target_full h b]
    refine ⟨x, ?_, rfl⟩
    change circ.proj x ∈ (circ.cornerChart (K.handleCorner h b)).target
    rw [hhb', ← hkv]
    exact (circ.cornerChart k).toPartialEquiv.map_source hvs
  exact mem_iUnion.2 ⟨_, hsafe h b (subset_closure htarget)⟩

/-! ## Rim pullbacks -/

/-- In a corner chart the cornered base is the closed quadrant. -/
theorem _root_.GC.GraphManifold.Assembly.CircleRegion.cornerChart_mem_cornerBase_iff_GRND (circ : CircleRegion W)
    (k : Fin circ.cornerCount) {v : ℝ × ℝ} (hv : v ∈ rimBox 2) :
    circ.cornerChart k v ∈ circ.cornerBase ↔ (0 ≤ v.1 ∧ 0 ≤ v.2) := by
  rw [circ.cornerBase_eq, mem_ofPred_eq]
  have hl := circ.cornerScale_pos k
  constructor
  · intro h
    have h1 := h (circ.cornerFirst k)
    have h2 := h (circ.cornerSecond k)
    rw [circ.chart_first k v hv, neg_nonpos] at h1
    rw [circ.chart_second k v hv, neg_nonpos] at h2
    exact ⟨nonneg_of_mul_nonneg_right (by linarith) hl,
      nonneg_of_mul_nonneg_right (by linarith) hl⟩
  · rintro ⟨h1, h2⟩ l
    by_cases hl1 : l = circ.cornerFirst k
    · rw [hl1, circ.chart_first k v hv, neg_nonpos]
      exact mul_nonneg hl.le h1
    by_cases hl2 : l = circ.cornerSecond k
    · rw [hl2, circ.chart_second k v hv, neg_nonpos]
      exact mul_nonneg hl.le h2
    exact (circ.chart_other k l v hl1 hl2 hv).le

/-- **Rim pullback of the cornered region** (= the certificate field `rim_region`, derived from
`rim_proj` and the corner-chart fields). -/
theorem RimChartLayer.rimChart_mem_region_iff_GRND {H : EdgeLayer W} {circ : CircleRegion W}
    (K : RimChartLayer W H circ) (h : Fin H.handleCount) (b : Bool) {p : Circle × (ℝ × ℝ)}
    (hp : p ∈ (K.rimChart h b).source) :
    K.rimChart h b p ∈ circ.region ↔ (0 ≤ p.2.1 ∧ 0 ≤ p.2.2) := by
  obtain ⟨hx, hproj⟩ := K.rim_proj h b p hp
  have hv : p.2 ∈ rimBox 2 := (K.rim_source h b).1 hp
  rw [← circ.cornerChart_mem_cornerBase_iff_GRND (K.handleCorner h b) hv, ← hproj]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hy' : y = ⟨K.rimChart h b p, hx⟩ := Subtype.ext hyx
    rw [← hy']
    exact hy
  · intro hmem
    exact ⟨⟨K.rimChart h b p, hx⟩, hmem, rfl⟩

/-- **Rim pullback of the rounded region**: in a rim chart, the rounded region reads
`{0 ≤ ψ_std (x, y)}`. -/
theorem RimChartLayer.rimChart_mem_rounded_iff_GRND {H : EdgeLayer W} {circ : CircleRegion W}
    (K : RimChartLayer W H circ) (h : Fin H.handleCount) (b : Bool) {p : Circle × (ℝ × ℝ)}
    (hp : p ∈ (K.rimChart h b).source) :
    K.rimChart h b p ∈ circ.rounded ↔ 0 ≤ standardRimRounding p.2 := by
  obtain ⟨hx, hproj⟩ := K.rim_proj h b p hp
  have hv : p.2 ∈ rimBox 2 := (K.rim_source h b).1 hp
  have hr : circ.rounding (circ.proj ⟨K.rimChart h b p, hx⟩) =
      -(circ.cornerScale (K.handleCorner h b) * standardRimRounding p.2) := by
    rw [hproj]
    exact circ.rounding_chart _ _ hv
  have hiff : circ.rounding (circ.proj ⟨K.rimChart h b p, hx⟩) ≤ 0 ↔
      0 ≤ standardRimRounding p.2 := by
    rw [hr, neg_nonpos, mul_nonneg_iff_of_pos_left (circ.cornerScale_pos _)]
  rw [← hiff]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hy' : y = ⟨K.rimChart h b p, hx⟩ := Subtype.ext hyx
    rw [← hy']
    exact hy
  · intro hmem
    exact ⟨⟨K.rimChart h b p, hx⟩, hmem, rfl⟩

end GC.GraphManifold.Assembly.FC39P0
