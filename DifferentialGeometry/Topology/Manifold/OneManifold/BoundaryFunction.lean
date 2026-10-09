import DifferentialGeometry.Topology.Manifold.OneManifold.HalfChart

/-!
# A boundary function on a compact one-manifold with boundary

For a compact one-manifold `M` modelled on `EuclideanHalfSpace 1`, the boundary is finite
(`finite_boundary`), and `bdryFn : M → [0, 1]` is a continuous function vanishing exactly on the
boundary which, near each boundary point `p`, equals the chart coordinate of `chartAt p` divided
by a positive constant `bdryRadius p` (`bdryNbhd`, `bdryFn_eq_on_bdryNbhd`).
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

noncomputable section

namespace DifferentialGeometry.Topology.Manifold.OneManifold

variable {M : Type*} [TopologicalSpace M]

/-- The real coordinate of a chart of a one-manifold with boundary. -/
def chartCoord (e : OpenPartialHomeomorph M (EuclideanHalfSpace 1)) (x : M) : ℝ := (e x).val 0

theorem chartCoord_nonneg (e : OpenPartialHomeomorph M (EuclideanHalfSpace 1)) (x : M) :
    0 ≤ chartCoord e x := (e x).2

theorem halfPt_chartCoord (e : OpenPartialHomeomorph M (EuclideanHalfSpace 1)) (x : M) :
    halfPt (chartCoord e x) = e x := halfPt_coord (e x)

theorem chartCoord_symm_halfPt (e : OpenPartialHomeomorph M (EuclideanHalfSpace 1)) {t : ℝ}
    (ht : 0 ≤ t) (hte : halfPt t ∈ e.target) : chartCoord e (e.symm (halfPt t)) = t := by
  unfold chartCoord
  rw [e.right_inv hte, halfPt_val_zero_of_nonneg ht]

theorem continuousOn_chartCoord (e : OpenPartialHomeomorph M (EuclideanHalfSpace 1)) :
    ContinuousOn (chartCoord e) e.source :=
  continuous_coord.comp_continuousOn e.continuousOn

variable [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]

theorem chartCoord_self_of_boundary {p : M} (hp : p ∈ (𝓡∂ 1).boundary M) :
    chartCoord (chartAt (EuclideanHalfSpace 1) p) p = 0 :=
  (isBoundaryPoint_iff_coord_eq_zero (chart_mem_atlas _ p) (mem_chart_source _ p)).mp hp

theorem chartAt_self_of_boundary {p : M} (hp : p ∈ (𝓡∂ 1).boundary M) :
    chartAt (EuclideanHalfSpace 1) p p = halfPt 0 := by
  rw [← halfPt_chartCoord, chartCoord_self_of_boundary hp]

theorem eq_of_mem_boundary_of_mem_chartAt_source {p x : M} (hp : p ∈ (𝓡∂ 1).boundary M)
    (hx : x ∈ (𝓡∂ 1).boundary M) (hxs : x ∈ (chartAt (EuclideanHalfSpace 1) p).source) :
    x = p := by
  apply (chartAt (EuclideanHalfSpace 1) p).injOn hxs (mem_chart_source _ p)
  apply coord_injective
  change chartCoord _ x = chartCoord _ p
  rw [chartCoord_self_of_boundary hp]
  exact (isBoundaryPoint_iff_coord_eq_zero (chart_mem_atlas _ p) hxs).mp hx

theorem finite_boundary [CompactSpace M] : ((𝓡∂ 1).boundary M).Finite := by
  apply ((𝓡∂ 1).isClosed_boundary (n := ∞) (M := M) (by simp)).isCompact.finite
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro p hp
  refine ⟨(chartAt (EuclideanHalfSpace 1) p).source,
    (chartAt (EuclideanHalfSpace 1) p).open_source, ?_⟩
  ext x
  constructor
  · rintro ⟨hxs, hx⟩
    exact eq_of_mem_boundary_of_mem_chartAt_source hp hx hxs
  · rintro rfl
    exact ⟨mem_chart_source _ x, hp⟩

/-- The boundary points of `M`, as a type. -/
abbrev Bdry (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 1) M] :=
  ↥((𝓡∂ 1).boundary M)

instance [CompactSpace M] : Finite (Bdry M) := (finite_boundary (M := M)).to_subtype

theorem exists_bdryRadius (p : Bdry M) :
    ∃ r : ℝ, 0 < r ∧ ∀ t : ℝ, 0 ≤ t → t ≤ 2 * r →
      halfPt t ∈ (chartAt (EuclideanHalfSpace 1) p.1).target := by
  have h0 : halfPt 0 ∈ (chartAt (EuclideanHalfSpace 1) p.1).target := by
    rw [← chartAt_self_of_boundary p.2]
    exact (chartAt _ p.1).map_source (mem_chart_source _ p.1)
  have hopen := continuous_halfPt.isOpen_preimage _ (chartAt _ p.1).open_target
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen 0 h0
  refine ⟨ε / 4, by positivity, fun t ht0 ht => hball ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht0]
  linarith

/-- The collar radius at a boundary point. -/
def bdryRadius (p : Bdry M) : ℝ := (exists_bdryRadius p).choose

theorem bdryRadius_pos (p : Bdry M) : 0 < bdryRadius p := (exists_bdryRadius p).choose_spec.1

theorem halfPt_mem_target_of_le (p : Bdry M) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 2 * bdryRadius p) :
    halfPt t ∈ (chartAt (EuclideanHalfSpace 1) p.1).target :=
  (exists_bdryRadius p).choose_spec.2 t ht0 ht

/-- The closed collar `[0, r]` at a boundary point. -/
def bdryCollar (p : Bdry M) : Set M :=
  (chartAt (EuclideanHalfSpace 1) p.1).symm '' (halfPt '' Icc 0 (bdryRadius p))

theorem bdryCollar_subset_source (p : Bdry M) :
    bdryCollar p ⊆ (chartAt (EuclideanHalfSpace 1) p.1).source := by
  rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
  exact (chartAt _ p.1).map_target (halfPt_mem_target_of_le p ht.1
    (by linarith [ht.2, bdryRadius_pos p]))

theorem isClosed_bdryCollar [T2Space M] (p : Bdry M) : IsClosed (bdryCollar p) := by
  apply IsCompact.isClosed
  apply ((isCompact_Icc).image continuous_halfPt).image_of_continuousOn
  apply (chartAt (EuclideanHalfSpace 1) p.1).continuousOn_symm.mono
  rintro _ ⟨t, ht, rfl⟩
  exact halfPt_mem_target_of_le p ht.1 (by linarith [ht.2, bdryRadius_pos p])

theorem mem_bdryCollar_of_chartCoord_le (p : Bdry M) {x : M}
    (hx : x ∈ (chartAt (EuclideanHalfSpace 1) p.1).source)
    (hle : chartCoord (chartAt (EuclideanHalfSpace 1) p.1) x ≤ bdryRadius p) :
    x ∈ bdryCollar p :=
  ⟨halfPt (chartCoord _ x), ⟨_, ⟨chartCoord_nonneg _ x, hle⟩, rfl⟩, by
    rw [halfPt_chartCoord, (chartAt _ p.1).left_inv hx]⟩

open scoped Classical in
/-- The factor of `bdryFn` attached to one boundary point. -/
def bdryFactor (p : Bdry M) (x : M) : ℝ :=
  if x ∈ (chartAt (EuclideanHalfSpace 1) p.1).source then
    min (chartCoord (chartAt (EuclideanHalfSpace 1) p.1) x / bdryRadius p) 1
  else 1

theorem bdryFactor_nonneg (p : Bdry M) (x : M) : 0 ≤ bdryFactor p x := by
  unfold bdryFactor
  split_ifs
  · exact le_min (div_nonneg (chartCoord_nonneg _ x) (bdryRadius_pos p).le) zero_le_one
  · exact zero_le_one

theorem bdryFactor_le_one (p : Bdry M) (x : M) : bdryFactor p x ≤ 1 := by
  unfold bdryFactor
  split_ifs
  · exact min_le_right _ _
  · exact le_rfl

theorem bdryFactor_eq_one_of_notMem (p : Bdry M) {x : M} (hx : x ∉ bdryCollar p) :
    bdryFactor p x = 1 := by
  unfold bdryFactor
  split_ifs with hs
  · apply min_eq_right
    rw [one_le_div (bdryRadius_pos p)]
    by_contra hlt
    exact hx (mem_bdryCollar_of_chartCoord_le p hs (not_le.mp hlt).le)
  · rfl

theorem continuous_bdryFactor [T2Space M] (p : Bdry M) : Continuous (bdryFactor p) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hs : x ∈ (chartAt (EuclideanHalfSpace 1) p.1).source
  · have hopen := (chartAt (EuclideanHalfSpace 1) p.1).open_source
    have hc : ContinuousAt (fun y => min (chartCoord (chartAt (EuclideanHalfSpace 1) p.1) y /
        bdryRadius p) 1) x :=
      (((continuousOn_chartCoord _).continuousAt (hopen.mem_nhds hs)).div_const _).min
        continuousAt_const
    apply hc.congr
    filter_upwards [hopen.mem_nhds hs] with y hy
    unfold bdryFactor
    simp only [hy, ↓reduceIte]
  · have hx : x ∉ bdryCollar p := fun h => hs (bdryCollar_subset_source p h)
    refine (continuousAt_const (y := (1 : ℝ))).congr ?_
    filter_upwards [(isClosed_bdryCollar p).isOpen_compl.mem_nhds hx] with y hy
    exact (bdryFactor_eq_one_of_notMem p hy).symm

theorem bdryFactor_eq_zero_iff {p : Bdry M} {x : M} :
    bdryFactor p x = 0 ↔ x = p.1 := by
  constructor
  · intro h
    unfold bdryFactor at h
    split_ifs at h with hs
    · have hpos := bdryRadius_pos p
      have hc : chartCoord (chartAt (EuclideanHalfSpace 1) p.1) x = 0 := by
        rcases min_choice (chartCoord (chartAt (EuclideanHalfSpace 1) p.1) x / bdryRadius p) 1
          with h' | h'
        · rw [h', div_eq_zero_iff] at h
          exact h.resolve_right hpos.ne'
        · rw [h'] at h
          exact absurd h one_ne_zero
      exact eq_of_mem_boundary_of_mem_chartAt_source p.2
        ((isBoundaryPoint_iff_coord_eq_zero (chart_mem_atlas _ p.1) hs).mpr hc) hs
    · exact absurd h one_ne_zero
  · rintro rfl
    unfold bdryFactor
    simp only [mem_chart_source, ↓reduceIte]
    rw [chartCoord_self_of_boundary p.2, zero_div, min_eq_left zero_le_one]

open scoped Classical in
/-- A continuous function `M → [0, 1]` vanishing exactly on the boundary. -/
def bdryFn [CompactSpace M] (x : M) : ℝ :=
  @Finset.prod _ _ _ (@Finset.univ _ (Fintype.ofFinite (Bdry M))) fun p => bdryFactor p x

variable [CompactSpace M]

theorem bdryFn_nonneg (x : M) : 0 ≤ bdryFn x := by
  unfold bdryFn
  exact Finset.prod_nonneg fun p _ => bdryFactor_nonneg p x

theorem bdryFn_le_one (x : M) : bdryFn x ≤ 1 := by
  unfold bdryFn
  exact Finset.prod_le_one₀ (fun p _ => bdryFactor_nonneg p x) fun p _ => bdryFactor_le_one p x

theorem continuous_bdryFn [T2Space M] : Continuous (bdryFn (M := M)) := by
  unfold bdryFn
  exact continuous_finsetProd _ fun p _ => continuous_bdryFactor p

theorem bdryFn_eq_zero_iff {x : M} : bdryFn x = 0 ↔ x ∈ (𝓡∂ 1).boundary M := by
  unfold bdryFn
  rw [Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨p, -, hp⟩
    rw [bdryFactor_eq_zero_iff.mp hp]
    exact p.2
  · intro hx
    exact ⟨⟨x, hx⟩, @Finset.mem_univ _ (Fintype.ofFinite _) _, bdryFactor_eq_zero_iff.mpr rfl⟩

theorem bdryFn_pos_iff {x : M} : 0 < bdryFn x ↔ x ∉ (𝓡∂ 1).boundary M := by
  rw [← bdryFn_eq_zero_iff, lt_iff_le_and_ne]
  exact ⟨fun h => fun h' => h.2 h'.symm, fun h => ⟨bdryFn_nonneg _, fun h' => h h'.symm⟩⟩

/-- An open neighbourhood of a boundary point on which `bdryFn` is the scaled chart
coordinate. -/
def bdryNbhd (p : Bdry M) : Set M :=
  ((chartAt (EuclideanHalfSpace 1) p.1).source ∩
      chartCoord (chartAt (EuclideanHalfSpace 1) p.1) ⁻¹' Iio (bdryRadius p)) ∩
    ⋂ q : Bdry M, ⋂ (_ : q ≠ p), (bdryCollar q)ᶜ

theorem isOpen_bdryNbhd [T2Space M] (p : Bdry M) : IsOpen (bdryNbhd p) :=
  ((continuousOn_chartCoord _).isOpen_inter_preimage (chartAt _ p.1).open_source isOpen_Iio).inter
    (isOpen_iInter_of_finite fun q => isOpen_iInter_of_finite fun _ =>
      (isClosed_bdryCollar q).isOpen_compl)

omit [CompactSpace M] in
theorem mem_bdryNbhd_self (p : Bdry M) : p.1 ∈ bdryNbhd p := by
  refine ⟨⟨mem_chart_source _ p.1, ?_⟩, ?_⟩
  · change chartCoord _ p.1 < bdryRadius p
    rw [chartCoord_self_of_boundary p.2]
    exact bdryRadius_pos p
  · rw [mem_iInter₂]
    intro q hq hmem
    exact hq (Subtype.ext (eq_of_mem_boundary_of_mem_chartAt_source q.2 p.2
      (bdryCollar_subset_source q hmem)).symm)

omit [CompactSpace M] in
theorem bdryNbhd_subset_source (p : Bdry M) :
    bdryNbhd p ⊆ (chartAt (EuclideanHalfSpace 1) p.1).source :=
  fun _ hx => hx.1.1

omit [CompactSpace M] in
theorem chartCoord_lt_of_mem_bdryNbhd (p : Bdry M) {x : M} (hx : x ∈ bdryNbhd p) :
    chartCoord (chartAt (EuclideanHalfSpace 1) p.1) x < bdryRadius p := hx.1.2

theorem bdryFn_eq_on_bdryNbhd (p : Bdry M) {x : M} (hx : x ∈ bdryNbhd p) :
    bdryFn x = chartCoord (chartAt (EuclideanHalfSpace 1) p.1) x / bdryRadius p := by
  classical
  unfold bdryFn
  rw [@Finset.prod_eq_single _ _ _ (@Finset.univ _ (Fintype.ofFinite (Bdry M))) _ p]
  · unfold bdryFactor
    simp only [bdryNbhd_subset_source p hx, ↓reduceIte]
    rw [min_eq_left]
    rw [div_le_one (bdryRadius_pos p)]
    exact (chartCoord_lt_of_mem_bdryNbhd p hx).le
  · intro q _ hq
    apply bdryFactor_eq_one_of_notMem
    have h := hx.2
    rw [mem_iInter₂] at h
    exact h q hq
  · intro h
    exact absurd (@Finset.mem_univ _ (Fintype.ofFinite (Bdry M)) p) h

end DifferentialGeometry.Topology.Manifold.OneManifold
