import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.LoopCollarModelBasic

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff Topology
namespace GC.LongTime.CuspP1

open GC.Endpoint GC.GraphManifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.Geometry.Hyperbolic

universe u

variable {H : FiniteVolumeHyperbolicModel.{u}} (T : HyperbolicTruncation H) (q : Fin T.count)

theorem outer_pos_not_range_LTP1 {p : Torus × ℝ} (hp : 0 < p.2) :
    bcOuter_LTP1 T q p ∉ range T.inclusion := by
  rintro ⟨c, hc⟩
  have hmem : bcOuter_LTP1 T q p ∈ range T.inclusion ∩ range (T.cuspMap q) :=
    ⟨⟨c, hc⟩, ⟨_, rfl⟩⟩
  rw [T.intersection q] at hmem
  obtain ⟨x, hx⟩ := hmem
  have h := (T.cuspEmbedding q).isEmbedding.injective (hx.trans rfl : _ = bcOuter_LTP1 T q p)
  have h2 : (halfZero : EuclideanHalfSpace 1).val 0 = (hpt_LTP1 p.2).val 0 :=
    congrArg (fun z : Torus × EuclideanHalfSpace 1 => z.2.val 0) h
  have : (0 : ℝ) = max p.2 0 := h2
  rw [max_eq_left hp.le] at this
  exact hp.ne this

theorem bdy_not_interior_LTP1 (t : Torus) :
    T.boundary.torusMap q t ∉ (T.core.interior : Set T.core.Carrier) := by
  intro h
  have := T.boundary.boundary_zero q t
  exact (T.core.model.isInteriorPoint_iff_not_isBoundaryPoint _ |>.mp h) this

theorem collar_mem_interior_LTP1 {p : Torus × ℝ} (h1 : -1 < p.2) (h2 : p.2 < 0) :
    T.boundary.collar q (p.1, hpt_LTP1 (-p.2)) ∈ (T.core.interior : Set T.core.Carrier) := by
  by_contra hn
  have hb : T.boundary.collar q (p.1, hpt_LTP1 (-p.2)) ∈ T.core.model.boundary T.core.Carrier := by
    rw [← T.core.model.compl_interior]; exact hn
  rw [T.boundary_exhausted] at hb
  obtain ⟨_, ⟨j, rfl⟩, x, hx⟩ := hb
  have hsrc := collar_mem_source_LTP1 T q h1
  have hsrc' : (x, (halfZero : EuclideanHalfSpace 1)) ∈ (T.boundary.collar j).source := by
    rw [T.boundary.source_eq]; change (0 : ℝ) < 1; norm_num
  by_cases hjq : j = q
  · subst hjq
    have := (T.boundary.collar j).toOpenPartialHomeomorph.injOn hsrc' hsrc hx
    have h3 : (halfZero : EuclideanHalfSpace 1).val 0 = (hpt_LTP1 (-p.2)).val 0 :=
      congrArg (fun z : Torus × EuclideanHalfSpace 1 => z.2.val 0) this
    have : (0 : ℝ) = max (-p.2) 0 := h3
    rw [max_eq_left (by linarith)] at this
    linarith
  · have a1 : T.boundary.collar j (x, halfZero) ∈ (T.boundary.collar j).target :=
      (T.boundary.collar j).toOpenPartialHomeomorph.map_source hsrc'
    have a2 : T.boundary.collar q (p.1, hpt_LTP1 (-p.2)) ∈ (T.boundary.collar q).target :=
      (T.boundary.collar q).toOpenPartialHomeomorph.map_source hsrc
    exact Set.disjoint_left.mp (T.boundary.disjoint hjq) a1 (show T.boundary.torusMap j x ∈ (T.boundary.collar q).target by rw [hx]; exact a2)

theorem bcFun_injOn_LTP1 : InjOn (bcFun_LTP1 T q) bcSource_LTP1 := by
  have hinc := T.embedding.isEmbedding.injective
  have hcus := (T.cuspEmbedding q).isEmbedding.injective
  intro p hp p' hp' h
  by_cases h1 : p.2 ≤ 0 <;> by_cases h2 : p'.2 ≤ 0
  · rw [bcFun_of_nonpos_LTP1 T q h1, bcFun_of_nonpos_LTP1 T q h2] at h
    have h3 := (T.boundary.collar q).toOpenPartialHomeomorph.injOn
      (collar_mem_source_LTP1 T q hp.1) (collar_mem_source_LTP1 T q hp'.1) (hinc h)
    have h4 : max (-p.2) 0 = max (-p'.2) 0 :=
      congrArg (fun z : Torus × EuclideanHalfSpace 1 => z.2.val 0) h3
    rw [max_eq_left (by linarith), max_eq_left (by linarith)] at h4
    exact Prod.ext (Prod.mk.inj h3).1 (by linarith)
  · exfalso
    rw [bcFun_of_nonpos_LTP1 T q h1, bcFun_of_pos_LTP1 T q (not_le.1 h2)] at h
    exact outer_pos_not_range_LTP1 T q (not_le.1 h2) ⟨_, h⟩
  · exfalso
    rw [bcFun_of_nonpos_LTP1 T q h2, bcFun_of_pos_LTP1 T q (not_le.1 h1)] at h
    exact outer_pos_not_range_LTP1 T q (not_le.1 h1) ⟨_, h.symm⟩
  · rw [bcFun_of_pos_LTP1 T q (not_le.1 h1), bcFun_of_pos_LTP1 T q (not_le.1 h2)] at h
    have h3 := hcus h
    have h4 : max p.2 0 = max p'.2 0 :=
      congrArg (fun z : Torus × EuclideanHalfSpace 1 => z.2.val 0) h3
    rw [max_eq_left (not_le.1 h1).le, max_eq_left (not_le.1 h2).le] at h4
    exact Prod.ext (Prod.mk.inj h3).1 h4

/-- The two-sided collar of the `q`-th boundary torus of a hyperbolic truncation: the
inner collar of the core (`s ≤ 0`) glued with the cusp-side map `cuspMap q` (`s ≥ 0`). -/
def bicollar_LTP1 : OpenPartialHomeomorph (Torus × ℝ) H.Carrier :=
  ofInjOnTorusLine_LTP1 (bcFun_LTP1 T q) bcSource_LTP1 isOpen_bcSource_LTP1
    (continuousOn_bcFun_LTP1 T q) (bcFun_injOn_LTP1 T q)

theorem bicollar_source_LTP1 : (bicollar_LTP1 T q).source = {p | -1 < p.2 ∧ p.2 < 1} := rfl

theorem bicollar_apply_LTP1 (p : Torus × ℝ) : bicollar_LTP1 T q p = bcFun_LTP1 T q p := rfl

theorem bicollar_apply_of_nonpos_LTP1 (t : Torus) {s : ℝ} (hs : s ≤ 0) (hs' : 0 ≤ -s) :
    bicollar_LTP1 T q (t, s) = T.inclusion (T.boundary.collar q (t, halfPoint (-s) hs')) := by
  rw [bicollar_apply_LTP1, bcFun_of_nonpos_LTP1 T q hs]
  simp only [bcInner_LTP1, hpt_of_nonneg_LTP1 hs']

theorem bicollar_apply_of_nonneg_LTP1 (t : Torus) {s : ℝ} (hs : 0 ≤ s) :
    bicollar_LTP1 T q (t, s) = T.cuspMap q (t, halfPoint s hs) := by
  rw [bicollar_apply_LTP1, bcFun_of_nonneg_LTP1 T q hs]
  simp only [bcOuter_LTP1, hpt_of_nonneg_LTP1 hs]

theorem bicollar_zero_LTP1 (t : Torus) :
    bicollar_LTP1 T q (t, 0) = T.inclusion (T.boundary.torusMap q t) :=
  bcInner_zero_LTP1 T q t ▸ (bcFun_of_nonpos_LTP1 T q (le_refl _))

theorem bicollar_zero_eq_cusp_LTP1 (t : Torus) :
    bicollar_LTP1 T q (t, 0) = T.cuspMap q (t, halfZero) := by
  rw [bicollar_zero_LTP1, T.cusp_zero]

theorem bicollar_neg_mem_LTP1 {p : Torus × ℝ} (hp : p ∈ (bicollar_LTP1 T q).source)
    (hs : p.2 < 0) : bicollar_LTP1 T q p ∈ T.inclusion '' (T.core.interior : Set T.core.Carrier) := by
  rw [bicollar_apply_LTP1, bcFun_of_nonpos_LTP1 T q hs.le]
  exact ⟨_, collar_mem_interior_LTP1 T q hp.1 hs, rfl⟩

theorem bicollar_nonneg_not_mem_LTP1 {p : Torus × ℝ} (hs : 0 ≤ p.2) :
    bicollar_LTP1 T q p ∉ T.inclusion '' (T.core.interior : Set T.core.Carrier) := by
  rintro ⟨c, hc, h⟩
  rcases hs.lt_or_eq with hs | hs
  · rw [bicollar_apply_LTP1, bcFun_of_pos_LTP1 T q hs] at h
    exact outer_pos_not_range_LTP1 T q hs ⟨c, h⟩
  · obtain ⟨t, s⟩ := p
    have hs' : s = 0 := hs.symm
    subst hs'
    rw [bicollar_zero_LTP1] at h
    have := T.embedding.isEmbedding.injective h
    exact bdy_not_interior_LTP1 T q t (this ▸ hc)

theorem bicollar_range_inner_LTP1 {p : Torus × ℝ} (hs : p.2 ≤ 0) :
    bicollar_LTP1 T q p ∈ range T.inclusion := by
  rw [bicollar_apply_LTP1, bcFun_of_nonpos_LTP1 T q hs]; exact ⟨_, rfl⟩

theorem bicollar_disjoint_LTP1 {q q' : Fin T.count} (hq : q ≠ q') :
    Disjoint (bicollar_LTP1 T q).target (bicollar_LTP1 T q').target := by
  rw [Set.disjoint_left]
  intro y hy hy'
  rw [← (bicollar_LTP1 T q).image_source_eq_target] at hy
  rw [← (bicollar_LTP1 T q').image_source_eq_target] at hy'
  obtain ⟨p, hp, rfl⟩ := hy
  obtain ⟨p', hp', h⟩ := hy'
  simp only [bicollar_apply_LTP1] at h
  by_cases h1 : p.2 ≤ 0 <;> by_cases h2 : p'.2 ≤ 0
  · rw [bcFun_of_nonpos_LTP1 T q h1] at h
    rw [bcFun_of_nonpos_LTP1 T q' h2] at h
    have h3 := T.embedding.isEmbedding.injective h
    have a1 := (T.boundary.collar q).toOpenPartialHomeomorph.map_source (collar_mem_source_LTP1 T q hp.1)
    have a2 := (T.boundary.collar q').toOpenPartialHomeomorph.map_source (collar_mem_source_LTP1 T q' hp'.1)
    exact Set.disjoint_left.mp (T.boundary.disjoint hq) a1 (by simpa [bcInner_LTP1] using h3 ▸ a2)
  · rw [bcFun_of_pos_LTP1 T q' (not_le.1 h2), bcFun_of_nonpos_LTP1 T q h1] at h
    exact outer_pos_not_range_LTP1 T q' (not_le.1 h2) ⟨_, h.symm⟩
  · rw [bcFun_of_nonpos_LTP1 T q' h2, bcFun_of_pos_LTP1 T q (not_le.1 h1)] at h
    exact outer_pos_not_range_LTP1 T q (not_le.1 h1) ⟨_, h⟩
  · rw [bcFun_of_pos_LTP1 T q (not_le.1 h1), bcFun_of_pos_LTP1 T q' (not_le.1 h2)] at h
    exact Set.disjoint_left.mp (T.cusp_disjoint hq) ⟨_, rfl⟩ ⟨_, h⟩

end GC.LongTime.CuspP1
