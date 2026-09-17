import DifferentialGeometry.Topology.Planar.VertexRoundingProfile
import DifferentialGeometry.Topology.Planar.PolygonVertexArcs
import DifferentialGeometry.Topology.Planar.CornerRounding
import DifferentialGeometry.Analysis.Calculus.RegularRegion
import Mathlib.Data.Finset.Lattice.Fold

open Set Metric Filter
open scoped Topology

namespace Schoenflies

open DifferentialGeometry.Analysis (roundedPolygonalCurve)

theorem PrePolygon.frontier_finite_vertex_rounding
    {m : ℕ} (P : PrePolygon m)
    (e : ZMod (m + 3) → Plane ≃ᵃ[ℝ] Plane)
    (U : ZMod (m + 3) → Set Plane) (r d s R : ZMod (m + 3) → ℝ)
    (hnorm : ∀ i, e i (P.vertex (i - 1)) = Plane.mk (-1) 0 ∧
      e i (P.vertex i) = 0 ∧ e i (P.vertex (i + 1)) = Plane.mk (r i) (d i * r i))
    (hr : ∀ i, 0 < r i) (hd : ∀ i, d i = 0 ∨ d i = 1)
    (hunit : ∀ i, d i = 1 → r i = 1) (hs : ∀ i, s i ≠ 0)
    (hU : ∀ i, IsOpen (U i)) (hdisj : Pairwise fun i j => Disjoint (U i) (U j))
    (hArc : ∀ i j, i ≠ j → Disjoint (U i) (P.vertexArc j))
    (hstrip : ∀ i, ∀ p ∈ U i, (e i p) 0 ∈ Icc (-(1 / 2 : ℝ)) (r i / 2))
    (hside : ∀ i, ∀ p ∈ U i, p ∈ closure (inside P.carrier) ↔
      0 ≤ s i * ((e i p) 1 - d i * max ((e i p) 0) 0))
    {h σ : ℝ} (hh : 0 < h) (hσ : 0 < σ) (hσh : σ < h / 2)
    (hR : ∀ i, 3 * (σ / h) < R i)
    (hKU : ∀ i, e i ⁻¹' closedBall (0 : Plane) (R i) ⊆ U i) :
    let D := closure (inside P.carrier)
    let D' := (D \ ⋃ i, e i ⁻¹' ball (0 : Plane) (R i)) ∪
      ⋃ i, (e i ⁻¹' closedBall (0 : Plane) (R i)) ∩
        {p | 0 ≤ s i * ((e i p) 1 - d i * Real.smoothMax (σ / h) ((e i p) 0) 0)}
    IsCompact D' ∧ range (roundedPolygonalCurve h σ (fun k : ℤ => P.vertex k)) =
      frontier D' := by
  let D := closure (inside P.carrier)
  let N := fun i => e i ⁻¹' ball (0 : Plane) (R i)
  let K := fun i => e i ⁻¹' closedBall (0 : Plane) (R i)
  let H := fun i p => s i * ((e i p) 1 - d i * Real.smoothMax (σ / h) ((e i p) 0) 0)
  let A := fun i => e i ⁻¹' {q : Plane | q 0 ∈ Icc (-(1 / 2 : ℝ)) (r i / 2) ∧
    q 1 = d i * Real.smoothMax (σ / h) (q 0) 0}
  let D' := (D \ ⋃ i, N i) ∪ ⋃ i, K i ∩ {p | 0 ≤ H i p}
  have hε : 0 < σ / h := div_pos hσ hh
  have hN (i) : IsOpen (N i) := isOpen_ball.preimage (e i).toAffineMap.continuous_of_finiteDimensional
  have hK (i) : IsCompact (K i) := by
    rw [show K i = (e i).symm '' closedBall (0 : Plane) (R i) from
      ((e i).toEquiv.image_symm_eq_preimage _).symm]
    exact (isCompact_closedBall _ _).image (e i).symm.toAffineMap.continuous_of_finiteDimensional
  have hNK (i) : N i ⊆ K i := preimage_mono ball_subset_closedBall
  have hH (i) := affine_smooth_corner_regular (e i) (σ / h) (d i) (s i) (hs i)
  have heq (i) (p) (hp : p ∈ U i \ N i) : (0 ≤ H i p) ↔ p ∈ D := by
    have hnormp : R i ≤ ‖e i p‖ := by
      have hn : ¬ ‖e i p‖ < R i := by
        simpa only [N, mem_preimage, mem_ball_zero_iff] using hp.2
      exact le_of_not_gt hn
    exact (smooth_corner_signs_eq_outside_ball (σ := s i) hε (hd i)
      ((hR i).trans_le hnormp)).1.trans (hside i p hp.1).symm
  obtain ⟨hD', hlocal, hout⟩ := Set.isCompact_finite_disjoint_replacement
    P.isSeparating_carrier.isBounded_inside.isCompact_closure hN hK
    (fun i => isClosed_le continuous_const (hH i).1.continuous) hNK hKU hdisj heq
  have hfront (i) (p) (hp : p ∈ U i) : p ∈ frontier D' ↔
      (e i p) 1 = d i * Real.smoothMax (σ / h) ((e i p) 0) 0 := by
    have hf := (DifferentialGeometry.Analysis.interior_frontier_iff_of_local_regular_superlevel
      hD'.isClosed (hU i) (hH i).1.continuous (fun p _ _ => (hH i).2 p)
      (hlocal i) p hp).2
    change (p ∈ frontier D' ↔ H i p = 0) at hf
    rw [hf]
    simp only [H, mul_eq_zero, hs i, false_or, sub_eq_zero]
  have hAout (i) (p) (hp : p ∉ K i) : p ∈ A i ↔ p ∈ P.vertexArc i := by
    have hpR : R i < ‖e i p‖ := by
      simpa only [K, mem_preimage, mem_closedBall_zero_iff, not_le] using hp
    have hgraph := (smooth_corner_signs_eq_outside_ball (σ := s i) hε (hd i)
      ((hR i).trans hpR)).2.2
    rw [← (e i).injective.mem_set_image (s := P.vertexArc i), P.affine_image_vertexArc i (e i) (hr i)
      (hnorm i).1 (hnorm i).2.1 (hnorm i).2.2]
    change (_ ∧ _) ↔ (_ ∧ _)
    exact and_congr Iff.rfl hgraph
  have hAin (i) (p) (hp : p ∈ U i) : p ∈ ⋃ j, A j ↔
      (e i p) 1 = d i * Real.smoothMax (σ / h) ((e i p) 0) 0 := by
    constructor
    · intro hpA
      obtain ⟨j, hpj⟩ := mem_iUnion.mp hpA
      by_cases hji : j = i
      · exact (hji ▸ hpj).2
      · have hnotK : p ∉ K j := fun h =>
          disjoint_left.mp (hdisj hji) (hKU j h) hp
        exact False.elim (disjoint_left.mp (hArc i j (Ne.symm hji)) hp
          ((hAout j p hnotK).mp hpj))
    · intro hpH
      exact mem_iUnion.mpr ⟨i, hstrip i p hp, hpH⟩
  have hAoutside (p) (hp : p ∉ ⋃ i, U i) : p ∈ ⋃ i, A i ↔ p ∈ P.carrier := by
    rw [← P.iUnion_vertexArc]
    simp only [mem_iUnion]
    apply exists_congr
    intro i
    exact hAout i p (fun h => hp (mem_iUnion.mpr ⟨i, hKU i h⟩))
  have hfD : frontier D = P.carrier := by
    calc
      frontier D = closure (inside P.carrier) \ inside P.carrier := by
        change frontier (closure (inside P.carrier)) = _
        rw [frontier, closure_closure,
          interior_closure_inside_of_separating P.isSeparating_carrier]
      _ = frontier (inside P.carrier) := by
        rw [frontier, P.isSeparating_carrier.isOpen_inside.interior_eq]
      _ = P.carrier := P.isSeparating_carrier.frontier_inside
  have hFout (p) (hp : p ∉ ⋃ i, U i) : p ∈ frontier D' ↔ p ∈ P.carrier := by
    have hpK : p ∉ ⋃ i, K i := fun h => by
      obtain ⟨i, hi⟩ := mem_iUnion.mp h
      exact hp (mem_iUnion.mpr ⟨i, hKU i hi⟩)
    have hsame : D' =ᶠ[𝓝 p] D := by
      filter_upwards [(isCompact_iUnion hK).isClosed.isOpen_compl.mem_nhds hpK] with q hq
      exact propext (hout q hq)
    rw [← hfD, hD'.isClosed.frontier_eq, isClosed_closure.frontier_eq]
    change (p ∈ D' ∧ p ∉ interior D') ↔ (p ∈ D ∧ p ∉ interior D)
    exact and_congr (hout p hpK) (not_congr hsame.mem_interior_iff)
  refine ⟨hD', ?_⟩
  rw [range_roundedPolygonalCurve_eq_iUnion_graphs P.vertex e r d hnorm hr hd hunit hh hσ hσh]
  ext p
  by_cases hp : p ∈ ⋃ i, U i
  · obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    exact (hAin i p hi).trans (hfront i p hi).symm
  · exact (hAoutside p hp).trans (hFout p hp).symm

open LeanEval.Topology.ClassificationOfSurfaces.Moise in
theorem PrePolygon.exists_finite_vertex_roundings_frontier
    {m : ℕ} (P : PrePolygon m) {h : ℝ} (hh : 0 < h) :
    ∃ (e : ZMod (m + 3) → Plane ≃ᵃ[ℝ] Plane)
      (U : ZMod (m + 3) → Set Plane) (r d s R : ZMod (m + 3) → ℝ) (δ : ℝ),
      (∀ i, 0 < r i ∧ e i (P.vertex (i - 1)) = Plane.mk (-1) 0 ∧
        e i (P.vertex (i + 1)) = Plane.mk (r i) (d i * r i) ∧ e i (P.vertex i) = 0) ∧
      (∀ i, IsOpen (U i) ∧ P.vertex i ∈ U i ∧ (d i = 0 ∨ d i = 1) ∧
        (s i = -1 ∨ s i = 1) ∧
        ∀ p ∈ U i, p ∈ closure (inside P.carrier) ↔
          0 ≤ s i * ((e i p) 1 - d i * max ((e i p) 0) 0)) ∧
      (Pairwise fun i j => Disjoint (U i) (U j)) ∧
      (∀ i, e i ⁻¹' closedBall (0 : Plane) (R i) ⊆ U i) ∧ 0 < δ ∧
      ∀ ε ∈ Ioo (0 : ℝ) δ,
        ε < 1 / 2 ∧ (∀ i, 3 * ε < R i) ∧
        let D := closure (inside P.carrier)
        let D' := (D \ ⋃ i, e i ⁻¹' ball (0 : Plane) (R i)) ∪
          ⋃ i, (e i ⁻¹' closedBall (0 : Plane) (R i)) ∩
            {p | 0 ≤ s i * ((e i p) 1 - d i * Real.smoothMax ε ((e i p) 0) 0)}
        IsCompact D' ∧
          range (roundedPolygonalCurve h (h * ε) (fun k : ℤ => P.vertex k)) = frontier D' := by
  classical
  choose e W r d s hW hcW hiW hr hd hs he0 hea heb hstraight hunit hside using
    P.exists_affine_vertex_graph_sides_normalized
  have hezero (i) : e i (P.vertex i) = 0 := by
    rw [he0 i]
    ext j
    fin_cases j <;> rfl
  let O := fun i => W i ∩ (e i) ⁻¹' {q : Plane | q 0 ∈ Ioo (-(1 / 2 : ℝ)) (r i / 2)}
  have hO (i) : IsOpen (O i) := by
    have hc : Continuous (fun p : Plane => (e i p) 0) :=
      (cartesianX.comp (e i).toAffineMap).continuous_of_finiteDimensional
    exact (hW i).inter (isOpen_Ioo.preimage hc)
  have hiO (i) : P.vertex i ∈ O i := by
    refine ⟨hiW i, ?_⟩
    change -(1 / 2 : ℝ) < (e i (P.vertex i)) 0 ∧ (e i (P.vertex i)) 0 < r i / 2
    rw [hezero i]
    exact ⟨by norm_num, half_pos (hr i)⟩
  obtain ⟨U, hU, hdisj, hArc⟩ := P.exists_disjoint_open_vertexArc_neighborhoods O hO hiO
  have hballs (i) : ∃ R > 0, e i ⁻¹' closedBall (0 : Plane) R ⊆ U i := by
    have hopen := (hU i).1.preimage (e i).symm.toAffineMap.continuous_of_finiteDimensional
    have hzero : (0 : Plane) ∈ (e i).symm ⁻¹' U i := by
      change (e i).symm 0 ∈ U i
      rw [← hezero i, (e i).symm_apply_apply]
      exact (hU i).2.1
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hopen 0 hzero
    refine ⟨ρ / 2, half_pos hρ, ?_⟩
    intro p hp
    have hnormp : ‖e i p‖ ≤ ρ / 2 := by
      simpa only [mem_preimage, mem_closedBall_zero_iff] using hp
    have hpball : e i p ∈ ball (0 : Plane) ρ :=
      mem_ball_zero_iff.mpr (hnormp.trans_lt (half_lt_self hρ))
    have hpU : (e i).symm (e i p) ∈ U i := hball hpball
    simpa only [AffineEquiv.symm_apply_apply] using hpU
  choose R hR hKU using hballs
  let δ := min (1 / 4 : ℝ) (Finset.univ.inf' Finset.univ_nonempty (fun i => R i / 6))
  have hδ : 0 < δ := lt_min (by norm_num)
    ((Finset.lt_inf'_iff _).mpr (fun i _ => div_pos (hR i) (by norm_num)))
  have hδR (i) : δ ≤ R i / 6 := (min_le_right _ _).trans
    (Finset.inf'_le _ (Finset.mem_univ i))
  refine ⟨e, U, r, d, s, R, δ, fun i => ⟨hr i, hea i, heb i, hezero i⟩,
    fun i => ⟨(hU i).1, (hU i).2.1, hd i, hs i,
      fun p hp => (hside i p ((hU i).2.2 hp).1).1⟩, hdisj, hKU, hδ, ?_⟩
  intro ε hε
  have hεhalf : ε < 1 / 2 := lt_of_lt_of_le (hε.2.trans_le (min_le_left _ _)) (by norm_num)
  have hεR (i) : 3 * ε < R i := by
    have ht := hε.2.trans_le (hδR i)
    nlinarith [hR i]
  refine ⟨hεhalf, hεR, ?_⟩
  have hratio : h * ε / h = ε := mul_div_cancel_left₀ ε hh.ne'
  have hf := P.frontier_finite_vertex_rounding e U r d s R
    (fun i => ⟨hea i, hezero i, heb i⟩) hr hd hunit
    (fun i => by rcases hs i with hi | hi <;> rw [hi] <;> norm_num)
    (fun i => (hU i).1) hdisj hArc
    (fun i p hp => ⟨((hU i).2.2 hp).2.1.le, ((hU i).2.2 hp).2.2.le⟩)
    (fun i p hp => (hside i p ((hU i).2.2 hp).1).1)
    hh (mul_pos hh hε.1) (by nlinarith)
    (fun i => by simpa only [hratio] using hεR i) hKU
  simpa only [hratio] using hf

end Schoenflies
