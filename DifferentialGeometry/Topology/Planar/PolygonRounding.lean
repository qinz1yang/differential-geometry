import DifferentialGeometry.Topology.Planar.VertexReplacement
import Mathlib.LinearAlgebra.Ray
import DifferentialGeometry.Analysis.Calculus.RegularRegion
import DifferentialGeometry.Topology.Planar.VertexRoundingProfile
import DifferentialGeometry.Topology.Compactness.FiniteReplacement
import DifferentialGeometry.Topology.Planar.CornerRounding
import DifferentialGeometry.Topology.Planar.PolygonIsotopy
import Mathlib.Geometry.Manifold.Diffeomorph
import DifferentialGeometry.External.ClassificationOfSurfaces.PrePolygonDeletion
import Mathlib.Topology.MetricSpace.Thickening
import DifferentialGeometry.Analysis.Calculus.SmoothMax
import DifferentialGeometry.External.Schoenflies.Plane
import DifferentialGeometry.External.ClassificationOfSurfaces.Moise.LineSubdivision
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.NhdsWithin
import Mathlib.Tactic.Linarith
import DifferentialGeometry.External.Schoenflies.PrePolygonSep
import DifferentialGeometry.External.Schoenflies.PrePolygonArc
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff
import DifferentialGeometry.Topology.Planar.PolygonVertexCharts

section
open Set Metric
open scoped ContDiff Topology

namespace Schoenflies

open LeanEval.Topology.ClassificationOfSurfaces.Moise

private theorem compact_region_replace_on_open
    {X : Type*} [TopologicalSpace X]
    {D N K R : Set X} (hD : IsCompact D) (hN : IsOpen N)
    (hK : IsCompact K) (hR : IsClosed R) (hNK : N ⊆ K)
    (heq : ∀ p ∈ K \ N, p ∈ R ↔ p ∈ D) :
    IsCompact ((D \ N) ∪ (K ∩ R)) ∧
      (∀ p ∈ N, p ∈ (D \ N) ∪ (K ∩ R) ↔ p ∈ R) ∧
      (∀ p ∉ N, p ∈ (D \ N) ∪ (K ∩ R) ↔ p ∈ D) := by
  refine ⟨(hD.diff hN).union (hK.inter_right hR), ?_, ?_⟩
  · intro p hp
    constructor
    · rintro (⟨_, hn⟩ | ⟨_, hr⟩)
      · exact False.elim (hn hp)
      · exact hr
    · intro hr
      exact Or.inr ⟨hNK hp, hr⟩
  · intro p hp
    constructor
    · rintro (⟨hd, _⟩ | ⟨hk, hr⟩)
      · exact hd
      · exact (heq p ⟨hk, hp⟩).mp hr
    · intro hd
      exact Or.inl ⟨hd, hp⟩

private theorem affine_preimage_isCompact (e : Plane ≃ᵃ[ℝ] Plane)
    {K : Set Plane} (hK : IsCompact K) : IsCompact (e ⁻¹' K) := by
  let h : Plane ≃ₜ Plane :=
    { e.toEquiv with
      continuous_toFun := e.toAffineMap.continuous_of_finiteDimensional
      continuous_invFun := e.symm.toAffineMap.continuous_of_finiteDimensional }
  exact h.isCompact_preimage.mpr hK

private theorem regular_region_replace_on_open
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {D N K : Set E} {H : E → ℝ} (hD : IsCompact D) (hN : IsOpen N)
    (hK : IsCompact K) (hNK : N ⊆ K) (hH : Continuous H)
    (hreg : ∀ p ∈ N, H p = 0 → fderiv ℝ H p ≠ 0)
    (heq : ∀ p ∈ K \ N, 0 ≤ H p ↔ p ∈ D) :
    let D' := (D \ N) ∪ (K ∩ {p | 0 ≤ H p})
    IsCompact D' ∧
      (∀ p ∈ N, (p ∈ D' ↔ 0 ≤ H p) ∧
        (p ∈ interior D' ↔ 0 < H p) ∧ (p ∈ frontier D' ↔ H p = 0)) ∧
      (∀ p ∉ N, p ∈ D' ↔ p ∈ D) := by
  obtain ⟨hD', hlocal, hout⟩ := compact_region_replace_on_open hD hN hK
    (isClosed_le continuous_const hH) hNK heq
  have hsides := DifferentialGeometry.Analysis.interior_frontier_iff_of_local_regular_superlevel
    hD'.isClosed hN hH hreg hlocal
  exact ⟨hD', fun p hp => ⟨hlocal p hp, hsides p hp⟩, hout⟩

private theorem region_replace_eq_self_of_local_eq
    {X : Type*} {D N K A : Set X} (hNK : N ⊆ K)
    (heq : ∀ p ∈ K, p ∈ A ↔ p ∈ D) :
    (D \ N) ∪ (K ∩ A) = D := by
  ext p
  constructor
  · rintro (⟨hp, _⟩ | ⟨hpK, hpA⟩)
    · exact hp
    · exact (heq p hpK).mp hpA
  · intro hp
    by_cases hpN : p ∈ N
    · exact Or.inr ⟨hNK hpN, (heq p (hNK hpN)).mpr hp⟩
    · exact Or.inl ⟨hp, hpN⟩

private theorem affine_smooth_corner_side_eq_outside_ball
    (e : Plane ≃ᵃ[ℝ] Plane) {ε R d σ : ℝ} (hε : 0 < ε)
    (hεR : 3 * ε < R) (hd : d = 0 ∨ d = 1)
    {p : Plane} (hp : p ∉ e ⁻¹' ball (0 : Plane) R) :
    (0 ≤ σ * ((e p) 1 - d * Real.smoothMax ε ((e p) 0) 0) ↔
      0 ≤ σ * ((e p) 1 - d * max ((e p) 0) 0)) := by
  have hpR : R ≤ ‖e p‖ := by
    have hn : ¬ ‖e p‖ < R := by
      simpa only [Set.mem_preimage, mem_ball_zero_iff] using hp
    exact le_of_not_gt hn
  exact (smooth_corner_signs_eq_outside_ball (σ := σ) hε hd (hεR.trans_le hpR)).1

end Schoenflies

end

section
open Set Metric
open scoped ContDiff Topology

namespace Schoenflies

private theorem exists_affine_closed_ball_subset
    {U : Set Plane} (hU : IsOpen U) (e : Plane ≃ᵃ[ℝ] Plane)
    {a : Plane} (ha : a ∈ U) (hea : e a = 0) :
    ∃ R : ℝ, 0 < R ∧ a ∈ e ⁻¹' ball (0 : Plane) R ∧
      e ⁻¹' closedBall (0 : Plane) R ⊆ U := by
  have hei : Continuous e.symm := e.symm.toAffineMap.continuous_of_finiteDimensional
  have hz : (0 : Plane) ∈ e.symm ⁻¹' U := by
    change e.symm 0 ∈ U
    rw [← hea, e.symm_apply_apply]
    exact ha
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp (hU.preimage hei) 0 hz
  have hR : 0 < δ / 2 := half_pos hδ
  refine ⟨δ / 2, hR, ?_, ?_⟩
  · exact Set.mem_preimage.mpr
      ((congrArg (fun q : Plane => q ∈ ball (0 : Plane) (δ / 2)) hea).mpr
        (mem_ball_self hR))
  · intro p hp
    have hpδ : e p ∈ ball (0 : Plane) δ := by
      have hpR : dist (e p) 0 ≤ δ / 2 := hp
      exact lt_of_le_of_lt hpR (half_lt_self hδ)
    have hpU := hδU hpδ
    change e.symm (e p) ∈ U at hpU
    rwa [e.symm_apply_apply] at hpU

private theorem compact_corner_replacement_of_closed_ball_subset
    {D U : Set Plane} (hD : IsCompact D) (e : Plane ≃ᵃ[ℝ] Plane)
    {ε R d σ : ℝ} (hε : 0 < ε) (hεR : 3 * ε < R)
    (hd : d = 0 ∨ d = 1) (hσ : σ = -1 ∨ σ = 1)
    (hKU : e ⁻¹' closedBall (0 : Plane) R ⊆ U)
    (hside : ∀ p ∈ U, p ∈ D ↔ 0 ≤ σ * ((e p) 1 - d * max ((e p) 0) 0)) :
    let N := e ⁻¹' ball (0 : Plane) R
    let K := e ⁻¹' closedBall (0 : Plane) R
    let H : Plane → ℝ := fun p => σ * ((e p) 1 - d * Real.smoothMax ε ((e p) 0) 0)
    let D' := (D \ N) ∪ (K ∩ {p | 0 ≤ H p})
    IsCompact D' ∧ ContDiff ℝ ∞ H ∧ (∀ p, fderiv ℝ H p ≠ 0) ∧
      (∀ p ∈ N, (p ∈ D' ↔ 0 ≤ H p) ∧
        (p ∈ interior D' ↔ 0 < H p) ∧ (p ∈ frontier D' ↔ H p = 0)) ∧
      (∀ p ∉ N, p ∈ D' ↔ p ∈ D) ∧ (d = 0 → D' = D) := by
  let N := e ⁻¹' ball (0 : Plane) R
  let K := e ⁻¹' closedBall (0 : Plane) R
  let H : Plane → ℝ := fun p => σ * ((e p) 1 - d * Real.smoothMax ε ((e p) 0) 0)
  have he : Continuous e := e.toAffineMap.continuous_of_finiteDimensional
  have hN : IsOpen N := isOpen_ball.preimage he
  have hK : IsCompact K := affine_preimage_isCompact e (isCompact_closedBall (0 : Plane) R)
  have hNK : N ⊆ K := Set.preimage_mono (f := e)
    (ball_subset_closedBall (x := (0 : Plane)) (ε := R))
  have hσne : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  obtain ⟨hH, hreg⟩ := affine_smooth_corner_regular e ε d σ hσne
  have heq : ∀ p ∈ K \ N, 0 ≤ H p ↔ p ∈ D := fun p hp =>
    (affine_smooth_corner_side_eq_outside_ball e hε hεR hd hp.2).trans
      (hside p (hKU hp.1)).symm
  obtain ⟨hD', hlocal, hout⟩ := regular_region_replace_on_open
    (D := D) (N := N) (K := K) (H := H) hD hN hK hNK hH.continuous
    (fun p _ _ => hreg p) heq
  refine ⟨hD', hH, hreg, hlocal, hout, fun hd0 => ?_⟩
  apply region_replace_eq_self_of_local_eq hNK
  intro p hp
  change 0 ≤ H p ↔ p ∈ D
  rw [hside p (hKU hp)]
  simp only [H, hd0, zero_mul, sub_zero]

private theorem exists_compact_corner_replacement
    {D U : Set Plane} (hD : IsCompact D) (hU : IsOpen U)
    (e : Plane ≃ᵃ[ℝ] Plane) {a : Plane} (ha : a ∈ U) (hea : e a = 0)
    {d σ : ℝ} (hd : d = 0 ∨ d = 1) (hσ : σ = -1 ∨ σ = 1)
    (hside : ∀ p ∈ U, p ∈ D ↔ 0 ≤ σ * ((e p) 1 - d * max ((e p) 0) 0)) :
    ∃ ε R : ℝ, 0 < ε ∧ 3 * ε < R ∧
      let N := e ⁻¹' ball (0 : Plane) R
      let K := e ⁻¹' closedBall (0 : Plane) R
      let H : Plane → ℝ := fun p => σ * ((e p) 1 - d * Real.smoothMax ε ((e p) 0) 0)
      let D' := (D \ N) ∪ (K ∩ {p | 0 ≤ H p})
      a ∈ N ∧ IsOpen N ∧ IsCompact K ∧ K ⊆ U ∧ IsCompact D' ∧
      ContDiff ℝ ∞ H ∧ (∀ p, fderiv ℝ H p ≠ 0) ∧
      (∀ p ∈ N, (p ∈ D' ↔ 0 ≤ H p) ∧
        (p ∈ interior D' ↔ 0 < H p) ∧ (p ∈ frontier D' ↔ H p = 0)) ∧
      (∀ p ∉ N, p ∈ D' ↔ p ∈ D) ∧ (d = 0 → D' = D) := by
  obtain ⟨R, hR, haN, hKU⟩ := exists_affine_closed_ball_subset hU e ha hea
  let ε := R / 4
  have hε : 0 < ε := div_pos hR (by norm_num)
  have hεR : 3 * ε < R := by dsimp [ε]; linarith
  have he : Continuous e := e.toAffineMap.continuous_of_finiteDimensional
  exact ⟨ε, R, hε, hεR, haN, isOpen_ball.preimage he,
    affine_preimage_isCompact e (isCompact_closedBall (0 : Plane) R), hKU,
    compact_corner_replacement_of_closed_ball_subset hD e hε hεR hd hσ hKU hside⟩

theorem PrePolygon.exists_compact_vertex_rounding
    {m : ℕ} (P : PrePolygon m) (i : ZMod (m + 3)) :
    ∃ (e : Plane ≃ᵃ[ℝ] Plane) (U : Set Plane) (d σ ε R : ℝ),
      IsOpen U ∧ P.vertex i ∈ U ∧ e (P.vertex i) = 0 ∧
      (d = 0 ∨ d = 1) ∧ (σ = -1 ∨ σ = 1) ∧
      (d = 0 ↔ Plane.det (P.vertex (i - 1) - P.vertex i)
        (P.vertex (i + 1) - P.vertex i) = 0) ∧
      0 < ε ∧ 3 * ε < R ∧
      let D := closure (inside P.carrier)
      let N := e ⁻¹' ball (0 : Plane) R
      let K := e ⁻¹' closedBall (0 : Plane) R
      let H : Plane → ℝ := fun p => σ * ((e p) 1 - d * Real.smoothMax ε ((e p) 0) 0)
      let D' := (D \ N) ∪ (K ∩ {p | 0 ≤ H p})
      (∀ p ∈ U, (p ∈ D ↔ 0 ≤ σ * ((e p) 1 - d * max ((e p) 0) 0)) ∧
        (p ∈ interior D ↔ 0 < σ * ((e p) 1 - d * max ((e p) 0) 0)) ∧
        (p ∈ frontier D ↔ (e p) 1 = d * max ((e p) 0) 0)) ∧
      P.vertex i ∈ N ∧ IsOpen N ∧ IsCompact K ∧ K ⊆ U ∧ IsCompact D' ∧
      ContDiff ℝ ∞ H ∧ (∀ p, fderiv ℝ H p ≠ 0) ∧
      (∀ p ∈ N, (p ∈ D' ↔ 0 ≤ H p) ∧
        (p ∈ interior D' ↔ 0 < H p) ∧ (p ∈ frontier D' ↔ H p = 0)) ∧
      (∀ p ∉ N, p ∈ D' ↔ p ∈ D) ∧ (d = 0 → D' = D) := by
  obtain ⟨e, U, _, d, σ, hU, _, hiU, _, hd, hσ, he0, _, _, hs, hside⟩ :=
    P.exists_affine_vertex_graph_sides i
  have hea : e (P.vertex i) = 0 := by
    rw [he0]
    ext j
    fin_cases j <;> rfl
  obtain ⟨ε, R, hε, hεR, hround⟩ := exists_compact_corner_replacement
    P.isSeparating_carrier.isBounded_inside.isCompact_closure hU e hiU hea hd hσ
    (fun p hp => (hside p hp).1)
  exact ⟨e, U, d, σ, ε, R, hU, hiU, hea, hd, hσ, hs, hε, hεR,
    fun p hp => ⟨(hside p hp).1, (hside p hp).2.1, (hside p hp).2.2.1⟩, hround⟩

end Schoenflies

end

section
open Set
open scoped ContDiff

namespace Schoenflies

private theorem PrePolygon.exists_straight_vertex_of_mem_open_edge
    {m : ℕ} (P : PrePolygon m) {i : ZMod (m + 3)} {p : Plane}
    (hp : p ∈ openSegment ℝ (P.vertex i) (P.vertex (i + 1))) :
    ∃ (Q : PrePolygon (m + 1)) (j : ZMod (m + 1 + 3)),
      Q.carrier = P.carrier ∧ Q.vertex j = p ∧
      Plane.det (Q.vertex (j - 1) - Q.vertex j) (Q.vertex (j + 1) - Q.vertex j) = 0 := by
  let Q := P.rotate (i + 1)
  have hQm : Q.vertex (-1) = P.vertex i := by
    change P.vertex (i + 1 + (-1)) = P.vertex i
    congr 1
    ring
  have hQ0 : Q.vertex 0 = P.vertex (i + 1) := by
    change P.vertex (i + 1 + 0) = P.vertex (i + 1)
    rw [add_zero]
  have hpQ : p ∈ openSegment ℝ (Q.vertex (-1)) (Q.vertex 0) := by
    rw [hQm, hQ0]
    exact hp
  let Q' := Q.insertLast hpQ
  have hv : Q'.vertex (-1) = p := Q.insVertex_neg_one _
  have hvpred : Q'.vertex (-1 - 1) = Q.vertex (-1) := by
    have he : PrePolygon.emb (-1 : ZMod (m + 3)) = (-1 - 1 : ZMod (m + 1 + 3)) :=
      PrePolygon.emb_eq_last (by rw [PrePolygon.val_neg_one])
    change Q.insVertex p (-1 - 1) = Q.vertex (-1)
    rw [← he, Q.insVertex_emb]
  have hvsucc : Q'.vertex (-1 + 1) = Q.vertex 0 := by
    have he : PrePolygon.emb (0 : ZMod (m + 3)) = (0 : ZMod (m + 1 + 3)) := by
      rw [PrePolygon.emb, ZMod.val_zero, Nat.cast_zero]
    change Q.insVertex p (-1 + 1) = Q.vertex 0
    rw [neg_add_cancel, ← he, Q.insVertex_emb]
  refine ⟨Q', -1, ?_, hv, ?_⟩
  · exact (PrePolygon.carrier_insertLast hpQ).trans (P.carrier_rotate (i + 1))
  · rw [hvpred, hvsucc, hv]
    exact det_eq_zero_of_mem_segment (left_mem_segment ℝ _ _)
      (right_mem_segment ℝ _ _) (openSegment_subset_segment ℝ _ _ hpQ)

private theorem PrePolygon.exists_regular_neighborhood_of_mem_carrier_not_vertex
    {m : ℕ} (P : PrePolygon m) {p : Plane} (hp : p ∈ P.carrier)
    (hn : p ∉ Set.range P.vertex) :
    ∃ (U : Set Plane) (H : Plane → ℝ), IsOpen U ∧ p ∈ U ∧
      ContDiff ℝ ∞ H ∧ (∀ q, fderiv ℝ H q ≠ 0) ∧
      ∀ q ∈ U,
        (q ∈ closure (inside P.carrier) ↔ 0 ≤ H q) ∧
        (q ∈ interior (closure (inside P.carrier)) ↔ 0 < H q) ∧
        (q ∈ frontier (closure (inside P.carrier)) ↔ H q = 0) := by
  obtain ⟨i, hpi⟩ := Set.mem_iUnion.mp hp
  have hopen : p ∈ openSegment ℝ (P.vertex i) (P.vertex (i + 1)) :=
    mem_openSegment_of_ne_left_right (fun he => hn ⟨i, he⟩)
      (fun he => hn ⟨i + 1, he⟩) hpi
  obtain ⟨Q, j, hcar, hj, hdet⟩ := P.exists_straight_vertex_of_mem_open_edge hopen
  obtain ⟨e, U, _, d, σ, hU, _, hjU, _, _, hσ, _, _, _, hs, hside⟩ :=
    Q.exists_affine_vertex_graph_sides j
  have hd0 : d = 0 := hs.mpr hdet
  subst d
  have hσne : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  have hh := affine_smooth_corner_regular e 1 0 σ hσne
  simp only [zero_mul, sub_zero] at hh
  have hweak : ∀ q ∈ U, q ∈ closure (inside P.carrier) ↔ 0 ≤ σ * (e q) 1 := by
    intro q hq
    simpa only [hcar, zero_mul, sub_zero] using (hside q hq).1
  have hsides := DifferentialGeometry.Analysis.interior_frontier_iff_of_local_regular_superlevel
    isClosed_closure hU hh.1.continuous
    (fun q _ _ => hh.2 q) hweak
  exact ⟨U, _, hU, hj ▸ hjU, hh.1, hh.2,
    fun q hq => ⟨hweak q hq, hsides q hq⟩⟩

end Schoenflies

end

section
open Set

namespace Schoenflies

end Schoenflies

end

section
open Set Metric
open scoped ContDiff Topology

namespace Schoenflies

private theorem PrePolygon.regular_frontier_of_finite_replacement
    {m : ℕ} (P : PrePolygon m) {D' : Set Plane} (hD' : IsClosed D')
    (U K : ZMod (m + 3) → Set Plane) (H : ZMod (m + 3) → Plane → ℝ)
    (hU : ∀ i, IsOpen (U i)) (hiU : ∀ i, P.vertex i ∈ U i)
    (hK : ∀ i, IsCompact (K i)) (hKU : ∀ i, K i ⊆ U i)
    (hH : ∀ i, ContDiff ℝ ∞ (H i)) (hreg : ∀ i p, fderiv ℝ (H i) p ≠ 0)
    (hlocal : ∀ i, ∀ p ∈ U i, p ∈ D' ↔ 0 ≤ H i p)
    (hout : ∀ p ∉ ⋃ i, K i, p ∈ D' ↔ p ∈ closure (inside P.carrier)) :
    ∀ p ∈ frontier D', ∃ (V : Set Plane) (G : Plane → ℝ),
      IsOpen V ∧ p ∈ V ∧ ContDiff ℝ ∞ G ∧ (∀ q, fderiv ℝ G q ≠ 0) ∧
      ∀ q ∈ V, (q ∈ D' ↔ 0 ≤ G q) ∧
        (q ∈ interior D' ↔ 0 < G q) ∧ (q ∈ frontier D' ↔ G q = 0) := by
  let D := closure (inside P.carrier)
  have hsides (i) := DifferentialGeometry.Analysis.interior_frontier_iff_of_local_regular_superlevel
    hD' (hU i)
    (hH i).continuous (fun p _ _ => hreg i p) (hlocal i)
  intro p hp
  by_cases hpU : p ∈ ⋃ i, U i
  · obtain ⟨i, hpi⟩ := Set.mem_iUnion.mp hpU
    exact ⟨U i, H i, hU i, hpi, hH i, hreg i,
      fun q hq => ⟨hlocal i q hq, hsides i q hq⟩⟩
  · let L := (⋃ i, K i)ᶜ
    have hL : IsOpen L := (isCompact_iUnion hK).isClosed.isOpen_compl
    have hpL : p ∈ L := by
      intro hpK
      obtain ⟨i, hpi⟩ := Set.mem_iUnion.mp hpK
      exact hpU (Set.mem_iUnion.mpr ⟨i, hKU i hpi⟩)
    have hsame : D' =ᶠ[𝓝 p] D := by
      filter_upwards [hL.mem_nhds hpL] with q hq
      exact propext (hout q hq)
    have hpD : p ∈ D := (hout p hpL).mp (hD'.frontier_subset hp)
    have hpfront : p ∈ frontier D := by
      rw [isClosed_closure.frontier_eq]
      refine ⟨hpD, ?_⟩
      intro hi
      exact hp.2 (hsame.mem_interior_iff.mpr hi)
    have hpcar : p ∈ P.carrier := by
      rw [← P.isSeparating_carrier.frontier_inside]
      exact frontier_closure_subset hpfront
    have hn : p ∉ Set.range P.vertex := by
      rintro ⟨i, rfl⟩
      exact hpU (Set.mem_iUnion.mpr ⟨i, hiU i⟩)
    obtain ⟨V, G, hV, hpV, hG, hGreg, hGsides⟩ :=
      P.exists_regular_neighborhood_of_mem_carrier_not_vertex hpcar hn
    have hweak : ∀ q ∈ L ∩ V, q ∈ D' ↔ 0 ≤ G q :=
      fun q hq => (hout q hq.1).trans (hGsides q hq.2).1
    have hnew := DifferentialGeometry.Analysis.interior_frontier_iff_of_local_regular_superlevel
      hD' (hL.inter hV)
      hG.continuous (fun q _ _ => hGreg q) hweak
    exact ⟨L ∩ V, G, hL.inter hV, ⟨hpL, hpV⟩, hG, hGreg,
      fun q hq => ⟨hweak q hq, hnew q hq⟩⟩

theorem PrePolygon.exists_normalized_finite_compact_vertex_rounding
    {m : ℕ} (P : PrePolygon m) (O : ZMod (m + 3) → Set Plane)
    (hO : ∀ i, IsOpen (O i)) (hiO : ∀ i, P.vertex i ∈ O i) :
    ∃ (e : ZMod (m + 3) → Plane ≃ᵃ[ℝ] Plane)
      (U : ZMod (m + 3) → Set Plane) (d σ ε R r : ZMod (m + 3) → ℝ),
      (∀ i, 0 < r i ∧ e i (P.vertex (i - 1)) = Plane.mk (-1) 0 ∧
        e i (P.vertex (i + 1)) = Plane.mk (r i) (d i * r i)) ∧
      (∀ i, IsOpen (U i) ∧ P.vertex i ∈ U i ∧ U i ⊆ O i ∧
        e i (P.vertex i) = 0 ∧ (d i = 0 ∨ d i = 1) ∧
        (σ i = -1 ∨ σ i = 1) ∧
        (d i = 0 ↔ Plane.det (P.vertex (i - 1) - P.vertex i)
          (P.vertex (i + 1) - P.vertex i) = 0) ∧ 0 < ε i ∧ 3 * ε i < R i ∧
        ∀ p ∈ U i, p ∈ closure (inside P.carrier) ↔
          0 ≤ σ i * ((e i p) 1 - d i * max ((e i p) 0) 0)) ∧
      (Pairwise fun i j => Disjoint (U i) (U j)) ∧
      let N := fun i => e i ⁻¹' ball (0 : Plane) (R i)
      let K := fun i => e i ⁻¹' closedBall (0 : Plane) (R i)
      let H := fun i p => σ i * ((e i p) 1 - d i * Real.smoothMax (ε i) ((e i p) 0) 0)
      let D := closure (inside P.carrier)
      let D' := (D \ ⋃ i, N i) ∪ ⋃ i, K i ∩ {p | 0 ≤ H i p}
      (∀ i, P.vertex i ∈ N i ∧ IsOpen (N i) ∧ IsCompact (K i) ∧ K i ⊆ U i) ∧
      IsCompact D' ∧ (∀ p ∉ ⋃ i, K i, p ∈ D' ↔ p ∈ D) ∧
      (∀ i, ContDiff ℝ ∞ (H i) ∧ (∀ p, fderiv ℝ (H i) p ≠ 0) ∧
        ∀ p ∈ U i, (p ∈ D' ↔ 0 ≤ H i p) ∧
          (p ∈ interior D' ↔ 0 < H i p) ∧ (p ∈ frontier D' ↔ H i p = 0)) ∧
      ∀ p ∈ frontier D', ∃ (V : Set Plane) (G : Plane → ℝ),
        IsOpen V ∧ p ∈ V ∧ ContDiff ℝ ∞ G ∧ (∀ q, fderiv ℝ G q ≠ 0) ∧
        ∀ q ∈ V, (q ∈ D' ↔ 0 ≤ G q) ∧
          (q ∈ interior D' ↔ 0 < G q) ∧ (q ∈ frontier D' ↔ G q = 0) := by
  classical
  choose e A r d σ hA _ hiA hr hd hσ he0 heprev henext hstraight hside using
    (fun i => P.exists_affine_vertex_graph_sides i)
  obtain ⟨U, hU, hdisj⟩ := Set.exists_pairwise_disjoint_open_neighborhoods P.vertex P.vertex_inj
    (fun i => A i ∩ O i) (fun i => (hA i).inter (hO i)) (fun i => ⟨hiA i, hiO i⟩)
  have hea (i) : e i (P.vertex i) = 0 := by
    rw [he0 i]
    ext j
    fin_cases j <;> rfl
  have hD : IsCompact (closure (inside P.carrier)) :=
    P.isSeparating_carrier.isBounded_inside.isCompact_closure
  choose ε R hε hεR hround using fun i => exists_compact_corner_replacement hD (hU i).1
    (e i) (hU i).2.1 (hea i) (hd i) (hσ i)
    (fun p hp => (hside i p ((hU i).2.2 hp).1).1)
  let N := fun i => e i ⁻¹' ball (0 : Plane) (R i)
  let K := fun i => e i ⁻¹' closedBall (0 : Plane) (R i)
  let H := fun i p => σ i * ((e i p) 1 - d i * Real.smoothMax (ε i) ((e i p) 0) 0)
  let D := closure (inside P.carrier)
  have hN (i) : IsOpen (N i) := (hround i).2.1
  have hK (i) : IsCompact (K i) := (hround i).2.2.1
  have hKU (i) : K i ⊆ U i := (hround i).2.2.2.1
  have hNK (i) : N i ⊆ K i := Set.preimage_mono (f := e i)
    (ball_subset_closedBall (x := (0 : Plane)) (ε := R i))
  have hH (i) : ContDiff ℝ ∞ (H i) := (hround i).2.2.2.2.2.1
  have hreg (i) : ∀ p, fderiv ℝ (H i) p ≠ 0 := (hround i).2.2.2.2.2.2.1
  have heq (i) : ∀ p ∈ U i \ N i, p ∈ {p | 0 ≤ H i p} ↔ p ∈ D := by
    intro p hp
    have hpR : R i ≤ ‖e i p‖ := by
      have hn : ¬ ‖e i p‖ < R i := by
        simpa only [N, Set.mem_preimage, mem_ball_zero_iff] using hp.2
      exact le_of_not_gt hn
    exact (smooth_corner_signs_eq_outside_ball (σ := σ i) (hε i) (hd i)
      ((hεR i).trans_le hpR)).1.trans
        (hside i p ((hU i).2.2 hp.1).1).1.symm
  obtain ⟨hD', hlocal, hout⟩ := Set.isCompact_finite_disjoint_replacement hD hN hK
    (fun i => isClosed_le continuous_const (hH i).continuous) hNK hKU hdisj heq
  have hsides (i) := DifferentialGeometry.Analysis.interior_frontier_iff_of_local_regular_superlevel
    hD'.isClosed (hU i).1
    (hH i).continuous (fun p _ _ => hreg i p) (hlocal i)
  refine ⟨e, U, d, σ, ε, R, r, fun i => ⟨hr i, heprev i, henext i⟩,
    ?_, hdisj, ?_, hD', hout,
    fun i => ⟨hH i, hreg i, fun p hp => ⟨hlocal i p hp, hsides i p hp⟩⟩, ?_⟩
  · exact fun i => ⟨(hU i).1, (hU i).2.1,
      fun p hp => ((hU i).2.2 hp).2, hea i, hd i, hσ i, hstraight i, hε i, hεR i,
        fun p hp => (hside i p ((hU i).2.2 hp).1).1⟩
  · exact fun i => ⟨(hround i).1, hN i, hK i, hKU i⟩
  · exact P.regular_frontier_of_finite_replacement hD'.isClosed U K H
      (fun i => (hU i).1) (fun i => (hU i).2.1) hK hKU hH hreg hlocal hout


theorem PrePolygon.exists_finite_compact_vertex_rounding
    {m : ℕ} (P : PrePolygon m) (O : ZMod (m + 3) → Set Plane)
    (hO : ∀ i, IsOpen (O i)) (hiO : ∀ i, P.vertex i ∈ O i) :
    ∃ (e : ZMod (m + 3) → Plane ≃ᵃ[ℝ] Plane)
      (U : ZMod (m + 3) → Set Plane) (d σ ε R : ZMod (m + 3) → ℝ),
      (∀ i, IsOpen (U i) ∧ P.vertex i ∈ U i ∧ U i ⊆ O i ∧
        e i (P.vertex i) = 0 ∧ (d i = 0 ∨ d i = 1) ∧
        (σ i = -1 ∨ σ i = 1) ∧
        (d i = 0 ↔ Plane.det (P.vertex (i - 1) - P.vertex i)
          (P.vertex (i + 1) - P.vertex i) = 0) ∧ 0 < ε i ∧ 3 * ε i < R i ∧
        ∀ p ∈ U i, p ∈ closure (inside P.carrier) ↔
          0 ≤ σ i * ((e i p) 1 - d i * max ((e i p) 0) 0)) ∧
      (Pairwise fun i j => Disjoint (U i) (U j)) ∧
      let N := fun i => e i ⁻¹' ball (0 : Plane) (R i)
      let K := fun i => e i ⁻¹' closedBall (0 : Plane) (R i)
      let H := fun i p => σ i * ((e i p) 1 - d i * Real.smoothMax (ε i) ((e i p) 0) 0)
      let D := closure (inside P.carrier)
      let D' := (D \ ⋃ i, N i) ∪ ⋃ i, K i ∩ {p | 0 ≤ H i p}
      (∀ i, P.vertex i ∈ N i ∧ IsOpen (N i) ∧ IsCompact (K i) ∧ K i ⊆ U i) ∧
      IsCompact D' ∧ (∀ p ∉ ⋃ i, K i, p ∈ D' ↔ p ∈ D) ∧
      (∀ i, ContDiff ℝ ∞ (H i) ∧ (∀ p, fderiv ℝ (H i) p ≠ 0) ∧
        ∀ p ∈ U i, (p ∈ D' ↔ 0 ≤ H i p) ∧
          (p ∈ interior D' ↔ 0 < H i p) ∧ (p ∈ frontier D' ↔ H i p = 0)) ∧
      ∀ p ∈ frontier D', ∃ (V : Set Plane) (G : Plane → ℝ),
        IsOpen V ∧ p ∈ V ∧ ContDiff ℝ ∞ G ∧ (∀ q, fderiv ℝ G q ≠ 0) ∧
        ∀ q ∈ V, (q ∈ D' ↔ 0 ≤ G q) ∧
          (q ∈ interior D' ↔ 0 < G q) ∧ (q ∈ frontier D' ↔ G q = 0) := by
  obtain ⟨e, U, d, σ, ε, R, _, _, hrest⟩ :=
    P.exists_normalized_finite_compact_vertex_rounding O hO hiO
  exact ⟨e, U, d, σ, ε, R, hrest⟩

end Schoenflies

end

section
open Set Metric
open scoped ContDiff

namespace Schoenflies

theorem PrePolygon.exists_compact_rounding
    {m : ℕ} (P : PrePolygon m) {O : Set Plane}
    (hO : IsOpen O) (hvO : Set.range P.vertex ⊆ O) :
    ∃ D' : Set Plane, IsCompact D' ∧ (frontier D').Nonempty ∧
      (∀ p ∉ O, p ∈ D' ↔ p ∈ closure (inside P.carrier)) ∧
      ∀ p ∈ frontier D', ∃ (U : Set Plane) (H : Plane → ℝ),
        IsOpen U ∧ p ∈ U ∧ ContDiff ℝ ∞ H ∧ (∀ q, fderiv ℝ H q ≠ 0) ∧
        ∀ q ∈ U, (q ∈ D' ↔ 0 ≤ H q) ∧
          (q ∈ interior D' ↔ 0 < H q) ∧ (q ∈ frontier D' ↔ H q = 0) := by
  obtain ⟨e, U, d, σ, ε, R, hc, _, hn, hD, hout, hlocal, hglobal⟩ :=
    P.exists_finite_compact_vertex_rounding (fun _ => O) (fun _ => hO)
      (fun i => hvO (Set.mem_range_self i))
  let K := fun i => e i ⁻¹' closedBall (0 : Plane) (R i)
  let H := fun i p => σ i * ((e i p) 1 - d i * Real.smoothMax (ε i) ((e i p) 0) 0)
  let D' := (closure (inside P.carrier) \ ⋃ i, e i ⁻¹' ball (0 : Plane) (R i)) ∪
    ⋃ i, K i ∩ {p | 0 ≤ H i p}
  obtain ⟨_, _, _, _, hd, _, _, hε, hεR, _⟩ := hc 0
  let μ := Real.smoothMax (ε 0) 0 0
  have hμ : 0 ≤ μ := by
    simpa only [max_self] using Real.smoothMax.max_le hε 0 0
  have hμε : μ ≤ ε 0 := by
    simpa only [max_self, zero_add] using Real.smoothMax.le_max_add hε 0 0
  have hy : 0 ≤ d 0 * μ ∧ d 0 * μ ≤ ε 0 := by
    rcases hd with hd | hd
    · rw [hd, zero_mul]
      exact ⟨le_rfl, hε.le⟩
    · rw [hd, one_mul]
      exact ⟨hμ, hμε⟩
  let p := (e 0).symm (Plane.mk 0 (d 0 * μ))
  have hpN : p ∈ e 0 ⁻¹' ball (0 : Plane) (R 0) := by
    change (e 0) ((e 0).symm (Plane.mk 0 (d 0 * μ))) ∈ ball (0 : Plane) (R 0)
    rw [(e 0).apply_symm_apply, mem_ball_zero_iff]
    have hnorm : ‖Plane.mk 0 (d 0 * μ)‖ = d 0 * μ := by
      apply (sq_eq_sq₀ (norm_nonneg _) hy.1).mp
      rw [EuclideanSpace.real_norm_sq_eq]
      norm_num [Fin.sum_univ_two, Plane.mk]
    rw [hnorm]
    linarith
  have hpU : p ∈ U 0 := (hn 0).2.2.2
    (Set.preimage_mono (f := e 0)
      (ball_subset_closedBall (x := (0 : Plane)) (ε := R 0)) hpN)
  have hpfront : p ∈ frontier D' := by
    apply ((hlocal 0).2.2 p hpU).2.2.mpr
    change σ 0 * (((e 0) ((e 0).symm (Plane.mk 0 (d 0 * μ)))) 1 - d 0 *
      Real.smoothMax (ε 0) (((e 0) ((e 0).symm (Plane.mk 0 (d 0 * μ)))) 0) 0) = 0
    rw [(e 0).apply_symm_apply]
    change σ 0 * (d 0 * μ - d 0 * μ) = 0
    ring
  refine ⟨D', hD, ⟨p, hpfront⟩, ?_, hglobal⟩
  intro q hq
  apply hout q
  intro hqK
  obtain ⟨i, hqi⟩ := Set.mem_iUnion.mp hqK
  exact hq ((hc i).2.2.1 ((hn i).2.2.2 hqi))

end Schoenflies

end

section

open Set Metric
open scoped ContDiff Topology

namespace Schoenflies

private theorem region_sides_of_open_local_eq
    {X : Type*} [TopologicalSpace X] {D D' V : Set X}
    (hD : IsClosed D) (hD' : IsClosed D') (hV : IsOpen V)
    (heq : ∀ p ∈ V, p ∈ D' ↔ p ∈ D) :
    ∀ p ∈ V, (p ∈ D' ↔ p ∈ D) ∧
      (p ∈ interior D' ↔ p ∈ interior D) ∧
      (p ∈ frontier D' ↔ p ∈ frontier D) := by
  intro p hp
  have hsame : D' =ᶠ[𝓝 p] D := by
    filter_upwards [hV.mem_nhds hp] with q hq
    exact propext (heq q hq)
  refine ⟨heq p hp, hsame.mem_interior_iff, ?_⟩
  rw [hD'.frontier_eq, hD.frontier_eq]
  change (p ∈ D' ∧ p ∉ interior D') ↔ (p ∈ D ∧ p ∉ interior D)
  rw [heq p hp, hsame.mem_interior_iff]

private theorem PrePolygon.regular_frontier_of_partial_replacement
    {m : ℕ} (P : PrePolygon m) {D D' L W : Set Plane}
    (hD : IsClosed D) (hD' : IsClosed D') (hL : IsClosed L) (hLW : L ⊆ W)
    (hold : ∀ p ∉ L, p ∈ D ↔ p ∈ closure (inside P.carrier))
    (hgood : ∀ p ∈ frontier D, p ∈ W →
      ∃ (N : Set Plane) (G : Plane → ℝ), IsOpen N ∧ p ∈ N ∧
        ContDiff ℝ ∞ G ∧ fderiv ℝ G p ≠ 0 ∧
        ∀ q ∈ N, (q ∈ D ↔ 0 ≤ G q) ∧
          (q ∈ interior D ↔ 0 < G q) ∧ (q ∈ frontier D ↔ G q = 0))
    (U K : {i : ZMod (m + 3) // P.vertex i ∉ W} → Set Plane)
    (H : {i : ZMod (m + 3) // P.vertex i ∉ W} → Plane → ℝ)
    (hU : ∀ i, IsOpen (U i)) (hiU : ∀ i, P.vertex i.val ∈ U i)
    (hK : ∀ i, IsCompact (K i)) (hKU : ∀ i, K i ⊆ U i)
    (hH : ∀ i, ContDiff ℝ ∞ (H i)) (hreg : ∀ i p, fderiv ℝ (H i) p ≠ 0)
    (hlocal : ∀ i, ∀ p ∈ U i, p ∈ D' ↔ 0 ≤ H i p)
    (hout : ∀ p ∉ ⋃ i, K i, p ∈ D' ↔ p ∈ D) :
    ∀ p ∈ frontier D', ∃ (N : Set Plane) (G : Plane → ℝ),
      IsOpen N ∧ p ∈ N ∧ ContDiff ℝ ∞ G ∧ fderiv ℝ G p ≠ 0 ∧
      ∀ q ∈ N, (q ∈ D' ↔ 0 ≤ G q) ∧
        (q ∈ interior D' ↔ 0 < G q) ∧ (q ∈ frontier D' ↔ G q = 0) := by
  have hsides (i) := DifferentialGeometry.Analysis.interior_frontier_iff_of_local_regular_superlevel
    hD' (hU i)
    (hH i).continuous (fun p _ _ => hreg i p) (hlocal i)
  let A := (⋃ i, K i)ᶜ
  have hA : IsOpen A := (isCompact_iUnion hK).isClosed.isOpen_compl
  have heqA := region_sides_of_open_local_eq hD hD' hA hout
  intro p hp
  by_cases hpU : p ∈ ⋃ i, U i
  · obtain ⟨i, hpi⟩ := Set.mem_iUnion.mp hpU
    exact ⟨U i, H i, hU i, hpi, hH i, hreg i p,
      fun q hq => ⟨hlocal i q hq, hsides i q hq⟩⟩
  · have hpA : p ∈ A := by
      intro hpK
      obtain ⟨i, hpi⟩ := Set.mem_iUnion.mp hpK
      exact hpU (Set.mem_iUnion.mpr ⟨i, hKU i hpi⟩)
    by_cases hpW : p ∈ W
    · obtain ⟨N, G, hN, hpN, hG, hGreg, hGsides⟩ :=
        hgood p ((heqA p hpA).2.2.mp hp) hpW
      refine ⟨N ∩ A, G, hN.inter hA, ⟨hpN, hpA⟩, hG, hGreg, ?_⟩
      intro q hq
      exact ⟨(heqA q hq.2).1.trans (hGsides q hq.1).1,
        (heqA q hq.2).2.1.trans (hGsides q hq.1).2.1,
        (heqA q hq.2).2.2.trans (hGsides q hq.1).2.2⟩
    · let B := A ∩ Lᶜ
      have hB : IsOpen B := hA.inter hL.isOpen_compl
      have hpB : p ∈ B := ⟨hpA, fun hpL => hpW (hLW hpL)⟩
      have hweak : ∀ q ∈ B, q ∈ D' ↔ q ∈ closure (inside P.carrier) :=
        fun q hq => (hout q hq.1).trans (hold q hq.2)
      have heqB := region_sides_of_open_local_eq isClosed_closure hD' hB hweak
      have hpfront : p ∈ frontier (closure (inside P.carrier)) :=
        (heqB p hpB).2.2.mp hp
      have hpcar : p ∈ P.carrier := by
        rw [← P.isSeparating_carrier.frontier_inside]
        exact frontier_closure_subset hpfront
      have hn : p ∉ Set.range P.vertex := by
        rintro ⟨i, rfl⟩
        exact hpU (Set.mem_iUnion.mpr ⟨⟨i, hpW⟩, hiU ⟨i, hpW⟩⟩)
      obtain ⟨N, G, hN, hpN, hG, hGreg, hGsides⟩ :=
        P.exists_regular_neighborhood_of_mem_carrier_not_vertex hpcar hn
      refine ⟨B ∩ N, G, hB.inter hN, ⟨hpB, hpN⟩, hG, hGreg p, ?_⟩
      intro q hq
      exact ⟨(heqB q hq.1).1.trans (hGsides q hq.2).1,
        (heqB q hq.1).2.1.trans (hGsides q hq.2).2.1,
        (heqB q hq.1).2.2.trans (hGsides q hq.2).2.2⟩

end Schoenflies

end

section

open Set Metric
open scoped ContDiff Topology

namespace Schoenflies

theorem PrePolygon.exists_normalized_relative_compact_rounding
    {m : ℕ} (P : PrePolygon m) {D L W O : Set Plane}
    (hD : IsCompact D) (hL : IsClosed L) (hW : IsOpen W) (hLW : L ⊆ W)
    (hO : IsOpen O) (hvO : ∀ i, P.vertex i ∉ W → P.vertex i ∈ O)
    (hold : ∀ p ∉ L, p ∈ D ↔ p ∈ closure (inside P.carrier))
    (hgood : ∀ p ∈ frontier D, p ∈ W →
      ∃ (N : Set Plane) (G : Plane → ℝ), IsOpen N ∧ p ∈ N ∧
        ContDiff ℝ ∞ G ∧ fderiv ℝ G p ≠ 0 ∧
        ∀ q ∈ N, (q ∈ D ↔ 0 ≤ G q) ∧
          (q ∈ interior D ↔ 0 < G q) ∧ (q ∈ frontier D ↔ G q = 0)) :
    let I := {i : ZMod (m + 3) // P.vertex i ∉ W}
    ∃ (e : I → Plane ≃ᵃ[ℝ] Plane) (U : I → Set Plane) (d σ ε R r : I → ℝ),
      (∀ i, 0 < r i ∧ e i (P.vertex (i.val - 1)) = Plane.mk (-1) 0 ∧
        e i (P.vertex (i.val + 1)) = Plane.mk (r i) (d i * r i)) ∧
      (∀ i, IsOpen (U i) ∧ P.vertex i.val ∈ U i ∧ U i ⊆ Lᶜ ∩ O ∧
        e i (P.vertex i.val) = 0 ∧ (d i = 0 ∨ d i = 1) ∧
        (σ i = -1 ∨ σ i = 1) ∧
        (d i = 0 ↔ Plane.det (P.vertex (i.val - 1) - P.vertex i.val)
          (P.vertex (i.val + 1) - P.vertex i.val) = 0) ∧ 0 < ε i ∧ 3 * ε i < R i ∧
        ∀ p ∈ U i, p ∈ D ↔ 0 ≤ σ i * ((e i p) 1 - d i * max ((e i p) 0) 0)) ∧
      (Pairwise fun i j => Disjoint (U i) (U j)) ∧
      let N := fun i => e i ⁻¹' ball (0 : Plane) (R i)
      let K := fun i => e i ⁻¹' closedBall (0 : Plane) (R i)
      let H := fun i p => σ i * ((e i p) 1 - d i * Real.smoothMax (ε i) ((e i p) 0) 0)
      let D' := (D \ ⋃ i, N i) ∪ ⋃ i, K i ∩ {p | 0 ≤ H i p}
      let V := W ∩ (⋃ i, K i)ᶜ
      (∀ i, P.vertex i.val ∈ N i ∧ IsOpen (N i) ∧ IsCompact (K i) ∧ K i ⊆ U i) ∧
      (∀ i, ContDiff ℝ ∞ (H i) ∧ (∀ p, fderiv ℝ (H i) p ≠ 0) ∧
        ∀ p ∈ U i, (p ∈ D' ↔ 0 ≤ H i p) ∧
          (p ∈ interior D' ↔ 0 < H i p) ∧ (p ∈ frontier D' ↔ H i p = 0)) ∧
      (∀ p ∉ ⋃ i, K i, (p ∈ D' ↔ p ∈ D) ∧
        (p ∈ interior D' ↔ p ∈ interior D) ∧
        (p ∈ frontier D' ↔ p ∈ frontier D)) ∧
      IsCompact D' ∧ IsOpen V ∧ L ⊆ V ∧ V ⊆ W ∧
      (∀ p ∈ V, (p ∈ D' ↔ p ∈ D) ∧
        (p ∈ interior D' ↔ p ∈ interior D) ∧
        (p ∈ frontier D' ↔ p ∈ frontier D)) ∧
      (∀ p ∉ O, (p ∈ D' ↔ p ∈ D) ∧
        (p ∈ interior D' ↔ p ∈ interior D) ∧
        (p ∈ frontier D' ↔ p ∈ frontier D)) ∧
      ∀ p ∈ frontier D', ∃ (N : Set Plane) (G : Plane → ℝ),
        IsOpen N ∧ p ∈ N ∧ ContDiff ℝ ∞ G ∧ fderiv ℝ G p ≠ 0 ∧
        ∀ q ∈ N, (q ∈ D' ↔ 0 ≤ G q) ∧
          (q ∈ interior D' ↔ 0 < G q) ∧ (q ∈ frontier D' ↔ G q = 0) := by
  classical
  let I := {i : ZMod (m + 3) // P.vertex i ∉ W}
  choose e A r d σ hA _ hiA hr hd hσ he0 heprev henext hstraight hside using
    (fun i : I => P.exists_affine_vertex_graph_sides i.val)
  have hinj : Function.Injective (fun i : I => P.vertex i.val) :=
    P.vertex_inj.comp Subtype.val_injective
  obtain ⟨U, hU, hdisj⟩ := Set.exists_pairwise_disjoint_open_neighborhoods
    (fun i : I => P.vertex i.val) hinj (fun i => (A i ∩ Lᶜ) ∩ O)
    (fun i => ((hA i).inter hL.isOpen_compl).inter hO)
    (fun i => ⟨⟨hiA i, fun hp => i.property (hLW hp)⟩, hvO i.val i.property⟩)
  have hea (i : I) : e i (P.vertex i.val) = 0 := by
    rw [he0 i]
    ext j
    fin_cases j <;> rfl
  have hsideD (i : I) : ∀ p ∈ U i,
      p ∈ D ↔ 0 ≤ σ i * ((e i p) 1 - d i * max ((e i p) 0) 0) := by
    intro p hp
    exact (hold p ((hU i).2.2 hp).1.2).trans (hside i p ((hU i).2.2 hp).1.1).1
  choose ε R hε hεR hround using fun i => exists_compact_corner_replacement hD (hU i).1
    (e i) (hU i).2.1 (hea i) (hd i) (hσ i) (hsideD i)
  let N := fun i => e i ⁻¹' ball (0 : Plane) (R i)
  let K := fun i => e i ⁻¹' closedBall (0 : Plane) (R i)
  let H := fun i p => σ i * ((e i p) 1 - d i * Real.smoothMax (ε i) ((e i p) 0) 0)
  have hN (i) : IsOpen (N i) := (hround i).2.1
  have hK (i) : IsCompact (K i) := (hround i).2.2.1
  have hKU (i) : K i ⊆ U i := (hround i).2.2.2.1
  have hNK (i) : N i ⊆ K i := Set.preimage_mono (f := e i)
    (ball_subset_closedBall (x := (0 : Plane)) (ε := R i))
  have hH (i) : ContDiff ℝ ∞ (H i) := (hround i).2.2.2.2.2.1
  have hreg (i) : ∀ p, fderiv ℝ (H i) p ≠ 0 := (hround i).2.2.2.2.2.2.1
  have heq (i) : ∀ p ∈ U i \ N i, p ∈ {p | 0 ≤ H i p} ↔ p ∈ D := by
    intro p hp
    exact (affine_smooth_corner_side_eq_outside_ball (e i) (hε i) (hεR i)
      (hd i) hp.2).trans (hsideD i p hp.1).symm
  obtain ⟨hD', hlocal, hout⟩ := Set.isCompact_finite_disjoint_replacement hD hN hK
    (fun i => isClosed_le continuous_const (hH i).continuous) hNK hKU hdisj heq
  let D' := (D \ ⋃ i, N i) ∪ ⋃ i, K i ∩ {p | 0 ≤ H i p}
  let V := W ∩ (⋃ i, K i)ᶜ
  have hV : IsOpen V := hW.inter (isCompact_iUnion hK).isClosed.isOpen_compl
  have hLV : L ⊆ V := by
    intro p hp
    refine ⟨hLW hp, ?_⟩
    intro hpK
    obtain ⟨i, hpi⟩ := Set.mem_iUnion.mp hpK
    exact ((hU i).2.2 (hKU i hpi)).1.2 hp
  have heqV : ∀ p ∈ V, p ∈ D' ↔ p ∈ D := fun p hp => hout p hp.2
  have houtside : ∀ p ∉ O, (p ∈ D' ↔ p ∈ D) ∧
      (p ∈ interior D' ↔ p ∈ interior D) ∧
      (p ∈ frontier D' ↔ p ∈ frontier D) := by
    intro p hp
    apply region_sides_of_open_local_eq hD.isClosed hD'.isClosed
      (isCompact_iUnion hK).isClosed.isOpen_compl hout p
    intro hpK
    obtain ⟨i, hpi⟩ := Set.mem_iUnion.mp hpK
    exact hp ((hU i).2.2 (hKU i hpi)).2
  have hsides (i) := DifferentialGeometry.Analysis.interior_frontier_iff_of_local_regular_superlevel
    hD'.isClosed (hU i).1
    (hH i).continuous (fun p _ _ => hreg i p) (hlocal i)
  have houter : ∀ p ∉ ⋃ i, K i, (p ∈ D' ↔ p ∈ D) ∧
      (p ∈ interior D' ↔ p ∈ interior D) ∧
      (p ∈ frontier D' ↔ p ∈ frontier D) :=
    region_sides_of_open_local_eq hD.isClosed hD'.isClosed
      (isCompact_iUnion hK).isClosed.isOpen_compl hout
  refine ⟨e, U, d, σ, ε, R, r, fun i => ⟨hr i, heprev i, henext i⟩,
    ?_, hdisj, ?_, ?_, houter, hD', hV, hLV, Set.inter_subset_left,
    region_sides_of_open_local_eq hD.isClosed hD'.isClosed hV heqV, houtside, ?_⟩
  · exact fun i => ⟨(hU i).1, (hU i).2.1,
      fun p hp => ⟨((hU i).2.2 hp).1.2, ((hU i).2.2 hp).2⟩,
      hea i, hd i, hσ i, hstraight i, hε i, hεR i, hsideD i⟩
  · exact fun i => ⟨(hround i).1, hN i, hK i, hKU i⟩
  · exact fun i => ⟨hH i, hreg i, fun p hp => ⟨hlocal i p hp, hsides i p hp⟩⟩
  · exact P.regular_frontier_of_partial_replacement hD.isClosed hD'.isClosed
      hL hLW hold hgood U K H (fun i => (hU i).1) (fun i => (hU i).2.1)
      hK hKU hH hreg hlocal hout

theorem PrePolygon.exists_relative_compact_rounding
    {m : ℕ} (P : PrePolygon m) {D L W O : Set Plane}
    (hD : IsCompact D) (hL : IsClosed L) (hW : IsOpen W) (hLW : L ⊆ W)
    (hO : IsOpen O) (hvO : ∀ i, P.vertex i ∉ W → P.vertex i ∈ O)
    (hold : ∀ p ∉ L, p ∈ D ↔ p ∈ closure (inside P.carrier))
    (hgood : ∀ p ∈ frontier D, p ∈ W →
      ∃ (N : Set Plane) (G : Plane → ℝ), IsOpen N ∧ p ∈ N ∧
        ContDiff ℝ ∞ G ∧ fderiv ℝ G p ≠ 0 ∧
        ∀ q ∈ N, (q ∈ D ↔ 0 ≤ G q) ∧
          (q ∈ interior D ↔ 0 < G q) ∧ (q ∈ frontier D ↔ G q = 0)) :
    ∃ (D' V : Set Plane), IsCompact D' ∧ IsOpen V ∧ L ⊆ V ∧ V ⊆ W ∧
      (∀ p ∈ V, (p ∈ D' ↔ p ∈ D) ∧
        (p ∈ interior D' ↔ p ∈ interior D) ∧
        (p ∈ frontier D' ↔ p ∈ frontier D)) ∧
      (∀ p ∉ O, (p ∈ D' ↔ p ∈ D) ∧
        (p ∈ interior D' ↔ p ∈ interior D) ∧
        (p ∈ frontier D' ↔ p ∈ frontier D)) ∧
      ∀ p ∈ frontier D', ∃ (N : Set Plane) (G : Plane → ℝ),
        IsOpen N ∧ p ∈ N ∧ ContDiff ℝ ∞ G ∧ fderiv ℝ G p ≠ 0 ∧
        ∀ q ∈ N, (q ∈ D' ↔ 0 ≤ G q) ∧
          (q ∈ interior D' ↔ 0 < G q) ∧ (q ∈ frontier D' ↔ G q = 0) := by
  obtain ⟨e, U, d, σ, ε, R, r, _, _, _, _, _, _, hround⟩ :=
    P.exists_normalized_relative_compact_rounding hD hL hW hLW hO hvO hold hgood
  exact ⟨_, _, hround⟩

end Schoenflies

end

section

namespace Schoenflies

private theorem compact_region_replace_preserving_germ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {D K W : Set E} {H : E → ℝ} (hD : IsCompact D) (hK : IsCompact K)
    (hW : IsOpen W) (hKW : K ⊆ W) (hH : Continuous H)
    (hreg : ∀ p ∈ W, H p = 0 → fderiv ℝ H p ≠ 0)
    (heq : ∀ p ∈ W \ interior K, p ∈ D ↔ 0 ≤ H p) :
    let D' := (D \ interior K) ∪ (K ∩ {p | 0 ≤ H p})
    IsCompact D' ∧
      (∀ p ∈ W, (p ∈ D' ↔ 0 ≤ H p) ∧
        (p ∈ interior D' ↔ 0 < H p) ∧ (p ∈ frontier D' ↔ H p = 0)) ∧
      (∀ p ∉ K, p ∈ D' ↔ p ∈ D) := by
  obtain ⟨hD', hlocal, hout⟩ := compact_region_replace_on_open hD isOpen_interior hK
    (isClosed_le continuous_const hH) interior_subset
    (fun p hp => (heq p ⟨hKW hp.1, hp.2⟩).symm)
  have hweak : ∀ p ∈ W,
      p ∈ (D \ interior K) ∪ (K ∩ {p | 0 ≤ H p}) ↔ 0 ≤ H p := by
    intro p hp
    by_cases hi : p ∈ interior K
    · exact hlocal p hi
    · exact (hout p hi).trans (heq p ⟨hp, hi⟩)
  have hsides := DifferentialGeometry.Analysis.interior_frontier_iff_of_local_regular_superlevel
    hD'.isClosed hW hH hreg hweak
  exact ⟨hD', fun p hp => ⟨hweak p hp, hsides p hp⟩,
    fun p hp => hout p (fun hi => hp (interior_subset hi))⟩

end Schoenflies

end

section

open scoped ContDiff Manifold Topology

namespace Schoenflies

private theorem PrePolygon.native_compact_region_with_prescribed_isotopy
    {m : ℕ} (P : PrePolygon m)
    (M : LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh)
    (hfrontier : frontier M.toPlaneComplex.support = P.carrier)
    (T : M.Triangle) (k : Fin 3) (hfree : M.IsOneEdgeFreeTriangle T k)
    {σ : ℝ} (hσ : 0 < σ) (hσsmall : σ ≤ 1 / 4) :
    let b := LeanEval.Topology.ClassificationOfSurfaces.Moise.affineBasisOfTriangle
      (M.freeTriangleOrder T k) (M.freeTriangleOrder_affineIndependent T k)
    let R := closure (P.carrier \ segment ℝ (b 0) (b 1))
    ∃ (v₀ v₁ : Plane) (f₀ f₁ : Plane →ᵃ[ℝ] ℝ) (ε : ℝ)
      (U₀ U₁ V : Set Plane) (F : Plane → ℝ × ℝ),
      let s₀ := b.coord 2 v₀ / f₀ v₀
      let s₁ := b.coord 2 v₁ / f₁ v₁
      let A₀ := fun p => s₀ * (f₀ p - Real.smoothMax ε (f₀ p) 0) - b.coord 2 p
      let A₁ := fun p => s₁ * (f₁ p - Real.smoothMax ε (f₁ p) 0) - b.coord 2 p
      let B₀ := fun p => f₀ (b 2) / f₀ (b 1) *
        (s₀ * (f₀ p - Real.smoothMax ε (f₀ p) 0) +
          Real.smoothMax ε (f₀ p) 0 / f₀ (b 2) - b.coord 2 p)
      let B₁ := fun p => f₁ (b 2) / f₁ (b 0) *
        (s₁ * (f₁ p - Real.smoothMax ε (f₁ p) 0) +
          Real.smoothMax ε (f₁ p) 0 / f₁ (b 2) - b.coord 2 p)
      let H := fun q : ℝ × Plane => (1 - q.1) * (F q.2).1 + q.1 * (F q.2).2
      0 < ε ∧ ContDiff ℝ ∞ F ∧ IsOpen U₀ ∧ IsOpen U₁ ∧ IsOpen V ∧
      b 0 ∈ U₀ ∧ b 1 ∈ U₁ ∧ Disjoint U₀ U₁ ∧
      M.triangleCarrier T.1 ⊆ U₀ ∪ U₁ ∪ V ∧
      segment ℝ (b 0) v₀ ⊆ R ∧ segment ℝ (b 1) v₁ ⊆ R ∧
      f₀ (b 0) = 0 ∧ 0 < f₀ (b 1) ∧ 0 < f₀ (b 2) ∧ f₀ v₀ < 0 ∧
      f₁ (b 1) = 0 ∧ 0 < f₁ (b 0) ∧ 0 < f₁ (b 2) ∧ f₁ v₁ < 0 ∧
      (∀ p ∈ U₀, (1 : ℝ) / 4 < b.coord 0 p - b.coord 1 p) ∧
      (∀ p ∈ U₁, (1 : ℝ) / 4 < b.coord 1 p - b.coord 0 p) ∧
      Set.EqOn F (fun p => (A₀ p, B₀ p)) U₀ ∧
      Set.EqOn F (fun p => (A₁ p, B₁ p)) U₁ ∧
      Set.EqOn F (fun p => (-b.coord 2 p,
        -Real.smoothMax σ (-b.coord 0 p) (-b.coord 1 p))) V ∧
      (∀ p ∈ U₀,
        (p ∈ M.toPlaneComplex.support ↔
          (if f₀ p < 0 then b.coord 2 v₀ / f₀ v₀ * f₀ p else 0) ≤ b.coord 2 p) ∧
        (p ∈ interior M.toPlaneComplex.support ↔
          (if f₀ p < 0 then b.coord 2 v₀ / f₀ v₀ * f₀ p else 0) < b.coord 2 p) ∧
        (p ∈ frontier M.toPlaneComplex.support ↔
          b.coord 2 p = if f₀ p < 0 then b.coord 2 v₀ / f₀ v₀ * f₀ p else 0) ∧
        (p ∈ (M.eraseTriangle T.1).toPlaneComplex.support ↔
          (if f₀ p < 0 then b.coord 2 v₀ / f₀ v₀ * f₀ p else f₀ p / f₀ (b 2)) ≤
            b.coord 2 p) ∧
        (p ∈ interior (M.eraseTriangle T.1).toPlaneComplex.support ↔
          (if f₀ p < 0 then b.coord 2 v₀ / f₀ v₀ * f₀ p else f₀ p / f₀ (b 2)) <
            b.coord 2 p) ∧
        (p ∈ frontier (M.eraseTriangle T.1).toPlaneComplex.support ↔
          b.coord 2 p = if f₀ p < 0 then b.coord 2 v₀ / f₀ v₀ * f₀ p else
            f₀ p / f₀ (b 2))) ∧
      (∀ p ∈ U₁,
        (p ∈ M.toPlaneComplex.support ↔
          (if f₁ p < 0 then b.coord 2 v₁ / f₁ v₁ * f₁ p else 0) ≤ b.coord 2 p) ∧
        (p ∈ interior M.toPlaneComplex.support ↔
          (if f₁ p < 0 then b.coord 2 v₁ / f₁ v₁ * f₁ p else 0) < b.coord 2 p) ∧
        (p ∈ frontier M.toPlaneComplex.support ↔
          b.coord 2 p = if f₁ p < 0 then b.coord 2 v₁ / f₁ v₁ * f₁ p else 0) ∧
        (p ∈ (M.eraseTriangle T.1).toPlaneComplex.support ↔
          (if f₁ p < 0 then b.coord 2 v₁ / f₁ v₁ * f₁ p else f₁ p / f₁ (b 2)) ≤
            b.coord 2 p) ∧
        (p ∈ interior (M.eraseTriangle T.1).toPlaneComplex.support ↔
          (if f₁ p < 0 then b.coord 2 v₁ / f₁ v₁ * f₁ p else f₁ p / f₁ (b 2)) <
            b.coord 2 p) ∧
        (p ∈ frontier (M.eraseTriangle T.1).toPlaneComplex.support ↔
          b.coord 2 p = if f₁ p < 0 then b.coord 2 v₁ / f₁ v₁ * f₁ p else
            f₁ p / f₁ (b 2))) ∧
      (∀ p ∈ U₀ ∪ U₁ ∪ V,
        fderiv ℝ (fun q => (F q).1) p ≠ 0 ∧
          fderiv ℝ (fun q => (F q).2) p ≠ 0) ∧
      ContDiff ℝ ∞ H ∧
      (∀ t p, deriv (fun s => H (s, p)) t = (F p).2 - (F p).1) ∧
      (∀ p, H (0, p) = (F p).1) ∧
      (∀ p, H (1, p) = (F p).2) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀ ∪ U₁ ∪ V,
        fderiv ℝ (fun q => H (t, q)) p ≠ 0) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀, f₀ p ≤ -ε → H (t, p) = 0 →
        (F p).1 = 0 ∧ (F p).2 = 0 ∧ (∀ u : ℝ, H (u, p) = 0) ∧
          (∀ u : ℝ, deriv (fun s => H (s, p)) u = 0)) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₁, f₁ p ≤ -ε → H (t, p) = 0 →
        (F p).1 = 0 ∧ (F p).2 = 0 ∧ (∀ u : ℝ, H (u, p) = 0) ∧
          (∀ u : ℝ, deriv (fun s => H (s, p)) u = 0)) ∧
      (∀ p ∈ V, ε < f₀ p ∧ ε < f₁ p) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ V, H (t, p) = 0 →
        p ∈ M.triangleCarrier T.1) ∧
      ∃ J : Set Plane, IsCompact J ∧ M.triangleCarrier T.1 ⊆ interior J ∧
        J ⊆ U₀ ∪ U₁ ∪ V ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀ ∪ U₁ ∪ V,
          H (t, p) = 0 → deriv (fun u => H (u, p)) t ≠ 0 → p ∈ interior J) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀,
          H (t, p) = 0 → -ε ≤ f₀ p → p ∈ interior J) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₁,
          H (t, p) = 0 → -ε ≤ f₁ p → p ∈ interior J) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀ ∪ U₁ ∪ V, H (t, p) = 0 → p ∉ J →
          (p ∈ U₀ ∧ f₀ p < -ε ∧ ∃ N : Set Plane,
            IsOpen N ∧ p ∈ N ∧ N ⊆ U₀ ∩ {q | f₀ q < -ε} ∧
              Set.EqOn (fun q => (F q).2) (fun q => f₀ (b 2) / f₀ (b 1) * (F q).1) N) ∨
          (p ∈ U₁ ∧ f₁ p < -ε ∧ ∃ N : Set Plane,
            IsOpen N ∧ p ∈ N ∧ N ⊆ U₁ ∩ {q | f₁ q < -ε} ∧
              Set.EqOn (fun q => (F q).2) (fun q => f₁ (b 2) / f₁ (b 0) * (F q).1) N)) ∧
        (∀ p ∈ V,
          (p ∈ M.toPlaneComplex.support ↔ 0 ≤ b.coord 2 p) ∧
          (p ∈ interior M.toPlaneComplex.support ↔ 0 < b.coord 2 p) ∧
          (p ∈ frontier M.toPlaneComplex.support ↔ b.coord 2 p = 0)) ∧
        (∀ p ∈ U₀ ∪ U₁ ∪ V, p ∉ interior J →
          (p ∈ M.toPlaneComplex.support ↔ (F p).1 ≤ 0) ∧
          (p ∈ interior M.toPlaneComplex.support ↔ (F p).1 < 0) ∧
          (p ∈ frontier M.toPlaneComplex.support ↔ (F p).1 = 0)) ∧
        (∀ p ∈ U₀ ∪ U₁ ∪ V, p ∉ interior J →
          (p ∈ (M.eraseTriangle T.1).toPlaneComplex.support ↔ (F p).2 ≤ 0) ∧
          (p ∈ interior (M.eraseTriangle T.1).toPlaneComplex.support ↔ (F p).2 < 0) ∧
          (p ∈ frontier (M.eraseTriangle T.1).toPlaneComplex.support ↔ (F p).2 = 0)) ∧
        ∃ (K : Set Plane) (X : ℝ × Plane → Plane) (Ω : Set (ℝ × Plane))
          (κ : ℝ × Plane → ℝ),
          IsCompact K ∧ J ⊆ interior K ∧ K ⊆ U₀ ∪ U₁ ∪ V ∧
          ContDiff ℝ ∞ X ∧ HasCompactSupport X ∧
          IsOpen Ω ∧ Set.Icc (0 : ℝ) 1 ×ˢ (U₀ ∪ U₁ ∪ V) ⊆ Ω ∧
          Ω ⊆ Set.univ ×ˢ (U₀ ∪ U₁ ∪ V) ∧ ContDiffOn ℝ ∞ κ Ω ∧
          (∀ z ∈ Ω,
            deriv (fun t => H (t, z.2)) z.1 +
              fderiv ℝ (fun y => H (z.1, y)) z.2 (X z) = κ z * H z) ∧
          (∀ t x, x ∉ K → X (t, x) = 0) ∧
          ∃ Φ : ℝ → (Plane ≃ₘ[ℝ] Plane),
            (∀ (hX : ContDiff ℝ ∞ X) (hsX : HasCompactSupport X) (t : ℝ),
              Φ t = Diffeomorph.timeDependentFlow X hX hsX 0 t) ∧
            ContDiff ℝ ∞ (fun q : ℝ × Plane => Φ q.1 q.2) ∧
            ContDiff ℝ ∞ (fun q : ℝ × Plane => (Φ q.1).symm q.2) ∧
            Φ 0 = Diffeomorph.refl 𝓘(ℝ, Plane) Plane ∞ ∧
            (∀ t : ℝ, Set.EqOn (Φ t) id Kᶜ ∧ Set.EqOn (Φ t).symm id Kᶜ) ∧
            (∀ t : ℝ, (∀ p, Φ t p ∈ U₀ ∪ U₁ ∪ V ↔ p ∈ U₀ ∪ U₁ ∪ V) ∧
              (∀ p, (Φ t).symm p ∈ U₀ ∪ U₁ ∪ V ↔ p ∈ U₀ ∪ U₁ ∪ V)) ∧
            (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀ ∪ U₁ ∪ V,
              ((F p).1 = 0 ↔ H (t, Φ t p) = 0) ∧
              ((F p).1 < 0 ↔ H (t, Φ t p) < 0) ∧
              ((F p).1 ≤ 0 ↔ H (t, Φ t p) ≤ 0)) ∧
            (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀ ∪ U₁ ∪ V,
              (H (t, p) = 0 ↔ (F ((Φ t).symm p)).1 = 0) ∧
              (H (t, p) < 0 ↔ (F ((Φ t).symm p)).1 < 0) ∧
              (H (t, p) ≤ 0 ↔ (F ((Φ t).symm p)).1 ≤ 0)) ∧
            let D₀ := (M.toPlaneComplex.support \ interior K) ∪
              (K ∩ {p | (F p).1 ≤ 0})
            let p := AffineMap.lineMap (b 0) (b 1) ((1 : ℝ) / 2)
            M.toPlaneComplex.support = closure (inside P.carrier) ∧
            IsCompact D₀ ∧
            (∀ q ∈ U₀ ∪ U₁ ∪ V,
              (q ∈ D₀ ↔ (F q).1 ≤ 0) ∧
              (q ∈ interior D₀ ↔ (F q).1 < 0) ∧
              (q ∈ frontier D₀ ↔ (F q).1 = 0)) ∧
            (∀ q ∉ K, q ∈ D₀ ↔ q ∈ M.toPlaneComplex.support) ∧
            p ∈ interior K ∧ p ∈ frontier D₀ ∧ (frontier D₀).Nonempty ∧
            ContDiff ℝ ∞ (fun q => -(F q).1) ∧
            (∀ q ∈ U₀ ∪ U₁ ∪ V,
              fderiv ℝ (fun z => -(F z).1) q ≠ 0) ∧
            ∀ q ∈ frontier D₀ ∩ (U₀ ∪ U₁ ∪ V),
              ∃ (N : Set Plane) (G : Plane → ℝ),
                IsOpen N ∧ q ∈ N ∧ K ⊆ N ∧ ContDiff ℝ ∞ G ∧
                (∀ z ∈ N, fderiv ℝ G z ≠ 0) ∧
                (∀ z, G z = -(F z).1) ∧
                ∀ z ∈ N, (z ∈ D₀ ↔ 0 ≤ G z) ∧
                  (z ∈ interior D₀ ↔ 0 < G z) ∧
                  (z ∈ frontier D₀ ↔ G z = 0) := by
  dsimp only
  let b := LeanEval.Topology.ClassificationOfSurfaces.Moise.affineBasisOfTriangle
    (M.freeTriangleOrder T k) (M.freeTriangleOrder_affineIndependent T k)
  let p := AffineMap.lineMap (b 0) (b 1) ((1 : ℝ) / 2)
  obtain ⟨v₀, v₁, f₀, f₁, ε, U₀, U₁, V, F,
    hε, hF, hU₀, hU₁, hV, hb₀, hb₁, hdisj, hcover, hs₀, hs₁,
    hf₀, hfb, hfc₀, hfv₀, hf₁, hfa, hfc₁, hfv₁, hgap₀, hgap₁,
    he₀, he₁, heV, hgraph₀, hgraph₁, hreg, hH, hderiv, hstart, hend,
    hregH, hstat₀, hstat₁, hposV, hcentral,
    J, hJ, htriangleJ, hJW, hactive, hweak₀, hweak₁, hexterior, hraw, hsign, hremoved,
    K, X, Ω, κ, hK, hJK, hKW, hX, hsX, hΩ, hΩcover, hΩW, hκ, htransport, hXzero,
    Φ, hΦeq, hΦ, hΦinv, hΦzero, hΦfix, hΦW, hforward, hinverse⟩ :=
    P.exists_compactly_supported_isotopy_near_one_edge_free_triangle
      M hfrontier T k hfree hσ hσsmall
  let W := U₀ ∪ U₁ ∪ V
  let D₀ := (M.toPlaneComplex.support \ interior K) ∪ (K ∩ {q | (F q).1 ≤ 0})
  have hW : IsOpen W := (hU₀.union hU₁).union hV
  have hregneg (q : Plane) (hq : q ∈ W) :
      fderiv ℝ (fun z => -(F z).1) q ≠ 0 := by
    simpa only [fderiv_fun_neg, neg_ne_zero] using (hreg q hq).1
  obtain ⟨hcompact, hlocal, hout⟩ := compact_region_replace_preserving_germ
    M.toPlaneComplex.isCompact_support hK hW hKW hF.fst.neg.continuous
    (fun q hq _ => hregneg q hq) (by
      intro q hq
      simpa only [neg_nonneg] using
        (hsign q hq.1 (fun hqJ => hq.2 (hJK (interior_subset hqJ)))).1)
  have hD₀ : IsCompact D₀ := by
    simpa only [D₀, neg_nonneg] using hcompact
  have hsides (q : Plane) (hq : q ∈ W) :
      (q ∈ D₀ ↔ (F q).1 ≤ 0) ∧
      (q ∈ interior D₀ ↔ (F q).1 < 0) ∧
      (q ∈ frontier D₀ ↔ (F q).1 = 0) := by
    simpa only [D₀, neg_nonneg, neg_pos, neg_eq_zero] using hlocal q hq
  have houtside (q : Plane) (hq : q ∉ K) :
      q ∈ D₀ ↔ q ∈ M.toPlaneComplex.support := by
    simpa only [D₀, neg_nonneg] using hout q hq
  have hcoords (i : Fin 3) : b.coord i p =
      (1 - (1 : ℝ) / 2) * b.coord i (b 0) + (1 / 2) * b.coord i (b 1) := by
    change b.coord i (AffineMap.lineMap (b 0) (b 1) ((1 : ℝ) / 2)) = _
    rw [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring]
  have hp₀ : b.coord 0 p = 1 / 2 := by norm_num [hcoords, b.coord_apply, Fin.ext_iff]
  have hp₁ : b.coord 1 p = 1 / 2 := by norm_num [hcoords, b.coord_apply, Fin.ext_iff]
  have hp₂ : b.coord 2 p = 0 := by norm_num [hcoords, b.coord_apply, Fin.ext_iff]
  have hpbase : p ∈ segment ℝ (b 0) (b 1) :=
    lineMap_mem_segment ℝ _ _ (show (1 : ℝ) / 2 ∈ Set.Icc 0 1 from
      ⟨by norm_num, by norm_num⟩)
  have hfree' : frontier M.toPlaneComplex.support ∩ M.triangleCarrier T.1 =
      segment ℝ (b 0) (b 1) := hfree
  have hpT : p ∈ M.triangleCarrier T.1 := (hfree'.symm ▸ hpbase).2
  have hpV : p ∈ V := by
    rcases hcover hpT with (hpU₀ | hpU₁) | hpV
    · have h := hgap₀ p hpU₀
      rw [hp₀, hp₁, sub_self] at h
      norm_num at h
    · have h := hgap₁ p hpU₁
      rw [hp₁, hp₀, sub_self] at h
      norm_num at h
    · exact hpV
  have hpzero : (F p).1 = 0 := by
    have h : (F p).1 = -b.coord 2 p := congrArg Prod.fst (heV hpV)
    rw [h, hp₂, neg_zero]
  have hpfront : p ∈ frontier D₀ := (hsides p (Or.inr hpV)).2.2.mpr hpzero
  have hTsub : M.triangleCarrier T.1 ⊆ M.toPlaneComplex.support := by
    rw [M.toPlaneComplex_support]
    exact Set.subset_iUnion_of_subset T.1 (Set.subset_iUnion_of_subset T.2 Set.Subset.rfl)
  have hsupport : M.toPlaneComplex.support = closure (inside P.carrier) :=
    eq_closure_inside_of_isCompact_frontier_eq P.isSeparating_carrier
      M.toPlaneComplex.isCompact_support hfrontier
      ((M.interior_triangleCarrier_nonempty T).mono (interior_mono hTsub))
  refine ⟨v₀, v₁, f₀, f₁, ε, U₀, U₁, V, F,
    hε, hF, hU₀, hU₁, hV, hb₀, hb₁, hdisj, hcover, hs₀, hs₁,
    hf₀, hfb, hfc₀, hfv₀, hf₁, hfa, hfc₁, hfv₁, hgap₀, hgap₁,
    he₀, he₁, heV, hgraph₀, hgraph₁, hreg, hH, hderiv, hstart, hend,
    hregH, hstat₀, hstat₁, hposV, hcentral,
    J, hJ, htriangleJ, hJW, hactive, hweak₀, hweak₁, hexterior, hraw, hsign, hremoved,
    K, X, Ω, κ, hK, hJK, hKW, hX, hsX, hΩ, hΩcover, hΩW, hκ, htransport, hXzero,
    Φ, hΦeq, hΦ, hΦinv, hΦzero, hΦfix, hΦW, hforward, hinverse, hsupport, hD₀, hsides, houtside,
    hJK (interior_subset (htriangleJ hpT)), hpfront, ⟨p, hpfront⟩,
    hF.fst.neg, hregneg, ?_⟩
  intro q hq
  refine ⟨W, (fun z => -(F z).1), hW, hq.2, hKW, hF.fst.neg, hregneg,
    fun _ => rfl, ?_⟩
  intro z hz
  simpa only [neg_nonneg, neg_pos, neg_eq_zero] using hsides z hz

end Schoenflies

end

section

namespace Schoenflies

private theorem PrePolygon.exists_compact_neighborhood_of_vertices_outside
    {m : ℕ} (P : PrePolygon m) {K W : Set Plane} (hK : IsClosed K) (hKW : K ⊆ W) :
    ∃ O : Set Plane, IsOpen O ∧ IsCompact (closure O) ∧ closure O ⊆ Kᶜ ∧
      ∀ i : ZMod (m + 3), P.vertex i ∉ W → P.vertex i ∈ O := by
  let I := {i : ZMod (m + 3) // P.vertex i ∉ W}
  let Q := Set.range (fun i : I => P.vertex i.val)
  have hQ : IsCompact Q := (Set.finite_range _).isCompact
  have hQK : Q ⊆ Kᶜ := by
    rintro _ ⟨i, rfl⟩ hp
    exact i.property (hKW hp)
  obtain ⟨ρ, hρ, hρQ⟩ := hQ.exists_cthickening_subset_open hK.isOpen_compl hQK
  let O := Metric.thickening ρ Q
  have hclosure : closure O ⊆ Metric.cthickening ρ Q :=
    Metric.closure_thickening_subset_cthickening ρ Q
  refine ⟨O, Metric.isOpen_thickening,
    hQ.cthickening.of_isClosed_subset isClosed_closure hclosure, hclosure.trans hρQ, ?_⟩
  intro i hi
  exact Metric.self_subset_thickening hρ Q (Set.mem_range_self (⟨i, hi⟩ : I))

end Schoenflies

end

section

open scoped ContDiff Manifold Topology

namespace Schoenflies

private theorem PrePolygon.native_global_rounding_with_prescribed_isotopy
    {m : ℕ} (P : PrePolygon m)
    (M : LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh)
    (hfrontier : frontier M.toPlaneComplex.support = P.carrier)
    (T : M.Triangle) (k : Fin 3) (hfree : M.IsOneEdgeFreeTriangle T k)
    {σ : ℝ} (hσ : 0 < σ) (hσsmall : σ ≤ 1 / 4) :
    let b := LeanEval.Topology.ClassificationOfSurfaces.Moise.affineBasisOfTriangle
      (M.freeTriangleOrder T k) (M.freeTriangleOrder_affineIndependent T k)
    let R := closure (P.carrier \ segment ℝ (b 0) (b 1))
    ∃ (v₀ v₁ : Plane) (f₀ f₁ : Plane →ᵃ[ℝ] ℝ) (ε : ℝ)
      (U₀ U₁ V : Set Plane) (F : Plane → ℝ × ℝ),
      let s₀ := b.coord 2 v₀ / f₀ v₀
      let s₁ := b.coord 2 v₁ / f₁ v₁
      let A₀ := fun p => s₀ * (f₀ p - Real.smoothMax ε (f₀ p) 0) - b.coord 2 p
      let A₁ := fun p => s₁ * (f₁ p - Real.smoothMax ε (f₁ p) 0) - b.coord 2 p
      let B₀ := fun p => f₀ (b 2) / f₀ (b 1) *
        (s₀ * (f₀ p - Real.smoothMax ε (f₀ p) 0) +
          Real.smoothMax ε (f₀ p) 0 / f₀ (b 2) - b.coord 2 p)
      let B₁ := fun p => f₁ (b 2) / f₁ (b 0) *
        (s₁ * (f₁ p - Real.smoothMax ε (f₁ p) 0) +
          Real.smoothMax ε (f₁ p) 0 / f₁ (b 2) - b.coord 2 p)
      let H := fun q : ℝ × Plane => (1 - q.1) * (F q.2).1 + q.1 * (F q.2).2
      0 < ε ∧ ContDiff ℝ ∞ F ∧ IsOpen U₀ ∧ IsOpen U₁ ∧ IsOpen V ∧
      b 0 ∈ U₀ ∧ b 1 ∈ U₁ ∧ Disjoint U₀ U₁ ∧
      M.triangleCarrier T.1 ⊆ U₀ ∪ U₁ ∪ V ∧
      segment ℝ (b 0) v₀ ⊆ R ∧ segment ℝ (b 1) v₁ ⊆ R ∧
      f₀ (b 0) = 0 ∧ 0 < f₀ (b 1) ∧ 0 < f₀ (b 2) ∧ f₀ v₀ < 0 ∧
      f₁ (b 1) = 0 ∧ 0 < f₁ (b 0) ∧ 0 < f₁ (b 2) ∧ f₁ v₁ < 0 ∧
      (∀ p ∈ U₀, (1 : ℝ) / 4 < b.coord 0 p - b.coord 1 p) ∧
      (∀ p ∈ U₁, (1 : ℝ) / 4 < b.coord 1 p - b.coord 0 p) ∧
      Set.EqOn F (fun p => (A₀ p, B₀ p)) U₀ ∧
      Set.EqOn F (fun p => (A₁ p, B₁ p)) U₁ ∧
      Set.EqOn F (fun p => (-b.coord 2 p,
        -Real.smoothMax σ (-b.coord 0 p) (-b.coord 1 p))) V ∧
      (∀ p ∈ U₀,
        (p ∈ M.toPlaneComplex.support ↔
          (if f₀ p < 0 then b.coord 2 v₀ / f₀ v₀ * f₀ p else 0) ≤ b.coord 2 p) ∧
        (p ∈ interior M.toPlaneComplex.support ↔
          (if f₀ p < 0 then b.coord 2 v₀ / f₀ v₀ * f₀ p else 0) < b.coord 2 p) ∧
        (p ∈ frontier M.toPlaneComplex.support ↔
          b.coord 2 p = if f₀ p < 0 then b.coord 2 v₀ / f₀ v₀ * f₀ p else 0) ∧
        (p ∈ (M.eraseTriangle T.1).toPlaneComplex.support ↔
          (if f₀ p < 0 then b.coord 2 v₀ / f₀ v₀ * f₀ p else f₀ p / f₀ (b 2)) ≤
            b.coord 2 p) ∧
        (p ∈ interior (M.eraseTriangle T.1).toPlaneComplex.support ↔
          (if f₀ p < 0 then b.coord 2 v₀ / f₀ v₀ * f₀ p else f₀ p / f₀ (b 2)) <
            b.coord 2 p) ∧
        (p ∈ frontier (M.eraseTriangle T.1).toPlaneComplex.support ↔
          b.coord 2 p = if f₀ p < 0 then b.coord 2 v₀ / f₀ v₀ * f₀ p else
            f₀ p / f₀ (b 2))) ∧
      (∀ p ∈ U₁,
        (p ∈ M.toPlaneComplex.support ↔
          (if f₁ p < 0 then b.coord 2 v₁ / f₁ v₁ * f₁ p else 0) ≤ b.coord 2 p) ∧
        (p ∈ interior M.toPlaneComplex.support ↔
          (if f₁ p < 0 then b.coord 2 v₁ / f₁ v₁ * f₁ p else 0) < b.coord 2 p) ∧
        (p ∈ frontier M.toPlaneComplex.support ↔
          b.coord 2 p = if f₁ p < 0 then b.coord 2 v₁ / f₁ v₁ * f₁ p else 0) ∧
        (p ∈ (M.eraseTriangle T.1).toPlaneComplex.support ↔
          (if f₁ p < 0 then b.coord 2 v₁ / f₁ v₁ * f₁ p else f₁ p / f₁ (b 2)) ≤
            b.coord 2 p) ∧
        (p ∈ interior (M.eraseTriangle T.1).toPlaneComplex.support ↔
          (if f₁ p < 0 then b.coord 2 v₁ / f₁ v₁ * f₁ p else f₁ p / f₁ (b 2)) <
            b.coord 2 p) ∧
        (p ∈ frontier (M.eraseTriangle T.1).toPlaneComplex.support ↔
          b.coord 2 p = if f₁ p < 0 then b.coord 2 v₁ / f₁ v₁ * f₁ p else
            f₁ p / f₁ (b 2))) ∧
      (∀ p ∈ U₀ ∪ U₁ ∪ V,
        fderiv ℝ (fun q => (F q).1) p ≠ 0 ∧
          fderiv ℝ (fun q => (F q).2) p ≠ 0) ∧
      ContDiff ℝ ∞ H ∧
      (∀ t p, deriv (fun s => H (s, p)) t = (F p).2 - (F p).1) ∧
      (∀ p, H (0, p) = (F p).1) ∧
      (∀ p, H (1, p) = (F p).2) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀ ∪ U₁ ∪ V,
        fderiv ℝ (fun q => H (t, q)) p ≠ 0) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀, f₀ p ≤ -ε → H (t, p) = 0 →
        (F p).1 = 0 ∧ (F p).2 = 0 ∧ (∀ u : ℝ, H (u, p) = 0) ∧
          (∀ u : ℝ, deriv (fun s => H (s, p)) u = 0)) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₁, f₁ p ≤ -ε → H (t, p) = 0 →
        (F p).1 = 0 ∧ (F p).2 = 0 ∧ (∀ u : ℝ, H (u, p) = 0) ∧
          (∀ u : ℝ, deriv (fun s => H (s, p)) u = 0)) ∧
      (∀ p ∈ V, ε < f₀ p ∧ ε < f₁ p) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ V, H (t, p) = 0 →
        p ∈ M.triangleCarrier T.1) ∧
      ∃ J : Set Plane, IsCompact J ∧ M.triangleCarrier T.1 ⊆ interior J ∧
        J ⊆ U₀ ∪ U₁ ∪ V ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀ ∪ U₁ ∪ V,
          H (t, p) = 0 → deriv (fun u => H (u, p)) t ≠ 0 → p ∈ interior J) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀,
          H (t, p) = 0 → -ε ≤ f₀ p → p ∈ interior J) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₁,
          H (t, p) = 0 → -ε ≤ f₁ p → p ∈ interior J) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀ ∪ U₁ ∪ V, H (t, p) = 0 → p ∉ J →
          (p ∈ U₀ ∧ f₀ p < -ε ∧ ∃ N : Set Plane,
            IsOpen N ∧ p ∈ N ∧ N ⊆ U₀ ∩ {q | f₀ q < -ε} ∧
              Set.EqOn (fun q => (F q).2) (fun q => f₀ (b 2) / f₀ (b 1) * (F q).1) N) ∨
          (p ∈ U₁ ∧ f₁ p < -ε ∧ ∃ N : Set Plane,
            IsOpen N ∧ p ∈ N ∧ N ⊆ U₁ ∩ {q | f₁ q < -ε} ∧
              Set.EqOn (fun q => (F q).2) (fun q => f₁ (b 2) / f₁ (b 0) * (F q).1) N)) ∧
        (∀ p ∈ V,
          (p ∈ M.toPlaneComplex.support ↔ 0 ≤ b.coord 2 p) ∧
          (p ∈ interior M.toPlaneComplex.support ↔ 0 < b.coord 2 p) ∧
          (p ∈ frontier M.toPlaneComplex.support ↔ b.coord 2 p = 0)) ∧
        (∀ p ∈ U₀ ∪ U₁ ∪ V, p ∉ interior J →
          (p ∈ M.toPlaneComplex.support ↔ (F p).1 ≤ 0) ∧
          (p ∈ interior M.toPlaneComplex.support ↔ (F p).1 < 0) ∧
          (p ∈ frontier M.toPlaneComplex.support ↔ (F p).1 = 0)) ∧
        (∀ p ∈ U₀ ∪ U₁ ∪ V, p ∉ interior J →
          (p ∈ (M.eraseTriangle T.1).toPlaneComplex.support ↔ (F p).2 ≤ 0) ∧
          (p ∈ interior (M.eraseTriangle T.1).toPlaneComplex.support ↔ (F p).2 < 0) ∧
          (p ∈ frontier (M.eraseTriangle T.1).toPlaneComplex.support ↔ (F p).2 = 0)) ∧
        ∃ (K : Set Plane) (X : ℝ × Plane → Plane) (Ω : Set (ℝ × Plane))
          (κ : ℝ × Plane → ℝ),
          IsCompact K ∧ J ⊆ interior K ∧ K ⊆ U₀ ∪ U₁ ∪ V ∧
          ContDiff ℝ ∞ X ∧ HasCompactSupport X ∧
          IsOpen Ω ∧ Set.Icc (0 : ℝ) 1 ×ˢ (U₀ ∪ U₁ ∪ V) ⊆ Ω ∧
          Ω ⊆ Set.univ ×ˢ (U₀ ∪ U₁ ∪ V) ∧ ContDiffOn ℝ ∞ κ Ω ∧
          (∀ z ∈ Ω,
            deriv (fun t => H (t, z.2)) z.1 +
              fderiv ℝ (fun y => H (z.1, y)) z.2 (X z) = κ z * H z) ∧
          (∀ t x, x ∉ K → X (t, x) = 0) ∧
          ∃ Φ : ℝ → (Plane ≃ₘ[ℝ] Plane),
            (∀ (hX : ContDiff ℝ ∞ X) (hsX : HasCompactSupport X) (t : ℝ),
              Φ t = Diffeomorph.timeDependentFlow X hX hsX 0 t) ∧
            ContDiff ℝ ∞ (fun q : ℝ × Plane => Φ q.1 q.2) ∧
            ContDiff ℝ ∞ (fun q : ℝ × Plane => (Φ q.1).symm q.2) ∧
            Φ 0 = Diffeomorph.refl 𝓘(ℝ, Plane) Plane ∞ ∧
            (∀ t : ℝ, Set.EqOn (Φ t) id Kᶜ ∧ Set.EqOn (Φ t).symm id Kᶜ) ∧
            (∀ t : ℝ, (∀ p, Φ t p ∈ U₀ ∪ U₁ ∪ V ↔ p ∈ U₀ ∪ U₁ ∪ V) ∧
              (∀ p, (Φ t).symm p ∈ U₀ ∪ U₁ ∪ V ↔ p ∈ U₀ ∪ U₁ ∪ V)) ∧
            (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀ ∪ U₁ ∪ V,
              ((F p).1 = 0 ↔ H (t, Φ t p) = 0) ∧
              ((F p).1 < 0 ↔ H (t, Φ t p) < 0) ∧
              ((F p).1 ≤ 0 ↔ H (t, Φ t p) ≤ 0)) ∧
            (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀ ∪ U₁ ∪ V,
              (H (t, p) = 0 ↔ (F ((Φ t).symm p)).1 = 0) ∧
              (H (t, p) < 0 ↔ (F ((Φ t).symm p)).1 < 0) ∧
              (H (t, p) ≤ 0 ↔ (F ((Φ t).symm p)).1 ≤ 0)) ∧
            let D₀ := (M.toPlaneComplex.support \ interior K) ∪
              (K ∩ {p | (F p).1 ≤ 0})
            let p := AffineMap.lineMap (b 0) (b 1) ((1 : ℝ) / 2)
            M.toPlaneComplex.support = closure (inside P.carrier) ∧
            IsCompact D₀ ∧
            (∀ q ∈ U₀ ∪ U₁ ∪ V,
              (q ∈ D₀ ↔ (F q).1 ≤ 0) ∧
              (q ∈ interior D₀ ↔ (F q).1 < 0) ∧
              (q ∈ frontier D₀ ↔ (F q).1 = 0)) ∧
            (∀ q ∉ K, q ∈ D₀ ↔ q ∈ M.toPlaneComplex.support) ∧
            p ∈ interior K ∧ p ∈ frontier D₀ ∧ (frontier D₀).Nonempty ∧
            ContDiff ℝ ∞ (fun q => -(F q).1) ∧
            (∀ q ∈ U₀ ∪ U₁ ∪ V,
              fderiv ℝ (fun z => -(F z).1) q ≠ 0) ∧
            (∀ q ∈ frontier D₀ ∩ (U₀ ∪ U₁ ∪ V),
              ∃ (N : Set Plane) (G : Plane → ℝ),
                IsOpen N ∧ q ∈ N ∧ K ⊆ N ∧ ContDiff ℝ ∞ G ∧
                (∀ z ∈ N, fderiv ℝ G z ≠ 0) ∧
                (∀ z, G z = -(F z).1) ∧
                ∀ z ∈ N, (z ∈ D₀ ↔ 0 ≤ G z) ∧
                  (z ∈ interior D₀ ↔ 0 < G z) ∧
                  (z ∈ frontier D₀ ↔ G z = 0)) ∧
            ∃ (O V₁ D₁ : Set Plane),
              IsOpen O ∧ IsCompact (closure O) ∧ closure O ⊆ Kᶜ ∧
              (∀ i : ZMod (m + 3), P.vertex i ∉ U₀ ∪ U₁ ∪ V → P.vertex i ∈ O) ∧
              IsCompact D₁ ∧ IsOpen V₁ ∧ K ⊆ V₁ ∧ V₁ ⊆ U₀ ∪ U₁ ∪ V ∧
              (∀ q ∈ V₁, (q ∈ D₁ ↔ q ∈ D₀) ∧
                (q ∈ interior D₁ ↔ q ∈ interior D₀) ∧
                (q ∈ frontier D₁ ↔ q ∈ frontier D₀)) ∧
              (∀ q ∉ O, (q ∈ D₁ ↔ q ∈ D₀) ∧
                (q ∈ interior D₁ ↔ q ∈ interior D₀) ∧
                (q ∈ frontier D₁ ↔ q ∈ frontier D₀)) ∧
              (∀ q ∉ K ∪ O, q ∈ D₁ ↔ q ∈ M.toPlaneComplex.support) ∧
              (∀ q ∈ V₁, (q ∈ D₁ ↔ (F q).1 ≤ 0) ∧
                (q ∈ interior D₁ ↔ (F q).1 < 0) ∧
                (q ∈ frontier D₁ ↔ (F q).1 = 0)) ∧
              p ∈ frontier D₁ ∧ (frontier D₁).Nonempty ∧
              ∀ q ∈ frontier D₁, ∃ (N : Set Plane) (G : Plane → ℝ),
                IsOpen N ∧ q ∈ N ∧ ContDiff ℝ ∞ G ∧ fderiv ℝ G q ≠ 0 ∧
                ∀ z ∈ N, (z ∈ D₁ ↔ 0 ≤ G z) ∧
                  (z ∈ interior D₁ ↔ 0 < G z) ∧
                  (z ∈ frontier D₁ ↔ G z = 0) := by
  dsimp only
  let b := LeanEval.Topology.ClassificationOfSurfaces.Moise.affineBasisOfTriangle
    (M.freeTriangleOrder T k) (M.freeTriangleOrder_affineIndependent T k)
  let p := AffineMap.lineMap (b 0) (b 1) ((1 : ℝ) / 2)
  obtain ⟨v₀, v₁, f₀, f₁, ε, U₀, U₁, V, F,
    hε, hF, hU₀, hU₁, hV, hb₀, hb₁, hdisj, hcover, hs₀, hs₁,
    hf₀, hfb, hfc₀, hfv₀, hf₁, hfa, hfc₁, hfv₁, hgap₀, hgap₁,
    he₀, he₁, heV, hgraph₀, hgraph₁, hreg, hH, hderiv, hstart, hend,
    hregH, hstat₀, hstat₁, hposV, hcentral,
    J, hJ, htriangleJ, hJW, hactive, hweak₀, hweak₁, hexterior, hraw, hsign, hremoved,
    K, X, Ω, κ, hK, hJK, hKW, hX, hsX, hΩ, hΩcover, hΩW, hκ, htransport, hXzero,
    Φ, hΦeq, hΦ, hΦinv, hΦzero, hΦfix, hΦW, hforward, hinverse,
    hsupport, hD₀, hsides, hout, hpK, hpfront, hnonempty, hHneg, hregneg, hgerms⟩ :=
    P.native_compact_region_with_prescribed_isotopy M hfrontier T k hfree hσ hσsmall
  let W := U₀ ∪ U₁ ∪ V
  let D₀ := (M.toPlaneComplex.support \ interior K) ∪ (K ∩ {q | (F q).1 ≤ 0})
  have hW : IsOpen W := (hU₀.union hU₁).union hV
  obtain ⟨O, hO, hOc, hOK, hvO⟩ := P.exists_compact_neighborhood_of_vertices_outside hK.isClosed hKW
  have hold (q : Plane) (hq : q ∉ K) : q ∈ D₀ ↔ q ∈ closure (inside P.carrier) := by
    rw [← hsupport]
    exact hout q hq
  have hgood (q : Plane) (hq : q ∈ frontier D₀) (hqW : q ∈ W) :
      ∃ (N : Set Plane) (G : Plane → ℝ), IsOpen N ∧ q ∈ N ∧
        ContDiff ℝ ∞ G ∧ fderiv ℝ G q ≠ 0 ∧
        ∀ z ∈ N, (z ∈ D₀ ↔ 0 ≤ G z) ∧
          (z ∈ interior D₀ ↔ 0 < G z) ∧ (z ∈ frontier D₀ ↔ G z = 0) := by
    obtain ⟨N, G, hN, hqN, _, hG, hGreg, _, hGside⟩ := hgerms q ⟨hq, hqW⟩
    exact ⟨N, G, hN, hqN, hG, hGreg q hqN, hGside⟩
  obtain ⟨D₁, V₁, hD₁, hV₁, hKV₁, hV₁W, heq, houtO, hregular⟩ :=
    P.exists_relative_compact_rounding hD₀ hK.isClosed hW hKW hO hvO hold hgood
  have hprescribed (q : Plane) (hq : q ∈ V₁) :
      (q ∈ D₁ ↔ (F q).1 ≤ 0) ∧
      (q ∈ interior D₁ ↔ (F q).1 < 0) ∧
      (q ∈ frontier D₁ ↔ (F q).1 = 0) :=
    ⟨(heq q hq).1.trans (hsides q (hV₁W hq)).1,
      (heq q hq).2.1.trans (hsides q (hV₁W hq)).2.1,
      (heq q hq).2.2.trans (hsides q (hV₁W hq)).2.2⟩
  have hpD₁ : p ∈ frontier D₁ :=
    (heq p (hKV₁ (interior_subset hpK))).2.2.mpr hpfront
  refine ⟨v₀, v₁, f₀, f₁, ε, U₀, U₁, V, F,
    hε, hF, hU₀, hU₁, hV, hb₀, hb₁, hdisj, hcover, hs₀, hs₁,
    hf₀, hfb, hfc₀, hfv₀, hf₁, hfa, hfc₁, hfv₁, hgap₀, hgap₁,
    he₀, he₁, heV, hgraph₀, hgraph₁, hreg, hH, hderiv, hstart, hend,
    hregH, hstat₀, hstat₁, hposV, hcentral,
    J, hJ, htriangleJ, hJW, hactive, hweak₀, hweak₁, hexterior, hraw, hsign, hremoved,
    K, X, Ω, κ, hK, hJK, hKW, hX, hsX, hΩ, hΩcover, hΩW, hκ, htransport, hXzero,
    Φ, hΦeq, hΦ, hΦinv, hΦzero, hΦfix, hΦW, hforward, hinverse,
    hsupport, hD₀, hsides, hout, hpK, hpfront, hnonempty, hHneg, hregneg, hgerms,
    O, V₁, D₁, hO, hOc, hOK, hvO, hD₁, hV₁, hKV₁, hV₁W, heq, houtO, ?_,
    hprescribed, hpD₁, ⟨p, hpD₁⟩, hregular⟩
  intro q hq
  have hqK : q ∉ K := fun h => hq (Or.inl h)
  have hqO : q ∉ O := fun h => hq (Or.inr h)
  exact (houtO q hqO).1.trans (hout q hqK)

end Schoenflies

end

section

open Set
open scoped ContDiff Manifold Topology

namespace Diffeomorph

private theorem fderiv_comp_symm_ne_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : E ≃ₘ[ℝ] E) {G : E → ℝ} (hG : ContDiff ℝ ∞ G)
    {p : E} (hp : fderiv ℝ G p ≠ 0) : fderiv ℝ (G ∘ e.symm) (e p) ≠ 0 := by
  intro hz
  have hc := fderiv_comp p
    ((hG.comp e.symm.contDiff).differentiable (by simp)).differentiableAt
    (e.contDiff.differentiable (by simp)).differentiableAt
  have he : (G ∘ e.symm) ∘ e = G := by
    funext q
    simp only [Function.comp_apply, Diffeomorph.symm_apply_apply]
  rw [he, hz, ContinuousLinearMap.zero_comp] at hc
  exact hp hc

private theorem regular_frontier_image
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : E ≃ₘ[ℝ] E) {D : Set E}
    (hD : ∀ p ∈ frontier D, ∃ (N : Set E) (G : E → ℝ),
      IsOpen N ∧ p ∈ N ∧ ContDiff ℝ ∞ G ∧ fderiv ℝ G p ≠ 0 ∧
      ∀ q ∈ N, (q ∈ D ↔ 0 ≤ G q) ∧
        (q ∈ interior D ↔ 0 < G q) ∧ (q ∈ frontier D ↔ G q = 0)) :
    ∀ p ∈ frontier (e '' D), ∃ (N : Set E) (G : E → ℝ),
      IsOpen N ∧ p ∈ N ∧ ContDiff ℝ ∞ G ∧ fderiv ℝ G p ≠ 0 ∧
      ∀ q ∈ N, (q ∈ e '' D ↔ 0 ≤ G q) ∧
        (q ∈ interior (e '' D) ↔ 0 < G q) ∧
        (q ∈ frontier (e '' D) ↔ G q = 0) := by
  have hi : interior (e '' D) = e '' interior D :=
    (e.toHomeomorph.image_interior D).symm
  have hf : frontier (e '' D) = e '' frontier D :=
    (e.toHomeomorph.image_frontier D).symm
  have hm (A : Set E) (q : E) : q ∈ e '' A ↔ e.symm q ∈ A := by
    exact Set.mem_image_equiv
  intro p hp
  obtain ⟨N, G, hN, hpN, hG, hreg, hsides⟩ := hD (e.symm p) ((hm _ p).mp (hf ▸ hp))
  refine ⟨e.symm ⁻¹' N, G ∘ e.symm, hN.preimage e.symm.continuous,
    hpN, hG.comp e.symm.contDiff, ?_, ?_⟩
  · simpa only [Diffeomorph.apply_symm_apply] using e.fderiv_comp_symm_ne_zero hG hreg
  · intro q hq
    rw [hi, hf, hm D q, hm (interior D) q, hm (frontier D) q]
    exact hsides (e.symm q) hq

end Diffeomorph

end

section

open Set

namespace Homeomorph

private theorem image_region_sides
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) {D V : Set X} {F : X → ℝ} {G : Y → ℝ}
    (hD : ∀ p ∈ V, (p ∈ D ↔ F p ≤ 0) ∧
      (p ∈ interior D ↔ F p < 0) ∧ (p ∈ frontier D ↔ F p = 0))
    (hF : ∀ p ∈ e '' V, (G p = 0 ↔ F (e.symm p) = 0) ∧
      (G p < 0 ↔ F (e.symm p) < 0) ∧ (G p ≤ 0 ↔ F (e.symm p) ≤ 0)) :
    ∀ p ∈ e '' V, (p ∈ e '' D ↔ G p ≤ 0) ∧
      (p ∈ interior (e '' D) ↔ G p < 0) ∧
      (p ∈ frontier (e '' D) ↔ G p = 0) := by
  have hm (A : Set X) (p : Y) : p ∈ e '' A ↔ e.symm p ∈ A :=
    Set.mem_image_equiv
  intro p hp
  have hd := hD (e.symm p) ((hm V p).mp hp)
  have hf := hF p hp
  rw [← e.image_interior D, ← e.image_frontier D, hm D p,
    hm (interior D) p, hm (frontier D) p]
  exact ⟨hd.1.trans hf.2.2.symm, hd.2.1.trans hf.2.1.symm, hd.2.2.trans hf.1.symm⟩

private theorem image_neighborhood_of_eqOn_compl
    {X : Type*} [TopologicalSpace X] (e : X ≃ₜ X) {K V : Set X}
    (hV : IsOpen V) (hKV : K ⊆ V) (he : EqOn e id Kᶜ) :
    IsOpen (e '' V) ∧ K ⊆ e '' V ∧
      ∀ (D : Set X) p, p ∉ K →
        (p ∈ e '' D ↔ p ∈ D) ∧
        (p ∈ interior (e '' D) ↔ p ∈ interior D) ∧
        (p ∈ frontier (e '' D) ↔ p ∈ frontier D) := by
  have hm (A : Set X) (p : X) : p ∈ e '' A ↔ e.symm p ∈ A :=
    Set.mem_image_equiv
  refine ⟨e.isOpenMap V hV, ?_, ?_⟩
  · intro p hp
    apply (hm V p).mpr
    apply hKV
    by_contra hn
    have hh : e.symm p = p := by
      simpa only [Homeomorph.apply_symm_apply, id_eq] using (he hn).symm
    exact hn (hh.symm ▸ hp)
  · intro D p hp
    have hh : e.symm p = p := by
      calc
        e.symm p = e.symm (e p) := congrArg e.symm (he hp).symm
        _ = p := e.symm_apply_apply p
    rw [← e.image_interior D, ← e.image_frontier D, hm D p,
      hm (interior D) p, hm (frontier D) p, hh]
    exact ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩

end Homeomorph

end

section

open Set

namespace Homeomorph

private theorem image_region_sides_outside_interior
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (e : X ≃ₜ X) {K : Set X} (he : EqOn e id Kᶜ) :
    ∀ (D : Set X) p, p ∉ interior K →
      (p ∈ e '' D ↔ p ∈ D) ∧
      (p ∈ interior (e '' D) ↔ p ∈ interior D) ∧
      (p ∈ frontier (e '' D) ↔ p ∈ frontier D) := by
  have hfix : EqOn e id (interior K)ᶜ := by
    simpa only [closure_compl] using he.closure e.continuous continuous_id
  exact (e.image_neighborhood_of_eqOn_compl isOpen_univ (subset_univ _) hfix).2.2

private theorem image_eq_local_replacement
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (e : X ≃ₜ X) {K D S : Set X} (he : EqOn e id Kᶜ)
    (hS : ∀ p ∈ K, p ∈ e '' D ↔ p ∈ S) :
    e '' D = (D \ interior K) ∪ (K ∩ S) := by
  have hout := e.image_region_sides_outside_interior he
  ext p
  constructor
  · intro hp
    by_cases hpK : p ∈ K
    · exact Or.inr ⟨hpK, (hS p hpK).mp hp⟩
    · have hpI : p ∉ interior K := fun h => hpK (interior_subset h)
      exact Or.inl ⟨(hout D p hpI).1.mp hp, hpI⟩
  · rintro (⟨hpD, hpI⟩ | ⟨hpK, hpS⟩)
    · exact (hout D p hpI).1.mpr hpD
    · exact (hS p hpK).mpr hpS

end Homeomorph

end

section

open scoped ContDiff Manifold Topology

namespace Schoenflies

private theorem PrePolygon.native_image_rounding_with_prescribed_isotopy
    {m : ℕ} (P : PrePolygon m)
    (M : LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh)
    (hfrontier : frontier M.toPlaneComplex.support = P.carrier)
    (T : M.Triangle) (k : Fin 3) (hfree : M.IsOneEdgeFreeTriangle T k)
    {σ : ℝ} (hσ : 0 < σ) (hσsmall : σ ≤ 1 / 4) :
    let b := LeanEval.Topology.ClassificationOfSurfaces.Moise.affineBasisOfTriangle
      (M.freeTriangleOrder T k) (M.freeTriangleOrder_affineIndependent T k)
    let R := closure (P.carrier \ segment ℝ (b 0) (b 1))
    ∃ (v₀ v₁ : Plane) (f₀ f₁ : Plane →ᵃ[ℝ] ℝ) (ε : ℝ)
      (U₀ U₁ V : Set Plane) (F : Plane → ℝ × ℝ),
      let s₀ := b.coord 2 v₀ / f₀ v₀
      let s₁ := b.coord 2 v₁ / f₁ v₁
      let A₀ := fun p => s₀ * (f₀ p - Real.smoothMax ε (f₀ p) 0) - b.coord 2 p
      let A₁ := fun p => s₁ * (f₁ p - Real.smoothMax ε (f₁ p) 0) - b.coord 2 p
      let B₀ := fun p => f₀ (b 2) / f₀ (b 1) *
        (s₀ * (f₀ p - Real.smoothMax ε (f₀ p) 0) +
          Real.smoothMax ε (f₀ p) 0 / f₀ (b 2) - b.coord 2 p)
      let B₁ := fun p => f₁ (b 2) / f₁ (b 0) *
        (s₁ * (f₁ p - Real.smoothMax ε (f₁ p) 0) +
          Real.smoothMax ε (f₁ p) 0 / f₁ (b 2) - b.coord 2 p)
      let H := fun q : ℝ × Plane => (1 - q.1) * (F q.2).1 + q.1 * (F q.2).2
      0 < ε ∧ ContDiff ℝ ∞ F ∧ IsOpen U₀ ∧ IsOpen U₁ ∧ IsOpen V ∧
      b 0 ∈ U₀ ∧ b 1 ∈ U₁ ∧ Disjoint U₀ U₁ ∧
      M.triangleCarrier T.1 ⊆ U₀ ∪ U₁ ∪ V ∧
      segment ℝ (b 0) v₀ ⊆ R ∧ segment ℝ (b 1) v₁ ⊆ R ∧
      f₀ (b 0) = 0 ∧ 0 < f₀ (b 1) ∧ 0 < f₀ (b 2) ∧ f₀ v₀ < 0 ∧
      f₁ (b 1) = 0 ∧ 0 < f₁ (b 0) ∧ 0 < f₁ (b 2) ∧ f₁ v₁ < 0 ∧
      (∀ p ∈ U₀, (1 : ℝ) / 4 < b.coord 0 p - b.coord 1 p) ∧
      (∀ p ∈ U₁, (1 : ℝ) / 4 < b.coord 1 p - b.coord 0 p) ∧
      Set.EqOn F (fun p => (A₀ p, B₀ p)) U₀ ∧
      Set.EqOn F (fun p => (A₁ p, B₁ p)) U₁ ∧
      Set.EqOn F (fun p => (-b.coord 2 p,
        -Real.smoothMax σ (-b.coord 0 p) (-b.coord 1 p))) V ∧
      (∀ p ∈ U₀,
        (p ∈ M.toPlaneComplex.support ↔
          (if f₀ p < 0 then b.coord 2 v₀ / f₀ v₀ * f₀ p else 0) ≤ b.coord 2 p) ∧
        (p ∈ interior M.toPlaneComplex.support ↔
          (if f₀ p < 0 then b.coord 2 v₀ / f₀ v₀ * f₀ p else 0) < b.coord 2 p) ∧
        (p ∈ frontier M.toPlaneComplex.support ↔
          b.coord 2 p = if f₀ p < 0 then b.coord 2 v₀ / f₀ v₀ * f₀ p else 0) ∧
        (p ∈ (M.eraseTriangle T.1).toPlaneComplex.support ↔
          (if f₀ p < 0 then b.coord 2 v₀ / f₀ v₀ * f₀ p else f₀ p / f₀ (b 2)) ≤
            b.coord 2 p) ∧
        (p ∈ interior (M.eraseTriangle T.1).toPlaneComplex.support ↔
          (if f₀ p < 0 then b.coord 2 v₀ / f₀ v₀ * f₀ p else f₀ p / f₀ (b 2)) <
            b.coord 2 p) ∧
        (p ∈ frontier (M.eraseTriangle T.1).toPlaneComplex.support ↔
          b.coord 2 p = if f₀ p < 0 then b.coord 2 v₀ / f₀ v₀ * f₀ p else
            f₀ p / f₀ (b 2))) ∧
      (∀ p ∈ U₁,
        (p ∈ M.toPlaneComplex.support ↔
          (if f₁ p < 0 then b.coord 2 v₁ / f₁ v₁ * f₁ p else 0) ≤ b.coord 2 p) ∧
        (p ∈ interior M.toPlaneComplex.support ↔
          (if f₁ p < 0 then b.coord 2 v₁ / f₁ v₁ * f₁ p else 0) < b.coord 2 p) ∧
        (p ∈ frontier M.toPlaneComplex.support ↔
          b.coord 2 p = if f₁ p < 0 then b.coord 2 v₁ / f₁ v₁ * f₁ p else 0) ∧
        (p ∈ (M.eraseTriangle T.1).toPlaneComplex.support ↔
          (if f₁ p < 0 then b.coord 2 v₁ / f₁ v₁ * f₁ p else f₁ p / f₁ (b 2)) ≤
            b.coord 2 p) ∧
        (p ∈ interior (M.eraseTriangle T.1).toPlaneComplex.support ↔
          (if f₁ p < 0 then b.coord 2 v₁ / f₁ v₁ * f₁ p else f₁ p / f₁ (b 2)) <
            b.coord 2 p) ∧
        (p ∈ frontier (M.eraseTriangle T.1).toPlaneComplex.support ↔
          b.coord 2 p = if f₁ p < 0 then b.coord 2 v₁ / f₁ v₁ * f₁ p else
            f₁ p / f₁ (b 2))) ∧
      (∀ p ∈ U₀ ∪ U₁ ∪ V,
        fderiv ℝ (fun q => (F q).1) p ≠ 0 ∧
          fderiv ℝ (fun q => (F q).2) p ≠ 0) ∧
      ContDiff ℝ ∞ H ∧
      (∀ t p, deriv (fun s => H (s, p)) t = (F p).2 - (F p).1) ∧
      (∀ p, H (0, p) = (F p).1) ∧
      (∀ p, H (1, p) = (F p).2) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀ ∪ U₁ ∪ V,
        fderiv ℝ (fun q => H (t, q)) p ≠ 0) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀, f₀ p ≤ -ε → H (t, p) = 0 →
        (F p).1 = 0 ∧ (F p).2 = 0 ∧ (∀ u : ℝ, H (u, p) = 0) ∧
          (∀ u : ℝ, deriv (fun s => H (s, p)) u = 0)) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₁, f₁ p ≤ -ε → H (t, p) = 0 →
        (F p).1 = 0 ∧ (F p).2 = 0 ∧ (∀ u : ℝ, H (u, p) = 0) ∧
          (∀ u : ℝ, deriv (fun s => H (s, p)) u = 0)) ∧
      (∀ p ∈ V, ε < f₀ p ∧ ε < f₁ p) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ V, H (t, p) = 0 →
        p ∈ M.triangleCarrier T.1) ∧
      ∃ J : Set Plane, IsCompact J ∧ M.triangleCarrier T.1 ⊆ interior J ∧
        J ⊆ U₀ ∪ U₁ ∪ V ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀ ∪ U₁ ∪ V,
          H (t, p) = 0 → deriv (fun u => H (u, p)) t ≠ 0 → p ∈ interior J) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀,
          H (t, p) = 0 → -ε ≤ f₀ p → p ∈ interior J) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₁,
          H (t, p) = 0 → -ε ≤ f₁ p → p ∈ interior J) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀ ∪ U₁ ∪ V, H (t, p) = 0 → p ∉ J →
          (p ∈ U₀ ∧ f₀ p < -ε ∧ ∃ N : Set Plane,
            IsOpen N ∧ p ∈ N ∧ N ⊆ U₀ ∩ {q | f₀ q < -ε} ∧
              Set.EqOn (fun q => (F q).2) (fun q => f₀ (b 2) / f₀ (b 1) * (F q).1) N) ∨
          (p ∈ U₁ ∧ f₁ p < -ε ∧ ∃ N : Set Plane,
            IsOpen N ∧ p ∈ N ∧ N ⊆ U₁ ∩ {q | f₁ q < -ε} ∧
              Set.EqOn (fun q => (F q).2) (fun q => f₁ (b 2) / f₁ (b 0) * (F q).1) N)) ∧
        (∀ p ∈ V,
          (p ∈ M.toPlaneComplex.support ↔ 0 ≤ b.coord 2 p) ∧
          (p ∈ interior M.toPlaneComplex.support ↔ 0 < b.coord 2 p) ∧
          (p ∈ frontier M.toPlaneComplex.support ↔ b.coord 2 p = 0)) ∧
        (∀ p ∈ U₀ ∪ U₁ ∪ V, p ∉ interior J →
          (p ∈ M.toPlaneComplex.support ↔ (F p).1 ≤ 0) ∧
          (p ∈ interior M.toPlaneComplex.support ↔ (F p).1 < 0) ∧
          (p ∈ frontier M.toPlaneComplex.support ↔ (F p).1 = 0)) ∧
        (∀ p ∈ U₀ ∪ U₁ ∪ V, p ∉ interior J →
          (p ∈ (M.eraseTriangle T.1).toPlaneComplex.support ↔ (F p).2 ≤ 0) ∧
          (p ∈ interior (M.eraseTriangle T.1).toPlaneComplex.support ↔ (F p).2 < 0) ∧
          (p ∈ frontier (M.eraseTriangle T.1).toPlaneComplex.support ↔ (F p).2 = 0)) ∧
        ∃ (K : Set Plane) (X : ℝ × Plane → Plane) (Ω : Set (ℝ × Plane))
          (κ : ℝ × Plane → ℝ),
          IsCompact K ∧ J ⊆ interior K ∧ K ⊆ U₀ ∪ U₁ ∪ V ∧
          ContDiff ℝ ∞ X ∧ HasCompactSupport X ∧
          IsOpen Ω ∧ Set.Icc (0 : ℝ) 1 ×ˢ (U₀ ∪ U₁ ∪ V) ⊆ Ω ∧
          Ω ⊆ Set.univ ×ˢ (U₀ ∪ U₁ ∪ V) ∧ ContDiffOn ℝ ∞ κ Ω ∧
          (∀ z ∈ Ω,
            deriv (fun t => H (t, z.2)) z.1 +
              fderiv ℝ (fun y => H (z.1, y)) z.2 (X z) = κ z * H z) ∧
          (∀ t x, x ∉ K → X (t, x) = 0) ∧
          ∃ Φ : ℝ → (Plane ≃ₘ[ℝ] Plane),
            (∀ (hX : ContDiff ℝ ∞ X) (hsX : HasCompactSupport X) (t : ℝ),
              Φ t = Diffeomorph.timeDependentFlow X hX hsX 0 t) ∧
            ContDiff ℝ ∞ (fun q : ℝ × Plane => Φ q.1 q.2) ∧
            ContDiff ℝ ∞ (fun q : ℝ × Plane => (Φ q.1).symm q.2) ∧
            Φ 0 = Diffeomorph.refl 𝓘(ℝ, Plane) Plane ∞ ∧
            (∀ t : ℝ, Set.EqOn (Φ t) id Kᶜ ∧ Set.EqOn (Φ t).symm id Kᶜ) ∧
            (∀ t : ℝ, (∀ p, Φ t p ∈ U₀ ∪ U₁ ∪ V ↔ p ∈ U₀ ∪ U₁ ∪ V) ∧
              (∀ p, (Φ t).symm p ∈ U₀ ∪ U₁ ∪ V ↔ p ∈ U₀ ∪ U₁ ∪ V)) ∧
            (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀ ∪ U₁ ∪ V,
              ((F p).1 = 0 ↔ H (t, Φ t p) = 0) ∧
              ((F p).1 < 0 ↔ H (t, Φ t p) < 0) ∧
              ((F p).1 ≤ 0 ↔ H (t, Φ t p) ≤ 0)) ∧
            (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀ ∪ U₁ ∪ V,
              (H (t, p) = 0 ↔ (F ((Φ t).symm p)).1 = 0) ∧
              (H (t, p) < 0 ↔ (F ((Φ t).symm p)).1 < 0) ∧
              (H (t, p) ≤ 0 ↔ (F ((Φ t).symm p)).1 ≤ 0)) ∧
            let D₀ := (M.toPlaneComplex.support \ interior K) ∪
              (K ∩ {p | (F p).1 ≤ 0})
            let p := AffineMap.lineMap (b 0) (b 1) ((1 : ℝ) / 2)
            M.toPlaneComplex.support = closure (inside P.carrier) ∧
            IsCompact D₀ ∧
            (∀ q ∈ U₀ ∪ U₁ ∪ V,
              (q ∈ D₀ ↔ (F q).1 ≤ 0) ∧
              (q ∈ interior D₀ ↔ (F q).1 < 0) ∧
              (q ∈ frontier D₀ ↔ (F q).1 = 0)) ∧
            (∀ q ∉ K, q ∈ D₀ ↔ q ∈ M.toPlaneComplex.support) ∧
            p ∈ interior K ∧ p ∈ frontier D₀ ∧ (frontier D₀).Nonempty ∧
            ContDiff ℝ ∞ (fun q => -(F q).1) ∧
            (∀ q ∈ U₀ ∪ U₁ ∪ V,
              fderiv ℝ (fun z => -(F z).1) q ≠ 0) ∧
            (∀ q ∈ frontier D₀ ∩ (U₀ ∪ U₁ ∪ V),
              ∃ (N : Set Plane) (G : Plane → ℝ),
                IsOpen N ∧ q ∈ N ∧ K ⊆ N ∧ ContDiff ℝ ∞ G ∧
                (∀ z ∈ N, fderiv ℝ G z ≠ 0) ∧
                (∀ z, G z = -(F z).1) ∧
                ∀ z ∈ N, (z ∈ D₀ ↔ 0 ≤ G z) ∧
                  (z ∈ interior D₀ ↔ 0 < G z) ∧
                  (z ∈ frontier D₀ ↔ G z = 0)) ∧
            ∃ (O V₁ D₁ : Set Plane),
              IsOpen O ∧ IsCompact (closure O) ∧ closure O ⊆ Kᶜ ∧
              (∀ i : ZMod (m + 3), P.vertex i ∉ U₀ ∪ U₁ ∪ V → P.vertex i ∈ O) ∧
              IsCompact D₁ ∧ IsOpen V₁ ∧ K ⊆ V₁ ∧ V₁ ⊆ U₀ ∪ U₁ ∪ V ∧
              (∀ q ∈ V₁, (q ∈ D₁ ↔ q ∈ D₀) ∧
                (q ∈ interior D₁ ↔ q ∈ interior D₀) ∧
                (q ∈ frontier D₁ ↔ q ∈ frontier D₀)) ∧
              (∀ q ∉ O, (q ∈ D₁ ↔ q ∈ D₀) ∧
                (q ∈ interior D₁ ↔ q ∈ interior D₀) ∧
                (q ∈ frontier D₁ ↔ q ∈ frontier D₀)) ∧
              (∀ q ∉ K ∪ O, q ∈ D₁ ↔ q ∈ M.toPlaneComplex.support) ∧
              (∀ q ∈ V₁, (q ∈ D₁ ↔ (F q).1 ≤ 0) ∧
                (q ∈ interior D₁ ↔ (F q).1 < 0) ∧
                (q ∈ frontier D₁ ↔ (F q).1 = 0)) ∧
              p ∈ frontier D₁ ∧ (frontier D₁).Nonempty ∧
              (∀ q ∈ frontier D₁, ∃ (N : Set Plane) (G : Plane → ℝ),
                IsOpen N ∧ q ∈ N ∧ ContDiff ℝ ∞ G ∧ fderiv ℝ G q ≠ 0 ∧
                ∀ z ∈ N, (z ∈ D₁ ↔ 0 ≤ G z) ∧
                  (z ∈ interior D₁ ↔ 0 < G z) ∧
                  (z ∈ frontier D₁ ↔ G z = 0)) ∧
              let D₂ := (Φ 1) '' D₁
              let V₂ := (Φ 1) '' V₁
              IsCompact D₂ ∧ IsOpen V₂ ∧ K ⊆ V₂ ∧ V₂ ⊆ U₀ ∪ U₁ ∪ V ∧
              (∀ q ∈ V₂, (q ∈ D₂ ↔ (F q).2 ≤ 0) ∧
                (q ∈ interior D₂ ↔ (F q).2 < 0) ∧
                (q ∈ frontier D₂ ↔ (F q).2 = 0)) ∧
              (∀ q ∉ K, (q ∈ D₂ ↔ q ∈ D₁) ∧
                (q ∈ interior D₂ ↔ q ∈ interior D₁) ∧
                (q ∈ frontier D₂ ↔ q ∈ frontier D₁)) ∧
              (∀ q ∉ K ∪ O, q ∈ D₂ ↔ q ∈ M.toPlaneComplex.support) ∧
              D₂ = (D₁ \ interior K) ∪ (K ∩ {q | (F q).2 ≤ 0}) ∧
              (∀ q ∈ V₂, q ∉ interior J →
                (q ∈ D₂ ↔ q ∈ (M.eraseTriangle T.1).toPlaneComplex.support) ∧
                (q ∈ interior D₂ ↔
                  q ∈ interior (M.eraseTriangle T.1).toPlaneComplex.support) ∧
                (q ∈ frontier D₂ ↔
                  q ∈ frontier (M.eraseTriangle T.1).toPlaneComplex.support)) ∧
              Φ 1 p ∈ frontier D₂ ∧ (frontier D₂).Nonempty ∧
              ∀ q ∈ frontier D₂, ∃ (N : Set Plane) (G : Plane → ℝ),
                IsOpen N ∧ q ∈ N ∧ ContDiff ℝ ∞ G ∧ fderiv ℝ G q ≠ 0 ∧
                ∀ z ∈ N, (z ∈ D₂ ↔ 0 ≤ G z) ∧
                  (z ∈ interior D₂ ↔ 0 < G z) ∧
                  (z ∈ frontier D₂ ↔ G z = 0) := by
  dsimp only
  let b := LeanEval.Topology.ClassificationOfSurfaces.Moise.affineBasisOfTriangle
    (M.freeTriangleOrder T k) (M.freeTriangleOrder_affineIndependent T k)
  let p := AffineMap.lineMap (b 0) (b 1) ((1 : ℝ) / 2)
  obtain ⟨v₀, v₁, f₀, f₁, ε, U₀, U₁, V, F,
    hε, hF, hU₀, hU₁, hV, hb₀, hb₁, hdisj, hcover, hs₀, hs₁,
    hf₀, hfb, hfc₀, hfv₀, hf₁, hfa, hfc₁, hfv₁, hgap₀, hgap₁,
    he₀, he₁, heV, hgraph₀, hgraph₁, hreg, hH, hderiv, hstart, hend,
    hregH, hstat₀, hstat₁, hposV, hcentral,
    J, hJ, htriangleJ, hJW, hactive, hweak₀, hweak₁, hexterior, hraw, hsign, hremoved,
    K, X, Ω, κ, hK, hJK, hKW, hX, hsX, hΩ, hΩcover, hΩW, hκ, htransport, hXzero,
    Φ, hΦeq, hΦ, hΦinv, hΦzero, hΦfix, hΦW, hforward, hinverse,
    hsupport, hD₀, hsides, hout, hpK, hpfront, hnonempty, hHneg, hregneg, hgerms,
    O, V₁, D₁, hO, hOc, hOK, hvO, hD₁, hV₁, hKV₁, hV₁W, heqV₁, houtO, hold,
    hprescribed, hpD₁, hnonemptyD₁, hregular⟩ :=
    P.native_global_rounding_with_prescribed_isotopy M hfrontier T k hfree hσ hσsmall
  let D₂ := (Φ 1) '' D₁
  let V₂ := (Φ 1) '' V₁
  obtain ⟨hV₂, hKV₂, houtside⟩ := (Φ 1).toHomeomorph.image_neighborhood_of_eqOn_compl
    hV₁ hKV₁ (hΦfix 1).1
  have hV₂W : V₂ ⊆ U₀ ∪ U₁ ∪ V := by
    rintro _ ⟨q, hq, rfl⟩
    exact ((hΦW 1).1 q).mpr (hV₁W hq)
  have hsign₂ (q : Plane) (hq : q ∈ V₂) :
      ((F q).2 = 0 ↔ (F ((Φ 1).symm q)).1 = 0) ∧
      ((F q).2 < 0 ↔ (F ((Φ 1).symm q)).1 < 0) ∧
      ((F q).2 ≤ 0 ↔ (F ((Φ 1).symm q)).1 ≤ 0) := by
    have hi := hinverse 1 (show (1 : ℝ) ∈ Set.Icc 0 1 from ⟨by norm_num, le_rfl⟩)
      q (hV₂W hq)
    simpa only [sub_self, zero_mul, one_mul, zero_add] using hi
  have hsides₂ := (Φ 1).toHomeomorph.image_region_sides hprescribed hsign₂
  have hliteral : D₂ = (D₁ \ interior K) ∪ (K ∩ {q | (F q).2 ≤ 0}) :=
    (Φ 1).toHomeomorph.image_eq_local_replacement (hΦfix 1).1
      (fun q hq => (hsides₂ q (hKV₂ hq)).1)
  have hretained (q : Plane) (hq : q ∈ V₂) (hqJ : q ∉ interior J) :
      (q ∈ D₂ ↔ q ∈ (M.eraseTriangle T.1).toPlaneComplex.support) ∧
      (q ∈ interior D₂ ↔ q ∈ interior (M.eraseTriangle T.1).toPlaneComplex.support) ∧
      (q ∈ frontier D₂ ↔ q ∈ frontier (M.eraseTriangle T.1).toPlaneComplex.support) := by
    have hraw₂ := hremoved q (hV₂W hq) hqJ
    exact ⟨(hsides₂ q hq).1.trans hraw₂.1.symm,
      (hsides₂ q hq).2.1.trans hraw₂.2.1.symm,
      (hsides₂ q hq).2.2.trans hraw₂.2.2.symm⟩
  have hfront : frontier D₂ = (Φ 1) '' frontier D₁ :=
    ((Φ 1).toHomeomorph.image_frontier D₁).symm
  have hpD₂ : Φ 1 p ∈ frontier D₂ := by
    rw [hfront]
    exact ⟨p, hpD₁, rfl⟩
  refine ⟨v₀, v₁, f₀, f₁, ε, U₀, U₁, V, F,
    hε, hF, hU₀, hU₁, hV, hb₀, hb₁, hdisj, hcover, hs₀, hs₁,
    hf₀, hfb, hfc₀, hfv₀, hf₁, hfa, hfc₁, hfv₁, hgap₀, hgap₁,
    he₀, he₁, heV, hgraph₀, hgraph₁, hreg, hH, hderiv, hstart, hend,
    hregH, hstat₀, hstat₁, hposV, hcentral,
    J, hJ, htriangleJ, hJW, hactive, hweak₀, hweak₁, hexterior, hraw, hsign, hremoved,
    K, X, Ω, κ, hK, hJK, hKW, hX, hsX, hΩ, hΩcover, hΩW, hκ, htransport, hXzero,
    Φ, hΦeq, hΦ, hΦinv, hΦzero, hΦfix, hΦW, hforward, hinverse,
    hsupport, hD₀, hsides, hout, hpK, hpfront, hnonempty, hHneg, hregneg, hgerms,
    O, V₁, D₁, hO, hOc, hOK, hvO, hD₁, hV₁, hKV₁, hV₁W, heqV₁, houtO, hold,
    hprescribed, hpD₁, hnonemptyD₁, hregular,
    hD₁.image (Φ 1).continuous, hV₂, hKV₂, hV₂W, hsides₂, houtside D₁, ?_,
    hliteral, hretained, hpD₂, ⟨Φ 1 p, hpD₂⟩, (Φ 1).regular_frontier_image hregular⟩
  intro q hq
  exact (houtside D₁ q (fun h => hq (Or.inl h))).1.trans (hold q hq)

end Schoenflies

end

section

open scoped Topology

namespace Schoenflies

private theorem mesh_erase_triangle_sides_of_not_mem
    (M : LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh)
    (T : M.Triangle) {p : Plane} (hp : p ∉ M.triangleCarrier T.1) :
    (p ∈ M.toPlaneComplex.support ↔ p ∈ (M.eraseTriangle T.1).toPlaneComplex.support) ∧
    (p ∈ interior M.toPlaneComplex.support ↔
      p ∈ interior (M.eraseTriangle T.1).toPlaneComplex.support) ∧
    (p ∈ frontier M.toPlaneComplex.support ↔
      p ∈ frontier (M.eraseTriangle T.1).toPlaneComplex.support) := by
  have hclosed : IsClosed (M.triangleCarrier T.1) :=
    (T.1.finite_toSet.image M.position).isClosed_convexHull ℝ
  have hsplit := M.support_eq_eraseTriangle_union_triangleCarrier T.2
  have heq (q : Plane) (hq : q ∉ M.triangleCarrier T.1) :
      q ∈ M.toPlaneComplex.support ↔ q ∈ (M.eraseTriangle T.1).toPlaneComplex.support := by
    rw [hsplit]
    exact or_iff_left hq
  have hs : M.toPlaneComplex.support =ᶠ[𝓝 p] (M.eraseTriangle T.1).toPlaneComplex.support := by
    filter_upwards [hclosed.isOpen_compl.mem_nhds hp] with q hq
    exact propext (heq q hq)
  refine ⟨heq p hp, hs.mem_interior_iff, ?_⟩
  rw [M.toPlaneComplex.isCompact_support.isClosed.frontier_eq,
    (M.eraseTriangle T.1).toPlaneComplex.isCompact_support.isClosed.frontier_eq]
  change (p ∈ M.toPlaneComplex.support ∧ p ∉ interior M.toPlaneComplex.support) ↔
    (p ∈ (M.eraseTriangle T.1).toPlaneComplex.support ∧
      p ∉ interior (M.eraseTriangle T.1).toPlaneComplex.support)
  rw [heq p hp, hs.mem_interior_iff]

end Schoenflies

end

section

open scoped ContDiff Topology

namespace Schoenflies

private theorem compact_sublevel_replacement_preserving_germ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {D K W : Set E} {H : E → ℝ} (hD : IsCompact D) (hK : IsCompact K)
    (hW : IsOpen W) (hKW : K ⊆ W) (hH : Continuous H)
    (hreg : ∀ p ∈ W, H p = 0 → fderiv ℝ H p ≠ 0)
    (heq : ∀ p ∈ W \ interior K, p ∈ D ↔ H p ≤ 0) :
    let E₀ := (D \ interior K) ∪ (K ∩ {p | H p ≤ 0})
    IsCompact E₀ ∧
      (∀ p ∈ W, (p ∈ E₀ ↔ H p ≤ 0) ∧
        (p ∈ interior E₀ ↔ H p < 0) ∧ (p ∈ frontier E₀ ↔ H p = 0)) ∧
      (∀ p ∉ K, (p ∈ E₀ ↔ p ∈ D) ∧
        (p ∈ interior E₀ ↔ p ∈ interior D) ∧
        (p ∈ frontier E₀ ↔ p ∈ frontier D)) := by
  have hneg : ∀ p ∈ W, -H p = 0 → fderiv ℝ (fun q => -H q) p ≠ 0 := by
    intro p hp hz
    simpa only [fderiv_fun_neg, neg_ne_zero] using hreg p hp (neg_eq_zero.mp hz)
  obtain ⟨hc, hs, ho⟩ := compact_region_replace_preserving_germ (H := fun p => -H p)
    hD hK hW hKW hH.neg
    hneg (fun p hp => by simpa only [neg_nonneg] using heq p hp)
  have hc' : IsCompact ((D \ interior K) ∪ (K ∩ {p | H p ≤ 0})) := by
    simpa only [neg_nonneg] using hc
  refine ⟨hc', ?_, ?_⟩
  · intro p hp
    simpa only [neg_nonneg, neg_pos, neg_eq_zero] using hs p hp
  · exact region_sides_of_open_local_eq hD.isClosed hc'.isClosed hK.isClosed.isOpen_compl
      (fun p hp => by simpa only [neg_nonneg] using ho p hp)

private theorem matched_erased_region_of_prescribed_germs
    (M : LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh)
    (T : M.Triangle) {J K W O V₂ D₁ D₂ : Set Plane} {F : Plane → ℝ × ℝ}
    (hK : IsCompact K) (hW : IsOpen W) (hJK : J ⊆ interior K) (hKW : K ⊆ W)
    (hTK : M.triangleCarrier T.1 ⊆ K) (hF : ContDiff ℝ ∞ F)
    (hreg : ∀ p ∈ W, (F p).2 = 0 → fderiv ℝ (fun q => (F q).2) p ≠ 0)
    (hremoved : ∀ p ∈ W, p ∉ interior J →
      (p ∈ (M.eraseTriangle T.1).toPlaneComplex.support ↔ (F p).2 ≤ 0))
    (hKV₂ : K ⊆ V₂) (hV₂W : V₂ ⊆ W) (hOK : O ⊆ Kᶜ)
    (hsides₂ : ∀ p ∈ V₂, (p ∈ D₂ ↔ (F p).2 ≤ 0) ∧
      (p ∈ interior D₂ ↔ (F p).2 < 0) ∧ (p ∈ frontier D₂ ↔ (F p).2 = 0))
    (houtside : ∀ p ∉ K, (p ∈ D₂ ↔ p ∈ D₁) ∧
      (p ∈ interior D₂ ↔ p ∈ interior D₁) ∧
      (p ∈ frontier D₂ ↔ p ∈ frontier D₁))
    (houter : ∀ p ∉ O,
      (p ∈ D₁ ↔ p ∈ (M.toPlaneComplex.support \ interior K) ∪ (K ∩ {q | (F q).1 ≤ 0})) ∧
      (p ∈ interior D₁ ↔
        p ∈ interior ((M.toPlaneComplex.support \ interior K) ∪ (K ∩ {q | (F q).1 ≤ 0}))) ∧
      (p ∈ frontier D₁ ↔
        p ∈ frontier ((M.toPlaneComplex.support \ interior K) ∪ (K ∩ {q | (F q).1 ≤ 0})))) :
    let E₀ := ((M.eraseTriangle T.1).toPlaneComplex.support \ interior K) ∪
      (K ∩ {q | (F q).2 ≤ 0})
    IsCompact E₀ ∧
      (∀ p ∈ W, (p ∈ E₀ ↔ (F p).2 ≤ 0) ∧
        (p ∈ interior E₀ ↔ (F p).2 < 0) ∧
        (p ∈ frontier E₀ ↔ (F p).2 = 0)) ∧
      (∀ p ∉ K,
        (p ∈ E₀ ↔ p ∈ (M.eraseTriangle T.1).toPlaneComplex.support) ∧
        (p ∈ interior E₀ ↔ p ∈ interior (M.eraseTriangle T.1).toPlaneComplex.support) ∧
        (p ∈ frontier E₀ ↔ p ∈ frontier (M.eraseTriangle T.1).toPlaneComplex.support)) ∧
      (∀ p ∈ V₂, (p ∈ D₂ ↔ p ∈ E₀) ∧
        (p ∈ interior D₂ ↔ p ∈ interior E₀) ∧
        (p ∈ frontier D₂ ↔ p ∈ frontier E₀)) ∧
      (∀ p ∉ O, (p ∈ D₂ ↔ p ∈ E₀) ∧
        (p ∈ interior D₂ ↔ p ∈ interior E₀) ∧
        (p ∈ frontier D₂ ↔ p ∈ frontier E₀)) ∧
      D₂ = (E₀ \ O) ∪ (D₁ ∩ O) := by
  let D₀ := (M.toPlaneComplex.support \ interior K) ∪ (K ∩ {q | (F q).1 ≤ 0})
  let E₀ := ((M.eraseTriangle T.1).toPlaneComplex.support \ interior K) ∪
    (K ∩ {q | (F q).2 ≤ 0})
  have hD₀ : IsCompact D₀ :=
    (M.toPlaneComplex.isCompact_support.diff isOpen_interior).union
      (hK.inter_right (isClosed_le hF.fst.continuous continuous_const))
  have hraw₀ := region_sides_of_open_local_eq M.toPlaneComplex.isCompact_support.isClosed
    hD₀.isClosed hK.isClosed.isOpen_compl (by
      intro p hp
      change p ∉ K at hp
      have hpI : p ∉ interior K := fun hi => hp (interior_subset hi)
      simp only [D₀, Set.mem_union, Set.mem_sdiff, Set.mem_inter_iff,
        hp, hpI, not_false_eq_true, and_true, false_and, or_false])
  obtain ⟨hE₀, hsignE, hrawE⟩ := compact_sublevel_replacement_preserving_germ
    (M.eraseTriangle T.1).toPlaneComplex.isCompact_support hK hW hKW hF.snd.continuous
    hreg (fun p hp => hremoved p hp.1 (fun hj => hp.2 (hJK (interior_subset hj))))
  have hnear (p : Plane) (hp : p ∈ V₂) :
      (p ∈ D₂ ↔ p ∈ E₀) ∧ (p ∈ interior D₂ ↔ p ∈ interior E₀) ∧
        (p ∈ frontier D₂ ↔ p ∈ frontier E₀) := by
    have hd := hsides₂ p hp
    have he := hsignE p (hV₂W hp)
    exact ⟨hd.1.trans he.1.symm, hd.2.1.trans he.2.1.symm, hd.2.2.trans he.2.2.symm⟩
  have hout (p : Plane) (hp : p ∉ O) :
      (p ∈ D₂ ↔ p ∈ E₀) ∧ (p ∈ interior D₂ ↔ p ∈ interior E₀) ∧
        (p ∈ frontier D₂ ↔ p ∈ frontier E₀) := by
    by_cases hpK : p ∈ K
    · exact hnear p (hKV₂ hpK)
    have hd := houtside p hpK
    have ho := houter p hp
    have ha := hraw₀ p hpK
    have hb := mesh_erase_triangle_sides_of_not_mem M T (fun ht => hpK (hTK ht))
    have he := hrawE p hpK
    exact ⟨hd.1.trans (ho.1.trans (ha.1.trans (hb.1.trans he.1.symm))),
      hd.2.1.trans (ho.2.1.trans (ha.2.1.trans (hb.2.1.trans he.2.1.symm))),
      hd.2.2.trans (ho.2.2.trans (ha.2.2.trans (hb.2.2.trans he.2.2.symm)))⟩
  refine ⟨hE₀, hsignE, hrawE, hnear, hout, ?_⟩
  ext p
  by_cases hpO : p ∈ O
  · have he := (houtside p (hOK hpO)).1
    simp only [Set.mem_union, Set.mem_sdiff, Set.mem_inter_iff, hpO,
      not_true_eq_false, and_false, false_or, and_true]
    exact he
  · simp only [Set.mem_union, Set.mem_sdiff, Set.mem_inter_iff, hpO,
      not_false_eq_true, and_true, and_false, or_false]
    exact (hout p hpO).1

end Schoenflies

end

section

open scoped ContDiff Manifold Topology

namespace Schoenflies

theorem PrePolygon.exists_prescribed_rounding_isotopy_of_one_edge_free_triangle
    {m : ℕ} (P : PrePolygon m)
    (M : LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh)
    (hfrontier : frontier M.toPlaneComplex.support = P.carrier)
    (T : M.Triangle) (k : Fin 3) (hfree : M.IsOneEdgeFreeTriangle T k)
    {σ : ℝ} (hσ : 0 < σ) (hσsmall : σ ≤ 1 / 4) :
    let b := LeanEval.Topology.ClassificationOfSurfaces.Moise.affineBasisOfTriangle
      (M.freeTriangleOrder T k) (M.freeTriangleOrder_affineIndependent T k)
    let R := closure (P.carrier \ segment ℝ (b 0) (b 1))
    ∃ (v₀ v₁ : Plane) (f₀ f₁ : Plane →ᵃ[ℝ] ℝ) (ε : ℝ)
      (U₀ U₁ V : Set Plane) (F : Plane → ℝ × ℝ),
      let s₀ := b.coord 2 v₀ / f₀ v₀
      let s₁ := b.coord 2 v₁ / f₁ v₁
      let A₀ := fun p => s₀ * (f₀ p - Real.smoothMax ε (f₀ p) 0) - b.coord 2 p
      let A₁ := fun p => s₁ * (f₁ p - Real.smoothMax ε (f₁ p) 0) - b.coord 2 p
      let B₀ := fun p => f₀ (b 2) / f₀ (b 1) *
        (s₀ * (f₀ p - Real.smoothMax ε (f₀ p) 0) +
          Real.smoothMax ε (f₀ p) 0 / f₀ (b 2) - b.coord 2 p)
      let B₁ := fun p => f₁ (b 2) / f₁ (b 0) *
        (s₁ * (f₁ p - Real.smoothMax ε (f₁ p) 0) +
          Real.smoothMax ε (f₁ p) 0 / f₁ (b 2) - b.coord 2 p)
      let H := fun q : ℝ × Plane => (1 - q.1) * (F q.2).1 + q.1 * (F q.2).2
      0 < ε ∧ ContDiff ℝ ∞ F ∧ IsOpen U₀ ∧ IsOpen U₁ ∧ IsOpen V ∧
      b 0 ∈ U₀ ∧ b 1 ∈ U₁ ∧ Disjoint U₀ U₁ ∧
      M.triangleCarrier T.1 ⊆ U₀ ∪ U₁ ∪ V ∧
      segment ℝ (b 0) v₀ ⊆ R ∧ segment ℝ (b 1) v₁ ⊆ R ∧
      f₀ (b 0) = 0 ∧ 0 < f₀ (b 1) ∧ 0 < f₀ (b 2) ∧ f₀ v₀ < 0 ∧
      f₁ (b 1) = 0 ∧ 0 < f₁ (b 0) ∧ 0 < f₁ (b 2) ∧ f₁ v₁ < 0 ∧
      (∀ p ∈ U₀, (1 : ℝ) / 4 < b.coord 0 p - b.coord 1 p) ∧
      (∀ p ∈ U₁, (1 : ℝ) / 4 < b.coord 1 p - b.coord 0 p) ∧
      Set.EqOn F (fun p => (A₀ p, B₀ p)) U₀ ∧
      Set.EqOn F (fun p => (A₁ p, B₁ p)) U₁ ∧
      Set.EqOn F (fun p => (-b.coord 2 p,
        -Real.smoothMax σ (-b.coord 0 p) (-b.coord 1 p))) V ∧
      (∀ p ∈ U₀,
        (p ∈ M.toPlaneComplex.support ↔
          (if f₀ p < 0 then b.coord 2 v₀ / f₀ v₀ * f₀ p else 0) ≤ b.coord 2 p) ∧
        (p ∈ interior M.toPlaneComplex.support ↔
          (if f₀ p < 0 then b.coord 2 v₀ / f₀ v₀ * f₀ p else 0) < b.coord 2 p) ∧
        (p ∈ frontier M.toPlaneComplex.support ↔
          b.coord 2 p = if f₀ p < 0 then b.coord 2 v₀ / f₀ v₀ * f₀ p else 0) ∧
        (p ∈ (M.eraseTriangle T.1).toPlaneComplex.support ↔
          (if f₀ p < 0 then b.coord 2 v₀ / f₀ v₀ * f₀ p else f₀ p / f₀ (b 2)) ≤
            b.coord 2 p) ∧
        (p ∈ interior (M.eraseTriangle T.1).toPlaneComplex.support ↔
          (if f₀ p < 0 then b.coord 2 v₀ / f₀ v₀ * f₀ p else f₀ p / f₀ (b 2)) <
            b.coord 2 p) ∧
        (p ∈ frontier (M.eraseTriangle T.1).toPlaneComplex.support ↔
          b.coord 2 p = if f₀ p < 0 then b.coord 2 v₀ / f₀ v₀ * f₀ p else
            f₀ p / f₀ (b 2))) ∧
      (∀ p ∈ U₁,
        (p ∈ M.toPlaneComplex.support ↔
          (if f₁ p < 0 then b.coord 2 v₁ / f₁ v₁ * f₁ p else 0) ≤ b.coord 2 p) ∧
        (p ∈ interior M.toPlaneComplex.support ↔
          (if f₁ p < 0 then b.coord 2 v₁ / f₁ v₁ * f₁ p else 0) < b.coord 2 p) ∧
        (p ∈ frontier M.toPlaneComplex.support ↔
          b.coord 2 p = if f₁ p < 0 then b.coord 2 v₁ / f₁ v₁ * f₁ p else 0) ∧
        (p ∈ (M.eraseTriangle T.1).toPlaneComplex.support ↔
          (if f₁ p < 0 then b.coord 2 v₁ / f₁ v₁ * f₁ p else f₁ p / f₁ (b 2)) ≤
            b.coord 2 p) ∧
        (p ∈ interior (M.eraseTriangle T.1).toPlaneComplex.support ↔
          (if f₁ p < 0 then b.coord 2 v₁ / f₁ v₁ * f₁ p else f₁ p / f₁ (b 2)) <
            b.coord 2 p) ∧
        (p ∈ frontier (M.eraseTriangle T.1).toPlaneComplex.support ↔
          b.coord 2 p = if f₁ p < 0 then b.coord 2 v₁ / f₁ v₁ * f₁ p else
            f₁ p / f₁ (b 2))) ∧
      (∀ p ∈ U₀ ∪ U₁ ∪ V,
        fderiv ℝ (fun q => (F q).1) p ≠ 0 ∧
          fderiv ℝ (fun q => (F q).2) p ≠ 0) ∧
      ContDiff ℝ ∞ H ∧
      (∀ t p, deriv (fun s => H (s, p)) t = (F p).2 - (F p).1) ∧
      (∀ p, H (0, p) = (F p).1) ∧
      (∀ p, H (1, p) = (F p).2) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀ ∪ U₁ ∪ V,
        fderiv ℝ (fun q => H (t, q)) p ≠ 0) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀, f₀ p ≤ -ε → H (t, p) = 0 →
        (F p).1 = 0 ∧ (F p).2 = 0 ∧ (∀ u : ℝ, H (u, p) = 0) ∧
          (∀ u : ℝ, deriv (fun s => H (s, p)) u = 0)) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₁, f₁ p ≤ -ε → H (t, p) = 0 →
        (F p).1 = 0 ∧ (F p).2 = 0 ∧ (∀ u : ℝ, H (u, p) = 0) ∧
          (∀ u : ℝ, deriv (fun s => H (s, p)) u = 0)) ∧
      (∀ p ∈ V, ε < f₀ p ∧ ε < f₁ p) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ V, H (t, p) = 0 →
        p ∈ M.triangleCarrier T.1) ∧
      ∃ J : Set Plane, IsCompact J ∧ M.triangleCarrier T.1 ⊆ interior J ∧
        J ⊆ U₀ ∪ U₁ ∪ V ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀ ∪ U₁ ∪ V,
          H (t, p) = 0 → deriv (fun u => H (u, p)) t ≠ 0 → p ∈ interior J) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀,
          H (t, p) = 0 → -ε ≤ f₀ p → p ∈ interior J) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₁,
          H (t, p) = 0 → -ε ≤ f₁ p → p ∈ interior J) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀ ∪ U₁ ∪ V, H (t, p) = 0 → p ∉ J →
          (p ∈ U₀ ∧ f₀ p < -ε ∧ ∃ N : Set Plane,
            IsOpen N ∧ p ∈ N ∧ N ⊆ U₀ ∩ {q | f₀ q < -ε} ∧
              Set.EqOn (fun q => (F q).2) (fun q => f₀ (b 2) / f₀ (b 1) * (F q).1) N) ∨
          (p ∈ U₁ ∧ f₁ p < -ε ∧ ∃ N : Set Plane,
            IsOpen N ∧ p ∈ N ∧ N ⊆ U₁ ∩ {q | f₁ q < -ε} ∧
              Set.EqOn (fun q => (F q).2) (fun q => f₁ (b 2) / f₁ (b 0) * (F q).1) N)) ∧
        (∀ p ∈ V,
          (p ∈ M.toPlaneComplex.support ↔ 0 ≤ b.coord 2 p) ∧
          (p ∈ interior M.toPlaneComplex.support ↔ 0 < b.coord 2 p) ∧
          (p ∈ frontier M.toPlaneComplex.support ↔ b.coord 2 p = 0)) ∧
        (∀ p ∈ U₀ ∪ U₁ ∪ V, p ∉ interior J →
          (p ∈ M.toPlaneComplex.support ↔ (F p).1 ≤ 0) ∧
          (p ∈ interior M.toPlaneComplex.support ↔ (F p).1 < 0) ∧
          (p ∈ frontier M.toPlaneComplex.support ↔ (F p).1 = 0)) ∧
        (∀ p ∈ U₀ ∪ U₁ ∪ V, p ∉ interior J →
          (p ∈ (M.eraseTriangle T.1).toPlaneComplex.support ↔ (F p).2 ≤ 0) ∧
          (p ∈ interior (M.eraseTriangle T.1).toPlaneComplex.support ↔ (F p).2 < 0) ∧
          (p ∈ frontier (M.eraseTriangle T.1).toPlaneComplex.support ↔ (F p).2 = 0)) ∧
        ∃ (K : Set Plane) (X : ℝ × Plane → Plane) (Ω : Set (ℝ × Plane))
          (κ : ℝ × Plane → ℝ),
          IsCompact K ∧ J ⊆ interior K ∧ K ⊆ U₀ ∪ U₁ ∪ V ∧
          ContDiff ℝ ∞ X ∧ HasCompactSupport X ∧
          IsOpen Ω ∧ Set.Icc (0 : ℝ) 1 ×ˢ (U₀ ∪ U₁ ∪ V) ⊆ Ω ∧
          Ω ⊆ Set.univ ×ˢ (U₀ ∪ U₁ ∪ V) ∧ ContDiffOn ℝ ∞ κ Ω ∧
          (∀ z ∈ Ω,
            deriv (fun t => H (t, z.2)) z.1 +
              fderiv ℝ (fun y => H (z.1, y)) z.2 (X z) = κ z * H z) ∧
          (∀ t x, x ∉ K → X (t, x) = 0) ∧
          ∃ Φ : ℝ → (Plane ≃ₘ[ℝ] Plane),
            (∀ (hX : ContDiff ℝ ∞ X) (hsX : HasCompactSupport X) (t : ℝ),
              Φ t = Diffeomorph.timeDependentFlow X hX hsX 0 t) ∧
            ContDiff ℝ ∞ (fun q : ℝ × Plane => Φ q.1 q.2) ∧
            ContDiff ℝ ∞ (fun q : ℝ × Plane => (Φ q.1).symm q.2) ∧
            Φ 0 = Diffeomorph.refl 𝓘(ℝ, Plane) Plane ∞ ∧
            (∀ t : ℝ, Set.EqOn (Φ t) id Kᶜ ∧ Set.EqOn (Φ t).symm id Kᶜ) ∧
            (∀ t : ℝ, (∀ p, Φ t p ∈ U₀ ∪ U₁ ∪ V ↔ p ∈ U₀ ∪ U₁ ∪ V) ∧
              (∀ p, (Φ t).symm p ∈ U₀ ∪ U₁ ∪ V ↔ p ∈ U₀ ∪ U₁ ∪ V)) ∧
            (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀ ∪ U₁ ∪ V,
              ((F p).1 = 0 ↔ H (t, Φ t p) = 0) ∧
              ((F p).1 < 0 ↔ H (t, Φ t p) < 0) ∧
              ((F p).1 ≤ 0 ↔ H (t, Φ t p) ≤ 0)) ∧
            (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀ ∪ U₁ ∪ V,
              (H (t, p) = 0 ↔ (F ((Φ t).symm p)).1 = 0) ∧
              (H (t, p) < 0 ↔ (F ((Φ t).symm p)).1 < 0) ∧
              (H (t, p) ≤ 0 ↔ (F ((Φ t).symm p)).1 ≤ 0)) ∧
            let D₀ := (M.toPlaneComplex.support \ interior K) ∪
              (K ∩ {p | (F p).1 ≤ 0})
            let p := AffineMap.lineMap (b 0) (b 1) ((1 : ℝ) / 2)
            M.toPlaneComplex.support = closure (inside P.carrier) ∧
            IsCompact D₀ ∧
            (∀ q ∈ U₀ ∪ U₁ ∪ V,
              (q ∈ D₀ ↔ (F q).1 ≤ 0) ∧
              (q ∈ interior D₀ ↔ (F q).1 < 0) ∧
              (q ∈ frontier D₀ ↔ (F q).1 = 0)) ∧
            (∀ q ∉ K, q ∈ D₀ ↔ q ∈ M.toPlaneComplex.support) ∧
            p ∈ interior K ∧ p ∈ frontier D₀ ∧ (frontier D₀).Nonempty ∧
            ContDiff ℝ ∞ (fun q => -(F q).1) ∧
            (∀ q ∈ U₀ ∪ U₁ ∪ V,
              fderiv ℝ (fun z => -(F z).1) q ≠ 0) ∧
            (∀ q ∈ frontier D₀ ∩ (U₀ ∪ U₁ ∪ V),
              ∃ (N : Set Plane) (G : Plane → ℝ),
                IsOpen N ∧ q ∈ N ∧ K ⊆ N ∧ ContDiff ℝ ∞ G ∧
                (∀ z ∈ N, fderiv ℝ G z ≠ 0) ∧
                (∀ z, G z = -(F z).1) ∧
                ∀ z ∈ N, (z ∈ D₀ ↔ 0 ≤ G z) ∧
                  (z ∈ interior D₀ ↔ 0 < G z) ∧
                  (z ∈ frontier D₀ ↔ G z = 0)) ∧
            ∃ (O V₁ D₁ : Set Plane),
              IsOpen O ∧ IsCompact (closure O) ∧ closure O ⊆ Kᶜ ∧
              (∀ i : ZMod (m + 3), P.vertex i ∉ U₀ ∪ U₁ ∪ V → P.vertex i ∈ O) ∧
              IsCompact D₁ ∧ IsOpen V₁ ∧ K ⊆ V₁ ∧ V₁ ⊆ U₀ ∪ U₁ ∪ V ∧
              (∀ q ∈ V₁, (q ∈ D₁ ↔ q ∈ D₀) ∧
                (q ∈ interior D₁ ↔ q ∈ interior D₀) ∧
                (q ∈ frontier D₁ ↔ q ∈ frontier D₀)) ∧
              (∀ q ∉ O, (q ∈ D₁ ↔ q ∈ D₀) ∧
                (q ∈ interior D₁ ↔ q ∈ interior D₀) ∧
                (q ∈ frontier D₁ ↔ q ∈ frontier D₀)) ∧
              (∀ q ∉ K ∪ O, q ∈ D₁ ↔ q ∈ M.toPlaneComplex.support) ∧
              (∀ q ∈ V₁, (q ∈ D₁ ↔ (F q).1 ≤ 0) ∧
                (q ∈ interior D₁ ↔ (F q).1 < 0) ∧
                (q ∈ frontier D₁ ↔ (F q).1 = 0)) ∧
              p ∈ frontier D₁ ∧ (frontier D₁).Nonempty ∧
              (∀ q ∈ frontier D₁, ∃ (N : Set Plane) (G : Plane → ℝ),
                IsOpen N ∧ q ∈ N ∧ ContDiff ℝ ∞ G ∧ fderiv ℝ G q ≠ 0 ∧
                ∀ z ∈ N, (z ∈ D₁ ↔ 0 ≤ G z) ∧
                  (z ∈ interior D₁ ↔ 0 < G z) ∧
                  (z ∈ frontier D₁ ↔ G z = 0)) ∧
              let D₂ := (Φ 1) '' D₁
              let V₂ := (Φ 1) '' V₁
              IsCompact D₂ ∧ IsOpen V₂ ∧ K ⊆ V₂ ∧ V₂ ⊆ U₀ ∪ U₁ ∪ V ∧
              (∀ q ∈ V₂, (q ∈ D₂ ↔ (F q).2 ≤ 0) ∧
                (q ∈ interior D₂ ↔ (F q).2 < 0) ∧
                (q ∈ frontier D₂ ↔ (F q).2 = 0)) ∧
              (∀ q ∉ K, (q ∈ D₂ ↔ q ∈ D₁) ∧
                (q ∈ interior D₂ ↔ q ∈ interior D₁) ∧
                (q ∈ frontier D₂ ↔ q ∈ frontier D₁)) ∧
              (∀ q ∉ K ∪ O, q ∈ D₂ ↔ q ∈ M.toPlaneComplex.support) ∧
              D₂ = (D₁ \ interior K) ∪ (K ∩ {q | (F q).2 ≤ 0}) ∧
              (∀ q ∈ V₂, q ∉ interior J →
                (q ∈ D₂ ↔ q ∈ (M.eraseTriangle T.1).toPlaneComplex.support) ∧
                (q ∈ interior D₂ ↔
                  q ∈ interior (M.eraseTriangle T.1).toPlaneComplex.support) ∧
                (q ∈ frontier D₂ ↔
                  q ∈ frontier (M.eraseTriangle T.1).toPlaneComplex.support)) ∧
              Φ 1 p ∈ frontier D₂ ∧ (frontier D₂).Nonempty ∧
              (∀ q ∈ frontier D₂, ∃ (N : Set Plane) (G : Plane → ℝ),
                IsOpen N ∧ q ∈ N ∧ ContDiff ℝ ∞ G ∧ fderiv ℝ G q ≠ 0 ∧
                ∀ z ∈ N, (z ∈ D₂ ↔ 0 ≤ G z) ∧
                  (z ∈ interior D₂ ↔ 0 < G z) ∧
                  (z ∈ frontier D₂ ↔ G z = 0)) ∧
              let E₀ := ((M.eraseTriangle T.1).toPlaneComplex.support \ interior K) ∪
                (K ∩ {q | (F q).2 ≤ 0})
              IsCompact E₀ ∧
              (∀ q ∈ U₀ ∪ U₁ ∪ V, (q ∈ E₀ ↔ (F q).2 ≤ 0) ∧
                (q ∈ interior E₀ ↔ (F q).2 < 0) ∧
                (q ∈ frontier E₀ ↔ (F q).2 = 0)) ∧
              (∀ q ∉ K,
                (q ∈ E₀ ↔ q ∈ (M.eraseTriangle T.1).toPlaneComplex.support) ∧
                (q ∈ interior E₀ ↔ q ∈ interior (M.eraseTriangle T.1).toPlaneComplex.support) ∧
                (q ∈ frontier E₀ ↔ q ∈ frontier (M.eraseTriangle T.1).toPlaneComplex.support)) ∧
              (∀ q ∈ V₂, (q ∈ D₂ ↔ q ∈ E₀) ∧
                (q ∈ interior D₂ ↔ q ∈ interior E₀) ∧
                (q ∈ frontier D₂ ↔ q ∈ frontier E₀)) ∧
              (∀ q ∉ O, (q ∈ D₂ ↔ q ∈ E₀) ∧
                (q ∈ interior D₂ ↔ q ∈ interior E₀) ∧
                (q ∈ frontier D₂ ↔ q ∈ frontier E₀)) ∧
              D₂ = (E₀ \ O) ∪ (D₁ ∩ O) := by
  dsimp only
  obtain ⟨v₀, v₁, f₀, f₁, ε, U₀, U₁, V, F,
    hε, hF, hU₀, hU₁, hV, hb₀, hb₁, hdisj, hcover, hs₀, hs₁,
    hf₀, hfb, hfc₀, hfv₀, hf₁, hfa, hfc₁, hfv₁, hgap₀, hgap₁,
    he₀, he₁, heV, hgraph₀, hgraph₁, hreg, hH, hderiv, hstart, hend,
    hregH, hstat₀, hstat₁, hposV, hcentral,
    J, hJ, htriangleJ, hJW, hactive, hweak₀, hweak₁, hexterior, hraw, hsign, hremoved,
    K, X, Ω, κ, hK, hJK, hKW, hX, hsX, hΩ, hΩcover, hΩW, hκ, htransport, hXzero,
    Φ, hΦeq, hΦ, hΦinv, hΦzero, hΦfix, hΦW, hforward, hinverse,
    hsupport, hD₀, hsides, hout, hpK, hpfront, hnonempty, hHneg, hregneg, hgerms,
    O, V₁, D₁, hO, hOc, hOK, hvO, hD₁, hV₁, hKV₁, hV₁W, heqV₁, houtO, hold,
    hprescribed, hpD₁, hnonemptyD₁, hregular,
    hD₂, hV₂, hKV₂, hV₂W, hsides₂, houtside, hraw₂, hliteral, hretained,
    hpD₂, hnonemptyD₂, hregular₂⟩ :=
    P.native_image_rounding_with_prescribed_isotopy M hfrontier T k hfree hσ hσsmall
  obtain ⟨hE₀, hsignE, hrawE, hnearE, houtE, hliteralE⟩ :=
    matched_erased_region_of_prescribed_germs M T hK ((hU₀.union hU₁).union hV) hJK hKW
      (fun _ ht => interior_subset (hJK (interior_subset (htriangleJ ht)))) hF
      (fun q hq _ => (hreg q hq).2) (fun q hq hqJ => (hremoved q hq hqJ).1)
      hKV₂ hV₂W (fun _ hq => hOK (subset_closure hq)) hsides₂ houtside houtO
  exact ⟨v₀, v₁, f₀, f₁, ε, U₀, U₁, V, F,
    hε, hF, hU₀, hU₁, hV, hb₀, hb₁, hdisj, hcover, hs₀, hs₁,
    hf₀, hfb, hfc₀, hfv₀, hf₁, hfa, hfc₁, hfv₁, hgap₀, hgap₁,
    he₀, he₁, heV, hgraph₀, hgraph₁, hreg, hH, hderiv, hstart, hend,
    hregH, hstat₀, hstat₁, hposV, hcentral,
    J, hJ, htriangleJ, hJW, hactive, hweak₀, hweak₁, hexterior, hraw, hsign, hremoved,
    K, X, Ω, κ, hK, hJK, hKW, hX, hsX, hΩ, hΩcover, hΩW, hκ, htransport, hXzero,
    Φ, hΦeq, hΦ, hΦinv, hΦzero, hΦfix, hΦW, hforward, hinverse,
    hsupport, hD₀, hsides, hout, hpK, hpfront, hnonempty, hHneg, hregneg, hgerms,
    O, V₁, D₁, hO, hOc, hOK, hvO, hD₁, hV₁, hKV₁, hV₁W, heqV₁, houtO, hold,
    hprescribed, hpD₁, hnonemptyD₁, hregular,
    hD₂, hV₂, hKV₂, hV₂W, hsides₂, houtside, hraw₂, hliteral, hretained,
    hpD₂, hnonemptyD₂, hregular₂,
    hE₀, hsignE, hrawE, hnearE, houtE, hliteralE⟩

end Schoenflies

end

section
open Set Metric
open scoped ContDiff Manifold

namespace Schoenflies

theorem PrePolygon.exists_normalized_compatible_finite_vertex_roundings
    {m : ℕ} (P : PrePolygon m) (O : ZMod (m + 3) → Set Plane)
    (hO : ∀ i, IsOpen (O i)) (hiO : ∀ i, P.vertex i ∈ O i) :
    ∃ (e : ZMod (m + 3) → Plane ≃ᵃ[ℝ] Plane)
      (U : ZMod (m + 3) → Set Plane) (d σ δ R r : ZMod (m + 3) → ℝ),
      (∀ i, 0 < r i ∧ e i (P.vertex (i - 1)) = Plane.mk (-1) 0 ∧
        e i (P.vertex (i + 1)) = Plane.mk (r i) (d i * r i)) ∧
      (∀ i, IsOpen (U i) ∧ P.vertex i ∈ U i ∧ U i ⊆ O i ∧
        e i (P.vertex i) = 0 ∧ (d i = 0 ∨ d i = 1) ∧
        (σ i = -1 ∨ σ i = 1) ∧
        (d i = 0 ↔ Plane.det (P.vertex (i - 1) - P.vertex i)
          (P.vertex (i + 1) - P.vertex i) = 0) ∧ 0 < δ i ∧ 3 * δ i < R i ∧
        ∀ p ∈ U i, p ∈ closure (inside P.carrier) ↔
          0 ≤ σ i * ((e i p) 1 - d i * max ((e i p) 0) 0)) ∧
      (Pairwise fun i j => Disjoint (U i) (U j)) ∧
      let N := fun i => e i ⁻¹' ball (0 : Plane) (R i)
      let K := fun i => e i ⁻¹' closedBall (0 : Plane) (R i)
      let F := fun ε i p => σ i * ((e i p) 1 - d i * Real.smoothMax (ε i) ((e i p) 0) 0)
      let D := fun ε => (closure (inside P.carrier) \ ⋃ i, N i) ∪
        ⋃ i, K i ∩ {p | 0 ≤ F ε i p}
      (∀ i, P.vertex i ∈ N i ∧ IsOpen (N i) ∧ IsCompact (K i) ∧ K i ⊆ U i) ∧
      (∀ ε : ZMod (m + 3) → ℝ, (∀ i, 0 < ε i ∧ ε i ≤ δ i) →
        IsCompact (D ε) ∧
          (∀ p ∉ ⋃ i, K i, p ∈ D ε ↔ p ∈ closure (inside P.carrier)) ∧
          ∀ p ∈ frontier (D ε), ∃ (V : Set Plane) (G : Plane → ℝ),
            IsOpen V ∧ p ∈ V ∧ ContDiff ℝ ∞ G ∧ fderiv ℝ G p ≠ 0 ∧
            ∀ q ∈ V, (q ∈ D ε ↔ 0 ≤ G q) ∧
              (q ∈ interior (D ε) ↔ 0 < G q) ∧ (q ∈ frontier (D ε) ↔ G q = 0)) ∧
      ∀ ε₀ ε₁ : ZMod (m + 3) → ℝ,
        (∀ i, 0 < ε₀ i ∧ ε₀ i ≤ δ i) → (∀ i, 0 < ε₁ i ∧ ε₁ i ≤ δ i) →
        ∃ (Φ : ℝ → (Plane ≃ₘ[ℝ] Plane)) (C : Set Plane),
          ContDiff ℝ ∞ (fun z : ℝ × Plane => Φ z.1 z.2) ∧
          ContDiff ℝ ∞ (fun z : ℝ × Plane => (Φ z.1).symm z.2) ∧
          Φ 0 = Diffeomorph.refl 𝓘(ℝ, Plane) Plane ∞ ∧
          IsCompact C ∧ C ⊆ ⋃ i, N i ∧
          (∀ t : ℝ, EqOn (Φ t) id Cᶜ ∧ EqOn (Φ t).symm id Cᶜ) ∧
          Φ 1 '' D ε₀ = D ε₁ ∧
          Φ 1 '' interior (D ε₀) = interior (D ε₁) ∧
          Φ 1 '' frontier (D ε₀) = frontier (D ε₁) := by
  obtain ⟨e, U, d, σ, δ, R, r, hnorm, hc, hdisj, hn, hD, hout, _, hglobal⟩ :=
    P.exists_normalized_finite_compact_vertex_rounding O hO hiO
  let N := fun i => e i ⁻¹' ball (0 : Plane) (R i)
  let K := fun i => e i ⁻¹' closedBall (0 : Plane) (R i)
  let F := fun (ε : ZMod (m + 3) → ℝ) i p =>
    σ i * ((e i p) 1 - d i * Real.smoothMax (ε i) ((e i p) 0) 0)
  let D := fun ε => (closure (inside P.carrier) \ ⋃ i, N i) ∪
    ⋃ i, K i ∩ {p | 0 ≤ F ε i p}
  have hd (i) : d i = 0 ∨ d i = 1 := (hc i).2.2.2.2.1
  have hσ (i) : σ i = -1 ∨ σ i = 1 := (hc i).2.2.2.2.2.1
  have hδ (i) : 0 < δ i := (hc i).2.2.2.2.2.2.2.1
  have hδR (i) : 3 * δ i < R i := (hc i).2.2.2.2.2.2.2.2.1
  have hNK (i) : N i ⊆ K i := preimage_mono ball_subset_closedBall
  have hdisjK : Pairwise fun i j => Disjoint (K i) (K j) := by
    intro i j hij
    exact (hdisj hij).mono (hn i).2.2.2 (hn j).2.2.2
  have hisotopy (ε₀ ε₁ : ZMod (m + 3) → ℝ)
      (hε₀ : ∀ i, 0 < ε₀ i ∧ ε₀ i ≤ δ i)
      (hε₁ : ∀ i, 0 < ε₁ i ∧ ε₁ i ≤ δ i) :
      ∃ (Φ : ℝ → (Plane ≃ₘ[ℝ] Plane)) (C : Set Plane),
        ContDiff ℝ ∞ (fun z : ℝ × Plane => Φ z.1 z.2) ∧
        ContDiff ℝ ∞ (fun z : ℝ × Plane => (Φ z.1).symm z.2) ∧
        Φ 0 = Diffeomorph.refl 𝓘(ℝ, Plane) Plane ∞ ∧
        IsCompact C ∧ C ⊆ ⋃ i, N i ∧
        (∀ t : ℝ, EqOn (Φ t) id Cᶜ ∧ EqOn (Φ t).symm id Cᶜ) ∧
        Φ 1 '' D ε₀ = D ε₁ ∧
        Φ 1 '' interior (D ε₀) = interior (D ε₁) ∧
        Φ 1 '' frontier (D ε₀) = frontier (D ε₁) := by
    have hR (i) : 3 * max (ε₀ i) (ε₁ i) < R i :=
      (mul_le_mul_of_nonneg_left (max_le (hε₀ i).2 (hε₁ i).2)
        (by norm_num : (0 : ℝ) ≤ 3)).trans_lt (hδR i)
    obtain ⟨Φ, C, hΦ, hi, hz, hC, hCN, hfix, himage⟩ :=
      exists_isotopy_between_finite_affine_corner_replacements e ε₀ ε₁ R d σ
        (fun i => (hε₀ i).1) (fun i => (hε₁ i).1) hR hd hσ hdisjK
    exact ⟨Φ, C, hΦ, hi, hz, hC, hCN, hfix, himage (closure (inside P.carrier))⟩
  refine ⟨e, U, d, σ, δ, R, r, hnorm, hc, hdisj, hn, ?_, hisotopy⟩
  intro ε hε
  change IsCompact (D ε) ∧
    (∀ p ∉ ⋃ i, K i, p ∈ D ε ↔ p ∈ closure (inside P.carrier)) ∧
    ∀ p ∈ frontier (D ε), ∃ (V : Set Plane) (G : Plane → ℝ),
      IsOpen V ∧ p ∈ V ∧ ContDiff ℝ ∞ G ∧ fderiv ℝ G p ≠ 0 ∧
      ∀ q ∈ V, (q ∈ D ε ↔ 0 ≤ G q) ∧
        (q ∈ interior (D ε) ↔ 0 < G q) ∧ (q ∈ frontier (D ε) ↔ G q = 0)
  obtain ⟨Ψ, C, _, _, _, _, hCN, hfix, himage, _, _⟩ :=
    hisotopy δ ε (fun i => ⟨hδ i, le_rfl⟩) hε
  have hregular : ∀ p ∈ frontier (D δ), ∃ (V : Set Plane) (G : Plane → ℝ),
      IsOpen V ∧ p ∈ V ∧ ContDiff ℝ ∞ G ∧ fderiv ℝ G p ≠ 0 ∧
      ∀ q ∈ V, (q ∈ D δ ↔ 0 ≤ G q) ∧
        (q ∈ interior (D δ) ↔ 0 < G q) ∧ (q ∈ frontier (D δ) ↔ G q = 0) := by
    intro p hp
    obtain ⟨V, G, hV, hpV, hG, hreg, hsides⟩ := hglobal p hp
    exact ⟨V, G, hV, hpV, hG, hreg p, hsides⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [← himage]
    exact hD.image (Ψ 1).continuous
  · intro p hp
    have hpC : p ∉ C := fun h => hp ((iUnion_mono hNK) (hCN h))
    have heq : (Ψ 1).symm p = p := (hfix 1).2 hpC
    have hm : p ∈ Ψ 1 '' D δ ↔ (Ψ 1).symm p ∈ D δ := Set.mem_image_equiv
    rw [← himage, hm, heq]
    exact hout p hp
  · rw [← himage]
    exact (Ψ 1).regular_frontier_image hregular

end Schoenflies

end

section
open Set Metric
open scoped ContDiff Manifold

namespace Schoenflies

theorem PrePolygon.exists_compatible_native_rounding_families
    {m : ℕ} (P : PrePolygon m) (O : Fin 2 → ZMod (m + 3) → Set Plane)
    (hO : ∀ k i, IsOpen (O k i)) (hiO : ∀ k i, P.vertex i ∈ O k i) :
    ∃ (e : Fin 2 → ZMod (m + 3) → Plane ≃ᵃ[ℝ] Plane)
      (U : Fin 2 → ZMod (m + 3) → Set Plane) (d σ δ R r : Fin 2 → ZMod (m + 3) → ℝ),
      (∀ k i, 0 < r k i ∧ e k i (P.vertex (i - 1)) = Plane.mk (-1) 0 ∧
        e k i (P.vertex (i + 1)) = Plane.mk (r k i) (d k i * r k i)) ∧
      (∀ k i, IsOpen (U k i) ∧ P.vertex i ∈ U k i ∧ U k i ⊆ O k i ∧
        e k i (P.vertex i) = 0 ∧ (d k i = 0 ∨ d k i = 1) ∧
        (σ k i = -1 ∨ σ k i = 1) ∧
        (d k i = 0 ↔ Plane.det (P.vertex (i - 1) - P.vertex i)
          (P.vertex (i + 1) - P.vertex i) = 0) ∧ 0 < δ k i ∧ 3 * δ k i < R k i ∧
        ∀ p ∈ U k i, p ∈ closure (inside P.carrier) ↔
          0 ≤ σ k i * ((e k i p) 1 - d k i * max ((e k i p) 0) 0)) ∧
      (∀ k, Pairwise fun i j => Disjoint (U k i) (U k j)) ∧
      (∀ k i, e k i ⁻¹' closedBall (0 : Plane) (R k i) ⊆ U k i) ∧
      ∀ ε : Fin 2 → ZMod (m + 3) → ℝ, (∀ k i, 0 < ε k i ∧ ε k i ≤ δ k i) →
        let D := fun k => (closure (inside P.carrier) \
          ⋃ i, e k i ⁻¹' ball (0 : Plane) (R k i)) ∪
          ⋃ i, (e k i ⁻¹' closedBall (0 : Plane) (R k i)) ∩
            {p | 0 ≤ σ k i * ((e k i p) 1 -
              d k i * Real.smoothMax (ε k i) ((e k i p) 0) 0)}
        (∀ k, IsCompact (D k) ∧
          ∀ p ∈ frontier (D k), ∃ (V : Set Plane) (G : Plane → ℝ),
            IsOpen V ∧ p ∈ V ∧ ContDiff ℝ ∞ G ∧ fderiv ℝ G p ≠ 0 ∧
              ∀ q ∈ V, (q ∈ D k ↔ 0 ≤ G q) ∧
                (q ∈ interior (D k) ↔ 0 < G q) ∧ (q ∈ frontier (D k) ↔ G q = 0)) ∧
        ∃ (Φ : ℝ → Plane ≃ₘ[ℝ] Plane) (C : Set Plane),
          ContDiff ℝ ∞ (fun z : ℝ × Plane => Φ z.1 z.2) ∧
          ContDiff ℝ ∞ (fun z : ℝ × Plane => (Φ z.1).symm z.2) ∧
          Φ 0 = Diffeomorph.refl 𝓘(ℝ, Plane) Plane ∞ ∧
          IsCompact C ∧ C ⊆ ⋃ i, U 0 i ∪ U 1 i ∧
          (∀ t, EqOn (Φ t) id Cᶜ ∧ EqOn (Φ t).symm id Cᶜ) ∧
          Φ 1 '' D 0 = D 1 ∧ Φ 1 '' interior (D 0) = interior (D 1) ∧
          Φ 1 '' frontier (D 0) = frontier (D 1) := by
  classical
  have hfamily (k : Fin 2) :=
    P.exists_normalized_compatible_finite_vertex_roundings (O k) (hO k) (hiO k)
  choose e U d σ δ R r hnorm hc hdisj hn hround hisotopy using hfamily
  refine ⟨e, U, d, σ, δ, R, r, hnorm, hc, hdisj, fun k i => (hn k i).2.2.2, ?_⟩
  intro ε hε
  refine ⟨?_, ?_⟩
  · intro k
    obtain ⟨hcompact, _, hregular⟩ := hround k (ε k) (hε k)
    exact ⟨hcompact, hregular⟩
  · exact exists_isotopy_between_normalized_corner_replacements
      e (fun i => P.vertex (i - 1)) (fun i => P.vertex (i + 1)) P.vertex U r d σ ε R
      (fun k i => ⟨(hnorm k i).1, (hnorm k i).2.1, (hnorm k i).2.2,
        (hc k i).2.2.2.1⟩)
      (fun k i => (hc k i).1) (fun k i => (hc k i).2.2.2.2.1)
      (fun k i => (hc k i).2.2.2.2.2.1) (fun k i => (hε k i).1)
      (fun k i => (mul_le_mul_of_nonneg_left (hε k i).2
        (by norm_num : (0 : ℝ) ≤ 3)).trans_lt (hc k i).2.2.2.2.2.2.2.2.1)
      (fun k i => (hn k i).2.2.2) hdisj (fun k i => (hc k i).2.2.2.2.2.2.2.2.2)

end Schoenflies

end

section

open Set Metric
open scoped ContDiff Manifold Topology

namespace Schoenflies

theorem PrePolygon.exists_local_rounding_isotopy_of_two_edge_free_triangle
    {m : ℕ} (P : PrePolygon m)
    (M : LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh)
    (hfrontier : frontier M.toPlaneComplex.support = P.carrier)
    (T : M.Triangle) (k : Fin 3) (hfree : M.IsTwoEdgeFreeTriangle T k)
    {σ : ℝ} (hσ : 0 < σ) (hσsmall : σ ≤ 1 / 4) :
    let b := LeanEval.Topology.ClassificationOfSurfaces.Moise.affineBasisOfTriangle
      (M.freeTriangleOrder T k) (M.freeTriangleOrder_affineIndependent T k)
    let R := closure (P.carrier \ (segment ℝ (b 0) (b 2) ∪ segment ℝ (b 1) (b 2)))
    let N := (interior M.toPlaneComplex.support ∩
      {p | 0 < b.coord 0 p ∧ 0 < b.coord 1 p}) ∪
        ((M.eraseTriangle T.1).toPlaneComplex.supportᶜ ∩ {p | 0 < b.coord 2 p})
    ∃ (v₀ v₁ : Plane) (r₀ r₁ : ℝ) (f₀ f₁ : Plane →ᵃ[ℝ] ℝ)
      (e₀ e₁ : Plane ≃ᵃ[ℝ] Plane) (ε₀ ε : ℝ) (J W K : Set Plane)
      (F : Plane → ℝ × ℝ) (H : ℝ → Plane ≃ₘ[ℝ] Plane),
      let s₀ := b.coord 2 v₀ / f₀ v₀
      let s₁ := b.coord 2 v₁ / f₁ v₁
      let U₀ := ball (b 0) r₀ ∩ {p | (1 : ℝ) / 4 < b.coord 0 p - b.coord 1 p}
      let U₁ := ball (b 1) r₁ ∩ {p | (1 : ℝ) / 4 < b.coord 1 p - b.coord 0 p}
      let V := {p | ε₀ < f₀ p ∧ ε₀ < f₁ p} ∩ N
      let D := (M.toPlaneComplex.support \ interior K) ∪ (K ∩ {p | (F p).1 ≤ 0})
      let E := ((M.eraseTriangle T.1).toPlaneComplex.support \ interior K) ∪
        (K ∩ {p | (F p).2 ≤ 0})
      0 < r₀ ∧ 0 < r₁ ∧ Disjoint (ball (b 0) r₀) (ball (b 1) r₁) ∧
      segment ℝ (b 0) v₀ ⊆ R ∧ segment ℝ (b 1) v₁ ⊆ R ∧
      f₀ (b 0) = 0 ∧ 0 < f₀ (b 1) ∧ 0 < f₀ (b 2) ∧ f₀ v₀ < 0 ∧
      f₁ (b 1) = 0 ∧ 0 < f₁ (b 0) ∧ 0 < f₁ (b 2) ∧ f₁ v₁ < 0 ∧
      (∀ p, (e₀ p) 0 = f₀ p ∧ (e₀ p) 1 = b.coord 2 p) ∧
      (∀ p, (e₁ p) 0 = f₁ p ∧ (e₁ p) 1 = b.coord 2 p) ∧
      0 < ε₀ ∧ 0 < ε ∧ ε ≤ ε₀ ∧ IsCompact J ∧
      M.triangleCarrier T.1 ⊆ interior J ∧ IsOpen W ∧ J ⊆ W ∧
      W ⊆ U₀ ∪ U₁ ∪ V ∧ ContDiff ℝ ∞ F ∧
      EqOn F (fun p =>
        (-(f₀ (b 2) / f₀ (b 1) * (s₀ * (f₀ p - Real.smoothMax ε (f₀ p) 0) +
          Real.smoothMax ε (f₀ p) 0 / f₀ (b 2) - b.coord 2 p)),
          -(s₀ * (f₀ p - Real.smoothMax ε (f₀ p) 0) - b.coord 2 p))) (W ∩ U₀) ∧
      EqOn F (fun p =>
        (-(f₁ (b 2) / f₁ (b 0) * (s₁ * (f₁ p - Real.smoothMax ε (f₁ p) 0) +
          Real.smoothMax ε (f₁ p) 0 / f₁ (b 2) - b.coord 2 p)),
          -(s₁ * (f₁ p - Real.smoothMax ε (f₁ p) 0) - b.coord 2 p))) (W ∩ U₁) ∧
      EqOn F (fun p => (Real.smoothMax σ (-b.coord 0 p) (-b.coord 1 p),
        b.coord 2 p)) (W ∩ V) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ W ∩ V,
        (1 - t) * (F p).1 + t * (F p).2 = 0 → p ∈ M.triangleCarrier T.1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ W,
        fderiv ℝ (fun q => (1 - t) * (F q).1 + t * (F q).2) p ≠ 0) ∧
      (∀ p ∈ W, p ∉ interior J →
        (p ∈ M.toPlaneComplex.support ↔ (F p).1 ≤ 0) ∧
        (p ∈ interior M.toPlaneComplex.support ↔ (F p).1 < 0) ∧
        (p ∈ frontier M.toPlaneComplex.support ↔ (F p).1 = 0)) ∧
      (∀ p ∈ W, p ∉ interior J →
        (p ∈ (M.eraseTriangle T.1).toPlaneComplex.support ↔ (F p).2 ≤ 0) ∧
        (p ∈ interior (M.eraseTriangle T.1).toPlaneComplex.support ↔ (F p).2 < 0) ∧
        (p ∈ frontier (M.eraseTriangle T.1).toPlaneComplex.support ↔ (F p).2 = 0)) ∧
      IsCompact K ∧ J ⊆ interior K ∧ K ⊆ W ∧
      ContDiff ℝ ∞ (fun z : ℝ × Plane => H z.1 z.2) ∧
      ContDiff ℝ ∞ (fun z : ℝ × Plane => (H z.1).symm z.2) ∧
      H 0 = Diffeomorph.refl 𝓘(ℝ, Plane) Plane ∞ ∧
      (∀ t, EqOn (H t) id Kᶜ ∧ EqOn (H t).symm id Kᶜ ∧
        (∀ p, H t p ∈ W ↔ p ∈ W) ∧ (∀ p, (H t).symm p ∈ W ↔ p ∈ W)) ∧
      (∀ p ∈ W, ((F p).1 = 0 ↔ (F (H 1 p)).2 = 0) ∧
        ((F p).1 < 0 ↔ (F (H 1 p)).2 < 0) ∧ ((F p).1 ≤ 0 ↔ (F (H 1 p)).2 ≤ 0)) ∧
      (∀ p ∈ W, ((F p).2 = 0 ↔ (F ((H 1).symm p)).1 = 0) ∧
        ((F p).2 < 0 ↔ (F ((H 1).symm p)).1 < 0) ∧
        ((F p).2 ≤ 0 ↔ (F ((H 1).symm p)).1 ≤ 0)) ∧
      IsCompact D ∧ IsCompact E ∧
      (∀ p ∈ W, (p ∈ D ↔ (F p).1 ≤ 0) ∧
        (p ∈ interior D ↔ (F p).1 < 0) ∧ (p ∈ frontier D ↔ (F p).1 = 0)) ∧
      (∀ p ∈ W, (p ∈ E ↔ (F p).2 ≤ 0) ∧
        (p ∈ interior E ↔ (F p).2 < 0) ∧ (p ∈ frontier E ↔ (F p).2 = 0)) ∧
      (∀ p ∉ K, (p ∈ D ↔ p ∈ M.toPlaneComplex.support) ∧
        (p ∈ interior D ↔ p ∈ interior M.toPlaneComplex.support) ∧
        (p ∈ frontier D ↔ p ∈ frontier M.toPlaneComplex.support)) ∧
      (∀ p ∉ K, (p ∈ E ↔ p ∈ (M.eraseTriangle T.1).toPlaneComplex.support) ∧
        (p ∈ interior E ↔ p ∈ interior (M.eraseTriangle T.1).toPlaneComplex.support) ∧
        (p ∈ frontier E ↔ p ∈ frontier (M.eraseTriangle T.1).toPlaneComplex.support)) ∧
      (H 1) '' D = E ∧ (H 1) '' interior D = interior E ∧
      (H 1) '' frontier D = frontier E ∧
      (H 1).symm '' E = D ∧ (H 1).symm '' interior E = interior D ∧
      (H 1).symm '' frontier E = frontier D := by
  dsimp only
  obtain ⟨v₀, v₁, r₀, r₁, f₀, f₁, e₀, e₁, ε₀, ε, J, W, F,
      hr₀, hr₁, hdisj, hs₀, hs₁, hf₀, hfb, hfc₀, hfv₀, hf₁, hfa, hfc₁, hfv₁, he₀, he₁,
      hε₀, hε, hεle, hJ, hTJ, hW, hJW, hcover, hF, heW₀, heW₁, heWV, hzeroC, hreg,
      hold, herased, hprop⟩ :=
    P.exists_regular_interpolation_near_two_edge_free_triangle M hfrontier T k hfree hσ hσsmall
  obtain ⟨K, H, hK, hJK, hKW, hH, hHi, hH0, hfix, hforward, hinverse⟩ :=
    Diffeomorph.exists_isotopy_level_and_sublevels_of_proportional_interpolation
      hF.fst hF.snd hW hJ hJW (fun t ht p hp _ => hreg t ht p (hJW hp)) hprop
  have hsides (p : Plane) (hp : p ∈ W) (hpJ : p ∉ interior J) :=
    And.intro (hold p hp hpJ) (herased p hp hpJ)
  have hreg₀ (p : Plane) (hp : p ∈ W) :
      fderiv ℝ (fun q => (F q).1) p ≠ 0 := by
    simpa only [sub_zero, one_mul, zero_mul, add_zero] using
      hreg 0 ⟨le_rfl, zero_le_one⟩ p hp
  have hreg₁ (p : Plane) (hp : p ∈ W) :
      fderiv ℝ (fun q => (F q).2) p ≠ 0 := by
    simpa only [sub_self, zero_mul, one_mul, zero_add] using
      hreg 1 ⟨zero_le_one, le_rfl⟩ p hp
  let D := (M.toPlaneComplex.support \ interior K) ∪ (K ∩ {p | (F p).1 ≤ 0})
  let E := ((M.eraseTriangle T.1).toPlaneComplex.support \ interior K) ∪
    (K ∩ {p | (F p).2 ≤ 0})
  obtain ⟨hD, hDsides, hDraw⟩ := compact_sublevel_replacement_preserving_germ
    M.toPlaneComplex.isCompact_support hK hW hKW hF.fst.continuous
    (fun p hp _ => hreg₀ p hp)
    (fun p hp => (hsides p hp.1 (fun hj => hp.2 (hJK (interior_subset hj)))).1.1)
  obtain ⟨hE, hEsides, hEraw⟩ := compact_sublevel_replacement_preserving_germ
    (M.eraseTriangle T.1).toPlaneComplex.isCompact_support hK hW hKW hF.snd.continuous
    (fun p hp _ => hreg₁ p hp)
    (fun p hp => (hsides p hp.1 (fun hj => hp.2 (hJK (interior_subset hj)))).2.1)
  have himage : (H 1) '' D = E := by
    ext p
    change p ∈ (H 1).toEquiv '' D ↔ p ∈ E
    rw [Set.mem_image_equiv]
    change (H 1).symm p ∈ D ↔ p ∈ E
    by_cases hp : p ∈ W
    · exact (hDsides ((H 1).symm p) (((hfix 1).2.2.2 p).mpr hp)).1.trans
        ((hinverse p hp).2.2.symm.trans (hEsides p hp).1.symm)
    · have hpK : p ∉ K := fun h => hp (hKW h)
      rw [(hfix 1).2.1 hpK]
      have hpT : p ∉ M.triangleCarrier T.1 :=
        fun h => hpK (interior_subset (hJK (interior_subset (hTJ h))))
      have hsame : p ∈ M.toPlaneComplex.support ↔
          p ∈ (M.eraseTriangle T.1).toPlaneComplex.support := by
        rw [M.support_eq_eraseTriangle_union_triangleCarrier T.2]
        exact or_iff_left hpT
      exact (hDraw p hpK).1.trans (hsame.trans (hEraw p hpK).1.symm)
  have hinverseImage : (H 1).symm '' E = D := by
    rw [← himage]
    exact (H 1).toEquiv.symm_image_image D
  refine ⟨v₀, v₁, r₀, r₁, f₀, f₁, e₀, e₁, ε₀, ε, J, W, K, F, H,
    hr₀, hr₁, hdisj, hs₀, hs₁, hf₀, hfb, hfc₀, hfv₀, hf₁, hfa, hfc₁, hfv₁, he₀, he₁,
    hε₀, hε, hεle, hJ, hTJ, hW, hJW, hcover, hF, heW₀, heW₁, heWV, hzeroC, hreg,
    fun p hp hpJ => (hsides p hp hpJ).1, fun p hp hpJ => (hsides p hp hpJ).2,
    hK, hJK, hKW, hH, hHi, hH0, hfix, hforward, hinverse,
    hD, hE, hDsides, hEsides, hDraw, hEraw, himage, ?_, ?_, hinverseImage, ?_, ?_⟩
  · exact ((H 1).toHomeomorph.image_interior D).trans (congrArg interior himage)
  · exact ((H 1).toHomeomorph.image_frontier D).trans (congrArg frontier himage)
  · exact ((H 1).symm.toHomeomorph.image_interior E).trans (congrArg interior hinverseImage)
  · exact ((H 1).symm.toHomeomorph.image_frontier E).trans (congrArg frontier hinverseImage)

end Schoenflies

end

section

open Set Metric

namespace Schoenflies

private theorem PrePolygon.exists_pos_smul_incident_edges_of_local_carrier_eq
    {m n : ℕ} (P : PrePolygon m) (Q : PrePolygon n)
    (i : ZMod (m + 3)) (j : ZMod (n + 3))
    (hij : Q.vertex j = P.vertex i) {U : Set Plane}
    (hU : IsOpen U) (hiU : P.vertex i ∈ U)
    (hcar : ∀ x ∈ U, x ∈ P.carrier ↔ x ∈ Q.carrier)
    (hdet : Plane.det (P.vertex (i - 1) - P.vertex i)
      (P.vertex (i + 1) - P.vertex i) ≠ 0) :
    Plane.det (Q.vertex (j - 1) - Q.vertex j)
      (Q.vertex (j + 1) - Q.vertex j) ≠ 0 ∧
    ∃ r s : ℝ, 0 < r ∧ 0 < s ∧
      ((P.vertex (i - 1) - P.vertex i = r • (Q.vertex (j - 1) - Q.vertex j) ∧
        P.vertex (i + 1) - P.vertex i = s • (Q.vertex (j + 1) - Q.vertex j)) ∨
       (P.vertex (i - 1) - P.vertex i = r • (Q.vertex (j + 1) - Q.vertex j) ∧
        P.vertex (i + 1) - P.vertex i = s • (Q.vertex (j - 1) - Q.vertex j))) := by
  obtain ⟨ρ, hρ, hlocal⟩ := Q.exists_ball_carrier_eq_incident_edges j
  let V := U ∩ ball (Q.vertex j) ρ
  have hV : IsOpen V := hU.inter isOpen_ball
  have hiV : P.vertex i ∈ V := ⟨hiU, by rw [← hij]; exact mem_ball_self hρ⟩
  have hQprev : Q.vertex (j - 1) - Q.vertex j ≠ 0 := by
    apply sub_ne_zero.mpr
    intro he
    have hi := Q.vertex_inj he
    exact ClosedPolygon.succ_ne_self (j - 1) (by simpa only [sub_add_cancel] using hi.symm)
  have hQnext : Q.vertex (j + 1) - Q.vertex j ≠ 0 :=
    sub_ne_zero.mpr (fun he => ClosedPolygon.succ_ne_self j (Q.vertex_inj he))
  have hQ (x : Plane) (hx : x ∈ V) (hxP : x ∈ P.carrier) :
      x ∈ segment ℝ (P.vertex i) (Q.vertex (j - 1)) ∪
        segment ℝ (P.vertex i) (Q.vertex (j + 1)) := by
    have hxQ : x ∈ ball (Q.vertex j) ρ ∩ Q.carrier := ⟨hx.2, (hcar x hx.1).mp hxP⟩
    rw [hlocal] at hxQ
    have he := hxQ.2
    change x ∈ segment ℝ (Q.vertex (j - 1)) (Q.vertex (j - 1 + 1)) ∪
      segment ℝ (Q.vertex j) (Q.vertex (j + 1)) at he
    rw [sub_add_cancel, segment_symm ℝ (Q.vertex (j - 1)), hij] at he
    exact he
  have hprev := sameRay_or_of_local_segment_subset hV hiV (fun x hx hseg =>
    hQ x hx (P.edge_subset_carrier (i - 1) (by
      change x ∈ segment ℝ (P.vertex (i - 1)) (P.vertex (i - 1 + 1))
      rw [sub_add_cancel, segment_symm]
      exact hseg)))
  have hnext := sameRay_or_of_local_segment_subset hV hiV (fun x hx hseg =>
    hQ x hx (P.edge_subset_carrier i hseg))
  rw [← hij] at hprev hnext
  have hdet' : Plane.det (P.vertex (i - 1) - Q.vertex j)
      (P.vertex (i + 1) - Q.vertex j) ≠ 0 := by simpa only [hij] using hdet
  have h := exists_pos_smul_pair_of_sameRay_or hdet' hQprev hQnext hprev hnext
  simpa only [hij] using h

end Schoenflies

end

section

open Set Metric

namespace Schoenflies

private theorem PrePolygon.exists_matching_vertex_of_local_carrier_eq
    {m n : ℕ} (P : PrePolygon m) (Q : PrePolygon n) (i : ZMod (m + 3))
    {U : Set Plane} (hU : IsOpen U) (hiU : P.vertex i ∈ U)
    (hcar : ∀ x ∈ U, x ∈ P.carrier ↔ x ∈ Q.carrier)
    (hdet : Plane.det (P.vertex (i - 1) - P.vertex i)
      (P.vertex (i + 1) - P.vertex i) ≠ 0) :
    ∃ j : ZMod (n + 3), Q.vertex j = P.vertex i ∧
      Plane.det (Q.vertex (j - 1) - Q.vertex j)
        (Q.vertex (j + 1) - Q.vertex j) ≠ 0 ∧
      ∃ r s : ℝ, 0 < r ∧ 0 < s ∧
        ((P.vertex (i - 1) - P.vertex i = r • (Q.vertex (j - 1) - Q.vertex j) ∧
          P.vertex (i + 1) - P.vertex i = s • (Q.vertex (j + 1) - Q.vertex j)) ∨
         (P.vertex (i - 1) - P.vertex i = r • (Q.vertex (j + 1) - Q.vertex j) ∧
          P.vertex (i + 1) - P.vertex i = s • (Q.vertex (j - 1) - Q.vertex j))) := by
  have hp := (P.isCornerAt_vertex_of_det_ne_zero i hdet).of_local_subset hU hiU
    (fun x hx hxP => (hcar x hx).mp hxP)
  obtain ⟨j, hj⟩ := Q.exists_vertex_eq_of_isCornerAt hp
  exact ⟨j, hj, P.exists_pos_smul_incident_edges_of_local_carrier_eq Q i j hj
    hU hiU hcar hdet⟩

end Schoenflies

end

section

open Set Metric

namespace Schoenflies

private theorem replacement_eq_core_of_local_agreement
    {X : Type*} {D A C N K : Set X} (hCN : C ⊆ N) (hNK : N ⊆ K)
    (heq : ∀ p ∈ K \ C, p ∈ A ↔ p ∈ D) :
    (D \ N) ∪ (K ∩ A) = (D \ C) ∪ (C ∩ A) := by
  ext p
  by_cases hpC : p ∈ C
  · have hpN := hCN hpC
    have hpK := hNK hpN
    simp only [mem_union, mem_sdiff, mem_inter_iff, hpC, hpN, hpK, not_true_eq_false,
      and_false, true_and, false_or]
  · by_cases hpK : p ∈ K
    · have hpAD := heq p ⟨hpK, hpC⟩
      by_cases hpN : p ∈ N <;> simp [hpC, hpN, hpK, hpAD]
    · have hpN : p ∉ N := fun h => hpK (hNK h)
      simp [hpC, hpN, hpK]

private theorem replacement_eq_of_common_core
    {X : Type*} [TopologicalSpace X] {D A C N₀ K₀ N₁ K₁ : Set X}
    (hC : C ⊆ N₀ ∩ N₁) (hNK₀ : N₀ ⊆ K₀) (hNK₁ : N₁ ⊆ K₁)
    (heq : ∀ p ∈ (K₀ ∪ K₁) \ C, p ∈ A ↔ p ∈ D) :
    let D₀ := (D \ N₀) ∪ (K₀ ∩ A)
    let D₁ := (D \ N₁) ∪ (K₁ ∩ A)
    D₀ = D₁ ∧ interior D₀ = interior D₁ ∧ frontier D₀ = frontier D₁ := by
  have h₀ := replacement_eq_core_of_local_agreement (fun p hp => (hC hp).1) hNK₀
    (fun p hp => heq p ⟨Or.inl hp.1, hp.2⟩)
  have h₁ := replacement_eq_core_of_local_agreement (fun p hp => (hC hp).2) hNK₁
    (fun p hp => heq p ⟨Or.inr hp.1, hp.2⟩)
  have h := h₀.trans h₁.symm
  exact ⟨h, congrArg interior h, congrArg frontier h⟩

private theorem affine_corner_replacement_eq_of_common_core
    (e : Plane ≃ᵃ[ℝ] Plane) {ε d σ : ℝ} {D N₀ K₀ N₁ K₁ : Set Plane}
    (hε : 0 < ε) (hd : d = 0 ∨ d = 1)
    (hNK₀ : N₀ ⊆ K₀) (hNK₁ : N₁ ⊆ K₁)
    (hC : e ⁻¹' closedBall (0 : Plane) (3 * ε) ⊆ N₀ ∩ N₁)
    (hside : ∀ p ∈ K₀ ∪ K₁, p ∈ D ↔
      0 ≤ σ * ((e p) 1 - d * max ((e p) 0) 0)) :
    let A := {p | 0 ≤ σ * ((e p) 1 - d * Real.smoothMax ε ((e p) 0) 0)}
    let D₀ := (D \ N₀) ∪ (K₀ ∩ A)
    let D₁ := (D \ N₁) ∪ (K₁ ∩ A)
    D₀ = D₁ ∧ interior D₀ = interior D₁ ∧ frontier D₀ = frontier D₁ := by
  apply replacement_eq_of_common_core hC hNK₀ hNK₁
  intro p hp
  have hnorm : 3 * ε < ‖e p‖ := by
    apply lt_of_not_ge
    intro h
    exact hp.2 (mem_closedBall_zero_iff.mpr h)
  exact (smooth_corner_signs_eq_outside_ball (σ := σ) hε hd hnorm).1.trans
    (hside p hp.1).symm

private theorem exists_width_affine_corner_replacement_eq
    (e : Plane ≃ᵃ[ℝ] Plane) {c : Plane} {d σ δ : ℝ} {D N₀ K₀ N₁ K₁ : Set Plane}
    (hc : e c = 0) (hδ : 0 < δ) (hd : d = 0 ∨ d = 1)
    (hN₀ : IsOpen N₀) (hN₁ : IsOpen N₁) (hcN₀ : c ∈ N₀) (hcN₁ : c ∈ N₁)
    (hNK₀ : N₀ ⊆ K₀) (hNK₁ : N₁ ⊆ K₁)
    (hside : ∀ p ∈ K₀ ∪ K₁, p ∈ D ↔
      0 ≤ σ * ((e p) 1 - d * max ((e p) 0) 0)) :
    ∃ η : ℝ, 0 < η ∧ η ≤ δ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ η →
      let A := {p | 0 ≤ σ * ((e p) 1 - d * Real.smoothMax ε ((e p) 0) 0)}
      let D₀ := (D \ N₀) ∪ (K₀ ∩ A)
      let D₁ := (D \ N₁) ∪ (K₁ ∩ A)
      e ⁻¹' closedBall (0 : Plane) (3 * ε) ⊆ N₀ ∩ N₁ ∧
        D₀ = D₁ ∧ interior D₀ = interior D₁ ∧ frontier D₀ = frontier D₁ := by
  obtain ⟨R, hR, _, hRW⟩ := exists_affine_closed_ball_subset
    (hN₀.inter hN₁) e ⟨hcN₀, hcN₁⟩ hc
  let η := min δ (R / 4)
  have hη : 0 < η := lt_min hδ (div_pos hR (by norm_num))
  have hηδ : η ≤ δ := min_le_left _ _
  have hsmall (ε : ℝ) (hε : ε ≤ η) :
      e ⁻¹' closedBall (0 : Plane) (3 * ε) ⊆ N₀ ∩ N₁ := by
    have hεR : ε ≤ R / 4 := hε.trans (min_le_right _ _)
    exact (preimage_mono (closedBall_subset_closedBall (by linarith))).trans hRW
  refine ⟨η, hη, hηδ, fun ε hε hεη => ?_⟩
  exact ⟨hsmall ε hεη, affine_corner_replacement_eq_of_common_core e hε hd
    hNK₀ hNK₁ (hsmall ε hεη) hside⟩

end Schoenflies

end

section

open Set Metric

namespace Schoenflies

private theorem exists_small_equal_reanchored_corner_replacements
    (e f : Plane ≃ᵃ[ℝ] Plane) {c : Plane} {ℓ σ R δ : ℝ} {D U : Set Plane}
    (hec : e c = 0) (hfc : f c = 0) (hℓ : 0 < ℓ) (hR : 0 < R) (hδ : 0 < δ)
    (hU : IsOpen U) (hcU : c ∈ U)
    (hKU : e ⁻¹' closedBall (0 : Plane) R ⊆ U)
    (hside : ∀ p ∈ U, p ∈ D ↔ 0 ≤ σ * ((e p) 1 - max ((e p) 0) 0))
    (hraw : ∀ p, (f p) 1 - max ((f p) 0) 0 = ℓ * ((e p) 1 - max ((e p) 0) 0))
    (hsmooth : ∀ ε : ℝ, ε ≠ 0 → ∀ p,
      (f p) 1 - Real.smoothMax (ℓ * ε) ((f p) 0) 0 =
        ℓ * ((e p) 1 - Real.smoothMax ε ((e p) 0) 0)) :
    ∃ S η : ℝ, 0 < S ∧ 0 < η ∧ η ≤ δ ∧ f ⁻¹' closedBall (0 : Plane) S ⊆ U ∧
      (∀ p ∈ U, p ∈ D ↔ 0 ≤ σ * ((f p) 1 - max ((f p) 0) 0)) ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ η →
        let D₀ := (D \ e ⁻¹' ball (0 : Plane) R) ∪
          (e ⁻¹' closedBall (0 : Plane) R) ∩
            {p | 0 ≤ σ * ((e p) 1 - Real.smoothMax ε ((e p) 0) 0)}
        let D₁ := (D \ f ⁻¹' ball (0 : Plane) S) ∪
          (f ⁻¹' closedBall (0 : Plane) S) ∩
            {p | 0 ≤ σ * ((f p) 1 - Real.smoothMax (ℓ * ε) ((f p) 0) 0)}
        3 * ε < R ∧ 3 * (ℓ * ε) < S ∧
          D₀ = D₁ ∧ interior D₀ = interior D₁ ∧ frontier D₀ = frontier D₁ := by
  obtain ⟨S, hS, hcS, hSU⟩ := exists_affine_closed_ball_subset hU f hcU hfc
  let ζ := min δ (min (R / 4) (S / (4 * ℓ)))
  have hζ : 0 < ζ := lt_min hδ (lt_min (div_pos hR (by norm_num))
    (div_pos hS (mul_pos (by norm_num) hℓ)))
  have he : Continuous e := e.toAffineMap.continuous_of_finiteDimensional
  have hf : Continuous f := f.toAffineMap.continuous_of_finiteDimensional
  have hcR : c ∈ e ⁻¹' ball (0 : Plane) R := by
    change e c ∈ ball (0 : Plane) R
    rw [hec]
    exact mem_ball_self hR
  obtain ⟨η, hη, hηζ, hcut⟩ := exists_width_affine_corner_replacement_eq e hec hζ
    (d := 1) (Or.inr rfl) (isOpen_ball.preimage he) (isOpen_ball.preimage hf)
    hcR hcS (preimage_mono ball_subset_closedBall) (preimage_mono ball_subset_closedBall)
    (D := D) (K₀ := e ⁻¹' closedBall (0 : Plane) R)
    (K₁ := f ⁻¹' closedBall (0 : Plane) S) (by
      intro p hp
      simpa only [one_mul] using hside p (hp.elim (fun h => hKU h) (fun h => hSU h)))
  refine ⟨S, η, hS, hη, hηζ.trans (min_le_left _ _), hSU, ?_, ?_⟩
  · intro p hp
    rw [hraw p, mul_left_comm σ ℓ, mul_nonneg_iff_of_pos_left hℓ]
    exact hside p hp
  · intro ε hε hεη
    have hεR : ε ≤ R / 4 := hεη.trans
      (hηζ.trans ((min_le_right _ _).trans (min_le_left _ _)))
    have hεS : ε ≤ S / (4 * ℓ) := hεη.trans
      (hηζ.trans ((min_le_right _ _).trans (min_le_right _ _)))
    have hεSmul : ε * (4 * ℓ) ≤ S :=
      (le_div_iff₀ (mul_pos (by norm_num) hℓ)).mp hεS
    have hsmallR : 3 * ε < R := by linarith only [hεR, hR]
    have hsmallS : 3 * (ℓ * ε) < S := by nlinarith only [hεSmul, hS]
    have hA : {p | 0 ≤ σ * ((f p) 1 - Real.smoothMax (ℓ * ε) ((f p) 0) 0)} =
        {p | 0 ≤ σ * ((e p) 1 - Real.smoothMax ε ((e p) 0) 0)} := by
      ext p
      simp only [mem_ofPred_eq, hsmooth ε hε.ne' p, mul_left_comm σ ℓ,
        mul_nonneg_iff_of_pos_left hℓ]
    have h := (hcut ε hε hεη).2
    simp only [one_mul] at h
    dsimp only
    rw [hA]
    exact ⟨hsmallR, hsmallS, h⟩

end Schoenflies

end

section

open Set Metric

namespace Schoenflies

private theorem PrePolygon.exists_equal_reanchored_corner_replacement
    {m n : ℕ} (P : PrePolygon m) (Q : PrePolygon n)
    (i : ZMod (m + 3)) (j : ZMod (n + 3)) (hij : Q.vertex j = P.vertex i)
    (e : Plane ≃ᵃ[ℝ] Plane) {r d σ R δ : ℝ} {D V U : Set Plane}
    (hnorm : 0 < r ∧ e (Q.vertex j) = 0 ∧
      e (Q.vertex (j - 1)) = Plane.mk (-1) 0 ∧
      e (Q.vertex (j + 1)) = Plane.mk r (d * r))
    (hd : d = 0 ∨ d = 1)
    (hstraight : d = 0 ↔ Plane.det (Q.vertex (j - 1) - Q.vertex j)
      (Q.vertex (j + 1) - Q.vertex j) = 0)
    (hR : 0 < R) (hδ : 0 < δ)
    (hV : IsOpen V) (hjV : Q.vertex j ∈ V) (hKV : e ⁻¹' closedBall (0 : Plane) R ⊆ V)
    (hside : ∀ p ∈ V, p ∈ D ↔ 0 ≤ σ * ((e p) 1 - d * max ((e p) 0) 0))
    (hU : IsOpen U) (hiU : P.vertex i ∈ U)
    (hcar : ∀ x ∈ U, x ∈ P.carrier ↔ x ∈ Q.carrier)
    (hdet : Plane.det (P.vertex (i - 1) - P.vertex i)
      (P.vertex (i + 1) - P.vertex i) ≠ 0) :
    ∃ (f : Plane ≃ᵃ[ℝ] Plane) (ρ ℓ S η : ℝ),
      d = 1 ∧ 0 < ρ ∧ 0 < ℓ ∧
      f (P.vertex i) = 0 ∧ f (P.vertex (i - 1)) = Plane.mk (-1) 0 ∧
      f (P.vertex (i + 1)) = Plane.mk ρ ρ ∧
      ((∀ p, f p = ℓ • e p) ∨ (∀ p, f p = ℓ • cornerSwap (e p))) ∧
      (∀ p, (f p) 1 - max ((f p) 0) 0 = ℓ * ((e p) 1 - max ((e p) 0) 0)) ∧
      (∀ ε : ℝ, ε ≠ 0 → ∀ p,
        (f p) 1 - Real.smoothMax (ℓ * ε) ((f p) 0) 0 =
          ℓ * ((e p) 1 - Real.smoothMax ε ((e p) 0) 0)) ∧
      0 < S ∧ 0 < η ∧ η ≤ δ ∧ f ⁻¹' closedBall (0 : Plane) S ⊆ V ∧
      (∀ p ∈ V, p ∈ D ↔ 0 ≤ σ * ((f p) 1 - max ((f p) 0) 0)) ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ η →
        let D₀ := (D \ e ⁻¹' ball (0 : Plane) R) ∪
          (e ⁻¹' closedBall (0 : Plane) R) ∩
            {p | 0 ≤ σ * ((e p) 1 - d * Real.smoothMax ε ((e p) 0) 0)}
        let D₁ := (D \ f ⁻¹' ball (0 : Plane) S) ∪
          (f ⁻¹' closedBall (0 : Plane) S) ∩
            {p | 0 ≤ σ * ((f p) 1 - Real.smoothMax (ℓ * ε) ((f p) 0) 0)}
        3 * ε < R ∧ 3 * (ℓ * ε) < S ∧
          D₀ = D₁ ∧ interior D₀ = interior D₁ ∧ frontier D₀ = frontier D₁ := by
  obtain ⟨hdetQ, α, β, hα, hβ, hmatch⟩ :=
    P.exists_pos_smul_incident_edges_of_local_carrier_eq Q i j hij hU hiU hcar hdet
  have hdj : d = 1 := hd.resolve_left (fun h => hdetQ (hstraight.mp h))
  have hb : e (Q.vertex (j + 1)) = Plane.mk r r := by
    simpa only [hdj, one_mul] using hnorm.2.2.2
  have hec : e (P.vertex i) = 0 := by simpa only [hij] using hnorm.2.1
  obtain ⟨f, ρ, ℓ, hρ, hℓ, hfc, hfa, hfb, hform, hraw, hsmooth⟩ :=
    exists_reanchored_affine_corner_chart e hnorm.1 hα hβ hnorm.2.2.1 hb hec
      (by simpa only [hij] using hmatch)
  obtain ⟨S, η, hS, hη, hηδ, hSV, hsidef, hcompare⟩ :=
    exists_small_equal_reanchored_corner_replacements e f hec hfc hℓ hR hδ hV
      (hij ▸ hjV) hKV (D := D)
      (by intro p hp; simpa only [hdj, one_mul] using hside p hp) hraw hsmooth
  refine ⟨f, ρ, ℓ, S, η, hdj, hρ, hℓ, hfc, hfa, hfb, hform, hraw, hsmooth,
    hS, hη, hηδ, hSV, hsidef, ?_⟩
  intro ε hε hεη
  simpa only [hdj, one_mul] using hcompare ε hε hεη

end Schoenflies

end

section

open Set

namespace Schoenflies

private theorem PrePolygon.exists_corner_equiv_of_local_carrier_eq
    {m n : ℕ} (P : PrePolygon m) (Q : PrePolygon n)
    {U : Set Plane} (hU : IsOpen U)
    (hcar : ∀ x ∈ U, x ∈ P.carrier ↔ x ∈ Q.carrier) :
    let I := {i : ZMod (m + 3) // P.vertex i ∈ U ∧
      Plane.det (P.vertex (i - 1) - P.vertex i) (P.vertex (i + 1) - P.vertex i) ≠ 0}
    let J := {j : ZMod (n + 3) // Q.vertex j ∈ U ∧
      Plane.det (Q.vertex (j - 1) - Q.vertex j) (Q.vertex (j + 1) - Q.vertex j) ≠ 0}
    ∃ e : I ≃ J, ∀ i, Q.vertex (e i) = P.vertex i := by
  classical
  let I := {i : ZMod (m + 3) // P.vertex i ∈ U ∧
    Plane.det (P.vertex (i - 1) - P.vertex i) (P.vertex (i + 1) - P.vertex i) ≠ 0}
  let J := {j : ZMod (n + 3) // Q.vertex j ∈ U ∧
    Plane.det (Q.vertex (j - 1) - Q.vertex j) (Q.vertex (j + 1) - Q.vertex j) ≠ 0}
  have hex (i : I) : ∃ j : J, Q.vertex j = P.vertex i := by
    obtain ⟨j, hj, hdet, _⟩ :=
      P.exists_matching_vertex_of_local_carrier_eq Q i hU i.property.1 hcar i.property.2
    exact ⟨⟨j, hj.symm ▸ i.property.1, hdet⟩, hj⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    exact P.vertex_inj ((hf i).symm.trans ((congrArg (fun k : J => Q.vertex k) hij).trans
      (hf j)))
  have hsurj : Function.Surjective f := by
    intro j
    obtain ⟨i, hi, hdet, _⟩ := Q.exists_matching_vertex_of_local_carrier_eq P j hU
      j.property.1 (fun x hx => (hcar x hx).symm) j.property.2
    let i' : I := ⟨i, hi.symm ▸ j.property.1, hdet⟩
    refine ⟨i', Subtype.ext (Q.vertex_inj ?_)⟩
    exact (hf i').trans hi
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, hf⟩

end Schoenflies

end

section

open Set Metric

namespace Schoenflies

private theorem affine_corner_replacement_eq_nonstraight
    {ι : Type*} (D : Set Plane) (e : ι → Plane ≃ᵃ[ℝ] Plane) (ε R d σ : ι → ℝ)
    (hdisj : Pairwise fun i j => Disjoint
      (e i ⁻¹' closedBall (0 : Plane) (R i)) (e j ⁻¹' closedBall (0 : Plane) (R j)))
    (hside : ∀ i, d i = 0 → ∀ p ∈ e i ⁻¹' closedBall (0 : Plane) (R i),
      p ∈ D ↔ 0 ≤ σ i * ((e i p) 1 - d i * max ((e i p) 0) 0)) :
    let N := fun i => e i ⁻¹' ball (0 : Plane) (R i)
    let K := fun i => e i ⁻¹' closedBall (0 : Plane) (R i)
    let A := fun i => {p | 0 ≤ σ i * ((e i p) 1 -
      d i * Real.smoothMax (ε i) ((e i p) 0) 0)}
    let D₀ := (D \ ⋃ i, N i) ∪ ⋃ i, K i ∩ A i
    let D₁ := (D \ ⋃ i : {i // d i ≠ 0}, N i) ∪ ⋃ i : {i // d i ≠ 0}, K i ∩ A i
    D₀ = D₁ ∧ interior D₀ = interior D₁ ∧ frontier D₀ = frontier D₁ := by
  dsimp only
  have heq := indexed_replacement_eq_subtype_of_inactive D
    (fun i => e i ⁻¹' ball (0 : Plane) (R i))
    (fun i => e i ⁻¹' closedBall (0 : Plane) (R i))
    (fun i => {p | 0 ≤ σ i * ((e i p) 1 -
      d i * Real.smoothMax (ε i) ((e i p) 0) 0)})
    (fun i => d i ≠ 0) (fun _ => preimage_mono ball_subset_closedBall) hdisj
    (fun i hi p hp => by
      have hd : d i = 0 := not_ne_iff.mp hi
      simpa only [mem_ofPred_eq, hd, zero_mul, sub_zero] using (hside i hd p hp).symm)
  exact ⟨heq, congrArg interior heq, congrArg frontier heq⟩

end Schoenflies

end

section

open Set

namespace Schoenflies

private theorem PrePolygon.exists_corner_equiv_on_subset
    {m n : ℕ} (P : PrePolygon m) (Q : PrePolygon n)
    {S U : Set Plane} (hU : IsOpen U) (hSU : S ⊆ U)
    (hcar : ∀ x ∈ U, x ∈ P.carrier ↔ x ∈ Q.carrier) :
    let I := {i : ZMod (m + 3) // P.vertex i ∈ S ∧
      Plane.det (P.vertex (i - 1) - P.vertex i) (P.vertex (i + 1) - P.vertex i) ≠ 0}
    let J := {j : ZMod (n + 3) // Q.vertex j ∈ S ∧
      Plane.det (Q.vertex (j - 1) - Q.vertex j) (Q.vertex (j + 1) - Q.vertex j) ≠ 0}
    ∃ e : I ≃ J, ∀ i, Q.vertex (e i) = P.vertex i := by
  obtain ⟨e, he⟩ := P.exists_corner_equiv_of_local_carrier_eq Q hU hcar
  let p : ZMod (m + 3) → Prop := fun i =>
    Plane.det (P.vertex (i - 1) - P.vertex i) (P.vertex (i + 1) - P.vertex i) ≠ 0
  let q : ZMod (n + 3) → Prop := fun j =>
    Plane.det (Q.vertex (j - 1) - Q.vertex j) (Q.vertex (j + 1) - Q.vertex j) ≠ 0
  let rP := Equiv.subtypeSubtypeEquivSubtype
    (p := fun i => P.vertex i ∈ U ∧ p i) (q := fun i => P.vertex i ∈ S ∧ p i)
    (fun h => ⟨hSU h.1, h.2⟩)
  let rQ := Equiv.subtypeSubtypeEquivSubtype
    (p := fun j => Q.vertex j ∈ U ∧ q j) (q := fun j => Q.vertex j ∈ S ∧ q j)
    (fun h => ⟨hSU h.1, h.2⟩)
  let e' := e.subtypeEquiv
    (p := fun i : {i : ZMod (m + 3) // P.vertex i ∈ U ∧ p i} =>
      P.vertex i ∈ S ∧ p i)
    (q := fun j : {j : ZMod (n + 3) // Q.vertex j ∈ U ∧ q j} =>
      Q.vertex j ∈ S ∧ q j)
    (fun i => ⟨fun h => ⟨(he i).symm ▸ h.1, (e i).property.2⟩,
      fun h => ⟨he i ▸ h.1, i.property.2⟩⟩)
  exact ⟨rP.symm.trans (e'.trans rQ), fun i => he (rP.symm i).val⟩

end Schoenflies

end

section

open Set Metric

namespace Schoenflies

private theorem PrePolygon.exists_replacement_reindexing_on_subset
    {m n : ℕ} (P : PrePolygon m) (Q : PrePolygon n)
    {S U : Set Plane} (hU : IsOpen U) (hSU : S ⊆ U)
    (hcar : ∀ x ∈ U, x ∈ P.carrier ↔ x ∈ Q.carrier)
    (D : Set Plane) (e : {j : ZMod (n + 3) // Q.vertex j ∈ S} → Plane ≃ᵃ[ℝ] Plane)
    (R d σ : {j : ZMod (n + 3) // Q.vertex j ∈ S} → ℝ)
    (hstraight : ∀ j, d j = 0 ↔
      Plane.det (Q.vertex ((j : ZMod (n + 3)) - 1) - Q.vertex j)
        (Q.vertex ((j : ZMod (n + 3)) + 1) - Q.vertex j) = 0)
    (hdisj : Pairwise fun i j => Disjoint
      (e i ⁻¹' closedBall (0 : Plane) (R i)) (e j ⁻¹' closedBall (0 : Plane) (R j)))
    (hside : ∀ i, d i = 0 → ∀ p ∈ e i ⁻¹' closedBall (0 : Plane) (R i),
      p ∈ D ↔
        0 ≤ σ i * ((e i p) 1 - d i * max ((e i p) 0) 0)) :
    let I := {i : ZMod (m + 3) // P.vertex i ∈ S ∧
      Plane.det (P.vertex (i - 1) - P.vertex i) (P.vertex (i + 1) - P.vertex i) ≠ 0}
    let J := {j : ZMod (n + 3) // Q.vertex j ∈ S}
    ∃ j : I → J, Function.Injective j ∧
      (∀ i, Q.vertex (j i) = P.vertex i ∧ d (j i) ≠ 0) ∧
      (∀ k : J, d k ≠ 0 → ∃ i, j i = k) ∧
      ∀ ε : J → ℝ,
        let N := fun i => e i ⁻¹' ball (0 : Plane) (R i)
        let K := fun i => e i ⁻¹' closedBall (0 : Plane) (R i)
        let A := fun i => {p | 0 ≤ σ i * ((e i p) 1 -
          d i * Real.smoothMax (ε i) ((e i p) 0) 0)}
        let D₀ := (D \ ⋃ i, N i) ∪ ⋃ i, K i ∩ A i
        let D₁ := (D \ ⋃ i, N (j i)) ∪ ⋃ i, K (j i) ∩ A (j i)
        D₀ = D₁ ∧ interior D₀ = interior D₁ ∧ frontier D₀ = frontier D₁ := by
  classical
  let I := {i : ZMod (m + 3) // P.vertex i ∈ S ∧
    Plane.det (P.vertex (i - 1) - P.vertex i) (P.vertex (i + 1) - P.vertex i) ≠ 0}
  let J := {j : ZMod (n + 3) // Q.vertex j ∈ S}
  let C := {j : ZMod (n + 3) // Q.vertex j ∈ S ∧
    Plane.det (Q.vertex (j - 1) - Q.vertex j) (Q.vertex (j + 1) - Q.vertex j) ≠ 0}
  obtain ⟨v, hv⟩ := P.exists_corner_equiv_on_subset Q hU hSU hcar
  let j : I → J := fun i => ⟨(v i).val, (v i).property.1⟩
  have hj (i : I) : Q.vertex (j i) = P.vertex i := hv i
  have hdj (i : I) : d (j i) ≠ 0 :=
    fun h => (v i).property.2 ((hstraight (j i)).mp h)
  have hinj : Function.Injective j := by
    intro i k h
    apply Subtype.ext
    exact P.vertex_inj ((hj i).symm.trans
      ((congrArg (fun k : J => Q.vertex k) h).trans (hj k)))
  have hcover (k : J) (hk : d k ≠ 0) : ∃ i, j i = k := by
    let k' : C := ⟨k, k.property, fun h => hk ((hstraight k).mpr h)⟩
    obtain ⟨i, hi⟩ := v.surjective k'
    exact ⟨i, Subtype.ext (congrArg (fun z : C => z.val) hi)⟩
  refine ⟨j, hinj, fun i => ⟨hj i, hdj i⟩, hcover, fun ε => ?_⟩
  let f : I → {k : J // d k ≠ 0} := fun i => ⟨j i, hdj i⟩
  have hf : Function.Surjective f := by
    intro k
    obtain ⟨i, hi⟩ := hcover k k.property
    exact ⟨i, Subtype.ext hi⟩
  have heq := (affine_corner_replacement_eq_nonstraight
    D e ε R d σ hdisj hside).1
  rw [← hf.iUnion_comp (fun k => e k ⁻¹' ball (0 : Plane) (R k)),
    ← hf.iUnion_comp (fun k => (e k ⁻¹' closedBall (0 : Plane) (R k)) ∩
      {p | 0 ≤ σ k * ((e k p) 1 - d k * Real.smoothMax (ε k) ((e k p) 0) 0)})] at heq
  exact ⟨heq, congrArg interior heq, congrArg frontier heq⟩

end Schoenflies

end

section

open Set

namespace Schoenflies

private theorem mem_indexed_replacement_iff_single
    {X ι : Type*} {D : Set X} {U N K A : ι → Set X}
    (hNK : ∀ i, N i ⊆ K i) (hKU : ∀ i, K i ⊆ U i)
    (hdisj : Pairwise fun i j => Disjoint (U i) (U j))
    (i : ι) {p : X} (hp : p ∈ U i) :
    p ∈ ((D \ ⋃ j, N j) ∪ ⋃ j, K j ∩ A j) ↔ p ∈ (D \ N i) ∪ (K i ∩ A i) := by
  have houtside (j : ι) (hji : j ≠ i) (hpj : p ∈ U j) : False :=
    Set.disjoint_left.mp (hdisj hji) hpj hp
  constructor
  · rintro (⟨hpD, hpN⟩ | hpK)
    · exact Or.inl ⟨hpD, fun h => hpN (mem_iUnion.mpr ⟨i, h⟩)⟩
    · obtain ⟨j, hpj, hpa⟩ := mem_iUnion.mp hpK
      by_cases hji : j = i
      · exact Or.inr (hji ▸ ⟨hpj, hpa⟩)
      · exact False.elim (houtside j hji (hKU j hpj))
  · rintro (⟨hpD, hpN⟩ | hpK)
    · refine Or.inl ⟨hpD, ?_⟩
      intro hpall
      obtain ⟨j, hpj⟩ := mem_iUnion.mp hpall
      by_cases hji : j = i
      · exact hpN (hji ▸ hpj)
      · exact houtside j hji (hKU j (hNK j hpj))
    · exact Or.inr (mem_iUnion.mpr ⟨i, hpK⟩)

private theorem indexed_replacement_eq_of_single_eq
    {X ι : Type*} {D : Set X} {U : ι → Set X} {N K A : Fin 2 → ι → Set X}
    (hNK : ∀ k i, N k i ⊆ K k i) (hKU : ∀ k i, K k i ⊆ U i)
    (hdisj : Pairwise fun i j => Disjoint (U i) (U j))
    (heq : ∀ i, (D \ N 0 i) ∪ (K 0 i ∩ A 0 i) =
      (D \ N 1 i) ∪ (K 1 i ∩ A 1 i)) :
    (D \ ⋃ i, N 0 i) ∪ ⋃ i, K 0 i ∩ A 0 i =
      (D \ ⋃ i, N 1 i) ∪ ⋃ i, K 1 i ∩ A 1 i := by
  ext p
  by_cases hp : ∃ i, p ∈ U i
  · obtain ⟨i, hpi⟩ := hp
    have h₀ := mem_indexed_replacement_iff_single (D := D) (A := A 0)
      (hNK 0) (hKU 0) hdisj i hpi
    have h₁ := mem_indexed_replacement_iff_single (D := D) (A := A 1)
      (hNK 1) (hKU 1) hdisj i hpi
    rw [heq i] at h₀
    exact h₀.trans h₁.symm
  · have hN (k : Fin 2) : p ∉ ⋃ i, N k i := by
      intro h
      obtain ⟨i, hi⟩ := mem_iUnion.mp h
      exact hp ⟨i, hKU k i (hNK k i hi)⟩
    constructor
    · rintro (⟨hpD, _⟩ | hpA)
      · exact Or.inl ⟨hpD, hN 1⟩
      · obtain ⟨i, hi, _⟩ := mem_iUnion.mp hpA
        exact False.elim (hp ⟨i, hKU 0 i hi⟩)
    · rintro (⟨hpD, _⟩ | hpA)
      · exact Or.inl ⟨hpD, hN 0⟩
      · obtain ⟨i, hi, _⟩ := mem_iUnion.mp hpA
        exact False.elim (hp ⟨i, hKU 1 i hi⟩)

end Schoenflies

end

section

open Set Metric
open scoped ContDiff Manifold

namespace Schoenflies

theorem PrePolygon.exists_isotopy_to_reanchored_replacement
    {m n : ℕ} (P : PrePolygon m) (Q : PrePolygon n)
    {S U : Set Plane} (hU : IsOpen U) (hSU : S ⊆ U)
    (hcar : ∀ x ∈ U, x ∈ P.carrier ↔ x ∈ Q.carrier)
    (D : Set Plane) (e : {j : ZMod (n + 3) // Q.vertex j ∈ S} → Plane ≃ᵃ[ℝ] Plane)
    (V : {j : ZMod (n + 3) // Q.vertex j ∈ S} → Set Plane)
    (r d σ R θ : {j : ZMod (n + 3) // Q.vertex j ∈ S} → ℝ)
    (hnorm : ∀ j, 0 < r j ∧ e j (Q.vertex j) = 0 ∧
      e j (Q.vertex ((j : ZMod (n + 3)) - 1)) = Plane.mk (-1) 0 ∧
      e j (Q.vertex ((j : ZMod (n + 3)) + 1)) = Plane.mk (r j) (d j * r j))
    (hd : ∀ j, d j = 0 ∨ d j = 1)
    (hstraight : ∀ j, d j = 0 ↔
      Plane.det (Q.vertex ((j : ZMod (n + 3)) - 1) - Q.vertex j)
        (Q.vertex ((j : ZMod (n + 3)) + 1) - Q.vertex j) = 0)
    (hσ : ∀ j, σ j = -1 ∨ σ j = 1) (hθ : ∀ j, 0 < θ j ∧ 3 * θ j < R j)
    (hV : ∀ j, IsOpen (V j) ∧ Q.vertex j ∈ V j)
    (hdisj : Pairwise fun i j => Disjoint (V i) (V j))
    (hKV : ∀ j, e j ⁻¹' closedBall (0 : Plane) (R j) ⊆ V j)
    (hside : ∀ j, ∀ p ∈ V j, p ∈ D ↔
      0 ≤ σ j * ((e j p) 1 - d j * max ((e j p) 0) 0)) :
    let I := {i : ZMod (m + 3) // P.vertex i ∈ S ∧
      Plane.det (P.vertex (i - 1) - P.vertex i) (P.vertex (i + 1) - P.vertex i) ≠ 0}
    let J := {j : ZMod (n + 3) // Q.vertex j ∈ S}
    ∃ (j : I → J) (f : I → Plane ≃ᵃ[ℝ] Plane) (ρ ℓ A η : I → ℝ),
      Function.Injective j ∧ (∀ k : J, d k ≠ 0 → ∃ i, j i = k) ∧
      (∀ i, Q.vertex (j i) = P.vertex i ∧ d (j i) = 1 ∧ 0 < ρ i ∧ 0 < ℓ i ∧
        f i (P.vertex i) = 0 ∧ f i (P.vertex ((i : ZMod (m + 3)) - 1)) = Plane.mk (-1) 0 ∧
        f i (P.vertex ((i : ZMod (m + 3)) + 1)) = Plane.mk (ρ i) (ρ i) ∧
        ((∀ p, f i p = ℓ i • e (j i) p) ∨
          (∀ p, f i p = ℓ i • cornerSwap (e (j i) p))) ∧
        (∀ p, (f i p) 1 - max ((f i p) 0) 0 =
          ℓ i * ((e (j i) p) 1 - max ((e (j i) p) 0) 0)) ∧
        (∀ ε : ℝ, ε ≠ 0 → ∀ p,
          (f i p) 1 - Real.smoothMax (ℓ i * ε) ((f i p) 0) 0 =
            ℓ i * ((e (j i) p) 1 - Real.smoothMax ε ((e (j i) p) 0) 0)) ∧
        0 < A i ∧ 0 < η i ∧ η i ≤ θ (j i) ∧
        f i ⁻¹' closedBall (0 : Plane) (A i) ⊆ V (j i) ∧
        ∀ p ∈ V (j i), p ∈ D ↔
          0 ≤ σ (j i) * ((f i p) 1 - max ((f i p) 0) 0)) ∧
      ∀ ε : I → ℝ, (∀ i, 0 < ε i ∧ ε i ≤ η i) →
        let D₀ := (D \ ⋃ k : J, e k ⁻¹' ball (0 : Plane) (R k)) ∪
          ⋃ k : J, (e k ⁻¹' closedBall (0 : Plane) (R k)) ∩
            {p | 0 ≤ σ k * ((e k p) 1 - d k * Real.smoothMax (θ k) ((e k p) 0) 0)}
        let E := (D \ ⋃ i, e (j i) ⁻¹' ball (0 : Plane) (R (j i))) ∪
          ⋃ i, (e (j i) ⁻¹' closedBall (0 : Plane) (R (j i))) ∩
            {p | 0 ≤ σ (j i) * ((e (j i) p) 1 -
              d (j i) * Real.smoothMax (ε i) ((e (j i) p) 0) 0)}
        let D₁ := (D \ ⋃ i, f i ⁻¹' ball (0 : Plane) (A i)) ∪
          ⋃ i, (f i ⁻¹' closedBall (0 : Plane) (A i)) ∩
            {p | 0 ≤ σ (j i) * ((f i p) 1 - Real.smoothMax (ℓ i * ε i) ((f i p) 0) 0)}
        (∀ i, 3 * ε i < R (j i) ∧ 3 * (ℓ i * ε i) < A i) ∧
        E = D₁ ∧ interior E = interior D₁ ∧ frontier E = frontier D₁ ∧
        ∃ (Φ : ℝ → Plane ≃ₘ[ℝ] Plane) (C : Set Plane),
          ContDiff ℝ ∞ (fun z : ℝ × Plane => Φ z.1 z.2) ∧
          ContDiff ℝ ∞ (fun z : ℝ × Plane => (Φ z.1).symm z.2) ∧
          Φ 0 = Diffeomorph.refl 𝓘(ℝ, Plane) Plane ∞ ∧
          IsCompact C ∧ C ⊆ ⋃ i, V (j i) ∧
          (∀ t, EqOn (Φ t) id Cᶜ ∧ EqOn (Φ t).symm id Cᶜ) ∧
          Φ 1 '' D₀ = D₁ ∧ Φ 1 '' interior D₀ = interior D₁ ∧
          Φ 1 '' frontier D₀ = frontier D₁ := by
  classical
  let I := {i : ZMod (m + 3) // P.vertex i ∈ S ∧
    Plane.det (P.vertex (i - 1) - P.vertex i) (P.vertex (i + 1) - P.vertex i) ≠ 0}
  let J := {j : ZMod (n + 3) // Q.vertex j ∈ S}
  have hdisjK : Pairwise fun i j => Disjoint
      (e i ⁻¹' closedBall (0 : Plane) (R i)) (e j ⁻¹' closedBall (0 : Plane) (R j)) :=
    fun i j hij => (hdisj hij).mono (hKV i) (hKV j)
  obtain ⟨j, hji, hj, hcover, hreindex⟩ :=
    P.exists_replacement_reindexing_on_subset Q hU hSU hcar D e R d σ hstraight hdisjK
      (fun i _ p hp => hside i p (hKV i hp))
  have hR (k : J) : 0 < R k :=
    (mul_pos (by norm_num : (0 : ℝ) < 3) (hθ k).1).trans (hθ k).2
  have hlocal (i : I) := P.exists_equal_reanchored_corner_replacement Q i (j i) (hj i).1
    (e (j i)) (hnorm (j i)) (hd (j i)) (hstraight (j i)) (hR (j i))
    (hθ (j i)).1 (hV (j i)).1 (hV (j i)).2 (hKV (j i)) (hside (j i))
    hU (hSU i.property.1) hcar i.property.2
  choose f ρ ℓ A η hdj hρ hℓ hfc hfa hfb hform hraw hsmooth
    hA hη hηθ hAV hsidef hcompare using hlocal
  have hdisj' : Pairwise fun i k : I => Disjoint (V (j i)) (V (j k)) :=
    fun i k hik => hdisj (fun h => hik (hji h))
  refine ⟨j, f, ρ, ℓ, A, η, hji, hcover, ?_, ?_⟩
  · intro i
    exact ⟨(hj i).1, hdj i, hρ i, hℓ i, hfc i, hfa i, hfb i, hform i,
      hraw i, hsmooth i, hA i, hη i, hηθ i, hAV i, hsidef i⟩
  · intro ε hε
    let B := fun w : I → ℝ => (D \ ⋃ i, e (j i) ⁻¹' ball (0 : Plane) (R (j i))) ∪
      ⋃ i, (e (j i) ⁻¹' closedBall (0 : Plane) (R (j i))) ∩
        {p | 0 ≤ σ (j i) * ((e (j i) p) 1 -
          d (j i) * Real.smoothMax (w i) ((e (j i) p) 0) 0)}
    let F := (D \ ⋃ i, f i ⁻¹' ball (0 : Plane) (A i)) ∪
      ⋃ i, (f i ⁻¹' closedBall (0 : Plane) (A i)) ∩
        {p | 0 ≤ σ (j i) * ((f i p) 1 - Real.smoothMax (ℓ i * ε i) ((f i p) 0) 0)}
    have hεR (i : I) := (hcompare i (ε i) (hε i).1 (hε i).2).1
    have hεA (i : I) := (hcompare i (ε i) (hε i).1 (hε i).2).2.1
    let N : Fin 2 → I → Set Plane := ![fun i => e (j i) ⁻¹' ball (0 : Plane) (R (j i)),
      fun i => f i ⁻¹' ball (0 : Plane) (A i)]
    let K : Fin 2 → I → Set Plane :=
      ![fun i => e (j i) ⁻¹' closedBall (0 : Plane) (R (j i)),
        fun i => f i ⁻¹' closedBall (0 : Plane) (A i)]
    let G : Fin 2 → I → Set Plane :=
      ![fun i => {p | 0 ≤ σ (j i) * ((e (j i) p) 1 -
          d (j i) * Real.smoothMax (ε i) ((e (j i) p) 0) 0)},
        fun i => {p | 0 ≤ σ (j i) * ((f i p) 1 -
          Real.smoothMax (ℓ i * ε i) ((f i p) 0) 0)}]
    have hNK (k : Fin 2) (i : I) : N k i ⊆ K k i := by
      fin_cases k <;> exact preimage_mono ball_subset_closedBall
    have hKU (k : Fin 2) (i : I) : K k i ⊆ V (j i) := by
      fin_cases k
      · exact hKV (j i)
      · exact hAV i
    have hBF : B ε = F := indexed_replacement_eq_of_single_eq
      (A := G) hNK hKU hdisj'
      (fun i => (hcompare i (ε i) (hε i).1 (hε i).2).2.2.1)
    refine ⟨fun i => ⟨hεR i, hεA i⟩, hBF, congrArg interior hBF, congrArg frontier hBF, ?_⟩
    let w : Fin 2 → I → ℝ := ![fun i => θ (j i), ε]
    have hw (k : Fin 2) (i : I) : 0 < w k i := by
      fin_cases k
      · exact (hθ (j i)).1
      · exact (hε i).1
    have hwR (k : Fin 2) (i : I) : 3 * w k i < R (j i) := by
      fin_cases k
      · exact (hθ (j i)).2
      · exact hεR i
    obtain ⟨Φ, C, hΦ, hiΦ, hzero, hC, hCV, hfix, hB, hI, hF⟩ :=
      exists_isotopy_between_normalized_corner_replacements (fun _ i => e (j i))
        (fun i => Q.vertex ((j i : ZMod (n + 3)) - 1))
        (fun i => Q.vertex ((j i : ZMod (n + 3)) + 1)) (fun i => Q.vertex (j i))
        (fun _ i => V (j i)) (fun _ i => r (j i)) (fun _ i => d (j i))
        (fun _ i => σ (j i)) w (fun _ i => R (j i)) (D := D)
        (fun _ i => ⟨(hnorm (j i)).1, (hnorm (j i)).2.2.1,
          (hnorm (j i)).2.2.2, (hnorm (j i)).2.1⟩)
        (fun _ i => (hV (j i)).1) (fun _ i => hd (j i)) (fun _ i => hσ (j i))
        hw hwR (fun _ i => hKV (j i)) (fun _ => hdisj') (fun _ i => hside (j i))
    change Φ 1 '' B (fun i => θ (j i)) = B ε at hB
    change Φ 1 '' interior (B (fun i => θ (j i))) = interior (B ε) at hI
    change Φ 1 '' frontier (B (fun i => θ (j i))) = frontier (B ε) at hF
    refine ⟨Φ, C, hΦ, hiΦ, hzero, hC, by simpa only [union_self] using hCV, hfix, ?_⟩
    have heq := (hreindex θ).1
    rw [heq]
    exact ⟨hB.trans hBF, hI.trans (congrArg interior hBF), hF.trans (congrArg frontier hBF)⟩

end Schoenflies

end

section

open Set Metric
open scoped ContDiff Manifold

namespace Schoenflies

private theorem PrePolygon.exists_relative_rounding_isotopy_with_reanchored_corners
    {m n : ℕ} (P : PrePolygon m) (Q : PrePolygon n) {D L W O : Set Plane}
    (hcar : ∀ x ∉ L, x ∈ P.carrier ↔ x ∈ Q.carrier)
    (hD : IsCompact D) (hL : IsClosed L) (hW : IsOpen W) (hLW : L ⊆ W)
    (hO : IsOpen O) (hvO : ∀ i, Q.vertex i ∉ W → Q.vertex i ∈ O)
    (hold : ∀ p ∉ L, p ∈ D ↔ p ∈ closure (inside Q.carrier))
    (hgood : ∀ p ∈ frontier D, p ∈ W →
      ∃ (N : Set Plane) (G : Plane → ℝ), IsOpen N ∧ p ∈ N ∧
        ContDiff ℝ ∞ G ∧ fderiv ℝ G p ≠ 0 ∧
        ∀ q ∈ N, (q ∈ D ↔ 0 ≤ G q) ∧
          (q ∈ interior D ↔ 0 < G q) ∧ (q ∈ frontier D ↔ G q = 0)) :
    let I := {i : ZMod (m + 3) // P.vertex i ∉ W ∧
      Plane.det (P.vertex (i - 1) - P.vertex i) (P.vertex (i + 1) - P.vertex i) ≠ 0}
    let J := {j : ZMod (n + 3) // Q.vertex j ∉ W}
    ∃ (e : J → Plane ≃ᵃ[ℝ] Plane) (V : J → Set Plane) (r d σ R θ : J → ℝ)
      (j : I → J) (f : I → Plane ≃ᵃ[ℝ] Plane) (ρ ℓ A ε : I → ℝ)
      (Φ : ℝ → Plane ≃ₘ[ℝ] Plane) (C : Set Plane),
      (∀ k, 0 < r k ∧ e k (Q.vertex k) = 0 ∧
        e k (Q.vertex ((k : ZMod (n + 3)) - 1)) = Plane.mk (-1) 0 ∧
        e k (Q.vertex ((k : ZMod (n + 3)) + 1)) = Plane.mk (r k) (d k * r k)) ∧
      (∀ k, IsOpen (V k) ∧ Q.vertex k ∈ V k ∧ V k ⊆ Lᶜ ∩ O ∧
        (d k = 0 ∨ d k = 1) ∧ (σ k = -1 ∨ σ k = 1) ∧
        0 < θ k ∧ 3 * θ k < R k ∧ e k ⁻¹' closedBall (0 : Plane) (R k) ⊆ V k ∧
        ∀ p ∈ V k, p ∈ D ↔ 0 ≤ σ k * ((e k p) 1 - d k * max ((e k p) 0) 0)) ∧
      (Pairwise fun i j => Disjoint (V i) (V j)) ∧
      (∀ k, d k = 0 ↔ Plane.det
        (Q.vertex ((k : ZMod (n + 3)) - 1) - Q.vertex k)
        (Q.vertex ((k : ZMod (n + 3)) + 1) - Q.vertex k) = 0) ∧
      Function.Injective j ∧ (∀ k : J, d k ≠ 0 → ∃ i, j i = k) ∧
      (∀ i, Q.vertex (j i) = P.vertex i ∧ d (j i) = 1 ∧
        0 < ρ i ∧ 0 < ℓ i ∧ 0 < ε i ∧ ε i ≤ θ (j i) ∧
        3 * ε i < R (j i) ∧ 3 * (ℓ i * ε i) < A i ∧
        f i (P.vertex i) = 0 ∧ f i (P.vertex ((i : ZMod (m + 3)) - 1)) = Plane.mk (-1) 0 ∧
        f i (P.vertex ((i : ZMod (m + 3)) + 1)) = Plane.mk (ρ i) (ρ i) ∧
        f i ⁻¹' closedBall (0 : Plane) (A i) ⊆ V (j i) ∧
        (∀ p ∈ V (j i), p ∈ D ↔
          0 ≤ σ (j i) * ((f i p) 1 - max ((f i p) 0) 0)) ∧
        ∀ p, (f i p) 1 - Real.smoothMax (ℓ i * ε i) ((f i p) 0) 0 =
          ℓ i * ((e (j i) p) 1 - Real.smoothMax (ε i) ((e (j i) p) 0) 0)) ∧
      let D₀ := (D \ ⋃ k, e k ⁻¹' ball (0 : Plane) (R k)) ∪
        ⋃ k, (e k ⁻¹' closedBall (0 : Plane) (R k)) ∩
          {p | 0 ≤ σ k * ((e k p) 1 - d k * Real.smoothMax (θ k) ((e k p) 0) 0)}
      let D₁ := (D \ ⋃ i, f i ⁻¹' ball (0 : Plane) (A i)) ∪
        ⋃ i, (f i ⁻¹' closedBall (0 : Plane) (A i)) ∩
          {p | 0 ≤ σ (j i) * ((f i p) 1 - Real.smoothMax (ℓ i * ε i) ((f i p) 0) 0)}
      IsCompact D₀ ∧
      (∀ p ∈ frontier D₀, ∃ (N : Set Plane) (G : Plane → ℝ),
        IsOpen N ∧ p ∈ N ∧ ContDiff ℝ ∞ G ∧ fderiv ℝ G p ≠ 0 ∧
        ∀ q ∈ N, (q ∈ D₀ ↔ 0 ≤ G q) ∧
          (q ∈ interior D₀ ↔ 0 < G q) ∧ (q ∈ frontier D₀ ↔ G q = 0)) ∧
      ContDiff ℝ ∞ (fun z : ℝ × Plane => Φ z.1 z.2) ∧
      ContDiff ℝ ∞ (fun z : ℝ × Plane => (Φ z.1).symm z.2) ∧
      Φ 0 = Diffeomorph.refl 𝓘(ℝ, Plane) Plane ∞ ∧ IsCompact C ∧ C ⊆ Lᶜ ∩ O ∧
      (∀ t, EqOn (Φ t) id Cᶜ ∧ EqOn (Φ t).symm id Cᶜ) ∧
      Φ 1 '' D₀ = D₁ ∧ Φ 1 '' interior D₀ = interior D₁ ∧
      Φ 1 '' frontier D₀ = frontier D₁ := by
  obtain ⟨e, V, d, σ, θ, R, r, hnorm, hc, hdisj, hn, _, _,
    hcompact, _, _, _, _, _, hregular⟩ :=
    Q.exists_normalized_relative_compact_rounding hD hL hW hLW hO hvO hold hgood
  have hnorm' k : 0 < r k ∧ e k (Q.vertex k) = 0 ∧
      e k (Q.vertex (k.val - 1)) = Plane.mk (-1) 0 ∧
      e k (Q.vertex (k.val + 1)) = Plane.mk (r k) (d k * r k) :=
    ⟨(hnorm k).1, (hc k).2.2.2.1, (hnorm k).2⟩
  obtain ⟨j, f, ρ, ℓ, A, η, hji, hcover, hf, hcompare⟩ :=
    P.exists_isotopy_to_reanchored_replacement Q hL.isOpen_compl
      (show Wᶜ ⊆ Lᶜ from fun _ hp h => hp (hLW h)) hcar D e V r d σ R θ
      hnorm' (fun k => (hc k).2.2.2.2.1) (fun k => (hc k).2.2.2.2.2.2.1)
      (fun k => (hc k).2.2.2.2.2.1)
      (fun k => ⟨(hc k).2.2.2.2.2.2.2.1, (hc k).2.2.2.2.2.2.2.2.1⟩)
      (fun k => ⟨(hc k).1, (hc k).2.1⟩) hdisj (fun k => (hn k).2.2.2)
      (fun k => (hc k).2.2.2.2.2.2.2.2.2)
  let ε := fun i => η i / 2
  have hε i : 0 < ε i ∧ ε i ≤ η i := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hη, _⟩ := hf i
    exact ⟨half_pos hη, half_le_self hη.le⟩
  obtain ⟨hbound, _, _, _, Φ, C, hΦ, hiΦ, hzero, hC, hCV, hfix, himage, hinter, hfront⟩ :=
    hcompare ε hε
  refine ⟨e, V, r, d, σ, R, θ, j, f, ρ, ℓ, A, ε, Φ, C, hnorm', ?_,
    hdisj, (fun k => (hc k).2.2.2.2.2.2.1), hji, hcover, ?_, hcompact, hregular, hΦ, hiΦ, hzero,
    hC, ?_, hfix,
    himage, hinter, hfront⟩
  · intro k
    obtain ⟨hV, hk, hVO, _, hd, hσ, _, hθ, hR, hside⟩ := hc k
    exact ⟨hV, hk, hVO, hd, hσ, hθ, hR, (hn k).2.2.2, hside⟩
  · intro i
    obtain ⟨hj, hd, hρ, hℓ, hfc, hfa, hfb, _, _, hsmooth, _, _, hηθ, hAV, hside⟩ := hf i
    exact ⟨hj, hd, hρ, hℓ, (hε i).1, (hε i).2.trans hηθ,
      (hbound i).1, (hbound i).2, hfc, hfa, hfb, hAV, hside,
      hsmooth (ε i) (hε i).1.ne'⟩
  · intro p hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hCV hp)
    exact (hc (j i)).2.2.1 hi

end Schoenflies

end

section

open Set Metric
open scoped ContDiff Manifold Topology

namespace Function.Injective

private theorem image_indexed_replacement_of_eqOn
    {X ι : Type*} {f : X → X} (hf : Injective f) (D : Set X) (N K A : ι → Set X)
    (hNK : ∀ i, N i ⊆ K i) (hfix : ∀ i, EqOn f id (K i)) :
    f '' ((D \ ⋃ i, N i) ∪ ⋃ i, K i ∩ A i) =
      (f '' D \ ⋃ i, N i) ∪ ⋃ i, K i ∩ A i := by
  have hN : f '' (⋃ i, N i) = ⋃ i, N i := by
    apply EqOn.image_eq_self
    intro p hp
    obtain ⟨i, hpi⟩ := mem_iUnion.mp hp
    exact hfix i (hNK i hpi)
  have hA : f '' (⋃ i, K i ∩ A i) = ⋃ i, K i ∩ A i := by
    apply EqOn.image_eq_self
    intro p hp
    obtain ⟨i, hpi, _⟩ := mem_iUnion.mp hp
    exact hfix i hpi
  rw [image_union, image_sdiff hf, hN, hA]

end Function.Injective

namespace Schoenflies

private theorem affine_corner_replacement_image_of_fixed_charts
    {ι : Type*} (e : ι → Plane ≃ᵃ[ℝ] Plane) (ε R d σ : ι → ℝ)
    (φ : Plane ≃ₜ Plane) {D L : Set Plane}
    (hKL : ∀ i, e i ⁻¹' closedBall (0 : Plane) (R i) ⊆ Lᶜ)
    (hfix : EqOn φ id Lᶜ) :
    let N := fun i => e i ⁻¹' ball (0 : Plane) (R i)
    let K := fun i => e i ⁻¹' closedBall (0 : Plane) (R i)
    let H := fun i p => σ i * ((e i p) 1 - d i * Real.smoothMax (ε i) ((e i p) 0) 0)
    let D₀ := (D \ ⋃ i, N i) ∪ ⋃ i, K i ∩ {p | 0 ≤ H i p}
    let D₁ := (φ '' D \ ⋃ i, N i) ∪ ⋃ i, K i ∩ {p | 0 ≤ H i p}
    φ '' D₀ = D₁ ∧ φ '' interior D₀ = interior D₁ ∧ φ '' frontier D₀ = frontier D₁ := by
  dsimp only
  have himage := φ.injective.image_indexed_replacement_of_eqOn D
    (fun i => e i ⁻¹' ball (0 : Plane) (R i))
    (fun i => e i ⁻¹' closedBall (0 : Plane) (R i))
    (fun i => {p | 0 ≤ σ i * ((e i p) 1 - d i * Real.smoothMax (ε i) ((e i p) 0) 0)})
    (fun _ => preimage_mono ball_subset_closedBall) (fun i => hfix.mono (hKL i))
  exact ⟨himage, (φ.image_interior _).trans (congrArg interior himage),
    (φ.image_frontier _).trans (congrArg frontier himage)⟩

end Schoenflies

end

section

open Set Metric
open scoped ContDiff Manifold Topology

namespace Schoenflies

theorem PrePolygon.exists_two_edge_free_relative_rounding_splice
    {m : ℕ} (P : PrePolygon m)
    (M : LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh)
    (hfrontier : frontier M.toPlaneComplex.support = P.carrier)
    (T : M.Triangle) (k : Fin 3) (hfree : M.IsTwoEdgeFreeTriangle T k)
    {σ : ℝ} (hσ : 0 < σ) (hσsmall : σ ≤ 1 / 4) :
    let b := LeanEval.Topology.ClassificationOfSurfaces.Moise.affineBasisOfTriangle
      (M.freeTriangleOrder T k) (M.freeTriangleOrder_affineIndependent T k)
    let R := closure (P.carrier \ (segment ℝ (b 0) (b 2) ∪ segment ℝ (b 1) (b 2)))
    let N := (interior M.toPlaneComplex.support ∩
      {p | 0 < b.coord 0 p ∧ 0 < b.coord 1 p}) ∪
        ((M.eraseTriangle T.1).toPlaneComplex.supportᶜ ∩ {p | 0 < b.coord 2 p})
    ∃ (v₀ v₁ : Plane) (r₀ r₁ : ℝ) (f₀ f₁ : Plane →ᵃ[ℝ] ℝ)
      (e₀ e₁ : Plane ≃ᵃ[ℝ] Plane) (ε₀ ε : ℝ) (J W K : Set Plane)
      (F : Plane → ℝ × ℝ) (H : ℝ → Plane ≃ₘ[ℝ] Plane),
      let s₀ := b.coord 2 v₀ / f₀ v₀
      let s₁ := b.coord 2 v₁ / f₁ v₁
      let U₀ := ball (b 0) r₀ ∩ {p | (1 : ℝ) / 4 < b.coord 0 p - b.coord 1 p}
      let U₁ := ball (b 1) r₁ ∩ {p | (1 : ℝ) / 4 < b.coord 1 p - b.coord 0 p}
      let V := {p | ε₀ < f₀ p ∧ ε₀ < f₁ p} ∩ N
      let D := (M.toPlaneComplex.support \ interior K) ∪ (K ∩ {p | (F p).1 ≤ 0})
      let E := ((M.eraseTriangle T.1).toPlaneComplex.support \ interior K) ∪
        (K ∩ {p | (F p).2 ≤ 0})
      (0 < r₀ ∧ 0 < r₁ ∧ Disjoint (ball (b 0) r₀) (ball (b 1) r₁) ∧
      segment ℝ (b 0) v₀ ⊆ R ∧ segment ℝ (b 1) v₁ ⊆ R ∧
      f₀ (b 0) = 0 ∧ 0 < f₀ (b 1) ∧ 0 < f₀ (b 2) ∧ f₀ v₀ < 0 ∧
      f₁ (b 1) = 0 ∧ 0 < f₁ (b 0) ∧ 0 < f₁ (b 2) ∧ f₁ v₁ < 0 ∧
      (∀ p, (e₀ p) 0 = f₀ p ∧ (e₀ p) 1 = b.coord 2 p) ∧
      (∀ p, (e₁ p) 0 = f₁ p ∧ (e₁ p) 1 = b.coord 2 p) ∧
      0 < ε₀ ∧ 0 < ε ∧ ε ≤ ε₀ ∧ IsCompact J ∧
      M.triangleCarrier T.1 ⊆ interior J ∧ IsOpen W ∧ J ⊆ W ∧
      W ⊆ U₀ ∪ U₁ ∪ V ∧ ContDiff ℝ ∞ F ∧
      EqOn F (fun p =>
        (-(f₀ (b 2) / f₀ (b 1) * (s₀ * (f₀ p - Real.smoothMax ε (f₀ p) 0) +
          Real.smoothMax ε (f₀ p) 0 / f₀ (b 2) - b.coord 2 p)),
          -(s₀ * (f₀ p - Real.smoothMax ε (f₀ p) 0) - b.coord 2 p))) (W ∩ U₀) ∧
      EqOn F (fun p =>
        (-(f₁ (b 2) / f₁ (b 0) * (s₁ * (f₁ p - Real.smoothMax ε (f₁ p) 0) +
          Real.smoothMax ε (f₁ p) 0 / f₁ (b 2) - b.coord 2 p)),
          -(s₁ * (f₁ p - Real.smoothMax ε (f₁ p) 0) - b.coord 2 p))) (W ∩ U₁) ∧
      EqOn F (fun p => (Real.smoothMax σ (-b.coord 0 p) (-b.coord 1 p),
        b.coord 2 p)) (W ∩ V) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ W ∩ V,
        (1 - t) * (F p).1 + t * (F p).2 = 0 → p ∈ M.triangleCarrier T.1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ W,
        fderiv ℝ (fun q => (1 - t) * (F q).1 + t * (F q).2) p ≠ 0) ∧
      (∀ p ∈ W, p ∉ interior J →
        (p ∈ M.toPlaneComplex.support ↔ (F p).1 ≤ 0) ∧
        (p ∈ interior M.toPlaneComplex.support ↔ (F p).1 < 0) ∧
        (p ∈ frontier M.toPlaneComplex.support ↔ (F p).1 = 0)) ∧
      (∀ p ∈ W, p ∉ interior J →
        (p ∈ (M.eraseTriangle T.1).toPlaneComplex.support ↔ (F p).2 ≤ 0) ∧
        (p ∈ interior (M.eraseTriangle T.1).toPlaneComplex.support ↔ (F p).2 < 0) ∧
        (p ∈ frontier (M.eraseTriangle T.1).toPlaneComplex.support ↔ (F p).2 = 0)) ∧
      IsCompact K ∧ J ⊆ interior K ∧ K ⊆ W ∧
      ContDiff ℝ ∞ (fun z : ℝ × Plane => H z.1 z.2) ∧
      ContDiff ℝ ∞ (fun z : ℝ × Plane => (H z.1).symm z.2) ∧
      H 0 = Diffeomorph.refl 𝓘(ℝ, Plane) Plane ∞ ∧
      (∀ t, EqOn (H t) id Kᶜ ∧ EqOn (H t).symm id Kᶜ ∧
        (∀ p, H t p ∈ W ↔ p ∈ W) ∧ (∀ p, (H t).symm p ∈ W ↔ p ∈ W)) ∧
      (∀ p ∈ W, ((F p).1 = 0 ↔ (F (H 1 p)).2 = 0) ∧
        ((F p).1 < 0 ↔ (F (H 1 p)).2 < 0) ∧ ((F p).1 ≤ 0 ↔ (F (H 1 p)).2 ≤ 0)) ∧
      (∀ p ∈ W, ((F p).2 = 0 ↔ (F ((H 1).symm p)).1 = 0) ∧
        ((F p).2 < 0 ↔ (F ((H 1).symm p)).1 < 0) ∧
        ((F p).2 ≤ 0 ↔ (F ((H 1).symm p)).1 ≤ 0)) ∧
      IsCompact D ∧ IsCompact E ∧
      (∀ p ∈ W, (p ∈ D ↔ (F p).1 ≤ 0) ∧
        (p ∈ interior D ↔ (F p).1 < 0) ∧ (p ∈ frontier D ↔ (F p).1 = 0)) ∧
      (∀ p ∈ W, (p ∈ E ↔ (F p).2 ≤ 0) ∧
        (p ∈ interior E ↔ (F p).2 < 0) ∧ (p ∈ frontier E ↔ (F p).2 = 0)) ∧
      (∀ p ∉ K, (p ∈ D ↔ p ∈ M.toPlaneComplex.support) ∧
        (p ∈ interior D ↔ p ∈ interior M.toPlaneComplex.support) ∧
        (p ∈ frontier D ↔ p ∈ frontier M.toPlaneComplex.support)) ∧
      (∀ p ∉ K, (p ∈ E ↔ p ∈ (M.eraseTriangle T.1).toPlaneComplex.support) ∧
        (p ∈ interior E ↔ p ∈ interior (M.eraseTriangle T.1).toPlaneComplex.support) ∧
        (p ∈ frontier E ↔ p ∈ frontier (M.eraseTriangle T.1).toPlaneComplex.support)) ∧
      (H 1) '' D = E ∧ (H 1) '' interior D = interior E ∧
      (H 1) '' frontier D = frontier E ∧
      (H 1).symm '' E = D ∧ (H 1).symm '' interior E = interior D ∧
      (H 1).symm '' frontier E = frontier D) ∧
      ∃ (n : ℕ) (Q : PrePolygon n),
        Q.carrier = frontier (M.eraseTriangle T.1).toPlaneComplex.support ∧
        (M.eraseTriangle T.1).toPlaneComplex.support = closure (inside Q.carrier) ∧
      let I := {i : ZMod (m + 3) // P.vertex i ∉ W ∧
        Plane.det (P.vertex (i - 1) - P.vertex i) (P.vertex (i + 1) - P.vertex i) ≠ 0}
      let J := {j : ZMod (n + 3) // Q.vertex j ∉ W}
      ∃ (e : J → Plane ≃ᵃ[ℝ] Plane) (V : J → Set Plane) (r d σ R θ : J → ℝ)
        (j : I → J) (f : I → Plane ≃ᵃ[ℝ] Plane) (ρ ℓ A η : I → ℝ)
        (Ψ : ℝ → Plane ≃ₘ[ℝ] Plane) (C : Set Plane),
        (∀ k, 0 < r k ∧ e k (Q.vertex k) = 0 ∧
          e k (Q.vertex ((k : ZMod (n + 3)) - 1)) = Plane.mk (-1) 0 ∧
          e k (Q.vertex ((k : ZMod (n + 3)) + 1)) = Plane.mk (r k) (d k * r k)) ∧
        (∀ k, IsOpen (V k) ∧ Q.vertex k ∈ V k ∧ V k ⊆ Kᶜ ∧
          (d k = 0 ∨ d k = 1) ∧ (σ k = -1 ∨ σ k = 1) ∧
          0 < θ k ∧ 3 * θ k < R k ∧ e k ⁻¹' closedBall (0 : Plane) (R k) ⊆ V k ∧
          ∀ p ∈ V k, p ∈ E ↔ 0 ≤ σ k * ((e k p) 1 - d k * max ((e k p) 0) 0)) ∧
        Function.Injective j ∧ (∀ k : J, d k ≠ 0 → ∃ i, j i = k) ∧
        (∀ i, Q.vertex (j i) = P.vertex i ∧ d (j i) = 1 ∧
          0 < ρ i ∧ 0 < ℓ i ∧ 0 < η i ∧ η i ≤ θ (j i) ∧
          3 * η i < R (j i) ∧ 3 * (ℓ i * η i) < A i ∧
          f i (P.vertex i) = 0 ∧ f i (P.vertex ((i : ZMod (m + 3)) - 1)) = Plane.mk (-1) 0 ∧
          f i (P.vertex ((i : ZMod (m + 3)) + 1)) = Plane.mk (ρ i) (ρ i) ∧
          f i ⁻¹' closedBall (0 : Plane) (A i) ⊆ V (j i) ∧
          (∀ p ∈ V (j i), p ∈ E ↔
            0 ≤ σ (j i) * ((f i p) 1 - max ((f i p) 0) 0)) ∧
          ∀ p, (f i p) 1 - Real.smoothMax (ℓ i * η i) ((f i p) 0) 0 =
            ℓ i * ((e (j i) p) 1 - Real.smoothMax (η i) ((e (j i) p) 0) 0)) ∧
        let D₀ := (E \ ⋃ k, e k ⁻¹' ball (0 : Plane) (R k)) ∪
          ⋃ k, (e k ⁻¹' closedBall (0 : Plane) (R k)) ∩
            {p | 0 ≤ σ k * ((e k p) 1 - d k * Real.smoothMax (θ k) ((e k p) 0) 0)}
        let D₁ := (E \ ⋃ i, f i ⁻¹' ball (0 : Plane) (A i)) ∪
          ⋃ i, (f i ⁻¹' closedBall (0 : Plane) (A i)) ∩
            {p | 0 ≤ σ (j i) * ((f i p) 1 - Real.smoothMax (ℓ i * η i) ((f i p) 0) 0)}
        IsCompact D₀ ∧
        (∀ p ∈ frontier D₀, ∃ (N : Set Plane) (G : Plane → ℝ),
          IsOpen N ∧ p ∈ N ∧ ContDiff ℝ ∞ G ∧ fderiv ℝ G p ≠ 0 ∧
          ∀ q ∈ N, (q ∈ D₀ ↔ 0 ≤ G q) ∧
            (q ∈ interior D₀ ↔ 0 < G q) ∧ (q ∈ frontier D₀ ↔ G q = 0)) ∧
        ContDiff ℝ ∞ (fun z : ℝ × Plane => Ψ z.1 z.2) ∧
        ContDiff ℝ ∞ (fun z : ℝ × Plane => (Ψ z.1).symm z.2) ∧
        Ψ 0 = Diffeomorph.refl 𝓘(ℝ, Plane) Plane ∞ ∧ IsCompact C ∧ C ⊆ Kᶜ ∧
        (∀ t, EqOn (Ψ t) id Cᶜ ∧ EqOn (Ψ t).symm id Cᶜ) ∧
        Ψ 1 '' D₀ = D₁ ∧ Ψ 1 '' interior D₀ = interior D₁ ∧
        Ψ 1 '' frontier D₀ = frontier D₁ ∧
        let D₂ := (D \ ⋃ i, f i ⁻¹' ball (0 : Plane) (A i)) ∪
          ⋃ i, (f i ⁻¹' closedBall (0 : Plane) (A i)) ∩
            {p | 0 ≤ σ (j i) * ((f i p) 1 - Real.smoothMax (ℓ i * η i) ((f i p) 0) 0)}
        ∃ Γ : ℝ → Plane ≃ₘ[ℝ] Plane,
          (∀ t, Γ t = (H t).trans (Ψ t).symm) ∧
          ContDiff ℝ ∞ (fun z : ℝ × Plane => Γ z.1 z.2) ∧
          ContDiff ℝ ∞ (fun z : ℝ × Plane => (Γ z.1).symm z.2) ∧
          Γ 0 = Diffeomorph.refl 𝓘(ℝ, Plane) Plane ∞ ∧ IsCompact (K ∪ C) ∧
          (∀ t, EqOn (Γ t) id (K ∪ C)ᶜ ∧ EqOn (Γ t).symm id (K ∪ C)ᶜ) ∧
          Γ 1 '' D₂ = D₀ ∧ Γ 1 '' interior D₂ = interior D₀ ∧
          Γ 1 '' frontier D₂ = frontier D₀ := by
  dsimp only
  obtain ⟨v₀, v₁, r₀, r₁, f₀, f₁, e₀, e₁, ε₀, ε, J, W, K, F, H, hdata⟩ :=
    P.exists_local_rounding_isotopy_of_two_edge_free_triangle M hfrontier T k hfree hσ hσsmall
  have hs := hdata
  rcases hs with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTJ,
    hW, _, _, hF, _, _, _, _, hreg, _, _, hK, hJK, hKW, hH, hHi, hH0, hfix,
    _, _, _, hE, _, hEsides, _, hEraw, hDE, _, _, _, _, _⟩
  let D := (M.toPlaneComplex.support \ interior K) ∪ (K ∩ {p | (F p).1 ≤ 0})
  let E := ((M.eraseTriangle T.1).toPlaneComplex.support \ interior K) ∪
    (K ∩ {p | (F p).2 ≤ 0})
  obtain ⟨n, Q, _, _, hQ, hregion, _⟩ :=
    P.exists_prePolygon_closed_region_erase_triangle_of_two_edge_free M hfrontier T k hfree
  have hTK : M.triangleCarrier T.1 ⊆ K :=
    fun _ hp => interior_subset (hJK (interior_subset (hTJ hp)))
  have hcar : ∀ p ∉ K, p ∈ P.carrier ↔ p ∈ Q.carrier := by
    intro p hp
    have hpT : p ∉ M.triangleCarrier T.1 := fun h => hp (hTK h)
    rw [hQ, M.frontier_eraseTriangle_support T, hfrontier]
    simp only [mem_union, mem_sdiff, mem_inter_iff, hpT, not_false_eq_true, and_true,
      and_false, or_false]
  have hold : ∀ p ∉ K, p ∈ E ↔ p ∈ closure (inside Q.carrier) := by
    intro p hp
    rw [← hregion]
    exact (hEraw p hp).1
  have hgood : ∀ p ∈ frontier E, p ∈ W →
      ∃ (N : Set Plane) (G : Plane → ℝ), IsOpen N ∧ p ∈ N ∧
        ContDiff ℝ ∞ G ∧ fderiv ℝ G p ≠ 0 ∧
        ∀ q ∈ N, (q ∈ E ↔ 0 ≤ G q) ∧
          (q ∈ interior E ↔ 0 < G q) ∧ (q ∈ frontier E ↔ G q = 0) := by
    intro p _ hp
    have hreg₁ : fderiv ℝ (fun q => (F q).2) p ≠ 0 := by
      simpa only [sub_self, zero_mul, one_mul, zero_add] using
        hreg 1 ⟨zero_le_one, le_rfl⟩ p hp
    refine ⟨W, fun q => -(F q).2, hW, hp, hF.snd.neg, ?_, ?_⟩
    · rw [fderiv_fun_neg]
      exact neg_ne_zero.mpr hreg₁
    · intro q hq
      simpa only [neg_nonneg, neg_pos, neg_eq_zero] using hEsides q hq
  obtain ⟨e, V, r, d, σ, R, θ, j, f, ρ, ℓ, A, η, Ψ, C, hnorm, hc, _, _, hji, hcover,
    hf, hcompact, hregular, hΨ, hΨi, hΨ0, hC, hCK, hfixΨ, hΨimage, hΨinter, hΨfront⟩ :=
    P.exists_relative_rounding_isotopy_with_reanchored_corners Q hcar hE hK.isClosed hW hKW
      hK.isClosed.isOpen_compl (fun i hi h => hi (hKW h)) hold hgood
  have hcut i : f i ⁻¹' closedBall (0 : Plane) (A i) ⊆ Kᶜ := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hAV, _⟩ := hf i
    exact fun _ hp => ((hc (j i)).2.2.1 (hAV hp)).1
  let D₀ := (E \ ⋃ i, e i ⁻¹' ball (0 : Plane) (R i)) ∪
    ⋃ i, (e i ⁻¹' closedBall (0 : Plane) (R i)) ∩
      {p | 0 ≤ σ i * ((e i p) 1 - d i * Real.smoothMax (θ i) ((e i p) 0) 0)}
  let D₁ := (E \ ⋃ i, f i ⁻¹' ball (0 : Plane) (A i)) ∪
    ⋃ i, (f i ⁻¹' closedBall (0 : Plane) (A i)) ∩
      {p | 0 ≤ σ (j i) * ((f i p) 1 - Real.smoothMax (ℓ i * η i) ((f i p) 0) 0)}
  let D₂ := (D \ ⋃ i, f i ⁻¹' ball (0 : Plane) (A i)) ∪
    ⋃ i, (f i ⁻¹' closedBall (0 : Plane) (A i)) ∩
      {p | 0 ≤ σ (j i) * ((f i p) 1 - Real.smoothMax (ℓ i * η i) ((f i p) 0) 0)}
  have hDE' : (H 1).toHomeomorph '' D = E := hDE
  have hΨimage' : Ψ 1 '' D₀ = D₁ := hΨimage
  have hHD : H 1 '' D₂ = D₁ := by
    have hh := (affine_corner_replacement_image_of_fixed_charts f
      (fun i => ℓ i * η i) A (fun _ => 1) (fun i => σ (j i)) (H 1).toHomeomorph
      (D := D) hcut (hfix 1).1).1
    rw [hDE'] at hh
    simpa only [D₂, D₁, Diffeomorph.coe_toHomeomorph, one_mul] using hh
  have hΨinverse : (Ψ 1).symm '' D₁ = D₀ := by
    rw [← hΨimage']
    exact (Ψ 1).symm_image_image D₀
  have hΨi0 : (Ψ 0).symm = Diffeomorph.refl 𝓘(ℝ, Plane) Plane ∞ := by
    rw [hΨ0]
    rfl
  obtain ⟨Γ, hΓeq, hΓ, hΓi, hΓ0, hKC, hΓfix, hΓimage, hΓinter, hΓfront⟩ :=
    Diffeomorph.exists_compact_isotopy_image_trans H (fun t => (Ψ t).symm)
      hH hHi hH0 hK (fun t => ⟨(hfix t).1, (hfix t).2.1⟩) hΨi
      (by
        change ContDiff ℝ ∞ (fun z : ℝ × Plane => Ψ z.1 z.2)
        exact hΨ) hΨi0 hC
      (fun t => by
        change EqOn (Ψ t).symm id Cᶜ ∧ EqOn (Ψ t) id Cᶜ
        exact (hfixΨ t).symm)
      hHD hΨinverse
  refine ⟨v₀, v₁, r₀, r₁, f₀, f₁, e₀, e₁, ε₀, ε, J, W, K, F, H, hdata,
    n, Q, hQ, hregion, e, V, r, d, σ, R, θ, j, f, ρ, ℓ, A, η, Ψ, C,
    hnorm, ?_, hji, hcover, hf, hcompact, hregular, hΨ, hΨi, hΨ0, hC,
    hCK.trans inter_subset_left, hfixΨ, hΨimage, hΨinter, hΨfront,
    Γ, hΓeq, hΓ, hΓi, hΓ0, hKC, hΓfix, hΓimage, hΓinter, hΓfront⟩
  intro i
  obtain ⟨hV, hi, hVK, hd, hσ, hθ, hR, hKV, hside⟩ := hc i
  exact ⟨hV, hi, hVK.trans inter_subset_left, hd, hσ, hθ, hR, hKV, hside⟩

end Schoenflies

end

section

open Set Metric
open scoped ContDiff Manifold

namespace Schoenflies


theorem PrePolygon.exists_local_corner_replacement_isotopy_of_two_edge_free_triangle
    {m : ℕ} (P : PrePolygon m)
    (M : LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh)
    (hfrontier : frontier M.toPlaneComplex.support = P.carrier)
    (T : M.Triangle) (k : Fin 3) (hfree : M.IsTwoEdgeFreeTriangle T k) :
    let b := LeanEval.Topology.ClassificationOfSurfaces.Moise.affineBasisOfTriangle
      (M.freeTriangleOrder T k) (M.freeTriangleOrder_affineIndependent T k)
    ∃ (n : ℕ) (Q : PrePolygon n),
      Q.carrier = frontier (M.eraseTriangle T.1).toPlaneComplex.support ∧
      (M.eraseTriangle T.1).toPlaneComplex.support = closure (inside Q.carrier) ∧
    ∃ (e : Fin 3 → Plane ≃ᵃ[ℝ] Plane) (U : Fin 3 → Set Plane) (d s ε R : Fin 3 → ℝ)
      (e' : Fin 2 → Plane ≃ᵃ[ℝ] Plane) (U' : Fin 2 → Set Plane) (d' s' ε' R' : Fin 2 → ℝ)
      (W K : Set Plane) (H : ℝ → Plane ≃ₘ[ℝ] Plane),
      IsOpen W ∧ IsCompact K ∧ K ⊆ W ∧
      (∀ j, IsOpen (U j) ∧ b j ∈ U j ∧ U j ⊆ interior K ∧
        e j (b j) = 0 ∧ (d j = 0 ∨ d j = 1) ∧ (s j = -1 ∨ s j = 1) ∧
        0 < ε j ∧ 3 * ε j < R j ∧ e j ⁻¹' closedBall (0 : Plane) (R j) ⊆ U j ∧
        (∀ x ∈ U j, x ∈ M.toPlaneComplex.support ↔
          0 ≤ s j * ((e j x) 1 - d j * max ((e j x) 0) 0)) ∧
        (∀ x ∈ U j, x ∈ P.carrier ↔ (e j x) 1 = d j * max ((e j x) 0) 0) ∧
        (d j = 1 → ∃ (i : ZMod (m + 3)) (r : ℝ), P.vertex i = b j ∧ 0 < r ∧
          e j (P.vertex (i - 1)) = Plane.mk (-1) 0 ∧
          e j (P.vertex (i + 1)) = Plane.mk r r)) ∧
      (Pairwise fun i j => Disjoint (U i) (U j)) ∧
      (∀ j, IsOpen (U' j) ∧ b j.castSucc ∈ U' j ∧ U' j ⊆ interior K ∧
        e' j (b j.castSucc) = 0 ∧ (d' j = 0 ∨ d' j = 1) ∧ (s' j = -1 ∨ s' j = 1) ∧
        0 < ε' j ∧ 3 * ε' j < R' j ∧ e' j ⁻¹' closedBall (0 : Plane) (R' j) ⊆ U' j ∧
        (∀ x ∈ U' j, x ∈ (M.eraseTriangle T.1).toPlaneComplex.support ↔
          0 ≤ s' j * ((e' j x) 1 - d' j * max ((e' j x) 0) 0)) ∧
        (∀ x ∈ U' j, x ∈ Q.carrier ↔ (e' j x) 1 = d' j * max ((e' j x) 0) 0) ∧
        (d' j = 1 → ∃ (i : ZMod (n + 3)) (r : ℝ), Q.vertex i = b j.castSucc ∧ 0 < r ∧
          e' j (Q.vertex (i - 1)) = Plane.mk (-1) 0 ∧
          e' j (Q.vertex (i + 1)) = Plane.mk r r)) ∧
      (Pairwise fun i j => Disjoint (U' i) (U' j)) ∧
      (∀ i, P.vertex i ∈ W →
        Plane.det (P.vertex (i - 1) - P.vertex i) (P.vertex (i + 1) - P.vertex i) ≠ 0 →
        ∃ j, P.vertex i = b j ∧ d j = 1) ∧
      (∀ i, Q.vertex i ∈ W →
        Plane.det (Q.vertex (i - 1) - Q.vertex i) (Q.vertex (i + 1) - Q.vertex i) ≠ 0 →
        ∃ j : Fin 2, Q.vertex i = b j.castSucc ∧ d' j = 1) ∧
      (∀ x ∉ K, x ∈ P.carrier ↔ x ∈ Q.carrier) ∧
      let D := (M.toPlaneComplex.support \ ⋃ j, e j ⁻¹' ball (0 : Plane) (R j)) ∪
        ⋃ j, (e j ⁻¹' closedBall (0 : Plane) (R j)) ∩
          {x | 0 ≤ s j * ((e j x) 1 - d j * Real.smoothMax (ε j) ((e j x) 0) 0)}
      let E := ((M.eraseTriangle T.1).toPlaneComplex.support \
        ⋃ j, e' j ⁻¹' ball (0 : Plane) (R' j)) ∪
        ⋃ j, (e' j ⁻¹' closedBall (0 : Plane) (R' j)) ∩
          {x | 0 ≤ s' j * ((e' j x) 1 - d' j * Real.smoothMax (ε' j) ((e' j x) 0) 0)}
      IsCompact D ∧ IsCompact E ∧
      (∀ x ∈ frontier E, x ∈ W → ∃ (N : Set Plane) (G : Plane → ℝ),
        IsOpen N ∧ x ∈ N ∧ ContDiff ℝ ∞ G ∧ fderiv ℝ G x ≠ 0 ∧
        ∀ y ∈ N, (y ∈ E ↔ 0 ≤ G y) ∧
          (y ∈ interior E ↔ 0 < G y) ∧ (y ∈ frontier E ↔ G y = 0)) ∧
      ContDiff ℝ ∞ (fun z : ℝ × Plane => H z.1 z.2) ∧
      ContDiff ℝ ∞ (fun z : ℝ × Plane => (H z.1).symm z.2) ∧
      H 0 = Diffeomorph.refl 𝓘(ℝ, Plane) Plane ∞ ∧
      (∀ t, EqOn (H t) id Kᶜ ∧ EqOn (H t).symm id Kᶜ) ∧
      H 1 '' D = E ∧ H 1 '' interior D = interior E ∧ H 1 '' frontier D = frontier E := by
  dsimp only
  let b := LeanEval.Topology.ClassificationOfSurfaces.Moise.affineBasisOfTriangle
    (M.freeTriangleOrder T k) (M.freeTriangleOrder_affineIndependent T k)
  let S := M.toPlaneComplex.support
  let B := (M.eraseTriangle T.1).toPlaneComplex.support
  obtain ⟨v₀, v₁, r₀, r₁, f₀, f₁, e₀, e₁, hr₀, hr₁, hdisj, hs₀, hs₁,
      hf₀, hfb, hfc₀, hfv₀, hf₁, hfa, hfc₁, hfv₁, he₀, he₁, hgraph₀, hgraph₁⟩ :=
    P.exists_affine_graph_charts_of_two_edge_free_triangle M hfrontier T k hfree
  let s₀ := b.coord 2 v₀ / f₀ v₀
  let s₁ := b.coord 2 v₁ / f₁ v₁
  let N := (interior S ∩ {p | 0 < b.coord 0 p ∧ 0 < b.coord 1 p}) ∪
    (Bᶜ ∩ {p | 0 < b.coord 2 p})
  obtain ⟨hN, hNC, hNsides⟩ := P.two_edge_free_central_neighborhood M hfrontier T k hfree
  change IsOpen N at hN
  have htriangle : convexHull ℝ (range b) = M.triangleCarrier T.1 := by
    change convexHull ℝ (range ((M.position ∘ M.orderedVertex T) ∘ Equiv.swap 2 k)) = _
    rw [EquivLike.range_comp, Set.range_comp, M.range_orderedVertex T]
    rfl
  have hKN : convexHull ℝ (range b) \ {b 0, b 1} ⊆ N := by
    rw [htriangle]
    exact hNC
  obtain ⟨ε₀, εmax, J, hε₀, hεmax, _, hεmaxle, hJ, hTJ, hprofiles⟩ :=
    exists_regular_two_edge_affine_triangle_profiles b f₀ f₁ hf₀ hfb hfc₀ hf₁ hfa hfc₁
      s₀ s₁ (O₀ := ball (b 0) r₀) (O₁ := ball (b 1) r₁)
      isOpen_ball isOpen_ball (mem_ball_self hr₀) (mem_ball_self hr₁) N hN hKN
      (show (0 : ℝ) < 1 by norm_num)
  let U₀ := ball (b 0) r₀ ∩ {p | (1 : ℝ) / 4 < b.coord 0 p - b.coord 1 p}
  let U₁ := ball (b 1) r₁ ∩ {p | (1 : ℝ) / 4 < b.coord 1 p - b.coord 0 p}
  let V := {p | ε₀ < f₀ p ∧ ε₀ < f₁ p} ∩ N
  have hU₀ : IsOpen U₀ := isOpen_ball.inter (isOpen_lt continuous_const
    ((b.coord 0).continuous_of_finiteDimensional.sub (b.coord 1).continuous_of_finiteDimensional))
  have hU₁ : IsOpen U₁ := isOpen_ball.inter (isOpen_lt continuous_const
    ((b.coord 1).continuous_of_finiteDimensional.sub (b.coord 0).continuous_of_finiteDimensional))
  have hV : IsOpen V := ((isOpen_lt continuous_const f₀.continuous_of_finiteDimensional).inter
    (isOpen_lt continuous_const f₁.continuous_of_finiteDimensional)).inter hN
  have hbJ (i : Fin 3) : b i ∈ interior J := hTJ (subset_convexHull ℝ _ (mem_range_self i))
  have hb₀ : b 0 ∈ U₀ := ⟨mem_ball_self hr₀, by norm_num [b.coord_apply]⟩
  have hb₁ : b 1 ∈ U₁ := ⟨mem_ball_self hr₁, by norm_num [b.coord_apply]⟩
  have hb₂ : b 2 ∈ V := by
    obtain ⟨W, _, _, hJW, hcover, _⟩ :=
      hprofiles (1 / 4) ⟨by norm_num, le_rfl⟩ εmax ⟨hεmax, le_rfl⟩
    rcases hcover (hJW (interior_subset (hbJ 2))) with (h | h) | h
    · have : (1 : ℝ) / 4 < b.coord 0 (b 2) - b.coord 1 (b 2) := h.2
      rw [b.coord_apply_ne (by decide : (0 : Fin 3) ≠ 2),
        b.coord_apply_ne (by decide : (1 : Fin 3) ≠ 2)] at this
      linarith
    · have : (1 : ℝ) / 4 < b.coord 1 (b 2) - b.coord 0 (b 2) := h.2
      rw [b.coord_apply_ne (by decide : (1 : Fin 3) ≠ 2),
        b.coord_apply_ne (by decide : (0 : Fin 3) ≠ 2)] at this
      linarith
    · exact h
  obtain ⟨e₂, _, _, he₂c, he₂, hsmooth₂, hraw₂⟩ := exists_affine_triangle_corner_coordinates b
  let Og : Fin 3 → Set Plane := ![U₀, U₁, V]
  let O : Fin 3 → Set Plane := fun i => interior J ∩ Og i
  let f : Fin 3 → Plane ≃ᵃ[ℝ] Plane := ![e₀, e₁, e₂]
  let u : Fin 3 → ℝ := ![s₀, s₁, 0]
  let v : Fin 3 → ℝ := ![1 / f₀ (b 2), 1 / f₁ (b 2), 1]
  let c : Fin 3 → ℝ := ![-1, -1, 1]
  have hO (i : Fin 3) : IsOpen (O i) := by
    fin_cases i
    · exact isOpen_interior.inter hU₀
    · exact isOpen_interior.inter hU₁
    · exact isOpen_interior.inter hV
  have hOJ (i : Fin 3) : O i ⊆ interior J := by
    fin_cases i <;> exact inter_subset_left
  have hbO (i : Fin 3) : b i ∈ O i := by
    fin_cases i
    · exact ⟨hbJ 0, hb₀⟩
    · exact ⟨hbJ 1, hb₁⟩
    · exact ⟨hbJ 2, hb₂⟩
  have hf (i : Fin 3) : f i (b i) = 0 := by
    fin_cases i
    · ext j
      fin_cases j
      · exact (he₀ (b 0)).1.trans hf₀
      · exact (he₀ (b 0)).2.trans (by
          change b.coord 2 (b _) = 0; simp only [AffineBasis.coord_apply, Fin.reduceEq, if_false])
    · ext j
      fin_cases j
      · exact (he₁ (b 1)).1.trans hf₁
      · exact (he₁ (b 1)).2.trans (by
          change b.coord 2 (b _) = 0; simp only [AffineBasis.coord_apply, Fin.reduceEq, if_false])
    · exact he₂c
  have hc (i : Fin 3) : c i ≠ 0 := by fin_cases i <;> norm_num [c]
  have hgraph_full (i : Fin 3) (x : Plane) (hx : x ∈ Og i) : x ∈ P.carrier ↔
      (f i x) 1 = u i * (f i x) 0 + (v i - u i) * max ((f i x) 0) 0 := by
    fin_cases i
    · change x ∈ P.carrier ↔ (e₀ x) 1 = s₀ * (e₀ x) 0 +
        (1 / f₀ (b 2) - s₀) * max ((e₀ x) 0) 0
      rw [← hfrontier, (hgraph₀ x hx.1).2.2.1, (he₀ x).1, (he₀ x).2]
      dsimp only [s₀, b]
      ring_nf
    · change x ∈ P.carrier ↔ (e₁ x) 1 = s₁ * (e₁ x) 0 +
        (1 / f₁ (b 2) - s₁) * max ((e₁ x) 0) 0
      rw [← hfrontier, (hgraph₁ x hx.1).2.2.1, (he₁ x).1, (he₁ x).2]
      dsimp only [s₁, b]
      ring_nf
    · change x ∈ P.carrier ↔ (e₂ x) 1 = 0 * (e₂ x) 0 +
        (1 - 0) * max ((e₂ x) 0) 0
      simp only [zero_mul, sub_zero, one_mul, zero_add]
      rw [← sub_eq_zero, hraw₂, max_neg_neg, neg_neg, ← hfrontier]
      exact (hNsides x hx.2).1.2.2
  have hgraph (i : Fin 3) (x : Plane) (hx : x ∈ O i) : x ∈ P.carrier ↔
      (f i x) 1 = u i * (f i x) 0 + (v i - u i) * max ((f i x) 0) 0 :=
    hgraph_full i x hx.2
  obtain ⟨e, U, d, s, κ, R, δ, hcharts, hdisjoint, hrawsign, hcarrier, hreplace⟩ :=
    P.exists_finite_corner_replacement_of_local_graphs b b.ind.injective O f u v c
      hO hbO hf hc hgraph
  obtain ⟨n, Q, _, _, hQ, hregion, _⟩ :=
    P.exists_prePolygon_closed_region_erase_triangle_of_two_edge_free M hfrontier T k hfree
  let q : Fin 2 → Plane := fun i => b i.castSucc
  let O' : Fin 2 → Set Plane := fun i => O i.castSucc
  let f' : Fin 2 → Plane ≃ᵃ[ℝ] Plane := fun i => f i.castSucc
  let u' : Fin 2 → ℝ := fun i => u i.castSucc
  have hq : Function.Injective q := b.ind.injective.comp (Fin.castSucc_injective 2)
  have hgraph_full' (i : Fin 2) (x : Plane) (hx : x ∈ Og i.castSucc) : x ∈ Q.carrier ↔
      (f' i x) 1 = u' i * (f' i x) 0 + (0 - u' i) * max ((f' i x) 0) 0 := by
    fin_cases i
    · change x ∈ Q.carrier ↔ (e₀ x) 1 = s₀ * (e₀ x) 0 +
        (0 - s₀) * max ((e₀ x) 0) 0
      rw [hQ, (hgraph₀ x hx.1).2.2.2.2.2, (he₀ x).1, (he₀ x).2]
      dsimp only [s₀, b]
      ring_nf
    · change x ∈ Q.carrier ↔ (e₁ x) 1 = s₁ * (e₁ x) 0 +
        (0 - s₁) * max ((e₁ x) 0) 0
      rw [hQ, (hgraph₁ x hx.1).2.2.2.2.2, (he₁ x).1, (he₁ x).2]
      dsimp only [s₁, b]
      ring_nf
  have hgraph' (i : Fin 2) (x : Plane) (hx : x ∈ O' i) : x ∈ Q.carrier ↔
      (f' i x) 1 = u' i * (f' i x) 0 + (0 - u' i) * max ((f' i x) 0) 0 :=
    hgraph_full' i x hx.2
  obtain ⟨e', U', d', s', κ', R', δ', hcharts', hdisjoint', hrawsign', hcarrier', hreplace'⟩ :=
    Q.exists_finite_corner_replacement_of_local_graphs q hq O' f' u' (fun _ => 0)
      (fun _ => -1) (fun i => hO i.castSucc) (fun i => hbO i.castSucc)
      (fun i => hf i.castSucc) (fun _ => by norm_num) hgraph'
  have hδ i : 0 < δ i := by
    obtain ⟨_, _, _, _, _, _, _, _, _, h, _, _, _⟩ := hcharts i
    exact h
  have hδ' i : 0 < δ' i := by
    obtain ⟨_, _, _, _, _, _, _, _, _, h, _, _, _⟩ := hcharts' i
    exact h
  let ε := min εmax (min (δ 0) (min (δ 1) (min (δ' 0) (δ' 1))))
  have hε : 0 < ε := lt_min hεmax (lt_min (hδ 0) (lt_min (hδ 1) (lt_min (hδ' 0) (hδ' 1))))
  have hεmax' : ε ≤ εmax := min_le_left _ _
  have hεall : ε ≤ δ 0 ∧ ε ≤ δ 1 ∧ ε ≤ δ' 0 ∧ ε ≤ δ' 1 := by
    simpa only [le_min_iff] using
      (min_le_right εmax (min (δ 0) (min (δ 1) (min (δ' 0) (δ' 1)))))
  let σ := min (1 / 4) (δ 2)
  have hσ : 0 < σ := lt_min (by norm_num) (hδ 2)
  have hσsmall : σ ≤ 1 / 4 := min_le_left _ _
  let a : Fin 3 → ℝ := ![ε, ε, σ]
  have ha i : a i ∈ Ioc (0 : ℝ) (δ i) := by
    fin_cases i
    · exact ⟨hε, hεall.1⟩
    · exact ⟨hε, hεall.2.1⟩
    · exact ⟨hσ, min_le_right _ _⟩
  have ha' i : ε ∈ Ioc (0 : ℝ) (δ' i) := by
    fin_cases i
    · exact ⟨hε, hεall.2.2.1⟩
    · exact ⟨hε, hεall.2.2.2⟩
  obtain ⟨W, F, hW, hJW, hcover, hF, heW₀, heW₁, heWV, hzeroC,
      houter₀, hbase₀, houter₁, hbase₁, hreg, hprop⟩ :=
    hprofiles σ ⟨hσ, hσsmall⟩ ε ⟨hε, hεmax'⟩
  obtain ⟨K, H, hK, hJK, hKW, hH, hHi, hH0, hfix, hforward, hinverse⟩ :=
    Diffeomorph.exists_isotopy_level_and_sublevels_of_proportional_interpolation
      hF.fst hF.snd hW hJ hJW (fun t ht p hp _ => hreg t ht p (hJW hp)) hprop
  have hsides (x : Plane) (hx : x ∈ W) (hxJ : x ∉ interior J) :
      ((x ∈ S ↔ (F x).1 ≤ 0) ∧ (x ∈ interior S ↔ (F x).1 < 0) ∧
        (x ∈ frontier S ↔ (F x).1 = 0)) ∧
      ((x ∈ B ↔ (F x).2 ≤ 0) ∧ (x ∈ interior B ↔ (F x).2 < 0) ∧
        (x ∈ frontier B ↔ (F x).2 = 0)) := by
    rcases hcover hx with (hx₀ | hx₁) | hxV
    · have hraw := hgraph₀ x hx₀.1
      have ho := houter₀ x ⟨hx, hx₀⟩ hxJ
      have hn := hbase₀ x ⟨hx, hx₀⟩ hxJ
      exact ⟨⟨hraw.1.trans ho.1.symm, hraw.2.1.trans ho.2.1.symm,
        hraw.2.2.1.trans ho.2.2.symm⟩,
        hraw.2.2.2.1.trans hn.1.symm, hraw.2.2.2.2.1.trans hn.2.1.symm,
        hraw.2.2.2.2.2.trans hn.2.2.symm⟩
    · have hraw := hgraph₁ x hx₁.1
      have ho := houter₁ x ⟨hx, hx₁⟩ hxJ
      have hn := hbase₁ x ⟨hx, hx₁⟩ hxJ
      exact ⟨⟨hraw.1.trans ho.1.symm, hraw.2.1.trans ho.2.1.symm,
        hraw.2.2.1.trans ho.2.2.symm⟩,
        hraw.2.2.2.1.trans hn.1.symm, hraw.2.2.2.2.1.trans hn.2.1.symm,
        hraw.2.2.2.2.2.trans hn.2.2.symm⟩
    · have hxT : x ∉ M.triangleCarrier T.1 := fun h => hxJ (hTJ (htriangle.symm ▸ h))
      have hsame := mesh_erase_triangle_sides_of_not_mem M T hxT
      have hsign := linear_interpolation_signs_eq_of_ne_zero
        (fun t ht hz => hxT (htriangle ▸ hzeroC t ht x ⟨hx, hxV⟩ hz))
      have hnew := (hNsides x hxV.2).2
      have hF₂ : (F x).2 = b.coord 2 x := congrArg Prod.snd (heWV ⟨hx, hxV⟩)
      rw [← hF₂] at hnew
      exact ⟨⟨hsame.1.trans (hnew.1.trans hsign.1.symm),
        hsame.2.1.trans (hnew.2.1.trans hsign.2.1.symm),
        hsame.2.2.trans (hnew.2.2.trans hsign.2.2.symm)⟩, hnew⟩
  have hreg₀ (x : Plane) (hx : x ∈ W) : fderiv ℝ (fun q => (F q).1) x ≠ 0 := by
    simpa only [sub_zero, one_mul, zero_mul, add_zero] using hreg 0 ⟨le_rfl, zero_le_one⟩ x hx
  have hreg₁ (x : Plane) (hx : x ∈ W) : fderiv ℝ (fun q => (F q).2) x ≠ 0 := by
    simpa only [sub_self, zero_mul, one_mul, zero_add] using hreg 1 ⟨zero_le_one, le_rfl⟩ x hx
  let D := (S \ interior K) ∪ (K ∩ {x | (F x).1 ≤ 0})
  let E := (B \ interior K) ∪ (K ∩ {x | (F x).2 ≤ 0})
  obtain ⟨hD, hDsides, hDraw⟩ := compact_sublevel_replacement_preserving_germ
    M.toPlaneComplex.isCompact_support hK hW hKW hF.fst.continuous
    (fun x hx _ => hreg₀ x hx)
    (fun x hx => (hsides x hx.1 (fun hj => hx.2 (hJK (interior_subset hj)))).1.1)
  obtain ⟨hE, hEsides, hEraw⟩ := compact_sublevel_replacement_preserving_germ
    (M.eraseTriangle T.1).toPlaneComplex.isCompact_support hK hW hKW hF.snd.continuous
    (fun x hx _ => hreg₁ x hx)
    (fun x hx => (hsides x hx.1 (fun hj => hx.2 (hJK (interior_subset hj)))).2.1)
  have himage : (H 1) '' D = E := by
    ext x
    change x ∈ (H 1).toEquiv '' D ↔ x ∈ E
    rw [Set.mem_image_equiv]
    change (H 1).symm x ∈ D ↔ x ∈ E
    by_cases hx : x ∈ W
    · exact (hDsides ((H 1).symm x) (((hfix 1).2.2.2 x).mpr hx)).1.trans
        ((hinverse x hx).2.2.symm.trans (hEsides x hx).1.symm)
    · have hxK : x ∉ K := fun h => hx (hKW h)
      rw [(hfix 1).2.1 hxK]
      have hxT : x ∉ M.triangleCarrier T.1 :=
        fun h => hxK (interior_subset (hJK (interior_subset (hTJ (htriangle.symm ▸ h)))))
      have hsame : x ∈ S ↔ x ∈ B := by
        dsimp only [S, B]
        rw [M.support_eq_eraseTriangle_union_triangleCarrier T.2]
        exact or_iff_left hxT
      exact (hDraw x hxK).1.trans (hsame.trans (hEraw x hxK).1.symm)
  have hSraw (i : Fin 3) (x : Plane) (hx : x ∈ O i) : x ∈ S ↔
      0 ≤ c i * ((f i x) 1 - u i * (f i x) 0 -
        (v i - u i) * max ((f i x) 0) 0) := by
    fin_cases i
    · change x ∈ S ↔ 0 ≤ -1 * ((e₀ x) 1 - s₀ * (e₀ x) 0 -
        (1 / f₀ (b 2) - s₀) * max ((e₀ x) 0) 0)
      rw [(hgraph₀ x hx.2.1).1, (he₀ x).1, (he₀ x).2]
      dsimp only [s₀, b]
      simp only [div_eq_mul_inv, one_mul]
      constructor <;> intro h <;> nlinarith only [h]
    · change x ∈ S ↔ 0 ≤ -1 * ((e₁ x) 1 - s₁ * (e₁ x) 0 -
        (1 / f₁ (b 2) - s₁) * max ((e₁ x) 0) 0)
      rw [(hgraph₁ x hx.2.1).1, (he₁ x).1, (he₁ x).2]
      dsimp only [s₁, b]
      simp only [div_eq_mul_inv, one_mul]
      constructor <;> intro h <;> nlinarith only [h]
    · change x ∈ S ↔ 0 ≤ 1 * ((e₂ x) 1 - 0 * (e₂ x) 0 -
        (1 - 0) * max ((e₂ x) 0) 0)
      simp only [one_mul, zero_mul, sub_zero, hraw₂, max_neg_neg, neg_neg]
      exact (hNsides x hx.2.2).1.1
  have hDsm (i : Fin 3) (x : Plane) (hx : x ∈ O i) : x ∈ D ↔
      0 ≤ c i * ((f i x) 1 - u i * (f i x) 0 -
        (v i - u i) * Real.smoothMax (a i) ((f i x) 0) 0) := by
    have hxW : x ∈ W := hJW (interior_subset (hOJ i hx))
    fin_cases i
    · change x ∈ D ↔ 0 ≤ -1 * ((e₀ x) 1 - s₀ * (e₀ x) 0 -
        (1 / f₀ (b 2) - s₀) * Real.smoothMax ε ((e₀ x) 0) 0)
      rw [(hDsides x hxW).1, congrArg Prod.fst (heW₀ ⟨hxW, hx.2⟩), neg_nonpos,
        mul_nonneg_iff_of_pos_left (div_pos hfc₀ hfb), (he₀ x).1, (he₀ x).2]
      dsimp only [s₀, b]
      simp only [div_eq_mul_inv, one_mul]
      constructor <;> intro h <;> nlinarith only [h]
    · change x ∈ D ↔ 0 ≤ -1 * ((e₁ x) 1 - s₁ * (e₁ x) 0 -
        (1 / f₁ (b 2) - s₁) * Real.smoothMax ε ((e₁ x) 0) 0)
      rw [(hDsides x hxW).1, congrArg Prod.fst (heW₁ ⟨hxW, hx.2⟩), neg_nonpos,
        mul_nonneg_iff_of_pos_left (div_pos hfc₁ hfa), (he₁ x).1, (he₁ x).2]
      dsimp only [s₁, b]
      simp only [div_eq_mul_inv, one_mul]
      constructor <;> intro h <;> nlinarith only [h]
    · change x ∈ D ↔ 0 ≤ 1 * ((e₂ x) 1 - 0 * (e₂ x) 0 -
        (1 - 0) * Real.smoothMax σ ((e₂ x) 0) 0)
      simp only [one_mul, zero_mul, sub_zero, hsmooth₂, neg_nonneg]
      rw [(hDsides x hxW).1, congrArg Prod.fst (heWV ⟨hxW, hx.2⟩)]
  have hDoutside (x : Plane) (hx : x ∉ ⋃ i, O i) : x ∈ D ↔ x ∈ S := by
    by_cases hxW : x ∈ W
    · have hxJ : x ∉ interior J := by
        intro hxJ
        rcases hcover hxW with (hx₀ | hx₁) | hx₂
        · exact hx (mem_iUnion.mpr ⟨0, hxJ, hx₀⟩)
        · exact hx (mem_iUnion.mpr ⟨1, hxJ, hx₁⟩)
        · exact hx (mem_iUnion.mpr ⟨2, hxJ, hx₂⟩)
      exact (hDsides x hxW).1.trans (hsides x hxW hxJ).1.1.symm
    · exact (hDraw x (fun h => hxW (hKW h))).1
  have hDnative := (hreplace a ha).2 S D hSraw hDsm hDoutside
  have hBraw (i : Fin 2) (x : Plane) (hx : x ∈ O' i) : x ∈ B ↔
      0 ≤ -1 * ((f' i x) 1 - u' i * (f' i x) 0 -
        (0 - u' i) * max ((f' i x) 0) 0) := by
    fin_cases i
    · change x ∈ B ↔ 0 ≤ -1 * ((e₀ x) 1 - s₀ * (e₀ x) 0 -
        (0 - s₀) * max ((e₀ x) 0) 0)
      rw [(hgraph₀ x hx.2.1).2.2.2.1, (he₀ x).1, (he₀ x).2]
      dsimp only [s₀, b]
      simp only [div_eq_mul_inv]
      constructor <;> intro h <;> nlinarith only [h]
    · change x ∈ B ↔ 0 ≤ -1 * ((e₁ x) 1 - s₁ * (e₁ x) 0 -
        (0 - s₁) * max ((e₁ x) 0) 0)
      rw [(hgraph₁ x hx.2.1).2.2.2.1, (he₁ x).1, (he₁ x).2]
      dsimp only [s₁, b]
      simp only [div_eq_mul_inv]
      constructor <;> intro h <;> nlinarith only [h]
  have hEsm (i : Fin 2) (x : Plane) (hx : x ∈ O' i) : x ∈ E ↔
      0 ≤ -1 * ((f' i x) 1 - u' i * (f' i x) 0 -
        (0 - u' i) * Real.smoothMax ε ((f' i x) 0) 0) := by
    have hxW : x ∈ W := hJW (interior_subset (hOJ i.castSucc hx))
    fin_cases i
    · change x ∈ E ↔ 0 ≤ -1 * ((e₀ x) 1 - s₀ * (e₀ x) 0 -
        (0 - s₀) * Real.smoothMax ε ((e₀ x) 0) 0)
      rw [(hEsides x hxW).1, congrArg Prod.snd (heW₀ ⟨hxW, hx.2⟩),
        (he₀ x).1, (he₀ x).2]
      dsimp only [s₀, b]
      simp only [div_eq_mul_inv]
      constructor <;> intro h <;> nlinarith only [h]
    · change x ∈ E ↔ 0 ≤ -1 * ((e₁ x) 1 - s₁ * (e₁ x) 0 -
        (0 - s₁) * Real.smoothMax ε ((e₁ x) 0) 0)
      rw [(hEsides x hxW).1, congrArg Prod.snd (heW₁ ⟨hxW, hx.2⟩),
        (he₁ x).1, (he₁ x).2]
      dsimp only [s₁, b]
      simp only [div_eq_mul_inv]
      constructor <;> intro h <;> nlinarith only [h]
  have hEoutside (x : Plane) (hx : x ∉ ⋃ i, O' i) : x ∈ E ↔ x ∈ B := by
    by_cases hxW : x ∈ W
    · rcases hcover hxW with (hx₀ | hx₁) | hx₂
      · have hxJ : x ∉ interior J := fun hj => hx (mem_iUnion.mpr ⟨0, hj, hx₀⟩)
        exact (hEsides x hxW).1.trans (hsides x hxW hxJ).2.1.symm
      · have hxJ : x ∉ interior J := fun hj => hx (mem_iUnion.mpr ⟨1, hj, hx₁⟩)
        exact (hEsides x hxW).1.trans (hsides x hxW hxJ).2.1.symm
      · rw [(hEsides x hxW).1, congrArg Prod.snd (heWV ⟨hxW, hx₂⟩)]
        exact (hNsides x hx₂.2).2.1.symm
    · exact (hEraw x (fun h => hxW (hKW h))).1
  have hEnative := (hreplace' (fun _ => ε) ha').2 B E hBraw hEsm hEoutside
  have hOg (j : Fin 3) : IsOpen (Og j) := by
    fin_cases j
    · exact hU₀
    · exact hU₁
    · exact hV
  have hPactive (i : ZMod (m + 3)) (hiW : P.vertex i ∈ W)
      (hdet : Plane.det (P.vertex (i - 1) - P.vertex i)
        (P.vertex (i + 1) - P.vertex i) ≠ 0) :
      ∃ j : Fin 3, P.vertex i = b j ∧ d j = 1 := by
    have hiOg : P.vertex i ∈ ⋃ j, Og j := by
      rcases hcover hiW with (h | h) | h
      · exact mem_iUnion.mpr ⟨0, h⟩
      · exact mem_iUnion.mpr ⟨1, h⟩
      · exact mem_iUnion.mpr ⟨2, h⟩
    obtain ⟨j, hj⟩ := mem_iUnion.mp hiOg
    have hij := P.vertex_eq_of_local_piecewise_affine_graph (f j) (hOg j) (hf j)
      (fun x hx hxc => (hgraph_full j x hx).mp hxc) i hj hdet
    obtain ⟨_, _, _, _, hd, _⟩ := hcharts j
    rcases hd with hd | hd
    · exfalso
      apply hdet
      apply P.det_eq_zero_of_local_line i (e j) (c := 0) (hO j) (hij.symm ▸ hbO j)
      intro x hx hxc
      simpa only [hd, zero_mul] using (hcarrier j x hx).mp hxc
    · exact ⟨j, hij, hd⟩
  have hQactive (i : ZMod (n + 3)) (hiW : Q.vertex i ∈ W)
      (hdet : Plane.det (Q.vertex (i - 1) - Q.vertex i)
        (Q.vertex (i + 1) - Q.vertex i) ≠ 0) :
      ∃ j : Fin 2, Q.vertex i = q j ∧ d' j = 1 := by
    have hendpoint (j : Fin 2) (hj : Q.vertex i ∈ Og j.castSucc) :
        ∃ j : Fin 2, Q.vertex i = q j ∧ d' j = 1 := by
      have hij := Q.vertex_eq_of_local_piecewise_affine_graph (f' j) (hOg j.castSucc)
        (hf j.castSucc) (fun x hx hxc => (hgraph_full' j x hx).mp hxc) i hj hdet
      obtain ⟨_, _, _, _, hd, _⟩ := hcharts' j
      rcases hd with hd | hd
      · exfalso
        apply hdet
        apply Q.det_eq_zero_of_local_line i (e' j) (c := 0)
          (hO j.castSucc) (hij.symm ▸ hbO j.castSucc)
        intro x hx hxc
        simpa only [hd, zero_mul] using (hcarrier' j x hx).mp hxc
      · exact ⟨j, hij, hd⟩
    rcases hcover hiW with (h | h) | h
    · exact hendpoint 0 h
    · exact hendpoint 1 h
    · exfalso
      apply hdet
      apply Q.det_eq_zero_of_local_line i e₀ (c := 0) hV h
      intro x hx hxc
      exact (he₀ x).2.trans ((hNsides x hx.2).2.2.2.mp (hQ ▸ hxc))
  have hcar (x : Plane) (hx : x ∉ K) : x ∈ P.carrier ↔ x ∈ Q.carrier := by
    have hxT : x ∉ M.triangleCarrier T.1 :=
      fun h => hx (interior_subset (hJK (interior_subset (hTJ (htriangle.symm ▸ h)))))
    rw [← hfrontier, hQ]
    exact (mesh_erase_triangle_sides_of_not_mem M T hxT).2.2
  have hgood : ∀ x ∈ frontier E, x ∈ W → ∃ (N : Set Plane) (G : Plane → ℝ),
      IsOpen N ∧ x ∈ N ∧ ContDiff ℝ ∞ G ∧ fderiv ℝ G x ≠ 0 ∧
      ∀ y ∈ N, (y ∈ E ↔ 0 ≤ G y) ∧
        (y ∈ interior E ↔ 0 < G y) ∧ (y ∈ frontier E ↔ G y = 0) := by
    intro x _ hx
    refine ⟨W, fun y => -(F y).2, hW, hx, hF.snd.neg, ?_, ?_⟩
    · rw [fderiv_fun_neg]
      exact neg_ne_zero.mpr (hreg₁ x hx)
    · intro y hy
      simpa only [neg_nonneg, neg_pos, neg_eq_zero] using hEsides y hy
  refine ⟨n, Q, hQ, hregion, e, U, d, s, (fun i => κ i * a i), R,
    e', U', d', s', (fun i => κ' i * ε), R', W, K, H,
    hW, hK, hKW, ?_, hdisjoint, ?_, hdisjoint', hPactive, hQactive, hcar, ?_⟩
  · intro j
    obtain ⟨hU, hbU, hUO, he, hd, _, hs, hκ, _, _, hRU, hbound, hvertex⟩ := hcharts j
    refine ⟨hU, hbU, fun x hx => hJK (interior_subset (hUO hx).1),
      he, hd, hs, mul_pos hκ (ha j).1, hbound (a j) (ha j), hRU, ?_, ?_, hvertex⟩
    · intro x hx
      exact (hSraw j x (hUO hx)).trans (hrawsign j x)
    · exact fun x hx => hcarrier j x (hUO hx)
  · intro j
    obtain ⟨hU, hbU, hUO, he, hd, _, hs, hκ, _, _, hRU, hbound, hvertex⟩ := hcharts' j
    refine ⟨hU, hbU, fun x hx => hJK (interior_subset (hUO hx).1),
      he, hd, hs, mul_pos hκ hε, hbound ε (ha' j), hRU, ?_, ?_, hvertex⟩
    · intro x hx
      exact (hBraw j x (hUO hx)).trans (hrawsign' j x)
    · exact fun x hx => hcarrier' j x (hUO hx)
  · dsimp only
    rw [← hDnative, ← hEnative]
    exact ⟨hD, hE, hgood, hH, hHi, hH0, fun t => ⟨(hfix t).1, (hfix t).2.1⟩,
      himage, ((H 1).toHomeomorph.image_interior D).trans (congrArg interior himage),
      ((H 1).toHomeomorph.image_frontier D).trans (congrArg frontier himage)⟩

end Schoenflies

end

section

open Set Metric
open scoped ContDiff Manifold

namespace Schoenflies

theorem PrePolygon.exists_local_corner_replacement_isotopy_of_one_edge_free_triangle
    {m : ℕ} (P : PrePolygon m)
    (M : LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh)
    (hfrontier : frontier M.toPlaneComplex.support = P.carrier)
    (T : M.Triangle) (k : Fin 3) (hfree : M.IsOneEdgeFreeTriangle T k) :
    let b := LeanEval.Topology.ClassificationOfSurfaces.Moise.affineBasisOfTriangle
      (M.freeTriangleOrder T k) (M.freeTriangleOrder_affineIndependent T k)
    ∃ (n : ℕ) (Q : PrePolygon n),
      Q.carrier = frontier (M.eraseTriangle T.1).toPlaneComplex.support ∧
      (M.eraseTriangle T.1).toPlaneComplex.support = closure (inside Q.carrier) ∧
    ∃ (e : Fin 2 → Plane ≃ᵃ[ℝ] Plane) (U : Fin 2 → Set Plane) (d s ε R : Fin 2 → ℝ)
      (e' : Fin 3 → Plane ≃ᵃ[ℝ] Plane) (U' : Fin 3 → Set Plane) (d' s' ε' R' : Fin 3 → ℝ)
      (W K : Set Plane) (H : ℝ → Plane ≃ₘ[ℝ] Plane),
      IsOpen W ∧ IsCompact K ∧ K ⊆ W ∧
      (∀ j, IsOpen (U j) ∧ b j.castSucc ∈ U j ∧ U j ⊆ interior K ∧
        e j (b j.castSucc) = 0 ∧ (d j = 0 ∨ d j = 1) ∧ (s j = -1 ∨ s j = 1) ∧
        0 < ε j ∧ 3 * ε j < R j ∧ e j ⁻¹' closedBall (0 : Plane) (R j) ⊆ U j ∧
        (∀ x ∈ U j, x ∈ M.toPlaneComplex.support ↔
          0 ≤ s j * ((e j x) 1 - d j * max ((e j x) 0) 0)) ∧
        (∀ x ∈ U j, x ∈ P.carrier ↔ (e j x) 1 = d j * max ((e j x) 0) 0) ∧
        (d j = 1 → ∃ (i : ZMod (m + 3)) (r : ℝ), P.vertex i = b j.castSucc ∧ 0 < r ∧
          e j (P.vertex (i - 1)) = Plane.mk (-1) 0 ∧
          e j (P.vertex (i + 1)) = Plane.mk r r)) ∧
      (Pairwise fun i j => Disjoint (U i) (U j)) ∧
      (∀ j, IsOpen (U' j) ∧ b j ∈ U' j ∧ U' j ⊆ interior K ∧
        e' j (b j) = 0 ∧ (d' j = 0 ∨ d' j = 1) ∧ (s' j = -1 ∨ s' j = 1) ∧
        0 < ε' j ∧ 3 * ε' j < R' j ∧ e' j ⁻¹' closedBall (0 : Plane) (R' j) ⊆ U' j ∧
        (∀ x ∈ U' j, x ∈ (M.eraseTriangle T.1).toPlaneComplex.support ↔
          0 ≤ s' j * ((e' j x) 1 - d' j * max ((e' j x) 0) 0)) ∧
        (∀ x ∈ U' j, x ∈ Q.carrier ↔ (e' j x) 1 = d' j * max ((e' j x) 0) 0) ∧
        (d' j = 1 → ∃ (i : ZMod (n + 3)) (r : ℝ), Q.vertex i = b j ∧ 0 < r ∧
          e' j (Q.vertex (i - 1)) = Plane.mk (-1) 0 ∧
          e' j (Q.vertex (i + 1)) = Plane.mk r r)) ∧
      (Pairwise fun i j => Disjoint (U' i) (U' j)) ∧
      (∀ i, P.vertex i ∈ W →
        Plane.det (P.vertex (i - 1) - P.vertex i) (P.vertex (i + 1) - P.vertex i) ≠ 0 →
        ∃ j, P.vertex i = b j.castSucc ∧ d j = 1) ∧
      (∀ i, Q.vertex i ∈ W →
        Plane.det (Q.vertex (i - 1) - Q.vertex i) (Q.vertex (i + 1) - Q.vertex i) ≠ 0 →
        ∃ j : Fin 3, Q.vertex i = b j ∧ d' j = 1) ∧
      (∀ x ∉ K, x ∈ P.carrier ↔ x ∈ Q.carrier) ∧
      let D := (M.toPlaneComplex.support \ ⋃ j, e j ⁻¹' ball (0 : Plane) (R j)) ∪
        ⋃ j, (e j ⁻¹' closedBall (0 : Plane) (R j)) ∩
          {x | 0 ≤ s j * ((e j x) 1 - d j * Real.smoothMax (ε j) ((e j x) 0) 0)}
      let E := ((M.eraseTriangle T.1).toPlaneComplex.support \
        ⋃ j, e' j ⁻¹' ball (0 : Plane) (R' j)) ∪
        ⋃ j, (e' j ⁻¹' closedBall (0 : Plane) (R' j)) ∩
          {x | 0 ≤ s' j * ((e' j x) 1 - d' j * Real.smoothMax (ε' j) ((e' j x) 0) 0)}
      IsCompact D ∧ IsCompact E ∧
      (∀ x ∈ frontier E, x ∈ W → ∃ (N : Set Plane) (G : Plane → ℝ),
        IsOpen N ∧ x ∈ N ∧ ContDiff ℝ ∞ G ∧ fderiv ℝ G x ≠ 0 ∧
        ∀ y ∈ N, (y ∈ E ↔ 0 ≤ G y) ∧
          (y ∈ interior E ↔ 0 < G y) ∧ (y ∈ frontier E ↔ G y = 0)) ∧
      ContDiff ℝ ∞ (fun z : ℝ × Plane => H z.1 z.2) ∧
      ContDiff ℝ ∞ (fun z : ℝ × Plane => (H z.1).symm z.2) ∧
      H 0 = Diffeomorph.refl 𝓘(ℝ, Plane) Plane ∞ ∧
      (∀ t, EqOn (H t) id Kᶜ ∧ EqOn (H t).symm id Kᶜ) ∧
      H 1 '' D = E ∧ H 1 '' interior D = interior E ∧ H 1 '' frontier D = frontier E := by
  dsimp only
  let b := LeanEval.Topology.ClassificationOfSurfaces.Moise.affineBasisOfTriangle
    (M.freeTriangleOrder T k) (M.freeTriangleOrder_affineIndependent T k)
  let S := (M.eraseTriangle T.1).toPlaneComplex.support
  let B := M.toPlaneComplex.support
  obtain ⟨v₀, v₁, r₀, r₁, f₀, f₁, e₀, e₁, hr₀, hr₁, hdisj, hs₀, hs₁,
      hf₀, hfb, hfc₀, hfv₀, hf₁, hfa, hfc₁, hfv₁, he₀, he₁, hgraph₀, hgraph₁⟩ :=
    P.exists_affine_graph_charts_of_one_edge_free_triangle M hfrontier T k hfree
  obtain ⟨n, Q, _, _, hQ, hregion, _⟩ :=
    P.exists_prePolygon_closed_region_erase_triangle_of_one_edge_free M hfrontier T k hfree
  have hmax (s x : ℝ) : s * (x - max x 0) = if x < 0 then s * x else 0 := by
    by_cases hx : x < 0
    · rw [if_pos hx, max_eq_right hx.le, sub_zero]
    · rw [if_neg hx, max_eq_left (le_of_not_gt hx), sub_self, mul_zero]
  have hmax' (s x z : ℝ) : s * (x - max x 0) + max x 0 / z =
      if x < 0 then s * x else x / z := by
    by_cases hx : x < 0
    · rw [if_pos hx, max_eq_right hx.le, sub_zero, zero_div, add_zero]
    · rw [if_neg hx, max_eq_left (le_of_not_gt hx), sub_self, mul_zero, zero_add]
  let s₀ := b.coord 2 v₀ / f₀ v₀
  let s₁ := b.coord 2 v₁ / f₁ v₁
  let N := (interior B ∩ {p | 0 < b.coord 2 p}) ∪
    (Sᶜ ∩ {p | 0 < b.coord 0 p ∧ 0 < b.coord 1 p})
  obtain ⟨hN, hNC, hNold⟩ := M.one_edge_free_central_neighborhood T k hfree
  have hNnew := M.one_edge_free_central_survivor_sides T k hfree
  have hNsides (x : Plane) (hx : x ∈ N) := And.intro (hNnew x hx) (hNold x hx)
  change IsOpen N at hN
  have htriangle : convexHull ℝ (range b) = M.triangleCarrier T.1 := by
    change convexHull ℝ (range ((M.position ∘ M.orderedVertex T) ∘ Equiv.swap 2 k)) = _
    rw [EquivLike.range_comp, Set.range_comp, M.range_orderedVertex T]
    rfl
  have hKN : convexHull ℝ (range b) \ {b 0, b 1} ⊆ N := by
    rw [htriangle]
    exact hNC
  obtain ⟨ε₀, εmax, J, hε₀, hεmax, _, hεmaxle, hJ, hTJ, hprofiles⟩ :=
    exists_regular_two_edge_affine_triangle_profiles b f₀ f₁ hf₀ hfb hfc₀ hf₁ hfa hfc₁
      s₀ s₁ (O₀ := ball (b 0) r₀) (O₁ := ball (b 1) r₁)
      isOpen_ball isOpen_ball (mem_ball_self hr₀) (mem_ball_self hr₁) N hN hKN
      (show (0 : ℝ) < 1 by norm_num)
  let U₀ := ball (b 0) r₀ ∩ {p | (1 : ℝ) / 4 < b.coord 0 p - b.coord 1 p}
  let U₁ := ball (b 1) r₁ ∩ {p | (1 : ℝ) / 4 < b.coord 1 p - b.coord 0 p}
  let V := {p | ε₀ < f₀ p ∧ ε₀ < f₁ p} ∩ N
  have hU₀ : IsOpen U₀ := isOpen_ball.inter (isOpen_lt continuous_const
    ((b.coord 0).continuous_of_finiteDimensional.sub (b.coord 1).continuous_of_finiteDimensional))
  have hU₁ : IsOpen U₁ := isOpen_ball.inter (isOpen_lt continuous_const
    ((b.coord 1).continuous_of_finiteDimensional.sub (b.coord 0).continuous_of_finiteDimensional))
  have hV : IsOpen V := ((isOpen_lt continuous_const f₀.continuous_of_finiteDimensional).inter
    (isOpen_lt continuous_const f₁.continuous_of_finiteDimensional)).inter hN
  have hbJ (i : Fin 3) : b i ∈ interior J := hTJ (subset_convexHull ℝ _ (mem_range_self i))
  have hb₀ : b 0 ∈ U₀ := ⟨mem_ball_self hr₀, by norm_num [b.coord_apply]⟩
  have hb₁ : b 1 ∈ U₁ := ⟨mem_ball_self hr₁, by norm_num [b.coord_apply]⟩
  have hb₂ : b 2 ∈ V := by
    obtain ⟨W, _, _, hJW, hcover, _⟩ :=
      hprofiles (1 / 4) ⟨by norm_num, le_rfl⟩ εmax ⟨hεmax, le_rfl⟩
    rcases hcover (hJW (interior_subset (hbJ 2))) with (h | h) | h
    · have : (1 : ℝ) / 4 < b.coord 0 (b 2) - b.coord 1 (b 2) := h.2
      rw [b.coord_apply_ne (by decide : (0 : Fin 3) ≠ 2),
        b.coord_apply_ne (by decide : (1 : Fin 3) ≠ 2)] at this
      linarith
    · have : (1 : ℝ) / 4 < b.coord 1 (b 2) - b.coord 0 (b 2) := h.2
      rw [b.coord_apply_ne (by decide : (1 : Fin 3) ≠ 2),
        b.coord_apply_ne (by decide : (0 : Fin 3) ≠ 2)] at this
      linarith
    · exact h
  obtain ⟨e₂, _, _, he₂c, he₂, hsmooth₂, hraw₂⟩ := exists_affine_triangle_corner_coordinates b
  let Og : Fin 3 → Set Plane := ![U₀, U₁, V]
  let O : Fin 3 → Set Plane := fun i => interior J ∩ Og i
  let f : Fin 3 → Plane ≃ᵃ[ℝ] Plane := ![e₀, e₁, e₂]
  let u : Fin 3 → ℝ := ![s₀, s₁, 0]
  let v : Fin 3 → ℝ := ![1 / f₀ (b 2), 1 / f₁ (b 2), 1]
  let c : Fin 3 → ℝ := ![1, 1, -1]
  have hO (i : Fin 3) : IsOpen (O i) := by
    fin_cases i
    · exact isOpen_interior.inter hU₀
    · exact isOpen_interior.inter hU₁
    · exact isOpen_interior.inter hV
  have hOJ (i : Fin 3) : O i ⊆ interior J := by
    fin_cases i <;> exact inter_subset_left
  have hbO (i : Fin 3) : b i ∈ O i := by
    fin_cases i
    · exact ⟨hbJ 0, hb₀⟩
    · exact ⟨hbJ 1, hb₁⟩
    · exact ⟨hbJ 2, hb₂⟩
  have hf (i : Fin 3) : f i (b i) = 0 := by
    fin_cases i
    · ext j
      fin_cases j
      · exact (he₀ (b 0)).1.trans hf₀
      · exact (he₀ (b 0)).2.trans (by
          change b.coord 2 (b _) = 0; simp only [AffineBasis.coord_apply, Fin.reduceEq, if_false])
    · ext j
      fin_cases j
      · exact (he₁ (b 1)).1.trans hf₁
      · exact (he₁ (b 1)).2.trans (by
          change b.coord 2 (b _) = 0; simp only [AffineBasis.coord_apply, Fin.reduceEq, if_false])
    · exact he₂c
  have hc (i : Fin 3) : c i ≠ 0 := by fin_cases i <;> norm_num [c]
  have hgraph_full (i : Fin 3) (x : Plane) (hx : x ∈ Og i) : x ∈ Q.carrier ↔
      (f i x) 1 = u i * (f i x) 0 + (v i - u i) * max ((f i x) 0) 0 := by
    fin_cases i
    · change x ∈ Q.carrier ↔ (e₀ x) 1 = s₀ * (e₀ x) 0 +
        (1 / f₀ (b 2) - s₀) * max ((e₀ x) 0) 0
      rw [hQ, (hgraph₀ x hx.1).2.2.2.2.2, ← hmax', (he₀ x).1, (he₀ x).2]
      dsimp only [s₀, b]
      ring_nf
    · change x ∈ Q.carrier ↔ (e₁ x) 1 = s₁ * (e₁ x) 0 +
        (1 / f₁ (b 2) - s₁) * max ((e₁ x) 0) 0
      rw [hQ, (hgraph₁ x hx.1).2.2.2.2.2, ← hmax', (he₁ x).1, (he₁ x).2]
      dsimp only [s₁, b]
      ring_nf
    · change x ∈ Q.carrier ↔ (e₂ x) 1 = 0 * (e₂ x) 0 +
        (1 - 0) * max ((e₂ x) 0) 0
      simp only [zero_mul, sub_zero, one_mul, zero_add]
      rw [← sub_eq_zero, hraw₂, max_neg_neg, neg_neg, hQ]
      exact (hNsides x hx.2).1.2.2
  have hgraph (i : Fin 3) (x : Plane) (hx : x ∈ O i) : x ∈ Q.carrier ↔
      (f i x) 1 = u i * (f i x) 0 + (v i - u i) * max ((f i x) 0) 0 :=
    hgraph_full i x hx.2
  obtain ⟨e, U, d, s, κ, R, δ, hcharts, hdisjoint, hrawsign, hcarrier, hreplace⟩ :=
    Q.exists_finite_corner_replacement_of_local_graphs b b.ind.injective O f u v c
      hO hbO hf hc hgraph
  let q : Fin 2 → Plane := fun i => b i.castSucc
  let O' : Fin 2 → Set Plane := fun i => O i.castSucc
  let f' : Fin 2 → Plane ≃ᵃ[ℝ] Plane := fun i => f i.castSucc
  let u' : Fin 2 → ℝ := fun i => u i.castSucc
  have hq : Function.Injective q := b.ind.injective.comp (Fin.castSucc_injective 2)
  have hgraph_full' (i : Fin 2) (x : Plane) (hx : x ∈ Og i.castSucc) : x ∈ P.carrier ↔
      (f' i x) 1 = u' i * (f' i x) 0 + (0 - u' i) * max ((f' i x) 0) 0 := by
    fin_cases i
    · change x ∈ P.carrier ↔ (e₀ x) 1 = s₀ * (e₀ x) 0 +
        (0 - s₀) * max ((e₀ x) 0) 0
      rw [← hfrontier, (hgraph₀ x hx.1).2.2.1, ← hmax, (he₀ x).1, (he₀ x).2]
      dsimp only [s₀, b]
      ring_nf
    · change x ∈ P.carrier ↔ (e₁ x) 1 = s₁ * (e₁ x) 0 +
        (0 - s₁) * max ((e₁ x) 0) 0
      rw [← hfrontier, (hgraph₁ x hx.1).2.2.1, ← hmax, (he₁ x).1, (he₁ x).2]
      dsimp only [s₁, b]
      ring_nf
  have hgraph' (i : Fin 2) (x : Plane) (hx : x ∈ O' i) : x ∈ P.carrier ↔
      (f' i x) 1 = u' i * (f' i x) 0 + (0 - u' i) * max ((f' i x) 0) 0 :=
    hgraph_full' i x hx.2
  obtain ⟨e', U', d', s', κ', R', δ', hcharts', hdisjoint', hrawsign', hcarrier', hreplace'⟩ :=
    P.exists_finite_corner_replacement_of_local_graphs q hq O' f' u' (fun _ => 0)
      (fun _ => 1) (fun i => hO i.castSucc) (fun i => hbO i.castSucc)
      (fun i => hf i.castSucc) (fun _ => by norm_num) hgraph'
  have hδ i : 0 < δ i := by
    obtain ⟨_, _, _, _, _, _, _, _, _, h, _, _, _⟩ := hcharts i
    exact h
  have hδ' i : 0 < δ' i := by
    obtain ⟨_, _, _, _, _, _, _, _, _, h, _, _, _⟩ := hcharts' i
    exact h
  let ε := min εmax (min (δ 0) (min (δ 1) (min (δ' 0) (δ' 1))))
  have hε : 0 < ε := lt_min hεmax (lt_min (hδ 0) (lt_min (hδ 1) (lt_min (hδ' 0) (hδ' 1))))
  have hεmax' : ε ≤ εmax := min_le_left _ _
  have hεall : ε ≤ δ 0 ∧ ε ≤ δ 1 ∧ ε ≤ δ' 0 ∧ ε ≤ δ' 1 := by
    simpa only [le_min_iff] using
      (min_le_right εmax (min (δ 0) (min (δ 1) (min (δ' 0) (δ' 1)))))
  let σ := min (1 / 4) (δ 2)
  have hσ : 0 < σ := lt_min (by norm_num) (hδ 2)
  have hσsmall : σ ≤ 1 / 4 := min_le_left _ _
  let a : Fin 3 → ℝ := ![ε, ε, σ]
  have ha i : a i ∈ Ioc (0 : ℝ) (δ i) := by
    fin_cases i
    · exact ⟨hε, hεall.1⟩
    · exact ⟨hε, hεall.2.1⟩
    · exact ⟨hσ, min_le_right _ _⟩
  have ha' i : ε ∈ Ioc (0 : ℝ) (δ' i) := by
    fin_cases i
    · exact ⟨hε, hεall.2.2.1⟩
    · exact ⟨hε, hεall.2.2.2⟩
  obtain ⟨W, F, hW, hJW, hcover, hF, heW₀, heW₁, heWV, hzeroC,
      houter₀, hbase₀, houter₁, hbase₁, hreg, hprop⟩ :=
    hprofiles σ ⟨hσ, hσsmall⟩ ε ⟨hε, hεmax'⟩
  obtain ⟨K, H, hK, hJK, hKW, hH, hHi, hH0, hfix, hforward, hinverse⟩ :=
    Diffeomorph.exists_isotopy_level_and_sublevels_of_proportional_interpolation
      hF.fst.neg hF.snd.neg hW hJ hJW
      (fun t ht p hp _ => by
        have heq : (fun q => (1 - t) * -(F q).1 + t * -(F q).2) =
            fun q => -((1 - t) * (F q).1 + t * (F q).2) := by funext q; ring
        rw [heq, fderiv_fun_neg]
        exact neg_ne_zero.mpr (hreg t ht p (hJW hp)))
      (fun t ht p hp hz hpJ => by
        have hz' : (1 - t) * (F p).1 + t * (F p).2 = 0 := by linarith only [hz]
        obtain ⟨r, hr, U, hU, hpU, hUW, heq⟩ := hprop t ht p hp hz' hpJ
        refine ⟨r, hr, U, hU, hpU, hUW, ?_⟩
        intro q hq
        dsimp only
        have hh : (F q).2 = r * (F q).1 := heq hq
        rw [hh]
        ring)
  have hsides (x : Plane) (hx : x ∈ W) (hxJ : x ∉ interior J) :
      ((x ∈ S ↔ -(F x).1 ≤ 0) ∧ (x ∈ interior S ↔ -(F x).1 < 0) ∧
        (x ∈ frontier S ↔ -(F x).1 = 0)) ∧
      ((x ∈ B ↔ -(F x).2 ≤ 0) ∧ (x ∈ interior B ↔ -(F x).2 < 0) ∧
        (x ∈ frontier B ↔ -(F x).2 = 0)) := by
    have hreverse {u v w : ℝ}
        (h : (u ≤ 0 ↔ v ≤ w) ∧ (u < 0 ↔ v < w) ∧ (u = 0 ↔ v = w)) :
        (w ≤ v ↔ -u ≤ 0) ∧ (w < v ↔ -u < 0) ∧ (v = w ↔ -u = 0) := by
      refine ⟨?_, ?_, ?_⟩
      · simpa only [not_lt, neg_nonpos] using (not_congr h.2.1).symm
      · simpa only [not_le, neg_lt_zero] using (not_congr h.1).symm
      · simpa only [neg_eq_zero] using h.2.2.symm
    rcases hcover hx with (hx₀ | hx₁) | hxV
    · have hraw := hgraph₀ x hx₀.1
      rw [← hmax, ← hmax'] at hraw
      have ho := hreverse (houter₀ x ⟨hx, hx₀⟩ hxJ)
      have hn := hreverse (hbase₀ x ⟨hx, hx₀⟩ hxJ)
      exact ⟨⟨hraw.2.2.2.1.trans ho.1, hraw.2.2.2.2.1.trans ho.2.1,
        hraw.2.2.2.2.2.trans ho.2.2⟩, hraw.1.trans hn.1,
        hraw.2.1.trans hn.2.1, hraw.2.2.1.trans hn.2.2⟩
    · have hraw := hgraph₁ x hx₁.1
      rw [← hmax, ← hmax'] at hraw
      have ho := hreverse (houter₁ x ⟨hx, hx₁⟩ hxJ)
      have hn := hreverse (hbase₁ x ⟨hx, hx₁⟩ hxJ)
      exact ⟨⟨hraw.2.2.2.1.trans ho.1, hraw.2.2.2.2.1.trans ho.2.1,
        hraw.2.2.2.2.2.trans ho.2.2⟩, hraw.1.trans hn.1,
        hraw.2.1.trans hn.2.1, hraw.2.2.1.trans hn.2.2⟩
    · have hxT : x ∉ M.triangleCarrier T.1 := fun h => hxJ (hTJ (htriangle.symm ▸ h))
      have hsame := mesh_erase_triangle_sides_of_not_mem M T hxT
      have hsign := linear_interpolation_signs_eq_of_ne_zero
        (fun t ht hz => hxT (htriangle ▸ hzeroC t ht x ⟨hx, hxV⟩ hz))
      have hnew := (hNsides x hxV.2).2
      have hF₂ : (F x).2 = b.coord 2 x := congrArg Prod.snd (heWV ⟨hx, hxV⟩)
      rw [← hF₂] at hnew
      have hsign' : (0 ≤ (F x).1 ↔ 0 ≤ (F x).2) ∧
          (0 < (F x).1 ↔ 0 < (F x).2) ∧ ((F x).1 = 0 ↔ (F x).2 = 0) := by
        refine ⟨?_, ?_, hsign.2.2⟩
        · simpa only [not_lt] using not_congr hsign.2.1
        · simpa only [not_le] using not_congr hsign.1
      simp only [neg_nonpos, neg_lt_zero, neg_eq_zero]
      exact ⟨⟨hsame.1.symm.trans (hnew.1.trans hsign'.1.symm),
        hsame.2.1.symm.trans (hnew.2.1.trans hsign'.2.1.symm),
        hsame.2.2.symm.trans (hnew.2.2.trans hsign'.2.2.symm)⟩, hnew⟩
  have hreg₀ (x : Plane) (hx : x ∈ W) : fderiv ℝ (fun q => (F q).1) x ≠ 0 := by
    simpa only [sub_zero, one_mul, zero_mul, add_zero] using hreg 0 ⟨le_rfl, zero_le_one⟩ x hx
  have hreg₁ (x : Plane) (hx : x ∈ W) : fderiv ℝ (fun q => (F q).2) x ≠ 0 := by
    simpa only [sub_self, zero_mul, one_mul, zero_add] using hreg 1 ⟨zero_le_one, le_rfl⟩ x hx
  let D := (S \ interior K) ∪ (K ∩ {x | -(F x).1 ≤ 0})
  let E := (B \ interior K) ∪ (K ∩ {x | -(F x).2 ≤ 0})
  obtain ⟨hD, hDsides, hDraw⟩ := compact_sublevel_replacement_preserving_germ
    (M.eraseTriangle T.1).toPlaneComplex.isCompact_support hK hW hKW hF.fst.neg.continuous
    (fun x hx _ => by rw [fderiv_fun_neg]; exact neg_ne_zero.mpr (hreg₀ x hx))
    (fun x hx => (hsides x hx.1 (fun hj => hx.2 (hJK (interior_subset hj)))).1.1)
  obtain ⟨hE, hEsides, hEraw⟩ := compact_sublevel_replacement_preserving_germ
    M.toPlaneComplex.isCompact_support hK hW hKW hF.snd.neg.continuous
    (fun x hx _ => by rw [fderiv_fun_neg]; exact neg_ne_zero.mpr (hreg₁ x hx))
    (fun x hx => (hsides x hx.1 (fun hj => hx.2 (hJK (interior_subset hj)))).2.1)
  have himage : (H 1) '' D = E := by
    ext x
    change x ∈ (H 1).toEquiv '' D ↔ x ∈ E
    rw [Set.mem_image_equiv]
    change (H 1).symm x ∈ D ↔ x ∈ E
    by_cases hx : x ∈ W
    · exact (hDsides ((H 1).symm x) (((hfix 1).2.2.2 x).mpr hx)).1.trans
        ((hinverse x hx).2.2.symm.trans (hEsides x hx).1.symm)
    · have hxK : x ∉ K := fun h => hx (hKW h)
      rw [(hfix 1).2.1 hxK]
      have hxT : x ∉ M.triangleCarrier T.1 :=
        fun h => hxK (interior_subset (hJK (interior_subset (hTJ (htriangle.symm ▸ h)))))
      have hsame : x ∈ S ↔ x ∈ B := by
        dsimp only [S, B]
        rw [M.support_eq_eraseTriangle_union_triangleCarrier T.2]
        exact (or_iff_left hxT).symm
      exact (hDraw x hxK).1.trans (hsame.trans (hEraw x hxK).1.symm)
  have hSraw (i : Fin 3) (x : Plane) (hx : x ∈ O i) : x ∈ S ↔
      0 ≤ c i * ((f i x) 1 - u i * (f i x) 0 -
        (v i - u i) * max ((f i x) 0) 0) := by
    fin_cases i
    · change x ∈ S ↔ 0 ≤ 1 * ((e₀ x) 1 - s₀ * (e₀ x) 0 -
        (1 / f₀ (b 2) - s₀) * max ((e₀ x) 0) 0)
      rw [(hgraph₀ x hx.2.1).2.2.2.1, ← hmax', (he₀ x).1, (he₀ x).2]
      dsimp only [s₀, b]
      simp only [div_eq_mul_inv, one_mul]
      constructor <;> intro h <;> nlinarith only [h]
    · change x ∈ S ↔ 0 ≤ 1 * ((e₁ x) 1 - s₁ * (e₁ x) 0 -
        (1 / f₁ (b 2) - s₁) * max ((e₁ x) 0) 0)
      rw [(hgraph₁ x hx.2.1).2.2.2.1, ← hmax', (he₁ x).1, (he₁ x).2]
      dsimp only [s₁, b]
      simp only [div_eq_mul_inv, one_mul]
      constructor <;> intro h <;> nlinarith only [h]
    · change x ∈ S ↔ 0 ≤ -1 * ((e₂ x) 1 - 0 * (e₂ x) 0 -
        (1 - 0) * max ((e₂ x) 0) 0)
      simp only [neg_one_mul, zero_mul, sub_zero, one_mul, hraw₂, max_neg_neg, neg_neg, neg_nonneg]
      exact (hNsides x hx.2.2).1.1
  have hmul {a z : ℝ} (ha : 0 < a) : a * z ≤ 0 ↔ z ≤ 0 :=
    ⟨fun h => nonpos_of_mul_nonpos_right h ha, fun h => mul_nonpos_of_nonneg_of_nonpos ha.le h⟩
  have hDsm (i : Fin 3) (x : Plane) (hx : x ∈ O i) : x ∈ D ↔
      0 ≤ c i * ((f i x) 1 - u i * (f i x) 0 -
        (v i - u i) * Real.smoothMax (a i) ((f i x) 0) 0) := by
    have hxW : x ∈ W := hJW (interior_subset (hOJ i hx))
    fin_cases i
    · change x ∈ D ↔ 0 ≤ 1 * ((e₀ x) 1 - s₀ * (e₀ x) 0 -
        (1 / f₀ (b 2) - s₀) * Real.smoothMax ε ((e₀ x) 0) 0)
      rw [(hDsides x hxW).1, congrArg Prod.fst (heW₀ ⟨hxW, hx.2⟩), neg_neg,
        hmul (div_pos hfc₀ hfb), (he₀ x).1, (he₀ x).2]
      dsimp only [s₀, b]
      simp only [div_eq_mul_inv, one_mul]
      constructor <;> intro h <;> nlinarith only [h]
    · change x ∈ D ↔ 0 ≤ 1 * ((e₁ x) 1 - s₁ * (e₁ x) 0 -
        (1 / f₁ (b 2) - s₁) * Real.smoothMax ε ((e₁ x) 0) 0)
      rw [(hDsides x hxW).1, congrArg Prod.fst (heW₁ ⟨hxW, hx.2⟩), neg_neg,
        hmul (div_pos hfc₁ hfa), (he₁ x).1, (he₁ x).2]
      dsimp only [s₁, b]
      simp only [div_eq_mul_inv, one_mul]
      constructor <;> intro h <;> nlinarith only [h]
    · change x ∈ D ↔ 0 ≤ -1 * ((e₂ x) 1 - 0 * (e₂ x) 0 -
        (1 - 0) * Real.smoothMax σ ((e₂ x) 0) 0)
      simp only [neg_one_mul, zero_mul, sub_zero, one_mul, hsmooth₂, neg_neg]
      rw [(hDsides x hxW).1, congrArg Prod.fst (heWV ⟨hxW, hx.2⟩)]
      exact neg_nonpos
  have hDoutside (x : Plane) (hx : x ∉ ⋃ i, O i) : x ∈ D ↔ x ∈ S := by
    by_cases hxW : x ∈ W
    · have hxJ : x ∉ interior J := by
        intro hxJ
        rcases hcover hxW with (hx₀ | hx₁) | hx₂
        · exact hx (mem_iUnion.mpr ⟨0, hxJ, hx₀⟩)
        · exact hx (mem_iUnion.mpr ⟨1, hxJ, hx₁⟩)
        · exact hx (mem_iUnion.mpr ⟨2, hxJ, hx₂⟩)
      exact (hDsides x hxW).1.trans (hsides x hxW hxJ).1.1.symm
    · exact (hDraw x (fun h => hxW (hKW h))).1
  have hDnative := (hreplace a ha).2 S D hSraw hDsm hDoutside
  have hBraw (i : Fin 2) (x : Plane) (hx : x ∈ O' i) : x ∈ B ↔
      0 ≤ 1 * ((f' i x) 1 - u' i * (f' i x) 0 -
        (0 - u' i) * max ((f' i x) 0) 0) := by
    fin_cases i
    · change x ∈ B ↔ 0 ≤ 1 * ((e₀ x) 1 - s₀ * (e₀ x) 0 -
        (0 - s₀) * max ((e₀ x) 0) 0)
      rw [(hgraph₀ x hx.2.1).1, ← hmax, (he₀ x).1, (he₀ x).2]
      dsimp only [s₀, b]
      simp only [div_eq_mul_inv]
      constructor <;> intro h <;> nlinarith only [h]
    · change x ∈ B ↔ 0 ≤ 1 * ((e₁ x) 1 - s₁ * (e₁ x) 0 -
        (0 - s₁) * max ((e₁ x) 0) 0)
      rw [(hgraph₁ x hx.2.1).1, ← hmax, (he₁ x).1, (he₁ x).2]
      dsimp only [s₁, b]
      simp only [div_eq_mul_inv]
      constructor <;> intro h <;> nlinarith only [h]
  have hEsm (i : Fin 2) (x : Plane) (hx : x ∈ O' i) : x ∈ E ↔
      0 ≤ 1 * ((f' i x) 1 - u' i * (f' i x) 0 -
        (0 - u' i) * Real.smoothMax ε ((f' i x) 0) 0) := by
    have hxW : x ∈ W := hJW (interior_subset (hOJ i.castSucc hx))
    fin_cases i
    · change x ∈ E ↔ 0 ≤ 1 * ((e₀ x) 1 - s₀ * (e₀ x) 0 -
        (0 - s₀) * Real.smoothMax ε ((e₀ x) 0) 0)
      rw [(hEsides x hxW).1, congrArg Prod.snd (heW₀ ⟨hxW, hx.2⟩),
        (he₀ x).1, (he₀ x).2]
      dsimp only [s₀, b]
      simp only [div_eq_mul_inv]
      constructor <;> intro h <;> nlinarith only [h]
    · change x ∈ E ↔ 0 ≤ 1 * ((e₁ x) 1 - s₁ * (e₁ x) 0 -
        (0 - s₁) * Real.smoothMax ε ((e₁ x) 0) 0)
      rw [(hEsides x hxW).1, congrArg Prod.snd (heW₁ ⟨hxW, hx.2⟩),
        (he₁ x).1, (he₁ x).2]
      dsimp only [s₁, b]
      simp only [div_eq_mul_inv]
      constructor <;> intro h <;> nlinarith only [h]
  have hEoutside (x : Plane) (hx : x ∉ ⋃ i, O' i) : x ∈ E ↔ x ∈ B := by
    by_cases hxW : x ∈ W
    · rcases hcover hxW with (hx₀ | hx₁) | hx₂
      · have hxJ : x ∉ interior J := fun hj => hx (mem_iUnion.mpr ⟨0, hj, hx₀⟩)
        exact (hEsides x hxW).1.trans (hsides x hxW hxJ).2.1.symm
      · have hxJ : x ∉ interior J := fun hj => hx (mem_iUnion.mpr ⟨1, hj, hx₁⟩)
        exact (hEsides x hxW).1.trans (hsides x hxW hxJ).2.1.symm
      · rw [(hEsides x hxW).1, congrArg Prod.snd (heWV ⟨hxW, hx₂⟩)]
        simpa only [neg_nonpos] using (hNsides x hx₂.2).2.1.symm
    · exact (hEraw x (fun h => hxW (hKW h))).1
  have hEnative := (hreplace' (fun _ => ε) ha').2 B E hBraw hEsm hEoutside
  have hOg (j : Fin 3) : IsOpen (Og j) := by
    fin_cases j
    · exact hU₀
    · exact hU₁
    · exact hV
  have hPactive (i : ZMod (n + 3)) (hiW : Q.vertex i ∈ W)
      (hdet : Plane.det (Q.vertex (i - 1) - Q.vertex i)
        (Q.vertex (i + 1) - Q.vertex i) ≠ 0) :
      ∃ j : Fin 3, Q.vertex i = b j ∧ d j = 1 := by
    have hiOg : Q.vertex i ∈ ⋃ j, Og j := by
      rcases hcover hiW with (h | h) | h
      · exact mem_iUnion.mpr ⟨0, h⟩
      · exact mem_iUnion.mpr ⟨1, h⟩
      · exact mem_iUnion.mpr ⟨2, h⟩
    obtain ⟨j, hj⟩ := mem_iUnion.mp hiOg
    have hij := Q.vertex_eq_of_local_piecewise_affine_graph (f j) (hOg j) (hf j)
      (fun x hx hxc => (hgraph_full j x hx).mp hxc) i hj hdet
    obtain ⟨_, _, _, _, hd, _⟩ := hcharts j
    rcases hd with hd | hd
    · exfalso
      apply hdet
      apply Q.det_eq_zero_of_local_line i (e j) (c := 0) (hO j) (hij.symm ▸ hbO j)
      intro x hx hxc
      simpa only [hd, zero_mul] using (hcarrier j x hx).mp hxc
    · exact ⟨j, hij, hd⟩
  have hQactive (i : ZMod (m + 3)) (hiW : P.vertex i ∈ W)
      (hdet : Plane.det (P.vertex (i - 1) - P.vertex i)
        (P.vertex (i + 1) - P.vertex i) ≠ 0) :
      ∃ j : Fin 2, P.vertex i = q j ∧ d' j = 1 := by
    have hendpoint (j : Fin 2) (hj : P.vertex i ∈ Og j.castSucc) :
        ∃ j : Fin 2, P.vertex i = q j ∧ d' j = 1 := by
      have hij := P.vertex_eq_of_local_piecewise_affine_graph (f' j) (hOg j.castSucc)
        (hf j.castSucc) (fun x hx hxc => (hgraph_full' j x hx).mp hxc) i hj hdet
      obtain ⟨_, _, _, _, hd, _⟩ := hcharts' j
      rcases hd with hd | hd
      · exfalso
        apply hdet
        apply P.det_eq_zero_of_local_line i (e' j) (c := 0)
          (hO j.castSucc) (hij.symm ▸ hbO j.castSucc)
        intro x hx hxc
        simpa only [hd, zero_mul] using (hcarrier' j x hx).mp hxc
      · exact ⟨j, hij, hd⟩
    rcases hcover hiW with (h | h) | h
    · exact hendpoint 0 h
    · exact hendpoint 1 h
    · exfalso
      apply hdet
      apply P.det_eq_zero_of_local_line i e₀ (c := 0) hV h
      intro x hx hxc
      exact (he₀ x).2.trans ((hNsides x hx.2).2.2.2.mp (hfrontier.symm ▸ hxc))
  have hcar (x : Plane) (hx : x ∉ K) : x ∈ P.carrier ↔ x ∈ Q.carrier := by
    have hxT : x ∉ M.triangleCarrier T.1 :=
      fun h => hx (interior_subset (hJK (interior_subset (hTJ (htriangle.symm ▸ h)))))
    rw [← hfrontier, hQ]
    exact (mesh_erase_triangle_sides_of_not_mem M T hxT).2.2
  have hgood : ∀ x ∈ frontier D, x ∈ W → ∃ (N : Set Plane) (G : Plane → ℝ),
      IsOpen N ∧ x ∈ N ∧ ContDiff ℝ ∞ G ∧ fderiv ℝ G x ≠ 0 ∧
      ∀ y ∈ N, (y ∈ D ↔ 0 ≤ G y) ∧
        (y ∈ interior D ↔ 0 < G y) ∧ (y ∈ frontier D ↔ G y = 0) := by
    intro x _ hx
    refine ⟨W, fun y => (F y).1, hW, hx, hF.fst, ?_, ?_⟩
    · exact hreg₀ x hx
    · intro y hy
      simpa only [D, S, neg_nonpos, neg_lt_zero, neg_eq_zero] using hDsides y hy
  have hinvimage : (H 1).symm '' E = D := by
    rw [← himage]
    exact (H 1).toEquiv.symm_image_image D
  refine ⟨n, Q, hQ, hregion, e', U', d', s', (fun i => κ' i * ε), R',
    e, U, d, s, (fun i => κ i * a i), R, W, K, (fun t => (H t).symm),
    hW, hK, hKW, ?_, hdisjoint', ?_, hdisjoint, hQactive, hPactive, hcar, ?_⟩
  · intro j
    obtain ⟨hU, hbU, hUO, he, hd, _, hs, hκ, _, _, hRU, hbound, hvertex⟩ := hcharts' j
    refine ⟨hU, hbU, fun x hx => hJK (interior_subset (hUO hx).1),
      he, hd, hs, mul_pos hκ hε, hbound ε (ha' j), hRU, ?_, ?_, hvertex⟩
    · intro x hx
      exact (hBraw j x (hUO hx)).trans (hrawsign' j x)
    · exact fun x hx => hcarrier' j x (hUO hx)
  · intro j
    obtain ⟨hU, hbU, hUO, he, hd, _, hs, hκ, _, _, hRU, hbound, hvertex⟩ := hcharts j
    refine ⟨hU, hbU, fun x hx => hJK (interior_subset (hUO hx).1),
      he, hd, hs, mul_pos hκ (ha j).1, hbound (a j) (ha j), hRU, ?_, ?_, hvertex⟩
    · intro x hx
      exact (hSraw j x (hUO hx)).trans (hrawsign j x)
    · exact fun x hx => hcarrier j x (hUO hx)
  · dsimp only
    rw [← hEnative, ← hDnative]
    refine ⟨hE, hD, hgood, hHi, hH, ?_, fun t => ⟨(hfix t).2.1, (hfix t).1⟩,
      hinvimage, ((H 1).symm.toHomeomorph.image_interior E).trans (congrArg interior hinvimage),
      ((H 1).symm.toHomeomorph.image_frontier E).trans (congrArg frontier hinvimage)⟩
    rw [hH0]
    rfl

end Schoenflies

end

section

open Set Metric
open scoped ContDiff Manifold

namespace Schoenflies

private theorem PrePolygon.exists_global_corner_replacement_isotopy
    {m n : ℕ} (P : PrePolygon m) (Q : PrePolygon n) {ι κ : Type*}
    (p : ι → Plane) (hp : Function.Injective p) (q : κ → Plane) (hq : Function.Injective q)
    (e : ι → Plane ≃ᵃ[ℝ] Plane) (U : ι → Set Plane) (d s ε R : ι → ℝ)
    (e' : κ → Plane ≃ᵃ[ℝ] Plane) (U' : κ → Set Plane) (d' s' ε' R' : κ → ℝ)
    (W K : Set Plane) (H : ℝ → Plane ≃ₘ[ℝ] Plane)
    (hW : IsOpen W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hA : ∀ j, IsOpen (U j) ∧ p j ∈ U j ∧ U j ⊆ interior K ∧
      e j (p j) = 0 ∧ (d j = 0 ∨ d j = 1) ∧ (s j = -1 ∨ s j = 1) ∧
      0 < ε j ∧ 3 * ε j < R j ∧ e j ⁻¹' closedBall (0 : Plane) (R j) ⊆ U j ∧
      (∀ x ∈ U j, x ∈ closure (inside P.carrier) ↔
        0 ≤ s j * ((e j x) 1 - d j * max ((e j x) 0) 0)) ∧
      (∀ x ∈ U j, x ∈ P.carrier ↔ (e j x) 1 = d j * max ((e j x) 0) 0) ∧
      (d j = 1 → ∃ (i : ZMod (m + 3)) (r : ℝ), P.vertex i = p j ∧ 0 < r ∧
        e j (P.vertex (i - 1)) = Plane.mk (-1) 0 ∧
        e j (P.vertex (i + 1)) = Plane.mk r r))
    (hAdisj : Pairwise fun i j => Disjoint (U i) (U j))
    (hB : ∀ j, IsOpen (U' j) ∧ q j ∈ U' j ∧ U' j ⊆ interior K ∧
      e' j (q j) = 0 ∧ (d' j = 0 ∨ d' j = 1) ∧ (s' j = -1 ∨ s' j = 1) ∧
      0 < ε' j ∧ 3 * ε' j < R' j ∧ e' j ⁻¹' closedBall (0 : Plane) (R' j) ⊆ U' j ∧
      (∀ x ∈ U' j, x ∈ closure (inside Q.carrier) ↔
        0 ≤ s' j * ((e' j x) 1 - d' j * max ((e' j x) 0) 0)) ∧
      (∀ x ∈ U' j, x ∈ Q.carrier ↔ (e' j x) 1 = d' j * max ((e' j x) 0) 0) ∧
      (d' j = 1 → ∃ (i : ZMod (n + 3)) (r : ℝ), Q.vertex i = q j ∧ 0 < r ∧
        e' j (Q.vertex (i - 1)) = Plane.mk (-1) 0 ∧
        e' j (Q.vertex (i + 1)) = Plane.mk r r))
    (hBdisj : Pairwise fun i j => Disjoint (U' i) (U' j))
    (hPcover : ∀ i, P.vertex i ∈ W →
      Plane.det (P.vertex (i - 1) - P.vertex i) (P.vertex (i + 1) - P.vertex i) ≠ 0 →
      ∃ j, P.vertex i = p j ∧ d j = 1)
    (hQcover : ∀ i, Q.vertex i ∈ W →
      Plane.det (Q.vertex (i - 1) - Q.vertex i) (Q.vertex (i + 1) - Q.vertex i) ≠ 0 →
      ∃ j, Q.vertex i = q j ∧ d' j = 1)
    (hcar : ∀ x ∉ K, x ∈ P.carrier ↔ x ∈ Q.carrier) :
    let D := (closure (inside P.carrier) \ ⋃ j, e j ⁻¹' ball (0 : Plane) (R j)) ∪
      ⋃ j, (e j ⁻¹' closedBall (0 : Plane) (R j)) ∩
        {x | 0 ≤ s j * ((e j x) 1 - d j * Real.smoothMax (ε j) ((e j x) 0) 0)}
    let E := (closure (inside Q.carrier) \ ⋃ j, e' j ⁻¹' ball (0 : Plane) (R' j)) ∪
      ⋃ j, (e' j ⁻¹' closedBall (0 : Plane) (R' j)) ∩
        {x | 0 ≤ s' j * ((e' j x) 1 - d' j * Real.smoothMax (ε' j) ((e' j x) 0) 0)}
    IsCompact E →
    (∀ x ∈ frontier E, x ∈ W → ∃ (N : Set Plane) (G : Plane → ℝ),
      IsOpen N ∧ x ∈ N ∧ ContDiff ℝ ∞ G ∧ fderiv ℝ G x ≠ 0 ∧
      ∀ y ∈ N, (y ∈ E ↔ 0 ≤ G y) ∧
        (y ∈ interior E ↔ 0 < G y) ∧ (y ∈ frontier E ↔ G y = 0)) →
    ContDiff ℝ ∞ (fun z : ℝ × Plane => H z.1 z.2) →
    ContDiff ℝ ∞ (fun z : ℝ × Plane => (H z.1).symm z.2) →
    H 0 = Diffeomorph.refl 𝓘(ℝ, Plane) Plane ∞ →
    (∀ t, EqOn (H t) id Kᶜ ∧ EqOn (H t).symm id Kᶜ) → H 1 '' D = E →
    let I := {i : ZMod (m + 3) //
      Plane.det (P.vertex (i - 1) - P.vertex i) (P.vertex (i + 1) - P.vertex i) ≠ 0}
    let J := {i : ZMod (n + 3) //
      Plane.det (Q.vertex (i - 1) - Q.vertex i) (Q.vertex (i + 1) - Q.vertex i) ≠ 0}
    ∃ (g : I → Plane ≃ᵃ[ℝ] Plane) (V : I → Set Plane) (σ η A : I → ℝ)
      (g' : J → Plane ≃ᵃ[ℝ] Plane) (V' : J → Set Plane) (σ' η' A' : J → ℝ)
      (Φ : ℝ → Plane ≃ₘ[ℝ] Plane) (C : Set Plane),
      (∀ i, IsOpen (V i) ∧ P.vertex i ∈ V i ∧ g i (P.vertex i) = 0 ∧
        (σ i = -1 ∨ σ i = 1) ∧ 0 < η i ∧ 3 * η i < A i ∧
        g i ⁻¹' closedBall (0 : Plane) (A i) ⊆ V i ∧
        (∀ x ∈ V i, x ∈ closure (inside P.carrier) ↔
          0 ≤ σ i * ((g i x) 1 - max ((g i x) 0) 0)) ∧
        ∃ r : ℝ, 0 < r ∧ g i (P.vertex (i.val - 1)) = Plane.mk (-1) 0 ∧
          g i (P.vertex (i.val + 1)) = Plane.mk r r) ∧
      (Pairwise fun i j => Disjoint (V i) (V j)) ∧
      (∀ i, IsOpen (V' i) ∧ Q.vertex i ∈ V' i ∧ g' i (Q.vertex i) = 0 ∧
        (σ' i = -1 ∨ σ' i = 1) ∧ 0 < η' i ∧ 3 * η' i < A' i ∧
        g' i ⁻¹' closedBall (0 : Plane) (A' i) ⊆ V' i ∧
        (∀ x ∈ V' i, x ∈ closure (inside Q.carrier) ↔
          0 ≤ σ' i * ((g' i x) 1 - max ((g' i x) 0) 0)) ∧
        ∃ r : ℝ, 0 < r ∧ g' i (Q.vertex (i.val - 1)) = Plane.mk (-1) 0 ∧
          g' i (Q.vertex (i.val + 1)) = Plane.mk r r) ∧
      (Pairwise fun i j => Disjoint (V' i) (V' j)) ∧
      let D₀ := (closure (inside P.carrier) \ ⋃ i, g i ⁻¹' ball (0 : Plane) (A i)) ∪
        ⋃ i, (g i ⁻¹' closedBall (0 : Plane) (A i)) ∩
          {x | 0 ≤ σ i * ((g i x) 1 - Real.smoothMax (η i) ((g i x) 0) 0)}
      let D₁ := (closure (inside Q.carrier) \ ⋃ i, g' i ⁻¹' ball (0 : Plane) (A' i)) ∪
        ⋃ i, (g' i ⁻¹' closedBall (0 : Plane) (A' i)) ∩
          {x | 0 ≤ σ' i * ((g' i x) 1 - Real.smoothMax (η' i) ((g' i x) 0) 0)}
      ContDiff ℝ ∞ (fun z : ℝ × Plane => Φ z.1 z.2) ∧
      ContDiff ℝ ∞ (fun z : ℝ × Plane => (Φ z.1).symm z.2) ∧
      Φ 0 = Diffeomorph.refl 𝓘(ℝ, Plane) Plane ∞ ∧ IsCompact C ∧
      (∀ t, EqOn (Φ t) id Cᶜ ∧ EqOn (Φ t).symm id Cᶜ) ∧
      Φ 1 '' D₀ = D₁ ∧ Φ 1 '' interior D₀ = interior D₁ ∧
      Φ 1 '' frontier D₀ = frontier D₁ := by
  dsimp only
  intro hE hgood hH hHi hH0 hfix himage
  classical
  let S := closure (inside P.carrier)
  let B := closure (inside Q.carrier)
  let D := (S \ ⋃ j, e j ⁻¹' ball (0 : Plane) (R j)) ∪
    ⋃ j, (e j ⁻¹' closedBall (0 : Plane) (R j)) ∩
      {x | 0 ≤ s j * ((e j x) 1 - d j * Real.smoothMax (ε j) ((e j x) 0) 0)}
  let E := (B \ ⋃ j, e' j ⁻¹' ball (0 : Plane) (R' j)) ∪
    ⋃ j, (e' j ⁻¹' closedBall (0 : Plane) (R' j)) ∩
      {x | 0 ≤ s' j * ((e' j x) 1 - d' j * Real.smoothMax (ε' j) ((e' j x) 0) 0)}
  change IsCompact E at hE
  change H 1 '' D = E at himage
  have hcut (j : ι) : e j ⁻¹' closedBall (0 : Plane) (R j) ⊆ K := by
    obtain ⟨_, _, hUK, _, _, _, _, _, hKU, _⟩ := hA j
    exact hKU.trans (hUK.trans interior_subset)
  have hcut' (j : κ) : e' j ⁻¹' closedBall (0 : Plane) (R' j) ⊆ K := by
    obtain ⟨_, _, hUK, _, _, _, _, _, hKU, _⟩ := hB j
    exact hKU.trans (hUK.trans interior_subset)
  have hEaway (x : Plane) (hx : x ∉ K) : x ∈ E ↔ x ∈ B := by
    constructor
    · rintro (⟨hxB, _⟩ | hxR)
      · exact hxB
      · obtain ⟨j, hxj, _⟩ := mem_iUnion.mp hxR
        exact False.elim (hx (hcut' j hxj))
    · intro hxB
      refine Or.inl ⟨hxB, ?_⟩
      intro hxN
      obtain ⟨j, hxj⟩ := mem_iUnion.mp hxN
      exact hx (hcut' j ((preimage_mono (f := e' j) ball_subset_closedBall) hxj))
  have hDaway (x : Plane) (hx : x ∉ K) : x ∈ D ↔ x ∈ S := by
    constructor
    · rintro (⟨hxS, _⟩ | hxR)
      · exact hxS
      · obtain ⟨j, hxj, _⟩ := mem_iUnion.mp hxR
        exact False.elim (hx (hcut j hxj))
    · intro hxS
      refine Or.inl ⟨hxS, ?_⟩
      intro hxN
      obtain ⟨j, hxj⟩ := mem_iUnion.mp hxN
      exact hx (hcut j ((preimage_mono (f := e j) ball_subset_closedBall) hxj))
  have hold (x : Plane) (hx : x ∉ K) : x ∈ E ↔ x ∈ closure (inside Q.carrier) := by
    exact hEaway x hx
  obtain ⟨g, V, r, c, σ, A, θ, j, f, ρ, ℓ, A', η, Ψ, C, hnorm, hg, hVdisj, hstraight,
      hji, hjcover, hf, hcompact, hregular, hΨ, hΨi, hΨ0, hC, hCK, hfixΨ,
      hΨimage, hΨinter, hΨfront⟩ :=
    P.exists_relative_rounding_isotopy_with_reanchored_corners Q
      (D := E) (L := K) (W := W) (O := Kᶜ) hcar hE hK.isClosed hW hKW
      hK.isClosed.isOpen_compl (fun i hi h => hi (hKW h)) hold hgood
  let I := {i : ZMod (m + 3) // P.vertex i ∉ W ∧
    Plane.det (P.vertex (i - 1) - P.vertex i) (P.vertex (i + 1) - P.vertex i) ≠ 0}
  let J := {i : ZMod (n + 3) // Q.vertex i ∉ W}
  have hcutf i : f i ⁻¹' closedBall (0 : Plane) (A' i) ⊆ Kᶜ := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hAV, _⟩ := hf i
    exact fun _ hx => ((hg (j i)).2.2.1 (hAV hx)).1
  let D₀ := (E \ ⋃ i, g i ⁻¹' ball (0 : Plane) (A i)) ∪
    ⋃ i, (g i ⁻¹' closedBall (0 : Plane) (A i)) ∩
      {x | 0 ≤ σ i * ((g i x) 1 - c i * Real.smoothMax (θ i) ((g i x) 0) 0)}
  let D₁ := (E \ ⋃ i, f i ⁻¹' ball (0 : Plane) (A' i)) ∪
    ⋃ i, (f i ⁻¹' closedBall (0 : Plane) (A' i)) ∩
      {x | 0 ≤ σ (j i) * ((f i x) 1 - Real.smoothMax (ℓ i * η i) ((f i x) 0) 0)}
  let D₂ := (D \ ⋃ i, f i ⁻¹' ball (0 : Plane) (A' i)) ∪
    ⋃ i, (f i ⁻¹' closedBall (0 : Plane) (A' i)) ∩
      {x | 0 ≤ σ (j i) * ((f i x) 1 - Real.smoothMax (ℓ i * η i) ((f i x) 0) 0)}
  have hDE : (H 1).toHomeomorph '' D = E := himage
  have hHD : H 1 '' D₂ = D₁ := by
    have hh := (affine_corner_replacement_image_of_fixed_charts f
      (fun i => ℓ i * η i) A' (fun _ => 1) (fun i => σ (j i)) (H 1).toHomeomorph
      (D := D) hcutf (hfix 1).1).1
    rw [hDE] at hh
    simpa only [D₂, D₁, Diffeomorph.coe_toHomeomorph, one_mul] using hh
  have hΨimage' : Ψ 1 '' D₀ = D₁ := hΨimage
  have hΨinverse : (Ψ 1).symm '' D₁ = D₀ := by
    rw [← hΨimage']
    exact (Ψ 1).symm_image_image D₀
  have hΨi0 : (Ψ 0).symm = Diffeomorph.refl 𝓘(ℝ, Plane) Plane ∞ := by
    rw [hΨ0]
    rfl
  obtain ⟨Γ, hΓeq, hΓ, hΓi, hΓ0, hKC, hΓfix, hΓimage, hΓinter, hΓfront⟩ :=
    Diffeomorph.exists_compact_isotopy_image_trans H (fun t => (Ψ t).symm)
      hH hHi hH0 hK hfix hΨi
      (by
        change ContDiff ℝ ∞ (fun z : ℝ × Plane => Ψ z.1 z.2)
        exact hΨ) hΨi0 hC
      (fun t => by
        change EqOn (Ψ t).symm id Cᶜ ∧ EqOn (Ψ t) id Cᶜ
        exact (hfixΨ t).symm)
      hHD hΨinverse
  obtain ⟨vP, hvP⟩ := P.exists_corner_equiv_of_local_affine_graphs p hp U e d
    (S := W) (fun j => (hA j).1) (fun j => (hA j).2.1)
    (fun j => (hA j).2.2.2.1)
    (fun j x hx hz => by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, hcarrier, _⟩ := hA j
      exact (hcarrier x hx).mpr hz)
    (fun j _ => hKW (interior_subset ((hA j).2.2.1 (hA j).2.1)))
    (fun i hi hd => by
      obtain ⟨j, hij, hj⟩ := hPcover i hi hd
      exact ⟨j, hij, hj ▸ one_ne_zero⟩)
  obtain ⟨vQ, hvQ⟩ := Q.exists_corner_equiv_of_local_affine_graphs q
    hq U' e' d'
    (S := W) (fun j => (hB j).1) (fun j => (hB j).2.1)
    (fun j => (hB j).2.2.2.1)
    (fun j x hx hz => by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, hcarrier, _⟩ := hB j
      exact (hcarrier x hx).mpr hz)
    (fun j _ => hKW (interior_subset ((hB j).2.2.1 (hB j).2.1)))
    (fun i hi hd => by
      obtain ⟨j, hij, hj⟩ := hQcover i hi hd
      exact ⟨j, hij, hj ▸ one_ne_zero⟩)
  let pP : ZMod (m + 3) → Prop := fun i => P.vertex i ∈ W
  let cP : ZMod (m + 3) → Prop := fun i =>
    Plane.det (P.vertex (i - 1) - P.vertex i) (P.vertex (i + 1) - P.vertex i) ≠ 0
  let pQ : ZMod (n + 3) → Prop := fun i => Q.vertex i ∈ W
  let cQ : ZMod (n + 3) → Prop := fun i =>
    Plane.det (Q.vertex (i - 1) - Q.vertex i) (Q.vertex (i + 1) - Q.vertex i) ≠ 0
  let ePin : {i // pP i ∧ cP i} ≃ {i : {i // cP i} // pP i} :=
    (Equiv.subtypeEquivRight (fun _ => and_comm)).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter cP pP).symm
  let ePout : I ≃ {i : {i // cP i} // ¬pP i} :=
    (Equiv.subtypeEquivRight (fun _ => and_comm)).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter cP (fun i => ¬pP i)).symm
  let wP : ({j : ι // d j ≠ 0} ⊕ I) ≃ {i // cP i} :=
    (Equiv.sumCongr (vP.trans ePin) ePout).trans (Equiv.sumCompl (fun i : {i // cP i} => pP i))
  have hwP (z : {j : ι // d j ≠ 0} ⊕ I) :
      P.vertex (wP z) =
        Sum.elim (fun j : {j : ι // d j ≠ 0} => p j) (fun i : I => P.vertex i) z := by
    rcases z with j | i
    · change P.vertex (vP j) = p j
      exact hvP j
    · rfl
  let eQin : {i // pQ i ∧ cQ i} ≃ {i : {i // cQ i} // pQ i} :=
    (Equiv.subtypeEquivRight (fun _ => and_comm)).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter cQ pQ).symm
  let eQout₀ : {i : J // c i ≠ 0} ≃ {i : J // cQ i} :=
    Equiv.subtypeEquivRight fun i => not_congr (hstraight i)
  let eQout₁ : {i : J // cQ i} ≃ {i : {i // cQ i} // ¬pQ i} :=
    (Equiv.subtypeSubtypeEquivSubtypeInter (fun i => ¬pQ i) cQ).trans
      ((Equiv.subtypeEquivRight (fun _ => and_comm)).trans
        (Equiv.subtypeSubtypeEquivSubtypeInter cQ (fun i => ¬pQ i)).symm)
  let wQ : ({j : κ // d' j ≠ 0} ⊕ {i : J // c i ≠ 0}) ≃ {i // cQ i} :=
    (Equiv.sumCongr (vQ.trans eQin) (eQout₀.trans eQout₁)).trans
      (Equiv.sumCompl (fun i : {i // cQ i} => pQ i))
  have hwQ (z : {j : κ // d' j ≠ 0} ⊕ {i : J // c i ≠ 0}) :
      Q.vertex (wQ z) = Sum.elim (fun j : {j : κ // d' j ≠ 0} => q j)
        (fun i : {i : J // c i ≠ 0} => Q.vertex (i : J)) z := by
    rcases z with j | i
    · change Q.vertex (vQ j) = q j
      exact hvQ j
    · rfl
  have hd1 (j : {j : ι // d j ≠ 0}) : d j = 1 :=
    ((hA j).2.2.2.2.1).resolve_left j.property
  have hd1' (j : {j : κ // d' j ≠ 0}) : d' j = 1 :=
    ((hB j).2.2.2.2.1).resolve_left j.property
  have hc1 (i : {i : J // c i ≠ 0}) : c i = 1 :=
    ((hg i).2.2.2.1).resolve_left i.property
  have hDP : D = (S \ ⋃ j : {j : ι // d j ≠ 0}, e j ⁻¹' ball (0 : Plane) (R j)) ∪
      ⋃ j : {j : ι // d j ≠ 0}, (e j ⁻¹' closedBall (0 : Plane) (R j)) ∩
        {x | 0 ≤ s j * ((e j x) 1 - Real.smoothMax (ε j) ((e j x) 0) 0)} := by
    have hh := (affine_corner_replacement_eq_nonstraight S e ε R d s
      (fun i j hij => (hAdisj hij).mono
        (hA i).2.2.2.2.2.2.2.2.1 (hA j).2.2.2.2.2.2.2.2.1)
      (fun i _ x hx => (hA i).2.2.2.2.2.2.2.2.2.1 x
        ((hA i).2.2.2.2.2.2.2.2.1 hx))).1
    simpa only [hd1, one_mul] using hh
  have hEP : E = (B \ ⋃ j : {j : κ // d' j ≠ 0}, e' j ⁻¹' ball (0 : Plane) (R' j)) ∪
      ⋃ j : {j : κ // d' j ≠ 0}, (e' j ⁻¹' closedBall (0 : Plane) (R' j)) ∩
        {x | 0 ≤ s' j * ((e' j x) 1 - Real.smoothMax (ε' j) ((e' j x) 0) 0)} := by
    have hh := (affine_corner_replacement_eq_nonstraight B e' ε' R' d' s'
      (fun i j hij => (hBdisj hij).mono
        (hB i).2.2.2.2.2.2.2.2.1 (hB j).2.2.2.2.2.2.2.2.1)
      (fun i _ x hx => (hB i).2.2.2.2.2.2.2.2.2.1 x
        ((hB i).2.2.2.2.2.2.2.2.1 hx))).1
    simpa only [hd1', one_mul] using hh
  have hEQ : D₀ = (E \ ⋃ i : {i : J // c i ≠ 0}, g i ⁻¹' ball (0 : Plane) (A i)) ∪
      ⋃ i : {i : J // c i ≠ 0}, (g i ⁻¹' closedBall (0 : Plane) (A i)) ∩
        {x | 0 ≤ σ i * ((g i x) 1 - Real.smoothMax (θ i) ((g i x) 0) 0)} := by
    have hh := (affine_corner_replacement_eq_nonstraight E g θ A c σ
      (fun i j hij => (hVdisj hij).mono
        (hg i).2.2.2.2.2.2.2.1 (hg j).2.2.2.2.2.2.2.1)
      (fun i _ x hx => (hg i).2.2.2.2.2.2.2.2 x
        ((hg i).2.2.2.2.2.2.2.1 hx))).1
    simpa only [hc1, one_mul] using hh
  let XP := {j : ι // d j ≠ 0} ⊕ I
  let XQ := {j : κ // d' j ≠ 0} ⊕ {i : J // c i ≠ 0}
  let eP : XP → Plane ≃ᵃ[ℝ] Plane := Sum.elim (fun i => e i) f
  let UP : XP → Set Plane := Sum.elim (fun i => U i) (fun i => V (j i))
  let sP : XP → ℝ := Sum.elim (fun i => s i) (fun i => σ (j i))
  let εP : XP → ℝ := Sum.elim (fun i => ε i) (fun i => ℓ i * η i)
  let RP : XP → ℝ := Sum.elim (fun i => R i) A'
  let eQ : XQ → Plane ≃ᵃ[ℝ] Plane := Sum.elim (fun i => e' i) (fun i => g i)
  let UQ : XQ → Set Plane := Sum.elim (fun i => U' i) (fun i => V i)
  let sQ : XQ → ℝ := Sum.elim (fun i => s' i) (fun i => σ i)
  let εQ : XQ → ℝ := Sum.elim (fun i => ε' i) (fun i => θ i)
  let RQ : XQ → ℝ := Sum.elim (fun i => R' i) (fun i => A i)
  have hPsep : Disjoint
      (⋃ a : {j : ι // d j ≠ 0}, (e a ⁻¹' closedBall (0 : Plane) (R a)) ∩
        {x | 0 ≤ s a * ((e a x) 1 - Real.smoothMax (ε a) ((e a x) 0) 0)})
      (⋃ i : I, f i ⁻¹' ball (0 : Plane) (A' i)) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    obtain ⟨a, ha, _⟩ := mem_iUnion.mp hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hy
    exact hcutf i ((preimage_mono (f := f i) ball_subset_closedBall) hi) (hcut a ha)
  have hDsum : D₂ = (S \ ⋃ i, eP i ⁻¹' ball (0 : Plane) (RP i)) ∪
      ⋃ i, (eP i ⁻¹' closedBall (0 : Plane) (RP i)) ∩
        {x | 0 ≤ sP i * ((eP i x) 1 - Real.smoothMax (εP i) ((eP i x) 0) 0)} := by
    dsimp only [D₂]
    rw [hDP]
    simp only [XP, eP, RP, sP, εP, iUnion_sum, Sum.elim_inl, Sum.elim_inr]
    rw [union_sdiff_distrib, hPsep.sdiff_eq_left, Set.sdiff_sdiff, union_assoc]
  have hQsep : Disjoint
      (⋃ a : {j : κ // d' j ≠ 0}, (e' a ⁻¹' closedBall (0 : Plane) (R' a)) ∩
        {x | 0 ≤ s' a * ((e' a x) 1 - Real.smoothMax (ε' a) ((e' a x) 0) 0)})
      (⋃ i : {i : J // c i ≠ 0}, g i ⁻¹' ball (0 : Plane) (A i)) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    obtain ⟨a, ha, _⟩ := mem_iUnion.mp hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hy
    exact ((hg i).2.2.1 ((hg i).2.2.2.2.2.2.2.1
      ((preimage_mono (f := g i) ball_subset_closedBall) hi))).1 (hcut' a ha)
  have hEsum : D₀ = (B \ ⋃ i, eQ i ⁻¹' ball (0 : Plane) (RQ i)) ∪
      ⋃ i, (eQ i ⁻¹' closedBall (0 : Plane) (RQ i)) ∩
        {x | 0 ≤ sQ i * ((eQ i x) 1 - Real.smoothMax (εQ i) ((eQ i x) 0) 0)} := by
    rw [hEQ, hEP]
    simp only [XQ, eQ, RQ, sQ, εQ, iUnion_sum, Sum.elim_inl, Sum.elim_inr]
    rw [union_sdiff_distrib, hQsep.sdiff_eq_left, Set.sdiff_sdiff, union_assoc]
  have hSE (x : Plane) (hx : x ∉ K) : x ∈ S ↔ x ∈ E := by
    have hxfix : H 1 x = x := (hfix 1).1 hx
    constructor
    · intro hxS
      rw [← himage]
      exact ⟨x, (hDaway x hx).mpr hxS, hxfix⟩
    · intro hxE
      rw [← himage] at hxE
      obtain ⟨y, hy, hyx⟩ := hxE
      have hyx' : y = x := (H 1).injective (hyx.trans hxfix.symm)
      exact (hDaway x hx).mp (hyx' ▸ hy)
  have hPfamily (z : XP) : IsOpen (UP z) ∧ P.vertex (wP z) ∈ UP z ∧
      eP z (P.vertex (wP z)) = 0 ∧ (sP z = -1 ∨ sP z = 1) ∧
      0 < εP z ∧ 3 * εP z < RP z ∧ eP z ⁻¹' closedBall (0 : Plane) (RP z) ⊆ UP z ∧
      (∀ x ∈ UP z, x ∈ S ↔ 0 ≤ sP z * ((eP z x) 1 - max ((eP z x) 0) 0)) ∧
      ∃ r : ℝ, 0 < r ∧
        eP z (P.vertex ((wP z).val - 1)) = Plane.mk (-1) 0 ∧
        eP z (P.vertex ((wP z).val + 1)) = Plane.mk r r := by
    rcases z with a | i
    · obtain ⟨hU, haU, _, he, _, hs, hε, hR, hKU, hside, _, hv⟩ := hA a
      obtain ⟨v, r, hv, hr, hprev, hnext⟩ := hv (hd1 a)
      have hi : v = (wP (.inl a)).val := P.vertex_inj (hv.trans (hwP (.inl a)).symm)
      dsimp only [UP, eP, sP, εP, RP, Sum.elim_inl]
      refine ⟨hU, ?_, ?_, hs, hε, hR, hKU, ?_, r, hr, ?_, ?_⟩
      · rw [hwP (.inl a)]
        exact haU
      · rw [hwP (.inl a)]
        exact he
      · simpa only [hd1 a, one_mul] using hside
      · exact hi ▸ hprev
      · exact hi ▸ hnext
    · obtain ⟨hji', _, hr, hℓ, hη, _, _, hR, he, hprev, hnext, hKU, hside, _⟩ := hf i
      change IsOpen (V (j i)) ∧ P.vertex i ∈ V (j i) ∧
        f i (P.vertex i) = 0 ∧ (σ (j i) = -1 ∨ σ (j i) = 1) ∧
        0 < ℓ i * η i ∧ 3 * (ℓ i * η i) < A' i ∧
        f i ⁻¹' closedBall (0 : Plane) (A' i) ⊆ V (j i) ∧
        (∀ x ∈ V (j i), x ∈ S ↔ 0 ≤ σ (j i) * ((f i x) 1 - max ((f i x) 0) 0)) ∧
        ∃ r : ℝ, 0 < r ∧ f i (P.vertex (i.val - 1)) = Plane.mk (-1) 0 ∧
          f i (P.vertex (i.val + 1)) = Plane.mk r r
      refine ⟨(hg (j i)).1, hji' ▸ (hg (j i)).2.1, he,
        (hg (j i)).2.2.2.2.1, mul_pos hℓ hη, hR, hKU, ?_, ρ i, hr, hprev, hnext⟩
      intro x hx
      exact (hSE x ((hg (j i)).2.2.1 hx).1).trans (hside x hx)
  have hQfamily (z : XQ) : IsOpen (UQ z) ∧ Q.vertex (wQ z) ∈ UQ z ∧
      eQ z (Q.vertex (wQ z)) = 0 ∧ (sQ z = -1 ∨ sQ z = 1) ∧
      0 < εQ z ∧ 3 * εQ z < RQ z ∧ eQ z ⁻¹' closedBall (0 : Plane) (RQ z) ⊆ UQ z ∧
      (∀ x ∈ UQ z, x ∈ B ↔ 0 ≤ sQ z * ((eQ z x) 1 - max ((eQ z x) 0) 0)) ∧
      ∃ r : ℝ, 0 < r ∧
        eQ z (Q.vertex ((wQ z).val - 1)) = Plane.mk (-1) 0 ∧
        eQ z (Q.vertex ((wQ z).val + 1)) = Plane.mk r r := by
    rcases z with a | i
    · obtain ⟨hU, haU, _, he, _, hs, hε, hR, hKU, hside, _, hv⟩ := hB a
      obtain ⟨v, r, hv, hr, hprev, hnext⟩ := hv (hd1' a)
      have hi : v = (wQ (.inl a)).val := Q.vertex_inj (hv.trans (hwQ (.inl a)).symm)
      dsimp only [UQ, eQ, sQ, εQ, RQ, Sum.elim_inl]
      refine ⟨hU, ?_, ?_, hs, hε, hR, hKU, ?_, r, hr, ?_, ?_⟩
      · rw [hwQ (.inl a)]
        exact haU
      · rw [hwQ (.inl a)]
        exact he
      · simpa only [hd1' a, one_mul] using hside
      · exact hi ▸ hprev
      · exact hi ▸ hnext
    · obtain ⟨hr, he, hprev, hnext⟩ := hnorm i
      obtain ⟨hV, hiV, hVK, _, hs, hθ, hA, hKU, hside⟩ := hg i
      change IsOpen (V i) ∧ Q.vertex (i : J) ∈ V i ∧ g i (Q.vertex (i : J)) = 0 ∧
        (σ i = -1 ∨ σ i = 1) ∧ 0 < θ i ∧ 3 * θ i < A i ∧
        g i ⁻¹' closedBall (0 : Plane) (A i) ⊆ V i ∧
        (∀ x ∈ V i, x ∈ B ↔ 0 ≤ σ i * ((g i x) 1 - max ((g i x) 0) 0)) ∧
        ∃ r : ℝ, 0 < r ∧ g i (Q.vertex ((i : J).val - 1)) = Plane.mk (-1) 0 ∧
          g i (Q.vertex ((i : J).val + 1)) = Plane.mk r r
      refine ⟨hV, hiV, he, hs, hθ, hA, hKU, ?_, r i, hr, hprev, ?_⟩
      · intro x hx
        simpa only [hc1 i, one_mul] using
          (hEaway x (hVK hx).1).symm.trans (hside x hx)
      · simpa only [hc1 i, one_mul] using hnext
  have hUPdisj : Pairwise fun a p : XP => Disjoint (UP a) (UP p) := by
    intro a p hab
    rcases a with a | a <;> rcases p with p | p
    · exact hAdisj (fun h => hab (congrArg Sum.inl (Subtype.ext h)))
    · apply Set.disjoint_left.mpr
      intro x hx hy
      exact ((hg (j p)).2.2.1 hy).1 (interior_subset ((hA a).2.2.1 hx))
    · apply Set.disjoint_left.mpr
      intro x hx hy
      exact ((hg (j a)).2.2.1 hx).1 (interior_subset ((hA p).2.2.1 hy))
    · exact hVdisj (fun h => hab (congrArg Sum.inr (hji h)))
  have hUQdisj : Pairwise fun a p : XQ => Disjoint (UQ a) (UQ p) := by
    intro a p hab
    rcases a with a | a <;> rcases p with p | p
    · exact hBdisj (fun h => hab (congrArg Sum.inl (Subtype.ext h)))
    · apply Set.disjoint_left.mpr
      intro x hx hy
      exact ((hg p).2.2.1 hy).1 (interior_subset ((hB a).2.2.1 hx))
    · apply Set.disjoint_left.mpr
      intro x hx hy
      exact ((hg a).2.2.1 hx).1 (interior_subset ((hB p).2.2.1 hy))
    · exact hVdisj (fun h => hab (congrArg Sum.inr (Subtype.ext h)))
  have hDfull : D₂ = (S \ ⋃ i, eP (wP.symm i) ⁻¹' ball (0 : Plane) (RP (wP.symm i))) ∪
      ⋃ i, (eP (wP.symm i) ⁻¹' closedBall (0 : Plane) (RP (wP.symm i))) ∩
        {x | 0 ≤ sP (wP.symm i) * ((eP (wP.symm i) x) 1 -
          Real.smoothMax (εP (wP.symm i)) ((eP (wP.symm i) x) 0) 0)} := by
    rw [wP.symm.surjective.iUnion_comp (fun z => eP z ⁻¹' ball (0 : Plane) (RP z)),
      wP.symm.surjective.iUnion_comp (fun z =>
        (eP z ⁻¹' closedBall (0 : Plane) (RP z)) ∩
          {x | 0 ≤ sP z * ((eP z x) 1 - Real.smoothMax (εP z) ((eP z x) 0) 0)})]
    exact hDsum
  have hEfull : D₀ = (B \ ⋃ i, eQ (wQ.symm i) ⁻¹' ball (0 : Plane) (RQ (wQ.symm i))) ∪
      ⋃ i, (eQ (wQ.symm i) ⁻¹' closedBall (0 : Plane) (RQ (wQ.symm i))) ∩
        {x | 0 ≤ sQ (wQ.symm i) * ((eQ (wQ.symm i) x) 1 -
          Real.smoothMax (εQ (wQ.symm i)) ((eQ (wQ.symm i) x) 0) 0)} := by
    rw [wQ.symm.surjective.iUnion_comp (fun z => eQ z ⁻¹' ball (0 : Plane) (RQ z)),
      wQ.symm.surjective.iUnion_comp (fun z =>
        (eQ z ⁻¹' closedBall (0 : Plane) (RQ z)) ∩
          {x | 0 ≤ sQ z * ((eQ z x) 1 - Real.smoothMax (εQ z) ((eQ z x) 0) 0)})]
    exact hEsum
  refine ⟨fun i => eP (wP.symm i), fun i => UP (wP.symm i),
    fun i => sP (wP.symm i), fun i => εP (wP.symm i), fun i => RP (wP.symm i),
    fun i => eQ (wQ.symm i), fun i => UQ (wQ.symm i),
    fun i => sQ (wQ.symm i), fun i => εQ (wQ.symm i), fun i => RQ (wQ.symm i),
    Γ, K ∪ C, ?_, ?_, ?_, ?_, hΓ, hΓi, hΓ0, hKC, hΓfix, ?_⟩
  · intro i
    simpa only [wP.apply_symm_apply] using hPfamily (wP.symm i)
  · intro i k hik
    exact hUPdisj (fun h => hik (wP.symm.injective h))
  · intro i
    simpa only [wQ.apply_symm_apply] using hQfamily (wQ.symm i)
  · intro i k hik
    exact hUQdisj (fun h => hik (wQ.symm.injective h))
  · dsimp only
    rw [← hDfull, ← hEfull]
    exact ⟨hΓimage, hΓinter, hΓfront⟩

theorem PrePolygon.exists_corner_replacement_isotopy_of_geometrically_free_triangle
    {m : ℕ} (P : PrePolygon m)
    (M : LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh)
    (hfrontier : frontier M.toPlaneComplex.support = P.carrier)
    (T : M.Triangle) (hfree : M.IsGeometricallyFreeTriangle T) :
    ∃ (n : ℕ) (Q : PrePolygon n),
      Q.carrier = frontier (M.eraseTriangle T.1).toPlaneComplex.support ∧
      (M.eraseTriangle T.1).toPlaneComplex.support = closure (inside Q.carrier) ∧
    let I := {i : ZMod (m + 3) //
      Plane.det (P.vertex (i - 1) - P.vertex i) (P.vertex (i + 1) - P.vertex i) ≠ 0}
    let J := {i : ZMod (n + 3) //
      Plane.det (Q.vertex (i - 1) - Q.vertex i) (Q.vertex (i + 1) - Q.vertex i) ≠ 0}
    ∃ (g : I → Plane ≃ᵃ[ℝ] Plane) (V : I → Set Plane) (σ η A : I → ℝ)
      (g' : J → Plane ≃ᵃ[ℝ] Plane) (V' : J → Set Plane) (σ' η' A' : J → ℝ)
      (Φ : ℝ → Plane ≃ₘ[ℝ] Plane) (C : Set Plane),
      (∀ i, IsOpen (V i) ∧ P.vertex i ∈ V i ∧ g i (P.vertex i) = 0 ∧
        (σ i = -1 ∨ σ i = 1) ∧ 0 < η i ∧ 3 * η i < A i ∧
        g i ⁻¹' closedBall (0 : Plane) (A i) ⊆ V i ∧
        (∀ x ∈ V i, x ∈ closure (inside P.carrier) ↔
          0 ≤ σ i * ((g i x) 1 - max ((g i x) 0) 0)) ∧
        ∃ r : ℝ, 0 < r ∧ g i (P.vertex (i.val - 1)) = Plane.mk (-1) 0 ∧
          g i (P.vertex (i.val + 1)) = Plane.mk r r) ∧
      (Pairwise fun i j => Disjoint (V i) (V j)) ∧
      (∀ i, IsOpen (V' i) ∧ Q.vertex i ∈ V' i ∧ g' i (Q.vertex i) = 0 ∧
        (σ' i = -1 ∨ σ' i = 1) ∧ 0 < η' i ∧ 3 * η' i < A' i ∧
        g' i ⁻¹' closedBall (0 : Plane) (A' i) ⊆ V' i ∧
        (∀ x ∈ V' i, x ∈ closure (inside Q.carrier) ↔
          0 ≤ σ' i * ((g' i x) 1 - max ((g' i x) 0) 0)) ∧
        ∃ r : ℝ, 0 < r ∧ g' i (Q.vertex (i.val - 1)) = Plane.mk (-1) 0 ∧
          g' i (Q.vertex (i.val + 1)) = Plane.mk r r) ∧
      (Pairwise fun i j => Disjoint (V' i) (V' j)) ∧
      let D₀ := (closure (inside P.carrier) \ ⋃ i, g i ⁻¹' ball (0 : Plane) (A i)) ∪
        ⋃ i, (g i ⁻¹' closedBall (0 : Plane) (A i)) ∩
          {x | 0 ≤ σ i * ((g i x) 1 - Real.smoothMax (η i) ((g i x) 0) 0)}
      let D₁ := (closure (inside Q.carrier) \ ⋃ i, g' i ⁻¹' ball (0 : Plane) (A' i)) ∪
        ⋃ i, (g' i ⁻¹' closedBall (0 : Plane) (A' i)) ∩
          {x | 0 ≤ σ' i * ((g' i x) 1 - Real.smoothMax (η' i) ((g' i x) 0) 0)}
      ContDiff ℝ ∞ (fun z : ℝ × Plane => Φ z.1 z.2) ∧
      ContDiff ℝ ∞ (fun z : ℝ × Plane => (Φ z.1).symm z.2) ∧
      Φ 0 = Diffeomorph.refl 𝓘(ℝ, Plane) Plane ∞ ∧ IsCompact C ∧
      (∀ t, EqOn (Φ t) id Cᶜ ∧ EqOn (Φ t).symm id Cᶜ) ∧
      Φ 1 '' D₀ = D₁ ∧ Φ 1 '' interior D₀ = interior D₁ ∧
      Φ 1 '' frontier D₀ = frontier D₁ := by
  have hTsub : M.triangleCarrier T.1 ⊆ M.toPlaneComplex.support := by
    rw [M.toPlaneComplex_support]
    exact Set.subset_iUnion_of_subset T.1 (Set.subset_iUnion_of_subset T.2 Set.Subset.rfl)
  have hsupport : M.toPlaneComplex.support = closure (inside P.carrier) :=
    eq_closure_inside_of_isCompact_frontier_eq P.isSeparating_carrier
      M.toPlaneComplex.isCompact_support hfrontier
      ((M.interior_triangleCarrier_nonempty T).mono (interior_mono hTsub))
  obtain ⟨k, hfree | hfree⟩ := hfree
  · obtain ⟨n, Q, hQ, hregion, e, U, d, s, ε, R, e', U', d', s', ε', R', W, K, H,
        hW, hK, hKW, hA, hAdisj, hB, hBdisj, hPcover, hQcover, hcar,
        _, hE, hgood, hH, hHi, hH0, hfix, himage, _, _⟩ :=
      P.exists_local_corner_replacement_isotopy_of_one_edge_free_triangle M hfrontier T k hfree
    let b := LeanEval.Topology.ClassificationOfSurfaces.Moise.affineBasisOfTriangle
      (M.freeTriangleOrder T k) (M.freeTriangleOrder_affineIndependent T k)
    rw [hsupport] at hA himage
    rw [hregion] at hB hE hgood himage
    refine ⟨n, Q, hQ, hregion, ?_⟩
    exact P.exists_global_corner_replacement_isotopy Q
      (fun i : Fin 2 => b i.castSucc) (b.ind.injective.comp (Fin.castSucc_injective 2))
      b b.ind.injective e U d s ε R e' U' d' s' ε' R' W K H
      hW hK hKW hA hAdisj hB hBdisj hPcover hQcover hcar
      hE hgood hH hHi hH0 hfix himage
  · obtain ⟨n, Q, hQ, hregion, e, U, d, s, ε, R, e', U', d', s', ε', R', W, K, H,
        hW, hK, hKW, hA, hAdisj, hB, hBdisj, hPcover, hQcover, hcar,
        _, hE, hgood, hH, hHi, hH0, hfix, himage, _, _⟩ :=
      P.exists_local_corner_replacement_isotopy_of_two_edge_free_triangle M hfrontier T k hfree
    let b := LeanEval.Topology.ClassificationOfSurfaces.Moise.affineBasisOfTriangle
      (M.freeTriangleOrder T k) (M.freeTriangleOrder_affineIndependent T k)
    rw [hsupport] at hA himage
    rw [hregion] at hB hE hgood himage
    refine ⟨n, Q, hQ, hregion, ?_⟩
    exact P.exists_global_corner_replacement_isotopy Q b b.ind.injective
      (fun i : Fin 2 => b i.castSucc) (b.ind.injective.comp (Fin.castSucc_injective 2))
      e U d s ε R e' U' d' s' ε' R' W K H
      hW hK hKW hA hAdisj hB hBdisj hPcover hQcover hcar
      hE hgood hH hHi hH0 hfix himage

end Schoenflies

end
