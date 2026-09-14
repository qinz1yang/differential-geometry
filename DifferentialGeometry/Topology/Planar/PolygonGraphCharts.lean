import Mathlib.Order.Interval.Set.UnorderedInterval
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Module
import Mathlib.Tactic.Linarith
import Mathlib.Topology.MetricSpace.Thickening
import DifferentialGeometry.Analysis.Calculus.CompactCutoff
import Mathlib.Analysis.Calculus.ContDiff.Basic
import DifferentialGeometry.Analysis.Calculus.SmoothMax
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import DifferentialGeometry.External.ClassificationOfSurfaces.PrePolygonDeletion
import DifferentialGeometry.External.ClassificationOfSurfaces.Moise.LineSubdivision
import Mathlib.Analysis.Convex.Combination
import DifferentialGeometry.External.Schoenflies.Graph.K33Land
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Topology.Order.DenselyOrdered


namespace LeanEval.Topology.ClassificationOfSurfaces.Moise

private theorem TriangleMesh.one_edge_free_central_neighborhood
    (M : TriangleMesh) (T : M.Triangle) (k : Fin 3)
    (hfree : M.IsOneEdgeFreeTriangle T k) :
    let b := affineBasisOfTriangle (M.freeTriangleOrder T k)
      (M.freeTriangleOrder_affineIndependent T k)
    let N := (interior M.toPlaneComplex.support ∩ {p | 0 < b.coord 2 p}) ∪
      ((M.eraseTriangle T.1).toPlaneComplex.supportᶜ ∩
        {p | 0 < b.coord 0 p ∧ 0 < b.coord 1 p})
    IsOpen N ∧ M.triangleCarrier T.1 \ {b 0, b 1} ⊆ N ∧
      ∀ p ∈ N,
        (p ∈ M.toPlaneComplex.support ↔ 0 ≤ b.coord 2 p) ∧
        (p ∈ interior M.toPlaneComplex.support ↔ 0 < b.coord 2 p) ∧
        (p ∈ frontier M.toPlaneComplex.support ↔ b.coord 2 p = 0) := by
  dsimp only
  let b := affineBasisOfTriangle (M.freeTriangleOrder T k)
    (M.freeTriangleOrder_affineIndependent T k)
  let S := M.toPlaneComplex.support
  let B := (M.eraseTriangle T.1).toPlaneComplex.support
  let C := M.triangleCarrier T.1
  let N := (interior S ∩ {p | 0 < b.coord 2 p}) ∪
    (Bᶜ ∩ {p | 0 < b.coord 0 p ∧ 0 < b.coord 1 p})
  have hS : IsClosed S := M.toPlaneComplex.isCompact_support.isClosed
  have hB : IsClosed B := (M.eraseTriangle T.1).toPlaneComplex.isCompact_support.isClosed
  have hsplit : S = B ∪ C := M.support_eq_eraseTriangle_union_triangleCarrier T.2
  have hCS : C ⊆ S := by rw [hsplit]; exact Set.subset_union_right
  have htriangle : convexHull ℝ (Set.range b) = C := by
    change convexHull ℝ (Set.range ((M.position ∘ M.orderedVertex T) ∘ Equiv.swap 2 k)) = _
    rw [EquivLike.range_comp, Set.range_comp, M.range_orderedVertex T]
    rfl
  have hcoords : C = {p | ∀ i, 0 ≤ b.coord i p} :=
    htriangle.symm.trans b.convexHull_eq_nonneg_coord
  have hinterior : interior C = {p | ∀ i, 0 < b.coord i p} := by
    rw [← htriangle, b.interior_convexHull]
  have hfree' : frontier S ∩ C = segment ℝ (b 0) (b 1) := hfree
  have hattach : B ∩ C = segment ℝ (b 0) (b 2) ∪ segment ℝ (b 1) (b 2) :=
    M.eraseTriangle_support_inter_triangleCarrier_of_oneEdgeFree T k hfree
  have hN : IsOpen N :=
    (isOpen_interior.inter
      (isOpen_lt continuous_const (b.coord 2).continuous_of_finiteDimensional)).union
      (hB.isOpen_compl.inter
        ((isOpen_lt continuous_const (b.coord 0).continuous_of_finiteDimensional).inter
          (isOpen_lt continuous_const (b.coord 1).continuous_of_finiteDimensional)))
  have hcover : C \ {b 0, b 1} ⊆ N := by
    rintro p ⟨hpC, hpends⟩
    have hpcoord : ∀ i, 0 ≤ b.coord i p := by
      rw [hcoords] at hpC
      exact hpC
    by_cases hp2 : 0 < b.coord 2 p
    · refine Or.inl ⟨(mem_interior_iff_notMem_frontier (hCS hpC)).mpr ?_, hp2⟩
      intro hpF
      have hpbase := hfree' ▸ (show p ∈ frontier S ∩ C from ⟨hpF, hpC⟩)
      have hImage : b.coord 2 p ∈ (b.coord 2) '' segment ℝ (b 0) (b 1) :=
        ⟨p, hpbase, rfl⟩
      rw [image_segment] at hImage
      have hz : b.coord 2 p = 0 := by simpa [b.coord_apply, Fin.ext_iff] using hImage
      exact hp2.ne' hz
    · have hp2zero : b.coord 2 p = 0 := le_antisymm (le_of_not_gt hp2) (hpcoord 2)
      have hsum := b.sum_coord_apply_eq_one p
      simp only [Fin.sum_univ_three, hp2zero, add_zero] at hsum
      have hp0 : 0 < b.coord 0 p := by
        by_contra! h
        have hz : b.coord 0 p = 0 := le_antisymm h (hpcoord 0)
        have hp1 : b.coord 1 p = 1 := by linarith only [hsum, hz]
        have he : p = b 1 := by
          apply b.ext_elem
          intro i
          fin_cases i
          · exact hz.trans (b.coord_apply_ne (by decide : (0 : Fin 3) ≠ 1)).symm
          · exact hp1.trans (b.coord_apply_eq 1).symm
          · exact hp2zero.trans (b.coord_apply_ne (by decide : (2 : Fin 3) ≠ 1)).symm
        exact hpends (Or.inr he)
      have hp1 : 0 < b.coord 1 p := by
        by_contra! h
        have hz : b.coord 1 p = 0 := le_antisymm h (hpcoord 1)
        have hp0one : b.coord 0 p = 1 := by linarith only [hsum, hz]
        have he : p = b 0 := by
          apply b.ext_elem
          intro i
          fin_cases i
          · exact hp0one.trans (b.coord_apply_eq 0).symm
          · exact hz.trans (b.coord_apply_ne (by decide : (1 : Fin 3) ≠ 0)).symm
          · exact hp2zero.trans (b.coord_apply_ne (by decide : (2 : Fin 3) ≠ 0)).symm
        exact hpends (Or.inl he)
      refine Or.inr ⟨?_, hp0, hp1⟩
      intro hpB
      have hpA := hattach ▸ (show p ∈ B ∩ C from ⟨hpB, hpC⟩)
      rcases hpA with hpac | hpbc
      · have hImage : b.coord 1 p ∈ (b.coord 1) '' segment ℝ (b 0) (b 2) :=
          ⟨p, hpac, rfl⟩
        rw [image_segment] at hImage
        have hz : b.coord 1 p = 0 := by simpa [b.coord_apply, Fin.ext_iff] using hImage
        exact hp1.ne' hz
      · have hImage : b.coord 0 p ∈ (b.coord 0) '' segment ℝ (b 1) (b 2) :=
          ⟨p, hpbc, rfl⟩
        rw [image_segment] at hImage
        have hz : b.coord 0 p = 0 := by simpa [b.coord_apply, Fin.ext_iff] using hImage
        exact hp0.ne' hz
  refine ⟨hN, hcover, ?_⟩
  intro p hpN
  have hweak : p ∈ S ↔ 0 ≤ b.coord 2 p := by
    rcases hpN with hp | hp
    · exact iff_of_true (interior_subset hp.1) hp.2.le
    · constructor
      · intro hpS
        have hpC : p ∈ C := (hsplit ▸ hpS).resolve_left hp.1
        exact (hcoords ▸ hpC) 2
      · intro hp2
        apply hCS
        rw [hcoords]
        intro i
        fin_cases i
        · exact hp.2.1.le
        · exact hp.2.2.le
        · exact hp2
  have hstrict : p ∈ interior S ↔ 0 < b.coord 2 p := by
    rcases hpN with hp | hp
    · exact iff_of_true hp.1 hp.2
    · have hI : p ∈ interior S ↔ p ∈ interior C := by
        constructor
        · intro hpI
          have hpBC : p ∈ interior (B ∪ C) := hsplit ▸ hpI
          exact interior_union_inter_interior_compl_left_subset
            ⟨hpBC, hB.isOpen_compl.interior_eq.symm ▸ hp.1⟩
        · exact fun hpI => interior_mono hCS hpI
      rw [hI, hinterior]
      constructor
      · exact fun h => h 2
      · intro hp2 i
        fin_cases i
        · exact hp.2.1
        · exact hp.2.2
        · exact hp2
  refine ⟨hweak, hstrict, ?_⟩
  rw [hS.frontier_eq]
  change (p ∈ S ∧ p ∉ interior S) ↔ b.coord 2 p = 0
  rw [hweak, hstrict, not_lt]
  exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩

end LeanEval.Topology.ClassificationOfSurfaces.Moise


section

namespace Schoenflies

private theorem exists_ball_prePolygon_arc_eq_first_edge
    {m : ℕ} (P : PrePolygon m) (a : ZMod (m + 3)) {k : ℕ}
    (hk1 : 1 ≤ k) (hk2 : k ≤ m + 2) :
    ∃ r > 0, Metric.ball (P.vertex a) r ∩ P.arc a k =
      Metric.ball (P.vertex a) r ∩ P.edge a := by
  classical
  let s := Finset.Ioo 0 k
  let C : Set Plane := ⋃ t ∈ s, P.edge (a + (t : ZMod (m + 3)))
  have hC : IsClosed C :=
    (s.isCompact_biUnion (fun _ _ => isCompact_segment _ _)).isClosed
  have haC : P.vertex a ∉ C := by
    intro ha
    obtain ⟨t, ht, hat⟩ := Set.mem_iUnion₂.mp ha
    have ht1 : 0 < t := (Finset.mem_Ioo.mp ht).1
    have ht2 : t < k := (Finset.mem_Ioo.mp ht).2
    rcases PrePolygon.vertex_mem_edge_elim hat with he | he
    · have hzero : 0 = t := P.natCast_shift_inj a (by omega) (by omega)
        (by simpa only [Nat.cast_zero, add_zero] using he)
      omega
    · have hzero : 0 = t + 1 := P.natCast_shift_inj a (by omega) (by omega)
        (by simpa only [Nat.cast_zero, add_zero, Nat.cast_add, Nat.cast_one,
          add_assoc, Set.mem_singleton_iff] using he)
      omega
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hC.isOpen_compl (P.vertex a) haC
  refine ⟨r, hr, Set.Subset.antisymm ?_ ?_⟩
  · rintro p ⟨hpball, hparc⟩
    obtain ⟨t, ht, hpt⟩ := PrePolygon.mem_arc_iff.mp hparc
    refine ⟨hpball, ?_⟩
    rcases Nat.eq_zero_or_pos t with rfl | htpos
    · simpa only [Nat.cast_zero, add_zero] using hpt
    · exact False.elim (hball hpball
        (Set.mem_iUnion₂.mpr ⟨t, Finset.mem_Ioo.mpr ⟨htpos, ht⟩, hpt⟩))
  · rintro p ⟨hpball, hpedge⟩
    exact ⟨hpball, PrePolygon.mem_arc_iff.mpr
      ⟨0, hk1, by simpa only [Nat.cast_zero, add_zero] using hpedge⟩⟩

end Schoenflies
end
section

namespace Schoenflies

private theorem exists_affine_triangle_ray_separator
    (b : AffineBasis (Fin 3) ℝ Plane) {v : Plane} (hv : v ≠ b 0)
    {r : ℝ} (hr : 0 < r)
    (havoid : (Metric.ball (b 0) r ∩ segment ℝ (b 0) v) ∩
      convexHull ℝ (Set.range b) ⊆ {b 0}) :
    ∃ f : Plane →ᵃ[ℝ] ℝ, f (b 0) = 0 ∧ 0 < f (b 1) ∧ 0 < f (b 2) ∧ f v < 0 := by
  have hneg : b.coord 1 v < 0 ∨ b.coord 2 v < 0 := by
    by_contra! hnonneg
    let U : Set Plane := Metric.ball (b 0) r ∩ {p | 0 < b.coord 0 p}
    have hU : IsOpen U := Metric.isOpen_ball.inter
      (isOpen_lt continuous_const (b.coord 0).continuous_of_finiteDimensional)
    have hzero : (0 : ℝ) ∈ (AffineMap.lineMap (b 0) v) ⁻¹' U := by
      change AffineMap.lineMap (b 0) v 0 ∈ U
      rw [AffineMap.lineMap_apply_zero]
      refine ⟨Metric.mem_ball_self hr, ?_⟩
      change 0 < b.coord 0 (b 0)
      rw [b.coord_apply_eq]
      exact zero_lt_one
    obtain ⟨δ, hδ, hsmall⟩ := Metric.isOpen_iff.mp
      (hU.preimage AffineMap.lineMap_continuous) 0 hzero
    let t := min (δ / 2) (1 / 2)
    have ht : 0 < t := lt_min (half_pos hδ) (by norm_num)
    have ht1 : t ≤ 1 := (min_le_right _ _).trans (by norm_num)
    have htδ : t < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
    have hpU : AffineMap.lineMap (b 0) v t ∈ U := hsmall (by
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht] using htδ)
    have hpK : AffineMap.lineMap (b 0) v t ∈ convexHull ℝ (Set.range b) := by
      rw [b.convexHull_eq_nonneg_coord]
      intro i
      fin_cases i
      · exact hpU.2.le
      · change 0 ≤ b.coord 1 (AffineMap.lineMap (b 0) v t)
        rw [AffineMap.apply_lineMap, b.coord_apply_ne (by decide : (1 : Fin 3) ≠ 0),
          AffineMap.lineMap_apply_ring, mul_zero, zero_add]
        exact mul_nonneg ht.le hnonneg.1
      · change 0 ≤ b.coord 2 (AffineMap.lineMap (b 0) v t)
        rw [AffineMap.apply_lineMap, b.coord_apply_ne (by decide : (2 : Fin 3) ≠ 0),
          AffineMap.lineMap_apply_ring, mul_zero, zero_add]
        exact mul_nonneg ht.le hnonneg.2
    have hpzero : AffineMap.lineMap (b 0) v t = b 0 :=
      havoid ⟨⟨hpU.1, lineMap_mem_segment ℝ (b 0) v ⟨ht.le, ht1⟩⟩, hpK⟩
    rcases AffineMap.lineMap_eq_left_iff.mp hpzero with he | he
    · exact hv he.symm
    · exact ht.ne' he
  obtain ⟨α, β, hα, hβ, hsum⟩ : ∃ α β : ℝ, 0 < α ∧ 0 < β ∧
      α * b.coord 1 v + β * b.coord 2 v < 0 := by
    rcases hneg with h1 | h2
    · refine ⟨|b.coord 2 v| + 1, -b.coord 1 v, by positivity, neg_pos.mpr h1, ?_⟩
      have hpos : 0 < |b.coord 2 v| + 1 - b.coord 2 v := by
        linarith [le_abs_self (b.coord 2 v)]
      nlinarith [mul_neg_of_neg_of_pos h1 hpos]
    · refine ⟨-b.coord 2 v, |b.coord 1 v| + 1, neg_pos.mpr h2, by positivity, ?_⟩
      have hpos : 0 < |b.coord 1 v| + 1 - b.coord 1 v := by
        linarith [le_abs_self (b.coord 1 v)]
      nlinarith [mul_neg_of_neg_of_pos h2 hpos]
  refine ⟨α • b.coord 1 + β • b.coord 2, ?_, ?_, ?_, ?_⟩
  · simp [b.coord_apply]
  · simpa [b.coord_apply] using hα
  · simpa [b.coord_apply] using hβ
  · exact hsum

end Schoenflies
end
section

namespace Schoenflies

private theorem affine_triangle_map_apply_of_vertex_zero
    (b : AffineBasis (Fin 3) ℝ Plane) (f : Plane →ᵃ[ℝ] ℝ)
    (hf0 : f (b 0) = 0) (p : Plane) :
    f p = f (b 1) * b.coord 1 p + f (b 2) * b.coord 2 p := by
  have hf : f = f (b 1) • b.coord 1 + f (b 2) • b.coord 2 := by
    apply AffineMap.ext_on b.tot
    rintro q ⟨i, rfl⟩
    fin_cases i
    · simpa [b.coord_apply] using hf0
    · simp [b.coord_apply]
    · simp [b.coord_apply]
  exact congrArg (fun g : Plane →ᵃ[ℝ] ℝ => g p) hf

end Schoenflies
end
section

namespace LeanEval.Topology.ClassificationOfSurfaces.Moise

private theorem exists_affine_triangle_chart_with_first_coordinate
    (b : AffineBasis (Fin 3) ℝ Plane) (f : Plane →ᵃ[ℝ] ℝ)
    (hf0 : f (b 0) = 0) (hf1 : 0 < f (b 1)) :
    ∃ e : Plane ≃ᵃ[ℝ] Plane,
      (∀ p, (e p) 0 = f p) ∧
      e (b 0) = planePoint 0 0 ∧
      e (b 1) = planePoint (f (b 1)) 0 ∧
      e (b 2) = planePoint (f (b 2)) 1 := by
  let q : Fin 3 → Plane :=
    ![planePoint 0 0, planePoint (f (b 1)) 0, planePoint (f (b 2)) 1]
  have hq : AffineIndependent ℝ q := by
    apply affineIndependent_plane_triple_of_det_ne_zero
    simpa only [planePoint_apply_zero, planePoint_apply_one, PiLp.sub_apply,
      sub_zero, mul_one, mul_zero, zero_mul] using hf1.ne'
  let e := triangleAffineEquiv b q b.ind hq
  have he (i : Fin 3) : e (b i) = q i := triangleAffineEquiv_apply b q b.ind hq i
  have hx : cartesianX.comp e.toAffineMap = f := by
    apply AffineMap.ext_on b.tot
    rintro p ⟨i, rfl⟩
    change (e (b i)) 0 = f (b i)
    rw [he]
    fin_cases i
    · change 0 = f (b 0)
      exact hf0.symm
    · rfl
    · rfl
  refine ⟨e, ?_, he 0, he 1, he 2⟩
  intro p
  exact congrArg (fun g : Plane →ᵃ[ℝ] ℝ => g p) hx

end LeanEval.Topology.ClassificationOfSurfaces.Moise
end
section

namespace Schoenflies

private theorem exists_arc_start_triangle_separator {n : ℕ} (Q : PrePolygon n)
    (j : ZMod (n + 3)) {l : ℕ} (hl1 : 1 ≤ l) (hl2 : l ≤ n + 2)
    (b : AffineBasis (Fin 3) ℝ Plane) (ha : Q.vertex j = b 0)
    (hmeet : Q.arc j l ∩ convexHull ℝ (Set.range b) ⊆ {b 0, b 1}) :
    ∃ (v : Plane) (r : ℝ) (f : Plane →ᵃ[ℝ] ℝ),
      v ≠ b 0 ∧ 0 < r ∧ r < dist (b 0) (b 1) / 2 ∧
      segment ℝ (b 0) v ⊆ Q.arc j l ∧
      Metric.ball (b 0) r ∩ Q.arc j l = Metric.ball (b 0) r ∩ segment ℝ (b 0) v ∧
      f (b 0) = 0 ∧ 0 < f (b 1) ∧ 0 < f (b 2) ∧ f v < 0 := by
  obtain ⟨ρ, hρ, hgerm⟩ := exists_ball_prePolygon_arc_eq_first_edge Q j hl1 hl2
  have hab : b 0 ≠ b 1 := b.ind.injective.ne (by decide)
  have hd : 0 < dist (b 0) (b 1) := dist_pos.mpr hab
  let r := min ρ (dist (b 0) (b 1) / 3)
  have hr : 0 < r := lt_min hρ (by positivity)
  have hrhalf : r < dist (b 0) (b 1) / 2 :=
    (min_le_right _ _).trans_lt (by linarith)
  let v := Q.vertex (j + 1)
  have hv : v ≠ b 0 := fun he => Q.vertex_ne_succ j (ha.trans he.symm)
  have hseg : segment ℝ (b 0) v ⊆ Q.arc j l := by
    intro p hp
    apply PrePolygon.mem_arc_iff.mpr
    refine ⟨0, hl1, ?_⟩
    simpa only [Nat.cast_zero, add_zero, PrePolygon.edge, ha] using hp
  have hball : Metric.ball (b 0) r ⊆ Metric.ball (b 0) ρ :=
    Metric.ball_subset_ball (min_le_left _ _)
  have hgerm' : Metric.ball (b 0) r ∩ Q.arc j l =
      Metric.ball (b 0) r ∩ segment ℝ (b 0) v := by
    apply Set.Subset.antisymm
    · rintro p ⟨hp, hpR⟩
      refine ⟨hp, ?_⟩
      have heq : Metric.ball (b 0) ρ ∩ Q.arc j l =
          Metric.ball (b 0) ρ ∩ segment ℝ (b 0) v := by
        simpa only [PrePolygon.edge, ha] using hgerm
      exact (heq ▸ (show p ∈ Metric.ball (b 0) ρ ∩ Q.arc j l from ⟨hball hp, hpR⟩)).2
    · exact fun _ hp => ⟨hp.1, hseg hp.2⟩
  have havoid : (Metric.ball (b 0) r ∩ segment ℝ (b 0) v) ∩
      convexHull ℝ (Set.range b) ⊆ {b 0} := by
    rintro p ⟨⟨hp, hpseg⟩, hpK⟩
    rcases hmeet ⟨hseg hpseg, hpK⟩ with hpa | hpb
    · exact hpa
    · change p = b 1 at hpb
      have hpdist : dist (b 0) (b 1) < r := by
        rw [hpb] at hp
        simpa only [Metric.mem_ball, dist_comm] using hp
      exact False.elim (by linarith)
  obtain ⟨f, hf0, hf1, hf2, hfv⟩ := exists_affine_triangle_ray_separator b hv hr havoid
  exact ⟨v, r, f, hv, hr, hrhalf, hseg, hgerm', hf0, hf1, hf2, hfv⟩

private theorem exists_one_edge_free_two_endpoint_separators
    {m : ℕ} (P : PrePolygon m)
    (M : LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh)
    (hfrontier : frontier M.toPlaneComplex.support = P.carrier)
    (T : M.Triangle) (k : Fin 3) (hfree : M.IsOneEdgeFreeTriangle T k) :
    let b := LeanEval.Topology.ClassificationOfSurfaces.Moise.affineBasisOfTriangle
      (M.freeTriangleOrder T k) (M.freeTriangleOrder_affineIndependent T k)
    let R := closure (P.carrier \ segment ℝ (b 0) (b 1))
    ∃ (v₀ v₁ : Plane) (r₀ r₁ : ℝ) (f₀ f₁ : Plane →ᵃ[ℝ] ℝ),
      v₀ ≠ b 0 ∧ v₁ ≠ b 1 ∧ 0 < r₀ ∧ 0 < r₁ ∧
      Disjoint (Metric.ball (b 0) r₀) (Metric.ball (b 1) r₁) ∧
      segment ℝ (b 0) v₀ ⊆ R ∧ segment ℝ (b 1) v₁ ⊆ R ∧
      Metric.ball (b 0) r₀ ∩ R = Metric.ball (b 0) r₀ ∩ segment ℝ (b 0) v₀ ∧
      Metric.ball (b 1) r₁ ∩ R = Metric.ball (b 1) r₁ ∩ segment ℝ (b 1) v₁ ∧
      f₀ (b 0) = 0 ∧ 0 < f₀ (b 1) ∧ 0 < f₀ (b 2) ∧ f₀ v₀ < 0 ∧
      f₁ (b 1) = 0 ∧ 0 < f₁ (b 0) ∧ 0 < f₁ (b 2) ∧ f₁ v₁ < 0 := by
  dsimp only
  let b := LeanEval.Topology.ClassificationOfSurfaces.Moise.affineBasisOfTriangle
    (M.freeTriangleOrder T k) (M.freeTriangleOrder_affineIndependent T k)
  let R := closure (P.carrier \ segment ℝ (b 0) (b 1))
  let K := M.triangleCarrier T.1
  let B := (M.eraseTriangle T.1).toPlaneComplex.support
  obtain ⟨n, Q, j, l, hQ, _, hl1, hl2, hja, hjb, hR, hA, hattach⟩ :=
    P.exists_prePolygon_closed_region_erase_triangle_of_one_edge_free M hfrontier T k hfree
  change Q.vertex j = b 0 at hja
  change Q.vertex (j + (l : ZMod (n + 3))) = b 1 at hjb
  change Q.arc j l = R at hR
  change Q.arc (j + (l : ZMod (n + 3))) (n + 3 - l) =
    segment ℝ (b 0) (b 2) ∪ segment ℝ (b 1) (b 2) at hA
  change B ∩ K = segment ℝ (b 0) (b 2) ∪ segment ℝ (b 1) (b 2) at hattach
  have hK : convexHull ℝ (Set.range b) = K := by
    change convexHull ℝ (Set.range ((M.position ∘ M.orderedVertex T) ∘ Equiv.swap 2 k)) = _
    rw [EquivLike.range_comp, Set.range_comp, M.range_orderedVertex T]
    rfl
  have hRB : R ⊆ B := by
    rw [← hR]
    intro p hp
    apply (M.eraseTriangle T.1).toPlaneComplex.isCompact_support.isClosed.frontier_subset
    rw [← hQ]
    exact Q.arc_subset_carrier j l hp
  have hmeet : Q.arc j l ∩ convexHull ℝ (Set.range b) ⊆ {b 0, b 1} := by
    rintro p ⟨hpR, hpK⟩
    have hpA := hattach ▸ (show p ∈ B ∩ K from ⟨hRB (hR ▸ hpR), hK ▸ hpK⟩)
    have hp : p ∈ Q.arc j l ∩ Q.arc (j + (l : ZMod (n + 3))) (n + 3 - l) :=
      ⟨hpR, hA.symm ▸ hpA⟩
    simpa only [Q.arc_inter j hl1 hl2, hja, hjb] using hp
  obtain ⟨v₀, r₀, f₀, hv₀, hr₀, hsmall₀, hs₀, hg₀, hf₀, hfb, hfc₀, hfv₀⟩ :=
    exists_arc_start_triangle_separator Q j hl1 hl2 b hja hmeet
  let c := b.reindex (Equiv.swap (0 : Fin 3) 1)
  have hc0 : c 0 = b 1 := by simp [c]
  have hc1 : c 1 = b 0 := by simp [c]
  have hc2 : c 2 = b 2 := by simp [c, Equiv.swap_apply_def]
  have hcrange : Set.range c = Set.range b := by
    simp only [c, AffineBasis.coe_reindex, EquivLike.range_comp]
  have hrev : Q.reverse.arc (-j - (l : ZMod (n + 3))) l = Q.arc j l := Q.reverse_arc j l
  have hjrev : Q.reverse.vertex (-j - (l : ZMod (n + 3))) = c 0 := by
    rw [PrePolygon.reverse_vertex, show -(-j - (l : ZMod (n + 3))) =
      j + (l : ZMod (n + 3)) by ring, hjb, hc0]
  have hmeetrev : Q.reverse.arc (-j - (l : ZMod (n + 3))) l ∩
      convexHull ℝ (Set.range c) ⊆ {c 0, c 1} := by
    rw [hrev, hcrange, hc0, hc1, Set.pair_comm]
    exact hmeet
  obtain ⟨v₁, r₁, f₁, hv₁, hr₁, hsmall₁, hs₁, hg₁, hf₁, hfa, hfc₁, hfv₁⟩ :=
    exists_arc_start_triangle_separator Q.reverse (-j - (l : ZMod (n + 3)))
      hl1 hl2 c hjrev hmeetrev
  simp only [hc0, hc1, hc2] at hv₁ hsmall₁ hs₁ hg₁ hf₁ hfa hfc₁
  rw [dist_comm] at hsmall₁
  rw [hrev, hR] at hs₁ hg₁
  rw [hR] at hs₀ hg₀
  refine ⟨v₀, v₁, r₀, r₁, f₀, f₁, hv₀, hv₁, hr₀, hr₁, ?_,
    hs₀, hs₁, hg₀, hg₁, hf₀, hfb, hfc₀, hfv₀, hf₁, hfa, hfc₁, hfv₁⟩
  apply Set.disjoint_left.mpr
  intro p hp₀ hp₁
  have hp₀' : dist (b 0) p < r₀ := by simpa only [Metric.mem_ball, dist_comm] using hp₀
  have hp₁' : dist p (b 1) < r₁ := hp₁
  linarith [dist_triangle (b 0) p (b 1)]

end Schoenflies
end
section

namespace Schoenflies

private theorem triangle_nonneg_of_affine_vertex_nonneg
    (M : LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh)
    (T : M.Triangle) (b : AffineBasis (Fin 3) ℝ Plane)
    (htriangle : convexHull ℝ (Set.range b) = M.triangleCarrier T.1)
    (f : Plane →ᵃ[ℝ] ℝ) (hf : ∀ i, 0 ≤ f (b i)) :
    M.triangleCarrier T.1 ⊆ {p | 0 ≤ f p} := by
  rw [← htriangle]
  apply convexHull_min
  · rintro p ⟨i, rfl⟩
    exact hf i
  · exact (convex_Ici (0 : ℝ)).affine_preimage f

private theorem exists_one_edge_free_interior_survivor_near_endpoint
    (M : LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh)
    (T : M.Triangle) (b : AffineBasis (Fin 3) ℝ Plane)
    (htriangle : convexHull ℝ (Set.range b) = M.triangleCarrier T.1)
    (hfree : frontier M.toPlaneComplex.support ∩ M.triangleCarrier T.1 =
      segment ℝ (b 0) (b 1))
    (hattach : (M.eraseTriangle T.1).toPlaneComplex.support ∩ M.triangleCarrier T.1 =
      segment ℝ (b 0) (b 2) ∪ segment ℝ (b 1) (b 2))
    (f : Plane →ᵃ[ℝ] ℝ) (hf0 : f (b 0) = 0)
    (hf2 : 0 < f (b 2))
    {U : Set Plane} (hU : IsOpen U) (haU : b 0 ∈ U) :
    ∃ p ∈ U, p ∈ interior (M.eraseTriangle T.1).toPlaneComplex.support ∧
      0 < f p ∧ b.coord 1 p < 0 := by
  have hK : M.triangleCarrier T.1 ⊆ {p | 0 ≤ b.coord 1 p} :=
    triangle_nonneg_of_affine_vertex_nonneg M T b htriangle (b.coord 1) (by
      intro i
      change 0 ≤ b.coord 1 (b i)
      simp only [b.coord_apply]
      split_ifs <;> norm_num)
  have ha : (0 : ℝ) ∈ (AffineMap.lineMap (b 0) (b 2)) ⁻¹' U := by
    change AffineMap.lineMap (b 0) (b 2) 0 ∈ U
    rw [AffineMap.lineMap_apply_zero]
    exact haU
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp
    (hU.preimage AffineMap.lineMap_continuous) 0 ha
  let t := min (δ / 2) (1 / 2)
  have ht : 0 < t := lt_min (half_pos hδ) (by norm_num)
  have ht1 : t ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have htδ : t < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  let q := AffineMap.lineMap (b 0) (b 2) t
  have hqU : q ∈ U := hδU (by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht] using htδ)
  have hq1 : b.coord 1 q = 0 := by
    change b.coord 1 (AffineMap.lineMap (b 0) (b 2) t) = 0
    simp [AffineMap.apply_lineMap, b.coord_apply]
  have hq2 : b.coord 2 q = t := by
    change b.coord 2 (AffineMap.lineMap (b 0) (b 2) t) = t
    simp [AffineMap.apply_lineMap, b.coord_apply, AffineMap.lineMap_apply_ring]
  have hfq : 0 < f q := by
    change 0 < f (AffineMap.lineMap (b 0) (b 2) t)
    rw [AffineMap.apply_lineMap]
    rw [hf0, AffineMap.lineMap_apply_ring, mul_zero, zero_add]
    exact mul_pos ht hf2
  have hqBK : q ∈ (M.eraseTriangle T.1).toPlaneComplex.support ∩ M.triangleCarrier T.1 :=
    (hattach).symm ▸
      (Or.inl (lineMap_mem_segment ℝ (b 0) (b 2) ⟨ht.le, ht1⟩))
  have hqS : q ∈ interior M.toPlaneComplex.support := by
    apply (mem_interior_iff_notMem_frontier
      (M.eraseTriangle_support_subset T.1 hqBK.1)).mpr
    intro hqFrontier
    have hqBase : q ∈ segment ℝ (b 0) (b 1) := hfree ▸ ⟨hqFrontier, hqBK.2⟩
    have hqImage : b.coord 2 q ∈ (b.coord 2) '' segment ℝ (b 0) (b 1) :=
      ⟨q, hqBase, rfl⟩
    rw [image_segment] at hqImage
    have hzero : b.coord 2 q = 0 := by simpa [b.coord_apply] using hqImage
    exact ht.ne' (hq2.symm.trans hzero)
  let W := U ∩ interior M.toPlaneComplex.support ∩ {p | 0 < f p}
  have hW : IsOpen W := (hU.inter isOpen_interior).inter
    (isOpen_lt continuous_const f.continuous_of_finiteDimensional)
  have hqW : q ∈ W := ⟨⟨hqU, hqS⟩, hfq⟩
  have hq : (0 : ℝ) ∈ (AffineMap.lineMap q (b 1)) ⁻¹' W := by
    simpa only [Set.mem_preimage, AffineMap.lineMap_apply_zero] using hqW
  obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.mp
    (hW.preimage AffineMap.lineMap_continuous) 0 hq
  let p := AffineMap.lineMap q (b 1) (-(ε / 2))
  have hpW : p ∈ W := hεW (by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_neg,
      abs_of_pos (half_pos hε)] using half_lt_self hε)
  have hp1 : b.coord 1 p < 0 := by
    change b.coord 1 (AffineMap.lineMap q (b 1) (-(ε / 2))) < 0
    rw [AffineMap.apply_lineMap, hq1, b.coord_apply_eq,
      AffineMap.lineMap_apply_ring, mul_zero, zero_add, mul_one]
    exact neg_neg_of_pos (half_pos hε)
  have hV : IsOpen (interior M.toPlaneComplex.support ∩ {p | b.coord 1 p < 0}) :=
    isOpen_interior.inter
      (isOpen_lt (b.coord 1).continuous_of_finiteDimensional continuous_const)
  have hVB : interior M.toPlaneComplex.support ∩ {p | b.coord 1 p < 0} ⊆
      (M.eraseTriangle T.1).toPlaneComplex.support := by
    rintro x ⟨hxS, hxneg⟩
    have hx := interior_subset hxS
    rw [M.support_eq_eraseTriangle_union_triangleCarrier T.2] at hx
    rcases hx with hxB | hxK
    · exact hxB
    · have hxnonneg : 0 ≤ b.coord 1 x := hK hxK
      exact False.elim ((not_lt_of_ge hxnonneg) hxneg)
  exact ⟨p, hpW.1.1, (hV.subset_interior_iff.mpr hVB) ⟨hpW.1.2, hp1⟩, hpW.2, hp1⟩

private theorem subset_interior_of_isPreconnected_disjoint_frontier
    {X : Type*} [TopologicalSpace X] {A S : Set X}
    (hA : IsPreconnected A) (hS : IsClosed S) (hfrontier : Disjoint A (frontier S))
    (hpoint : (A ∩ interior S).Nonempty) : A ⊆ interior S := by
  apply hA.subset_left_of_subset_union isOpen_interior hS.isOpen_compl
    (Set.disjoint_left.mpr fun _ hpI hpC => hpC (interior_subset hpI)) _ hpoint
  intro p hpA
  by_cases hpS : p ∈ S
  · exact Or.inl ((mem_interior_iff_notMem_frontier hpS).mpr
      (Set.disjoint_left.mp hfrontier hpA))
  · exact Or.inr hpS

private theorem one_edge_free_positive_survivor_interior
    (M : LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh)
    (T : M.Triangle) (b : AffineBasis (Fin 3) ℝ Plane)
    (htriangle : convexHull ℝ (Set.range b) = M.triangleCarrier T.1)
    (hfree : frontier M.toPlaneComplex.support ∩ M.triangleCarrier T.1 =
      segment ℝ (b 0) (b 1))
    (hattach : (M.eraseTriangle T.1).toPlaneComplex.support ∩ M.triangleCarrier T.1 =
      segment ℝ (b 0) (b 2) ∪ segment ℝ (b 1) (b 2))
    (v : Plane) {r : ℝ} (hr : 0 < r) (f : Plane →ᵃ[ℝ] ℝ)
    (hf0 : f (b 0) = 0)
    (hf2 : 0 < f (b 2)) (hfv : f v < 0)
    (hfrontier : Metric.ball (b 0) r ∩
        frontier (M.eraseTriangle T.1).toPlaneComplex.support =
      Metric.ball (b 0) r ∩
        (segment ℝ (b 0) v ∪
          segment ℝ (b 0) (b 2))) :
    ∀ p ∈ Metric.ball (b 0) r,
      0 < f p → b.coord 1 p < 0 →
        p ∈ interior (M.eraseTriangle T.1).toPlaneComplex.support := by
  let A := (Metric.ball (b 0) r ∩ {p | 0 < f p}) ∩ {p | b.coord 1 p < 0}
  have hA : Convex ℝ A := ((convex_ball (b 0) r).inter
    ((convex_Ioi (0 : ℝ)).affine_preimage f)).inter
      ((convex_Iio (0 : ℝ)).affine_preimage (b.coord 1))
  have havoid : Disjoint A (frontier (M.eraseTriangle T.1).toPlaneComplex.support) := by
    apply Set.disjoint_left.mpr
    rintro p ⟨⟨hpball, hpf⟩, hpcoord⟩ hpF
    have hp : p ∈ Metric.ball (b 0) r ∩
        frontier (M.eraseTriangle T.1).toPlaneComplex.support := ⟨hpball, hpF⟩
    have hpgraph : p ∈ segment ℝ (b 0) v ∪ segment ℝ (b 0) (b 2) :=
      (hfrontier ▸ hp).2
    rcases hpgraph with hpv | hpc
    · have hseg := ((convex_Iic (0 : ℝ)).affine_preimage f).segment_subset hf0.le hfv.le
      have hnonpos : f p ≤ 0 := hseg hpv
      exact (not_lt_of_ge hnonpos) hpf
    · have hImage : b.coord 1 p ∈ (b.coord 1) '' segment ℝ (b 0) (b 2) :=
        ⟨p, hpc, rfl⟩
      rw [image_segment] at hImage
      have hzero : b.coord 1 p = 0 := by simpa [b.coord_apply] using hImage
      exact (show b.coord 1 p < 0 from hpcoord).ne hzero
  obtain ⟨q, hqball, hqB, hfq, hqcoord⟩ :=
    exists_one_edge_free_interior_survivor_near_endpoint M T b htriangle hfree hattach f hf0 hf2
      Metric.isOpen_ball (Metric.mem_ball_self hr)
  have hsub : A ⊆ interior (M.eraseTriangle T.1).toPlaneComplex.support :=
    subset_interior_of_isPreconnected_disjoint_frontier hA.isPreconnected
      (M.eraseTriangle T.1).toPlaneComplex.isCompact_support.isClosed havoid
      ⟨q, ⟨⟨hqball, hfq⟩, hqcoord⟩, hqB⟩
  exact fun p hp hpf hpcoord => hsub ⟨⟨hp, hpf⟩, hpcoord⟩

private theorem exists_triangle_interior_near_vertex_with_positive_affine
    (M : LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh)
    (T : M.Triangle) (b : AffineBasis (Fin 3) ℝ Plane)
    (htriangle : convexHull ℝ (Set.range b) = M.triangleCarrier T.1) (f : Plane →ᵃ[ℝ] ℝ)
    (hf0 : f (b 0) = 0)
    (hf2 : 0 < f (b 2))
    {U : Set Plane} (hU : IsOpen U) (haU : b 0 ∈ U) :
    ∃ p ∈ U, p ∈ interior (M.triangleCarrier T.1) ∧ 0 < f p ∧
      0 < b.coord 1 p ∧ p ∉ (M.eraseTriangle T.1).toPlaneComplex.support := by
  have hK : convexHull ℝ (Set.range b) = M.triangleCarrier T.1 := htriangle
  have hbK (i : Fin 3) : b i ∈ M.triangleCarrier T.1 :=
    hK ▸ subset_convexHull ℝ (Set.range b) ⟨i, rfl⟩
  have hpos : IsOpen {p | 0 < f p} :=
    isOpen_lt continuous_const f.continuous_of_finiteDimensional
  have hcClosure : b 2 ∈ closure (interior (M.triangleCarrier T.1)) := by
    rw [M.closure_interior_triangleCarrier T]
    exact hbK 2
  have hc : b 2 ∈ closure ({p | 0 < f p} ∩ interior (M.triangleCarrier T.1)) :=
    hpos.inter_closure ⟨hf2, hcClosure⟩
  obtain ⟨q, hfq, hqK⟩ := Set.Nonempty.of_closure ⟨b 2, hc⟩
  have ha : (0 : ℝ) ∈ (AffineMap.lineMap (b 0) q) ⁻¹' U := by
    change AffineMap.lineMap (b 0) q 0 ∈ U
    rw [AffineMap.lineMap_apply_zero]
    exact haU
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp
    (hU.preimage AffineMap.lineMap_continuous) 0 ha
  let t := min (δ / 2) (1 / 2)
  have ht : 0 < t := lt_min (half_pos hδ) (by norm_num)
  have ht1 : t < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have htδ : t < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  let p := AffineMap.lineMap (b 0) q t
  have hpU : p ∈ U := hδU (by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht] using htδ)
  have hconv : Convex ℝ (M.triangleCarrier T.1) := convex_convexHull ℝ _
  have hpK : p ∈ interior (M.triangleCarrier T.1) :=
    hconv.openSegment_self_interior_subset_interior (hbK 0) hqK
      (lineMap_mem_openSegment ℝ (b 0) q ⟨ht, ht1⟩)
  have hfp : 0 < f p := by
    change 0 < f (AffineMap.lineMap (b 0) q t)
    rw [AffineMap.apply_lineMap]
    rw [hf0, AffineMap.lineMap_apply_ring, mul_zero, zero_add]
    exact mul_pos ht hfq
  have hpcoord : 0 < b.coord 1 p := by
    have hpHull : p ∈ interior (convexHull ℝ (Set.range b)) := hK.symm ▸ hpK
    rw [b.interior_convexHull] at hpHull
    exact hpHull 1
  refine ⟨p, hpU, hpK, hfp, hpcoord, ?_⟩
  exact fun hpB => Set.disjoint_left.mp
    (M.disjoint_eraseTriangle_support_interior_triangleCarrier T) hpB hpK

private theorem subset_compl_of_isPreconnected_disjoint_frontier
    {X : Type*} [TopologicalSpace X] {A S : Set X}
    (hA : IsPreconnected A) (hS : IsClosed S) (hfrontier : Disjoint A (frontier S))
    (hpoint : (A ∩ Sᶜ).Nonempty) : A ⊆ Sᶜ := by
  intro p hpA hpS
  have hpI : p ∈ interior S := (mem_interior_iff_notMem_frontier hpS).mpr
    (Set.disjoint_left.mp hfrontier hpA)
  have hsub := subset_interior_of_isPreconnected_disjoint_frontier hA hS hfrontier
    ⟨p, hpA, hpI⟩
  obtain ⟨q, hqA, hqC⟩ := hpoint
  exact hqC (interior_subset (hsub hqA))

private theorem one_edge_free_positive_frontier_coord_eq_zero
    (M : LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh)
    (T : M.Triangle) (b : AffineBasis (Fin 3) ℝ Plane) (v : Plane) {r : ℝ} (f : Plane →ᵃ[ℝ] ℝ)
    (hf0 : f (b 0) = 0) (hfv : f v < 0)
    (hfrontier : Metric.ball (b 0) r ∩
        frontier (M.eraseTriangle T.1).toPlaneComplex.support =
      Metric.ball (b 0) r ∩
        (segment ℝ (b 0) v ∪
          segment ℝ (b 0) (b 2))) :
    ∀ p ∈ Metric.ball (b 0) r, 0 < f p →
      p ∈ frontier (M.eraseTriangle T.1).toPlaneComplex.support → b.coord 1 p = 0 := by
  intro p hpball hpf hpF
  have hp : p ∈ Metric.ball (b 0) r ∩
      frontier (M.eraseTriangle T.1).toPlaneComplex.support := ⟨hpball, hpF⟩
  have hpgraph : p ∈ segment ℝ (b 0) v ∪ segment ℝ (b 0) (b 2) :=
    (hfrontier ▸ hp).2
  rcases hpgraph with hpv | hpc
  · have hseg := ((convex_Iic (0 : ℝ)).affine_preimage f).segment_subset hf0.le hfv.le
    have hnonpos : f p ≤ 0 := hseg hpv
    exact False.elim ((not_lt_of_ge hnonpos) hpf)
  · have hImage : b.coord 1 p ∈ (b.coord 1) '' segment ℝ (b 0) (b 2) := ⟨p, hpc, rfl⟩
    rw [image_segment] at hImage
    simpa [b.coord_apply] using hImage

private theorem one_edge_free_positive_survivor_compl
    (M : LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh)
    (T : M.Triangle) (b : AffineBasis (Fin 3) ℝ Plane)
    (htriangle : convexHull ℝ (Set.range b) = M.triangleCarrier T.1)
    (v : Plane) {r : ℝ} (hr : 0 < r)
    (f : Plane →ᵃ[ℝ] ℝ) (hf0 : f (b 0) = 0)
    (hf2 : 0 < f (b 2)) (hfv : f v < 0)
    (hfrontier : Metric.ball (b 0) r ∩
        frontier (M.eraseTriangle T.1).toPlaneComplex.support =
      Metric.ball (b 0) r ∩
        (segment ℝ (b 0) v ∪
          segment ℝ (b 0) (b 2))) :
    ∀ p ∈ Metric.ball (b 0) r,
      0 < f p → 0 < b.coord 1 p → p ∉ (M.eraseTriangle T.1).toPlaneComplex.support := by
  let A := (Metric.ball (b 0) r ∩ {p | 0 < f p}) ∩ {p | 0 < b.coord 1 p}
  have hA : Convex ℝ A := ((convex_ball (b 0) r).inter
    ((convex_Ioi (0 : ℝ)).affine_preimage f)).inter
      ((convex_Ioi (0 : ℝ)).affine_preimage (b.coord 1))
  have havoid : Disjoint A (frontier (M.eraseTriangle T.1).toPlaneComplex.support) := by
    apply Set.disjoint_left.mpr
    rintro p ⟨⟨hpball, hpf⟩, hpcoord⟩ hpF
    have hzero := one_edge_free_positive_frontier_coord_eq_zero M T b v f hf0 hfv
      hfrontier p hpball hpf hpF
    exact (show 0 < b.coord 1 p from hpcoord).ne' hzero
  obtain ⟨q, hqball, _, hfq, hqcoord, hqB⟩ :=
    exists_triangle_interior_near_vertex_with_positive_affine M T b htriangle f hf0 hf2
      Metric.isOpen_ball (Metric.mem_ball_self hr)
  have hsub : A ⊆ ((M.eraseTriangle T.1).toPlaneComplex.support)ᶜ :=
    subset_compl_of_isPreconnected_disjoint_frontier hA.isPreconnected
      (M.eraseTriangle T.1).toPlaneComplex.isCompact_support.isClosed havoid
      ⟨q, ⟨⟨hqball, hfq⟩, hqcoord⟩, hqB⟩
  exact fun p hp hpf hpcoord => hsub ⟨⟨hp, hpf⟩, hpcoord⟩

private theorem mem_closure_inter_pos_of_affine_zero
    (f : Plane →ᵃ[ℝ] ℝ) (v : Plane) (hfv : 0 < f v)
    {U : Set Plane} (hU : IsOpen U) {p : Plane} (hpU : p ∈ U) (hfp : f p = 0) :
    p ∈ closure (U ∩ {q | 0 < f q}) := by
  have hzero : (0 : ℝ) ∈ closure (Set.Ioi (0 : ℝ)) := by
    rw [closure_Ioi]
    exact (show (0 : ℝ) ≤ 0 from le_rfl)
  have hpImage : p ∈ closure ((AffineMap.lineMap p v) '' Set.Ioi (0 : ℝ)) := by
    have h := mem_closure_image (f := AffineMap.lineMap p v)
      AffineMap.lineMap_continuous.continuousAt hzero
    simpa only [AffineMap.lineMap_apply_zero] using h
  have hsub : (AffineMap.lineMap p v) '' Set.Ioi (0 : ℝ) ⊆ {q | 0 < f q} := by
    rintro q ⟨t, ht, rfl⟩
    change 0 < f (AffineMap.lineMap p v t)
    rw [AffineMap.apply_lineMap, hfp, AffineMap.lineMap_apply_ring, mul_zero, zero_add]
    exact mul_pos ht hfv
  exact hU.inter_closure ⟨hpU, closure_mono hsub hpImage⟩

private theorem eq_left_of_mem_segment_of_affine_zero
    (f : Plane →ᵃ[ℝ] ℝ) (a v : Plane) (hfa : f a = 0) (hfv : f v ≠ 0)
    {p : Plane} (hp : p ∈ segment ℝ a v) (hfp : f p = 0) : p = a := by
  rw [segment_eq_image_lineMap] at hp
  obtain ⟨t, _, rfl⟩ := hp
  rw [AffineMap.apply_lineMap, hfa, AffineMap.lineMap_apply_ring,
    mul_zero, zero_add] at hfp
  have ht : t = 0 := (mul_eq_zero.mp hfp).resolve_right hfv
  rw [ht, AffineMap.lineMap_apply_zero]

private theorem one_edge_free_transverse_frontier_eq_endpoint
    (M : LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh)
    (T : M.Triangle) (b : AffineBasis (Fin 3) ℝ Plane) (v : Plane) {r : ℝ} (f : Plane →ᵃ[ℝ] ℝ)
    (hf0 : f (b 0) = 0)
    (hf2 : f (b 2) ≠ 0) (hfv : f v ≠ 0)
    (hfrontier : Metric.ball (b 0) r ∩
        frontier (M.eraseTriangle T.1).toPlaneComplex.support =
      Metric.ball (b 0) r ∩
        (segment ℝ (b 0) v ∪
          segment ℝ (b 0) (b 2))) :
    ∀ p ∈ Metric.ball (b 0) r, f p = 0 →
      p ∈ frontier (M.eraseTriangle T.1).toPlaneComplex.support →
        p = b 0 := by
  intro p hpball hfp hpF
  have hp : p ∈ Metric.ball (b 0) r ∩
      frontier (M.eraseTriangle T.1).toPlaneComplex.support := ⟨hpball, hpF⟩
  rcases (hfrontier ▸ hp).2 with hpv | hpc
  · exact eq_left_of_mem_segment_of_affine_zero f _ v hf0 hfv hpv hfp
  · exact eq_left_of_mem_segment_of_affine_zero f _ _ hf0 hf2 hpc hfp

private theorem one_edge_free_transverse_survivor_sides
    (M : LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh)
    (T : M.Triangle) (b : AffineBasis (Fin 3) ℝ Plane)
    (htriangle : convexHull ℝ (Set.range b) = M.triangleCarrier T.1)
    (hfree : frontier M.toPlaneComplex.support ∩ M.triangleCarrier T.1 =
      segment ℝ (b 0) (b 1))
    (hattach : (M.eraseTriangle T.1).toPlaneComplex.support ∩ M.triangleCarrier T.1 =
      segment ℝ (b 0) (b 2) ∪ segment ℝ (b 1) (b 2))
    (v : Plane) {r : ℝ} (hr : 0 < r) (f : Plane →ᵃ[ℝ] ℝ)
    (hf0 : f (b 0) = 0)
    (hf1 : 0 < f (b 1))
    (hf2 : 0 < f (b 2)) (hfv : f v < 0)
    (hfrontier : Metric.ball (b 0) r ∩
        frontier (M.eraseTriangle T.1).toPlaneComplex.support =
      Metric.ball (b 0) r ∩
        (segment ℝ (b 0) v ∪
          segment ℝ (b 0) (b 2))) :
    ∀ p ∈ Metric.ball (b 0) r, f p = 0 →
      (b.coord 1 p < 0 → p ∈ interior (M.eraseTriangle T.1).toPlaneComplex.support) ∧
      (0 < b.coord 1 p → p ∉ (M.eraseTriangle T.1).toPlaneComplex.support) := by
  let B := (M.eraseTriangle T.1).toPlaneComplex.support
  have hB : IsClosed B := (M.eraseTriangle T.1).toPlaneComplex.isCompact_support.isClosed
  intro p hpball hfp
  have hnotF (hne : b.coord 1 p ≠ 0) : p ∉ frontier B := by
    intro hpF
    have hp := one_edge_free_transverse_frontier_eq_endpoint M T b v f hf0 hf2.ne'
      hfv.ne hfrontier p hpball hfp hpF
    apply hne
    rw [hp]
    exact b.coord_apply_ne (by decide)
  constructor
  · intro hpneg
    let U := Metric.ball (b 0) r ∩ {q | b.coord 1 q < 0}
    have hU : IsOpen U := Metric.isOpen_ball.inter
      (isOpen_lt (b.coord 1).continuous_of_finiteDimensional continuous_const)
    have hpClosure := mem_closure_inter_pos_of_affine_zero f (b 1) hf1 hU
      (show p ∈ U from ⟨hpball, hpneg⟩) hfp
    have hsub : U ∩ {q | 0 < f q} ⊆ B := by
      rintro q ⟨⟨hqball, hqneg⟩, hfq⟩
      exact interior_subset (one_edge_free_positive_survivor_interior M T b htriangle hfree hattach
        v hr f
        hf0 hf2 hfv hfrontier q hqball hfq hqneg)
    have hpB : p ∈ B := closure_minimal hsub hB hpClosure
    exact (mem_interior_iff_notMem_frontier hpB).mpr (hnotF hpneg.ne)
  · intro hppos hpB
    let U := Metric.ball (b 0) r ∩ {q | 0 < b.coord 1 q}
    have hU : IsOpen U := Metric.isOpen_ball.inter
      (isOpen_lt continuous_const (b.coord 1).continuous_of_finiteDimensional)
    have hpClosure := mem_closure_inter_pos_of_affine_zero f (b 1) hf1 hU
      (show p ∈ U from ⟨hpball, hppos⟩) hfp
    have hsub : U ∩ {q | 0 < f q} ⊆ Bᶜ := by
      rintro q ⟨⟨hqball, hqpos⟩, hfq⟩
      exact one_edge_free_positive_survivor_compl M T b htriangle v hr f hf0 hf2 hfv hfrontier
        q hqball hfq hqpos
    apply hnotF hppos.ne'
    rw [frontier_eq_closure_inter_closure]
    exact ⟨subset_closure hpB, closure_mono hsub hpClosure⟩

private theorem exists_affine_triangle_transverse_points_in_open
    (b : AffineBasis (Fin 3) ℝ Plane) (f : Plane →ᵃ[ℝ] ℝ)
    (hf0 : f (b 0) = 0) (hf1 : 0 < f (b 1)) (hf2 : 0 < f (b 2))
    {U : Set Plane} (hU : IsOpen U) (haU : b 0 ∈ U) :
    ∃ p q, p ∈ U ∧ q ∈ U ∧ f p = 0 ∧ f q = 0 ∧
      b.coord 1 p < 0 ∧ 0 < b.coord 2 p ∧ 0 < b.coord 1 q ∧ b.coord 2 q < 0 := by
  let w : Fin 3 → ℝ := ![1 + f (b 2) - f (b 1), -f (b 2), f (b 1)]
  have hw : ∑ i, w i = 1 := by
    simp only [Fin.sum_univ_three]
    dsimp [w]
    ring
  let z := Finset.univ.affineCombination ℝ b w
  have hzcoord (i : Fin 3) : b.coord i z = w i :=
    b.coord_apply_combination_of_mem (Finset.mem_univ i) hw
  have hz1 : b.coord 1 z = -f (b 2) := hzcoord 1
  have hz2 : b.coord 2 z = f (b 1) := hzcoord 2
  have hfz : f z = 0 := by
    change f (Finset.univ.affineCombination ℝ b w) = 0
    rw [Finset.map_affineCombination Finset.univ b w hw f,
      Finset.affineCombination_eq_linear_combination _ _ _ hw]
    simp only [Fin.sum_univ_three, Function.comp_apply, smul_eq_mul]
    change (1 + f (b 2) - f (b 1)) * f (b 0) +
      -f (b 2) * f (b 1) + f (b 1) * f (b 2) = 0
    rw [hf0]
    ring
  have hzero : (0 : ℝ) ∈ (AffineMap.lineMap (b 0) z) ⁻¹' U := by
    simpa only [Set.mem_preimage, AffineMap.lineMap_apply_zero] using haU
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp
    (hU.preimage AffineMap.lineMap_continuous) 0 hzero
  let t := δ / 2
  have ht : 0 < t := half_pos hδ
  have hplus : AffineMap.lineMap (b 0) z t ∈ U := hδU (by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht] using half_lt_self hδ)
  have hminus : AffineMap.lineMap (b 0) z (-t) ∈ U := hδU (by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_neg,
      abs_of_pos ht] using half_lt_self hδ)
  have hvalue (s : ℝ) :
      b.coord 1 (AffineMap.lineMap (b 0) z s) = -s * f (b 2) ∧
      b.coord 2 (AffineMap.lineMap (b 0) z s) = s * f (b 1) := by
    constructor
    · rw [AffineMap.apply_lineMap, b.coord_apply_ne (by decide : (1 : Fin 3) ≠ 0),
        hz1, AffineMap.lineMap_apply_ring]
      ring
    · rw [AffineMap.apply_lineMap, b.coord_apply_ne (by decide : (2 : Fin 3) ≠ 0),
        hz2, AffineMap.lineMap_apply_ring]
      ring
  have hfvalue (s : ℝ) : f (AffineMap.lineMap (b 0) z s) = 0 := by
    rw [AffineMap.apply_lineMap, hf0, hfz]
    simp
  refine ⟨AffineMap.lineMap (b 0) z t, AffineMap.lineMap (b 0) z (-t),
    hplus, hminus, hfvalue t, hfvalue (-t), ?_, ?_, ?_, ?_⟩
  · rw [(hvalue t).1]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos ht) hf2
  · rw [(hvalue t).2]
    exact mul_pos ht hf1
  · rw [(hvalue (-t)).1, neg_neg]
    exact mul_pos ht hf2
  · rw [(hvalue (-t)).2]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos ht) hf1

private theorem exists_one_edge_free_negative_retained_side_points
    (M : LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh)
    (T : M.Triangle) (b : AffineBasis (Fin 3) ℝ Plane)
    (htriangle : convexHull ℝ (Set.range b) = M.triangleCarrier T.1)
    (hfree : frontier M.toPlaneComplex.support ∩ M.triangleCarrier T.1 =
      segment ℝ (b 0) (b 1))
    (hattach : (M.eraseTriangle T.1).toPlaneComplex.support ∩ M.triangleCarrier T.1 =
      segment ℝ (b 0) (b 2) ∪ segment ℝ (b 1) (b 2))
    (v : Plane) {r : ℝ} (hr : 0 < r) (f : Plane →ᵃ[ℝ] ℝ)
    (hf0 : f (b 0) = 0)
    (hf1 : 0 < f (b 1))
    (hf2 : 0 < f (b 2)) (hfv : f v < 0)
    (hfrontier : Metric.ball (b 0) r ∩
        frontier (M.eraseTriangle T.1).toPlaneComplex.support =
      Metric.ball (b 0) r ∩
        (segment ℝ (b 0) v ∪
          segment ℝ (b 0) (b 2))) :
    let g := (-f v) • b.coord 2 + b.coord 2 v • f
    (∃ p ∈ Metric.ball (b 0) r, f p < 0 ∧ 0 < g p ∧
      p ∈ interior (M.eraseTriangle T.1).toPlaneComplex.support) ∧
    (∃ p ∈ Metric.ball (b 0) r, f p < 0 ∧ g p < 0 ∧
      p ∉ (M.eraseTriangle T.1).toPlaneComplex.support) := by
  dsimp only
  let g := (-f v) • b.coord 2 + b.coord 2 v • f
  let B := (M.eraseTriangle T.1).toPlaneComplex.support
  obtain ⟨p, q, hpball, hqball, hfp, hfq, hp1, hp2, hq1, hq2⟩ :=
    exists_affine_triangle_transverse_points_in_open b f hf0 hf1 hf2
      Metric.isOpen_ball (Metric.mem_ball_self hr)
  have hpB : p ∈ interior B :=
    (one_edge_free_transverse_survivor_sides M T b htriangle hfree hattach
      v hr f hf0 hf1 hf2 hfv hfrontier
      p hpball hfp).1 hp1
  have hqB : q ∉ B :=
    (one_edge_free_transverse_survivor_sides M T b htriangle hfree hattach
      v hr f hf0 hf1 hf2 hfv hfrontier
      q hqball hfq).2 hq1
  have hgp : 0 < g p := by
    change 0 < (-f v) * b.coord 2 p + b.coord 2 v * f p
    rw [hfp, mul_zero, add_zero]
    exact mul_pos (neg_pos.mpr hfv) hp2
  have hgq : g q < 0 := by
    change (-f v) * b.coord 2 q + b.coord 2 v * f q < 0
    rw [hfq, mul_zero, add_zero]
    exact mul_neg_of_pos_of_neg (neg_pos.mpr hfv) hq2
  constructor
  · let U := (Metric.ball (b 0) r ∩ {x | 0 < g x}) ∩ interior B
    have hU : IsOpen U := (Metric.isOpen_ball.inter
      (isOpen_lt continuous_const g.continuous_of_finiteDimensional)).inter isOpen_interior
    have hp : p ∈ closure (U ∩ {x | 0 < (-f) x}) :=
      mem_closure_inter_pos_of_affine_zero (-f) v (neg_pos.mpr hfv) hU
        (show p ∈ U from ⟨⟨hpball, hgp⟩, hpB⟩) (by change -f p = 0; rw [hfp, neg_zero])
    obtain ⟨x, hxU, hxf⟩ := Set.Nonempty.of_closure ⟨p, hp⟩
    exact ⟨x, hxU.1.1, neg_pos.mp hxf, hxU.1.2, hxU.2⟩
  · let U := (Metric.ball (b 0) r ∩ {x | g x < 0}) ∩ Bᶜ
    have hU : IsOpen U := (Metric.isOpen_ball.inter
      (isOpen_lt g.continuous_of_finiteDimensional continuous_const)).inter
        (M.eraseTriangle T.1).toPlaneComplex.isCompact_support.isClosed.isOpen_compl
    have hq : q ∈ closure (U ∩ {x | 0 < (-f) x}) :=
      mem_closure_inter_pos_of_affine_zero (-f) v (neg_pos.mpr hfv) hU
        (show q ∈ U from ⟨⟨hqball, hgq⟩, hqB⟩) (by change -f q = 0; rw [hfq, neg_zero])
    obtain ⟨x, hxU, hxf⟩ := Set.Nonempty.of_closure ⟨q, hq⟩
    exact ⟨x, hxU.1.1, neg_pos.mp hxf, hxU.1.2, hxU.2⟩

private theorem one_edge_free_negative_frontier_retained_coord_eq_zero
    (M : LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh)
    (T : M.Triangle) (b : AffineBasis (Fin 3) ℝ Plane) (v : Plane) {r : ℝ} (f : Plane →ᵃ[ℝ] ℝ)
    (hf0 : f (b 0) = 0)
    (hf2 : 0 ≤ f (b 2))
    (hfrontier : Metric.ball (b 0) r ∩
        frontier (M.eraseTriangle T.1).toPlaneComplex.support =
      Metric.ball (b 0) r ∩
        (segment ℝ (b 0) v ∪
          segment ℝ (b 0) (b 2))) :
    let g := (-f v) • b.coord 2 + b.coord 2 v • f
    ∀ p ∈ Metric.ball (b 0) r, f p < 0 →
      p ∈ frontier (M.eraseTriangle T.1).toPlaneComplex.support → g p = 0 := by
  dsimp only
  let g := (-f v) • b.coord 2 + b.coord 2 v • f
  have hga : g (b 0) = 0 := by
    change (-f v) * b.coord 2 (b 0) + b.coord 2 v * f (b 0) = 0
    rw [b.coord_apply_ne (by decide : (2 : Fin 3) ≠ 0), show f (b 0) = 0 from hf0]
    ring
  have hgv : g v = 0 := by
    change (-f v) * b.coord 2 v + b.coord 2 v * f v = 0
    ring
  intro p hpball hfp hpF
  have hp : p ∈ Metric.ball (b 0) r ∩
      frontier (M.eraseTriangle T.1).toPlaneComplex.support := ⟨hpball, hpF⟩
  rcases (hfrontier ▸ hp).2 with hpv | hpc
  · have hImage : g p ∈ g '' segment ℝ (b 0) v := ⟨p, hpv, rfl⟩
    rw [image_segment, hga, hgv, segment_same] at hImage
    exact Set.mem_singleton_iff.mp hImage
  · have hseg := ((convex_Ici (0 : ℝ)).affine_preimage f).segment_subset hf0.ge hf2
    have hnonneg : 0 ≤ f p := hseg hpc
    exact False.elim ((not_lt_of_ge hnonneg) hfp)

private theorem one_edge_free_negative_survivor_sides
    (M : LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh)
    (T : M.Triangle) (b : AffineBasis (Fin 3) ℝ Plane)
    (htriangle : convexHull ℝ (Set.range b) = M.triangleCarrier T.1)
    (hfree : frontier M.toPlaneComplex.support ∩ M.triangleCarrier T.1 =
      segment ℝ (b 0) (b 1))
    (hattach : (M.eraseTriangle T.1).toPlaneComplex.support ∩ M.triangleCarrier T.1 =
      segment ℝ (b 0) (b 2) ∪ segment ℝ (b 1) (b 2))
    (v : Plane) {r : ℝ} (hr : 0 < r) (f : Plane →ᵃ[ℝ] ℝ)
    (hf0 : f (b 0) = 0)
    (hf1 : 0 < f (b 1))
    (hf2 : 0 < f (b 2)) (hfv : f v < 0)
    (hfrontier : Metric.ball (b 0) r ∩
        frontier (M.eraseTriangle T.1).toPlaneComplex.support =
      Metric.ball (b 0) r ∩
        (segment ℝ (b 0) v ∪
          segment ℝ (b 0) (b 2))) :
    let g := (-f v) • b.coord 2 + b.coord 2 v • f
    ∀ p ∈ Metric.ball (b 0) r, f p < 0 →
      (0 < g p → p ∈ interior (M.eraseTriangle T.1).toPlaneComplex.support) ∧
      (g p < 0 → p ∉ (M.eraseTriangle T.1).toPlaneComplex.support) := by
  dsimp only
  let g := (-f v) • b.coord 2 + b.coord 2 v • f
  let B := (M.eraseTriangle T.1).toPlaneComplex.support
  have hB : IsClosed B := (M.eraseTriangle T.1).toPlaneComplex.isCompact_support.isClosed
  obtain ⟨⟨q, hqball, hfq, hgq, hqB⟩, ⟨s, hsball, hfs, hgs, hsB⟩⟩ :=
    exists_one_edge_free_negative_retained_side_points M T b htriangle hfree hattach v hr f
      hf0 hf1 hf2 hfv hfrontier
  let Apos := (Metric.ball (b 0) r ∩ {p | f p < 0}) ∩ {p | 0 < g p}
  let Aneg := (Metric.ball (b 0) r ∩ {p | f p < 0}) ∩ {p | g p < 0}
  have hApos : Convex ℝ Apos := ((convex_ball (b 0) r).inter
    ((convex_Iio (0 : ℝ)).affine_preimage f)).inter
      ((convex_Ioi (0 : ℝ)).affine_preimage g)
  have hAneg : Convex ℝ Aneg := ((convex_ball (b 0) r).inter
    ((convex_Iio (0 : ℝ)).affine_preimage f)).inter
      ((convex_Iio (0 : ℝ)).affine_preimage g)
  have havoidPos : Disjoint Apos (frontier B) := by
    apply Set.disjoint_left.mpr
    rintro p ⟨⟨hpball, hfp⟩, hgp⟩ hpF
    have hzero := one_edge_free_negative_frontier_retained_coord_eq_zero M T b v f
      hf0 hf2.le hfrontier p hpball hfp hpF
    exact (show 0 < g p from hgp).ne' hzero
  have havoidNeg : Disjoint Aneg (frontier B) := by
    apply Set.disjoint_left.mpr
    rintro p ⟨⟨hpball, hfp⟩, hgp⟩ hpF
    have hzero := one_edge_free_negative_frontier_retained_coord_eq_zero M T b v f
      hf0 hf2.le hfrontier p hpball hfp hpF
    exact (show g p < 0 from hgp).ne hzero
  have hpos : Apos ⊆ interior B :=
    subset_interior_of_isPreconnected_disjoint_frontier hApos.isPreconnected hB havoidPos
      ⟨q, ⟨⟨hqball, hfq⟩, hgq⟩, hqB⟩
  have hneg : Aneg ⊆ Bᶜ :=
    subset_compl_of_isPreconnected_disjoint_frontier hAneg.isPreconnected hB havoidNeg
      ⟨s, ⟨⟨hsball, hfs⟩, hgs⟩, hsB⟩
  intro p hpball hfp
  exact ⟨fun hgp => hpos ⟨⟨hpball, hfp⟩, hgp⟩, fun hgp => hneg ⟨⟨hpball, hfp⟩, hgp⟩⟩

private theorem mem_openSegment_of_affine_retained_coord_zero
    (b : AffineBasis (Fin 3) ℝ Plane) (f : Plane →ᵃ[ℝ] ℝ)
    (hf0 : f (b 0) = 0) (hf1 : 0 < f (b 1)) (v : Plane) (hfv : f v < 0)
    {p : Plane} (hvp : f v < f p) (hfp : f p < 0)
    (hgp : (-f v) * b.coord 2 p + b.coord 2 v * f p = 0) :
    p ∈ openSegment ℝ (b 0) v := by
  have hvalue (x : Plane) : f x = f (b 1) * b.coord 1 x + f (b 2) * b.coord 2 x :=
    affine_triangle_map_apply_of_vertex_zero b f hf0 x
  let g := (-f v) • b.coord 2 + b.coord 2 v • f
  have hga : g (b 0) = 0 := by
    change (-f v) * b.coord 2 (b 0) + b.coord 2 v * f (b 0) = 0
    rw [b.coord_apply_ne (by decide : (2 : Fin 3) ≠ 0), hf0]
    ring
  have hgv : g v = 0 := by
    change (-f v) * b.coord 2 v + b.coord 2 v * f v = 0
    ring
  let t := f p / f v
  let q := AffineMap.lineMap (b 0) v t
  have ht : 0 < t := div_pos_of_neg_of_neg hfp hfv
  have ht1 : t < 1 := (div_lt_one_of_neg hfv).mpr hvp
  have hfq : f q = f p := by
    change f (AffineMap.lineMap (b 0) v (f p / f v)) = f p
    rw [AffineMap.apply_lineMap, hf0, AffineMap.lineMap_apply_ring,
      mul_zero, zero_add, div_mul_cancel₀ _ hfv.ne]
  have hgq : g q = 0 := by
    change g (AffineMap.lineMap (b 0) v t) = 0
    rw [AffineMap.apply_lineMap, hga, hgv]
    simp
  have h2 : b.coord 2 p = b.coord 2 q := by
    apply mul_left_cancel₀ (neg_ne_zero.mpr hfv.ne)
    change (-f v) * b.coord 2 q + b.coord 2 v * f q = 0 at hgq
    rw [hfq] at hgq
    linarith
  have h1 : b.coord 1 p = b.coord 1 q := by
    apply mul_left_cancel₀ hf1.ne'
    have hpvalue := hvalue p
    have hqvalue := hvalue q
    rw [hfq, ← h2] at hqvalue
    linarith
  have hpq : p = q := by
    apply b.ext_elem
    intro i
    fin_cases i
    · have hpSum := b.sum_coord_apply_eq_one p
      have hqSum := b.sum_coord_apply_eq_one q
      simp only [Fin.sum_univ_three] at hpSum hqSum
      rw [← h1, ← h2] at hqSum
      change b.coord 0 p = b.coord 0 q
      linarith
    · exact h1
    · exact h2
  rw [hpq]
  exact lineMap_mem_openSegment ℝ (b 0) v ⟨ht, ht1⟩

private theorem one_edge_free_negative_survivor_region_iff
    (M : LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh)
    (T : M.Triangle) (b : AffineBasis (Fin 3) ℝ Plane)
    (htriangle : convexHull ℝ (Set.range b) = M.triangleCarrier T.1)
    (hfree : frontier M.toPlaneComplex.support ∩ M.triangleCarrier T.1 =
      segment ℝ (b 0) (b 1))
    (hattach : (M.eraseTriangle T.1).toPlaneComplex.support ∩ M.triangleCarrier T.1 =
      segment ℝ (b 0) (b 2) ∪ segment ℝ (b 1) (b 2))
    (v : Plane) {r : ℝ} (hr : 0 < r) (f : Plane →ᵃ[ℝ] ℝ)
    (hf0 : f (b 0) = 0)
    (hf1 : 0 < f (b 1))
    (hf2 : 0 < f (b 2)) (hfv : f v < 0)
    (hfrontier : Metric.ball (b 0) r ∩
        frontier (M.eraseTriangle T.1).toPlaneComplex.support =
      Metric.ball (b 0) r ∩
        (segment ℝ (b 0) v ∪
          segment ℝ (b 0) (b 2))) :
    let g := (-f v) • b.coord 2 + b.coord 2 v • f
    ∀ p ∈ Metric.ball (b 0) r, f v < f p → f p < 0 →
      (p ∈ (M.eraseTriangle T.1).toPlaneComplex.support ↔ 0 ≤ g p) ∧
      (p ∈ interior (M.eraseTriangle T.1).toPlaneComplex.support ↔ 0 < g p) ∧
      (p ∈ frontier (M.eraseTriangle T.1).toPlaneComplex.support ↔ g p = 0) := by
  dsimp only
  let g := (-f v) • b.coord 2 + b.coord 2 v • f
  let B := (M.eraseTriangle T.1).toPlaneComplex.support
  have hB : IsClosed B := (M.eraseTriangle T.1).toPlaneComplex.isCompact_support.isClosed
  intro p hpball hvp hfp
  have hsides := one_edge_free_negative_survivor_sides M T b htriangle hfree hattach
    v hr f hf0 hf1 hf2
    hfv hfrontier p hpball hfp
  rcases lt_trichotomy (g p) 0 with hneg | hzero | hpos
  · have hpB : p ∉ B := hsides.2 hneg
    have hpI : p ∉ interior B := fun hpI => hpB (interior_subset hpI)
    have hpF : p ∉ frontier B := fun hpF => hpB (hB.frontier_subset hpF)
    exact ⟨iff_of_false hpB (not_le_of_gt hneg), iff_of_false hpI (not_lt_of_ge hneg.le),
      iff_of_false hpF hneg.ne⟩
  · have hpseg : p ∈ segment ℝ (b 0) v := openSegment_subset_segment ℝ (b 0) v
      (mem_openSegment_of_affine_retained_coord_zero b f hf0 hf1 v hfv hvp hfp hzero)
    have hp : p ∈ Metric.ball (b 0) r ∩ (segment ℝ (b 0) v ∪ segment ℝ (b 0) (b 2)) :=
      ⟨hpball, Or.inl hpseg⟩
    have hpF : p ∈ frontier B := (hfrontier.symm ▸ hp).2
    have hpB : p ∈ B := hB.frontier_subset hpF
    have hpI : p ∉ interior B :=
      fun hpI => Set.disjoint_left.mp disjoint_interior_frontier hpI hpF
    exact ⟨iff_of_true hpB hzero.ge, iff_of_false hpI (not_lt_of_ge hzero.le),
      iff_of_true hpF hzero⟩
  · have hpI : p ∈ interior B := hsides.1 hpos
    have hpB : p ∈ B := interior_subset hpI
    have hpF : p ∉ frontier B := Set.disjoint_left.mp disjoint_interior_frontier hpI
    exact ⟨iff_of_true hpB hpos.le, iff_of_true hpI hpos, iff_of_false hpF hpos.ne'⟩

private theorem mem_openSegment_of_affine_triangle_coord_zero
    (b : AffineBasis (Fin 3) ℝ Plane) (f : Plane →ᵃ[ℝ] ℝ)
    (hf0 : f (b 0) = 0) (hf2 : 0 < f (b 2)) {p : Plane}
    (hp0 : 0 < b.coord 0 p) (hp1 : b.coord 1 p = 0) (hfp : 0 < f p) :
    p ∈ openSegment ℝ (b 0) (b 2) := by
  have hvalue : f p = f (b 2) * b.coord 2 p := by
    have h := affine_triangle_map_apply_of_vertex_zero b f hf0 p
    simpa [hp1] using h
  have hp2 : 0 < b.coord 2 p := by
    rw [hvalue] at hfp
    exact (mul_pos_iff_of_pos_left hf2).mp hfp
  have hsum : b.coord 0 p + b.coord 2 p = 1 := by
    simpa only [Fin.sum_univ_three, hp1, add_zero] using b.sum_coord_apply_eq_one p
  refine ⟨b.coord 0 p, b.coord 2 p, hp0, hp2, hsum, ?_⟩
  simpa only [Fin.sum_univ_three, hp1, zero_smul, add_zero] using
    b.linear_combination_coord_eq_self p

private theorem one_edge_free_positive_coord_zero_mem_frontier
    (M : LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh)
    (T : M.Triangle) (b : AffineBasis (Fin 3) ℝ Plane) (v : Plane) {r : ℝ} (f : Plane →ᵃ[ℝ] ℝ)
    (hf0 : f (b 0) = 0)
    (hf2 : 0 < f (b 2))
    (hfrontier : Metric.ball (b 0) r ∩
        frontier (M.eraseTriangle T.1).toPlaneComplex.support =
      Metric.ball (b 0) r ∩
        (segment ℝ (b 0) v ∪
          segment ℝ (b 0) (b 2))) :
    ∀ p ∈ Metric.ball (b 0) r,
      0 < f p → 0 < b.coord 0 p → b.coord 1 p = 0 →
        p ∈ frontier (M.eraseTriangle T.1).toPlaneComplex.support := by
  intro p hpball hfp hp0 hp1
  have hpseg : p ∈ segment ℝ (b 0) (b 2) := openSegment_subset_segment ℝ (b 0) (b 2)
    (mem_openSegment_of_affine_triangle_coord_zero b f hf0 hf2 hp0 hp1 hfp)
  have hp : p ∈ Metric.ball (b 0) r ∩ (segment ℝ (b 0) v ∪ segment ℝ (b 0) (b 2)) :=
    ⟨hpball, Or.inr hpseg⟩
  exact (hfrontier.symm ▸ hp).2

private theorem eq_affine_triangle_vertex_of_map_coord_zero
    (b : AffineBasis (Fin 3) ℝ Plane) (f : Plane →ᵃ[ℝ] ℝ)
    (hf0 : f (b 0) = 0) (hf2 : f (b 2) ≠ 0) {p : Plane}
    (hfp : f p = 0) (hp1 : b.coord 1 p = 0) : p = b 0 := by
  have hvalue := affine_triangle_map_apply_of_vertex_zero b f hf0 p
  rw [hfp, hp1, mul_zero, zero_add] at hvalue
  have hp2 : b.coord 2 p = 0 := (mul_eq_zero.mp hvalue.symm).resolve_left hf2
  have hp0 := b.sum_coord_apply_eq_one p
  simp only [Fin.sum_univ_three, hp1, hp2, add_zero] at hp0
  apply b.ext_elem
  intro i
  fin_cases i
  · exact hp0.trans (b.coord_apply_eq 0).symm
  · exact hp1.trans (b.coord_apply_ne (by decide : (1 : Fin 3) ≠ 0)).symm
  · exact hp2.trans (b.coord_apply_ne (by decide : (2 : Fin 3) ≠ 0)).symm

private theorem one_edge_free_nonnegative_survivor_region_iff
    (M : LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh)
    (T : M.Triangle) (b : AffineBasis (Fin 3) ℝ Plane)
    (htriangle : convexHull ℝ (Set.range b) = M.triangleCarrier T.1)
    (hfree : frontier M.toPlaneComplex.support ∩ M.triangleCarrier T.1 =
      segment ℝ (b 0) (b 1))
    (hattach : (M.eraseTriangle T.1).toPlaneComplex.support ∩ M.triangleCarrier T.1 =
      segment ℝ (b 0) (b 2) ∪ segment ℝ (b 1) (b 2))
    (v : Plane) {r : ℝ} (hr : 0 < r) (f : Plane →ᵃ[ℝ] ℝ)
    (hf0 : f (b 0) = 0)
    (hf1 : 0 < f (b 1))
    (hf2 : 0 < f (b 2)) (hfv : f v < 0)
    (hfrontier : Metric.ball (b 0) r ∩
        frontier (M.eraseTriangle T.1).toPlaneComplex.support =
      Metric.ball (b 0) r ∩
        (segment ℝ (b 0) v ∪
          segment ℝ (b 0) (b 2))) :
    ∀ p ∈ Metric.ball (b 0) r, 0 < b.coord 0 p → 0 ≤ f p →
      (p ∈ (M.eraseTriangle T.1).toPlaneComplex.support ↔ b.coord 1 p ≤ 0) ∧
      (p ∈ interior (M.eraseTriangle T.1).toPlaneComplex.support ↔ b.coord 1 p < 0) ∧
      (p ∈ frontier (M.eraseTriangle T.1).toPlaneComplex.support ↔ b.coord 1 p = 0) := by
  let B := (M.eraseTriangle T.1).toPlaneComplex.support
  have hB : IsClosed B := (M.eraseTriangle T.1).toPlaneComplex.isCompact_support.isClosed
  intro p hpball hp0 hfp
  have hsides : (b.coord 1 p < 0 → p ∈ interior B) ∧
      (0 < b.coord 1 p → p ∉ B) := by
    rcases hfp.eq_or_lt with hzero | hpos
    · exact one_edge_free_transverse_survivor_sides M T b htriangle hfree hattach v hr f
        hf0 hf1 hf2 hfv hfrontier p hpball hzero.symm
    · exact ⟨one_edge_free_positive_survivor_interior M T b htriangle hfree hattach v hr f
        hf0 hf2 hfv hfrontier p hpball hpos,
        one_edge_free_positive_survivor_compl M T b htriangle v hr f
          hf0 hf2 hfv hfrontier p hpball hpos⟩
  rcases lt_trichotomy (b.coord 1 p) 0 with hneg | hzero | hpos
  · have hpI : p ∈ interior B := hsides.1 hneg
    have hpB : p ∈ B := interior_subset hpI
    have hpF : p ∉ frontier B := Set.disjoint_left.mp disjoint_interior_frontier hpI
    exact ⟨iff_of_true hpB hneg.le, iff_of_true hpI hneg, iff_of_false hpF hneg.ne⟩
  · have hpF : p ∈ frontier B := by
      rcases hfp.eq_or_lt with hfzero | hfpos
      · have hp := eq_affine_triangle_vertex_of_map_coord_zero b f hf0 hf2.ne'
          hfzero.symm hzero
        have hpGraph : p ∈ Metric.ball (b 0) r ∩
            (segment ℝ (b 0) v ∪ segment ℝ (b 0) (b 2)) := by
          refine ⟨hpball, Or.inl ?_⟩
          rw [hp]
          exact left_mem_segment ℝ (b 0) v
        exact (hfrontier.symm ▸ hpGraph).2
      · exact one_edge_free_positive_coord_zero_mem_frontier M T b v f
          hf0 hf2 hfrontier p hpball hfpos hp0 hzero
    have hpB : p ∈ B := hB.frontier_subset hpF
    have hpI : p ∉ interior B :=
      fun hpI => Set.disjoint_left.mp disjoint_interior_frontier hpI hpF
    exact ⟨iff_of_true hpB hzero.le, iff_of_false hpI (not_lt_of_ge hzero.ge),
      iff_of_true hpF hzero⟩
  · have hpB : p ∉ B := hsides.2 hpos
    have hpI : p ∉ interior B := fun hpI => hpB (interior_subset hpI)
    have hpF : p ∉ frontier B := fun hpF => hpB (hB.frontier_subset hpF)
    exact ⟨iff_of_false hpB (not_le_of_gt hpos), iff_of_false hpI (not_lt_of_ge hpos.le),
      iff_of_false hpF hpos.ne'⟩

private theorem one_edge_free_nonnegative_old_region_iff
    (M : LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh)
    (T : M.Triangle) (b : AffineBasis (Fin 3) ℝ Plane)
    (htriangle : convexHull ℝ (Set.range b) = M.triangleCarrier T.1)
    (hfree : frontier M.toPlaneComplex.support ∩ M.triangleCarrier T.1 =
      segment ℝ (b 0) (b 1))
    (hattach : (M.eraseTriangle T.1).toPlaneComplex.support ∩ M.triangleCarrier T.1 =
      segment ℝ (b 0) (b 2) ∪ segment ℝ (b 1) (b 2))
    (v : Plane) {r : ℝ} (hr : 0 < r) (f : Plane →ᵃ[ℝ] ℝ)
    (hf0 : f (b 0) = 0)
    (hf1 : 0 < f (b 1))
    (hf2 : 0 < f (b 2)) (hfv : f v < 0)
    (hOld : Metric.ball (b 0) r ∩ frontier M.toPlaneComplex.support =
      Metric.ball (b 0) r ∩
        (segment ℝ (b 0) v ∪
          segment ℝ (b 0) (b 1)))
    (hNew : Metric.ball (b 0) r ∩
        frontier (M.eraseTriangle T.1).toPlaneComplex.support =
      Metric.ball (b 0) r ∩
        (segment ℝ (b 0) v ∪
          segment ℝ (b 0) (b 2))) :
    ∀ p ∈ Metric.ball (b 0) r, 0 < b.coord 0 p → 0 ≤ f p →
      (p ∈ M.toPlaneComplex.support ↔ 0 ≤ b.coord 2 p) ∧
      (p ∈ interior M.toPlaneComplex.support ↔ 0 < b.coord 2 p) ∧
      (p ∈ frontier M.toPlaneComplex.support ↔ b.coord 2 p = 0) := by
  have hK : convexHull ℝ (Set.range b) = M.triangleCarrier T.1 := htriangle
  intro p hpball hp0 hfp
  have hB := one_edge_free_nonnegative_survivor_region_iff M T b htriangle hfree hattach v hr f
    hf0 hf1 hf2 hfv hNew p hpball hp0 hfp
  have hvalue := affine_triangle_map_apply_of_vertex_zero b f hf0 p
  have hweak : p ∈ M.toPlaneComplex.support ↔ 0 ≤ b.coord 2 p := by
    rw [M.support_eq_eraseTriangle_union_triangleCarrier T.2]
    constructor
    · rintro (hpB | hpK)
      · have hp1 := hB.1.mp hpB
        by_contra! hp2
        have hprod1 : f (b 1) * b.coord 1 p ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hf1.le hp1
        have hprod2 : f (b 2) * b.coord 2 p < 0 := mul_neg_of_pos_of_neg hf2 hp2
        linarith
      · have hpHull : p ∈ convexHull ℝ (Set.range b) := hK.symm ▸ hpK
        rw [b.convexHull_eq_nonneg_coord] at hpHull
        exact hpHull 2
    · intro hp2
      by_cases hp1 : b.coord 1 p ≤ 0
      · exact Or.inl (hB.1.mpr hp1)
      · right
        change p ∈ M.triangleCarrier T.1
        rw [← hK, b.convexHull_eq_nonneg_coord]
        intro i
        fin_cases i
        · exact hp0.le
        · exact le_of_lt (lt_of_not_ge hp1)
        · exact hp2
  have hboundary : p ∈ frontier M.toPlaneComplex.support ↔ b.coord 2 p = 0 := by
    constructor
    · intro hpF
      have hp : p ∈ Metric.ball (b 0) r ∩ frontier M.toPlaneComplex.support := ⟨hpball, hpF⟩
      rcases (hOld ▸ hp).2 with hpv | hpb
      · have hseg := ((convex_Iic (0 : ℝ)).affine_preimage f).segment_subset hf0.le hfv.le
        have hnonpos : f p ≤ 0 := hseg hpv
        have hp := eq_left_of_mem_segment_of_affine_zero f (b 0) v hf0 hfv.ne hpv
          (le_antisymm hnonpos hfp)
        rw [hp]
        exact b.coord_apply_ne (by decide)
      · have hImage : b.coord 2 p ∈ (b.coord 2) '' segment ℝ (b 0) (b 1) :=
          ⟨p, hpb, rfl⟩
        rw [image_segment] at hImage
        simpa [b.coord_apply] using hImage
    · intro hp2
      have hp1 : 0 ≤ b.coord 1 p := by
        rw [hp2, mul_zero, add_zero] at hvalue
        by_contra! hneg
        have hprod : f (b 1) * b.coord 1 p < 0 := mul_neg_of_pos_of_neg hf1 hneg
        linarith
      have hsum : b.coord 0 p + b.coord 1 p = 1 := by
        simpa only [Fin.sum_univ_three, hp2, add_zero] using b.sum_coord_apply_eq_one p
      have hpseg : p ∈ segment ℝ (b 0) (b 1) := by
        refine ⟨b.coord 0 p, b.coord 1 p, hp0.le, hp1, hsum, ?_⟩
        simpa only [Fin.sum_univ_three, hp2, zero_smul, add_zero] using
          b.linear_combination_coord_eq_self p
      have hp : p ∈ Metric.ball (b 0) r ∩ (segment ℝ (b 0) v ∪ segment ℝ (b 0) (b 1)) :=
        ⟨hpball, Or.inr hpseg⟩
      exact (hOld.symm ▸ hp).2
  have hinterior : p ∈ interior M.toPlaneComplex.support ↔ 0 < b.coord 2 p := by
    constructor
    · intro hpI
      have hpnonneg := hweak.mp (interior_subset hpI)
      have hpne : b.coord 2 p ≠ 0 := fun hpzero =>
        Set.disjoint_left.mp disjoint_interior_frontier hpI (hboundary.mpr hpzero)
      exact lt_of_le_of_ne hpnonneg hpne.symm
    · intro hppos
      apply (mem_interior_iff_notMem_frontier (hweak.mpr hppos.le)).mpr
      exact fun hpF => hppos.ne' (hboundary.mp hpF)
  exact ⟨hweak, hinterior, hboundary⟩

end Schoenflies
end
section

namespace Schoenflies

open LeanEval.Topology.ClassificationOfSurfaces.Moise
  (exists_affine_triangle_chart_with_first_coordinate)

private theorem affine_triangle_graph_comparison
    (b : AffineBasis (Fin 3) ℝ Plane) (f : Plane →ᵃ[ℝ] ℝ)
    (hf0 : f (b 0) = 0) (hf1 : 0 < f (b 1)) (hf2 : 0 < f (b 2)) (p : Plane) :
    (b.coord 1 p ≤ 0 ↔ f p / f (b 2) ≤ b.coord 2 p) ∧
    (b.coord 1 p < 0 ↔ f p / f (b 2) < b.coord 2 p) ∧
    (b.coord 1 p = 0 ↔ b.coord 2 p = f p / f (b 2)) := by
  have hvalue := affine_triangle_map_apply_of_vertex_zero b f hf0 p
  refine ⟨?_, ?_, ?_⟩
  · rw [div_le_iff₀ hf2, hvalue, mul_comm (b.coord 2 p), add_le_iff_nonpos_left]
    exact ⟨mul_nonpos_of_nonneg_of_nonpos hf1.le,
      fun h => nonpos_of_mul_nonpos_right h hf1⟩
  · rw [div_lt_iff₀ hf2, hvalue, mul_comm (b.coord 2 p), add_lt_iff_neg_right]
    exact ⟨mul_neg_of_pos_of_neg hf1, fun h => neg_of_mul_neg_right h hf1.le⟩
  · rw [eq_div_iff hf2.ne', hvalue, mul_comm (b.coord 2 p)]
    constructor
    · intro h
      rw [h, mul_zero, zero_add]
    · intro h
      have hz : f (b 1) * b.coord 1 p = 0 := by linarith
      exact (mul_eq_zero.mp hz).resolve_left hf1.ne'

private theorem exists_one_edge_free_endpoint_graph_regions_of_basis
    (M : LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh)
    (T : M.Triangle) (b : AffineBasis (Fin 3) ℝ Plane)
    (htriangle : convexHull ℝ (Set.range b) = M.triangleCarrier T.1)
    (hfree : frontier M.toPlaneComplex.support ∩ M.triangleCarrier T.1 =
      segment ℝ (b 0) (b 1))
    (hattach : (M.eraseTriangle T.1).toPlaneComplex.support ∩ M.triangleCarrier T.1 =
      segment ℝ (b 0) (b 2) ∪ segment ℝ (b 1) (b 2))
    (v : Plane) {ρ : ℝ} (hρ : 0 < ρ) (f : Plane →ᵃ[ℝ] ℝ)
    (hf0 : f (b 0) = 0) (hf1 : 0 < f (b 1)) (hf2 : 0 < f (b 2)) (hfv : f v < 0)
    (hOld : Metric.ball (b 0) ρ ∩ frontier M.toPlaneComplex.support =
      Metric.ball (b 0) ρ ∩ (segment ℝ (b 0) v ∪ segment ℝ (b 0) (b 1)))
    (hNew : Metric.ball (b 0) ρ ∩ frontier (M.eraseTriangle T.1).toPlaneComplex.support =
      Metric.ball (b 0) ρ ∩ (segment ℝ (b 0) v ∪ segment ℝ (b 0) (b 2))) :
    ∃ (r : ℝ) (e : Plane ≃ᵃ[ℝ] Plane), 0 < r ∧ r ≤ ρ ∧
      (∀ p, (e p) 0 = f p ∧ (e p) 1 = b.coord 2 p) ∧
      ∀ p ∈ Metric.ball (b 0) r,
        (p ∈ M.toPlaneComplex.support ↔
          (if f p < 0 then b.coord 2 v / f v * f p else 0) ≤ b.coord 2 p) ∧
        (p ∈ interior M.toPlaneComplex.support ↔
          (if f p < 0 then b.coord 2 v / f v * f p else 0) < b.coord 2 p) ∧
        (p ∈ frontier M.toPlaneComplex.support ↔
          b.coord 2 p = if f p < 0 then b.coord 2 v / f v * f p else 0) ∧
        (p ∈ (M.eraseTriangle T.1).toPlaneComplex.support ↔
          (if f p < 0 then b.coord 2 v / f v * f p else f p / f (b 2)) ≤ b.coord 2 p) ∧
        (p ∈ interior (M.eraseTriangle T.1).toPlaneComplex.support ↔
          (if f p < 0 then b.coord 2 v / f v * f p else f p / f (b 2)) < b.coord 2 p) ∧
        (p ∈ frontier (M.eraseTriangle T.1).toPlaneComplex.support ↔
          b.coord 2 p = if f p < 0 then b.coord 2 v / f v * f p else f p / f (b 2)) := by
  have hK := triangle_nonneg_of_affine_vertex_nonneg M T b htriangle f (by
    intro i
    fin_cases i
    · exact hf0.ge
    · exact hf1.le
    · exact hf2.le)
  let L : Set Plane := {p | f p < 0}
  have hL : IsOpen L := isOpen_lt f.continuous_of_finiteDimensional continuous_const
  have hS : L ∩ M.toPlaneComplex.support =
      L ∩ (M.eraseTriangle T.1).toPlaneComplex.support := by
    apply Set.Subset.antisymm
    · rintro p ⟨hpL, hpM⟩
      rw [M.support_eq_eraseTriangle_union_triangleCarrier T.2] at hpM
      rcases hpM with hpB | hpK
      · exact ⟨hpL, hpB⟩
      · have hpnonneg : 0 ≤ f p := hK hpK
        exact False.elim ((not_lt_of_ge hpnonneg) hpL)
    · exact fun p hp => ⟨hp.1, M.eraseTriangle_support_subset T.1 hp.2⟩
  have hI : L ∩ interior M.toPlaneComplex.support =
      L ∩ interior (M.eraseTriangle T.1).toPlaneComplex.support := by
    have h := congrArg interior hS
    simpa only [interior_inter, hL.interior_eq] using h
  change {p | f p < 0} ∩ M.toPlaneComplex.support =
    {p | f p < 0} ∩ (M.eraseTriangle T.1).toPlaneComplex.support at hS
  change {p | f p < 0} ∩ interior M.toPlaneComplex.support =
    {p | f p < 0} ∩ interior (M.eraseTriangle T.1).toPlaneComplex.support at hI
  obtain ⟨e, heX, he0, he1, he2⟩ :=
    exists_affine_triangle_chart_with_first_coordinate
      b f hf0 hf1
  have heY : ∀ p, (e p) 1 = b.coord 2 p := by
    have he : LeanEval.Topology.ClassificationOfSurfaces.Moise.cartesianY.comp e.toAffineMap =
        b.coord 2 := by
      apply AffineMap.ext_on b.tot
      rintro p ⟨i, rfl⟩
      change (e (b i)) 1 = b.coord 2 (b i)
      fin_cases i
      · change (e (b 0)) 1 = b.coord 2 (b 0)
        rw [he0, b.coord_apply_ne (by decide : (2 : Fin 3) ≠ 0)]
        rfl
      · change (e (b 1)) 1 = b.coord 2 (b 1)
        rw [he1, b.coord_apply_ne (by decide : (2 : Fin 3) ≠ 1)]
        rfl
      · change (e (b 2)) 1 = b.coord 2 (b 2)
        rw [he2, b.coord_apply_eq]
        rfl
    exact fun p => congrArg (fun g : Plane →ᵃ[ℝ] ℝ => g p) he
  let U := {p | 0 < b.coord 0 p} ∩ {p | f v < f p}
  have hU : IsOpen U := (isOpen_lt continuous_const
    (b.coord 0).continuous_of_finiteDimensional).inter
      (isOpen_lt continuous_const f.continuous_of_finiteDimensional)
  have haU : b 0 ∈ U := by
    constructor
    · change 0 < b.coord 0 (b 0)
      rw [b.coord_apply_eq]
      exact zero_lt_one
    · change f v < f (b 0)
      rw [show f (b 0) = 0 from hf0]
      exact hfv
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp hU (b 0) haU
  let r := min ρ δ
  refine ⟨r, e, lt_min hρ hδ, min_le_left _ _, fun p => ⟨heX p, heY p⟩, ?_⟩
  intro p hpball
  have hpρ : p ∈ Metric.ball (b 0) ρ := Metric.ball_subset_ball (min_le_left _ _) hpball
  have hpU : p ∈ U := hδU (Metric.ball_subset_ball (min_le_right _ _) hpball)
  by_cases hfp : f p < 0
  · simp only [if_pos hfp]
    let B := (M.eraseTriangle T.1).toPlaneComplex.support
    let S := M.toPlaneComplex.support
    let g := (-f v) • b.coord 2 + b.coord 2 v • f
    have hB := one_edge_free_negative_survivor_region_iff M T b htriangle hfree hattach v hρ f
      hf0 hf1 hf2 hfv hNew p hpρ hpU.2 hfp
    have hmem : p ∈ S ↔ p ∈ B := by
      constructor
      · intro hpS
        exact (hS ▸ (show p ∈ {q | f q < 0} ∩ S from ⟨hfp, hpS⟩)).2
      · intro hpB
        exact (hS.symm ▸ (show p ∈ {q | f q < 0} ∩ B from ⟨hfp, hpB⟩)).2
    have hint : p ∈ interior S ↔ p ∈ interior B := by
      constructor
      · intro hpS
        exact (hI ▸ (show p ∈ {q | f q < 0} ∩ interior S from ⟨hfp, hpS⟩)).2
      · intro hpB
        exact (hI.symm ▸ (show p ∈ {q | f q < 0} ∩ interior B from ⟨hfp, hpB⟩)).2
    have hfront : p ∈ frontier S ↔ p ∈ frontier B := by
      have hclosedS : IsClosed S := M.toPlaneComplex.isCompact_support.isClosed
      have hclosedB : IsClosed B :=
        (M.eraseTriangle T.1).toPlaneComplex.isCompact_support.isClosed
      change (p ∈ closure S ∧ p ∉ interior S) ↔ (p ∈ closure B ∧ p ∉ interior B)
      rw [hclosedS.closure_eq, hclosedB.closure_eq]
      exact and_congr hmem (not_congr hint)
    have hg : g p = (-f v) * (b.coord 2 p - b.coord 2 v / f v * f p) := by
      calc
        g p = (-f v) * b.coord 2 p + (f v * (b.coord 2 v / f v)) * f p := by
          rw [mul_div_cancel₀ _ hfv.ne]
          rfl
        _ = (-f v) * (b.coord 2 p - b.coord 2 v / f v * f p) := by ring
    have hgweak : 0 ≤ g p ↔ b.coord 2 v / f v * f p ≤ b.coord 2 p := by
      rw [hg, mul_nonneg_iff_of_pos_left (neg_pos.mpr hfv), sub_nonneg]
    have hgstrict : 0 < g p ↔ b.coord 2 v / f v * f p < b.coord 2 p := by
      rw [hg, mul_pos_iff_of_pos_left (neg_pos.mpr hfv), sub_pos]
    have hgzero : g p = 0 ↔ b.coord 2 p = b.coord 2 v / f v * f p := by
      rw [hg, mul_eq_zero]
      simp only [neg_ne_zero.mpr hfv.ne, false_or, sub_eq_zero]
    exact ⟨hmem.trans (hB.1.trans hgweak), hint.trans (hB.2.1.trans hgstrict),
      hfront.trans (hB.2.2.trans hgzero), hB.1.trans hgweak, hB.2.1.trans hgstrict,
      hB.2.2.trans hgzero⟩
  · simp only [if_neg hfp]
    have hB := one_edge_free_nonnegative_survivor_region_iff M T b htriangle hfree hattach v hρ f
      hf0 hf1 hf2 hfv hNew p hpρ hpU.1 (le_of_not_gt hfp)
    have hS := one_edge_free_nonnegative_old_region_iff M T b htriangle hfree hattach v hρ f
      hf0 hf1 hf2 hfv hOld hNew p hpρ hpU.1 (le_of_not_gt hfp)
    have hcompare := affine_triangle_graph_comparison b f hf0 hf1 hf2 p
    exact ⟨hS.1, hS.2.1, hS.2.2, hB.1.trans hcompare.1,
      hB.2.1.trans hcompare.2.1, hB.2.2.trans hcompare.2.2⟩

end Schoenflies
end
section

namespace Schoenflies

private theorem one_edge_free_frontier_decompositions {m : ℕ} (P : PrePolygon m)
    (M : LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh)
    (hfrontier : frontier M.toPlaneComplex.support = P.carrier)
    (T : M.Triangle) (k : Fin 3) (hfree : M.IsOneEdgeFreeTriangle T k) :
    let b := LeanEval.Topology.ClassificationOfSurfaces.Moise.affineBasisOfTriangle
      (M.freeTriangleOrder T k) (M.freeTriangleOrder_affineIndependent T k)
    let R := closure (P.carrier \ segment ℝ (b 0) (b 1))
    frontier M.toPlaneComplex.support = R ∪ segment ℝ (b 0) (b 1) ∧
      frontier (M.eraseTriangle T.1).toPlaneComplex.support =
        R ∪ (segment ℝ (b 0) (b 2) ∪ segment ℝ (b 1) (b 2)) := by
  dsimp only
  let b := LeanEval.Topology.ClassificationOfSurfaces.Moise.affineBasisOfTriangle
    (M.freeTriangleOrder T k) (M.freeTriangleOrder_affineIndependent T k)
  let R := closure (P.carrier \ segment ℝ (b 0) (b 1))
  change frontier M.toPlaneComplex.support ∩ M.triangleCarrier T.1 =
    segment ℝ (b 0) (b 1) at hfree
  constructor
  · rw [hfrontier]
    apply Set.Subset.antisymm
    · intro p hp
      by_cases hpbase : p ∈ segment ℝ (b 0) (b 1)
      · exact Or.inr hpbase
      · exact Or.inl (subset_closure ⟨hp, hpbase⟩)
    · rintro p (hpR | hpbase)
      · exact closure_minimal Set.sdiff_subset P.isClosed_carrier hpR
      · exact hfrontier ▸ (hfree.symm ▸ hpbase).1
  · obtain ⟨n, Q, j, l, hQ, _, _, hl2, _, _, hRarc, hAarc, _⟩ :=
      P.exists_prePolygon_closed_region_erase_triangle_of_one_edge_free M hfrontier T k hfree
    change Q.arc j l = R at hRarc
    change Q.arc (j + (l : ZMod (n + 3))) (n + 3 - l) =
      segment ℝ (b 0) (b 2) ∪ segment ℝ (b 1) (b 2) at hAarc
    rw [← hQ, ← Q.arc_union j (show l ≤ n + 3 by omega), hRarc, hAarc]

private theorem exists_endpoint_frontier_pairs_of_retained_germ
    (b : AffineBasis (Fin 3) ℝ Plane) (R S B : Set Plane)
    (hS : frontier S = R ∪ segment ℝ (b 0) (b 1))
    (hB : frontier B = R ∪ (segment ℝ (b 0) (b 2) ∪ segment ℝ (b 1) (b 2)))
    (v : Plane) {ρ : ℝ} (hρ : 0 < ρ) (hseg : segment ℝ (b 0) v ⊆ R)
    (hgerm : Metric.ball (b 0) ρ ∩ R = Metric.ball (b 0) ρ ∩ segment ℝ (b 0) v) :
    ∃ r : ℝ, 0 < r ∧ r ≤ ρ ∧
      Metric.ball (b 0) r ∩ frontier S =
        Metric.ball (b 0) r ∩ (segment ℝ (b 0) v ∪ segment ℝ (b 0) (b 1)) ∧
      Metric.ball (b 0) r ∩ frontier B =
        Metric.ball (b 0) r ∩ (segment ℝ (b 0) v ∪ segment ℝ (b 0) (b 2)) := by
  have haBC : b 0 ∉ segment ℝ (b 1) (b 2) := by
    intro ha
    have hImage : b.coord 0 (b 0) ∈ (b.coord 0) '' segment ℝ (b 1) (b 2) :=
      ⟨b 0, ha, rfl⟩
    rw [image_segment] at hImage
    simp [b.coord_apply] at hImage
  obtain ⟨δ, hδ, hballBC⟩ := Metric.isOpen_iff.mp
    (isCompact_segment (b 1) (b 2)).isClosed.isOpen_compl (b 0) haBC
  let r := min ρ δ
  have hr : 0 < r := lt_min hρ hδ
  have hball : Metric.ball (b 0) r ⊆ Metric.ball (b 0) ρ :=
    Metric.ball_subset_ball (min_le_left _ _)
  have havoid : Disjoint (Metric.ball (b 0) r) (segment ℝ (b 1) (b 2)) :=
    Set.disjoint_left.mpr fun p hp hpc =>
      hballBC (Metric.ball_subset_ball (min_le_right ρ δ) hp) hpc
  have hgerm' : Metric.ball (b 0) r ∩ R = Metric.ball (b 0) r ∩ segment ℝ (b 0) v := by
    apply Set.Subset.antisymm
    · rintro p ⟨hpball, hpR⟩
      exact ⟨hpball, (hgerm ▸ (show p ∈ Metric.ball (b 0) ρ ∩ R from
        ⟨hball hpball, hpR⟩)).2⟩
    · exact fun p hp => ⟨hp.1, hseg hp.2⟩
  refine ⟨r, hr, min_le_left _ _, ?_, ?_⟩
  · rw [hS, Set.inter_union_distrib_left, hgerm', ← Set.inter_union_distrib_left]
  · rw [hB]
    apply Set.Subset.antisymm
    · rintro p ⟨hpball, hpR | hpac | hpbc⟩
      · have hp : p ∈ Metric.ball (b 0) r ∩ R := ⟨hpball, hpR⟩
        exact ⟨hpball, Or.inl ((hgerm' ▸ hp).2)⟩
      · exact ⟨hpball, Or.inr hpac⟩
      · exact False.elim (Set.disjoint_left.mp havoid hpball hpbc)
    · rintro p ⟨hpball, hpav | hpac⟩
      · exact ⟨hpball, Or.inl (hseg hpav)⟩
      · exact ⟨hpball, Or.inr (Or.inl hpac)⟩

end Schoenflies
end
section

namespace Schoenflies

theorem PrePolygon.exists_affine_graph_charts_of_one_edge_free_triangle
    {m : ℕ} (P : PrePolygon m)
    (M : LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh)
    (hfrontier : frontier M.toPlaneComplex.support = P.carrier)
    (T : M.Triangle) (k : Fin 3) (hfree : M.IsOneEdgeFreeTriangle T k) :
    let b := LeanEval.Topology.ClassificationOfSurfaces.Moise.affineBasisOfTriangle
      (M.freeTriangleOrder T k) (M.freeTriangleOrder_affineIndependent T k)
    let R := closure (P.carrier \ segment ℝ (b 0) (b 1))
    ∃ (v₀ v₁ : Plane) (r₀ r₁ : ℝ) (f₀ f₁ : Plane →ᵃ[ℝ] ℝ)
      (e₀ e₁ : Plane ≃ᵃ[ℝ] Plane), 0 < r₀ ∧ 0 < r₁ ∧
      Disjoint (Metric.ball (b 0) r₀) (Metric.ball (b 1) r₁) ∧
      segment ℝ (b 0) v₀ ⊆ R ∧ segment ℝ (b 1) v₁ ⊆ R ∧
      f₀ (b 0) = 0 ∧ 0 < f₀ (b 1) ∧ 0 < f₀ (b 2) ∧ f₀ v₀ < 0 ∧
      f₁ (b 1) = 0 ∧ 0 < f₁ (b 0) ∧ 0 < f₁ (b 2) ∧ f₁ v₁ < 0 ∧
      (∀ p, (e₀ p) 0 = f₀ p ∧ (e₀ p) 1 = b.coord 2 p) ∧
      (∀ p, (e₁ p) 0 = f₁ p ∧ (e₁ p) 1 = b.coord 2 p) ∧
      (∀ p ∈ Metric.ball (b 0) r₀,
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
      (∀ p ∈ Metric.ball (b 1) r₁,
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
            f₁ p / f₁ (b 2))) := by
  dsimp only
  let b := LeanEval.Topology.ClassificationOfSurfaces.Moise.affineBasisOfTriangle
    (M.freeTriangleOrder T k) (M.freeTriangleOrder_affineIndependent T k)
  let R := closure (P.carrier \ segment ℝ (b 0) (b 1))
  let S := M.toPlaneComplex.support
  let B := (M.eraseTriangle T.1).toPlaneComplex.support
  obtain ⟨v₀, v₁, δ₀, δ₁, f₀, f₁, _, _, hδ₀, hδ₁, hdisj, hs₀, hs₁, hg₀, hg₁,
    hf₀, hfb, hfc₀, hfv₀, hf₁, hfa, hfc₁, hfv₁⟩ :=
    exists_one_edge_free_two_endpoint_separators P M hfrontier T k hfree
  obtain ⟨hOld, hNew⟩ := one_edge_free_frontier_decompositions P M hfrontier T k hfree
  change frontier S = R ∪ segment ℝ (b 0) (b 1) at hOld
  change frontier B = R ∪ (segment ℝ (b 0) (b 2) ∪ segment ℝ (b 1) (b 2)) at hNew
  have htriangle : convexHull ℝ (Set.range b) = M.triangleCarrier T.1 := by
    change convexHull ℝ (Set.range ((M.position ∘ M.orderedVertex T) ∘ Equiv.swap 2 k)) = _
    rw [EquivLike.range_comp, Set.range_comp, M.range_orderedVertex T]
    rfl
  have hattach : B ∩ M.triangleCarrier T.1 =
      segment ℝ (b 0) (b 2) ∪ segment ℝ (b 1) (b 2) :=
    M.eraseTriangle_support_inter_triangleCarrier_of_oneEdgeFree T k hfree
  change frontier S ∩ M.triangleCarrier T.1 = segment ℝ (b 0) (b 1) at hfree
  obtain ⟨ρ₀, hρ₀, hρ₀δ, hOld₀, hNew₀⟩ :=
    exists_endpoint_frontier_pairs_of_retained_germ b R S B hOld hNew v₀ hδ₀ hs₀ hg₀
  obtain ⟨r₀, e₀, hr₀, hr₀ρ, he₀, hgraph₀⟩ :=
    exists_one_edge_free_endpoint_graph_regions_of_basis M T b htriangle hfree hattach
      v₀ hρ₀ f₀ hf₀ hfb hfc₀ hfv₀ hOld₀ hNew₀
  let c := b.reindex (Equiv.swap (0 : Fin 3) 1)
  have hc0 : c 0 = b 1 := by simp [c]
  have hc1 : c 1 = b 0 := by simp [c]
  have hc2 : c 2 = b 2 := by simp [c, Equiv.swap_apply_def]
  have hcoord2 : c.coord 2 = b.coord 2 := by simp [c, Equiv.swap_apply_def]
  have hcbase : segment ℝ (c 0) (c 1) = segment ℝ (b 0) (b 1) := by
    rw [hc0, hc1, segment_symm]
  have hcattach : segment ℝ (c 0) (c 2) ∪ segment ℝ (c 1) (c 2) =
      segment ℝ (b 0) (b 2) ∪ segment ℝ (b 1) (b 2) := by
    rw [hc0, hc1, hc2, Set.union_comm]
  have hcrange : Set.range c = Set.range b := by
    simp only [c, AffineBasis.coe_reindex, EquivLike.range_comp]
  obtain ⟨ρ₁, hρ₁, hρ₁δ, hOld₁, hNew₁⟩ :=
    exists_endpoint_frontier_pairs_of_retained_germ c R S B
      (by rw [hcbase]; exact hOld) (by rw [hcattach]; exact hNew) v₁ hδ₁
      (by simpa only [hc0] using hs₁) (by simpa only [hc0] using hg₁)
  obtain ⟨r₁, e₁, hr₁, hr₁ρ, he₁, hgraph₁⟩ :=
    exists_one_edge_free_endpoint_graph_regions_of_basis M T c
      (by rw [hcrange]; exact htriangle) (by rw [hcbase]; exact hfree)
      (by rw [hcattach]; exact hattach) v₁ hρ₁ f₁
      (by simpa only [hc0] using hf₁) (by simpa only [hc1] using hfa)
      (by simpa only [hc2] using hfc₁) hfv₁ hOld₁ hNew₁
  simp only [hc0, hc2, hcoord2] at hgraph₁
  simp only [hcoord2] at he₁
  refine ⟨v₀, v₁, r₀, r₁, f₀, f₁, e₀, e₁, hr₀, hr₁, ?_, hs₀, hs₁,
    hf₀, hfb, hfc₀, hfv₀, hf₁, hfa, hfc₁, hfv₁, he₀, he₁, hgraph₀, hgraph₁⟩
  exact hdisj.mono (Metric.ball_subset_ball (hr₀ρ.trans hρ₀δ))
    (Metric.ball_subset_ball (hr₁ρ.trans hρ₁δ))

end Schoenflies
end

section

open scoped ContDiff Topology

namespace DifferentialGeometry.Analysis

private theorem exists_contDiff_glued_near_compact
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K U₀ U₁ V : Set E} (hK : IsCompact K)
    (hU₀ : IsOpen U₀) (hU₁ : IsOpen U₁) (hV : IsOpen V)
    (hdisj : Disjoint U₀ U₁) (hcover : K ⊆ U₀ ∪ U₁ ∪ V)
    (f₀ f₁ f₂ : E → F) (hf₀ : ContDiff ℝ ∞ f₀) (hf₁ : ContDiff ℝ ∞ f₁)
    (hf₂ : ContDiff ℝ ∞ f₂) (h₀ : Set.EqOn f₀ f₂ (U₀ ∩ V))
    (h₁ : Set.EqOn f₁ f₂ (U₁ ∩ V)) :
    ∃ (g : E → F) (W : Set E), ContDiff ℝ ∞ g ∧ IsOpen W ∧ K ⊆ W ∧
      Set.EqOn g f₀ (W ∩ U₀) ∧ Set.EqOn g f₁ (W ∩ U₁) ∧
      Set.EqOn g f₂ (W ∩ V) := by
  classical
  let f : E → F := fun x => if x ∈ U₀ then f₀ x else if x ∈ U₁ then f₁ x else f₂ x
  have he₀ : Set.EqOn f f₀ U₀ := fun x hx => by simp only [f, if_pos hx]
  have he₁ : Set.EqOn f f₁ U₁ := by
    intro x hx
    have hx₀ : x ∉ U₀ := fun hy => Set.disjoint_left.mp hdisj hy hx
    simp only [f, if_neg hx₀, if_pos hx]
  have he₂ : Set.EqOn f f₂ V := by
    intro x hx
    by_cases hx₀ : x ∈ U₀
    · exact (he₀ hx₀).trans (h₀ ⟨hx₀, hx⟩)
    by_cases hx₁ : x ∈ U₁
    · exact (he₁ hx₁).trans (h₁ ⟨hx₁, hx⟩)
    simp only [f, if_neg hx₀, if_neg hx₁]
  have hf : ContDiffOn ℝ ∞ f (U₀ ∪ U₁ ∪ V) :=
    ((hf₀.contDiffOn.congr (fun _ hx => he₀ hx)).union_of_isOpen
      (hf₁.contDiffOn.congr (fun _ hx => he₁ hx)) hU₀ hU₁).union_of_isOpen
        (hf₂.contDiffOn.congr (fun _ hx => he₂ hx)) (hU₀.union hU₁) hV
  obtain ⟨χ, hχ, _, hχone, hχsupport, _⟩ :=
    exists_bump_compact hK ((hU₀.union hU₁).union hV) hcover
  obtain ⟨W, hW, hKW, hWone⟩ := mem_nhdsSet_iff_exists.mp hχone
  refine ⟨fun x => χ x • f x, W,
    contDiff_cutoff_smul ((hU₀.union hU₁).union hV) hχ hχsupport hf,
    hW, hKW, ?_, ?_, ?_⟩
  · intro x hx
    change χ x • f x = f₀ x
    rw [show χ x = 1 from hWone hx.1, one_smul]
    exact he₀ hx.2
  · intro x hx
    change χ x • f x = f₁ x
    rw [show χ x = 1 from hWone hx.1, one_smul]
    exact he₁ hx.2
  · intro x hx
    change χ x • f x = f₂ x
    rw [show χ x = 1 from hWone hx.1, one_smul]
    exact he₂ hx.2

end DifferentialGeometry.Analysis

end

section

open scoped ContDiff

namespace Schoenflies

private theorem matched_endpoint_defining_functions_overlap
    (b : AffineBasis (Fin 3) ℝ Plane) (f : Plane →ᵃ[ℝ] ℝ)
    (hf0 : f (b 0) = 0) (hf1 : 0 < f (b 1)) (hf2 : 0 < f (b 2))
    (s : ℝ) {ε σ : ℝ} (hε : 0 < ε) (hσ : 0 < σ) :
    let g := fun p => s * (f p - Real.smoothMax ε (f p) 0)
    let A := fun p => g p - b.coord 2 p
    let B := fun p => f (b 2) / f (b 1) *
      (g p + Real.smoothMax ε (f p) 0 / f (b 2) - b.coord 2 p)
    let C := fun p => -Real.smoothMax σ (-b.coord 0 p) (-b.coord 1 p)
    let U := {p | ε < f p ∧ σ < b.coord 0 p - b.coord 1 p}
    ContDiff ℝ ∞ A ∧ ContDiff ℝ ∞ B ∧ ContDiff ℝ ∞ C ∧ IsOpen U ∧
      (∀ p, B p ≤ 0 ↔ g p + Real.smoothMax ε (f p) 0 / f (b 2) ≤ b.coord 2 p) ∧
      (∀ p ∈ U, A p = -b.coord 2 p ∧ B p = C p ∧ C p = b.coord 1 p) := by
  dsimp only
  have hf : ContDiff ℝ ∞ f :=
    (⟨f, f.continuous_of_finiteDimensional⟩ : Plane →ᴬ[ℝ] ℝ).contDiff
  have hβ (i : Fin 3) : ContDiff ℝ ∞ (b.coord i) :=
    (⟨b.coord i, (b.coord i).continuous_of_finiteDimensional⟩ : Plane →ᴬ[ℝ] ℝ).contDiff
  have hμ : ContDiff ℝ ∞ (fun p => Real.smoothMax ε (f p) 0) :=
    (Real.smoothMax.contDiff ε).comp (hf.prodMk contDiff_const)
  have hg : ContDiff ℝ ∞ (fun p => s * (f p - Real.smoothMax ε (f p) 0)) :=
    contDiff_const.mul (hf.sub hμ)
  refine ⟨hg.sub (hβ 2), contDiff_const.mul ((hg.add (hμ.div_const _)).sub (hβ 2)),
    ((Real.smoothMax.contDiff σ).comp ((hβ 0).neg.prodMk (hβ 1).neg)).neg,
    (isOpen_lt continuous_const hf.continuous).inter
      (isOpen_lt continuous_const ((hβ 0).sub (hβ 1)).continuous), ?_, ?_⟩
  · intro p
    constructor
    · intro hp
      exact sub_nonpos.mp (nonpos_of_mul_nonpos_right hp (div_pos hf2 hf1))
    · intro hp
      exact mul_nonpos_of_nonneg_of_nonpos (div_pos hf2 hf1).le (sub_nonpos.mpr hp)
  · intro p hp
    have hmax : Real.smoothMax ε (f p) 0 = f p := by
      have hgap : ε ≤ |f p - 0| := by
        simpa only [sub_zero, abs_of_pos (hε.trans hp.1)] using hp.1.le
      rw [Real.smoothMax.eq_max_of_le hε hgap, max_eq_left (hε.trans hp.1).le]
    have hdiff : -b.coord 0 p - -b.coord 1 p = -(b.coord 0 p - b.coord 1 p) := by ring
    have hcentral : -Real.smoothMax σ (-b.coord 0 p) (-b.coord 1 p) = b.coord 1 p := by
      have hgap : σ ≤ |-b.coord 0 p - -b.coord 1 p| := by
        rw [hdiff, abs_neg, abs_of_pos (hσ.trans hp.2)]
        exact hp.2.le
      rw [Real.smoothMax.eq_max_of_le hσ hgap,
        max_eq_right (by linarith [hp.2]), neg_neg]
    have hvalue := affine_triangle_map_apply_of_vertex_zero b f hf0 p
    rw [hmax, sub_self, mul_zero, zero_add, zero_sub]
    refine ⟨rfl, ?_, hcentral⟩
    rw [hcentral, hvalue]
    field_simp [hf1.ne', hf2.ne']
    ring

end Schoenflies

end

section

namespace Schoenflies

private theorem affine_triangle_positive_off_zero_vertex
    (b : AffineBasis (Fin 3) ℝ Plane) (f : Plane →ᵃ[ℝ] ℝ)
    (hf₀ : f (b 0) = 0) (hf₁ : 0 < f (b 1)) (hf₂ : 0 < f (b 2))
    {p : Plane} (hp : p ∈ convexHull ℝ (Set.range b)) (hne : p ≠ b 0) : 0 < f p := by
  have hβ : ∀ i, 0 ≤ b.coord i p := by
    rwa [b.convexHull_eq_nonneg_coord] at hp
  have hvalue := affine_triangle_map_apply_of_vertex_zero b f hf₀ p
  by_contra hfp
  have hsum : f (b 1) * b.coord 1 p + f (b 2) * b.coord 2 p ≤ 0 := by
    rw [← hvalue]
    exact le_of_not_gt hfp
  have hzero₁ : b.coord 1 p = 0 := by
    have hterm : f (b 1) * b.coord 1 p ≤ 0 :=
      (le_add_of_nonneg_right (mul_nonneg hf₂.le (hβ 2))).trans hsum
    exact le_antisymm (nonpos_of_mul_nonpos_right hterm hf₁) (hβ 1)
  have hzero : f p = 0 := le_antisymm (le_of_not_gt hfp) (by
    rw [hvalue]
    exact add_nonneg (mul_nonneg hf₁.le (hβ 1)) (mul_nonneg hf₂.le (hβ 2)))
  exact hne (eq_affine_triangle_vertex_of_map_coord_zero b f hf₀ hf₂.ne' hzero hzero₁)

private theorem exists_affine_triangle_positive_core
    (b : AffineBasis (Fin 3) ℝ Plane) (f₀ f₁ : Plane →ᵃ[ℝ] ℝ)
    (hf₀ : f₀ (b 0) = 0) (hf₀₁ : 0 < f₀ (b 1)) (hf₀₂ : 0 < f₀ (b 2))
    (hf₁ : f₁ (b 1) = 0) (hf₁₀ : 0 < f₁ (b 0)) (hf₁₂ : 0 < f₁ (b 2))
    {U₀ U₁ : Set Plane} (hU₀ : IsOpen U₀) (hU₁ : IsOpen U₁)
    (hb₀ : b 0 ∈ U₀) (hb₁ : b 1 ∈ U₁) :
    ∃ ε : ℝ, 0 < ε ∧ convexHull ℝ (Set.range b) ⊆
      U₀ ∪ U₁ ∪ {p | ε < f₀ p ∧ ε < f₁ p} := by
  let K := convexHull ℝ (Set.range b)
  have hK : IsCompact K := (Set.finite_range b).isCompact_convexHull ℝ
  let c := b.reindex (Equiv.swap (0 : Fin 3) 1)
  have hc0 : c 0 = b 1 := by simp [c]
  have hc1 : c 1 = b 0 := by simp [c]
  have hc2 : c 2 = b 2 := by simp [c, Equiv.swap_apply_def]
  have hcrange : Set.range c = Set.range b := by
    simp only [c, AffineBasis.coe_reindex, EquivLike.range_comp]
  have hpos : ∀ p ∈ K \ (U₀ ∪ U₁), 0 < min (f₀ p) (f₁ p) := by
    intro p hp
    refine lt_min (affine_triangle_positive_off_zero_vertex b f₀ hf₀ hf₀₁ hf₀₂ hp.1 ?_) ?_
    · intro heq
      exact hp.2 (Or.inl (by simpa only [heq] using hb₀))
    · apply affine_triangle_positive_off_zero_vertex c f₁
        (by simpa only [hc0] using hf₁) (by simpa only [hc1] using hf₁₀)
        (by simpa only [hc2] using hf₁₂) (by simpa only [hcrange] using hp.1)
      intro heq
      exact hp.2 (Or.inr (by simpa only [heq, hc0] using hb₁))
  obtain ⟨δ, hδ, hbound⟩ := (hK.diff (hU₀.union hU₁)).exists_forall_le'
    (f₀.continuous_of_finiteDimensional.min f₁.continuous_of_finiteDimensional).continuousOn hpos
  refine ⟨δ / 2, half_pos hδ, ?_⟩
  intro p hp
  by_cases hU : p ∈ U₀ ∪ U₁
  · exact Or.inl hU
  · have h := (half_lt_self hδ).trans_le (hbound p ⟨hp, hU⟩)
    exact Or.inr ⟨h.trans_le (min_le_left _ _), h.trans_le (min_le_right _ _)⟩

end Schoenflies

end

section

open scoped ContDiff Topology

namespace Schoenflies

private theorem fderiv_apply_of_translation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : E → ℝ} {p : E} (hH : DifferentiableAt ℝ H p) (w : E) (c : ℝ)
    (h : ∀ t : ℝ, H (t • w + p) = H p + t * c) :
    fderiv ℝ H p w = c := by
  have hp : HasDerivAt (fun t : ℝ => t • w + p) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).add_const p
  have hd : HasFDerivAt H (fderiv ℝ H p) ((0 : ℝ) • w + p) := by
    simpa using hH.hasFDerivAt
  have he : (fun t : ℝ => H (t • w + p)) = fun t => H p + t * c := funext h
  have hq : HasDerivAt (fun t : ℝ => H (t • w + p)) c 0 := by
    rw [he]
    simpa using (((hasDerivAt_id (0 : ℝ)).mul_const c).const_add (H p))
  exact (hd.comp_hasDerivAt 0 hp).unique hq

private theorem affine_map_smul_add (f : Plane →ᵃ[ℝ] ℝ) (w p : Plane) (t : ℝ) :
    f (t • w + p) = t * f.linear w + f p := by
  change f (t • w +ᵥ p) = _
  rw [f.map_vadd, map_smul]
  rfl

private theorem affine_graph_fderiv_ne_zero
    (b : AffineBasis (Fin 3) ℝ Plane) (f : Plane →ᵃ[ℝ] ℝ)
    (hf₀ : f (b 0) = 0) (hf₁ : f (b 1) ≠ 0)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) {a : ℝ} (ha : a ≠ 0) (p : Plane) :
    fderiv ℝ (fun q => a * (φ (f q) - b.coord 2 q)) p ≠ 0 := by
  let w := (b 2 - b 0) - (f (b 2) / f (b 1)) • (b 1 - b 0)
  have hfv : f.linear w = 0 := by
    change f.linear ((b 2 -ᵥ b 0) - (f (b 2) / f (b 1)) • (b 1 -ᵥ b 0)) = 0
    rw [map_sub, map_smul, f.linearMap_vsub, f.linearMap_vsub, hf₀]
    simp only [vsub_eq_sub, sub_zero, smul_eq_mul]
    field_simp [hf₁]
    ring
  have hβv : (b.coord 2).linear w = 1 := by
    change (b.coord 2).linear
      ((b 2 -ᵥ b 0) - (f (b 2) / f (b 1)) • (b 1 -ᵥ b 0)) = 1
    rw [map_sub, map_smul, (b.coord 2).linearMap_vsub,
      (b.coord 2).linearMap_vsub]
    norm_num [vsub_eq_sub, b.coord_apply, Fin.ext_iff]
  have hf : ContDiff ℝ ∞ f :=
    (⟨f, f.continuous_of_finiteDimensional⟩ : Plane →ᴬ[ℝ] ℝ).contDiff
  have hβ : ContDiff ℝ ∞ (b.coord 2) :=
    (⟨b.coord 2, (b.coord 2).continuous_of_finiteDimensional⟩ : Plane →ᴬ[ℝ] ℝ).contDiff
  have hd := fderiv_apply_of_translation (p := p)
    ((contDiff_const.mul ((hφ.comp hf).sub hβ)).differentiable (by simp)).differentiableAt w (-a)
    (fun t => by
      change a * (φ (f (t • w + p)) - b.coord 2 (t • w + p)) =
        a * (φ (f p) - b.coord 2 p) + t * (-a)
      rw [affine_map_smul_add f w p t, affine_map_smul_add (b.coord 2) w p t,
        hfv, hβv]
      simp only [mul_zero, zero_add, mul_one]
      ring)
  intro hz
  simp only [Function.comp_apply] at hd
  rw [hz, zero_apply] at hd
  exact ha (neg_eq_zero.mp hd.symm)

private theorem barycentric_central_translation
    (b : AffineBasis (Fin 3) ℝ Plane) (σ : ℝ) (p : Plane) (t : ℝ) :
    let w := (b 0 - b 2) + (b 1 - b 2);
    -b.coord 2 (t • w + p) = -b.coord 2 p + t * 2 ∧
      -Real.smoothMax σ (-b.coord 0 (t • w + p)) (-b.coord 1 (t • w + p)) =
        -Real.smoothMax σ (-b.coord 0 p) (-b.coord 1 p) + t := by
  dsimp only
  let w := (b 0 - b 2) + (b 1 - b 2)
  have hβv (i : Fin 3) : (b.coord i).linear w =
      b.coord i (b 0) - b.coord i (b 2) + (b.coord i (b 1) - b.coord i (b 2)) := by
    change (b.coord i).linear ((b 0 -ᵥ b 2) + (b 1 -ᵥ b 2)) = _
    rw [map_add, (b.coord i).linearMap_vsub, (b.coord i).linearMap_vsub]
    simp only [vsub_eq_sub]
  have h₀ : (b.coord 0).linear w = 1 := by
    rw [hβv]
    norm_num [b.coord_apply, Fin.ext_iff]
  have h₁ : (b.coord 1).linear w = 1 := by
    rw [hβv]
    norm_num [b.coord_apply, Fin.ext_iff]
  have h₂ : (b.coord 2).linear w = -2 := by
    rw [hβv]
    norm_num [b.coord_apply, Fin.ext_iff]
  constructor
  · change -b.coord 2 (t • w + p) = -b.coord 2 p + t * 2
    rw [affine_map_smul_add (b.coord 2) w p t, h₂]
    ring
  · change -Real.smoothMax σ (-b.coord 0 (t • w + p)) (-b.coord 1 (t • w + p)) =
      -Real.smoothMax σ (-b.coord 0 p) (-b.coord 1 p) + t
    rw [affine_map_smul_add (b.coord 0) w p t,
      affine_map_smul_add (b.coord 1) w p t, h₀, h₁]
    simp only [mul_one]
    rw [show -(t + b.coord 0 p) = -b.coord 0 p + -t by ring,
      show -(t + b.coord 1 p) = -b.coord 1 p + -t by ring,
      Real.smoothMax.add_right]
    ring

end Schoenflies

end

section

open scoped ContDiff Topology

namespace Schoenflies

private theorem affine_graph_interpolation_fderiv_ne_zero
    (b : AffineBasis (Fin 3) ℝ Plane) (f : Plane →ᵃ[ℝ] ℝ)
    (hf₀ : f (b 0) = 0) (hf₁ : f (b 1) ≠ 0)
    {φ ψ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ)
    {r t : ℝ} (hr : 0 < r) (ht : t ∈ Set.Icc 0 1) (p : Plane) :
    fderiv ℝ (fun q => (1 - t) * (φ (f q) - b.coord 2 q) +
      t * (r * (ψ (f q) - b.coord 2 q))) p ≠ 0 := by
  let a := (1 - t) + t * r
  have ha : 0 < a := by
    change 0 < (1 - t) + t * r
    rcases eq_or_lt_of_le ht.1 with ht₀ | ht₀
    · rw [← ht₀]
      norm_num
    · exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr ht.2) (mul_pos ht₀ hr)
  let Φ := fun x => ((1 - t) * φ x + (t * r) * ψ x) / a
  have hΦ : ContDiff ℝ ∞ Φ :=
    ((contDiff_const.mul hφ).add (contDiff_const.mul hψ)).div_const a
  have he : (fun q => (1 - t) * (φ (f q) - b.coord 2 q) +
      t * (r * (ψ (f q) - b.coord 2 q))) =
      fun q => a * (Φ (f q) - b.coord 2 q) := by
    funext q
    dsimp only [Φ]
    field_simp [ha.ne']
    dsimp only [a]
    ring
  rw [he]
  exact affine_graph_fderiv_ne_zero b f hf₀ hf₁ hΦ ha.ne' p

private theorem matched_endpoint_interpolation_fderiv_ne_zero
    (b : AffineBasis (Fin 3) ℝ Plane) (f : Plane →ᵃ[ℝ] ℝ)
    (hf₀ : f (b 0) = 0) (hf₁ : 0 < f (b 1)) (hf₂ : 0 < f (b 2))
    (s ε : ℝ) {t : ℝ} (ht : t ∈ Set.Icc 0 1) (p : Plane) :
    fderiv ℝ (fun q =>
      (1 - t) * (s * (f q - Real.smoothMax ε (f q) 0) - b.coord 2 q) +
      t * (f (b 2) / f (b 1) * (s * (f q - Real.smoothMax ε (f q) 0) +
        Real.smoothMax ε (f q) 0 / f (b 2) - b.coord 2 q))) p ≠ 0 := by
  have hμ : ContDiff ℝ ∞ (fun x : ℝ => Real.smoothMax ε x 0) :=
    (Real.smoothMax.contDiff ε).comp (contDiff_id.prodMk contDiff_const)
  have hA : ContDiff ℝ ∞ (fun x : ℝ => s * (x - Real.smoothMax ε x 0)) :=
    contDiff_const.mul (contDiff_id.sub hμ)
  exact affine_graph_interpolation_fderiv_ne_zero b f hf₀ hf₁.ne' hA
    (hA.add (hμ.div_const _)) (div_pos hf₂ hf₁) ht p

private theorem barycentric_central_interpolation_fderiv_ne_zero
    (b : AffineBasis (Fin 3) ℝ Plane) (σ : ℝ) {t : ℝ}
    (ht : t ≤ 1) (p : Plane) :
    fderiv ℝ (fun q => (1 - t) * (-b.coord 2 q) +
      t * (-Real.smoothMax σ (-b.coord 0 q) (-b.coord 1 q))) p ≠ 0 := by
  let w := (b 0 - b 2) + (b 1 - b 2)
  have hβ (i : Fin 3) : ContDiff ℝ ∞ (b.coord i) :=
    (⟨b.coord i, (b.coord i).continuous_of_finiteDimensional⟩ : Plane →ᴬ[ℝ] ℝ).contDiff
  have hC : ContDiff ℝ ∞
      (fun q => -Real.smoothMax σ (-b.coord 0 q) (-b.coord 1 q)) :=
    ((Real.smoothMax.contDiff σ).comp ((hβ 0).neg.prodMk (hβ 1).neg)).neg
  have hH : ContDiff ℝ ∞ (fun q => (1 - t) * (-b.coord 2 q) +
      t * (-Real.smoothMax σ (-b.coord 0 q) (-b.coord 1 q))) :=
    (contDiff_const.mul (hβ 2).neg).add (contDiff_const.mul hC)
  have hd : fderiv ℝ (fun q => (1 - t) * (-b.coord 2 q) +
      t * (-Real.smoothMax σ (-b.coord 0 q) (-b.coord 1 q))) p w = 2 - t :=
    fderiv_apply_of_translation (p := p)
      (hH.differentiable (by simp)).differentiableAt w (2 - t) (fun s => by
        change (1 - t) * (-b.coord 2 (s • w + p)) +
          t * (-Real.smoothMax σ (-b.coord 0 (s • w + p)) (-b.coord 1 (s • w + p))) =
          (1 - t) * (-b.coord 2 p) +
            t * (-Real.smoothMax σ (-b.coord 0 p) (-b.coord 1 p)) + s * (2 - t)
        rw [(barycentric_central_translation b σ p s).1,
          (barycentric_central_translation b σ p s).2]
        ring)
  intro hz
  rw [hz, zero_apply] at hd
  linarith

private theorem eqOn_interpolation_fderiv_ne_zero
    {F G : Plane → ℝ × ℝ} {U : Set Plane} (hU : IsOpen U)
    (he : Set.EqOn F G U) (t : ℝ)
    (hG : ∀ p, fderiv ℝ (fun q => (1 - t) * (G q).1 + t * (G q).2) p ≠ 0) :
    ∀ p ∈ U, fderiv ℝ (fun q => (1 - t) * (F q).1 + t * (F q).2) p ≠ 0 := by
  intro p hp
  have h : (fun q => (1 - t) * (F q).1 + t * (F q).2) =ᶠ[𝓝 p]
      (fun q => (1 - t) * (G q).1 + t * (G q).2) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact congrArg (fun z : ℝ × ℝ => (1 - t) * z.1 + t * z.2) (he hq)
  rw [h.fderiv_eq]
  exact hG p

private theorem contDiff_pair_interpolation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → ℝ × ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun q : ℝ × E => (1 - q.1) * (F q.2).1 + q.1 * (F q.2).2) :=
  ((contDiff_const.sub contDiff_fst).mul (hF.fst.comp contDiff_snd)).add
    (contDiff_fst.mul (hF.snd.comp contDiff_snd))

private theorem deriv_pair_interpolation
    {E : Type*} (F : E → ℝ × ℝ) (p : E) (t : ℝ) :
    deriv (fun s => (1 - s) * (F p).1 + s * (F p).2) t = (F p).2 - (F p).1 := by
  have h : HasDerivAt (fun s => (1 - s) * (F p).1 + s * (F p).2)
      ((0 - 1) * (F p).1 + 1 * (F p).2) t :=
    (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).mul_const (F p).1).add
    ((hasDerivAt_id t).mul_const (F p).2)
  simpa only [zero_sub, zero_add, neg_one_mul, one_mul, sub_eq_add_neg, add_comm] using h.deriv

end Schoenflies

end

section

namespace Schoenflies

private theorem matched_profile_eq_smul_of_le_neg
    {ε x : ℝ} (hε : 0 < ε) (hx : x ≤ -ε) (s y r d : ℝ) :
    r * (s * (x - Real.smoothMax ε x 0) + Real.smoothMax ε x 0 / d - y) =
      r * (s * (x - Real.smoothMax ε x 0) - y) := by
  have hx₀ : x ≤ 0 := le_trans hx (neg_nonpos.mpr hε.le)
  have hgap : ε ≤ |x - 0| := by
    rw [sub_zero, abs_of_nonpos hx₀]
    linarith
  have hμ : Real.smoothMax ε x 0 = 0 :=
    (Real.smoothMax.eq_max_of_le hε hgap).trans (max_eq_right hx₀)
  simp only [hμ, sub_zero, zero_div, add_zero]

private theorem pair_interpolation_stationary_of_pos_smul
    {a b r t : ℝ} (hr : 0 < r) (hb : b = r * a) (ht : t ∈ Set.Icc 0 1)
    (hz : (1 - t) * a + t * b = 0) :
    a = 0 ∧ b = 0 ∧ (∀ u : ℝ, (1 - u) * a + u * b = 0) ∧
      (∀ u : ℝ, deriv (fun s => (1 - s) * a + s * b) u = 0) := by
  have hc : 0 < (1 - t) + t * r := by
    rcases eq_or_lt_of_le ht.1 with ht₀ | ht₀
    · rw [← ht₀]
      norm_num
    · exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr ht.2) (mul_pos ht₀ hr)
  have he : ((1 - t) + t * r) * a = 0 := by
    rw [hb] at hz
    nlinarith only [hz]
  have ha : a = 0 := (mul_eq_zero.mp he).resolve_left hc.ne'
  have hb₀ : b = 0 := by rw [hb, ha, mul_zero]
  refine ⟨ha, hb₀, ?_, ?_⟩ <;> intro u <;> simp [ha, hb₀]

private theorem matched_pair_interpolation_stationary_of_left
    {F : ℝ × ℝ} {ε x r t : ℝ} (hε : 0 < ε) (hx : x ≤ -ε)
    (hr : 0 < r) (s y d : ℝ)
    (he : F = (s * (x - Real.smoothMax ε x 0) - y,
      r * (s * (x - Real.smoothMax ε x 0) + Real.smoothMax ε x 0 / d - y)))
    (ht : t ∈ Set.Icc 0 1) (hz : (1 - t) * F.1 + t * F.2 = 0) :
    F.1 = 0 ∧ F.2 = 0 ∧ (∀ u : ℝ, (1 - u) * F.1 + u * F.2 = 0) ∧
      (∀ u : ℝ, deriv (fun s => (1 - s) * F.1 + s * F.2) u = 0) := by
  apply pair_interpolation_stationary_of_pos_smul hr ?_ ht hz
  rw [he]
  exact matched_profile_eq_smul_of_le_neg hε hx s y r d

end Schoenflies

end

section

namespace Schoenflies

private theorem smoothMax_neg_neg_lt_zero_of_small
    {σ x y : ℝ} (hσ : 0 < σ) (hx : 0 < x) (hy : 0 < y)
    (hsmall : 3 * σ < x + y) : Real.smoothMax σ (-x) (-y) < 0 := by
  by_cases hgap : σ ≤ |(-x) - (-y)|
  · rw [Real.smoothMax.eq_max_of_le hσ hgap]
    exact max_lt_iff.mpr ⟨by linarith, by linarith⟩
  · have hg := abs_lt.mp (lt_of_not_ge hgap)
    have hxσ : σ < x := by linarith [hg.2]
    have hyσ : σ < y := by linarith [hg.1]
    have hbound := Real.smoothMax.le_max_add hσ (-x) (-y)
    rcases le_total (-x) (-y) with h | h
    · rw [max_eq_right h] at hbound
      linarith
    · rw [max_eq_left h] at hbound
      linarith

private theorem central_interpolation_zero_mem_triangle
    (b : AffineBasis (Fin 3) ℝ Plane) (f₀ f₁ : Plane →ᵃ[ℝ] ℝ)
    (hf₀ : f₀ (b 0) = 0) (hf₀₁ : 0 < f₀ (b 1)) (hf₀₂ : 0 < f₀ (b 2))
    (hf₁ : f₁ (b 1) = 0) (hf₁₀ : 0 < f₁ (b 0)) (hf₁₂ : 0 < f₁ (b 2))
    {p : Plane} (hp₀ : 0 < f₀ p) (hp₁ : 0 < f₁ p)
    {σ t : ℝ} (hσ : 0 < σ) (hσsmall : 3 * σ < 1) (ht : t ∈ Set.Icc 0 1)
    (hz : (1 - t) * (-b.coord 2 p) +
      t * (-Real.smoothMax σ (-b.coord 0 p) (-b.coord 1 p)) = 0) :
    p ∈ convexHull ℝ (Set.range b) := by
  have he₀ := affine_triangle_map_apply_of_vertex_zero b f₀ hf₀ p
  let c := b.reindex (Equiv.swap (0 : Fin 3) 1)
  have hc0 : c 0 = b 1 := by simp [c]
  have hc1 : c 1 = b 0 := by simp [c]
  have hc2 : c 2 = b 2 := by simp [c, Equiv.swap_apply_def]
  have hcoord1 : c.coord 1 = b.coord 0 := by simp [c]
  have hcoord2 : c.coord 2 = b.coord 2 := by simp [c, Equiv.swap_apply_def]
  have he₁ := affine_triangle_map_apply_of_vertex_zero c f₁
    (by simpa only [hc0] using hf₁) p
  simp only [hc1, hc2, hcoord1, hcoord2] at he₁
  have hpos (h₂ : b.coord 2 p ≤ 0) : 0 < b.coord 0 p ∧ 0 < b.coord 1 p := by
    have h₀ : 0 < f₁ (b 0) * b.coord 0 p := by
      have h := mul_nonpos_of_nonneg_of_nonpos hf₁₂.le h₂
      linarith [he₁]
    have h₁ : 0 < f₀ (b 1) * b.coord 1 p := by
      have h := mul_nonpos_of_nonneg_of_nonpos hf₀₂.le h₂
      linarith [he₀]
    exact ⟨pos_of_mul_pos_right h₀ hf₁₀.le, pos_of_mul_pos_right h₁ hf₀₁.le⟩
  have hsum := b.sum_coord_apply_eq_one p
  simp only [Fin.sum_univ_three] at hsum
  have h₂ : 0 ≤ b.coord 2 p := by
    by_contra hn
    have hneg : b.coord 2 p < 0 := lt_of_not_ge hn
    have hxy := hpos hneg.le
    have hc : 0 < -Real.smoothMax σ (-b.coord 0 p) (-b.coord 1 p) :=
      neg_pos.mpr (smoothMax_neg_neg_lt_zero_of_small hσ hxy.1 hxy.2 (by linarith))
    rcases eq_or_lt_of_le ht.1 with ht₀ | ht₀
    · rw [← ht₀] at hz
      simp only [sub_zero, one_mul, zero_mul, add_zero, neg_eq_zero] at hz
      exact hneg.ne hz
    · have hleft : 0 ≤ (1 - t) * (-b.coord 2 p) :=
        mul_nonneg (sub_nonneg.mpr ht.2) (neg_nonneg.mpr hneg.le)
      have hright := mul_pos ht₀ hc
      linarith
  have h₀₁ : 0 ≤ b.coord 0 p ∧ 0 ≤ b.coord 1 p := by
    rcases eq_or_lt_of_le ht.1 with ht₀ | ht₀
    · rw [← ht₀] at hz
      simp only [sub_zero, one_mul, zero_mul, add_zero, neg_eq_zero] at hz
      exact ⟨(hpos hz.le).1.le, (hpos hz.le).2.le⟩
    · have hc : 0 ≤ -Real.smoothMax σ (-b.coord 0 p) (-b.coord 1 p) := by
        by_contra hn
        have hright := mul_neg_of_pos_of_neg ht₀ (lt_of_not_ge hn)
        have hleft := mul_nonpos_of_nonneg_of_nonpos
          (sub_nonneg.mpr ht.2) (neg_nonpos.mpr h₂)
        linarith
      have hmax := Real.smoothMax.max_le hσ (-b.coord 0 p) (-b.coord 1 p)
      have hleft := (le_max_left (-b.coord 0 p) (-b.coord 1 p)).trans hmax
      have hright := (le_max_right (-b.coord 0 p) (-b.coord 1 p)).trans hmax
      constructor <;> linarith
  rw [b.convexHull_eq_nonneg_coord]
  intro i
  fin_cases i
  · exact h₀₁.1
  · exact h₀₁.2
  · exact h₂

end Schoenflies

end

section

namespace Schoenflies

private theorem smoothMax_sub_left_mem_Icc
    {ε x : ℝ} (hε : 0 < ε) (hx : -ε ≤ x) :
    Real.smoothMax ε x 0 - x ∈ Set.Icc 0 ε := by
  have hl := (le_max_left x 0).trans (Real.smoothMax.max_le hε x 0)
  have hu := Real.smoothMax.monotone_right ε x (show 0 ≤ x + ε by linarith)
  have he : Real.smoothMax ε x (x + ε) = x + ε := by
    rw [Real.smoothMax.eq_max_of_le hε]
    · exact max_eq_right (by linarith)
    · rw [show x - (x + ε) = -ε by ring, abs_neg, abs_of_pos hε]
  rw [he] at hu
  constructor <;> linarith

private theorem weighted_interpolation_zero_mem_Icc
    {a b z r t : ℝ} (hab : a ≤ b) (hr : 0 < r) (ht : t ∈ Set.Icc 0 1)
    (hz : (1 - t) * (a - z) + t * (r * (b - z)) = 0) :
    z ∈ Set.Icc a b := by
  constructor
  · by_contra hn
    have hza : z < a := lt_of_not_ge hn
    have hzb : z < b := hza.trans_le hab
    rcases eq_or_lt_of_le ht.1 with ht₀ | ht₀
    · rw [← ht₀] at hz
      simp only [sub_zero, one_mul, zero_mul, add_zero] at hz
      linarith
    · have hl := mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hza.le)
      have hu := mul_pos ht₀ (mul_pos hr (sub_pos.mpr hzb))
      linarith
  · by_contra hn
    have hbz : b < z := lt_of_not_ge hn
    have haz : a < z := hab.trans_lt hbz
    rcases eq_or_lt_of_le ht.1 with ht₀ | ht₀
    · rw [← ht₀] at hz
      simp only [sub_zero, one_mul, zero_mul, add_zero] at hz
      linarith
    · have hl := mul_nonpos_of_nonneg_of_nonpos
        (sub_nonneg.mpr ht.2) (sub_nonpos.mpr haz.le)
      have hu := mul_neg_of_pos_of_neg ht₀ (mul_neg_of_pos_of_neg hr (sub_neg.mpr hbz))
      linarith

private theorem matched_interpolation_coordinate_bounds
    {ε x s fb fc y z t : ℝ} (hε : 0 < ε) (hx : -ε ≤ x)
    (hfb : 0 < fb) (hfc : 0 < fc) (he : x = fb * y + fc * z)
    (ht : t ∈ Set.Icc 0 1)
    (hz : (1 - t) * (s * (x - Real.smoothMax ε x 0) - z) +
      t * (fc / fb * (s * (x - Real.smoothMax ε x 0) +
        Real.smoothMax ε x 0 / fc - z)) = 0) :
    -((1 + fc * |s|) / fb) * ε ≤ y ∧ -|s| * ε ≤ z := by
  have hm := smoothMax_sub_left_mem_Icc hε hx
  have hm₀ : 0 ≤ Real.smoothMax ε x 0 :=
    (le_max_right x 0).trans (Real.smoothMax.max_le hε x 0)
  have hd : |x - Real.smoothMax ε x 0| ≤ ε := by
    rw [abs_of_nonpos (by linarith [hm.1] : x - Real.smoothMax ε x 0 ≤ 0)]
    linarith [hm.2]
  have hs : |s * (x - Real.smoothMax ε x 0)| ≤ |s| * ε := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hd (abs_nonneg s)
  have hbetween := weighted_interpolation_zero_mem_Icc
    (le_add_of_nonneg_right (div_nonneg hm₀ hfc.le)) (div_pos hfc hfb) ht hz
  have hupper := mul_le_mul_of_nonneg_left hbetween.2 hfc.le
  have hcancel : fc * (Real.smoothMax ε x 0 / fc) = Real.smoothMax ε x 0 :=
    mul_div_cancel₀ _ hfc.ne'
  rw [mul_add, hcancel] at hupper
  have hsupper := mul_le_mul_of_nonneg_left (abs_le.mp hs).2 hfc.le
  have hy : -(1 + fc * |s|) * ε ≤ fb * y := by
    nlinarith [hm.2, he]
  constructor
  · have hdiv := (div_le_iff₀ hfb).mpr
      (show -(1 + fc * |s|) * ε ≤ y * fb by nlinarith [hy])
    calc
      -((1 + fc * |s|) / fb) * ε = (-(1 + fc * |s|) * ε) / fb := by ring
      _ ≤ y := hdiv
  · linarith [(abs_le.mp hs).1, hbetween.1]

end Schoenflies

end

section

namespace Schoenflies

private theorem exists_triangle_point_dist_le_of_coord_lower_bounds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b : AffineBasis (Fin 3) ℝ E) {p : E} {δ : ℝ}
    (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1 / 12)
    (h₁ : -δ ≤ b.coord 1 p) (h₂ : -δ ≤ b.coord 2 p)
    (hgap : (1 : ℝ) / 4 < b.coord 0 p - b.coord 1 p) :
    ∃ q ∈ convexHull ℝ (Set.range b),
      dist p q ≤ δ * (‖b 1 - b 0‖ + ‖b 2 - b 0‖) := by
  classical
  let d₁ := max (-b.coord 1 p) 0
  let d₂ := max (-b.coord 2 p) 0
  have hd₁ : d₁ ∈ Set.Icc 0 δ :=
    ⟨le_max_right _ _, max_le (by linarith) hδ⟩
  have hd₂ : d₂ ∈ Set.Icc 0 δ :=
    ⟨le_max_right _ _, max_le (by linarith) hδ⟩
  have hw₀ : 0 ≤ b.coord 0 p - d₁ - d₂ := by linarith [hd₁.2, hd₂.2]
  have hw₁ : 0 ≤ b.coord 1 p + d₁ := by
    have h : -b.coord 1 p ≤ d₁ := le_max_left _ _
    linarith
  have hw₂ : 0 ≤ b.coord 2 p + d₂ := by
    have h : -b.coord 2 p ≤ d₂ := le_max_left _ _
    linarith
  let w : Fin 3 → ℝ := ![b.coord 0 p - d₁ - d₂, b.coord 1 p + d₁, b.coord 2 p + d₂]
  have hw : ∑ i, w i = 1 := by
    have hsum := b.sum_coord_apply_eq_one p
    simp only [Fin.sum_univ_three] at hsum
    simp only [Fin.sum_univ_three, w, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    linarith
  let q := Finset.univ.affineCombination ℝ b w
  have hq : q ∈ convexHull ℝ (Set.range b) := by
    apply affineCombination_mem_convexHull ?_ hw
    intro i _
    fin_cases i
    · exact hw₀
    · exact hw₁
    · exact hw₂
  have hcoord (i : Fin 3) : b.coord i q = w i :=
    b.coord_apply_combination_of_mem (Finset.mem_univ i) hw
  have he : q - p = d₁ • (b 1 - b 0) + d₂ • (b 2 - b 0) := by
    calc
      q - p = (∑ i, b.coord i q • b i) - ∑ i, b.coord i p • b i := by
        rw [b.linear_combination_coord_eq_self, b.linear_combination_coord_eq_self]
      _ = d₁ • (b 1 - b 0) + d₂ • (b 2 - b 0) := by
        simp only [hcoord, Fin.sum_univ_three, w, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
        module
  refine ⟨q, hq, ?_⟩
  calc
    dist p q = ‖q - p‖ := by rw [dist_comm, dist_eq_norm]
    _ = ‖d₁ • (b 1 - b 0) + d₂ • (b 2 - b 0)‖ := by rw [he]
    _ ≤ ‖d₁ • (b 1 - b 0)‖ + ‖d₂ • (b 2 - b 0)‖ := norm_add_le _ _
    _ = d₁ * ‖b 1 - b 0‖ + d₂ * ‖b 2 - b 0‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hd₁.1, abs_of_nonneg hd₂.1]
    _ ≤ δ * ‖b 1 - b 0‖ + δ * ‖b 2 - b 0‖ :=
      add_le_add (mul_le_mul_of_nonneg_right hd₁.2 (norm_nonneg _))
        (mul_le_mul_of_nonneg_right hd₂.2 (norm_nonneg _))
    _ = δ * (‖b 1 - b 0‖ + ‖b 2 - b 0‖) := by ring

end Schoenflies

end

section

namespace Schoenflies

private theorem endpoint_interpolation_confinement
    (b : AffineBasis (Fin 3) ℝ Plane) (f : Plane →ᵃ[ℝ] ℝ)
    (hf₀ : f (b 0) = 0) (hfb : 0 < f (b 1)) (hfc : 0 < f (b 2)) (s : ℝ) :
    let C := 1 + (1 + f (b 2) * |s|) / f (b 1) + |s|
    0 < C ∧ ∀ (ε : ℝ) (p : Plane) (t : ℝ), 0 < ε → -ε ≤ f p →
      t ∈ Set.Icc 0 1 → C * ε ≤ 1 / 12 →
      (1 : ℝ) / 4 < b.coord 0 p - b.coord 1 p →
      (1 - t) * (s * (f p - Real.smoothMax ε (f p) 0) - b.coord 2 p) +
        t * (f (b 2) / f (b 1) *
          (s * (f p - Real.smoothMax ε (f p) 0) +
            Real.smoothMax ε (f p) 0 / f (b 2) - b.coord 2 p)) = 0 →
      -C * ε ≤ b.coord 1 p ∧ -C * ε ≤ b.coord 2 p ∧
        ∃ q ∈ convexHull ℝ (Set.range b),
          dist p q ≤ C * ε * (‖b 1 - b 0‖ + ‖b 2 - b 0‖) := by
  dsimp only
  let C := 1 + (1 + f (b 2) * |s|) / f (b 1) + |s|
  have hdiv : 0 < (1 + f (b 2) * |s|) / f (b 1) :=
    div_pos (by positivity) hfb
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨hC, ?_⟩
  intro ε p t hε hx ht hsmall hgap hz
  have hbounds := matched_interpolation_coordinate_bounds hε hx hfb hfc
    (affine_triangle_map_apply_of_vertex_zero b f hf₀ p) ht hz
  have h₁ : -C * ε ≤ b.coord 1 p := by
    have hconst : (1 + f (b 2) * |s|) / f (b 1) ≤ C := by
      dsimp [C]
      linarith [abs_nonneg s]
    have h := mul_le_mul_of_nonneg_right hconst hε.le
    linarith [hbounds.1]
  have h₂ : -C * ε ≤ b.coord 2 p := by
    have hconst : |s| ≤ C := by dsimp [C]; linarith
    have h := mul_le_mul_of_nonneg_right hconst hε.le
    linarith [hbounds.2]
  exact ⟨h₁, h₂, exists_triangle_point_dist_le_of_coord_lower_bounds b
    (mul_nonneg hC.le hε.le) hsmall (by simpa only [neg_mul] using h₁)
    (by simpa only [neg_mul] using h₂) hgap⟩

end Schoenflies

end

section

namespace Schoenflies

private theorem matched_pair_interpolation_active_left
    {F : ℝ × ℝ} {ε x r t : ℝ} (hε : 0 < ε) (hr : 0 < r) (s y d : ℝ)
    (he : F = (s * (x - Real.smoothMax ε x 0) - y,
      r * (s * (x - Real.smoothMax ε x 0) + Real.smoothMax ε x 0 / d - y)))
    (ht : t ∈ Set.Icc 0 1) (hz : (1 - t) * F.1 + t * F.2 = 0)
    (hactive : deriv (fun u => (1 - u) * F.1 + u * F.2) t ≠ 0) : -ε < x := by
  by_contra hn
  have hfix := matched_pair_interpolation_stationary_of_left hε (le_of_not_gt hn)
    hr s y d he ht hz
  exact hactive (hfix.2.2.2 t)

private theorem endpoint_zero_mem_interior_cthickening
    (b : AffineBasis (Fin 3) ℝ Plane) (f : Plane →ᵃ[ℝ] ℝ)
    (hf₀ : f (b 0) = 0) (hfb : 0 < f (b 1)) (hfc : 0 < f (b 2))
    (s : ℝ) {η ρ t : ℝ} {p : Plane} (hη : 0 < η)
    (ht : t ∈ Set.Icc 0 1)
    (hsmall : (1 + (1 + f (b 2) * |s|) / f (b 1) + |s|) * η ≤ 1 / 12)
    (hdist : (1 + (1 + f (b 2) * |s|) / f (b 1) + |s|) * η *
      (‖b 1 - b 0‖ + ‖b 2 - b 0‖) < ρ)
    (hgap : (1 : ℝ) / 4 < b.coord 0 p - b.coord 1 p) :
    let A := s * (f p - Real.smoothMax η (f p) 0) - b.coord 2 p
    let B := f (b 2) / f (b 1) *
      (s * (f p - Real.smoothMax η (f p) 0) +
        Real.smoothMax η (f p) 0 / f (b 2) - b.coord 2 p)
    (1 - t) * A + t * B = 0 →
      -η ≤ f p →
      p ∈ interior (Metric.cthickening ρ (convexHull ℝ (Set.range b))) := by
  dsimp only
  intro hz hstrip
  obtain ⟨_, _, q, hq, hpq⟩ := (endpoint_interpolation_confinement b f hf₀ hfb hfc s).2
    η p t hη hstrip ht hsmall hgap hz
  exact Metric.thickening_subset_interior_cthickening ρ _
    (Metric.mem_thickening_iff.mpr ⟨q, hq, hpq.trans_lt hdist⟩)

private theorem endpoint_active_zero_mem_interior_cthickening
    (b : AffineBasis (Fin 3) ℝ Plane) (f : Plane →ᵃ[ℝ] ℝ)
    (hf₀ : f (b 0) = 0) (hfb : 0 < f (b 1)) (hfc : 0 < f (b 2))
    (s : ℝ) {η ρ t : ℝ} {p : Plane} (hη : 0 < η)
    (ht : t ∈ Set.Icc 0 1)
    (hsmall : (1 + (1 + f (b 2) * |s|) / f (b 1) + |s|) * η ≤ 1 / 12)
    (hdist : (1 + (1 + f (b 2) * |s|) / f (b 1) + |s|) * η *
      (‖b 1 - b 0‖ + ‖b 2 - b 0‖) < ρ)
    (hgap : (1 : ℝ) / 4 < b.coord 0 p - b.coord 1 p) :
    let A := s * (f p - Real.smoothMax η (f p) 0) - b.coord 2 p
    let B := f (b 2) / f (b 1) *
      (s * (f p - Real.smoothMax η (f p) 0) +
        Real.smoothMax η (f p) 0 / f (b 2) - b.coord 2 p)
    (1 - t) * A + t * B = 0 →
      deriv (fun u => (1 - u) * A + u * B) t ≠ 0 →
      p ∈ interior (Metric.cthickening ρ (convexHull ℝ (Set.range b))) := by
  dsimp only
  intro hz hactive
  have hstrip := matched_pair_interpolation_active_left hη (div_pos hfc hfb)
    s (b.coord 2 p) (f (b 2)) rfl ht hz hactive
  exact endpoint_zero_mem_interior_cthickening b f hf₀ hfb hfc s hη ht
    hsmall hdist hgap hz hstrip.le

end Schoenflies

end

section

open scoped ContDiff

namespace Schoenflies

private theorem mem_uIcc_of_sign_disagreement {a b z : ℝ}
    (h : ¬ ((a ≤ z ↔ b ≤ z) ∧ (a < z ↔ b < z) ∧ (z = a ↔ z = b))) :
    z ∈ Set.uIcc a b := by
  by_cases hlo : min a b ≤ z
  · refine ⟨hlo, ?_⟩
    by_contra hn
    have haz : a < z := (le_max_left a b).trans_lt (lt_of_not_ge hn)
    have hbz : b < z := (le_max_right a b).trans_lt (lt_of_not_ge hn)
    exact h ⟨iff_of_true haz.le hbz.le, iff_of_true haz hbz,
      iff_of_false haz.ne' hbz.ne'⟩
  · have hza : z < a := (lt_of_not_ge hlo).trans_le (min_le_left a b)
    have hzb : z < b := (lt_of_not_ge hlo).trans_le (min_le_right a b)
    exact False.elim (h ⟨iff_of_false (not_le_of_gt hza) (not_le_of_gt hzb),
      iff_of_false (not_lt_of_ge hza.le) (not_lt_of_ge hzb.le),
      iff_of_false hza.ne hzb.ne⟩)

private theorem endpoint_sign_disagreement_mem_band
    {ε x s z : ℝ} (hε : 0 < ε)
    (h : ¬ ((s * (x - Real.smoothMax ε x 0) ≤ z ↔ s * (x - max x 0) ≤ z) ∧
      (s * (x - Real.smoothMax ε x 0) < z ↔ s * (x - max x 0) < z) ∧
      (z = s * (x - Real.smoothMax ε x 0) ↔ z = s * (x - max x 0)))) :
    |x| < ε ∧ z ∈ Set.uIcc (s * (x - max x 0))
      (s * (x - Real.smoothMax ε x 0)) := by
  refine ⟨?_, ?_⟩
  · by_contra hn
    have he := Real.smoothMax.eq_max_of_le (x := x) (y := 0) hε
      (by simpa only [sub_zero] using le_of_not_gt hn)
    apply h
    rw [he]
    exact ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩
  · rw [Set.uIcc_comm]
    exact mem_uIcc_of_sign_disagreement h

private theorem endpoint_rounding_band_coordinate_bounds
    {ε x s fb fc y z : ℝ} (hε : 0 < ε) (hx : |x| ≤ ε)
    (hfb : 0 < fb) (hfc : 0 < fc) (he : x = fb * y + fc * z)
    (hz : z ∈ Set.uIcc (s * (x - max x 0))
      (s * (x - Real.smoothMax ε x 0))) :
    -((1 + fc * |s|) / fb) * ε ≤ y ∧ -|s| * ε ≤ z := by
  have hm := smoothMax_sub_left_mem_Icc hε (abs_le.mp hx).1
  have hraw : |x - max x 0| ≤ ε := by
    rcases le_total x 0 with hx0 | hx0
    · rw [max_eq_right hx0, sub_zero]
      exact hx
    · rw [max_eq_left hx0, sub_self, abs_zero]
      exact hε.le
  have hsm : |x - Real.smoothMax ε x 0| ≤ ε := by
    rw [abs_of_nonpos (by linarith [hm.1] : x - Real.smoothMax ε x 0 ≤ 0)]
    linarith [hm.2]
  have hscale {a : ℝ} (ha : |a| ≤ ε) : |s * a| ≤ |s| * ε := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ha (abs_nonneg s)
  have hzb : z ∈ Set.Icc (-|s| * ε) (|s| * ε) := by
    apply Set.uIcc_subset_Icc _ _ hz
    · simpa only [Set.mem_Icc, neg_mul] using abs_le.mp (hscale hraw)
    · simpa only [Set.mem_Icc, neg_mul] using abs_le.mp (hscale hsm)
  have hupper := mul_le_mul_of_nonneg_left hzb.2 hfc.le
  have hlow : -(1 + fc * |s|) * ε ≤ fb * y := by
    nlinarith [hupper, (abs_le.mp hx).1]
  refine ⟨?_, hzb.1⟩
  have hdiv := (div_le_iff₀ hfb).mpr
    (show -(1 + fc * |s|) * ε ≤ y * fb by nlinarith [hlow])
  calc
    -((1 + fc * |s|) / fb) * ε = (-(1 + fc * |s|) * ε) / fb := by ring
    _ ≤ y := hdiv

private theorem endpoint_rounding_band_mem_interior_cthickening
    (b : AffineBasis (Fin 3) ℝ Plane) (f : Plane →ᵃ[ℝ] ℝ)
    (hf₀ : f (b 0) = 0) (hfb : 0 < f (b 1)) (hfc : 0 < f (b 2))
    (s : ℝ) {ε ρ : ℝ} {p : Plane} (hε : 0 < ε) (hx : |f p| ≤ ε)
    (hsmall : (1 + (1 + f (b 2) * |s|) / f (b 1) + |s|) * ε ≤ 1 / 12)
    (hdist : (1 + (1 + f (b 2) * |s|) / f (b 1) + |s|) * ε *
      (‖b 1 - b 0‖ + ‖b 2 - b 0‖) < ρ)
    (hgap : (1 : ℝ) / 4 < b.coord 0 p - b.coord 1 p)
    (hz : b.coord 2 p ∈ Set.uIcc (s * (f p - max (f p) 0))
      (s * (f p - Real.smoothMax ε (f p) 0))) :
    p ∈ interior (Metric.cthickening ρ (convexHull ℝ (Set.range b))) := by
  let C := 1 + (1 + f (b 2) * |s|) / f (b 1) + |s|
  have hdiv : 0 < (1 + f (b 2) * |s|) / f (b 1) := div_pos (by positivity) hfb
  have hC : 0 < C := by dsimp [C]; positivity
  have hb := endpoint_rounding_band_coordinate_bounds hε hx hfb hfc
    (affine_triangle_map_apply_of_vertex_zero b f hf₀ p) hz
  have h₁ : -C * ε ≤ b.coord 1 p := by
    have hc : (1 + f (b 2) * |s|) / f (b 1) ≤ C := by
      dsimp [C]
      linarith [abs_nonneg s]
    have h := mul_le_mul_of_nonneg_right hc hε.le
    linarith [hb.1]
  have h₂ : -C * ε ≤ b.coord 2 p := by
    have hc : |s| ≤ C := by dsimp [C]; linarith
    have h := mul_le_mul_of_nonneg_right hc hε.le
    linarith [hb.2]
  obtain ⟨q, hq, hpq⟩ := exists_triangle_point_dist_le_of_coord_lower_bounds b
    (mul_nonneg hC.le hε.le) hsmall (by simpa only [neg_mul] using h₁)
    (by simpa only [neg_mul] using h₂) hgap
  exact Metric.thickening_subset_interior_cthickening ρ _
    (Metric.mem_thickening_iff.mpr ⟨q, hq, hpq.trans_lt hdist⟩)

private theorem endpoint_signs_eq_outside_cthickening
    (b : AffineBasis (Fin 3) ℝ Plane) (f : Plane →ᵃ[ℝ] ℝ)
    (hf₀ : f (b 0) = 0) (hfb : 0 < f (b 1)) (hfc : 0 < f (b 2))
    (s : ℝ) {ε ρ : ℝ} {p : Plane} (hε : 0 < ε)
    (hsmall : (1 + (1 + f (b 2) * |s|) / f (b 1) + |s|) * ε ≤ 1 / 12)
    (hdist : (1 + (1 + f (b 2) * |s|) / f (b 1) + |s|) * ε *
      (‖b 1 - b 0‖ + ‖b 2 - b 0‖) < ρ)
    (hgap : (1 : ℝ) / 4 < b.coord 0 p - b.coord 1 p)
    (hp : p ∉ interior (Metric.cthickening ρ (convexHull ℝ (Set.range b)))) :
    (s * (f p - Real.smoothMax ε (f p) 0) ≤ b.coord 2 p ↔
      s * (f p - max (f p) 0) ≤ b.coord 2 p) ∧
    (s * (f p - Real.smoothMax ε (f p) 0) < b.coord 2 p ↔
      s * (f p - max (f p) 0) < b.coord 2 p) ∧
    (b.coord 2 p = s * (f p - Real.smoothMax ε (f p) 0) ↔
      b.coord 2 p = s * (f p - max (f p) 0)) := by
  by_contra hn
  obtain ⟨hx, hz⟩ := endpoint_sign_disagreement_mem_band hε hn
  exact hp (endpoint_rounding_band_mem_interior_cthickening b f hf₀ hfb hfc s
    hε hx.le hsmall hdist hgap hz)

private theorem mul_sub_max_zero (s x : ℝ) :
    s * (x - max x 0) = if x < 0 then s * x else 0 := by
  by_cases hx : x < 0
  · rw [if_pos hx, max_eq_right hx.le, sub_zero]
  · rw [if_neg hx, max_eq_left (le_of_not_gt hx), sub_self, mul_zero]

private theorem exists_fixed_cover_small_matched_interpolation
    (b : AffineBasis (Fin 3) ℝ Plane) (f₀ f₁ : Plane →ᵃ[ℝ] ℝ)
    (hf₀ : f₀ (b 0) = 0) (hfb : 0 < f₀ (b 1)) (hfc₀ : 0 < f₀ (b 2))
    (hf₁ : f₁ (b 1) = 0) (hfa : 0 < f₁ (b 0)) (hfc₁ : 0 < f₁ (b 2))
    (s₀ s₁ : ℝ) {U₀ U₁ : Set Plane} (hU₀ : IsOpen U₀) (hU₁ : IsOpen U₁)
    (hb₀ : b 0 ∈ U₀) (hb₁ : b 1 ∈ U₁)
    (hgap₀ : ∀ p ∈ U₀, (1 : ℝ) / 4 < b.coord 0 p - b.coord 1 p)
    (hgap₁ : ∀ p ∈ U₁, (1 : ℝ) / 4 < b.coord 1 p - b.coord 0 p)
    (N : Set Plane) (hN : IsOpen N)
    (hKN : convexHull ℝ (Set.range b) \ {b 0, b 1} ⊆ N) :
    let K := convexHull ℝ (Set.range b)
    let G := fun p => (-b.coord 2 p,
      -Real.smoothMax (1 / 4) (-b.coord 0 p) (-b.coord 1 p))
    let F₀ := fun η p => (s₀ * (f₀ p - Real.smoothMax η (f₀ p) 0) - b.coord 2 p,
      f₀ (b 2) / f₀ (b 1) * (s₀ * (f₀ p - Real.smoothMax η (f₀ p) 0) +
        Real.smoothMax η (f₀ p) 0 / f₀ (b 2) - b.coord 2 p))
    let F₁ := fun η p => (s₁ * (f₁ p - Real.smoothMax η (f₁ p) 0) - b.coord 2 p,
      f₁ (b 2) / f₁ (b 0) * (s₁ * (f₁ p - Real.smoothMax η (f₁ p) 0) +
        Real.smoothMax η (f₁ p) 0 / f₁ (b 2) - b.coord 2 p))
    ∃ (ε₀ ε : ℝ) (J : Set Plane),
      let V := {p | ε₀ < f₀ p ∧ ε₀ < f₁ p} ∩ N
      0 < ε₀ ∧ 0 < ε ∧ ε ≤ ε₀ ∧ IsCompact J ∧ K ⊆ interior J ∧
      J ⊆ U₀ ∪ U₁ ∪ V ∧ K ⊆ U₀ ∪ U₁ ∪ V ∧
      (∀ η ∈ Set.Ioc 0 ε, Set.EqOn (F₀ η) G (U₀ ∩ V)) ∧
      (∀ η ∈ Set.Ioc 0 ε, Set.EqOn (F₁ η) G (U₁ ∩ V)) ∧
      (∀ η ∈ Set.Ioc 0 ε, ∀ t ∈ Set.Icc 0 1, ∀ p ∈ U₀,
        (1 - t) * (F₀ η p).1 + t * (F₀ η p).2 = 0 →
        -η ≤ f₀ p →
        p ∈ interior J) ∧
      (∀ η ∈ Set.Ioc 0 ε, ∀ t ∈ Set.Icc 0 1, ∀ p ∈ U₁,
        (1 - t) * (F₁ η p).1 + t * (F₁ η p).2 = 0 →
        -η ≤ f₁ p →
        p ∈ interior J) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ V,
        (1 - t) * (G p).1 + t * (G p).2 = 0 → p ∈ K) ∧
      (∀ η ∈ Set.Ioc 0 ε, ∀ p ∈ U₀, p ∉ interior J →
        (s₀ * (f₀ p - Real.smoothMax η (f₀ p) 0) ≤ b.coord 2 p ↔
          s₀ * (f₀ p - max (f₀ p) 0) ≤ b.coord 2 p) ∧
        (s₀ * (f₀ p - Real.smoothMax η (f₀ p) 0) < b.coord 2 p ↔
          s₀ * (f₀ p - max (f₀ p) 0) < b.coord 2 p) ∧
        (b.coord 2 p = s₀ * (f₀ p - Real.smoothMax η (f₀ p) 0) ↔
          b.coord 2 p = s₀ * (f₀ p - max (f₀ p) 0))) ∧
      (∀ η ∈ Set.Ioc 0 ε, ∀ p ∈ U₁, p ∉ interior J →
        (s₁ * (f₁ p - Real.smoothMax η (f₁ p) 0) ≤ b.coord 2 p ↔
          s₁ * (f₁ p - max (f₁ p) 0) ≤ b.coord 2 p) ∧
        (s₁ * (f₁ p - Real.smoothMax η (f₁ p) 0) < b.coord 2 p ↔
          s₁ * (f₁ p - max (f₁ p) 0) < b.coord 2 p) ∧
        (b.coord 2 p = s₁ * (f₁ p - Real.smoothMax η (f₁ p) 0) ↔
          b.coord 2 p = s₁ * (f₁ p - max (f₁ p) 0))) := by
  dsimp only
  let K := convexHull ℝ (Set.range b)
  have hK : IsCompact K := (Set.finite_range b).isCompact_convexHull ℝ
  obtain ⟨ε₀, hε₀, hcover₀⟩ := exists_affine_triangle_positive_core b f₀ f₁
    hf₀ hfb hfc₀ hf₁ hfa hfc₁ hU₀ hU₁ hb₀ hb₁
  let V := {p | ε₀ < f₀ p ∧ ε₀ < f₁ p} ∩ N
  have hV : IsOpen V :=
    ((isOpen_lt continuous_const f₀.continuous_of_finiteDimensional).inter
      (isOpen_lt continuous_const f₁.continuous_of_finiteDimensional)).inter hN
  have hcover : K ⊆ U₀ ∪ U₁ ∪ V := by
    intro p hp
    by_cases hp₀ : p = b 0
    · exact Or.inl (Or.inl (hp₀.symm ▸ hb₀))
    by_cases hp₁ : p = b 1
    · exact Or.inl (Or.inr (hp₁.symm ▸ hb₁))
    rcases hcover₀ hp with (h₀ | h₁) | hV
    · exact Or.inl (Or.inl h₀)
    · exact Or.inl (Or.inr h₁)
    · exact Or.inr ⟨hV, hKN ⟨hp, by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨hp₀, hp₁⟩⟩⟩
  obtain ⟨ρ, hρ, hρsub⟩ := hK.exists_cthickening_subset_open
    ((hU₀.union hU₁).union hV) hcover
  let J := Metric.cthickening ρ K
  have hJ : IsCompact J := hK.cthickening
  have hKJ : K ⊆ interior J :=
    (Metric.self_subset_thickening hρ K).trans
      (Metric.thickening_subset_interior_cthickening ρ K)
  let c := b.reindex (Equiv.swap (0 : Fin 3) 1)
  have hc0 : c 0 = b 1 := by simp [c]
  have hc1 : c 1 = b 0 := by simp [c]
  have hc2 : c 2 = b 2 := by simp [c, Equiv.swap_apply_def]
  have hcoord0 : c.coord 0 = b.coord 1 := by simp [c]
  have hcoord1 : c.coord 1 = b.coord 0 := by simp [c]
  have hcoord2 : c.coord 2 = b.coord 2 := by simp [c, Equiv.swap_apply_def]
  have hcrange : Set.range c = Set.range b := by
    simp only [c, AffineBasis.coe_reindex, EquivLike.range_comp]
  let C₀ := 1 + (1 + f₀ (b 2) * |s₀|) / f₀ (b 1) + |s₀|
  let C₁ := 1 + (1 + f₁ (b 2) * |s₁|) / f₁ (b 0) + |s₁|
  have hC₀ : 0 < C₀ := (endpoint_interpolation_confinement b f₀ hf₀ hfb hfc₀ s₀).1
  have hC₁ : 0 < C₁ := by
    simpa only [hc1, hc2] using
      (endpoint_interpolation_confinement c f₁ (by simpa only [hc0] using hf₁)
        (by simpa only [hc1] using hfa) (by simpa only [hc2] using hfc₁) s₁).1
  let L₀ := ‖b 1 - b 0‖ + ‖b 2 - b 0‖
  let L₁ := ‖b 0 - b 1‖ + ‖b 2 - b 1‖
  have hL₀ : 0 ≤ L₀ := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hL₁ : 0 ≤ L₁ := add_nonneg (norm_nonneg _) (norm_nonneg _)
  let B := 1 + C₀ + C₁ + C₀ * L₀ + C₁ * L₁
  have hB : 0 < B := by dsimp [B]; positivity
  have hC₀B : C₀ ≤ B := by
    dsimp only [B]
    linarith only [hC₀, hC₁, mul_nonneg hC₀.le hL₀, mul_nonneg hC₁.le hL₁]
  have hC₁B : C₁ ≤ B := by
    dsimp only [B]
    linarith only [hC₀, hC₁, mul_nonneg hC₀.le hL₀, mul_nonneg hC₁.le hL₁]
  have hC₀LB : C₀ * L₀ ≤ B := by
    dsimp only [B]
    linarith only [hC₀, hC₁, mul_nonneg hC₀.le hL₀, mul_nonneg hC₁.le hL₁]
  have hC₁LB : C₁ * L₁ ≤ B := by
    dsimp only [B]
    linarith only [hC₀, hC₁, mul_nonneg hC₀.le hL₀, mul_nonneg hC₁.le hL₁]
  obtain ⟨δ, hδ, hδbound⟩ := exists_pos_mul_lt
    (lt_min (by norm_num : (0 : ℝ) < 1 / 12) hρ) B
  let ε := min ε₀ δ
  have hε : 0 < ε := lt_min hε₀ hδ
  have hε₀bound : ε ≤ ε₀ := min_le_left _ _
  have hbound {η : ℝ} (hη : η ∈ Set.Ioc 0 ε) :
      C₀ * η ≤ 1 / 12 ∧ C₁ * η ≤ 1 / 12 ∧
        C₀ * η * L₀ < ρ ∧ C₁ * η * L₁ < ρ := by
    have hηδ : η ≤ δ := hη.2.trans (min_le_right _ _)
    have hBη : B * η < min (1 / 12) ρ :=
      (mul_le_mul_of_nonneg_left hηδ hB.le).trans_lt hδbound
    have hsmall := hBη.trans_le (min_le_left _ _)
    have hdist := hBη.trans_le (min_le_right _ _)
    refine ⟨((mul_le_mul_of_nonneg_right hC₀B hη.1.le).trans_lt hsmall).le,
      ((mul_le_mul_of_nonneg_right hC₁B hη.1.le).trans_lt hsmall).le, ?_, ?_⟩
    · have h := (mul_le_mul_of_nonneg_right hC₀LB hη.1.le).trans_lt hdist
      calc
        C₀ * η * L₀ = C₀ * L₀ * η := mul_right_comm _ _ _
        _ < ρ := h
    · have h := (mul_le_mul_of_nonneg_right hC₁LB hη.1.le).trans_lt hdist
      calc
        C₁ * η * L₁ = C₁ * L₁ * η := mul_right_comm _ _ _
        _ < ρ := h
  refine ⟨ε₀, ε, J, hε₀, hε, hε₀bound, hJ, hKJ, hρsub, hcover, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro η hη p hp
    have h := (matched_endpoint_defining_functions_overlap b f₀ hf₀ hfb hfc₀ s₀ hη.1
      (by norm_num : (0 : ℝ) < 1 / 4)).2.2.2.2.2 p
      ⟨(hη.2.trans hε₀bound).trans_lt hp.2.1.1, hgap₀ p hp.1⟩
    exact Prod.ext h.1 h.2.1
  · intro η hη p hp
    have h := (matched_endpoint_defining_functions_overlap c f₁
      (by simpa only [hc0] using hf₁) (by simpa only [hc1] using hfa)
      (by simpa only [hc2] using hfc₁) s₁ hη.1
      (by norm_num : (0 : ℝ) < 1 / 4)).2.2.2.2.2 p
      ⟨(hη.2.trans hε₀bound).trans_lt hp.2.1.2,
        by simpa only [hcoord0, hcoord1] using hgap₁ p hp.1⟩
    simp only [hc1, hc2, hcoord0, hcoord1, hcoord2] at h
    refine Prod.ext h.1 (h.2.1.trans ?_)
    exact congrArg Neg.neg (Real.smoothMax.comm (by norm_num : (1 / 4 : ℝ) ≠ 0) _ _)
  · intro η hη t ht p hp
    exact endpoint_zero_mem_interior_cthickening b f₀ hf₀ hfb hfc₀ s₀ hη.1 ht
      (hbound hη).1 (hbound hη).2.2.1 (hgap₀ p hp)
  · intro η hη t ht p hp hz hstrip
    have h := endpoint_zero_mem_interior_cthickening c f₁
      (by simpa only [hc0] using hf₁) (by simpa only [hc1] using hfa)
      (by simpa only [hc2] using hfc₁) s₁ hη.1 ht
      (by simpa only [hc1, hc2] using (hbound hη).2.1)
      (by simpa only [hc0, hc1, hc2] using (hbound hη).2.2.2)
      (by simpa only [hcoord0, hcoord1] using hgap₁ p hp)
      (by simpa only [hc1, hc2, hcoord2] using hz)
      hstrip
    simpa only [hcrange] using h
  · intro t ht p hp hz
    exact central_interpolation_zero_mem_triangle b f₀ f₁ hf₀ hfb hfc₀ hf₁ hfa hfc₁
      (hε₀.trans hp.1.1) (hε₀.trans hp.1.2) (by norm_num) (by norm_num) ht hz
  · intro η hη p hp hpJ
    exact endpoint_signs_eq_outside_cthickening b f₀ hf₀ hfb hfc₀ s₀ hη.1
      (hbound hη).1 (hbound hη).2.2.1 (hgap₀ p hp) hpJ
  · intro η hη p hp hpJ
    have h := endpoint_signs_eq_outside_cthickening c f₁
      (by simpa only [hc0] using hf₁) (by simpa only [hc1] using hfa)
      (by simpa only [hc2] using hfc₁) s₁ hη.1
      (by simpa only [hc1, hc2] using (hbound hη).2.1)
      (by simpa only [hc0, hc1, hc2] using (hbound hη).2.2.2)
      (by simpa only [hcoord0, hcoord1] using hgap₁ p hp)
      (by simpa only [hcrange] using hpJ)
    simpa only [hcoord2] using h

end Schoenflies

end

section

open scoped ContDiff

namespace Schoenflies

private theorem exists_open_matched_pair_eq_smul
    {F : Plane → ℝ × ℝ} (f : Plane →ᵃ[ℝ] ℝ) {ε : ℝ} (hε : 0 < ε)
    (s r d : ℝ) (β : Plane → ℝ) {U : Set Plane} (hU : IsOpen U)
    (he : Set.EqOn F (fun q => (s * (f q - Real.smoothMax ε (f q) 0) - β q,
      r * (s * (f q - Real.smoothMax ε (f q) 0) +
        Real.smoothMax ε (f q) 0 / d - β q))) U)
    {p : Plane} (hp : p ∈ U) (hfp : f p < -ε) :
    ∃ N : Set Plane, IsOpen N ∧ p ∈ N ∧ N ⊆ U ∩ {q | f q < -ε} ∧
      Set.EqOn (fun q => (F q).2) (fun q => r * (F q).1) N := by
  refine ⟨U ∩ {q | f q < -ε},
    hU.inter (isOpen_lt f.continuous_of_finiteDimensional continuous_const),
    ⟨hp, hfp⟩, Set.Subset.refl _, ?_⟩
  intro q hq
  change (F q).2 = r * (F q).1
  rw [he hq.1]
  exact matched_profile_eq_smul_of_le_neg hε hq.2.le s (β q) r d

theorem PrePolygon.exists_regular_interpolation_near_one_edge_free_triangle
    {m : ℕ} (P : PrePolygon m)
    (M : LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh)
    (hfrontier : frontier M.toPlaneComplex.support = P.carrier)
    (T : M.Triangle) (k : Fin 3) (hfree : M.IsOneEdgeFreeTriangle T k) :
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
        -Real.smoothMax (1 / 4) (-b.coord 0 p) (-b.coord 1 p))) V ∧
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
          (p ∈ frontier M.toPlaneComplex.support ↔ (F p).1 = 0)) := by
  dsimp only
  let b := LeanEval.Topology.ClassificationOfSurfaces.Moise.affineBasisOfTriangle
    (M.freeTriangleOrder T k) (M.freeTriangleOrder_affineIndependent T k)
  obtain ⟨v₀, v₁, r₀, r₁, f₀, f₁, _, _, hr₀, hr₁, hdisj, hs₀, hs₁,
    hf₀, hfb, hfc₀, hfv₀, hf₁, hfa, hfc₁, hfv₁, _, _, hgraph₀, hgraph₁⟩ :=
    P.exists_affine_graph_charts_of_one_edge_free_triangle M hfrontier T k hfree
  let U₀ := Metric.ball (b 0) r₀ ∩ {p | (1 : ℝ) / 4 < b.coord 0 p - b.coord 1 p}
  let U₁ := Metric.ball (b 1) r₁ ∩ {p | (1 : ℝ) / 4 < b.coord 1 p - b.coord 0 p}
  have hβ (i : Fin 3) : ContDiff ℝ ∞ (b.coord i) :=
    (⟨b.coord i, (b.coord i).continuous_of_finiteDimensional⟩ : Plane →ᴬ[ℝ] ℝ).contDiff
  have hU₀ : IsOpen U₀ := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const ((hβ 0).sub (hβ 1)).continuous)
  have hU₁ : IsOpen U₁ := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const ((hβ 1).sub (hβ 0)).continuous)
  have hdisjU : Disjoint U₀ U₁ :=
    hdisj.mono Set.inter_subset_left Set.inter_subset_left
  have hb₀ : b 0 ∈ U₀ := ⟨Metric.mem_ball_self hr₀, by norm_num [b.coord_apply]⟩
  have hb₁ : b 1 ∈ U₁ := ⟨Metric.mem_ball_self hr₁, by norm_num [b.coord_apply]⟩
  have htriangle : convexHull ℝ (Set.range b) = M.triangleCarrier T.1 := by
    change convexHull ℝ (Set.range ((M.position ∘ M.orderedVertex T) ∘ Equiv.swap 2 k)) = _
    rw [EquivLike.range_comp, Set.range_comp, M.range_orderedVertex T]
    rfl
  let N := (interior M.toPlaneComplex.support ∩ {p | 0 < b.coord 2 p}) ∪
    ((M.eraseTriangle T.1).toPlaneComplex.supportᶜ ∩
      {p | 0 < b.coord 0 p ∧ 0 < b.coord 1 p})
  obtain ⟨hN, hNC, hNsides⟩ := M.one_edge_free_central_neighborhood T k hfree
  change IsOpen N at hN
  have hKN : convexHull ℝ (Set.range b) \ {b 0, b 1} ⊆ N := by
    rw [htriangle]
    exact hNC
  obtain ⟨ε₀, ε, J, _, hε, hεle, hJ, hKJ, hJcover, hcover,
    heleft, heright, htrace₀, htrace₁, hcentral, hsign₀, hsign₁⟩ :=
    exists_fixed_cover_small_matched_interpolation b f₀ f₁ hf₀ hfb hfc₀ hf₁ hfa hfc₁
      (b.coord 2 v₀ / f₀ v₀) (b.coord 2 v₁ / f₁ v₁) hU₀ hU₁ hb₀ hb₁
      (fun _ hp => hp.2) (fun _ hp => hp.2) N hN hKN
  let V := {p | ε₀ < f₀ p ∧ ε₀ < f₁ p} ∩ N
  have hV : IsOpen V :=
    ((isOpen_lt continuous_const f₀.continuous_of_finiteDimensional).inter
      (isOpen_lt continuous_const f₁.continuous_of_finiteDimensional)).inter hN
  let s₀ := b.coord 2 v₀ / f₀ v₀
  let s₁ := b.coord 2 v₁ / f₁ v₁
  have hleft := matched_endpoint_defining_functions_overlap b f₀ hf₀ hfb hfc₀ s₀ hε
    (show (0 : ℝ) < 1 / 4 by norm_num)
  let c := b.reindex (Equiv.swap (0 : Fin 3) 1)
  have hc0 : c 0 = b 1 := by simp [c]
  have hc1 : c 1 = b 0 := by simp [c]
  have hc2 : c 2 = b 2 := by simp [c, Equiv.swap_apply_def]
  have hcoord0 : c.coord 0 = b.coord 1 := by simp [c]
  have hcoord1 : c.coord 1 = b.coord 0 := by simp [c]
  have hcoord2 : c.coord 2 = b.coord 2 := by simp [c, Equiv.swap_apply_def]
  have hright := matched_endpoint_defining_functions_overlap c f₁
    (by simpa only [hc0] using hf₁) (by simpa only [hc1] using hfa)
    (by simpa only [hc2] using hfc₁) s₁ hε
    (show (0 : ℝ) < 1 / 4 by norm_num)
  simp only [hc1, hc2, hcoord0, hcoord1, hcoord2] at hright
  rw [htriangle] at hcover hKJ hcentral
  obtain ⟨F, W, hF, hW, hJW, he₀, he₁, he₂⟩ :=
    DifferentialGeometry.Analysis.exists_contDiff_glued_near_compact hJ hU₀ hU₁ hV
      hdisjU hJcover
      _ _ _ (hleft.1.prodMk hleft.2.1) (hright.1.prodMk hright.2.1)
      ((hβ 2).neg.prodMk hleft.2.2.1)
      (heleft ε ⟨hε, le_rfl⟩) (heright ε ⟨hε, le_rfl⟩)
  have hKW : M.triangleCarrier T.1 ⊆ W :=
    hKJ.trans (interior_subset.trans hJW)
  have hbK (i : Fin 3) : b i ∈ M.triangleCarrier T.1 := by
    rw [← htriangle]
    exact subset_convexHull ℝ _ ⟨i, rfl⟩
  have hregH (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
      ∀ p ∈ (W ∩ U₀) ∪ (W ∩ U₁) ∪ (W ∩ V),
        fderiv ℝ (fun q => (1 - t) * (F q).1 + t * (F q).2) p ≠ 0 := by
    have hreg₀ := eqOn_interpolation_fderiv_ne_zero (hW.inter hU₀) he₀ t
      (matched_endpoint_interpolation_fderiv_ne_zero b f₀ hf₀ hfb hfc₀ _ ε ht)
    have hreg₁ := eqOn_interpolation_fderiv_ne_zero (hW.inter hU₁) he₁ t (fun p => by
      have h := matched_endpoint_interpolation_fderiv_ne_zero c f₁
        (by simpa only [hc0] using hf₁) (by simpa only [hc1] using hfa)
        (by simpa only [hc2] using hfc₁) (b.coord 2 v₁ / f₁ v₁) ε ht p
      simpa only [hc1, hc2, hcoord2] using h)
    have hregV := eqOn_interpolation_fderiv_ne_zero (hW.inter hV) he₂ t
      (barycentric_central_interpolation_fderiv_ne_zero b (1 / 4) ht.2)
    intro p hp
    rcases hp with (hp₀ | hp₁) | hpV
    · exact hreg₀ p hp₀
    · exact hreg₁ p hp₁
    · exact hregV p hpV
  have hreg : ∀ p ∈ (W ∩ U₀) ∪ (W ∩ U₁) ∪ (W ∩ V),
      fderiv ℝ (fun q => (F q).1) p ≠ 0 ∧ fderiv ℝ (fun q => (F q).2) p ≠ 0 := by
    intro p hp
    constructor
    · simpa only [sub_zero, one_mul, zero_mul, add_zero] using
        hregH 0 (show (0 : ℝ) ∈ Set.Icc 0 1 from ⟨le_rfl, by norm_num⟩) p hp
    · simpa only [sub_self, zero_mul, one_mul, zero_add] using
        hregH 1 (show (1 : ℝ) ∈ Set.Icc 0 1 from ⟨by norm_num, le_rfl⟩) p hp
  have hcentralF (t : ℝ) (ht : t ∈ Set.Icc 0 1) (p : Plane) (hp : p ∈ W ∩ V)
      (hz : (1 - t) * (F p).1 + t * (F p).2 = 0) : p ∈ M.triangleCarrier T.1 := by
    rw [he₂ hp] at hz
    exact hcentral t ht p hp.2 hz
  have hweak₀ (t : ℝ) (ht : t ∈ Set.Icc 0 1) (p : Plane) (hp : p ∈ W ∩ U₀)
      (hz : (1 - t) * (F p).1 + t * (F p).2 = 0) (hf : -ε ≤ f₀ p) :
      p ∈ interior J := by
    rw [he₀ hp] at hz
    exact htrace₀ ε ⟨hε, le_rfl⟩ t ht p hp.2 hz hf
  have hweak₁ (t : ℝ) (ht : t ∈ Set.Icc 0 1) (p : Plane) (hp : p ∈ W ∩ U₁)
      (hz : (1 - t) * (F p).1 + t * (F p).2 = 0) (hf : -ε ≤ f₁ p) :
      p ∈ interior J := by
    rw [he₁ hp] at hz
    exact htrace₁ ε ⟨hε, le_rfl⟩ t ht p hp.2 hz hf
  refine ⟨v₀, v₁, f₀, f₁, ε, W ∩ U₀, W ∩ U₁, W ∩ V, F,
    hε, hF, hW.inter hU₀, hW.inter hU₁, hW.inter hV,
    ⟨hKW (hbK 0), hb₀⟩, ⟨hKW (hbK 1), hb₁⟩,
    hdisjU.mono Set.inter_subset_right Set.inter_subset_right, ?_, hs₀, hs₁,
    hf₀, hfb, hfc₀, hfv₀, hf₁, hfa, hfc₁, hfv₁,
    fun _ hp => hp.2.2, fun _ hp => hp.2.2, he₀, he₁, he₂,
    fun p hp => hgraph₀ p hp.2.1, fun p hp => hgraph₁ p hp.2.1,
    hreg, contDiff_pair_interpolation hF, (fun t p => deriv_pair_interpolation F p t),
    by intro p; simp, by intro p; simp, hregH, ?_, ?_,
    (fun _ hp => ⟨hεle.trans_lt hp.2.1.1, hεle.trans_lt hp.2.1.2⟩),
    hcentralF, J, hJ, hKJ, ?_, ?_, hweak₀, hweak₁, ?_,
    (fun p hp => hNsides p hp.2.2), ?_⟩
  · intro p hp
    rcases hcover hp with (hp₀ | hp₁) | hpV
    · exact Or.inl (Or.inl ⟨hKW hp, hp₀⟩)
    · exact Or.inl (Or.inr ⟨hKW hp, hp₁⟩)
    · exact Or.inr ⟨hKW hp, hpV⟩
  · intro t ht p hp hfp hz
    exact matched_pair_interpolation_stationary_of_left hε hfp (div_pos hfc₀ hfb)
      _ _ _ (he₀ hp) ht hz
  · intro t ht p hp hfp hz
    exact matched_pair_interpolation_stationary_of_left hε hfp (div_pos hfc₁ hfa)
      _ _ _ (he₁ hp) ht hz
  · intro p hp
    rcases hJcover hp with (hp₀ | hp₁) | hpV
    · exact Or.inl (Or.inl ⟨hJW hp, hp₀⟩)
    · exact Or.inl (Or.inr ⟨hJW hp, hp₁⟩)
    · exact Or.inr ⟨hJW hp, hpV⟩
  · intro t ht p hp hz hactive
    rcases hp with (hp₀ | hp₁) | hpV
    · exact hweak₀ t ht p hp₀ hz
        (matched_pair_interpolation_active_left hε (div_pos hfc₀ hfb)
          _ _ _ (he₀ hp₀) ht hz hactive).le
    · exact hweak₁ t ht p hp₁ hz
        (matched_pair_interpolation_active_left hε (div_pos hfc₁ hfa)
          _ _ _ (he₁ hp₁) ht hz hactive).le
    · exact hKJ (hcentralF t ht p hpV hz)
  · intro t ht p hp hz hpJ
    rcases hp with (hp₀ | hp₁) | hpV
    · have hf : f₀ p < -ε := lt_of_not_ge
        (fun hn => hpJ (interior_subset (hweak₀ t ht p hp₀ hz hn)))
      exact Or.inl ⟨hp₀, hf, exists_open_matched_pair_eq_smul f₀ hε
        _ _ _ _ (hW.inter hU₀) he₀ hp₀ hf⟩
    · have hf : f₁ p < -ε := lt_of_not_ge
        (fun hn => hpJ (interior_subset (hweak₁ t ht p hp₁ hz hn)))
      exact Or.inr ⟨hp₁, hf, exists_open_matched_pair_eq_smul f₁ hε
        _ _ _ _ (hW.inter hU₁) he₁ hp₁ hf⟩
    · exact False.elim (hpJ (interior_subset (hKJ (hcentralF t ht p hpV hz))))
  · intro p hp hpJ
    rcases hp with (hp₀ | hp₁) | hpV
    · have h := hsign₀ ε ⟨hε, le_rfl⟩ p hp₀.2 hpJ
      rw [mul_sub_max_zero] at h
      rw [he₀ hp₀]
      dsimp only
      refine ⟨?_, ?_, ?_⟩
      · rw [sub_nonpos]
        exact (hgraph₀ p hp₀.2.1).1.trans h.1.symm
      · rw [sub_neg]
        exact (hgraph₀ p hp₀.2.1).2.1.trans h.2.1.symm
      · rw [sub_eq_zero]
        exact ((hgraph₀ p hp₀.2.1).2.2.1.trans h.2.2.symm).trans eq_comm
    · have h := hsign₁ ε ⟨hε, le_rfl⟩ p hp₁.2 hpJ
      rw [mul_sub_max_zero] at h
      rw [he₁ hp₁]
      dsimp only
      refine ⟨?_, ?_, ?_⟩
      · rw [sub_nonpos]
        exact (hgraph₁ p hp₁.2.1).1.trans h.1.symm
      · rw [sub_neg]
        exact (hgraph₁ p hp₁.2.1).2.1.trans h.2.1.symm
      · rw [sub_eq_zero]
        exact ((hgraph₁ p hp₁.2.1).2.2.1.trans h.2.2.symm).trans eq_comm
    · rw [he₂ hpV]
      dsimp only
      simpa only [neg_nonpos, neg_lt_zero, neg_eq_zero] using hNsides p hpV.2.2

end Schoenflies

end
