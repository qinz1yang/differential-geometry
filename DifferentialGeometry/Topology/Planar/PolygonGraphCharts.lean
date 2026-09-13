import DifferentialGeometry.External.ClassificationOfSurfaces.PrePolygonDeletion
import DifferentialGeometry.External.ClassificationOfSurfaces.Moise.LineSubdivision
import Mathlib.Analysis.Convex.Combination
import DifferentialGeometry.External.Schoenflies.Graph.K33Land
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Topology.Order.DenselyOrdered

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
