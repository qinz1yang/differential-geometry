import DifferentialGeometry.Topology.PlanarJordan.LocalSides
import DifferentialGeometry.External.Schoenflies.PrePolygonArc
import DifferentialGeometry.External.Schoenflies.PrePolygonSep
import DifferentialGeometry.External.ClassificationOfSurfaces.Moise.LineSubdivision
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Tactic.Module
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp
import DifferentialGeometry.External.ClassificationOfSurfaces.TriangleMeshCrosscut

section
open Set Metric

namespace Schoenflies

open LeanEval.Topology.ClassificationOfSurfaces.Moise

theorem PrePolygon.exists_ball_carrier_eq_incident_edges
    {m : ℕ} (P : PrePolygon m) (i : ZMod (m + 3)) :
    ∃ r > 0, ball (P.vertex i) r ∩ P.carrier =
      ball (P.vertex i) r ∩ (P.edge (i - 1) ∪ P.edge i) := by
  classical
  let s := Finset.univ.filter fun j : ZMod (m + 3) => j ≠ i - 1 ∧ j ≠ i
  let C : Set Plane := ⋃ j ∈ s, P.edge j
  have hC : IsClosed C :=
    (s.isCompact_biUnion (fun _ _ => isCompact_segment _ _)).isClosed
  have hiC : P.vertex i ∉ C := by
    intro hi
    obtain ⟨j, hj, hij⟩ := Set.mem_iUnion₂.mp hi
    obtain ⟨hjpred, hji⟩ := (Finset.mem_filter.mp hj).2
    rcases PrePolygon.vertex_mem_edge_elim hij with he | he
    · exact hji (P.vertex_inj he).symm
    · change P.vertex i = P.vertex (j + 1) at he
      exact hjpred (by rw [P.vertex_inj he, add_sub_cancel_right])
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hC.isOpen_compl (P.vertex i) hiC
  refine ⟨r, hr, Set.Subset.antisymm ?_ ?_⟩
  · rintro p ⟨hp, hpC⟩
    obtain ⟨j, hpj⟩ := Set.mem_iUnion.mp hpC
    refine ⟨hp, ?_⟩
    by_cases hjpred : j = i - 1
    · exact Or.inl (hjpred ▸ hpj)
    by_cases hji : j = i
    · exact Or.inr (hji ▸ hpj)
    exact False.elim (hball hp (Set.mem_iUnion₂.mpr
      ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjpred, hji⟩, hpj⟩))
  · rintro p ⟨hp, hpedge⟩
    exact ⟨hp, hpedge.elim (fun h => P.edge_subset_carrier _ h) (fun h => P.edge_subset_carrier _ h)⟩

private theorem PrePolygon.exists_affine_vertex_model
    {m : ℕ} (P : PrePolygon m) (i : ZMod (m + 3)) :
    ∃ (e : Plane ≃ᵃ[ℝ] Plane) (r d : ℝ), 0 < r ∧ (d = 0 ∨ d = 1) ∧
      e (P.vertex i) = Plane.mk 0 0 ∧
      e (P.vertex (i - 1)) = Plane.mk (-1) 0 ∧
      e (P.vertex (i + 1)) = Plane.mk r (d * r) ∧
      (d = 0 ↔ Plane.det (P.vertex (i - 1) - P.vertex i)
        (P.vertex (i + 1) - P.vertex i) = 0) ∧ (d = 1 → r = 1) := by
  classical
  by_cases hd : Plane.det (P.vertex (i - 1) - P.vertex i)
      (P.vertex (i + 1) - P.vertex i) = 0
  · let a := P.vertex i
    let v := P.vertex (i - 1)
    let w := a + Plane.perp (v - a)
    have hva : v ≠ a := by
      intro he
      have hi := P.vertex_inj he
      exact ClosedPolygon.succ_ne_self (i - 1) (by simpa only [sub_add_cancel] using hi.symm)
    have hp : AffineIndependent ℝ ![a, v, w] := by
      apply affineIndependent_plane_triple_of_det_ne_zero
      change Plane.det (v - a) (w - a) ≠ 0
      change Plane.det (v - a) (a + Plane.perp (v - a) - a) ≠ 0
      rw [add_sub_cancel_left, Plane.det_perp_self]
      exact pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hva))
    have hq : AffineIndependent ℝ ![Plane.mk 0 0, Plane.mk (-1) 0, Plane.mk 0 1] := by
      apply affineIndependent_plane_triple_of_det_ne_zero
      norm_num [Plane.mk, PiLp.sub_apply]
    let e := triangleAffineEquiv ![a, v, w]
      ![Plane.mk 0 0, Plane.mk (-1) 0, Plane.mk 0 1] hp hq
    have he0 : e (P.vertex i) = Plane.mk 0 0 := triangleAffineEquiv_apply _ _ hp hq 0
    have he1 : e (P.vertex (i - 1)) = Plane.mk (-1) 0 :=
      triangleAffineEquiv_apply _ _ hp hq 1
    have hmem : e (P.vertex i) ∈ openSegment ℝ
        (e (P.vertex (i - 1))) (e (P.vertex (i + 1))) := by
      change e.toAffineMap (P.vertex i) ∈ openSegment ℝ
        (e.toAffineMap (P.vertex (i - 1))) (e.toAffineMap (P.vertex (i + 1)))
      rw [← image_openSegment ℝ e.toAffineMap]
      exact Set.mem_image_of_mem e.toAffineMap (P.mem_openSegment_of_det_eq_zero i hd)
    rw [he0, he1] at hmem
    obtain ⟨u, v, hu, hv, _, he⟩ := hmem
    have heX := congrArg (fun q : Plane => q 0) he
    have heY := congrArg (fun q : Plane => q 1) he
    change u * (-1) + v * (e (P.vertex (i + 1))) 0 = 0 at heX
    change u * 0 + v * (e (P.vertex (i + 1))) 1 = 0 at heY
    simp only [mul_zero, zero_add] at heY
    have hr : 0 < e (P.vertex (i + 1)) 0 := by nlinarith
    have hy : e (P.vertex (i + 1)) 1 = 0 := (mul_eq_zero.mp heY).resolve_left hv.ne'
    refine ⟨e, e (P.vertex (i + 1)) 0, 0, hr, Or.inl rfl, he0, he1, ?_, ?_, by norm_num⟩
    · ext j
      fin_cases j
      · rfl
      · change (e (P.vertex (i + 1))) 1 = 0 * (e (P.vertex (i + 1))) 0
        rw [zero_mul]
        exact hy
    · exact ⟨fun _ => hd, fun _ => rfl⟩
  · have hp : AffineIndependent ℝ
        ![P.vertex i, P.vertex (i - 1), P.vertex (i + 1)] :=
      affineIndependent_plane_triple_of_det_ne_zero hd
    have hq : AffineIndependent ℝ ![Plane.mk 0 0, Plane.mk (-1) 0, Plane.mk 1 1] := by
      apply affineIndependent_plane_triple_of_det_ne_zero
      norm_num [Plane.mk, PiLp.sub_apply]
    let e := triangleAffineEquiv ![P.vertex i, P.vertex (i - 1), P.vertex (i + 1)]
      ![Plane.mk 0 0, Plane.mk (-1) 0, Plane.mk 1 1] hp hq
    refine ⟨e, 1, 1, zero_lt_one, Or.inr rfl,
      triangleAffineEquiv_apply _ _ hp hq 0, triangleAffineEquiv_apply _ _ hp hq 1, ?_, ?_, fun _ => rfl⟩
    · change e (P.vertex (i + 1)) = Plane.mk 1 (1 * 1)
      rw [mul_one]
      exact triangleAffineEquiv_apply _ _ hp hq 2
    · exact ⟨fun h => False.elim (one_ne_zero h), fun h => False.elim (hd h)⟩

theorem mem_union_segments_iff_max {a r d : ℝ} (ha : 0 < a) (hr : 0 < r)
    {p : Plane} :
    p ∈ segment ℝ (Plane.mk (-a) 0) (Plane.mk 0 0) ∪
        segment ℝ (Plane.mk 0 0) (Plane.mk r (d * r)) ↔
      (p 0 ∈ Icc (-a) r ∧ p 1 = d * max (p 0) 0) := by
  constructor
  · rintro (⟨u, v, hu, hv, huv, he⟩ | ⟨u, v, hu, hv, huv, he⟩)
    · have heX := congrArg (fun q : Plane => q 0) he
      have heY := congrArg (fun q : Plane => q 1) he
      change u * (-a) + v * 0 = p 0 at heX
      change u * 0 + v * 0 = p 1 at heY
      simp only [mul_zero, zero_add] at heY
      refine ⟨⟨by nlinarith, by nlinarith⟩, ?_⟩
      rw [max_eq_right (by nlinarith : p 0 ≤ 0), mul_zero]
      exact heY.symm
    · have heX := congrArg (fun q : Plane => q 0) he
      have heY := congrArg (fun q : Plane => q 1) he
      change u * 0 + v * r = p 0 at heX
      change u * 0 + v * (d * r) = p 1 at heY
      simp only [mul_zero, zero_add] at heX heY
      refine ⟨⟨by nlinarith, by nlinarith⟩, ?_⟩
      rw [max_eq_left (by nlinarith : 0 ≤ p 0)]
      calc
        p 1 = v * (d * r) := heY.symm
        _ = d * (v * r) := by ring
        _ = d * p 0 := by rw [heX]
  · rintro ⟨hp, he⟩
    by_cases hx : p 0 ≤ 0
    · refine Or.inl ⟨-p 0 / a, 1 + p 0 / a, div_nonneg (by linarith) ha.le, ?_, by ring, ?_⟩
      · have hbound : -1 ≤ p 0 / a := (le_div_iff₀ ha).mpr (by nlinarith [hp.1])
        linarith
      · rw [max_eq_right hx, mul_zero] at he
        ext j
        fin_cases j
        · change (-p 0 / a) * (-a) + (1 + p 0 / a) * 0 = p 0
          field_simp
          ring
        · change (-p 0 / a) * 0 + (1 + p 0 / a) * 0 = p 1
          simpa only [mul_zero, zero_add] using he.symm
    · have hxpos : 0 < p 0 := lt_of_not_ge hx
      refine Or.inr ⟨1 - p 0 / r, p 0 / r, ?_, (div_pos hxpos hr).le, by ring, ?_⟩
      · have := (div_le_one hr).mpr hp.2
        linarith
      · rw [max_eq_left hxpos.le] at he
        have hcancel : p 0 / r * r = p 0 := div_mul_cancel₀ _ hr.ne'
        ext j
        fin_cases j
        · change (1 - p 0 / r) * 0 + p 0 / r * r = p 0
          simpa only [mul_zero, zero_add] using hcancel
        · change (1 - p 0 / r) * 0 + p 0 / r * (d * r) = p 1
          rw [mul_zero, zero_add]
          calc
            p 0 / r * (d * r) = d * (p 0 / r * r) := by ring
            _ = p 1 := by rw [hcancel, he]

private theorem PrePolygon.exists_affine_vertex_graph
    {m : ℕ} (P : PrePolygon m) (i : ZMod (m + 3)) :
    ∃ (e : Plane ≃ᵃ[ℝ] Plane) (U : Set Plane) (r d : ℝ),
      IsOpen U ∧ Convex ℝ U ∧ P.vertex i ∈ U ∧ 0 < r ∧ (d = 0 ∨ d = 1) ∧
      e (P.vertex i) = Plane.mk 0 0 ∧
      e (P.vertex (i - 1)) = Plane.mk (-1) 0 ∧
      e (P.vertex (i + 1)) = Plane.mk r (d * r) ∧
      (d = 0 ↔ Plane.det (P.vertex (i - 1) - P.vertex i)
        (P.vertex (i + 1) - P.vertex i) = 0) ∧
      (d = 1 → r = 1) ∧
      ∀ p ∈ U, (p ∈ P.carrier ↔ (e p) 1 = d * max ((e p) 0) 0) := by
  obtain ⟨ρ, hρ, hlocal⟩ := P.exists_ball_carrier_eq_incident_edges i
  obtain ⟨e, r, d, hr, hd, he0, he1, he2, hstraight, hunit⟩ := P.exists_affine_vertex_model i
  let f := cartesianX.comp e.toAffineMap
  let U := ball (P.vertex i) ρ ∩ f ⁻¹' Ioo (-1) r
  have hU : IsOpen U := isOpen_ball.inter
    (isOpen_Ioo.preimage f.continuous_of_finiteDimensional)
  have hUc : Convex ℝ U := (convex_ball _ _).inter ((convex_Ioo (-1 : ℝ) r).affine_preimage f)
  have hiU : P.vertex i ∈ U := by
    refine ⟨mem_ball_self hρ, ?_⟩
    change -1 < (e (P.vertex i)) 0 ∧ (e (P.vertex i)) 0 < r
    rw [he0]
    exact ⟨by norm_num, hr⟩
  refine ⟨e, U, r, d, hU, hUc, hiU, hr, hd, he0, he1, he2, hstraight, hunit, ?_⟩
  intro p hp
  have hpI : -1 < (e p) 0 ∧ (e p) 0 < r := hp.2
  have hedge : p ∈ P.carrier ↔ p ∈ P.edge (i - 1) ∪ P.edge i := by
    constructor
    · intro hpC
      have hpL : p ∈ ball (P.vertex i) ρ ∩ P.carrier := ⟨hp.1, hpC⟩
      rw [hlocal] at hpL
      exact hpL.2
    · exact fun h => h.elim (fun hp => P.edge_subset_carrier _ hp) (fun hp => P.edge_subset_carrier _ hp)
  have himage : e '' (P.edge (i - 1) ∪ P.edge i) =
      segment ℝ (Plane.mk (-1) 0) (Plane.mk 0 0) ∪
        segment ℝ (Plane.mk 0 0) (Plane.mk r (d * r)) := by
    rw [Set.image_union]
    change e.toAffineMap '' segment ℝ (P.vertex (i - 1)) (P.vertex (i - 1 + 1)) ∪
      e.toAffineMap '' segment ℝ (P.vertex i) (P.vertex (i + 1)) = _
    rw [sub_add_cancel, image_segment ℝ e.toAffineMap, image_segment ℝ e.toAffineMap]
    change segment ℝ (e (P.vertex (i - 1))) (e (P.vertex i)) ∪
      segment ℝ (e (P.vertex i)) (e (P.vertex (i + 1))) = _
    rw [he0, he1, he2]
  rw [hedge, ← e.injective.mem_set_image, himage]
  rw [mem_union_segments_iff_max zero_lt_one hr]
  exact and_iff_right ⟨hpI.1.le, hpI.2.le⟩

end Schoenflies

end

section
open Set Metric

namespace Schoenflies

open LeanEval.Topology.ClassificationOfSurfaces.Moise

private theorem isPreconnected_affine_max_sides
    (e : Plane ≃ᵃ[ℝ] Plane) {U : Set Plane} {a : Plane} {d : ℝ}
    (hU : IsOpen U) (hcU : Convex ℝ U) (haU : a ∈ U)
    (hea : e a = Plane.mk 0 0) (hd : d = 0 ∨ d = 1) :
    IsPreconnected (U ∩ {p | d * max ((e p) 0) 0 < (e p) 1}) ∧
      IsPreconnected (U ∩ {p | (e p) 1 < d * max ((e p) 0) 0}) := by
  let f := cartesianX.comp e.toAffineMap
  let g := cartesianY.comp e.toAffineMap
  have hcpos : ∀ h : Plane →ᵃ[ℝ] ℝ,
      Convex ℝ (U ∩ {p | 0 < h p}) := fun h =>
    hcU.inter ((convex_Ioi (0 : ℝ)).affine_preimage h)
  have hcneg : ∀ h : Plane →ᵃ[ℝ] ℝ,
      Convex ℝ (U ∩ {p | h p < 0}) := fun h =>
    hcU.inter ((convex_Iio (0 : ℝ)).affine_preimage h)
  rcases hd with rfl | rfl
  · simpa only [zero_mul] using ⟨(hcpos g).isPreconnected, (hcneg g).isPreconnected⟩
  · have hpos : U ∩ {p | 1 * max ((e p) 0) 0 < (e p) 1} =
        (U ∩ {p | 0 < g p}) ∩ {p | 0 < (g - f) p} := by
      ext p
      change (p ∈ U ∧ 1 * max (f p) 0 < g p) ↔
        (p ∈ U ∧ 0 < g p) ∧ 0 < g p - f p
      rw [one_mul, max_lt_iff]
      constructor <;> rintro ⟨h₁, h₂⟩
      · exact ⟨⟨h₁, h₂.2⟩, sub_pos.mpr h₂.1⟩
      · exact ⟨h₁.1, sub_pos.mp h₂, h₁.2⟩
    have hneg : U ∩ {p | (e p) 1 < 1 * max ((e p) 0) 0} =
        (U ∩ {p | g p < 0}) ∪ (U ∩ {p | (g - f) p < 0}) := by
      ext p
      change (p ∈ U ∧ g p < 1 * max (f p) 0) ↔
        (p ∈ U ∧ g p < 0) ∨ (p ∈ U ∧ g p - f p < 0)
      rw [one_mul, lt_max_iff]
      constructor
      · rintro ⟨hp, h | h⟩
        · exact Or.inr ⟨hp, sub_neg.mpr h⟩
        · exact Or.inl ⟨hp, h⟩
      · rintro (⟨hp, h⟩ | ⟨hp, h⟩)
        · exact ⟨hp, Or.inr h⟩
        · exact ⟨hp, Or.inl (sub_neg.mp h)⟩
    have hmap : Continuous (fun t : ℝ => e.symm (Plane.mk 0 (-t))) :=
      e.symm.toAffineMap.continuous_of_finiteDimensional.comp (by fun_prop)
    have hzero : (0 : ℝ) ∈ (fun t : ℝ => e.symm (Plane.mk 0 (-t))) ⁻¹' U := by
      change e.symm (Plane.mk 0 (-0)) ∈ U
      rw [neg_zero, ← hea, e.symm_apply_apply]
      exact haU
    obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp (hU.preimage hmap) 0 hzero
    let p := e.symm (Plane.mk 0 (-(δ / 2)))
    have hpU : p ∈ U := hδU (by
      rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)]
      exact half_lt_self hδ)
    have hpg : g p = -(δ / 2) := by
      change (e (e.symm (Plane.mk 0 (-(δ / 2))))) 1 = _
      rw [e.apply_symm_apply]
      rfl
    have hpf : f p = 0 := by
      change (e (e.symm (Plane.mk 0 (-(δ / 2))))) 0 = _
      rw [e.apply_symm_apply]
      rfl
    rw [hpos, hneg]
    refine ⟨((hcpos g).inter
      ((convex_Ioi (0 : ℝ)).affine_preimage (g - f))).isPreconnected, ?_⟩
    apply IsPreconnected.union' (s := U ∩ {p | g p < 0})
      (t := U ∩ {p | (g - f) p < 0}) ?_ (hcneg g).isPreconnected
        (hcneg (g - f)).isPreconnected
    refine ⟨p, ⟨hpU, ?_⟩, hpU, ?_⟩
    · change g p < 0
      rw [hpg]
      linarith
    · change g p - f p < 0
      rw [hpg, hpf]
      linarith

theorem PrePolygon.exists_affine_vertex_graph_sides_normalized
    {m : ℕ} (P : PrePolygon m) (i : ZMod (m + 3)) :
    ∃ (e : Plane ≃ᵃ[ℝ] Plane) (U : Set Plane) (r d σ : ℝ),
      IsOpen U ∧ Convex ℝ U ∧ P.vertex i ∈ U ∧ 0 < r ∧
      (d = 0 ∨ d = 1) ∧ (σ = -1 ∨ σ = 1) ∧
      e (P.vertex i) = Plane.mk 0 0 ∧
      e (P.vertex (i - 1)) = Plane.mk (-1) 0 ∧
      e (P.vertex (i + 1)) = Plane.mk r (d * r) ∧
      (d = 0 ↔ Plane.det (P.vertex (i - 1) - P.vertex i)
        (P.vertex (i + 1) - P.vertex i) = 0) ∧
      (d = 1 → r = 1) ∧
      ∀ p ∈ U,
        (p ∈ closure (inside P.carrier) ↔
          0 ≤ σ * ((e p) 1 - d * max ((e p) 0) 0)) ∧
        (p ∈ interior (closure (inside P.carrier)) ↔
          0 < σ * ((e p) 1 - d * max ((e p) 0) 0)) ∧
        (p ∈ frontier (closure (inside P.carrier)) ↔
          (e p) 1 = d * max ((e p) 0) 0) ∧
        (p ∈ P.carrier ↔ (e p) 1 = d * max ((e p) 0) 0) := by
  obtain ⟨e, U, r, d, hU, hcU, hiU, hr, hd, he0, he1, he2, hstraight, hunit, hgraph⟩ :=
    P.exists_affine_vertex_graph i
  let g : Plane → ℝ := fun p => (e p) 1 - d * max ((e p) 0) 0
  have hz : ∀ p ∈ U, p ∈ P.carrier ↔ g p = 0 := by
    intro p hp
    rw [hgraph p hp]
    exact sub_eq_zero.symm
  obtain ⟨hpos, hneg⟩ := isPreconnected_affine_max_sides e hU hcU hiU he0 hd
  have hpos' : IsPreconnected (U ∩ {p | 0 < g p}) := by
    simpa only [g, sub_pos] using hpos
  have hneg' : IsPreconnected (U ∩ {p | g p < 0}) := by
    simpa only [g, sub_neg] using hneg
  obtain ⟨σ, hσ, hside⟩ : ∃ σ : ℝ, (σ = -1 ∨ σ = 1) ∧
      ∀ p ∈ U, p ∈ inside P.carrier ↔ 0 < σ * g p := by
    rcases P.isSeparating_carrier.local_side_sign hU (P.vertex_mem_carrier i) hiU g hz
      hpos' hneg' with h | h
    · exact ⟨1, Or.inr rfl, fun p hp => by simpa only [one_mul] using h p hp⟩
    · refine ⟨-1, Or.inl rfl, fun p hp => ?_⟩
      simpa only [neg_one_mul, neg_pos] using h p hp
  have hσne : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  refine ⟨e, U, r, d, σ, hU, hcU, hiU, hr, hd, hσ, he0, he1, he2, hstraight, hunit, ?_⟩
  intro p hp
  have hweak : p ∈ closure (inside P.carrier) ↔ 0 ≤ σ * g p := by
    rw [(IsRegionOf.inside P.carrier).closure_eq P.isSeparating_carrier,
      Set.mem_union, hside p hp, hz p hp]
    have hm : σ * g p = 0 ↔ g p = 0 := mul_eq_zero.trans (or_iff_right hσne)
    rw [← hm]
    simpa only [eq_comm] using
      (le_iff_lt_or_eq : 0 ≤ σ * g p ↔ (0 < σ * g p ∨ 0 = σ * g p)).symm
  have hstrict : p ∈ interior (closure (inside P.carrier)) ↔ 0 < σ * g p := by
    rw [interior_closure_inside_of_separating P.isSeparating_carrier]
    exact hside p hp
  refine ⟨hweak, hstrict, ?_, hgraph p hp⟩
  rw [isClosed_closure.frontier_eq]
  change (p ∈ closure (inside P.carrier) ∧ p ∉ interior (closure (inside P.carrier))) ↔ _
  rw [hweak, hstrict, not_lt]
  constructor
  · intro h
    have hg : g p = 0 := (mul_eq_zero.mp (le_antisymm h.2 h.1)).resolve_left hσne
    exact sub_eq_zero.mp hg
  · intro h
    have hg : g p = 0 := sub_eq_zero.mpr h
    rw [hg, mul_zero]
    exact ⟨le_rfl, le_rfl⟩

theorem PrePolygon.exists_affine_vertex_graph_sides
    {m : ℕ} (P : PrePolygon m) (i : ZMod (m + 3)) :
    ∃ (e : Plane ≃ᵃ[ℝ] Plane) (U : Set Plane) (r d σ : ℝ),
      IsOpen U ∧ Convex ℝ U ∧ P.vertex i ∈ U ∧ 0 < r ∧
      (d = 0 ∨ d = 1) ∧ (σ = -1 ∨ σ = 1) ∧
      e (P.vertex i) = Plane.mk 0 0 ∧
      e (P.vertex (i - 1)) = Plane.mk (-1) 0 ∧
      e (P.vertex (i + 1)) = Plane.mk r (d * r) ∧
      (d = 0 ↔ Plane.det (P.vertex (i - 1) - P.vertex i)
        (P.vertex (i + 1) - P.vertex i) = 0) ∧
      ∀ p ∈ U,
        (p ∈ closure (inside P.carrier) ↔
          0 ≤ σ * ((e p) 1 - d * max ((e p) 0) 0)) ∧
        (p ∈ interior (closure (inside P.carrier)) ↔
          0 < σ * ((e p) 1 - d * max ((e p) 0) 0)) ∧
        (p ∈ frontier (closure (inside P.carrier)) ↔
          (e p) 1 = d * max ((e p) 0) 0) ∧
        (p ∈ P.carrier ↔ (e p) 1 = d * max ((e p) 0) 0) := by
  obtain ⟨e, U, r, d, σ, hU, hcU, hiU, hr, hd, hσ, he0, he1, he2,
    hstraight, _, hside⟩ := P.exists_affine_vertex_graph_sides_normalized i
  exact ⟨e, U, r, d, σ, hU, hcU, hiU, hr, hd, hσ, he0, he1, he2, hstraight, hside⟩

end Schoenflies

end
