import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Connected.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set
open scoped ENNReal NNReal

namespace DifferentialGeometry.Topology

theorem exists_pos_isSeparated_of_finite
    {X : Type*} [EMetricSpace X] {A : Set X} (hA : A.Finite) :
    ∃ r : ℝ≥0, 0 < r ∧ Metric.IsSeparated r A := by
  let P : Set (X × X) := {z ∈ A ×ˢ A | z.1 ≠ z.2}
  have hP : P.Finite := (hA.prod hA).subset fun _ hz => hz.1
  rcases P.eq_empty_or_nonempty with hemp | hne
  · refine ⟨1, one_pos, ?_⟩
    intro x hx y hy hxy
    have hp : (x, y) ∈ P := ⟨⟨hx, hy⟩, hxy⟩
    rw [hemp] at hp
    exact hp.elim
  · obtain ⟨z, hz, hmin⟩ := Set.exists_min_image P (fun z => edist z.1 z.2) hP hne
    obtain ⟨r, hr, hrd⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp
      (edist_pos.mpr hz.2)
    refine ⟨r, by exact_mod_cast hr, ?_⟩
    intro x hx y hy hxy
    exact hrd.trans_le (hmin (x, y) ⟨⟨hx, hy⟩, hxy⟩)

private theorem packingNumber_ne_top_of_totallyBounded
    {X : Type*} [PseudoEMetricSpace X] {C : Set X} (hC : TotallyBounded C)
    {r : ℝ≥0} (hr : 0 < r) : Metric.packingNumber r C ≠ ⊤ := by
  obtain ⟨A, _, hA, hcover⟩ :=
    Metric.exists_finite_isCover_of_totallyBounded (show r / 2 ≠ 0 by positivity) hC
  have hpack : Metric.packingNumber r C ≤ A.encard := by
    calc
      Metric.packingNumber r C = Metric.packingNumber (2 * (r / 2)) C := by congr 1; ring
      _ ≤ Metric.externalCoveringNumber (r / 2) C :=
        Metric.packingNumber_two_mul_le_externalCoveringNumber _ _
      _ ≤ A.encard := hcover.externalCoveringNumber_le_encard
  exact ne_top_of_le_ne_top (Set.encard_ne_top_iff.mpr hA) hpack

theorem exists_finite_separated_cover_containing
    {X : Type*} [PseudoEMetricSpace X] {C A : Set X}
    (hC : TotallyBounded C) (hA : A.Finite) (hAC : A ⊆ C)
    {r : ℝ≥0} (hr : 0 < r) (hsep : Metric.IsSeparated r A) :
    ∃ S : Set X, A ⊆ S ∧ S ⊆ C ∧ S.Finite ∧
      Metric.IsSeparated r S ∧ Metric.IsCover r C S := by
  classical
  let D : Set X := {x ∈ C | ∀ y ∈ A, (r : ℝ≥0∞) < edist x y}
  have hDC : D ⊆ C := fun _ hx => hx.1
  have hpack := packingNumber_ne_top_of_totallyBounded (hC.subset hDC) hr
  let B : Set X := Metric.maximalSeparatedSet r D
  have hBD : B ⊆ D := Metric.maximalSeparatedSet_subset
  have hBfin : B.Finite := Set.encard_ne_top_iff.mp (by
    rw [show B = Metric.maximalSeparatedSet r D from rfl,
      Metric.encard_maximalSeparatedSet hpack]
    exact hpack)
  have hBsep : Metric.IsSeparated r B := Metric.isSeparated_maximalSeparatedSet
  have hBcover : Metric.IsCover r D B := Metric.isCover_maximalSeparatedSet hpack
  refine ⟨A ∪ B, subset_union_left, union_subset hAC (hBD.trans hDC),
    hA.union hBfin, ?_, ?_⟩
  · change (A ∪ B).Pairwise (fun x y => (r : ℝ≥0∞) < edist x y)
    refine (Set.pairwise_union (s := A) (t := B)
      (r := fun x y => (r : ℝ≥0∞) < edist x y)).mpr ⟨hsep, hBsep, ?_⟩
    intro x hx y hy _
    have hxy := (hBD hy).2 x hx
    exact ⟨by simpa only [edist_comm] using hxy, hxy⟩
  · intro x hx
    by_cases hxD : x ∈ D
    · obtain ⟨y, hy, hdist⟩ := hBcover hxD
      exact ⟨y, Or.inr hy, hdist⟩
    · have hex : ∃ y ∈ A, edist x y ≤ r := by
        by_contra! h
        exact hxD ⟨hx, h⟩
      obtain ⟨y, hy, hdist⟩ := hex
      exact ⟨y, Or.inl hy, hdist⟩

theorem reflTransGen_edist_lt_of_isPreconnected_isCover
    {X : Type*} [PseudoEMetricSpace X] {C S : Set X}
    (hC : IsPreconnected C) (hSC : S ⊆ C) {r : ℝ≥0} (hr : 0 < r)
    (hcover : Metric.IsCover r C S) (a b : S) :
    Relation.ReflTransGen (fun p q : S => edist (p : X) q < (4 * r : ℝ≥0)) a b := by
  classical
  let R : S → S → Prop := fun p q => edist (p : X) q < (4 * r : ℝ≥0)
  let U : Set X := ⋃ p : S, ⋃ (_ : Relation.ReflTransGen R a p), Metric.eball p (2 * r : ℝ≥0)
  let V : Set X := ⋃ p : S, ⋃ (_ : ¬ Relation.ReflTransGen R a p), Metric.eball p (2 * r : ℝ≥0)
  have hU : IsOpen U := isOpen_iUnion fun _ => isOpen_iUnion fun _ => Metric.isOpen_eball
  have hV : IsOpen V := isOpen_iUnion fun _ => isOpen_iUnion fun _ => Metric.isOpen_eball
  have hc : C ⊆ U ∪ V := by
    intro x hx
    obtain ⟨p, hpS, hxp⟩ := hcover hx
    change edist x p ≤ (r : ℝ≥0∞) at hxp
    let q : S := ⟨p, hpS⟩
    have hball : x ∈ Metric.eball (q : X) (2 * r : ℝ≥0) := by
      change edist x p < (2 * r : ℝ≥0)
      have htwice : r < 2 * r := (lt_mul_iff_one_lt_left hr).mpr (by norm_num)
      exact hxp.trans_lt (by exact_mod_cast htwice)
    by_cases hq : Relation.ReflTransGen R a q
    · exact Or.inl (mem_iUnion.mpr ⟨q, mem_iUnion.mpr ⟨hq, hball⟩⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨q, mem_iUnion.mpr ⟨hq, hball⟩⟩)
  by_contra hab
  have ha : (C ∩ U).Nonempty := by
    refine ⟨a, hSC a.property, mem_iUnion.mpr ⟨a, mem_iUnion.mpr ⟨.refl, ?_⟩⟩⟩
    exact Metric.mem_eball_self (by positivity)
  have hb : (C ∩ V).Nonempty := by
    refine ⟨b, hSC b.property, mem_iUnion.mpr ⟨b, mem_iUnion.mpr ⟨hab, ?_⟩⟩⟩
    exact Metric.mem_eball_self (by positivity)
  obtain ⟨x, _, hxU, hxV⟩ := hC U V hU hV hc ha hb
  obtain ⟨p, hp⟩ := mem_iUnion.mp hxU
  obtain ⟨hpR, hxp⟩ := mem_iUnion.mp hp
  obtain ⟨q, hq⟩ := mem_iUnion.mp hxV
  obtain ⟨hqR, hxq⟩ := mem_iUnion.mp hq
  apply hqR
  apply hpR.tail
  change edist (p : X) q < (4 * r : ℝ≥0)
  have hpdist : edist x (p : X) < (2 * r : ℝ≥0) := hxp
  have hqdist : edist x (q : X) < (2 * r : ℝ≥0) := hxq
  calc
    edist (p : X) q ≤ edist (p : X) x + edist x q := edist_triangle _ _ _
    _ < (2 * r : ℝ≥0) + (2 * r : ℝ≥0) := by
      rw [edist_comm (p : X) x]
      exact ENNReal.add_lt_add hpdist hqdist
    _ = (4 * r : ℝ≥0) := by norm_cast; ring

end DifferentialGeometry.Topology
