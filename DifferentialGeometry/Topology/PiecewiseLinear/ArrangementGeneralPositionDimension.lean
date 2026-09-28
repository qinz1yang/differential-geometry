/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Topology.MetricSpace.HausdorffDimension
import DifferentialGeometry.Topology.PiecewiseLinear.ArrangementGeneralPosition

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem dimH_iUnion_lt_of_finite {X ι : Type*} [EMetricSpace X] [Finite ι] {s : ι → Set X}
    {c : ENNReal} (hc : 0 < c) (hs : ∀ i, dimH (s i) < c) : dimH (⋃ i, s i) < c := by
  cases nonempty_fintype ι
  rw [dimH_iUnion]
  exact lt_of_le_of_lt
    (iSup_le fun i => Finset.le_sup (f := fun i => dimH (s i)) (Finset.mem_univ i))
    ((Finset.sup_lt_iff (lt_of_le_of_lt bot_le hc)).mpr fun i _ => hs i)

theorem dimH_biUnion_inter_lt {X κ : Type*} [EMetricSpace X] {K : Set κ} (hK : K.Finite)
    (B : κ → Set X) (L : Set X) {c : ENNReal} (hc : 0 < c)
    (hB : ∀ k ∈ K, dimH (B k ∩ L) < c) : dimH ((⋃ k ∈ K, B k) ∩ L) < c := by
  have : Finite K := hK.to_subtype
  rw [iUnion₂_inter, biUnion_eq_iUnion]
  exact dimH_iUnion_lt_of_finite hc fun k => hB k k.2

theorem exists_dimH_inter_lt_forall_of_finite {X κ : Type*} [EMetricSpace X] {K : Set κ}
    (hK : K.Finite) (L : Set X) {c : ENNReal} (hc : 0 < c) (P : κ → X → Prop)
    (h : ∀ k ∈ K, ∃ B : Set X, dimH (B ∩ L) < c ∧ ∀ x ∈ L, x ∉ B → P k x) :
    ∃ B : Set X, dimH (B ∩ L) < c ∧ ∀ x ∈ L, x ∉ B → ∀ k ∈ K, P k x := by
  choose! B hB hP using h
  refine ⟨⋃ k ∈ K, B k, dimH_biUnion_inter_lt hK B L hc hB, fun x hx hxB k hk => ?_⟩
  exact hP k hk x hx fun hxk => hxB (mem_biUnion hk hxk)

theorem dimH_inter_lt_of_finrank_direction_lt [FiniteDimensional ℝ E]
    {L A : AffineSubspace ℝ E}
    (h : Module.finrank ℝ A.direction < Module.finrank ℝ L.direction) :
    dimH ((A : Set E) ∩ L) < Module.finrank ℝ L.direction := by
  rcases (A : Set E).eq_empty_or_nonempty with hA | hA
  · rw [hA, empty_inter, dimH_empty]
    exact_mod_cast (Nat.zero_le _).trans_lt h
  · calc dimH ((A : Set E) ∩ L) ≤ dimH (A : Set E) := dimH_mono inter_subset_left
      _ = Module.finrank ℝ (vectorSpan ℝ (A : Set E)) :=
        Real.Convex.dimH_eq_finrank_vectorSpan A.convex hA
      _ < Module.finrank ℝ L.direction := by
        rw [← AffineSubspace.direction_eq_vectorSpan]
        exact_mod_cast h

theorem dimH_inter_lt_of_not_le [FiniteDimensional ℝ E] {L A : AffineSubspace ℝ E}
    (hL : 0 < Module.finrank ℝ L.direction) (h : ¬L ≤ A) :
    dimH ((A : Set E) ∩ L) < Module.finrank ℝ L.direction := by
  have hrank : Module.finrank ℝ (A ⊓ L).direction < Module.finrank ℝ L.direction := by
    rcases (((A ⊓ L : AffineSubspace ℝ E)) : Set E).eq_empty_or_nonempty with he | ⟨p, hp⟩
    · rw [(AffineSubspace.coe_eq_bot_iff _).mp he, AffineSubspace.direction_bot, finrank_bot]
      exact hL
    · rw [AffineSubspace.direction_inf_of_mem_inf hp]
      refine lt_of_le_of_ne (Submodule.finrank_mono inf_le_right) fun heq => h ?_
      have hdir : A.direction ⊓ L.direction = L.direction :=
        Submodule.eq_of_le_of_finrank_eq inf_le_right heq
      have hle : L.direction ≤ A.direction := by
        rw [← hdir]
        exact inf_le_left
      obtain ⟨hpA, hpL⟩ := (AffineSubspace.mem_inf_iff p A L).mp hp
      intro q hq
      have hqp : q -ᵥ p ∈ A.direction := hle (AffineSubspace.vsub_mem_direction hq hpL)
      have hmem := AffineSubspace.vadd_mem_of_mem_direction hqp hpA
      rwa [vsub_vadd] at hmem
  have heq : (A : Set E) ∩ L = ((A ⊓ L : AffineSubspace ℝ E) : Set E) ∩ L := by
    ext q
    simp only [mem_inter_iff, SetLike.mem_coe, AffineSubspace.mem_inf_iff]
    tauto
  rw [heq]
  exact dimH_inter_lt_of_finrank_direction_lt hrank

theorem exists_mem_inter_notMem_of_dimH_inter_lt [FiniteDimensional ℝ E]
    (L : AffineSubspace ℝ E) {x₀ : E} (hx₀ : x₀ ∈ L) {U : Set E} (hU : U ∈ 𝓝 x₀) {B : Set E}
    (hB : dimH (B ∩ L) < Module.finrank ℝ L.direction) : ∃ x ∈ L, x ∈ U ∧ x ∉ B := by
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp hU
  have hconv : Convex ℝ ((L : Set E) ∩ ball x₀ r) := L.convex.inter (convex_ball x₀ r)
  have hx₀s : x₀ ∈ (L : Set E) ∩ ball x₀ r := ⟨hx₀, mem_ball_self hr⟩
  have hspan : vectorSpan ℝ ((L : Set E) ∩ ball x₀ r) = L.direction := by
    refine le_antisymm ?_ fun v hv => ?_
    · rw [AffineSubspace.direction_eq_vectorSpan]
      exact vectorSpan_mono ℝ inter_subset_left
    · by_cases hv0 : v = 0
      · rw [hv0]
        exact Submodule.zero_mem _
      have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv0
      obtain ⟨c, hc⟩ : ∃ c : ℝ, c = r / (2 * ‖v‖) := ⟨_, rfl⟩
      have hcpos : 0 < c := by
        rw [hc]
        positivity
      have hcv : c * ‖v‖ = r / 2 := by
        rw [hc]
        field_simp
      have hmem : c • v +ᵥ x₀ ∈ (L : Set E) ∩ ball x₀ r := by
        refine ⟨AffineSubspace.vadd_mem_of_mem_direction (L.direction.smul_mem c hv) hx₀, ?_⟩
        rw [mem_ball, dist_eq_norm, vadd_eq_add, add_sub_cancel_right, norm_smul,
          Real.norm_eq_abs, abs_of_pos hcpos, hcv]
        linarith
      have h1 := vsub_mem_vectorSpan ℝ hmem hx₀s
      rw [vadd_vsub] at h1
      have h2 := (vectorSpan ℝ ((L : Set E) ∩ ball x₀ r)).smul_mem c⁻¹ h1
      rwa [smul_smul, inv_mul_cancel₀ hcpos.ne', one_smul] at h2
  have hdim : dimH ((L : Set E) ∩ ball x₀ r) = Module.finrank ℝ L.direction := by
    rw [Real.Convex.dimH_eq_finrank_vectorSpan hconv ⟨x₀, hx₀s⟩, hspan]
  by_contra hcon
  push Not at hcon
  have hsub : (L : Set E) ∩ ball x₀ r ⊆ B ∩ L := fun x hx => ⟨hcon x hx.1 (hrU hx.2), hx.1⟩
  have hle := dimH_mono hsub
  rw [hdim] at hle
  exact absurd hB (not_lt.mpr hle)

theorem exists_mem_openCell_notMem_affineSubspaces_notMem_ranges {κ ι η F : Type*} [Finite κ]
    [Finite ι] [Finite η] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (l : κ → E →ᵃ[ℝ] ℝ) (A : ι → AffineSubspace ℝ E)
    (f : η → F → E) (x : E) (hA : ∀ i, ¬arrangementLayer l x ≤ A i)
    (hf : ∀ j, ContDiff ℝ 1 (f j))
    (hF : Module.finrank ℝ F < Module.finrank ℝ (arrangementDirection l x))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ y ∈ openCell l (signVec l x), dist y x < ε ∧ (∀ i, y ∉ A i) ∧
      ∀ j, y ∉ range (f j) := by
  have hLdir : (arrangementLayer l x).direction = arrangementDirection l x :=
    direction_arrangementLayer l x
  have hm : 0 < Module.finrank ℝ (arrangementLayer l x).direction := by
    rw [hLdir]
    omega
  obtain ⟨V, hV, hVcell⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp
    (openCell_mem_nhdsWithin_arrangementLayer l x)
  have hpos : (0 : ENNReal) < Module.finrank ℝ (arrangementLayer l x).direction := by
    exact_mod_cast hm
  have hB : dimH (((⋃ i, (A i : Set E)) ∪ ⋃ j, range (f j)) ∩ arrangementLayer l x) <
      Module.finrank ℝ (arrangementLayer l x).direction := by
    rw [union_inter_distrib_right, dimH_union, max_lt_iff, iUnion_inter, iUnion_inter]
    refine ⟨dimH_iUnion_lt_of_finite hpos fun i => dimH_inter_lt_of_not_le hm (hA i),
      dimH_iUnion_lt_of_finite hpos fun j => ?_⟩
    calc dimH (range (f j) ∩ arrangementLayer l x) ≤ dimH (range (f j)) :=
          dimH_mono inter_subset_left
      _ ≤ Module.finrank ℝ F := ((hf j).differentiable one_ne_zero).dimH_range_le
      _ < Module.finrank ℝ (arrangementLayer l x).direction := by
          rw [hLdir]
          exact_mod_cast hF
  obtain ⟨y, hyL, hyU, hyB⟩ := exists_mem_inter_notMem_of_dimH_inter_lt
    (arrangementLayer l x) (self_mem_arrangementLayer l x)
    (Filter.inter_mem hV (ball_mem_nhds x hε)) hB
  exact ⟨y, hVcell ⟨hyU.1, hyL⟩, mem_ball.mp hyU.2,
    fun i hi => hyB (Or.inl (mem_iUnion.mpr ⟨i, hi⟩)),
    fun j hj => hyB (Or.inr (mem_iUnion.mpr ⟨j, hj⟩))⟩

end DifferentialGeometry.Topology.PiecewiseLinear
