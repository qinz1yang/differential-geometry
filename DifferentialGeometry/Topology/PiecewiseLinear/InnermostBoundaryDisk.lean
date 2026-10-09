/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ArcSubinterval
import DifferentialGeometry.Topology.PiecewiseLinear.CircleDiskSubarc
import DifferentialGeometry.Topology.PiecewiseLinear.DiskCrosscutContainment
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceDiskSeparation

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_innermost_disk_with_boundary_subarc
    (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces] (hL : IsCombinatorialManifold 2 L)
    {D₀ B₀ R₀ : Set E} {q₀ : (Fin 3 → ℝ) → E}
    (hq₀ : IsPLHomeomorphOn q₀ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₀)
    (hD₀L : D₀ ⊆ L.space) {β₀ δ₀ : ℝ → E}
    (hβ₀ : IsPLHomeomorphOn β₀ (Icc 0 1) B₀) (hδ₀ : IsPLHomeomorphOn δ₀ (Icc 0 1) R₀)
    (hδ₀0 : δ₀ 0 = β₀ 0) (hδ₀1 : δ₀ 1 = β₀ 1)
    (hB₀R₀ : B₀ ∩ R₀ = {β₀ 0, β₀ 1}) (hq₀B : q₀ '' stdSimplexBoundary 2 = B₀ ∪ R₀)
    {ι : Type*} {F : ι → Set E} (hF : ∀ i, IsPLSphere 1 (F i)) (hFL : ∀ i, F i ⊆ L.space)
    (hdis : Pairwise fun i j => Disjoint (F i) (F j))
    (hfinite : (R₀ ∩ ⋃ i, F i).Finite) (hno : ∀ i, ¬ F i ⊆ D₀)
    (i₀ : ι) (hB₀F : B₀ ⊆ F i₀) :
    ∃ (i : ι) (B R D : Set E) (q : (Fin 3 → ℝ) → E) (β δ : ℝ → E),
      IsPLHomeomorphOn β (Icc 0 1) B ∧ IsPLHomeomorphOn δ (Icc 0 1) R ∧
      δ 0 = β 0 ∧ δ 1 = β 1 ∧ B ⊆ F i ∧ R ⊆ R₀ ∧ B ∩ R = {β 0, β 1} ∧
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧ D ⊆ D₀ ∧ D ∩ R₀ = R ∧
      q '' stdSimplexBoundary 2 = B ∪ R ∧ ∀ j, Disjoint (D \ (B ∪ R)) (F j) := by
  classical
  let Z := ⋃ i, F i
  let P := fun (i : ι) (B R D : Set E) (q : (Fin 3 → ℝ) → E) (β δ : ℝ → E) =>
    IsPLHomeomorphOn β (Icc 0 1) B ∧ IsPLHomeomorphOn δ (Icc 0 1) R ∧
      δ 0 = β 0 ∧ δ 1 = β 1 ∧ B ⊆ F i ∧ R ⊆ R₀ ∧ B ∩ R = {β 0, β 1} ∧
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧ D ⊆ D₀ ∧ D ∩ R₀ = R ∧
      q '' stdSimplexBoundary 2 = B ∪ R
  have hR₀D₀ : R₀ ⊆ D₀ := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := hq₀B.symm.subset (Or.inr hx)
    exact hax ▸ hq₀.bijOn.mapsTo ha.1
  have hinit : P i₀ B₀ R₀ D₀ q₀ β₀ δ₀ :=
    ⟨hβ₀, hδ₀, hδ₀0, hδ₀1, hB₀F, Subset.rfl, hB₀R₀, hq₀, Subset.rfl,
      inter_eq_right.mpr hR₀D₀, hq₀B⟩
  have hex : ∃ n, ∃ (i : ι) (B R D : Set E) (q : (Fin 3 → ℝ) → E) (β δ : ℝ → E),
      P i B R D q β δ ∧ (R ∩ Z).ncard = n := ⟨_, i₀, B₀, R₀, D₀, q₀, β₀, δ₀, hinit, rfl⟩
  obtain ⟨i, B, R, D, q, β, δ, hdata, hn⟩ := Nat.find_spec hex
  obtain ⟨hβ, hδ, hδ0, hδ1, hBF, hRR₀, hBR, hq, hDD₀, hDR₀, hqB⟩ := hdata
  have hBD : B ⊆ D := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := hqB.symm.subset (Or.inl hx)
    exact hax ▸ hq.bijOn.mapsTo ha.1
  have hRJ : R ⊆ q '' stdSimplexBoundary 2 := subset_union_right.trans hqB.symm.subset
  refine ⟨i, B, R, D, q, β, δ, hβ, hδ, hδ0, hδ1, hBF, hRR₀, hBR,
    hq, hDD₀, hDR₀, hqB, fun j => ?_⟩
  apply Set.disjoint_left.mpr
  rintro x ⟨hxD, hxJ⟩ hxF
  have hD : IsPLBall 2 D := ⟨q, hq⟩
  have hboundary : D ∩ closure (L.space \ D) = B ∪ R :=
    (hL.inter_closure_sdiff_disk L hq (hDD₀.trans hD₀L)).trans hqB
  have hrel : Disjoint (F j) B ∨ B ⊆ F j := by
    by_cases hji : j = i
    · exact Or.inr (hji.symm ▸ hBF)
    · exact Or.inl ((hdis hji).mono_right hBF)
  have hjfin : (F j ∩ R).Finite := hfinite.subset fun y hy =>
    ⟨hRR₀ hy.2, mem_iUnion.mpr ⟨j, hy.1⟩⟩
  have hjnot : ¬ F j ⊆ D := fun hjD => hno j (hjD.trans hDD₀)
  obtain ⟨A, α, hα, hAFD, hα0R, hα1R, hAR, hopen, -⟩ :=
    exists_crossing_subarc_ending_on_boundary_arc (hF j) (hFL j) hD.isPolyhedron.isClosed
      hboundary hβ hBR hrel hjfin hjnot ⟨hxF, hxD, hxJ⟩
  have hαne : α 0 ≠ α 1 := fun heq => zero_ne_one
    (hα.bijOn.injOn (by norm_num) (by norm_num) heq)
  obtain ⟨R', δ', hδ', hδ'0, hδ'1, hR'R, hfullends, hfull⟩ :=
    exists_subarc_between_points hδ hα0R hα1R hαne
  have hendsR' : ({α 0, α 1} : Set E) ⊆ R' := by
    rw [← hδ'0, ← hδ'1]
    exact pair_subset (hδ'.bijOn.mapsTo (by norm_num)) (hδ'.bijOn.mapsTo (by norm_num))
  have hAJ : A ∩ (q '' stdSimplexBoundary 2) = {α 0, α 1} := by
    apply Subset.antisymm
    · rintro y ⟨hyA, hyJ⟩
      by_contra hy
      exact (hopen ⟨hyA, hy⟩).2 (hqB.subset hyJ)
    · intro y hy
      exact ⟨(pair_subset (hα.bijOn.mapsTo (by norm_num)) (hα.bijOn.mapsTo (by norm_num))) hy,
        hRJ ((pair_subset hα0R hα1R) hy)⟩
  obtain ⟨D', q', hq', hD'D, hq'B, hD'J⟩ :=
    hq.exists_disk_between_proper_arc_and_boundary_arc
      hα hδ' hδ'0 hδ'1 (fun y hy => (hAFD hy).2) (hR'R.trans hRJ) hAJ
  have hAR' : A ∩ R' = {α 0, α 1} := Subset.antisymm
    (fun y hy => hAR.subset ⟨hy.1, hR'R hy.2⟩)
    (fun y hy => ⟨(pair_subset (hα.bijOn.mapsTo (by norm_num))
      (hα.bijOn.mapsTo (by norm_num))) hy, hendsR' hy⟩)
  have hD'R₀ : D' ∩ R₀ = R' := by
    apply Subset.antisymm
    · rintro y ⟨hyD', hyR₀⟩
      exact hD'J.subset ⟨hyD', hRJ (hDR₀.subset ⟨hD'D hyD', hyR₀⟩)⟩
    · intro y hyR'
      obtain ⟨a, ha, hay⟩ := hq'B.symm.subset (Or.inr hyR')
      exact ⟨hay ▸ hq'.bijOn.mapsTo ha.1, hRR₀ (hR'R hyR')⟩
  have hproper : R' ≠ R := by
    intro hEq
    have hends : ({α 0, α 1} : Set E) = {β 0, β 1} := by
      simpa only [hδ0, hδ1] using hfullends hEq
    have hα0B : α 0 ∈ B := (pair_subset (hβ.bijOn.mapsTo (by norm_num))
      (hβ.bijOn.mapsTo (by norm_num))) (hends.subset (by simp))
    have hji : j = i := by
      by_contra hji
      exact Set.disjoint_left.mp (hdis hji)
        (hAFD (hα.bijOn.mapsTo (by norm_num))).1 (hBF hα0B)
    have hAB : A ∩ B = {α 0, α 1} := by
      apply Subset.antisymm
      · rintro y ⟨hyA, hyB⟩
        by_contra hy
        exact (hopen ⟨hyA, hy⟩).2 (Or.inl hyB)
      · intro y hy
        exact ⟨(pair_subset (hα.bijOn.mapsTo (by norm_num))
          (hα.bijOn.mapsTo (by norm_num))) hy,
          (pair_subset (hβ.bijOn.mapsTo (by norm_num))
            (hβ.bijOn.mapsTo (by norm_num))) (hends.subset hy)⟩
    have hcircle : IsPLSphere 1 (A ∪ B) := by
      rcases Set.pair_eq_pair_iff.mp hends with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · exact isPLSphere_one_union_of_isPLHomeomorphOn_Icc hα hβ h0.symm h1.symm hAB
      · apply isPLSphere_one_union_of_isPLHomeomorphOn_Icc hα
          (isPLHomeomorphOn_comp_one_sub hβ) _ _ hAB
        · simpa only [sub_zero] using h0.symm
        · simpa only [sub_self] using h1.symm
    have hAFi : A ⊆ F i := fun y hy => hji ▸ (hAFD hy).1
    have hEqF := eq_of_subset_of_isPLSphere_one hcircle (hF i) (union_subset hAFi hBF)
    exact hno i (hEqF.symm.subset.trans
      ((union_subset (fun y hy => (hAFD hy).2) hBD).trans hDD₀))
  have hδ0Z : δ 0 ∈ Z := by
    rw [hδ0]
    exact mem_iUnion.mpr ⟨i, hBF (hβ.bijOn.mapsTo (by norm_num))⟩
  have hδ1Z : δ 1 ∈ Z := by
    rw [hδ1]
    exact mem_iUnion.mpr ⟨i, hBF (hβ.bijOn.mapsTo (by norm_num))⟩
  obtain ⟨z, hzR, hzZ, hzR'⟩ : ∃ z, z ∈ R ∧ z ∈ Z ∧ z ∉ R' := by
    by_cases h0 : δ 0 ∈ R'
    · exact ⟨δ 1, hδ.bijOn.mapsTo (by norm_num), hδ1Z, fun h1 => hproper (hfull h0 h1)⟩
    · exact ⟨δ 0, hδ.bijOn.mapsTo (by norm_num), hδ0Z, h0⟩
  have hfin : (R ∩ Z).Finite := hfinite.subset fun y hy => ⟨hRR₀ hy.1, hy.2⟩
  have hlt : (R' ∩ Z).ncard < (R ∩ Z).ncard := Set.ncard_lt_ncard
    (ssubset_of_subset_not_subset (fun y hy => ⟨hR'R hy.1, hy.2⟩)
      (fun h => hzR' (h ⟨hzR, hzZ⟩).1)) hfin
  have hnew : P j A R' D' q' α δ' :=
    ⟨hα, hδ', hδ'0, hδ'1, fun y hy => (hAFD hy).1, hR'R.trans hRR₀, hAR',
      hq', hD'D.trans hDD₀, hD'R₀, hq'B⟩
  have hmin := Nat.find_min' hex ⟨j, A, R', D', q', α, δ', hnew, rfl⟩
  omega

end DifferentialGeometry.Topology.PiecewiseLinear
