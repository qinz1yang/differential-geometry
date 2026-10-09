/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.GenericPlacementClauses

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem finrank_direction_affineSpan_image_le_card_sub_one {ι E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (s : Finset ι) (ψ : ι → E) :
    Module.finrank ℝ (affineSpan ℝ (ψ '' ↑s)).direction ≤ s.card - 1 := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · rw [Finset.coe_empty, image_empty, AffineSubspace.span_empty, AffineSubspace.direction_bot,
      finrank_bot]
    exact Nat.zero_le _
  · have := finrank_direction_affineSpan_image_lt_card hs ψ
    omega

theorem exists_small_vertexMap_generic_lines_planes_in_halfSpace {ι ιS ιP : Type*}
    [DecidableEq ι] [Finite ιS] [Finite ιP] (U Vf Bv : Finset ι) (Afz : Set ι)
    [DecidablePred (· ∈ Afz)] (hVf : ∀ u, u ∈ Vf ↔ u ∈ U ∧ u ∉ Afz)
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) (φ₀ : ι → EuclideanSpace ℝ (Fin 3))
    (hφ₀ : ∀ u ∈ U, (ℓ (φ₀ u) = 0 ↔ u ∈ Bv) ∧ 0 ≤ ℓ (φ₀ u))
    (S : ιS → AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)))
    (hS : ∀ j, Module.finrank ℝ (S j).direction = 1)
    (P : ιP → AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)))
    (hP : ∀ j, Module.finrank ℝ (P j).direction ≤ 2) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : ι → EuclideanSpace ℝ (Fin 3), EqOn φ φ₀ (↑Vf)ᶜ ∧ (∀ u, dist (φ u) (φ₀ u) < ε) ∧
      (∀ u ∈ Vf, (u ∈ Bv → ℓ (φ u) = 0) ∧ (u ∉ Bv → 0 < ℓ (φ u))) ∧
      (∀ s ⊆ U, s.card ≤ 4 → (s ∩ Bv).card ≤ 3 →
        AffineIndependent ℝ (fun u : s.filter (· ∈ Afz) => φ u) →
          AffineIndependent ℝ (fun u : s => φ u)) ∧
      (∀ u ∈ Vf, ∀ j, (u ∈ Bv → ¬(LinearMap.ker ℓ).toAffineSubspace ≤ P j) → φ u ∉ P j) ∧
      (∀ α ⊆ Vf, ∀ β ⊆ Vf,
        ((α.card = 3 ∧ β.card = 3 ∧ ¬α ⊆ Bv ∧ ¬β ⊆ Bv ∧ (α ∩ β).card ≤ 1) ∨
          (α.card = 3 ∧ ¬α ⊆ Bv ∧ β.card = 2 ∧ Disjoint α β) ∨
          (α.card = 2 ∧ β.card = 2 ∧ α ⊆ Bv ∧ β ⊆ Bv ∧ Disjoint α β)) →
        ∀ j (w w' : ι → ℝ), (∀ u ∈ α, 0 < w u) → ∑ u ∈ α, w u = 1 → (∀ u ∈ β, 0 < w' u) →
          ∑ u ∈ β, w' u = 1 → ∑ u ∈ α, w u • φ u = ∑ u ∈ β, w' u • φ u →
            ∑ u ∈ α, w u • φ u ∉ S j) ∧
      (∀ α ⊆ Vf, ∀ β ⊆ Vf, α.card = 3 → ¬α ⊆ Bv → β.card = 2 → ¬β ⊆ Bv →
        Disjoint α β → ∀ j, ¬(LinearMap.ker ℓ).toAffineSubspace ≤ P j →
          ∀ w w' : ι → ℝ, (∀ u ∈ α, 0 < w u) → ∑ u ∈ α, w u = 1 → (∀ u ∈ β, 0 < w' u) →
            ∑ u ∈ β, w' u = 1 → ∑ u ∈ α, w u • φ u = ∑ u ∈ β, w' u • φ u →
              ∑ u ∈ α, w u • φ u ∉ P j) ∧
      (∀ α ⊆ Vf, ∀ β ⊆ Vf, α.card = 3 → β.card = 3 → ¬α ⊆ Bv → ¬β ⊆ Bv →
        Disjoint α β → ∀ j, ¬(LinearMap.ker ℓ).toAffineSubspace ≤ P j →
          ∀ w w' : ι → ℝ, (∀ u ∈ α, 0 < w u) → ∑ u ∈ α, w u = 1 → (∀ u ∈ β, 0 < w' u) →
            ∑ u ∈ β, w' u = 1 → ∑ u ∈ α, w u • φ u = ∑ u ∈ β, w' u • φ u →
              ∑ u ∈ α, w u • φ u ∈ P j →
                ¬affineSpan ℝ (φ '' ↑α) ⊓ affineSpan ℝ (φ '' ↑β) ≤ P j) := by
  have hker2 : Module.finrank ℝ (LinearMap.ker ℓ) = 2 := by
    have hrange : LinearMap.range ℓ = ⊤ := by
      obtain ⟨q, hq⟩ : ∃ q, ℓ q ≠ 0 := by
        by_contra h
        push Not at h
        exact hℓ (LinearMap.ext h)
      refine eq_top_iff.mpr fun r _ => ⟨(r / ℓ q) • q, ?_⟩
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ r hq]
    have h := LinearMap.finrank_range_add_finrank_ker ℓ
    rw [hrange, finrank_top, Module.finrank_self, finrank_euclideanSpace_fin] at h
    omega
  let Inv : Finset ι → (ι → EuclideanSpace ℝ (Fin 3)) → Prop := fun T φ =>
    EqOn φ φ₀ (↑T)ᶜ ∧ (∀ u, dist (φ u) (φ₀ u) < ε) ∧
      (∀ u ∈ T, (u ∈ Bv → ℓ (φ u) = 0) ∧ (u ∉ Bv → 0 < ℓ (φ u))) ∧
      (∀ s ⊆ U, (∀ u ∈ s, u ∈ Vf → u ∈ T) → s.card ≤ 4 → (s ∩ Bv).card ≤ 3 →
        AffineIndependent ℝ (fun u : s.filter (· ∈ Afz) => φ u) →
          AffineIndependent ℝ (fun u : s => φ u)) ∧
      (∀ u ∈ T, ∀ j, φ u ∉ S j) ∧
      (∀ u ∈ T, ∀ j, (u ∈ Bv → ¬(LinearMap.ker ℓ).toAffineSubspace ≤ P j) → φ u ∉ P j) ∧
      (∀ β ⊆ T, β.card = 3 → ¬β ⊆ Bv → ∀ j, ¬S j ≤ affineSpan ℝ (φ '' ↑β)) ∧
      (∀ α ⊆ T, ∀ β ⊆ T,
        ((α.card = 3 ∧ β.card = 3 ∧ ¬α ⊆ Bv ∧ ¬β ⊆ Bv ∧ (α ∩ β).card ≤ 1) ∨
          (α.card = 3 ∧ ¬α ⊆ Bv ∧ β.card = 2 ∧ Disjoint α β) ∨
          (α.card = 2 ∧ β.card = 2 ∧ α ⊆ Bv ∧ β ⊆ Bv ∧ Disjoint α β)) →
        ∀ j (w w' : ι → ℝ), (∀ u ∈ α, 0 < w u) → ∑ u ∈ α, w u = 1 → (∀ u ∈ β, 0 < w' u) →
          ∑ u ∈ β, w' u = 1 → ∑ u ∈ α, w u • φ u = ∑ u ∈ β, w' u • φ u →
            ∑ u ∈ α, w u • φ u ∉ S j) ∧
      (∀ α ⊆ T, ∀ β ⊆ T, α.card = 3 → ¬α ⊆ Bv → β.card = 2 → ¬β ⊆ Bv →
        Disjoint α β → ∀ j, ¬(LinearMap.ker ℓ).toAffineSubspace ≤ P j →
          ∀ w w' : ι → ℝ, (∀ u ∈ α, 0 < w u) → ∑ u ∈ α, w u = 1 → (∀ u ∈ β, 0 < w' u) →
            ∑ u ∈ β, w' u = 1 → ∑ u ∈ α, w u • φ u = ∑ u ∈ β, w' u • φ u →
              ∑ u ∈ α, w u • φ u ∉ P j) ∧
      (∀ α ⊆ T, ∀ β ⊆ T, α.card = 3 → β.card = 3 → ¬α ⊆ Bv → ¬β ⊆ Bv →
        Disjoint α β → ∀ j, ¬(LinearMap.ker ℓ).toAffineSubspace ≤ P j →
          ∀ w w' : ι → ℝ, (∀ u ∈ α, 0 < w u) → ∑ u ∈ α, w u = 1 → (∀ u ∈ β, 0 < w' u) →
            ∑ u ∈ β, w' u = 1 → ∑ u ∈ α, w u • φ u = ∑ u ∈ β, w' u • φ u →
              ∑ u ∈ α, w u • φ u ∈ P j →
                ¬affineSpan ℝ (φ '' ↑α) ⊓ affineSpan ℝ (φ '' ↑β) ≤ P j)
  have hbase : Inv ∅ φ₀ := by
    refine ⟨fun _ _ => rfl, fun u => by simpa using hε,
      fun u hu => absurd hu (Finset.notMem_empty u), ?_,
      fun u hu => absurd hu (Finset.notMem_empty u), fun u hu => absurd hu (Finset.notMem_empty u),
      ?_, ?_, ?_, ?_⟩
    · intro s hsU hfree _ _ hfrz
      have hall : ∀ u ∈ s, u ∈ Afz := fun u hu => by
        by_contra hA
        exact Finset.notMem_empty u (hfree u hu ((hVf u).mpr ⟨hsU hu, hA⟩))
      rwa [Finset.filter_true_of_mem hall] at hfrz
    · intro β hβ h3
      rw [Finset.subset_empty.mp hβ] at h3
      simp at h3
    · intro α hα β _ hk
      rw [Finset.subset_empty.mp hα] at hk
      simp at hk
    · intro α hα β _ h3
      rw [Finset.subset_empty.mp hα] at h3
      simp at h3
    · intro α hα β _ h3
      rw [Finset.subset_empty.mp hα] at h3
      simp at h3
  have hKg : ∀ (T : Finset ι) (v : ι), {s : Finset ι | s ⊆ U ∧ v ∈ s ∧
      (∀ u ∈ s, u ∈ Vf → u ∈ insert v T) ∧ s.card ≤ 4 ∧ (s ∩ Bv).card ≤ 3}.Finite :=
    fun T v => U.powerset.finite_toSet.subset fun s hs => Finset.mem_powerset.mpr hs.1
  have hphase1 : ∀ T : Finset ι, T ⊆ Vf.filter (· ∈ Bv) → ∃ φ, Inv T φ := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact fun _ => ⟨φ₀, hbase⟩
    | @insert v T hvT ih =>
      intro hsub
      obtain ⟨φ, hfix, hclose, hlay, hguard, hline, hplane, htri, hskel, hfold, hcross⟩ :=
        ih ((Finset.subset_insert v T).trans hsub)
      have hvmem := Finset.mem_filter.mp (hsub (Finset.mem_insert_self v T))
      have hvV : v ∈ Vf := hvmem.1
      have hvB : v ∈ Bv := hvmem.2
      have hTB : T ⊆ Bv := fun u hu =>
        (Finset.mem_filter.mp (hsub (Finset.mem_insert_of_mem hu))).2
      have hvU : v ∈ U := ((hVf v).mp hvV).1
      have hφ₀v : ℓ (φ₀ v) = 0 := ((hφ₀ v hvU).1).mpr hvB
      have hzeroB : ∀ u ∈ U, ℓ (φ u) = 0 → u ∈ Bv := fun u huU hu => by
        by_cases huT : u ∈ T
        · exact hTB huT
        · rw [hfix huT] at hu
          exact ((hφ₀ u huU).1).mp hu
      obtain ⟨L0, hL0⟩ : ∃ L0 : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)),
          L0 = (LinearMap.ker ℓ).toAffineSubspace := ⟨_, rfl⟩
      have hL0dir : Module.finrank ℝ L0.direction = 2 := by
        rw [hL0, Submodule.toAffineSubspace_direction, hker2]
      have hmemL0 : ∀ q, q ∈ L0 ↔ ℓ q = 0 := fun q => by
        rw [hL0, Submodule.mem_toAffineSubspace, LinearMap.mem_ker]
      have hpos : (0 : ENNReal) < Module.finrank ℝ L0.direction := by
        rw [hL0dir]
        norm_num
      have hpos' : 0 < Module.finrank ℝ L0.direction := by
        rw [hL0dir]
        norm_num
      obtain ⟨Bk, hBk, hBkx⟩ := exists_dimH_lt_skeleton_update_boundary hvB hTB φ S hline hskel
      obtain ⟨Bg, hBg⟩ : ∃ Bg : Set (EuclideanSpace ℝ (Fin 3)), Bg = ⋃ s ∈ {s : Finset ι |
          s ⊆ U ∧ v ∈ s ∧ (∀ u ∈ s, u ∈ Vf → u ∈ insert v T) ∧ s.card ≤ 4 ∧
            (s ∩ Bv).card ≤ 3}, (affineSpan ℝ (φ '' ↑(s.erase v)) : Set _) := ⟨_, rfl⟩
      have hBgsmall : dimH (Bg ∩ L0) < Module.finrank ℝ L0.direction := by
        rw [hBg]
        refine dimH_biUnion_inter_lt (hKg T v) _ _ hpos fun s hs =>
          dimH_inter_lt_of_not_le hpos' ?_
        obtain ⟨hsU, hvs, -, h4, h3⟩ := hs
        intro hle
        have h1 : 2 ≤ Module.finrank ℝ (affineSpan ℝ (φ '' ↑(s.erase v))).direction := by
          have := Submodule.finrank_mono (AffineSubspace.direction_le hle)
          rwa [hL0dir] at this
        have h2 := finrank_direction_affineSpan_image_le_card_sub_one (s.erase v) φ
        have hce := Finset.card_erase_of_mem hvs
        have heq : L0 = affineSpan ℝ (φ '' ↑(s.erase v)) :=
          eq_of_le_of_finrank_direction_le hle ⟨0, (hmemL0 0).mpr (map_zero ℓ)⟩ (by omega)
        have hsB : s ⊆ Bv := by
          intro u hu
          by_cases huv : u = v
          · rw [huv]
            exact hvB
          · have hu' : u ∈ s.erase v := Finset.mem_erase.mpr ⟨huv, hu⟩
            have hmem : φ u ∈ L0 := by
              rw [heq]
              exact subset_affineSpan ℝ _ (mem_image_of_mem φ hu')
            exact hzeroB u (hsU hu) ((hmemL0 _).mp hmem)
        rw [Finset.inter_eq_left.mpr hsB] at h3
        omega
      have hBSsmall : dimH ((⋃ j, (S j : Set (EuclideanSpace ℝ (Fin 3)))) ∩ L0) <
          Module.finrank ℝ L0.direction := by
        rw [iUnion_inter]
        refine dimH_iUnion_lt_of_finite hpos fun j => ?_
        calc dimH ((S j : Set (EuclideanSpace ℝ (Fin 3))) ∩ L0) ≤
              dimH (S j : Set (EuclideanSpace ℝ (Fin 3))) := dimH_mono inter_subset_left
          _ < 2 := dimH_lt_two_of_finrank_direction_le_one (S j) (hS j).le
          _ = Module.finrank ℝ L0.direction := by
              rw [hL0dir]
              norm_num
      have hBPsmall : dimH ((⋃ j ∈ {j | ¬L0 ≤ P j}, (P j : Set (EuclideanSpace ℝ (Fin 3)))) ∩
          L0) < Module.finrank ℝ L0.direction :=
        dimH_biUnion_inter_lt (toFinite _) _ _ hpos fun j hj => dimH_inter_lt_of_not_le hpos' hj
      have hBksmall : dimH (Bk ∩ L0) < Module.finrank ℝ L0.direction :=
        calc dimH (Bk ∩ L0) ≤ dimH Bk := dimH_mono inter_subset_left
          _ < 2 := hBk
          _ = Module.finrank ℝ L0.direction := by
              rw [hL0dir]
              norm_num
      have hsmall : dimH ((Bg ∪ (⋃ j, (S j : Set (EuclideanSpace ℝ (Fin 3)))) ∪
          (⋃ j ∈ {j | ¬L0 ≤ P j}, (P j : Set (EuclideanSpace ℝ (Fin 3)))) ∪ Bk) ∩ L0) <
          Module.finrank ℝ L0.direction := by
        rw [union_inter_distrib_right, union_inter_distrib_right, union_inter_distrib_right,
          dimH_union, dimH_union, dimH_union]
        exact max_lt (max_lt (max_lt hBgsmall hBSsmall) hBPsmall) hBksmall
      obtain ⟨x, hxL, hxU, hxB⟩ := exists_mem_inter_notMem_of_dimH_inter_lt L0
        ((hmemL0 _).mpr hφ₀v) (ball_mem_nhds _ hε) hsmall
      have hinsB : insert v T ⊆ Bv := Finset.insert_subset hvB hTB
      refine ⟨Function.update φ v x, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro u hu
        have huv : u ≠ v := fun h => hu (by
          rw [h]
          exact Finset.mem_coe.mpr (Finset.mem_insert_self v T))
        rw [Function.update_of_ne huv]
        exact hfix fun h => hu (Finset.mem_coe.mpr (Finset.mem_insert_of_mem h))
      · intro u
        by_cases huv : u = v
        · rw [huv, Function.update_self]
          exact mem_ball.mp hxU
        · rw [Function.update_of_ne huv]
          exact hclose u
      · intro u hu
        by_cases huv : u = v
        · rw [huv, Function.update_self]
          exact ⟨fun _ => (hmemL0 x).mp hxL, fun h => absurd hvB h⟩
        · rw [Function.update_of_ne huv]
          exact hlay u ((Finset.mem_insert.mp hu).resolve_left huv)
      · exact guard_update_of_forall_notMem_affineSpan hVf hvV hguard
          fun s hsU hvs hfree h4 h3 hxs => hxB (Or.inl (Or.inl (Or.inl (by
            rw [hBg]
            exact mem_biUnion (show s ∈ {s : Finset ι | s ⊆ U ∧ v ∈ s ∧
              (∀ u ∈ s, u ∈ Vf → u ∈ insert v T) ∧ s.card ≤ 4 ∧ (s ∩ Bv).card ≤ 3} from
                ⟨hsU, hvs, hfree, h4, h3⟩) hxs))))
      · intro u hu j
        by_cases huv : u = v
        · rw [huv, Function.update_self]
          exact fun h => hxB (Or.inl (Or.inl (Or.inr (mem_iUnion.mpr ⟨j, h⟩))))
        · rw [Function.update_of_ne huv]
          exact hline u ((Finset.mem_insert.mp hu).resolve_left huv) j
      · intro u hu j hpre
        by_cases huv : u = v
        · rw [huv, Function.update_self]
          have hnle : ¬L0 ≤ P j := by
            rw [hL0]
            exact hpre (huv ▸ hvB)
          exact fun h => hxB (Or.inl (Or.inr (mem_biUnion hnle h)))
        · rw [Function.update_of_ne huv]
          exact hplane u ((Finset.mem_insert.mp hu).resolve_left huv) j hpre
      · intro β hβ _ hβB
        exact absurd (hβ.trans hinsB) hβB
      · exact hBkx x fun h => hxB (Or.inr h)
      · intro α hα _ _ _ hαB
        exact absurd (hα.trans hinsB) hαB
      · intro α hα _ _ _ _ hαB
        exact absurd (hα.trans hinsB) hαB
  have hphase2 : ∀ T : Finset ι, T ⊆ Vf.filter (· ∉ Bv) →
      ∃ φ, Inv (Vf.filter (· ∈ Bv) ∪ T) φ := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      obtain ⟨φ, hφ⟩ := hphase1 _ subset_rfl
      exact ⟨φ, by rwa [Finset.union_empty]⟩
    | @insert v T hvT ih =>
      intro hsub
      obtain ⟨φ, hfix, hclose, hlay, hguard, hline, hplane, htri, hskel, hfold, hcross⟩ :=
        ih ((Finset.subset_insert v T).trans hsub)
      have hvmem := Finset.mem_filter.mp (hsub (Finset.mem_insert_self v T))
      have hvV : v ∈ Vf := hvmem.1
      have hvB : v ∉ Bv := hvmem.2
      have hvU : v ∈ U := ((hVf v).mp hvV).1
      have hφ₀v : 0 < ℓ (φ₀ v) := lt_of_le_of_ne (hφ₀ v hvU).2
        fun h => hvB (((hφ₀ v hvU).1).mp h.symm)
      have hT'V : Vf.filter (· ∈ Bv) ∪ T ⊆ Vf := Finset.union_subset (Finset.filter_subset _ _)
        fun u hu => (Finset.mem_filter.mp (hsub (Finset.mem_insert_of_mem hu))).1
      rw [Finset.union_insert]
      obtain ⟨T', hT'⟩ : ∃ T' : Finset ι, T' = Vf.filter (· ∈ Bv) ∪ T := ⟨_, rfl⟩
      rw [← hT'] at hfix hlay hguard hline hplane htri hskel hfold hcross hT'V ⊢
      have hind : ∀ s ⊆ T', s.card ≤ 3 → AffineIndependent ℝ (fun u : s => φ u) := by
        intro s hs h3
        refine hguard s (fun u hu => ((hVf u).mp (hT'V (hs hu))).1) (fun u hu _ => hs hu)
          (by omega) ((Finset.card_le_card Finset.inter_subset_left).trans h3) ?_
        have hempty : IsEmpty (s.filter (· ∈ Afz)) := ⟨fun u =>
          ((hVf u).mp (hT'V (hs (Finset.mem_filter.mp u.2).1))).2 (Finset.mem_filter.mp u.2).2⟩
        exact affineIndependent_of_subsingleton ℝ _
      obtain ⟨Bt, hBt, hBtx⟩ := exists_dimH_lt_tri_update (v := v) φ S hS hline htri
      obtain ⟨Bs, hBs, hBsx⟩ := exists_dimH_lt_skeleton_update hvB φ S hS hind hline htri hskel
      obtain ⟨Bf, hBf, hBfx⟩ := exists_dimH_lt_fold_update (v := v) φ ℓ P hind hplane hfold
      obtain ⟨Bc, hBc, hBcx⟩ := exists_dimH_lt_cross_update (v := v) φ ℓ P hind hplane hcross
      obtain ⟨Bg, hBg⟩ : ∃ Bg : Set (EuclideanSpace ℝ (Fin 3)), Bg = ⋃ s ∈ {s : Finset ι |
          s ⊆ U ∧ v ∈ s ∧ (∀ u ∈ s, u ∈ Vf → u ∈ insert v T') ∧ s.card ≤ 4 ∧
            (s ∩ Bv).card ≤ 3}, (affineSpan ℝ (φ '' ↑(s.erase v)) : Set _) := ⟨_, rfl⟩
      have hBgsmall : dimH Bg < 3 := by
        have h := dimH_biUnion_inter_lt (hKg T' v)
          (fun s => (affineSpan ℝ (φ '' ↑(s.erase v)) : Set (EuclideanSpace ℝ (Fin 3)))) univ
          (c := 3) (by norm_num) fun s hs => by
            rw [inter_univ]
            refine dimH_lt_three_of_finrank_direction_le_two _ ?_
            have h1 := finrank_direction_affineSpan_image_le_card_sub_one (s.erase v) φ
            have h2 := Finset.card_erase_of_mem hs.2.1
            have h3 := hs.2.2.2.1
            omega
        rw [inter_univ] at h
        rw [hBg]
        exact h
      have hBSsmall : dimH (⋃ j, (S j : Set (EuclideanSpace ℝ (Fin 3)))) < 3 :=
        dimH_iUnion_lt_of_finite (by norm_num) fun j =>
          dimH_lt_three_of_finrank_direction_le_two (S j) (by rw [hS j]; norm_num)
      have hBPsmall : dimH (⋃ j, (P j : Set (EuclideanSpace ℝ (Fin 3)))) < 3 :=
        dimH_iUnion_lt_of_finite (by norm_num) fun j =>
          dimH_lt_three_of_finrank_direction_le_two (P j) (hP j)
      have hsmall3 : dimH (Bg ∪ (⋃ j, (S j : Set (EuclideanSpace ℝ (Fin 3)))) ∪
          (⋃ j, (P j : Set (EuclideanSpace ℝ (Fin 3)))) ∪ Bt ∪ Bs ∪ Bf ∪ Bc) < 3 := by
        rw [dimH_union, dimH_union, dimH_union, dimH_union, dimH_union, dimH_union]
        exact max_lt (max_lt (max_lt (max_lt (max_lt (max_lt hBgsmall hBSsmall) hBPsmall) hBt)
          hBs) hBf) hBc
      have hsmall : dimH ((Bg ∪ (⋃ j, (S j : Set (EuclideanSpace ℝ (Fin 3)))) ∪
          (⋃ j, (P j : Set (EuclideanSpace ℝ (Fin 3)))) ∪ Bt ∪ Bs ∪ Bf ∪ Bc) ∩
            (⊤ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)))) <
          Module.finrank ℝ (⊤ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3))).direction := by
        rw [AffineSubspace.top_coe, inter_univ, AffineSubspace.direction_top, finrank_top,
          finrank_euclideanSpace_fin]
        exact_mod_cast hsmall3
      have hUx : ball (φ₀ v) ε ∩ {q | 0 < ℓ q} ∈ 𝓝 (φ₀ v) :=
        Filter.inter_mem (ball_mem_nhds _ hε) ((isOpen_lt continuous_const
          (LinearMap.continuous_of_finiteDimensional ℓ)).mem_nhds hφ₀v)
      obtain ⟨x, -, hxU, hxB⟩ := exists_mem_inter_notMem_of_dimH_inter_lt ⊤
        (AffineSubspace.mem_top ℝ (EuclideanSpace ℝ (Fin 3)) (φ₀ v)) hUx hsmall
      refine ⟨Function.update φ v x, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro u hu
        have huv : u ≠ v := fun h => hu (by
          rw [h]
          exact Finset.mem_coe.mpr (Finset.mem_insert_self v T'))
        rw [Function.update_of_ne huv]
        exact hfix fun h => hu (Finset.mem_coe.mpr (Finset.mem_insert_of_mem h))
      · intro u
        by_cases huv : u = v
        · rw [huv, Function.update_self]
          exact mem_ball.mp hxU.1
        · rw [Function.update_of_ne huv]
          exact hclose u
      · intro u hu
        by_cases huv : u = v
        · rw [huv, Function.update_self]
          exact ⟨fun h => absurd h hvB, fun _ => hxU.2⟩
        · rw [Function.update_of_ne huv]
          exact hlay u ((Finset.mem_insert.mp hu).resolve_left huv)
      · exact guard_update_of_forall_notMem_affineSpan hVf hvV hguard
          fun s hsU hvs hfree h4 h3 hxs => hxB (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
            (Or.inl (by
              rw [hBg]
              exact mem_biUnion (show s ∈ {s : Finset ι | s ⊆ U ∧ v ∈ s ∧
                (∀ u ∈ s, u ∈ Vf → u ∈ insert v T') ∧ s.card ≤ 4 ∧ (s ∩ Bv).card ≤ 3} from
                  ⟨hsU, hvs, hfree, h4, h3⟩) hxs)))))))
      · intro u hu j
        by_cases huv : u = v
        · rw [huv, Function.update_self]
          exact fun h => hxB (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
            (Or.inr (mem_iUnion.mpr ⟨j, h⟩)))))))
        · rw [Function.update_of_ne huv]
          exact hline u ((Finset.mem_insert.mp hu).resolve_left huv) j
      · intro u hu j hpre
        by_cases huv : u = v
        · rw [huv, Function.update_self]
          exact fun h => hxB (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (mem_iUnion.mpr ⟨j, h⟩))))))
        · rw [Function.update_of_ne huv]
          exact hplane u ((Finset.mem_insert.mp hu).resolve_left huv) j hpre
      · exact hBtx x fun h => hxB (Or.inl (Or.inl (Or.inl (Or.inr h))))
      · exact hBsx x fun h => hxB (Or.inl (Or.inl (Or.inr h)))
      · exact hBfx x fun h => hxB (Or.inl (Or.inr h))
      · exact hBcx x fun h => hxB (Or.inr h)
  have hfinal := hphase2 (Vf.filter (· ∉ Bv)) subset_rfl
  have hVeq : Vf.filter (· ∈ Bv) ∪ Vf.filter (· ∉ Bv) = Vf :=
    Finset.filter_union_filter_not_eq _ _
  rw [hVeq] at hfinal
  obtain ⟨φ, hfix, hclose, hlay, hguard, -, hplane, -, hskel, hfold, hcross⟩ := hfinal
  exact ⟨φ, hfix, hclose, hlay, fun s hsU h4 h3 => hguard s hsU (fun u _ hu => hu) h4 h3, hplane,
    hskel, hfold, hcross⟩

end DifferentialGeometry.Topology.PiecewiseLinear
