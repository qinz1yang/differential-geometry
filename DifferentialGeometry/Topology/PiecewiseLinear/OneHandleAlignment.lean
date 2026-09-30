/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CylinderEndExtension
import DifferentialGeometry.Topology.PiecewiseLinear.TwoHandleAlignment

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_oneHandle_end_assignment {M : Type} [TopologicalSpace M] [T2Space M]
    (ψ : {z : Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1 |
      z.val ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ)} → M)
    (hψ : Continuous ψ) (f : Fin 2 → EuclideanSpace ℝ (Fin 2) → M) (hf : ∀ j, Continuous (f j))
    (hdisj : Disjoint (range (f 0)) (range (f 1)))
    (hrange : range ψ = ⋃ j, f j '' closedBall 0 1) :
    ∃ Fb Ft : EuclideanSpace ℝ (Fin 2) → M, ((Fb = f 0 ∧ Ft = f 1) ∨ (Fb = f 1 ∧ Ft = f 0)) ∧
      ψ '' {z | z.val.val.2 = 0} = Fb '' closedBall 0 1 ∧
      ψ '' {z | z.val.val.2 = 1} = Ft '' closedBall 0 1 := by
  classical
  let C : Fin 2 → Set M := fun j => f j '' closedBall 0 1
  have hCc : ∀ j, IsClosed (C j) := fun j => ((isCompact_closedBall _ _).image (hf j)).isClosed
  have hCne : ∀ j, (C j).Nonempty := fun j => ⟨f j 0, 0, mem_closedBall_self zero_le_one, rfl⟩
  have hCdisj : C 0 ∩ C 1 = ∅ := by
    refine eq_empty_iff_forall_notMem.mpr fun x hx => ?_
    obtain ⟨⟨u, -, hu⟩, ⟨v, -, hv⟩⟩ := hx
    exact hdisj.ne_of_mem ⟨u, rfl⟩ ⟨v, rfl⟩ (hu.trans hv.symm)
  have hrange' : range ψ = C 0 ∪ C 1 := by
    rw [hrange]
    ext x
    simp only [mem_iUnion, mem_union, Fin.exists_fin_two]
    rfl
  have hend : ∀ e : ℝ, (e = 0 ∨ e = 1) → IsPreconnected (ψ '' {z | z.val.val.2 = e}) := by
    intro e he
    have heI : e ∈ Icc (0 : ℝ) 1 := by
      rcases he with rfl | rfl
      · exact ⟨le_rfl, zero_le_one⟩
      · exact ⟨zero_le_one, le_rfl⟩
    have he2 : e ∈ ({0, 1} : Set ℝ) := by
      rcases he with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    let ι : Convexity.StdSimplex.coordinateSet ℝ (Fin 3) → {z : Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1 |
        z.val ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ)} := fun x =>
      ⟨⟨(x.val, e), x.2, heI⟩, x.2, he2⟩
    have hι : Continuous ι :=
      ((continuous_subtype_val.prodMk continuous_const).subtype_mk _).subtype_mk _
    have himg : ψ '' {z | z.val.val.2 = e} = range (ψ ∘ ι) := by
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        refine ⟨⟨z.val.val.1, z.2.1⟩, ?_⟩
        have hz' : ι ⟨z.val.val.1, z.2.1⟩ = z := by
          apply Subtype.ext
          apply Subtype.ext
          exact Prod.ext rfl hz.symm
        change ψ (ι _) = ψ z
        rw [hz']
      · rintro ⟨x, rfl⟩
        exact ⟨ι x, rfl, rfl⟩
    rw [himg]
    let : PreconnectedSpace (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) :=
      Subtype.preconnectedSpace (Convexity.StdSimplex.convex_coordinateSet ℝ (Fin 3)).isPreconnected
    exact isPreconnected_range (hψ.comp hι)
  have hsplit : ∀ e : ℝ, (e = 0 ∨ e = 1) →
      ψ '' {z | z.val.val.2 = e} ⊆ C 0 ∨ ψ '' {z | z.val.val.2 = e} ⊆ C 1 := by
    intro e he
    refine isPreconnected_iff_subset_of_disjoint_closed.mp (hend e he) (C 0) (C 1) (hCc 0)
      (hCc 1) ?_ ?_
    · rw [← hrange']
      exact image_subset_range _ _
    · rw [hCdisj, inter_empty]
  have hcover : range ψ = ψ '' {z | z.val.val.2 = 0} ∪ ψ '' {z | z.val.val.2 = 1} := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      rcases z.2.2 with h | h
      · exact Or.inl ⟨z, h, rfl⟩
      · exact Or.inr ⟨z, h, rfl⟩
    · rintro (⟨z, -, rfl⟩ | ⟨z, -, rfl⟩) <;> exact ⟨z, rfl⟩
  have hkey : ∀ j k : Fin 2, C j ∩ C k = ∅ →
      ψ '' {z | z.val.val.2 = 0} ⊆ C j → ψ '' {z | z.val.val.2 = 1} ⊆ C k →
      ψ '' {z | z.val.val.2 = 0} = C j ∧ ψ '' {z | z.val.val.2 = 1} = C k := by
    intro j k hjk h0 h1
    have hC : C j ∪ C k = range ψ := by
      rw [hrange']
      fin_cases j <;> fin_cases k
      · simp only [inter_self] at hjk
        exact absurd hjk (hCne 0).ne_empty
      · rfl
      · exact union_comm _ _
      · simp only [inter_self] at hjk
        exact absurd hjk (hCne 1).ne_empty
    constructor
    · refine subset_antisymm h0 fun x hx => ?_
      have hx' : x ∈ range ψ := by rw [← hC]; exact Or.inl hx
      rw [hcover] at hx'
      rcases hx' with hx' | hx'
      · exact hx'
      · have : x ∈ C j ∩ C k := ⟨hx, h1 hx'⟩
        rw [hjk] at this
        exact absurd this (notMem_empty x)
    · refine subset_antisymm h1 fun x hx => ?_
      have hx' : x ∈ range ψ := by rw [← hC]; exact Or.inr hx
      rw [hcover] at hx'
      rcases hx' with hx' | hx'
      · have : x ∈ C j ∩ C k := ⟨h0 hx', hx⟩
        rw [hjk] at this
        exact absurd this (notMem_empty x)
      · exact hx'
  have hsame : ∀ j : Fin 2, ψ '' {z | z.val.val.2 = 0} ⊆ C j →
      ψ '' {z | z.val.val.2 = 1} ⊆ C j → False := by
    intro j h0 h1
    have hall : range ψ ⊆ C j := by
      rw [hcover]
      exact union_subset h0 h1
    rw [hrange'] at hall
    have h01 : C 0 ⊆ C j := subset_union_left.trans hall
    have h11 : C 1 ⊆ C j := subset_union_right.trans hall
    obtain ⟨x0, hx0⟩ := hCne 0
    obtain ⟨x1, hx1⟩ := hCne 1
    fin_cases j
    · have : x1 ∈ C 0 ∩ C 1 := ⟨h11 hx1, hx1⟩
      rw [hCdisj] at this
      exact notMem_empty _ this
    · have : x0 ∈ C 0 ∩ C 1 := ⟨hx0, h01 hx0⟩
      rw [hCdisj] at this
      exact notMem_empty _ this
  rcases hsplit 0 (Or.inl rfl) with h0 | h0 <;> rcases hsplit 1 (Or.inr rfl) with h1 | h1
  · exact (hsame 0 h0 h1).elim
  · obtain ⟨e0, e1⟩ := hkey 0 1 hCdisj h0 h1
    exact ⟨f 0, f 1, Or.inl ⟨rfl, rfl⟩, e0, e1⟩
  · obtain ⟨e0, e1⟩ := hkey 1 0 (by rw [inter_comm]; exact hCdisj) h0 h1
    exact ⟨f 1, f 0, Or.inr ⟨rfl, rfl⟩, e0, e1⟩
  · exact (hsame 1 h0 h1).elim

theorem exists_endDisk_homeomorph {M : Type} [TopologicalSpace M] [CompactSpace M]
    (ψ : {z : Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1 |
      z.val ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ)} → M)
    (hψ : IsClosedEmbedding ψ) (F : EuclideanSpace ℝ (Fin 2) → M) (hF : IsEmbedding F)
    {e : ℝ} (he : e = 0 ∨ e = 1) (himg : ψ '' {z | z.val.val.2 = e} = F '' closedBall 0 1) :
    ∃ γ : closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ
        closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,
      ∀ z : {z : Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1 |
        z.val ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ)}, z.val.val.2 = e →
        ∀ w : closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,
          w.val = (prismCylinderMap z.val).1 → F (γ w).val = ψ z := by
  classical
  have hAc : CompactSpace {z : Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1 |
      z.val ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ)} := hψ.compactSpace
  let Ae : Set {z : Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1 |
      z.val ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ)} := {z | z.val.val.2 = e}
  have hAec : CompactSpace Ae := isCompact_iff_compactSpace.mp
    ((isClosed_eq ((continuous_snd.comp continuous_subtype_val).comp continuous_subtype_val)
      continuous_const).isCompact)
  have heI : e ∈ Icc (0 : ℝ) 1 := by
    rcases he with rfl | rfl
    · exact ⟨le_rfl, zero_le_one⟩
    · exact ⟨zero_le_one, le_rfl⟩
  have he2 : e ∈ ({0, 1} : Set ℝ) := by
    rcases he with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  let mEf : Ae → closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
    fun z => (prismBallHomeomorph z.val.val).1
  have hmEc : Continuous mEf :=
    continuous_fst.comp (prismBallHomeomorph.continuous.comp
      (continuous_subtype_val.comp continuous_subtype_val))
  have hmEinj : Function.Injective mEf := by
    intro z z' h
    apply Subtype.ext
    apply Subtype.ext
    apply prismBallHomeomorph.injective
    refine Prod.ext h (Subtype.ext ?_)
    change z.val.val.val.2 = z'.val.val.val.2
    rw [z.2, z'.2]
  have hmEsurj : Function.Surjective mEf := by
    intro w
    let p := prismBallHomeomorph.symm (w, ⟨e, heI⟩)
    have hp : prismBallHomeomorph p = (w, ⟨e, heI⟩) := prismBallHomeomorph.apply_symm_apply _
    have hp2 : p.val.2 = e := congrArg (fun x => (x.2 : ℝ)) hp
    refine ⟨⟨⟨p, p.2.1, by rw [hp2]; exact he2⟩, hp2⟩, ?_⟩
    change (prismBallHomeomorph p).1 = w
    rw [hp]
  let mE : Ae ≃ₜ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
    hmEc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective mEf ⟨hmEinj, hmEsurj⟩)
  have hψe : IsEmbedding (fun z : Ae => ψ z.val) := hψ.isEmbedding.comp IsEmbedding.subtypeVal
  have hr : range (fun z : Ae => ψ z.val) = F '' closedBall 0 1 := by
    rw [← himg]
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z.val, z.2, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩
  let γ := mE.symm.trans (hψe.toHomeomorph.trans ((Homeomorph.setCongr hr).trans
    (hF.homeomorphImage (closedBall 0 1)).symm))
  have hγ : ∀ w, F (γ w).val = ψ (mE.symm w).val := by
    intro w
    have h := congrArg Subtype.val ((hF.homeomorphImage (closedBall 0 1)).apply_symm_apply
      ((Homeomorph.setCongr hr) (hψe.toHomeomorph (mE.symm w))))
    exact h
  refine ⟨γ, fun z hz w hw => ?_⟩
  rw [hγ]
  have hw' : w = mE ⟨z, hz⟩ := Subtype.ext hw
  rw [hw', mE.symm_apply_apply]

noncomputable def closedBallReflection :
    closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
  planarReflection.toHomeomorph.subtype fun x => by
    change x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ↔ planarReflection x ∈ closedBall 0 1
    rw [mem_closedBall_zero_iff, mem_closedBall_zero_iff, planarReflection.norm_map]

theorem closedBallReflection_apply (w : closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) :
    (closedBallReflection w : EuclideanSpace ℝ (Fin 2)) = planarReflection w := rfl

theorem exists_oneHandle_alignment {M : Type} [TopologicalSpace M] [CompactSpace M]
    (ψ : {z : Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1 |
      z.val ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ)} → M)
    (hψ : IsClosedEmbedding ψ) (Fb Ft : EuclideanSpace ℝ (Fin 2) → M) (hFb : IsEmbedding Fb)
    (hFt : IsEmbedding Ft) (hb : ψ '' {z | z.val.val.2 = 0} = Fb '' closedBall 0 1)
    (ht : ψ '' {z | z.val.val.2 = 1} = Ft '' closedBall 0 1) :
    ∃ (L : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
      (Ext : (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1 : Set ((Fin 3 → ℝ) × ℝ)) →
        EuclideanSpace ℝ (Fin 2) × ℝ),
      (L = id ∨ L = planarReflection) ∧ IsClosedEmbedding Ext ∧ range Ext = closedBall 0 1 ∧
      (∀ b, ‖(Ext b).1‖ = 1 ↔ b.val.1 ∈ stdSimplexBoundary 2) ∧
      (∀ b, |(Ext b).2| = 1 ↔ b.val.2 = 0 ∨ b.val.2 = 1) ∧
      (∀ z : {z : Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1 |
        z.val ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ)}, z.val.val.2 = 0 →
          (Ext z.val).2 = -1 ∧ Fb (Ext z.val).1 = ψ z) ∧
      ∀ z : {z : Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1 |
        z.val ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ)}, z.val.val.2 = 1 →
          (Ext z.val).2 = 1 ∧ Ft (L (Ext z.val).1) = ψ z := by
  classical
  have hPc : CompactSpace (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1 : Set ((Fin 3 → ℝ) × ℝ)) :=
    isCompact_iff_compactSpace.mp ((Convexity.StdSimplex.isCompact_coordinateSet ℝ (Fin 3)).prod isCompact_Icc)
  obtain ⟨γb, hγb⟩ := exists_endDisk_homeomorph ψ hψ Fb hFb (Or.inl rfl) hb
  obtain ⟨γt, hγt⟩ := exists_endDisk_homeomorph ψ hψ Ft hFt (Or.inr rfl) ht
  have hchoice : ∃ (L : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
      (γt' : closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ
        closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1),
      (L = id ∨ L = planarReflection) ∧ (∀ w, Ft (L (γt' w).val) = Ft (γt w).val) ∧
      (HasIncreasingCircleLift
          (fun θ => planarCircleParam.symm (rimHomeomorph γb (planarCircleParam θ))) ↔
        HasIncreasingCircleLift
          (fun θ => planarCircleParam.symm (rimHomeomorph γt' (planarCircleParam θ)))) := by
    by_cases hor : (HasIncreasingCircleLift
          (fun θ => planarCircleParam.symm (rimHomeomorph γb (planarCircleParam θ))) ↔
        HasIncreasingCircleLift
          (fun θ => planarCircleParam.symm (rimHomeomorph γt (planarCircleParam θ))))
    · exact ⟨id, γt, Or.inl rfl, fun w => rfl, hor⟩
    · refine ⟨planarReflection, γt.trans closedBallReflection, Or.inr rfl, fun w => ?_, ?_⟩
      · change Ft (planarReflection (planarReflection (γt w).val)) = Ft (γt w).val
        rw [planarReflection_planarReflection]
      · have hrim : (fun θ => planarCircleParam.symm
            (rimHomeomorph (γt.trans closedBallReflection) (planarCircleParam θ))) =
            fun θ => planarCircleParam.symm
              (sphereReflection (rimHomeomorph γt (planarCircleParam θ))) := by
          funext θ
          congr 1
        rw [hrim, hasIncreasingCircleLift_reflect_iff]
        constructor
        · intro hA hB
          exact hor ⟨fun _ => hB, fun _ => hA⟩
        · intro hnB
          by_contra hA
          exact hor ⟨fun h => absurd h hA, fun h => absurd h hnB⟩
  obtain ⟨L, γt', hL, hLγ, hor⟩ := hchoice
  obtain ⟨Φ, hΦn, hΦb, hΦt, hΦside⟩ := exists_homeomorph_extension_of_ends γb γt' hor
  have hball : ∀ b, prismCylinderMap b ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2) × ℝ) 1 := by
    intro b
    rw [← range_prismCylinderMap]
    exact ⟨b, rfl⟩
  have hΦball : ∀ q ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2) × ℝ) 1,
      Φ q ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2) × ℝ) 1 := by
    intro q hq
    rw [mem_closedBall_zero_iff, hΦn]
    exact mem_closedBall_zero_iff.mp hq
  have hcap : ∀ q ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2) × ℝ) 1, q ∉ cylinderSide →
      ‖q‖ = 1 → ‖(Φ q).1‖ < 1 ∧ (Φ q).2 = q.2 := by
    intro q hq hs hn
    obtain ⟨hq1, hq2⟩ := norm_fst_lt_one_of_notMem_cylinderSide hn hs
    have hw : q.1 ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
      mem_closedBall_zero_iff.mpr hq1.le
    rcases (abs_eq zero_le_one).mp hq2 with h | h
    · have hqe : q = ((⟨q.1, hw⟩ : closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1).val, 1) :=
        Prod.ext rfl h
      rw [hqe, hΦt]
      exact ⟨norm_lt_one_of_closedBall_homeomorph γt' _ hq1, rfl⟩
    · have hqe : q = ((⟨q.1, hw⟩ : closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1).val, -1) :=
        Prod.ext rfl h
      rw [hqe, hΦb]
      exact ⟨norm_lt_one_of_closedBall_homeomorph γb _ hq1, rfl⟩
  refine ⟨L, fun p => Φ (prismCylinderMap p), hL, ?_, ?_, fun b => ?_, fun b => ?_,
    fun z hz => ?_, fun z hz => ?_⟩
  · exact (Φ.continuous.comp continuous_prismCylinderMap).isClosedEmbedding
      (Φ.injective.comp prismCylinderMap_injective)
  · ext y
    constructor
    · rintro ⟨p, rfl⟩
      exact hΦball _ (hball p)
    · intro hy
      have hy' : Φ.symm y ∈ range prismCylinderMap := by
        rw [range_prismCylinderMap, mem_closedBall_zero_iff, ← hΦn, Φ.apply_symm_apply]
        exact mem_closedBall_zero_iff.mp hy
      obtain ⟨p, hp⟩ := hy'
      refine ⟨p, ?_⟩
      change Φ (prismCylinderMap p) = y
      rw [hp, Φ.apply_symm_apply]
  · change ‖(Φ (prismCylinderMap b)).1‖ = 1 ↔ _
    rw [← norm_prismCylinderMap_fst_eq_one_iff]
    have hq := hball b
    constructor
    · intro h
      by_contra hne
      have hs : prismCylinderMap b ∉ cylinderSide := fun hs => hne hs.1
      have hn : ‖prismCylinderMap b‖ = 1 := by
        rw [← hΦn]
        refine le_antisymm (mem_closedBall_zero_iff.mp (hΦball _ hq)) ?_
        rw [← h]
        exact norm_fst_le _
      have := (hcap _ hq hs hn).1
      rw [h] at this
      exact lt_irrefl _ this
    · intro h
      have hs : prismCylinderMap b ∈ cylinderSide :=
        ⟨h, (mem_closedBall_zero_prod_iff.mp hq).2⟩
      exact (hΦside _ hs).1.1
  · change |(Φ (prismCylinderMap b)).2| = 1 ↔ _
    have hmb : |(prismCylinderMap b).2| = 1 ↔ b.val.2 = 0 ∨ b.val.2 = 1 := by
      rw [prismCylinderMap_snd]
      obtain ⟨h0, h1⟩ := b.2.2
      constructor
      · intro h
        rcases (abs_eq zero_le_one).mp h with h | h
        · right
          linarith
        · left
          linarith
      · rintro (h | h) <;> rw [h] <;> norm_num
    rw [← hmb]
    have hq := hball b
    by_cases hn : ‖prismCylinderMap b‖ = 1
    · by_cases hs : prismCylinderMap b ∈ cylinderSide
      · rw [(hΦside _ hs).2]
      · rw [(hcap _ hq hs hn).2]
    · have hlt : ‖prismCylinderMap b‖ < 1 :=
        lt_of_le_of_ne (mem_closedBall_zero_iff.mp hq) hn
      have h1 : |(prismCylinderMap b).2| < 1 := by
        rw [← Real.norm_eq_abs]
        exact lt_of_le_of_lt (norm_snd_le _) hlt
      have h2 : |(Φ (prismCylinderMap b)).2| < 1 := by
        rw [← Real.norm_eq_abs]
        exact lt_of_le_of_lt (norm_snd_le _) (by rw [hΦn]; exact hlt)
      exact ⟨fun h => absurd h h2.ne, fun h => absurd h h1.ne⟩
  · let w : closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := (prismBallHomeomorph z.val).1
    have hm : prismCylinderMap z.val = (w.val, -1) := by
      refine Prod.ext rfl ?_
      rw [prismCylinderMap_snd, hz]
      norm_num
    change (Φ (prismCylinderMap z.val)).2 = -1 ∧ Fb (Φ (prismCylinderMap z.val)).1 = ψ z
    rw [hm, hΦb]
    exact ⟨rfl, hγb z hz w rfl⟩
  · let w : closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := (prismBallHomeomorph z.val).1
    have hm : prismCylinderMap z.val = (w.val, 1) := by
      refine Prod.ext rfl ?_
      rw [prismCylinderMap_snd, hz]
      norm_num
    change (Φ (prismCylinderMap z.val)).2 = 1 ∧ Ft (L (Φ (prismCylinderMap z.val)).1) = ψ z
    rw [hm, hΦt]
    exact ⟨rfl, (hLγ w).trans (hγt z hz w rfl)⟩

end DifferentialGeometry.Topology.PiecewiseLinear
