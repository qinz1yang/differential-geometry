/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CylinderSideExtension
import DifferentialGeometry.Topology.PiecewiseLinear.PrismAnnulusChart
import DifferentialGeometry.Topology.PiecewiseLinear.TwoHandleModelAttachment

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

noncomputable def prismCylinderMap
    (p : (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1 : Set ((Fin 3 → ℝ) × ℝ))) :
    EuclideanSpace ℝ (Fin 2) × ℝ :=
  (((prismBallHomeomorph p).1 : EuclideanSpace ℝ (Fin 2)),
    2 * ((prismBallHomeomorph p).2 : ℝ) - 1)

theorem prismCylinderMap_snd
    (p : (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1 : Set ((Fin 3 → ℝ) × ℝ))) :
    (prismCylinderMap p).2 = 2 * p.val.2 - 1 := rfl

theorem norm_prismCylinderMap_fst_eq_one_iff
    (p : (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1 : Set ((Fin 3 → ℝ) × ℝ))) :
    ‖(prismCylinderMap p).1‖ = 1 ↔ p.val.1 ∈ stdSimplexBoundary 2 := by
  rw [← prismBallHomeomorph_mem_sphere_iff p, mem_sphere_zero_iff_norm]
  rfl

theorem continuous_prismCylinderMap : Continuous prismCylinderMap :=
  (continuous_subtype_val.comp (continuous_fst.comp prismBallHomeomorph.continuous)).prodMk
    ((continuous_const.mul (continuous_subtype_val.comp
      (continuous_snd.comp prismBallHomeomorph.continuous))).sub continuous_const)

theorem prismCylinderMap_injective : Function.Injective prismCylinderMap := by
  intro p p' h
  apply prismBallHomeomorph.injective
  have h1 := congrArg Prod.fst h
  have h2 : 2 * p.val.2 - 1 = 2 * p'.val.2 - 1 := congrArg Prod.snd h
  refine Prod.ext (Subtype.ext h1) (Subtype.ext ?_)
  change p.val.2 = p'.val.2
  linarith

theorem range_prismCylinderMap : range prismCylinderMap = closedBall 0 1 := by
  ext q
  rw [mem_closedBall_zero_prod_iff]
  constructor
  · rintro ⟨p, rfl⟩
    have h1 := (prismBallHomeomorph p).1.2
    obtain ⟨h2, h3⟩ := p.2.2
    refine ⟨mem_closedBall_zero_iff.mp h1, abs_le.mpr ⟨?_, ?_⟩⟩
    · rw [prismCylinderMap_snd]
      linarith
    · rw [prismCylinderMap_snd]
      linarith
  · rintro ⟨h1, h2⟩
    obtain ⟨h2a, h2b⟩ := abs_le.mp h2
    have hI : (q.2 + 1) / 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    refine ⟨prismBallHomeomorph.symm (⟨q.1, mem_closedBall_zero_iff.mpr h1⟩, ⟨_, hI⟩), ?_⟩
    change (((prismBallHomeomorph (prismBallHomeomorph.symm _)).1 : EuclideanSpace ℝ (Fin 2)),
      2 * ((prismBallHomeomorph (prismBallHomeomorph.symm _)).2 : ℝ) - 1) = q
    rw [Homeomorph.apply_symm_apply]
    refine Prod.ext rfl ?_
    change 2 * ((q.2 + 1) / 2) - 1 = q.2
    ring

theorem abs_snd_eq_one_iff_norm_eq_one {q : EuclideanSpace ℝ (Fin 2) × ℝ}
    (hs : q ∉ cylinderSide) (hq : q ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2) × ℝ) 1) :
    |q.2| = 1 ↔ ‖q‖ = 1 := by
  constructor
  · intro h
    have h1 := (mem_closedBall_zero_prod_iff.mp hq).1
    rw [Prod.norm_def, Real.norm_eq_abs, h]
    exact max_eq_right h1
  · intro h
    exact (norm_fst_lt_one_of_notMem_cylinderSide h hs).2

theorem exists_twoHandle_alignment {M : Type} [TopologicalSpace M] [CompactSpace M]
    (ψ : {z : Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1 |
      z.val ∈ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1} → M)
    (hψ : IsClosedEmbedding ψ) (f : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × ℝ → M)
    (hf : IsEmbedding f) (hrange : range ψ = f '' (univ ×ˢ Icc (0 : ℝ) 1)) :
    ∃ (Ext : (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1 : Set ((Fin 3 → ℝ) × ℝ)) →
        EuclideanSpace ℝ (Fin 2) × ℝ)
      (g : {z : Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1 |
        z.val ∈ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1} →
          Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × ℝ),
      IsClosedEmbedding Ext ∧ range Ext = closedBall 0 1 ∧
      (∀ b, ‖(Ext b).1‖ = 1 ↔ b.val.1 ∈ stdSimplexBoundary 2) ∧
      (∀ b, |(Ext b).2| = 1 ↔ b.val.2 = 0 ∨ b.val.2 = 1) ∧
      (∀ z, f (g z) = ψ z) ∧
      ∀ z, Ext z.val = (((g z).1 : EuclideanSpace ℝ (Fin 2)), 2 * (g z).2 - 1) := by
  classical
  have hAc : CompactSpace {z : Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1 |
      z.val ∈ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1} := hψ.compactSpace
  have hPc : CompactSpace (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1 : Set ((Fin 3 → ℝ) × ℝ)) :=
    isCompact_iff_compactSpace.mp ((Convexity.StdSimplex.isCompact_coordinateSet ℝ (Fin 3)).prod isCompact_Icc)
  have hmem : ∀ z : {z : Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1 |
      z.val ∈ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1}, prismCylinderMap z.val ∈ cylinderSide := by
    intro z
    refine ⟨(norm_prismCylinderMap_fst_eq_one_iff _).mpr z.2.1, ?_⟩
    rw [prismCylinderMap_snd]
    obtain ⟨h0, h1⟩ := z.2.2
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  let mAf : {z : Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1 |
      z.val ∈ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1} → cylinderSide := fun z => ⟨_, hmem z⟩
  have hmAc : Continuous mAf :=
    (continuous_prismCylinderMap.comp continuous_subtype_val).subtype_mk _
  have hmAinj : Function.Injective mAf := fun z z' h =>
    Subtype.ext (prismCylinderMap_injective (congrArg Subtype.val h))
  have hmAsurj : Function.Surjective mAf := by
    intro q
    have hq : q.val ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2) × ℝ) 1 :=
      mem_closedBall_zero_iff.mpr (norm_eq_one_of_mem_cylinderSide q.2).le
    rw [← range_prismCylinderMap] at hq
    obtain ⟨p, hp⟩ := hq
    have hp1 : p.val.1 ∈ stdSimplexBoundary 2 :=
      (norm_prismCylinderMap_fst_eq_one_iff p).mp (by rw [hp]; exact q.2.1)
    exact ⟨⟨p, hp1, p.2.2⟩, Subtype.ext hp⟩
  let mA := hmAc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective mAf ⟨hmAinj, hmAsurj⟩)
  let T : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × ℝ) := univ ×ˢ Icc (0 : ℝ) 1
  let fT : T ≃ₜ f '' T := hf.homeomorphImage T
  let gH := hψ.isEmbedding.toHomeomorph.trans ((Homeomorph.setCongr hrange).trans fT.symm)
  have hgH : ∀ z, f (gH z).val = ψ z := by
    intro z
    have h := congrArg Subtype.val
      (fT.apply_symm_apply ((Homeomorph.setCongr hrange) (hψ.isEmbedding.toHomeomorph z)))
    exact h
  have hnT : ∀ x : T, (((x.val.1 : EuclideanSpace ℝ (Fin 2)), 2 * x.val.2 - 1) :
      EuclideanSpace ℝ (Fin 2) × ℝ) ∈ cylinderSide := by
    intro x
    obtain ⟨-, h0, h1⟩ := x.2
    exact ⟨norm_eq_of_mem_sphere x.val.1, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  have hnTinv : ∀ q : cylinderSide,
      ((⟨q.val.1, mem_sphere_zero_iff_norm.mpr q.2.1⟩ :
        Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1), (q.val.2 + 1) / 2) ∈ T := by
    intro q
    obtain ⟨h0, h1⟩ := abs_le.mp q.2.2
    exact ⟨mem_univ _, by linarith, by linarith⟩
  let nT : T ≃ₜ cylinderSide :=
    { toFun := fun x => ⟨_, hnT x⟩
      invFun := fun q => ⟨_, hnTinv q⟩
      left_inv := fun x => by
        apply Subtype.ext
        refine Prod.ext (Subtype.ext rfl) ?_
        change (2 * x.val.2 - 1 + 1) / 2 = x.val.2
        ring
      right_inv := fun q => by
        apply Subtype.ext
        refine Prod.ext rfl ?_
        change 2 * ((q.val.2 + 1) / 2) - 1 = q.val.2
        ring
      continuous_toFun :=
        ((continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)).prodMk
          ((continuous_const.mul (continuous_snd.comp continuous_subtype_val)).sub
            continuous_const)).subtype_mk _
      continuous_invFun :=
        ((((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
          (((continuous_snd.comp continuous_subtype_val).add continuous_const).div_const
            2)).subtype_mk _) }
  let σ : cylinderSide ≃ₜ cylinderSide := mA.symm.trans (gH.trans nT)
  obtain ⟨Φ, hΦn, hΦσ⟩ := exists_homeomorph_extension_of_cylinderSide σ
  refine ⟨fun p => Φ (prismCylinderMap p), fun z => (gH z).val, ?_, ?_, ?_, ?_, hgH, ?_⟩
  · exact (Φ.continuous.comp continuous_prismCylinderMap).isClosedEmbedding
      (Φ.injective.comp prismCylinderMap_injective)
  · ext y
    constructor
    · rintro ⟨p, rfl⟩
      rw [mem_closedBall_zero_iff, hΦn, ← mem_closedBall_zero_iff, ← range_prismCylinderMap]
      exact ⟨p, rfl⟩
    · intro hy
      have hy' : Φ.symm y ∈ range prismCylinderMap := by
        rw [range_prismCylinderMap, mem_closedBall_zero_iff, ← hΦn, Φ.apply_symm_apply]
        exact mem_closedBall_zero_iff.mp hy
      obtain ⟨p, hp⟩ := hy'
      refine ⟨p, ?_⟩
      change Φ (prismCylinderMap p) = y
      rw [hp, Φ.apply_symm_apply]
  · have hball : ∀ b, Φ (prismCylinderMap b) ∈
        closedBall (0 : EuclideanSpace ℝ (Fin 2) × ℝ) 1 := by
      intro b
      rw [mem_closedBall_zero_iff, hΦn, ← mem_closedBall_zero_iff, ← range_prismCylinderMap]
      exact ⟨b, rfl⟩
    intro b
    constructor
    · intro h
      have hside : Φ (prismCylinderMap b) ∈ cylinderSide :=
        ⟨h, (mem_closedBall_zero_prod_iff.mp (hball b)).2⟩
      obtain ⟨q, hq⟩ := σ.surjective ⟨_, hside⟩
      have h1 : Φ q.val = Φ (prismCylinderMap b) := by rw [hΦσ, hq]
      rw [← norm_prismCylinderMap_fst_eq_one_iff, ← Φ.injective h1]
      exact q.2.1
    · intro h
      have hs : prismCylinderMap b ∈ cylinderSide := by
        refine ⟨(norm_prismCylinderMap_fst_eq_one_iff b).mpr h, ?_⟩
        rw [prismCylinderMap_snd]
        obtain ⟨h0, h1⟩ := b.2.2
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      have he : Φ (prismCylinderMap b) = (σ ⟨_, hs⟩).val := hΦσ ⟨_, hs⟩
      change ‖(Φ (prismCylinderMap b)).1‖ = 1
      rw [he]
      exact (σ _).2.1
  · have hball : ∀ b, Φ (prismCylinderMap b) ∈
        closedBall (0 : EuclideanSpace ℝ (Fin 2) × ℝ) 1 := by
      intro b
      rw [mem_closedBall_zero_iff, hΦn, ← mem_closedBall_zero_iff, ← range_prismCylinderMap]
      exact ⟨b, rfl⟩
    intro b
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
    change |(Φ (prismCylinderMap b)).2| = 1 ↔ _
    rw [← hmb]
    by_cases hs : prismCylinderMap b ∈ cylinderSide
    · have he : Φ (prismCylinderMap b) = (σ ⟨_, hs⟩).val := hΦσ ⟨_, hs⟩
      rw [he]
      exact abs_snd_eq_one_iff_of_cylinderSide σ ⟨_, hs⟩
    · have hs' : Φ (prismCylinderMap b) ∉ cylinderSide := by
        intro h
        obtain ⟨q, hq⟩ := σ.surjective ⟨_, h⟩
        have h1 : Φ q.val = Φ (prismCylinderMap b) := by rw [hΦσ, hq]
        rw [← Φ.injective h1] at hs
        exact hs q.2
      have hmball : prismCylinderMap b ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2) × ℝ) 1 := by
        rw [← range_prismCylinderMap]
        exact ⟨b, rfl⟩
      rw [abs_snd_eq_one_iff_norm_eq_one hs' (hball b),
        abs_snd_eq_one_iff_norm_eq_one hs hmball, hΦn]
  · intro z
    change Φ (mA z).val = _
    rw [hΦσ]
    change (nT (gH (mA.symm (mA z)))).val = _
    rw [mA.symm_apply_apply]
    rfl

end DifferentialGeometry.Topology.PiecewiseLinear
