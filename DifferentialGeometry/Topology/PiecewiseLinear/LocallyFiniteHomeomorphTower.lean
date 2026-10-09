/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePieceTower
import DifferentialGeometry.Topology.PiecewiseLinear.PLMap

open Set Topology Filter

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] [HasGroupoid X (plGroupoid n)]

structure CompatiblePLHomeomorphTower
    (T : LocallyFinitePieceTower n X (Set.univ : Set X)) where
  stage : ℕ → X ≃ₜ X
  isPL_stage : ∀ i, IsPL n n (stage i)
  image_coreSpace : ∀ i, stage i '' T.coreSpace i = T.coreSpace i
  eqOn_coreSpace : ∀ i, EqOn (stage (i + 1)) (stage i) (T.coreSpace i)

structure PLHomeomorphIncrementSystem
    (T : LocallyFinitePieceTower n X (Set.univ : Set X)) where
  step : ℕ → X ≃ₜ X
  isPL_step : ∀ i, IsPL n n (step i)
  fixes_coreSpace : ∀ i, EqOn (step i) id (T.coreSpace i)
  image_coreSpace : ∀ i j, step i '' T.coreSpace j = T.coreSpace j

namespace PLHomeomorphIncrementSystem

variable {T : LocallyFinitePieceTower n X (Set.univ : Set X)}

def partialHomeomorph (S : PLHomeomorphIncrementSystem T) : ℕ → X ≃ₜ X
  | 0 => Homeomorph.refl X
  | i + 1 => (S.partialHomeomorph i).trans (S.step i)

omit [HasGroupoid X (plGroupoid n)] in
@[simp]
theorem partialHomeomorph_zero (S : PLHomeomorphIncrementSystem T) :
    S.partialHomeomorph 0 = Homeomorph.refl X := rfl

omit [HasGroupoid X (plGroupoid n)] in
@[simp]
theorem partialHomeomorph_succ_apply (S : PLHomeomorphIncrementSystem T) (i : ℕ) (x : X) :
    S.partialHomeomorph (i + 1) x = S.step i (S.partialHomeomorph i x) := rfl

omit [HasGroupoid X (plGroupoid n)] in
theorem isPL_partialHomeomorph (S : PLHomeomorphIncrementSystem T) :
    ∀ i, IsPL n n (S.partialHomeomorph i)
  | 0 => isPL_id
  | i + 1 => (S.isPL_step i).comp (S.isPL_partialHomeomorph i)

omit [HasGroupoid X (plGroupoid n)] in
theorem image_partialHomeomorph_coreSpace (S : PLHomeomorphIncrementSystem T) (i j : ℕ) :
    S.partialHomeomorph i '' T.coreSpace j = T.coreSpace j := by
  induction i with
  | zero =>
      change (id : X → X) '' T.coreSpace j = T.coreSpace j
      exact image_id (T.coreSpace j)
  | succ i ih =>
      calc
        S.partialHomeomorph (i + 1) '' T.coreSpace j =
            S.step i '' (S.partialHomeomorph i '' T.coreSpace j) := by
          apply Subset.antisymm
          · rintro y ⟨x, hx, rfl⟩
            exact ⟨S.partialHomeomorph i x, ⟨x, hx, rfl⟩, rfl⟩
          · rintro y ⟨z, ⟨x, hx, rfl⟩, rfl⟩
            exact ⟨x, hx, rfl⟩
        _ = T.coreSpace j := by rw [ih, S.image_coreSpace]

omit [HasGroupoid X (plGroupoid n)] in
theorem eqOn_partialHomeomorph_succ (S : PLHomeomorphIncrementSystem T) (i : ℕ) :
    EqOn (S.partialHomeomorph (i + 1)) (S.partialHomeomorph i) (T.coreSpace i) := by
  intro x hx
  rw [S.partialHomeomorph_succ_apply]
  have hmem : S.partialHomeomorph i x ∈ T.coreSpace i := by
    rw [← S.image_partialHomeomorph_coreSpace i i]
    exact ⟨x, hx, rfl⟩
  exact S.fixes_coreSpace i hmem

def toCompatibleTower (S : PLHomeomorphIncrementSystem T) : CompatiblePLHomeomorphTower T where
  stage := S.partialHomeomorph
  isPL_stage := S.isPL_partialHomeomorph
  image_coreSpace := fun i => S.image_partialHomeomorph_coreSpace i i
  eqOn_coreSpace := S.eqOn_partialHomeomorph_succ

end PLHomeomorphIncrementSystem

namespace LocallyFinitePieceTower

variable (T : LocallyFinitePieceTower n X (Set.univ : Set X))

open Classical in
noncomputable def prependEmpty [Nonempty X] :
    LocallyFinitePieceTower n X (Set.univ : Set X) where
  N
    | 0 => ∅
    | _ + 1 => T.N _
  piece
    | 0 => ⟨0, PLPieceIn.empty (EuclideanSpace ℝ (Fin 0))⟩
    | i + 1 => T.piece i
  subset_nhdsWithin i := by
    cases i with
    | zero => exact fun _ hx => hx.elim
    | succ i => exact T.subset_nhdsWithin i
  iUnion_eq := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
      cases i with
      | zero => exact hxi.elim
      | succ i => exact Set.mem_univ x
    · intro x _
      have hx : x ∈ ⋃ i, T.N i := T.iUnion_eq.symm ▸ Set.mem_univ x
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨i + 1, hxi⟩
  core
    | 0 => ⊥
    | i + 1 => T.core i
  core_le i := by
    cases i with
    | zero => exact fun _ hs => hs.elim
    | succ i => exact T.core_le i
  subset_core i := by
    cases i with
    | zero => exact fun _ hx => hx.elim
    | succ i => exact T.subset_core i
  coreImage
    | 0 => ⊥
    | i + 1 => T.coreImage i
  coreImage_le i := by
    cases i with
    | zero => exact fun _ hs => hs.elim
    | succ i => exact T.coreImage_le i
  embed
    | 0 => 0
    | i + 1 => T.embed i
  embedInv
    | 0 => 0
    | i + 1 => T.embedInv i
  embed_isGlueIso i := by
    cases i with
    | zero => exact ⟨fun _ hs => hs.elim, fun _ hs => hs.elim,
        fun _ hs => hs.elim, fun _ hs => hs.elim⟩
    | succ i => exact T.embed_isGlueIso i
  map_embed i := by
    cases i with
    | zero =>
        intro x hx
        rw [show (⊥ : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 0))).space = ∅ from
          space_bot] at hx
        exact hx.elim
    | succ i => exact T.map_embed i

omit [HasGroupoid X (plGroupoid n)] in
@[simp]
theorem prependEmpty_coreSpace_zero [Nonempty X] : T.prependEmpty.coreSpace 0 = ∅ := by
  rw [coreSpace, prependEmpty, space_bot, image_empty]

omit [HasGroupoid X (plGroupoid n)] in
@[simp]
theorem prependEmpty_coreSpace_succ [Nonempty X] (i : ℕ) :
    T.prependEmpty.coreSpace (i + 1) = T.coreSpace i := rfl

omit [HasGroupoid X (plGroupoid n)] in
noncomputable def coreIndex (x : X) : ℕ := by
  classical
  exact Nat.find (T.exists_mem_core_space (Set.mem_univ x))

omit [HasGroupoid X (plGroupoid n)] in
theorem mem_coreSpace_coreIndex (x : X) : x ∈ T.coreSpace (T.coreIndex x) := by
  classical
  exact Nat.find_spec (T.exists_mem_core_space (Set.mem_univ x))

omit [HasGroupoid X (plGroupoid n)] in
theorem coreIndex_le {i : ℕ} {x : X} (hx : x ∈ T.coreSpace i) : T.coreIndex x ≤ i := by
  classical
  exact Nat.find_min' (T.exists_mem_core_space (Set.mem_univ x)) hx

end LocallyFinitePieceTower

namespace PLHomeomorphIncrementSystem

open Classical in
noncomputable def single [Nonempty X] (P : PLPiece n X (Set.univ : Set X))
    (h : X ≃ₜ X) (hh : IsPL n n h) :
    PLHomeomorphIncrementSystem (LocallyFinitePieceTower.prependEmpty
      (LocallyFinitePieceTower.ofPiece P)) where
  step
    | 0 => h
    | _ + 1 => Homeomorph.refl X
  isPL_step i := by
    cases i with
    | zero => exact hh
    | succ _ => exact isPL_id
  fixes_coreSpace i := by
    cases i with
    | zero =>
        intro x hx
        rw [LocallyFinitePieceTower.prependEmpty_coreSpace_zero] at hx
        exact hx.elim
    | succ _ => exact fun _ _ => rfl
  image_coreSpace i j := by
    cases i with
    | zero =>
        cases j with
        | zero => simp
        | succ j =>
            rw [LocallyFinitePieceTower.prependEmpty_coreSpace_succ]
            rw [LocallyFinitePieceTower.coreSpace]
            change h '' (P.piece.map '' P.piece.complex.space) =
              P.piece.map '' P.piece.complex.space
            rw [P.piece.bijOn.image_eq]
            simpa only [image_univ] using h.surjective.range_eq
    | succ _ => simp

end PLHomeomorphIncrementSystem

namespace CompatiblePLHomeomorphTower

variable {T : LocallyFinitePieceTower n X (Set.univ : Set X)}

omit [HasGroupoid X (plGroupoid n)] in
theorem eqOn_coreSpace_of_le (H : CompatiblePLHomeomorphTower T) {i j : ℕ} (hij : i ≤ j) :
    EqOn (H.stage j) (H.stage i) (T.coreSpace i) := by
  induction j, hij using Nat.le_induction with
  | base => exact fun _ _ => rfl
  | succ j hij ih =>
      intro x hx
      exact (H.eqOn_coreSpace j (T.core_space_monotone hij hx)).trans (ih hx)

omit [HasGroupoid X (plGroupoid n)] in
theorem image_stage_coreSpace_of_le (H : CompatiblePLHomeomorphTower T)
    {i j : ℕ} (hij : i ≤ j) : H.stage j '' T.coreSpace i = T.coreSpace i := by
  apply Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    rw [H.eqOn_coreSpace_of_le hij hx]
    rw [← H.image_coreSpace i]
    exact ⟨x, hx, rfl⟩
  · intro y hy
    have hy' : y ∈ H.stage i '' T.coreSpace i := by
      rw [H.image_coreSpace i]
      exact hy
    obtain ⟨x, hx, rfl⟩ := hy'
    exact ⟨x, hx, H.eqOn_coreSpace_of_le hij hx⟩

noncomputable def limitMap (H : CompatiblePLHomeomorphTower T) : X → X :=
  fun x => H.stage (T.coreIndex x) x

omit [HasGroupoid X (plGroupoid n)] in
theorem limitMap_eq_stage (H : CompatiblePLHomeomorphTower T) {i : ℕ} {x : X}
    (hx : x ∈ T.coreSpace i) : H.limitMap x = H.stage i x := by
  exact (H.eqOn_coreSpace_of_le (T.coreIndex_le hx) (T.mem_coreSpace_coreIndex x)).symm

omit [HasGroupoid X (plGroupoid n)] in
theorem image_limitMap_coreSpace (H : CompatiblePLHomeomorphTower T) (i : ℕ) :
    H.limitMap '' T.coreSpace i = T.coreSpace i := by
  apply Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    rw [H.limitMap_eq_stage hx]
    rw [← H.image_coreSpace i]
    exact ⟨x, hx, rfl⟩
  · intro y hy
    have hy' : y ∈ H.stage i '' T.coreSpace i := by
      rw [H.image_coreSpace i]
      exact hy
    obtain ⟨x, hx, rfl⟩ := hy'
    exact ⟨x, hx, H.limitMap_eq_stage hx⟩

omit [HasGroupoid X (plGroupoid n)] in
theorem isPL_limitMap (H : CompatiblePLHomeomorphTower T) : IsPL n n H.limitMap := by
  intro x
  obtain ⟨i, hxi⟩ := T.exists_mem_core_space (Set.mem_univ x)
  have hxN : x ∈ T.N i := T.core_space_subset i hxi
  have hnhds : T.coreSpace (i + 2) ∈ nhds x := by
    simpa only [nhdsWithin_univ] using T.core_space_mem_nhdsWithin hxN
  apply piecewiseAffineProperty_localInvariantProp.liftPropAt_congr_of_eventuallyEq
    (H.isPL_stage (i + 2) x)
  filter_upwards [hnhds] with y hy
  exact H.limitMap_eq_stage hy

noncomputable def symm (H : CompatiblePLHomeomorphTower T) :
    CompatiblePLHomeomorphTower T where
  stage i := (H.stage i).symm
  isPL_stage i := isPL_symm_of_homeomorph (H.isPL_stage i)
  image_coreSpace i := by
    apply Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      have hx' : x ∈ H.stage i '' T.coreSpace i := by
        rw [H.image_coreSpace i]
        exact hx
      obtain ⟨z, hz, hzx⟩ := hx'
      have hzy : z = (H.stage i).symm x := by
        apply (H.stage i).injective
        rw [hzx, (H.stage i).apply_symm_apply]
      exact hzy ▸ hz
    · intro y hy
      refine ⟨H.stage i y, ?_, (H.stage i).symm_apply_apply y⟩
      rw [← H.image_coreSpace i]
      exact ⟨y, hy, rfl⟩
  eqOn_coreSpace i := by
    intro y hy
    let x := (H.stage i).symm y
    have hx : x ∈ T.coreSpace i := by
      have hy' : y ∈ H.stage i '' T.coreSpace i := by
        rw [H.image_coreSpace i]
        exact hy
      obtain ⟨z, hz, hzy⟩ := hy'
      have hzx : z = x := by
        apply (H.stage i).injective
        rw [hzy, (H.stage i).apply_symm_apply]
      exact hzx ▸ hz
    have heq := H.eqOn_coreSpace i hx
    apply (H.stage (i + 1)).injective
    rw [(H.stage (i + 1)).apply_symm_apply]
    simpa only [x, (H.stage i).apply_symm_apply] using heq.symm

theorem symm_limitMap_leftInverse (H : CompatiblePLHomeomorphTower T) :
    Function.LeftInverse H.symm.limitMap H.limitMap := by
  intro x
  obtain ⟨i, hxi⟩ := T.exists_mem_core_space (Set.mem_univ x)
  rw [H.limitMap_eq_stage hxi]
  have himage : H.stage i x ∈ T.coreSpace i := by
    rw [← H.image_coreSpace i]
    exact ⟨x, hxi, rfl⟩
  rw [H.symm.limitMap_eq_stage himage]
  exact (H.stage i).symm_apply_apply x

theorem symm_limitMap_rightInverse (H : CompatiblePLHomeomorphTower T) :
    Function.RightInverse H.symm.limitMap H.limitMap := by
  intro y
  obtain ⟨i, hyi⟩ := T.exists_mem_core_space (Set.mem_univ y)
  rw [H.symm.limitMap_eq_stage hyi]
  have himage : (H.stage i).symm y ∈ T.coreSpace i := by
    rw [← H.symm.image_coreSpace i]
    exact ⟨y, hyi, rfl⟩
  change H.limitMap ((H.stage i).symm y) = y
  rw [H.limitMap_eq_stage himage]
  exact (H.stage i).apply_symm_apply y

noncomputable def limitHomeomorph (H : CompatiblePLHomeomorphTower T) : X ≃ₜ X :=
  Homeomorph.mk
    ⟨H.limitMap, H.symm.limitMap, H.symm_limitMap_leftInverse,
      H.symm_limitMap_rightInverse⟩
    (continuous_iff_continuousAt.mpr fun x => by
      simpa only [continuousWithinAt_univ] using (H.isPL_limitMap x).continuousWithinAt)
    (continuous_iff_continuousAt.mpr fun x => by
      simpa only [continuousWithinAt_univ] using (H.symm.isPL_limitMap x).continuousWithinAt)

theorem isPL_limitHomeomorph (H : CompatiblePLHomeomorphTower T) :
    IsPL n n H.limitHomeomorph := H.isPL_limitMap

theorem limitHomeomorph_eq_stage (H : CompatiblePLHomeomorphTower T) {i : ℕ} {x : X}
    (hx : x ∈ T.coreSpace i) : H.limitHomeomorph x = H.stage i x :=
  H.limitMap_eq_stage hx

theorem image_limitHomeomorph_coreSpace (H : CompatiblePLHomeomorphTower T) (i : ℕ) :
    H.limitHomeomorph '' T.coreSpace i = T.coreSpace i :=
  H.image_limitMap_coreSpace i

theorem eventually_eqOn_limitHomeomorph_of_isCompact (H : CompatiblePLHomeomorphTower T)
    {C : Set X} (hC : IsCompact C) :
    ∀ᶠ i in atTop, EqOn H.limitHomeomorph (H.stage i) C := by
  filter_upwards [T.core_space_eventually hC (subset_univ C)] with i hi
  exact fun x hx => H.limitHomeomorph_eq_stage (hi hx)

end CompatiblePLHomeomorphTower

namespace PLHomeomorphIncrementSystem

theorem limitHomeomorph_single_eq [Nonempty X] (P : PLPiece n X (Set.univ : Set X))
    (h : X ≃ₜ X) (hh : IsPL n n h) :
    ((single P h hh).toCompatibleTower.limitHomeomorph : X → X) = h := by
  funext x
  have hx : x ∈ (LocallyFinitePieceTower.prependEmpty
      (LocallyFinitePieceTower.ofPiece P)).coreSpace 1 := by
    rw [LocallyFinitePieceTower.prependEmpty_coreSpace_succ, LocallyFinitePieceTower.coreSpace]
    exact ⟨Function.invFunOn P.piece.map P.piece.complex.space x,
      P.piece.bijOn.surjOn.mapsTo_invFunOn (Set.mem_univ x),
      P.piece.bijOn.invOn_invFunOn.2 (Set.mem_univ x)⟩
  rw [(single P h hh).toCompatibleTower.limitHomeomorph_eq_stage hx]
  rfl

end PLHomeomorphIncrementSystem

end DifferentialGeometry.Topology.PiecewiseLinear
