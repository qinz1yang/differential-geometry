import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CoreDecompositionMobius

/-!
# Decomposition of the core with one-sided pieces: assembly

Lane MD3b, T5 (S-Asm). The planar decomposition of the core of Morse data on a base `B` whose slab
components may be one-sided saddle slabs (Möbius slabs, possible when `B` is not orientable).

* `exists_planarDecomposition_of_finite`: a decomposition whose cuts and pieces are indexed by
  arbitrary finite types gives a `PlanarDecomposition` (reindexing by `Fin`), with the same cuts
  and the same unhit sides.
* `qLvl`, `QIdx`, `qexists_above`, `qexists_below`, …: the level-circle bookkeeping of
  `exists_planarDecomposition_of_pieces`, for components described only by their `LevelCircles`.
* `CompPack`: the pieces of one slab component (elementary pieces embedded in the core, internal
  cuts, one external side per level circle collared by the given bicollar, two sides per internal
  cut). `nonempty_compPack_of_slab` is the planar piece of `exists_recollared_of_data`;
  `nonempty_compPack_of_split` is the Möbius piece, the pants piece and the internal cut of
  `exists_split_pieces`.
* `exists_planarDecomposition_of_packs`: the global assembly (level cuts at the lower circles of the
  components above level `1`, internal cuts inside the split components), with the base bicollar
  of every cut and the level-`0` half collars of the unhit sides.
* `exists_split_margin`, `exists_planarMobiusDecomposition_of_margin`: the hypothesis of
  `exists_split_pieces` holds once `κ` is below the distance from the levels to the middle band
  `{1/4 ≤ h ≤ 7/4}` of every Möbius slab.
* `exists_planarMobiusDecomposition_core_of_shrink`: the frozen S-Asm statement (shrink `κ`, then
  assemble).
-/

set_option autoImplicit false

noncomputable section
open Set Function TopologicalSpace Topology Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open DifferentialGeometry.Topology.Morse
open scoped Manifold ContDiff Topology

universe u v w

namespace GC.Seifert.CoreDecomposition

section Reindex

variable {S : CompactSurface.{u}} {PI : Type v} {CI : Type w} [Finite PI] [Finite CI]

theorem exists_planarDecomposition_of_finite
    (cut : CI → PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model S.kind) (Circle × ℝ)
      S.Carrier ∞)
    (cut_source : ∀ c, (cut c).source = {p | -1 < p.2 ∧ p.2 < 1})
    (cut_interior : ∀ c, (cut c).target ⊆ (SurfaceModel.model S.kind).interior S.Carrier)
    (cut_disjoint : Pairwise fun c d => Disjoint (cut c).target (cut d).target)
    (piece : PI → ElementaryBase.{u}) (inclusion : ∀ j, (piece j).surface.Carrier → S.Carrier)
    (isSmoothEmbedding : ∀ j, Manifold.IsSmoothEmbedding
      (SurfaceModel.model (piece j).surface.kind) (SurfaceModel.model S.kind) ∞ (inclusion j))
    (covers : ⋃ j, range (inclusion j) = univ)
    (cutSide : CI → Bool → Σ j, Fin (piece j).boundaryCount)
    (cutSide_injective : Function.Injective (Function.uncurry cutSide))
    (cutSide_collar : ∀ c b, ∃ σ : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle, ∀ t s (hs : 0 ≤ s), s < 1 →
      inclusion (cutSide c b).1 ((piece (cutSide c b).1).collar (cutSide c b).2
        (t, halfPoint s hs)) = cut c (σ t, if b then s else -s))
    (boundary_side : ∀ j l, (∀ c b, cutSide c b ≠ ⟨j, l⟩) → ∀ t,
      (SurfaceModel.model S.kind).IsBoundaryPoint (inclusion j ((piece j).collar l (t, halfZero))))
    (overlap : ∀ j j' x x', j ≠ j' → inclusion j x = inclusion j' x' →
      ∃ c t, inclusion j x = cut c (t, 0)) :
    ∃ P : PlanarDecomposition S, (∀ c, ∃ c', P.cut c = cut c') ∧
      ∀ j l, (∀ c b, P.cutSide c b ≠ ⟨j, l⟩) → ∃ j' l', (∀ c b, cutSide c b ≠ ⟨j', l'⟩) ∧
        ∀ p, P.inclusion j ((P.piece j).collar l p) = inclusion j' ((piece j').collar l' p) := by
  obtain ⟨nP, ⟨eP⟩⟩ := Finite.exists_equiv_fin PI
  obtain ⟨nC, ⟨eC⟩⟩ := Finite.exists_equiv_fin CI
  let sideE : (Σ j : PI, Fin (piece j).boundaryCount) ≃
      Σ j : Fin nP, Fin (piece (eP.symm j)).boundaryCount :=
    (Equiv.sigmaCongrLeft (β := fun j => Fin (piece j).boundaryCount) eP.symm).symm
  have hsymm : ∀ r : Σ j : Fin nP, Fin (piece (eP.symm j)).boundaryCount,
      sideE.symm r = ⟨eP.symm r.1, r.2⟩ := fun r => rfl
  have hspec : ∀ (s₀ : Σ j : PI, Fin (piece j).boundaryCount) (p : Circle × EuclideanHalfSpace 1),
      inclusion (eP.symm (sideE s₀).1) ((piece (eP.symm (sideE s₀).1)).collar (sideE s₀).2 p) =
        inclusion s₀.1 ((piece s₀.1).collar s₀.2 p) := by
    intro s₀ p
    have h := congrArg (fun X : Σ j : PI, Fin (piece j).boundaryCount =>
      inclusion X.1 ((piece X.1).collar X.2 p)) (sideE.symm_apply_apply s₀)
    rw [← h, hsymm]
  let P : PlanarDecomposition S :=
    { cutCount := nC
      cut := fun c => cut (eC.symm c)
      cut_source := fun c => cut_source _
      cut_interior := fun c => cut_interior _
      cut_disjoint := fun c d hcd => cut_disjoint (fun h => hcd (eC.symm.injective h))
      pieceCount := nP
      piece := fun j => piece (eP.symm j)
      inclusion := fun j => inclusion (eP.symm j)
      isSmoothEmbedding := fun j => isSmoothEmbedding _
      covers := by
        refine Set.eq_univ_of_forall fun y => ?_
        obtain ⟨j, x, hx⟩ := mem_iUnion.mp (covers ▸ mem_univ y)
        obtain ⟨j', rfl⟩ := eP.symm.surjective j
        exact mem_iUnion.mpr ⟨j', x, hx⟩
      cutSide := fun c b => sideE (cutSide (eC.symm c) b)
      cutSide_injective := by
        rintro ⟨c, b⟩ ⟨c', b'⟩ h
        have h' := cutSide_injective (a₁ := (eC.symm c, b)) (a₂ := (eC.symm c', b'))
          (sideE.injective h)
        simp only [Prod.mk.injEq] at h' ⊢
        exact ⟨eC.symm.injective h'.1, h'.2⟩
      cutSide_collar := by
        intro c b
        obtain ⟨σ, hσ⟩ := cutSide_collar (eC.symm c) b
        refine ⟨σ, fun t s hs hs1 => ?_⟩
        exact (hspec _ _).trans (hσ t s hs hs1)
      boundary_side := by
        intro j l hns t
        have hns' : ∀ c b, cutSide c b ≠ sideE.symm ⟨j, l⟩ := by
          intro c b h
          apply hns (eC c) b
          rw [eC.symm_apply_apply, h, Equiv.apply_symm_apply]
        exact boundary_side (eP.symm j) l hns' t
      overlap := by
        intro j j' x x' hjj h
        obtain ⟨c, t, hc⟩ := overlap (eP.symm j) (eP.symm j') x x'
          (fun h' => hjj (eP.symm.injective h')) h
        refine ⟨eC c, t, ?_⟩
        rw [eC.symm_apply_apply]
        exact hc }
  refine ⟨P, fun c => ⟨eC.symm c, rfl⟩, fun j l hns => ⟨eP.symm j, l, ?_, fun p => rfl⟩⟩
  intro c b h
  apply hns (eC c) b
  change sideE (cutSide (eC.symm (eC c)) b) = ⟨j, l⟩
  rw [eC.symm_apply_apply, h]
  exact sideE.apply_symm_apply ⟨j, l⟩

end Reindex

section LAssembly

variable {B : CompactSurface.{u}} (D : BaseMorseData B)
  (lcs : ∀ π : PIdx D, LevelCircles D π.1 (pRep D π).val)

def qLvl (π : PIdx D) (l : Fin (lcs π).k) : Fin (D.m + 1) :=
  if (lcs π).lev l then π.1.succ else π.1.castSucc

theorem qGam_level (π : PIdx D) (l : Fin (lcs π).k) (t : Circle) :
    D.f ((lcs π).gam l t) = D.level (qLvl D lcs π l) := by
  have h := (lcs π).level l t
  rw [qLvl]
  split_ifs at h ⊢ <;> exact h

theorem level_qLvl (π : PIdx D) (l : Fin (lcs π).k) :
    D.level (qLvl D lcs π l) =
      if (lcs π).lev l then D.level π.1.succ else D.level π.1.castSucc := by
  rw [qLvl]
  split_ifs <;> rfl

theorem range_qGam (π : PIdx D) (l : Fin (lcs π).k) :
    range ((lcs π).gam l) = connectedComponentIn (D.f ⁻¹' {D.level (qLvl D lcs π l)})
      ((lcs π).gam l 1) := by
  rw [level_qLvl]
  exact (lcs π).range_gam l

theorem qGam_mem_pK (π : PIdx D) (l : Fin (lcs π).k) (t : Circle) :
    (lcs π).gam l t ∈ pK D π := by
  have h := opensVal_image_pieceSlab D.smooth (level_castSucc_lt_succ D π.1)
    (slab_regular D π.1) (slab_interior D π.1) (pRep D π).val
  rw [pK, ← h]
  exact mem_image_of_mem _ ((lcs π).γ l t).2

theorem exists_qGam_of_mem (π : PIdx D) {y : B.Carrier} (hy : y ∈ pK D π)
    (hyl : D.f y = D.level π.1.castSucc ∨ D.f y = D.level π.1.succ) :
    ∃ l t, (lcs π).gam l t = y := by
  have h := opensVal_image_pieceSlab D.smooth (level_castSucc_lt_succ D π.1)
    (slab_regular D π.1) (slab_interior D π.1) (pRep D π).val
  rw [pK, ← h] at hy
  obtain ⟨w, hw, rfl⟩ := hy
  exact (lcs π).exists_gam_of_level ⟨w, hw⟩ hyl

theorem qLvl_eq_of_meet {π π' : PIdx D} {l : Fin (lcs π).k} {l' : Fin (lcs π').k}
    (h : (range ((lcs π).gam l) ∩ range ((lcs π').gam l')).Nonempty) :
    qLvl D lcs π l = qLvl D lcs π' l' := by
  obtain ⟨y, ⟨t, rfl⟩, ⟨t', ht'⟩⟩ := h
  have h1 := qGam_level D lcs π l t
  have h2 := qGam_level D lcs π' l' t'
  rw [ht'] at h2
  exact D.level_strictMono.injective (h1.symm.trans h2)

theorem qIdx_eq_of_meet {π π' : PIdx D} {l : Fin (lcs π).k} {l' : Fin (lcs π').k}
    (h : (range ((lcs π).gam l) ∩ range ((lcs π').gam l')).Nonempty) (hi : π.1 = π'.1) :
    π = π' := by
  obtain ⟨y, ⟨t, rfl⟩, ⟨t', ht'⟩⟩ := h
  exact pIdx_eq_of_pK_meet D ⟨_, qGam_mem_pK D lcs π l t, ht' ▸ qGam_mem_pK D lcs π' l' t'⟩ hi

theorem lev_eq_of_qLvl {π : PIdx D} {l : Fin (lcs π).k} :
    (lcs π).lev l = true ↔ qLvl D lcs π l = π.1.succ := by
  rw [qLvl]
  split_ifs with h
  · exact ⟨by intro h'; rfl, by intro h'; exact h⟩
  · refine ⟨fun h' => absurd h' h, fun h' => absurd h' ?_⟩
    exact (Fin.castSucc_lt_succ).ne

theorem qeq_of_meet_same_slab {π π' : PIdx D} {l : Fin (lcs π).k} {l' : Fin (lcs π').k}
    (h : (range ((lcs π).gam l) ∩ range ((lcs π').gam l')).Nonempty) (hi : π.1 = π'.1) :
    (⟨π, l⟩ : Σ π : PIdx D, Fin (lcs π).k) = ⟨π', l'⟩ := by
  have hπ := qIdx_eq_of_meet D lcs h hi
  subst hπ
  by_contra hne
  have hll : l ≠ l' := fun h' => hne (by rw [h'])
  obtain ⟨y, hy, hy'⟩ := h
  exact Set.disjoint_left.mp ((lcs π).disjoint_range_gam hll) hy hy'

def QIdx : Type u :=
  {q : Σ π : PIdx D, Fin (lcs π).k // (lcs q.1).lev q.2 = false ∧ q.1.1.val ≠ 0}

theorem qlev_false_of_level {π : PIdx D} {l : Fin (lcs π).k} {t : Circle}
    (h : D.f ((lcs π).gam l t) = D.level π.1.castSucc) : (lcs π).lev l = false := by
  by_contra hl
  rw [Bool.not_eq_false] at hl
  have h1 := qGam_level D lcs π l t
  rw [(lev_eq_of_qLvl D lcs).mp hl, h] at h1
  exact (level_castSucc_lt_succ D π.1).ne h1

theorem qlev_true_of_level {π : PIdx D} {l : Fin (lcs π).k} {t : Circle}
    (h : D.f ((lcs π).gam l t) = D.level π.1.succ) : (lcs π).lev l = true := by
  by_contra hl
  rw [Bool.not_eq_true] at hl
  have h1 := qGam_level D lcs π l t
  have hp : qLvl D lcs π l = π.1.castSucc := by rw [qLvl, hl]; rfl
  rw [hp, h] at h1
  exact (level_castSucc_lt_succ D π.1).ne h1.symm

theorem qexists_circle_at (i : Fin D.m) {y : B.Carrier}
    (hy : D.f y ∈ Icc (D.level i.castSucc) (D.level i.succ))
    (hyl : D.f y = D.level i.castSucc ∨ D.f y = D.level i.succ) :
    ∃ (π : PIdx D) (l : Fin (lcs π).k) (t : Circle), π.1 = i ∧ (lcs π).gam l t = y := by
  obtain ⟨c, hc⟩ := exists_pK_of_mem D i hy
  obtain ⟨l, t, hlt⟩ := exists_qGam_of_mem D lcs ⟨i, c⟩ hc hyl
  exact ⟨⟨i, c⟩, l, t, rfl, hlt⟩

theorem qexists_above (π : PIdx D) (l : Fin (lcs π).k) (hl : (lcs π).lev l = true) :
    ∃ q : QIdx D lcs, (range ((lcs q.1.1).gam q.1.2) ∩ range ((lcs π).gam l)).Nonempty := by
  set i := π.1
  set y := (lcs π).gam l 1
  have hy : D.f y = D.level i.succ := by
    rw [qGam_level, (lev_eq_of_qLvl D lcs).mp hl]
  have hlt : i.val + 1 < D.m := by
    have h1 := D.lt_level_last y
    rw [hy] at h1
    have h2 : i.succ < Fin.last D.m := D.level_strictMono.lt_iff_lt.mp h1
    rw [Fin.lt_def, Fin.val_succ, Fin.val_last] at h2
    exact h2
  set i' : Fin D.m := ⟨i.val + 1, hlt⟩
  have hi' : i'.castSucc = i.succ := Fin.ext (by simp [i'])
  have hyI : D.f y ∈ Icc (D.level i'.castSucc) (D.level i'.succ) := by
    rw [hi', hy]
    exact ⟨le_rfl, (level_castSucc_lt_succ D i').le.trans' (by rw [hi'])⟩
  obtain ⟨π'', l'', t, hπ'', hlt''⟩ := qexists_circle_at D lcs i' hyI
    (Or.inl (by rw [hi', hy]))
  have hlev : (lcs π'').lev l'' = false := by
    apply qlev_false_of_level D lcs (t := t)
    rw [hlt'', hπ'', hi', hy]
  have hne : π''.1.val ≠ 0 := by
    rw [hπ'']
    simp [i']
  exact ⟨⟨⟨π'', l''⟩, hlev, hne⟩, ⟨y, ⟨t, hlt''⟩, ⟨1, rfl⟩⟩⟩

theorem qexists_below (q : QIdx D lcs) :
    ∃ r : Σ π : PIdx D, Fin (lcs π).k, (lcs r.1).lev r.2 = true ∧
      (range ((lcs r.1).gam r.2) ∩ range ((lcs q.1.1).gam q.1.2)).Nonempty := by
  set i := q.1.1.1
  set y := (lcs q.1.1).gam q.1.2 1
  have hy : D.f y = D.level i.castSucc := by
    rw [qGam_level, qLvl, q.2.1]
    rfl
  have hi0 : i.val ≠ 0 := q.2.2
  set i₀ : Fin D.m := ⟨i.val - 1, by omega⟩
  have hi₀ : i₀.succ = i.castSucc := Fin.ext (by simp [i₀]; omega)
  have hyI : D.f y ∈ Icc (D.level i₀.castSucc) (D.level i₀.succ) := by
    rw [hi₀, hy]
    exact ⟨(level_castSucc_lt_succ D i₀).le.trans (by rw [hi₀]), le_rfl⟩
  obtain ⟨π', l', t, hπ', hlt'⟩ := qexists_circle_at D lcs i₀ hyI (Or.inr (by rw [hi₀, hy]))
  have hlev : (lcs π').lev l' = true := by
    apply qlev_true_of_level D lcs (t := t)
    rw [hlt', hπ', hi₀, hy]
  exact ⟨⟨π', l'⟩, hlev, ⟨y, ⟨t, hlt'⟩, ⟨1, rfl⟩⟩⟩

theorem qrange_eq_of_meet {π π' : PIdx D} {l : Fin (lcs π).k} {l' : Fin (lcs π').k}
    (h : (range ((lcs π).gam l) ∩ range ((lcs π').gam l')).Nonempty) :
    range ((lcs π).gam l) = range ((lcs π').gam l') := by
  have hL := qLvl_eq_of_meet D lcs h
  obtain ⟨y, hy, hy'⟩ := h
  rw [range_qGam] at hy ⊢
  rw [range_qGam] at hy' ⊢
  rw [hL] at hy ⊢
  rw [connectedComponentIn_eq hy, connectedComponentIn_eq hy']

theorem qbottom_level {π : PIdx D} {l : Fin (lcs π).k} (hl : (lcs π).lev l = false)
    (h0 : π.1.val = 0) (t : Circle) : D.f ((lcs π).gam l t) = D.level 0 := by
  rw [qGam_level, qLvl, hl]
  simp only [Bool.false_eq_true, ↓reduceIte]
  congr 1
  exact Fin.ext (by simp [h0])

end LAssembly

section Pack

variable {B : CompactSurface.{u}} (D : BaseMorseData B)

structure CompPack (i : Fin D.m) (x₀ : Ambient B) (lc : LevelCircles D i x₀)
    (U : Fin lc.k → PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model B.kind)
      (Circle × ℝ) B.Carrier ∞) (lam' : Fin lc.k → ℝ) where
  np : ℕ
  pc : Fin np → Σ E : ElementaryBase.{u}, (E.surface.Carrier → D.core.Carrier)
  emb : ∀ a, Manifold.IsSmoothEmbedding (SurfaceModel.model (pc a).1.surface.kind)
    (SurfaceModel.model D.core.kind) ∞ (pc a).2
  nic : ℕ
  cc : Fin nic → PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (𝓡∂ 2) (Circle × ℝ) D.core.Carrier ∞
  cc_source : ∀ c, (cc c).source = {p | -1 < p.2 ∧ p.2 < 1}
  cc_f : ∀ c, ∀ y ∈ (cc c).target, D.level i.castSucc + D.κ < D.f y.val ∧
    D.f y.val < D.level i.succ - D.κ
  cc_K : ∀ c, ∀ y ∈ (cc c).target, y.val ∈ connectedComponentIn
    (D.f ⁻¹' Icc (D.level i.castSucc) (D.level i.succ)) (ambientVal x₀)
  cc_disjoint : Pairwise fun c d => Disjoint (cc c).target (cc d).target
  ext : Fin lc.k → Σ a, Fin (pc a).1.boundaryCount
  ics : Fin nic → Bool → Σ a, Fin (pc a).1.boundaryCount
  ext_inj : Injective ext
  ics_inj : Injective (uncurry ics)
  ext_ne_ics : ∀ l c b, ext l ≠ ics c b
  sides : ∀ s, (∃ l, ext l = s) ∨ ∃ c b, ics c b = s
  ext_collar : ∀ l, ∃ σ : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle, ∀ t s (hs : 0 ≤ s), s < 1 →
    ((pc (ext l).1).2 ((pc (ext l).1).1.collar (ext l).2 (t, halfPoint s hs))).val =
      U l (σ t, lam' l * ((if lc.lev l then -1 else 1) * s))
  ics_collar : ∀ c b, ∃ σ : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle, ∀ t s (hs : 0 ≤ s), s < 1 →
    (pc (ics c b).1).2 ((pc (ics c b).1).1.collar (ics c b).2 (t, halfPoint s hs)) =
      cc c (σ t, if b then s else -s)
  mem_K : ∀ a x, ((pc a).2 x).val ∈ connectedComponentIn
    (D.f ⁻¹' Icc (D.level i.castSucc) (D.level i.succ)) (ambientVal x₀)
  cover : ∀ y ∈ connectedComponentIn (D.f ⁻¹' Icc (D.level i.castSucc) (D.level i.succ))
    (ambientVal x₀), ∃ a x, ((pc a).2 x).val = y
  lvl : ∀ a x, D.f ((pc a).2 x).val = D.level i.castSucc ∨
    D.f ((pc a).2 x).val = D.level i.succ → ∃ l t, ((pc a).2 x).val = U l (t, 0)
  overlap : ∀ a a' x x', a ≠ a' → (pc a).2 x = (pc a').2 x' → ∃ c t, (pc a).2 x = cc c (t, 0)

theorem nonempty_compPack_of_slab (i : Fin D.m) {x₀ : Ambient B}
    {hx₀ : x₀ ∈ slabSet (ambientFun D.f) (D.level i.castSucc) (D.level i.succ)}
    (sp' : SlabPiece D i hx₀) {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    (hlamb : D.level 0 + D.κ < D.level 1 - D.κ * lam)
    (hlamg : ∀ i : Fin D.m, 2 * (D.κ * lam) < D.level i.succ - D.level i.castSucc)
    (U : Fin sp'.levelCircles.k → PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ))
      (SurfaceModel.model B.kind) (Circle × ℝ) B.Carrier ∞)
    (I : Fin sp'.levelCircles.k → Fin (D.m + 1)) (lam' : Fin sp'.levelCircles.k → ℝ)
    (hlam' : ∀ l, lam' l = if sp'.levelCircles.lev l = false ∧ i.val = 0 then 1 else lam)
    (hUs : ∀ l, (U l).source = {p | -1 < p.2 ∧ p.2 < 1})
    (hUr : ∀ l, range (fun t => U l (t, 0)) = range (sp'.levelCircles.gam l))
    (hUf : ∀ l t s, -1 < s → s < 1 → D.f (U l (t, s)) = D.level (I l) + D.κ * s)
    (hUc : ∀ l t, IsMIntegralCurveOn (fun s => U l (t, s)) (fun x => D.κ • D.field x)
      (Ioo (-1) 1))
    (hI : ∀ l, D.level (I l) =
      if sp'.levelCircles.lev l then D.level i.succ else D.level i.castSucc) :
    Nonempty (CompPack D i x₀ sp'.levelCircles U lam') := by
  obtain ⟨Q, ι, hιe, hιc, hιK, hιs, hιb, -⟩ := exists_recollared_of_data D i sp' hlam0 hlam1
    hlamb hlamg U I lam' hlam' hUs hUr hUf hUc hI
  refine ⟨{ np := 1
            pc := fun _ => ⟨.planar sp'.k sp'.hk Q, ι⟩
            emb := fun _ => hιe
            nic := 0
            cc := fun c => c.elim0
            cc_source := fun c => c.elim0
            cc_f := fun c => c.elim0
            cc_K := fun c => c.elim0
            cc_disjoint := fun c => c.elim0
            ext := fun l => ⟨0, l⟩
            ics := fun c => c.elim0
            ext_inj := ?_
            ics_inj := fun c => c.1.elim0
            ext_ne_ics := fun _ c => c.elim0
            sides := ?_
            ext_collar := hιc
            ics_collar := fun c => c.elim0
            mem_K := fun _ => hιK
            cover := fun y hy => ⟨0, hιs y hy⟩
            lvl := ?_
            overlap := ?_ }⟩
  · intro l l' h
    exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
  · rintro ⟨a, l⟩
    obtain rfl : a = 0 := Subsingleton.elim _ _
    exact Or.inl ⟨l, rfl⟩
  · intro a x hx
    obtain ⟨l, t, rfl⟩ := hιb x hx
    obtain ⟨σ, hσ⟩ := hιc l
    refine ⟨l, σ t, ?_⟩
    have h := hσ t 0 le_rfl zero_lt_one
    rw [mul_zero, mul_zero] at h
    exact h
  · intro a a' _ _ h
    exact absurd (Subsingleton.elim a a') h

theorem nonempty_compPack_of_split (i : Fin D.m) {x₀ : Ambient B} (sd : SplitData D i x₀)
    (hη : ∀ y : compSet D i x₀, 1 / 4 ≤ mobiusHeight (sd.e y).val →
      mobiusHeight (sd.e y).val ≤ 7 / 4 →
        D.level i.castSucc + D.κ < pieceFun D.f (slabOpens D i x₀) y.val ∧
          pieceFun D.f (slabOpens D i x₀) y.val < D.level i.succ - D.κ)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    (hlamb : D.level 0 + D.κ < D.level 1 - D.κ * lam)
    (hlamg : ∀ i : Fin D.m, 2 * (D.κ * lam) < D.level i.succ - D.level i.castSucc)
    (U : Fin sd.levelCircles.k → PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ))
      (SurfaceModel.model B.kind) (Circle × ℝ) B.Carrier ∞)
    (I : Fin sd.levelCircles.k → Fin (D.m + 1)) (lam' : Fin sd.levelCircles.k → ℝ)
    (hlam' : ∀ l, lam' l = if sd.levelCircles.lev l = false ∧ i.val = 0 then 1 else lam)
    (hUs : ∀ l, (U l).source = {p | -1 < p.2 ∧ p.2 < 1})
    (hUr : ∀ l, range (fun t => U l (t, 0)) = range (sd.levelCircles.gam l))
    (hUf : ∀ l t s, -1 < s → s < 1 → D.f (U l (t, s)) = D.level (I l) + D.κ * s)
    (hI : ∀ l, D.level (I l) =
      if sd.levelCircles.lev l then D.level i.succ else D.level i.castSucc) :
    Nonempty (CompPack D i x₀ sd.levelCircles U lam') := by
  have hκ := D.κ_pos
  have hl0 (l : Fin 2) : 0 < lam' l := by rw [hlam' l]; split_ifs <;> linarith
  have hl1 (l : Fin 2) : lam' l ≤ 1 := by rw [hlam' l]; split_ifs <;> linarith
  have hbot (h : i.val = 0) : D.level i.castSucc = D.level 0 ∧ D.level i.succ = D.level 1 := by
    have hm : 1 < D.m + 1 := by have := i.2; omega
    constructor
    · congr 1
      exact Fin.ext (by simp [h])
    · congr 1
      exact Fin.ext (by simp [h, Nat.mod_eq_of_lt hm])
  have hgapl (l : Fin 2) : D.κ * lam' l < D.level i.succ - D.level i.castSucc := by
    rw [hlam' l]
    split_ifs with h
    · rw [(hbot h.2).1, (hbot h.2).2, mul_one]
      nlinarith [mul_pos hκ hlam0]
    · nlinarith [hlamg i]
  have hlev : ∀ l : Fin 2, sd.levelCircles.lev l = decide (l.val = 1) := fun l => rfl
  let c : Fin 2 → PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model B.kind)
      (Circle × ℝ) B.Carrier ∞ := fun l => shrinkBicollar (U l) (lam' l) (hUs l) (hl0 l) (hl1 l)
  have hcs : ∀ l, (c l).source = {p | -1 < p.2 ∧ p.2 < 1} := fun l => rfl
  have hcapp : ∀ l p, c l p = U l (p.1, lam' l * p.2) := fun l p => rfl
  have hcf : ∀ l t s, -1 < s → s < 1 → D.f (c l (t, s)) =
      (if l.val = 1 then D.level i.succ else D.level i.castSucc) + D.κ * lam' l * s := by
    intro l t s h1 h2
    rw [shrink_f D (U l) (hUs l) (hUf l) (hl0 l) (hl1 l) t s h1 h2, hI l, hlev l]
    by_cases hl : l.val = 1 <;> simp [hl]
  have hc0 : ∀ l t, c l (t, 0) = U l (t, 0) := fun l t => by
    rw [hcapp]
    simp only [mul_zero]
  have hzero : ∀ (l : Fin 2) t, ∃ t', sd.levelCircles.gam l t' = c l (t, 0) := by
    intro l t
    have h : U l (t, 0) ∈ range (sd.levelCircles.gam l) := hUr l ▸ mem_range_self t
    obtain ⟨t', ht'⟩ := h
    exact ⟨t', ht'.trans (hc0 l t).symm⟩
  have hcov : ∀ (l : Fin 2) t, ∃ t', c l (t', 0) = sd.levelCircles.gam l t := by
    intro l t
    have h : sd.levelCircles.gam l t ∈ range (fun t => U l (t, 0)) :=
      (hUr l).symm ▸ mem_range_self t
    obtain ⟨t', ht'⟩ := h
    exact ⟨t', (hc0 l t').trans ht'⟩
  obtain ⟨ιM, Q, ιQ, cc, jc, jl, hembM, hembQ, hccs, hccf, hccK, hMcol, ⟨σc, hσc⟩, hjlne,
    hjlinj, hjlex, hQcol, hMK, hQK, hcover, hMf, hQlev, hov⟩ :=
    exists_split_pieces D i sd c hcs (fun l => D.κ * lam' l) (fun l => mul_pos hκ (hl0 l))
      (fun l => by nlinarith [hl1 l]) hcf hgapl hzero hcov hη
  have h3 : (3 : ℕ) ∈ ({1, 2, 3} : Finset ℕ) := by decide
  have heps : ∀ l : Fin 2, lvlEps l = if sd.levelCircles.lev l then -1 else 1 := by
    intro l
    rw [hlev l]
    by_cases hl : l.val = 1 <;> simp [lvlEps, hl]
  let pc : Fin 2 → Σ E : ElementaryBase.{u}, (E.surface.Carrier → D.core.Carrier) :=
    ![⟨.mobius mobiusBase.{u}, ιM⟩, ⟨.planar 3 h3 Q, ιQ⟩]
  let ext : Fin 2 → Σ a, Fin (pc a).1.boundaryCount := fun l => ⟨1, jl l⟩
  let ics : Fin 1 → Bool → Σ a, Fin (pc a).1.boundaryCount := fun _ b =>
    cond b ⟨0, (0 : Fin 1)⟩ ⟨1, jc⟩
  refine ⟨{ np := 2
            pc := pc
            emb := ?_
            nic := 1
            cc := fun _ => cc
            cc_source := fun _ => hccs
            cc_f := fun _ => hccf
            cc_K := fun _ => hccK
            cc_disjoint := fun c d h => absurd (Subsingleton.elim c d) h
            ext := ext
            ics := ics
            ext_inj := ?_
            ics_inj := ?_
            ext_ne_ics := ?_
            sides := ?_
            ext_collar := ?_
            ics_collar := ?_
            mem_K := ?_
            cover := ?_
            lvl := ?_
            overlap := ?_ }⟩
  · intro a
    fin_cases a
    · exact hembM
    · exact hembQ
  · intro l l' h
    exact hjlinj (eq_of_heq (Sigma.mk.inj_iff.mp h).2)
  · rintro ⟨c₁, b⟩ ⟨c₂, b'⟩ h
    obtain rfl : c₁ = c₂ := Subsingleton.elim _ _
    cases b <;> cases b'
    · rfl
    · exact absurd (congrArg Sigma.fst h) (show ¬ ((1 : Fin 2) = 0) by decide)
    · exact absurd (congrArg Sigma.fst h) (show ¬ ((0 : Fin 2) = 1) by decide)
    · rfl
  · intro l c₁ b h
    cases b
    · exact hjlne l (eq_of_heq (Sigma.mk.inj_iff.mp h).2)
    · exact absurd (congrArg Sigma.fst h) (show ¬ ((1 : Fin 2) = 0) by decide)
  · rintro ⟨a, l⟩
    rcases a with ⟨_ | _ | _, ha⟩
    · right
      refine ⟨0, true, ?_⟩
      change Fin 1 at l
      obtain rfl : l = 0 := Subsingleton.elim _ _
      rfl
    · rcases hjlex l with h | ⟨l', hl'⟩
      · right
        refine ⟨0, false, ?_⟩
        subst h
        rfl
      · left
        refine ⟨l', ?_⟩
        subst hl'
        rfl
    · omega
  · intro l
    obtain ⟨σ, hσ⟩ := hQcol l
    refine ⟨σ, fun t s hs hs1 => ?_⟩
    refine (hσ t s hs hs1).trans ?_
    change U l (σ t, lam' l * (lvlEps l * s)) = _
    rw [heps l]
  · intro c₁ b
    cases b
    · exact ⟨σc, hσc⟩
    · refine ⟨Diffeomorph.refl (𝓡 1) Circle ∞, fun t s hs hs1 => ?_⟩
      exact hMcol t s hs hs1
  · intro a x
    fin_cases a
    · exact hMK x
    · exact hQK x
  · intro y hy
    rcases hcover y hy with ⟨x, hx⟩ | ⟨x, hx⟩
    · exact ⟨0, x, hx⟩
    · exact ⟨1, x, hx⟩
  · intro a x hx
    fin_cases a
    · have h := hMf x
      exfalso
      rcases hx with hx | hx
      · change D.f (ιM x).val = _ at hx
        linarith [h.1]
      · change D.f (ιM x).val = _ at hx
        linarith [h.2]
    · obtain ⟨l, t, rfl⟩ := hQlev x hx
      obtain ⟨σ, hσ⟩ := hQcol l
      refine ⟨l, σ t, ?_⟩
      have h := hσ t 0 le_rfl zero_lt_one
      rw [mul_zero, hc0] at h
      exact h
  · intro a a'
    fin_cases a <;> fin_cases a'
    · intro _ _ h
      exact absurd rfl h
    · intro x x' _ h
      obtain ⟨t, ht⟩ := hov x x' h
      exact ⟨0, t, ht⟩
    · intro x x' _ h
      obtain ⟨t, ht⟩ := hov x' x h.symm
      exact ⟨0, t, h.trans ht⟩
    · intro _ _ h
      exact absurd rfl h

end Pack

section Global

variable {B : CompactSurface.{u}} (D : BaseMorseData B)

theorem exists_planarDecomposition_of_packs (hgap : D.κ < D.level 1 - D.level 0)
    (lcs : ∀ π : PIdx D, LevelCircles D π.1 (pRep D π).val)
    (hpk : ∀ π : PIdx D, ∀ {lam : ℝ}, 0 < lam → lam ≤ 1 →
      D.level 0 + D.κ < D.level 1 - D.κ * lam →
      (∀ i : Fin D.m, 2 * (D.κ * lam) < D.level i.succ - D.level i.castSucc) →
      ∀ (U : Fin (lcs π).k → PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ))
        (SurfaceModel.model B.kind) (Circle × ℝ) B.Carrier ∞)
      (I : Fin (lcs π).k → Fin (D.m + 1)) (lam' : Fin (lcs π).k → ℝ),
      (∀ l, lam' l = if (lcs π).lev l = false ∧ π.1.val = 0 then 1 else lam) →
      (∀ l, (U l).source = {p | -1 < p.2 ∧ p.2 < 1}) →
      (∀ l, range (fun t => U l (t, 0)) = range ((lcs π).gam l)) →
      (∀ l t s, -1 < s → s < 1 → D.f (U l (t, s)) = D.level (I l) + D.κ * s) →
      (∀ l t, IsMIntegralCurveOn (fun s => U l (t, s)) (fun x => D.κ • D.field x)
        (Ioo (-1) 1)) →
      (∀ l, D.level (I l) =
        if (lcs π).lev l then D.level π.1.succ else D.level π.1.castSucc) →
      Nonempty (CompPack D π.1 (pRep D π).val (lcs π) U lam')) :
    ∃ P : PlanarDecomposition D.core,
      (∀ c, ∃ cB : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model B.kind)
          (Circle × ℝ) B.Carrier ∞,
        cB.source = {p | -1 < p.2 ∧ p.2 < 1} ∧
          ∀ t s, -1 < s → s < 1 → (P.cut c (t, s)).val = cB (t, s)) ∧
      ∀ j l, (∀ c b, P.cutSide c b ≠ ⟨j, l⟩) → ∃ (x₀ : B.Carrier) (hx₀ : D.f x₀ = D.level 0)
        (σ : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle), ∀ t s (hs : 0 ≤ s), s < 1 →
          (P.inclusion j ((P.piece j).collar l (t, halfPoint s hs))).val =
            Classical.choose (D.exists_levelBicollar 0 hx₀) (σ t, s) := by
  classical
  obtain ⟨lam, hlam0, hlam1, hlamb, hlamg⟩ := exists_shrink_factor D hgap
  have hκ := D.κ_pos
  have : ∀ i, Finite (ConnectedComponents (slabS D i)) := finite_slabComponents D
  choose bc hbcs hbcr hbcf hbcc using fun (π : PIdx D) (l : Fin (lcs π).k) =>
    D.exists_levelBicollar (qLvl D lcs π l) (qGam_level D lcs π l 1)
  choose above habove using qexists_above D lcs
  choose below hbelow1 hbelow2 using qexists_below D lcs
  have hbl : ∀ (π : PIdx D) (l : Fin (lcs π).k), (lcs π).lev l = false ∧ π.1.val = 0 →
      D.f ((lcs π).gam l 1) = D.level 0 := fun π l h => qbottom_level D lcs h.1 h.2 1
  let U : (π : PIdx D) → (l : Fin (lcs π).k) → PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ))
      (SurfaceModel.model B.kind) (Circle × ℝ) B.Carrier ∞ := fun π l =>
    if hl : (lcs π).lev l = true then bc (above π l hl).1.1 (above π l hl).1.2
    else if hb : (lcs π).lev l = false ∧ π.1.val = 0 then
      Classical.choose (D.exists_levelBicollar 0 (hbl π l hb))
    else bc π l
  let I : (π : PIdx D) → (l : Fin (lcs π).k) → Fin (D.m + 1) := fun π l =>
    if hl : (lcs π).lev l = true then qLvl D lcs (above π l hl).1.1 (above π l hl).1.2
    else if (lcs π).lev l = false ∧ π.1.val = 0 then 0
    else qLvl D lcs π l
  let lam' : (π : PIdx D) → (l : Fin (lcs π).k) → ℝ := fun π l =>
    if (lcs π).lev l = false ∧ π.1.val = 0 then 1 else lam
  have hdata : ∀ (π : PIdx D) (l : Fin (lcs π).k),
      (U π l).source = {p | -1 < p.2 ∧ p.2 < 1} ∧
      range (fun t => U π l (t, 0)) = range ((lcs π).gam l) ∧
      (∀ t s, -1 < s → s < 1 → D.f (U π l (t, s)) = D.level (I π l) + D.κ * s) ∧
      (∀ t, IsMIntegralCurveOn (fun s => U π l (t, s)) (fun x => D.κ • D.field x)
        (Ioo (-1) 1)) ∧
      D.level (I π l) = if (lcs π).lev l then D.level π.1.succ else D.level π.1.castSucc := by
    intro π l
    by_cases hl : (lcs π).lev l = true
    · have hU : U π l = bc (above π l hl).1.1 (above π l hl).1.2 := by
        simp only [U, hl, ↓reduceDIte]
      have hI : I π l = qLvl D lcs (above π l hl).1.1 (above π l hl).1.2 := by
        simp only [I, hl, ↓reduceDIte]
      rw [hU, hI]
      have hmeet := habove π l hl
      refine ⟨hbcs _ _, ?_, hbcf _ _, hbcc _ _, ?_⟩
      · rw [hbcr, ← range_qGam]
        exact qrange_eq_of_meet D lcs hmeet
      · rw [qLvl_eq_of_meet D lcs hmeet, (lev_eq_of_qLvl D lcs).mp hl]
        simp only [hl, ↓reduceIte]
    · have hl' : (lcs π).lev l = false := by simpa using hl
      by_cases hb : (lcs π).lev l = false ∧ π.1.val = 0
      · have hU : U π l = Classical.choose (D.exists_levelBicollar 0 (hbl π l hb)) := by
          simp [U, hl', hb]
        have hI : I π l = 0 := by simp [I, hl', hb]
        rw [hU, hI]
        obtain ⟨h1, h2, h3, h4⟩ := Classical.choose_spec (D.exists_levelBicollar 0 (hbl π l hb))
        refine ⟨h1, ?_, h3, h4, ?_⟩
        · rw [h2, range_qGam]
          have hL : D.level (qLvl D lcs π l) = D.level 0 := by
            rw [← qGam_level D lcs π l 1]; exact hbl π l hb
          rw [hL]
        · rw [hl']
          simp only [Bool.false_eq_true, ↓reduceIte]
          congr 1
          exact Fin.ext (by simp [hb.2])
      · have hb' : ¬ π.1.val = 0 := fun h => hb ⟨hl', h⟩
        have hU : U π l = bc π l := by simp [U, hl', hb']
        have hI : I π l = qLvl D lcs π l := by simp [I, hl', hb']
        rw [hU, hI]
        refine ⟨hbcs _ _, ?_, hbcf _ _, hbcc _ _, ?_⟩
        · rw [hbcr, ← range_qGam]
        · rw [qLvl, hl']
          simp
  obtain ⟨pk⟩ : Nonempty (∀ π : PIdx D, CompPack D π.1 (pRep D π).val (lcs π) (U π) (lam' π)) :=
    ⟨fun π => Classical.choice (hpk π hlam0 hlam1 hlamb hlamg (U π) (I π) (lam' π)
      (fun l => rfl) (fun l => (hdata π l).1) (fun l => (hdata π l).2.1)
      (fun l => (hdata π l).2.2.1) (fun l => (hdata π l).2.2.2.1)
      (fun l => (hdata π l).2.2.2.2))⟩
  have : Finite (QIdx D lcs) := by unfold QIdx; infer_instance
  have hcutlev : ∀ q : QIdx D lcs, 1 ≤ (qLvl D lcs q.1.1 q.1.2).val ∧
      qLvl D lcs q.1.1 q.1.2 = q.1.1.1.castSucc := by
    intro q
    have h : qLvl D lcs q.1.1 q.1.2 = q.1.1.1.castSucc := by
      rw [qLvl, q.2.1]; rfl
    refine ⟨?_, h⟩
    rw [h, Fin.val_castSucc]
    exact Nat.one_le_iff_ne_zero.mpr q.2.2
  have hlev1 : ∀ q : QIdx D lcs, D.level 1 ≤ D.level (qLvl D lcs q.1.1 q.1.2) := by
    intro q
    apply D.level_strictMono.monotone
    rw [Fin.le_def]
    have hm : 1 < D.m + 1 := by have := q.1.1.1.2; omega
    simp only [Fin.val_one', Nat.mod_eq_of_lt hm]
    exact (hcutlev q).1
  have hpos : ∀ q : QIdx D lcs, ∀ t s, -1 < s → s < 1 →
      D.level 0 < D.f (bc q.1.1 q.1.2 (t, lam * s)) := by
    intro q t s h1 h2
    have hb : |lam * s| < 1 := by
      rw [abs_mul, abs_of_pos hlam0]
      have : |s| < 1 := abs_lt.mpr ⟨h1, h2⟩
      nlinarith [abs_nonneg s]
    rw [hbcf _ _ t _ (abs_lt.mp hb).1 (abs_lt.mp hb).2]
    have := hlev1 q
    nlinarith [mul_pos hκ hlam0]
  have hcut_eq : ∀ q q' : QIdx D lcs,
      (range ((lcs q.1.1).gam q.1.2) ∩ range ((lcs q'.1.1).gam q'.1.2)).Nonempty → q = q' := by
    intro q q' h
    have hL := qLvl_eq_of_meet D lcs h
    rw [(hcutlev q).2, (hcutlev q').2] at hL
    have hi : q.1.1.1 = q'.1.1.1 := Fin.castSucc_injective _ hL
    exact Subtype.ext (qeq_of_meet_same_slab D lcs h hi)
  have hzero' : ∀ (π : PIdx D) (l : Fin (lcs π).k) (t : Circle),
      bc π l (t, 0) ∈ range ((lcs π).gam l) := by
    intro π l t
    rw [range_qGam, ← hbcr]
    exact mem_range_self t
  have hlevgap : ∀ a b : Fin (D.m + 1), a < b → 2 * (D.κ * lam) < D.level b - D.level a := by
    intro a b hab
    have ha : a.val < D.m := by have := b.2; omega
    have h1 := hlamg ⟨a.val, ha⟩
    have e1 : (⟨a.val, ha⟩ : Fin D.m).castSucc = a := Fin.ext rfl
    have e2 : (⟨a.val, ha⟩ : Fin D.m).succ ≤ b := by rw [Fin.le_def]; simp; omega
    rw [e1] at h1
    have := D.level_strictMono.monotone e2
    linarith
  have hshrink : ∀ (q : QIdx D lcs) (y : B.Carrier), y ∈ (bc q.1.1 q.1.2).target →
      |((bc q.1.1 q.1.2).symm y).2| < lam →
        |D.f y - D.level (qLvl D lcs q.1.1 q.1.2)| < D.κ * lam := by
    intro q y hy hs
    have hp := (bc q.1.1 q.1.2).map_target hy
    rw [hbcs] at hp
    have hr : bc q.1.1 q.1.2 ((bc q.1.1 q.1.2).symm y) = y := (bc q.1.1 q.1.2).right_inv hy
    have h := hbcf q.1.1 q.1.2 ((bc q.1.1 q.1.2).symm y).1 ((bc q.1.1 q.1.2).symm y).2 hp.1 hp.2
    rw [show (((bc q.1.1 q.1.2).symm y).1, ((bc q.1.1 q.1.2).symm y).2) =
      (bc q.1.1 q.1.2).symm y from rfl, hr] at h
    rw [h, add_sub_cancel_left, abs_mul, abs_of_pos hκ]
    exact mul_lt_mul_of_pos_left hs hκ
  have hUq : ∀ q : QIdx D lcs, U q.1.1 q.1.2 = bc q.1.1 q.1.2 ∧ lam' q.1.1 q.1.2 = lam := by
    intro q
    exact ⟨by simp [U, q.2.1, q.2.2], by simp [lam', q.2.2]⟩
  have hUb : ∀ q : QIdx D lcs, U (below q).1 (below q).2 = bc q.1.1 q.1.2 ∧
      lam' (below q).1 (below q).2 = lam := by
    intro q
    have hl : (lcs (below q).1).lev (below q).2 = true := hbelow1 q
    have hab : above (below q).1 (below q).2 hl = q := by
      apply hcut_eq
      rw [qrange_eq_of_meet D lcs (habove _ _ hl), qrange_eq_of_meet D lcs (hbelow2 q)]
      obtain ⟨t₀⟩ : Nonempty Circle := inferInstance
      exact ⟨_, mem_range_self t₀, mem_range_self t₀⟩
    refine ⟨?_, by simp [lam', hl]⟩
    simp only [U, hl, ↓reduceDIte]
    rw [hab]
  let GP := Σ π : PIdx D, Fin (pk π).np
  let piece : GP → ElementaryBase.{u} := fun J => ((pk J.1).pc J.2).1
  let incl : ∀ J : GP, (piece J).surface.Carrier → D.core.Carrier := fun J => ((pk J.1).pc J.2).2
  let ST := Σ J : GP, Fin (piece J).boundaryCount
  let portSide : (Σ π : PIdx D, Fin (lcs π).k) → ST := fun r =>
    ⟨⟨r.1, ((pk r.1).ext r.2).1⟩, ((pk r.1).ext r.2).2⟩
  let icSide : (Σ π : PIdx D, Fin (pk π).nic) → Bool → ST := fun c b =>
    ⟨⟨c.1, ((pk c.1).ics c.2 b).1⟩, ((pk c.1).ics c.2 b).2⟩
  let port : QIdx D lcs → Bool → Σ π : PIdx D, Fin (lcs π).k := fun q b => cond b q.1 (below q)
  let cut : QIdx D lcs ⊕ (Σ π : PIdx D, Fin (pk π).nic) →
      PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (𝓡∂ 2) (Circle × ℝ) D.core.Carrier ∞ :=
    Sum.elim (fun q => coreCut D (bc q.1.1 q.1.2) lam (hbcs _ _) hlam0 hlam1 (hpos q))
      (fun c => (pk c.1).cc c.2)
  let cutSide : QIdx D lcs ⊕ (Σ π : PIdx D, Fin (pk π).nic) → Bool → ST :=
    Sum.elim (fun q b => portSide (port q b)) icSide
  have hcutval : ∀ (q : QIdx D lcs) (t : Circle) (s : ℝ), -1 < s → s < 1 →
      (cut (Sum.inl q) (t, s)).val = bc q.1.1 q.1.2 (t, lam * s) := fun q t s h1 h2 =>
    coreCutFun_val D _ lam (hpos q t s h1 h2).le
  have hcs : ∀ c, (cut c).source = {p | -1 < p.2 ∧ p.2 < 1} := by
    rintro (q | c)
    · rfl
    · exact (pk c.1).cc_source c.2
  have hint : ∀ c, (cut c).target ⊆ (SurfaceModel.model D.core.kind).interior D.core.Carrier := by
    have key : ∀ y : D.core.Carrier, D.f y.val ≠ D.level 0 →
        y ∈ (SurfaceModel.model D.core.kind).interior D.core.Carrier := fun y hne =>
      ((SurfaceModel.model D.core.kind).isInteriorPoint_iff_not_isBoundaryPoint y).mpr
        fun hb => hne ((D.core_isBoundaryPoint_iff y).mp hb)
    have hk : D.κ * lam ≤ D.κ := mul_le_of_le_one_right hκ.le hlam1
    rintro (q | c) y hy
    · apply key
      have h := hshrink q y.val hy.1 hy.2
      have h1 := hlev1 q
      intro h0
      rw [h0, abs_lt] at h
      linarith [h.1, h.2]
    · apply key
      have h := (pk c.1).cc_f c.2 y hy
      have h0 : D.level 0 ≤ D.level c.1.1.castSucc := D.level_strictMono.monotone (Fin.zero_le _)
      intro h'
      linarith [h.1]
  have hdisj : Pairwise fun c d => Disjoint (cut c).target (cut d).target := by
    have hk : D.κ * lam ≤ D.κ := mul_le_of_le_one_right hκ.le hlam1
    have hLI : ∀ (q : QIdx D lcs) (c : Σ π : PIdx D, Fin (pk π).nic) (y : D.core.Carrier),
        y ∈ (cut (Sum.inl q)).target → y ∈ (cut (Sum.inr c)).target → False := by
      intro q c y hy hy'
      have h1 := hshrink q y.val hy.1 hy.2
      have h2 := (pk c.1).cc_f c.2 y hy'
      rw [abs_lt] at h1
      rcases le_or_gt (qLvl D lcs q.1.1 q.1.2) c.1.1.castSucc with h | h
      · have := D.level_strictMono.monotone h
        linarith [h1.2, h2.1]
      · have h' : c.1.1.succ ≤ qLvl D lcs q.1.1 q.1.2 := Fin.castSucc_lt_iff_succ_le.mp h
        have := D.level_strictMono.monotone h'
        linarith [h1.1, h2.2]
    rintro (q | c) (q' | c') hne <;> rw [Set.disjoint_left] <;> intro y hy hy'
    · by_cases hL : qLvl D lcs q.1.1 q.1.2 = qLvl D lcs q'.1.1 q'.1.2
      · have hp := (bc q.1.1 q.1.2).map_target hy.1
        have hp' := (bc q'.1.1 q'.1.2).map_target hy'.1
        rw [hbcs] at hp hp'
        have hr := (bc q.1.1 q.1.2).right_inv hy.1
        have hr' := (bc q'.1.1 q'.1.2).right_inv hy'.1
        have hf' : ∀ t s, -1 < s → s < 1 → D.f (bc q'.1.1 q'.1.2 (t, s)) =
            D.level (qLvl D lcs q.1.1 q.1.2) + D.κ * s := by
          rw [hL]; exact hbcf _ _
        obtain ⟨-, h0⟩ := eq_of_bicollar_eq D (hbcf _ _) hf' (hbcc _ _) (hbcc _ _) hp hp'
          (hr.trans hr'.symm)
        have hmeet : (range ((lcs q.1.1).gam q.1.2) ∩ range ((lcs q'.1.1).gam q'.1.2)).Nonempty :=
          ⟨_, hzero' _ _ _, by rw [h0]; exact hzero' _ _ _⟩
        exact hne (congrArg Sum.inl (hcut_eq q q' hmeet))
      · have h1 := hshrink q y.val hy.1 hy.2
        have h2 := hshrink q' y.val hy'.1 hy'.2
        rw [abs_lt] at h1 h2
        rcases lt_or_gt_of_ne hL with h | h
        · have := hlevgap _ _ h
          linarith
        · have := hlevgap _ _ h
          linarith
    · exact hLI q c' y hy hy'
    · exact hLI q' c y hy' hy
    · obtain ⟨π, c₁⟩ := c
      obtain ⟨π', c₁'⟩ := c'
      by_cases hπ : π = π'
      · subst hπ
        have hc : c₁ ≠ c₁' := fun h => hne (by rw [h])
        exact Set.disjoint_left.mp ((pk π).cc_disjoint hc) hy hy'
      · have hK := (pk π).cc_K c₁ y hy
        have hK' := (pk π').cc_K c₁' y hy'
        have hf := (pk π).cc_f c₁ y hy
        have hf' := (pk π').cc_f c₁' y hy'
        by_cases hii : π.1 = π'.1
        · exact hπ (pIdx_eq_of_pK_meet D ⟨_, hK, hK'⟩ hii)
        · rcases lt_or_gt_of_ne hii with hlt | hgt
          · have := D.level_strictMono.monotone (Fin.succ_le_castSucc_iff.mpr hlt)
            linarith [hf.2, hf'.1]
          · have := D.level_strictMono.monotone (Fin.succ_le_castSucc_iff.mpr hgt)
            linarith [hf.1, hf'.2]
  have hcov : ⋃ J, range (incl J) = univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    have hy0 : D.level 0 ≤ D.f y.val := y.2
    obtain ⟨i, hi⟩ := exists_slab_of_level_zero_le D hy0
    obtain ⟨c, hc⟩ := exists_pK_of_mem D i hi
    obtain ⟨a, x, hx⟩ := (pk ⟨i, c⟩).cover y.val hc
    exact mem_iUnion.mpr ⟨⟨⟨i, c⟩, a⟩, x, Subtype.ext hx⟩
  have hportSide_inj : ∀ r r', portSide r = portSide r' → r = r' := by
    rintro ⟨π, l⟩ ⟨π', l'⟩ h
    have hπ : π = π' := congrArg (fun S : ST => S.1.1) h
    subst hπ
    obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp h
    obtain ⟨-, h1'⟩ := Sigma.mk.inj_iff.mp h1
    exact Sigma.ext rfl (heq_of_eq ((pk π).ext_inj (Sigma.ext (eq_of_heq h1') h2)))
  have hicSide_inj : ∀ c b c' b', icSide c b = icSide c' b' → c = c' ∧ b = b' := by
    rintro ⟨π, c⟩ b ⟨π', c'⟩ b' h
    have hπ : π = π' := congrArg (fun S : ST => S.1.1) h
    subst hπ
    obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp h
    obtain ⟨-, h1'⟩ := Sigma.mk.inj_iff.mp h1
    have h3 := (pk π).ics_inj (a₁ := (c, b)) (a₂ := (c', b')) (Sigma.ext (eq_of_heq h1') h2)
    simp only [Prod.mk.injEq] at h3
    rw [h3.1]
    exact ⟨rfl, h3.2⟩
  have hport_ne_ic : ∀ r c b, portSide r ≠ icSide c b := by
    rintro ⟨π, l⟩ ⟨π', c⟩ b h
    have hπ : π = π' := congrArg (fun S : ST => S.1.1) h
    subst hπ
    obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp h
    obtain ⟨-, h1'⟩ := Sigma.mk.inj_iff.mp h1
    exact (pk π).ext_ne_ics l c b (Sigma.ext (eq_of_heq h1') h2)
  have hcsinj : Injective (uncurry cutSide) := by
    have hrb : ∀ q : QIdx D lcs, range ((lcs (below q).1).gam (below q).2) =
        range ((lcs q.1.1).gam q.1.2) := fun q => qrange_eq_of_meet D lcs (hbelow2 q)
    have hlevf : ∀ r r' : Σ π : PIdx D, Fin (lcs π).k, r = r' →
        (lcs r.1).lev r.2 = (lcs r'.1).lev r'.2 := by
      rintro r r' rfl; rfl
    rintro ⟨c, b⟩ ⟨c', b'⟩ h
    rcases c with q | c <;> rcases c' with q' | c'
    · have h' := hportSide_inj (port q b) (port q' b') h
      cases b <;> cases b'
      · have hq : q = q' := by
          apply hcut_eq
          rw [← hrb, ← hrb]
          rw [show below q = below q' from h']
          obtain ⟨t⟩ : Nonempty Circle := inferInstance
          exact ⟨_, mem_range_self t, mem_range_self t⟩
        rw [hq]
      · have := hlevf _ _ h'
        change (lcs (below q).1).lev (below q).2 = (lcs q'.1.1).lev q'.1.2 at this
        rw [hbelow1, q'.2.1] at this
        exact absurd this (by decide)
      · have := hlevf _ _ h'
        change (lcs q.1.1).lev q.1.2 = (lcs (below q').1).lev (below q').2 at this
        rw [hbelow1, q.2.1] at this
        exact absurd this (by decide)
      · have hq : q = q' := Subtype.ext h'
        rw [hq]
    · exact absurd h (hport_ne_ic _ _ _)
    · exact absurd h.symm (hport_ne_ic _ _ _)
    · obtain ⟨h1, h2⟩ := hicSide_inj c b c' b' h
      rw [h1, h2]
  have hcscol : ∀ c b, ∃ σ : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle, ∀ t s (hs : 0 ≤ s), s < 1 →
      incl (cutSide c b).1 ((piece (cutSide c b).1).collar (cutSide c b).2
        (t, halfPoint s hs)) = cut c (σ t, if b then s else -s) := by
    rintro (q | c) b
    · cases b
      · obtain ⟨σ, hσ⟩ := (pk (below q).1).ext_collar (below q).2
        refine ⟨σ, fun t s hs hs1 => Subtype.ext ?_⟩
        refine (hσ t s hs hs1).trans ?_
        rw [(hUb q).1, (hUb q).2, hbelow1 q]
        simp only [↓reduceIte, Bool.false_eq_true]
        rw [hcutval q (σ t) (-s) (by linarith) (by linarith)]
        ring_nf
      · obtain ⟨σ, hσ⟩ := (pk q.1.1).ext_collar q.1.2
        refine ⟨σ, fun t s hs hs1 => Subtype.ext ?_⟩
        refine (hσ t s hs hs1).trans ?_
        rw [(hUq q).1, (hUq q).2, q.2.1]
        simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
        rw [hcutval q (σ t) s (by linarith) hs1]
    · exact (pk c.1).ics_collar c.2 b
  have hbotOf : ∀ r : Σ π : PIdx D, Fin (lcs π).k, (∀ q b, port q b ≠ r) →
      (lcs r.1).lev r.2 = false ∧ r.1.1.val = 0 := by
    rintro ⟨π, l⟩ hns
    by_contra hnb
    by_cases hl : (lcs π).lev l = true
    · apply hns (above π l hl) false
      change below (above π l hl) = ⟨π, l⟩
      have hmeet : (range ((lcs (below (above π l hl)).1).gam (below (above π l hl)).2) ∩
          range ((lcs π).gam l)).Nonempty := by
        rw [qrange_eq_of_meet D lcs (hbelow2 _), qrange_eq_of_meet D lcs (habove π l hl)]
        obtain ⟨t₀⟩ : Nonempty Circle := inferInstance
        exact ⟨_, mem_range_self t₀, mem_range_self t₀⟩
      have hL := qLvl_eq_of_meet D lcs hmeet
      rw [(lev_eq_of_qLvl D lcs).mp (hbelow1 _), (lev_eq_of_qLvl D lcs).mp hl] at hL
      exact qeq_of_meet_same_slab D lcs hmeet (Fin.succ_injective _ hL)
    · have hl' : (lcs π).lev l = false := by simpa using hl
      have h0 : π.1.val ≠ 0 := fun h => hnb ⟨hl', h⟩
      exact hns ⟨⟨π, l⟩, hl', h0⟩ true rfl
  have hunhit : ∀ (J : GP) (l : Fin (piece J).boundaryCount), (∀ c b, cutSide c b ≠ ⟨J, l⟩) →
      ∃ l' : Fin (lcs J.1).k, portSide ⟨J.1, l'⟩ = ⟨J, l⟩ ∧ (lcs J.1).lev l' = false ∧
        J.1.1.val = 0 := by
    rintro ⟨π, a⟩ l hns
    rcases (pk π).sides ⟨a, l⟩ with ⟨l', hl'⟩ | ⟨c, b, hcb⟩
    · have hps : portSide ⟨π, l'⟩ = ⟨⟨π, a⟩, l⟩ := by
        change (⟨⟨π, ((pk π).ext l').1⟩, ((pk π).ext l').2⟩ : ST) = _
        rw [hl']
      refine ⟨l', hps, hbotOf ⟨π, l'⟩ fun q b h => hns (Sum.inl q) b ?_⟩
      change portSide (port q b) = _
      rw [h, hps]
    · exfalso
      apply hns (Sum.inr ⟨π, c⟩) b
      change (⟨⟨π, ((pk π).ics c b).1⟩, ((pk π).ics c b).2⟩ : ST) = _
      rw [hcb]
  have hbside : ∀ J l, (∀ c b, cutSide c b ≠ ⟨J, l⟩) → ∀ t,
      (SurfaceModel.model D.core.kind).IsBoundaryPoint
        (incl J ((piece J).collar l (t, halfZero))) := by
    intro J l hns t
    obtain ⟨l', hps, hlev, h0⟩ := hunhit J l hns
    have key : ∀ S : ST, S = portSide ⟨J.1, l'⟩ → (SurfaceModel.model D.core.kind).IsBoundaryPoint
        (incl S.1 ((piece S.1).collar S.2 (t, halfZero))) := by
      rintro S rfl
      refine (D.core_isBoundaryPoint_iff _).mpr ?_
      obtain ⟨σ, hσ⟩ := (pk J.1).ext_collar l'
      have h := hσ t 0 le_rfl zero_lt_one
      rw [mul_zero, mul_zero] at h
      refine (congrArg D.f h).trans ?_
      rw [(hdata J.1 l').2.2.1 _ _ (by norm_num) (by norm_num), mul_zero, add_zero,
        (hdata J.1 l').2.2.2.2, hlev]
      simp only [Bool.false_eq_true, ↓reduceIte]
      congr 1
      exact Fin.ext (by simp [h0])
    exact key ⟨J, l⟩ hps.symm
  have hlow : ∀ (J : GP) (x : (piece J).surface.Carrier),
      D.f (incl J x).val = D.level J.1.1.castSucc → J.1.1.val ≠ 0 →
        ∃ c t, incl J x = cut c (t, 0) := by
    rintro ⟨π, a⟩ x hfa h0
    obtain ⟨l, t, hlt⟩ := (pk π).lvl a x (Or.inl hfa)
    have hfU := (hdata π l).2.2.1 t 0 (by norm_num) (by norm_num)
    rw [mul_zero, add_zero, ← hlt, (hdata π l).2.2.2.2] at hfU
    have hlev : (lcs π).lev l = false := by
      by_contra h
      rw [Bool.not_eq_false] at h
      rw [h] at hfU
      simp only [↓reduceIte] at hfU
      exact (level_castSucc_lt_succ D π.1).ne (hfa.symm.trans hfU)
    let q : QIdx D lcs := ⟨⟨π, l⟩, hlev, h0⟩
    refine ⟨Sum.inl q, t, Subtype.ext ?_⟩
    rw [hcutval q t 0 (by norm_num) (by norm_num), mul_zero, ← (hUq q).1]
    exact hlt
  have hov : ∀ J J' x x', J ≠ J' → incl J x = incl J' x' → ∃ c t, incl J x = cut c (t, 0) := by
    rintro ⟨π, a⟩ ⟨π', a'⟩ x x' hJJ h
    by_cases hπ : π = π'
    · subst hπ
      have ha : a ≠ a' := fun h' => hJJ (by rw [h'])
      obtain ⟨c, t, hc⟩ := (pk π).overlap a a' x x' ha h
      exact ⟨Sum.inr ⟨π, c⟩, t, hc⟩
    · have hy' : (incl ⟨π, a⟩ x).val = (incl ⟨π', a'⟩ x').val := congrArg Subtype.val h
      have hyK : (incl ⟨π, a⟩ x).val ∈ pK D π := (pk π).mem_K a x
      have hyK' : (incl ⟨π, a⟩ x).val ∈ pK D π' := by rw [hy']; exact (pk π').mem_K a' x'
      have hfy : D.f (incl ⟨π, a⟩ x).val ∈ Icc (D.level π.1.castSucc) (D.level π.1.succ) :=
        connectedComponentIn_subset (D.f ⁻¹' Icc (D.level π.1.castSucc) (D.level π.1.succ)) _ hyK
      have hfy' : D.f (incl ⟨π, a⟩ x).val ∈ Icc (D.level π'.1.castSucc) (D.level π'.1.succ) :=
        connectedComponentIn_subset (D.f ⁻¹' Icc (D.level π'.1.castSucc)
          (D.level π'.1.succ)) _ hyK'
      by_cases hii : π.1 = π'.1
      · exact absurd (pIdx_eq_of_pK_meet D ⟨_, hyK, hyK'⟩ hii) hπ
      · rcases lt_or_gt_of_ne hii with hlt | hgt
        · have hle : D.level π.1.succ ≤ D.level π'.1.castSucc :=
            D.level_strictMono.monotone (Fin.succ_le_castSucc_iff.mpr hlt)
          have hfa : D.f (incl ⟨π', a'⟩ x').val = D.level π'.1.castSucc := by
            rw [← hy']; linarith [hfy.2, hfy'.1]
          have h0 : π'.1.val ≠ 0 := by
            have := Fin.lt_def.mp hlt; omega
          obtain ⟨c, t, hc⟩ := hlow ⟨π', a'⟩ x' hfa h0
          exact ⟨c, t, h.trans hc⟩
        · have hle : D.level π'.1.succ ≤ D.level π.1.castSucc :=
            D.level_strictMono.monotone (Fin.succ_le_castSucc_iff.mpr hgt)
          have hfa : D.f (incl ⟨π, a⟩ x).val = D.level π.1.castSucc := by
            linarith [hfy.1, hfy'.2]
          have h0 : π.1.val ≠ 0 := by
            have := Fin.lt_def.mp hgt; omega
          exact hlow ⟨π, a⟩ x hfa h0
  obtain ⟨P, hPcut, hPside⟩ := exists_planarDecomposition_of_finite (S := D.core) cut hcs hint
    hdisj piece incl (fun J => (pk J.1).emb J.2) hcov cutSide hcsinj hcscol hbside hov
  refine ⟨P, fun c => ?_, fun j l hns => ?_⟩
  · obtain ⟨c', hc'⟩ := hPcut c
    rw [hc']
    rcases c' with q | c'
    · exact ⟨shrinkBicollar (bc q.1.1 q.1.2) lam (hbcs _ _) hlam0 hlam1, rfl,
        fun t s h1 h2 => hcutval q t s h1 h2⟩
    · refine ⟨coreToBPD D ((pk c'.1).cc c'.2) (fun y hy => ?_) ((pk c'.1).cc c'.2 (1, 0)),
        (pk c'.1).cc_source c'.2, fun t s _ _ => rfl⟩
      have h := (pk c'.1).cc_f c'.2 y hy
      have h0 : D.level 0 ≤ D.level c'.1.1.castSucc :=
        D.level_strictMono.monotone (Fin.zero_le _)
      linarith [h.1]
  · obtain ⟨J, l', hns', heq⟩ := hPside j l hns
    obtain ⟨l'', hps, hlev, h0⟩ := hunhit J l' hns'
    refine ⟨(lcs J.1).gam l'' 1, hbl J.1 l'' ⟨hlev, h0⟩, ?_⟩
    obtain ⟨σ, hσ⟩ := (pk J.1).ext_collar l''
    refine ⟨σ, fun t s hs hs1 => ?_⟩
    rw [heq]
    have hU : U J.1 l'' = Classical.choose (D.exists_levelBicollar 0 (hbl J.1 l'' ⟨hlev, h0⟩)) := by
      simp [U, hlev, h0]
    have hlam : lam' J.1 l'' = 1 := by simp [lam', hlev, h0]
    have key : ∀ S : ST, S = portSide ⟨J.1, l''⟩ →
        (incl S.1 ((piece S.1).collar S.2 (t, halfPoint s hs))).val =
          Classical.choose (D.exists_levelBicollar 0 (hbl J.1 l'' ⟨hlev, h0⟩)) (σ t, s) := by
      rintro S rfl
      refine (hσ t s hs hs1).trans ?_
      rw [hU, hlam]
      simp only [hlev, Bool.false_eq_true, ↓reduceIte, one_mul]
    exact key ⟨J, l'⟩ hps.symm

end Global

section Final

variable {B : CompactSurface.{u}} (D : BaseMorseData B)

theorem exists_split_margin (i : Fin D.m) {x₀ : Ambient B} (sd : SplitData D i x₀) :
    ∃ η : ℝ, 0 < η ∧ ∀ y : compSet D i x₀, 1 / 4 ≤ mobiusHeight (sd.e y).val →
      mobiusHeight (sd.e y).val ≤ 7 / 4 →
        D.level i.castSucc + η ≤ pieceFun D.f (slabOpens D i x₀) y.val ∧
          pieceFun D.f (slabOpens D i x₀) y.val ≤ D.level i.succ - η := by
  let := (shiftAtlas (pieceAtlas D.smooth (level_castSucc_lt_succ D i) (slab_regular D i)
    x₀)).toChartedSpace
  let := GC.Seifert.mobiusSlabAtlas.toChartedSpace
  have hab := level_castSucc_lt_succ D i
  have : CompactSpace (compSet D i x₀) :=
    compactSpace_pieceSlab D.smooth hab (slab_regular D i) (slab_interior D i) x₀
  let h : compSet D i x₀ → ℝ := fun y => mobiusHeight (sd.e y).val
  have hh : Continuous h :=
    contMDiff_mobiusHeight.continuous.comp (continuous_subtype_val.comp sd.e.continuous)
  let F : compSet D i x₀ → ℝ := fun y => pieceFun D.f (slabOpens D i x₀) y.val
  have hF : Continuous F := (contMDiff_pieceFun D.smooth _).continuous.comp continuous_subtype_val
  let C : Set (compSet D i x₀) := {y | 1 / 4 ≤ h y ∧ h y ≤ 7 / 4}
  have hC : IsCompact C :=
    ((isClosed_le continuous_const hh).inter (isClosed_le hh continuous_const)).isCompact
  let g : compSet D i x₀ → ℝ := fun y => min (F y - D.level i.castSucc) (D.level i.succ - F y)
  have hg : Continuous g := (hF.sub continuous_const).min (continuous_const.sub hF)
  rcases C.eq_empty_or_nonempty with hCe | hCne
  · refine ⟨1, one_pos, fun y h1 h2 => absurd (show y ∈ C from ⟨h1, h2⟩) ?_⟩
    rw [hCe]
    exact notMem_empty y
  · obtain ⟨y₀, hy₀C, hy₀⟩ := hC.exists_isMinOn hCne hg.continuousOn
    have hpos : 0 < g y₀ := by
      have hS := (mem_slabSet_iff hab.le y₀.val).mp y₀.2
      have h1 : 1 / 4 ≤ mobiusHeight (sd.e y₀).val := hy₀C.1
      have h2 : mobiusHeight (sd.e y₀).val ≤ 7 / 4 := hy₀C.2
      have hne1 : F y₀ ≠ D.level i.castSucc := fun he => by
        have := (sd.he y₀).1.mp he
        linarith
      have hne2 : F y₀ ≠ D.level i.succ := fun he => by
        have := (sd.he y₀).2.mp he
        linarith
      exact lt_min (sub_pos.mpr (lt_of_le_of_ne hS.1 (Ne.symm hne1)))
        (sub_pos.mpr (lt_of_le_of_ne hS.2 hne2))
    refine ⟨g y₀, hpos, fun y h1 h2 => ?_⟩
    have hle : g y₀ ≤ g y := hy₀ (show y ∈ C from ⟨h1, h2⟩)
    have hm1 : g y ≤ F y - D.level i.castSucc := min_le_left _ _
    have hm2 : g y ≤ D.level i.succ - F y := min_le_right _ _
    exact ⟨by linarith, by linarith⟩

theorem exists_planarMobiusDecomposition_of_margin (hgap : D.κ < D.level 1 - D.level 0)
    (hsk : ∀ π : PIdx D, Nonempty (SlabPiece D π.1 (pRep D π).2) ∨
      ∃ sd : SplitData D π.1 (pRep D π).val, ∀ y : compSet D π.1 (pRep D π).val,
        1 / 4 ≤ mobiusHeight (sd.e y).val → mobiusHeight (sd.e y).val ≤ 7 / 4 →
          D.level π.1.castSucc + D.κ < pieceFun D.f (slabOpens D π.1 (pRep D π).val) y.val ∧
            pieceFun D.f (slabOpens D π.1 (pRep D π).val) y.val < D.level π.1.succ - D.κ) :
    ∃ P : PlanarDecomposition D.core,
      (∀ c, ∃ cB : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model B.kind)
          (Circle × ℝ) B.Carrier ∞,
        cB.source = {p | -1 < p.2 ∧ p.2 < 1} ∧
          ∀ t s, -1 < s → s < 1 → (P.cut c (t, s)).val = cB (t, s)) ∧
      ∀ j l, (∀ c b, P.cutSide c b ≠ ⟨j, l⟩) → ∃ (x₀ : B.Carrier) (hx₀ : D.f x₀ = D.level 0)
        (σ : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle), ∀ t s (hs : 0 ≤ s), s < 1 →
          (P.inclusion j ((P.piece j).collar l (t, halfPoint s hs))).val =
            Classical.choose (D.exists_levelBicollar 0 hx₀) (σ t, s) := by
  have hlc : ∀ π : PIdx D, ∃ lc : LevelCircles D π.1 (pRep D π).val, ∀ {lam : ℝ}, 0 < lam →
      lam ≤ 1 → D.level 0 + D.κ < D.level 1 - D.κ * lam →
      (∀ i : Fin D.m, 2 * (D.κ * lam) < D.level i.succ - D.level i.castSucc) →
      ∀ (U : Fin lc.k → PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ))
        (SurfaceModel.model B.kind) (Circle × ℝ) B.Carrier ∞)
      (I : Fin lc.k → Fin (D.m + 1)) (lam' : Fin lc.k → ℝ),
      (∀ l, lam' l = if lc.lev l = false ∧ π.1.val = 0 then 1 else lam) →
      (∀ l, (U l).source = {p | -1 < p.2 ∧ p.2 < 1}) →
      (∀ l, range (fun t => U l (t, 0)) = range (lc.gam l)) →
      (∀ l t s, -1 < s → s < 1 → D.f (U l (t, s)) = D.level (I l) + D.κ * s) →
      (∀ l t, IsMIntegralCurveOn (fun s => U l (t, s)) (fun x => D.κ • D.field x)
        (Ioo (-1) 1)) →
      (∀ l, D.level (I l) = if lc.lev l then D.level π.1.succ else D.level π.1.castSucc) →
      Nonempty (CompPack D π.1 (pRep D π).val lc U lam') := by
    intro π
    rcases hsk π with hsp | ⟨sd, hη⟩
    · obtain ⟨sp⟩ := hsp
      exact ⟨sp.levelCircles, fun hlam0 hlam1 hlamb hlamg U I lam' hlam' hUs hUr hUf hUc hI =>
        nonempty_compPack_of_slab D π.1 sp hlam0 hlam1 hlamb hlamg U I lam' hlam' hUs hUr hUf hUc
          hI⟩
    · exact ⟨sd.levelCircles, fun hlam0 hlam1 hlamb hlamg U I lam' hlam' hUs hUr hUf _ hI =>
        nonempty_compPack_of_split D π.1 sd hη hlam0 hlam1 hlamb hlamg U I lam' hlam' hUs hUr hUf
          hI⟩
  choose lcs hpk using hlc
  exact exists_planarDecomposition_of_packs D hgap lcs hpk

theorem exists_planarMobiusDecomposition_core_of_shrink (D : BaseMorseData B) :
    ∃ D' : BaseMorseData B, D'.f = D.f ∧ D'.crit = D.crit ∧ D'.m = D.m ∧ D'.κ ≤ D.κ ∧
      (∀ i : Fin (D'.m + 1), ∃ j : Fin (D.m + 1), D'.level i = D.level j) ∧
      ∃ P : PlanarDecomposition D'.core,
      (∀ c, ∃ cB : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model B.kind)
          (Circle × ℝ) B.Carrier ∞,
        cB.source = {p | -1 < p.2 ∧ p.2 < 1} ∧
          ∀ t s, -1 < s → s < 1 → (P.cut c (t, s)).val = cB (t, s)) ∧
      ∀ j l, (∀ c b, P.cutSide c b ≠ ⟨j, l⟩) → ∃ (x₀ : B.Carrier) (hx₀ : D'.f x₀ = D'.level 0)
        (σ : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle), ∀ t s (hs : 0 ≤ s), s < 1 →
          (P.inclusion j ((P.piece j).collar l (t, halfPoint s hs))).val =
            Classical.choose (D'.exists_levelBicollar 0 hx₀) (σ t, s) := by
  have hm : 0 < D.m := by
    obtain ⟨x, hx⟩ := D.exists_level_zero_lt
    by_contra h
    have h0 : D.m = 0 := by omega
    have hlt := D.lt_level_last x
    have hl : Fin.last D.m = 0 := Fin.ext (by simp [h0])
    rw [hl] at hlt
    linarith
  have hgap0 : 0 < D.level 1 - D.level 0 := by
    have : (0 : Fin (D.m + 1)) < 1 := by
      rw [Fin.lt_def]
      simp [Nat.mod_eq_of_lt (show 1 < D.m + 1 by omega)]
    linarith [D.level_strictMono this]
  have hmar : ∀ π : PIdx D, ∃ η : ℝ, 0 < η ∧ (Nonempty (SlabPiece D π.1 (pRep D π).2) ∨
      ∃ sd : SplitData D π.1 (pRep D π).val, ∀ y : compSet D π.1 (pRep D π).val,
        1 / 4 ≤ mobiusHeight (sd.e y).val → mobiusHeight (sd.e y).val ≤ 7 / 4 →
          D.level π.1.castSucc + η ≤ pieceFun D.f (slabOpens D π.1 (pRep D π).val) y.val ∧
            pieceFun D.f (slabOpens D π.1 (pRep D π).val) y.val ≤ D.level π.1.succ - η) := by
    intro π
    rcases nonempty_slabPiece_or_split D π.1 (pRep D π).val (pRep D π).2 with h | hsd
    · exact ⟨1, one_pos, Or.inl h⟩
    · obtain ⟨sd⟩ := hsd
      obtain ⟨η, hη, h⟩ := exists_split_margin D π.1 sd
      exact ⟨η, hη, Or.inr ⟨sd, h⟩⟩
  choose η hη hsk using hmar
  have : ∀ i, Finite (ConnectedComponents (slabS D i)) := finite_slabComponents D
  obtain ⟨η₀, hη₀, hη₀le⟩ : ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ π, η₀ ≤ η π := by
    by_cases hne : Nonempty (PIdx D)
    · obtain ⟨π₀, hπ₀⟩ := Finite.exists_min η
      exact ⟨η π₀, hη π₀, hπ₀⟩
    · exact ⟨1, one_pos, fun π => absurd ⟨π⟩ hne⟩
  set κ' := min D.κ (min ((D.level 1 - D.level 0) / 2) (η₀ / 2)) with hκ'def
  have hκ' : 0 < κ' := lt_min D.κ_pos (lt_min (by linarith) (by linarith))
  have hκ'κ : κ' ≤ D.κ := min_le_left _ _
  have hκ'g : κ' ≤ (D.level 1 - D.level 0) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hκ'η : κ' ≤ η₀ / 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨withKappa D κ' hκ' hκ'κ, rfl, rfl, rfl, hκ'κ, fun i => ⟨i, rfl⟩, ?_⟩
  refine exists_planarMobiusDecomposition_of_margin (withKappa D κ' hκ' hκ'κ) ?_ ?_
  · change κ' < D.level 1 - D.level 0
    linarith
  · intro π
    rcases hsk π with hsp | ⟨sd, hsd⟩
    · obtain ⟨sp⟩ := hsp
      exact Or.inl ⟨⟨sp.k, sp.hk, sp.P, sp.hP, sp.e, sp.lev, sp.hlev⟩⟩
    · refine Or.inr ⟨⟨sd.e, sd.he⟩, fun y h1 h2 => ?_⟩
      have h : D.level π.1.castSucc + η π ≤ pieceFun D.f (slabOpens D π.1 (pRep D π).val) y.val ∧
          pieceFun D.f (slabOpens D π.1 (pRep D π).val) y.val ≤ D.level π.1.succ - η π :=
        hsd y h1 h2
      have h' := hη₀le π
      change D.level π.1.castSucc + κ' < pieceFun D.f (slabOpens D π.1 (pRep D π).val) y.val ∧
        pieceFun D.f (slabOpens D π.1 (pRep D π).val) y.val < D.level π.1.succ - κ'
      exact ⟨by linarith [h.1], by linarith [h.2]⟩

end Final

end GC.Seifert.CoreDecomposition
