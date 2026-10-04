import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ElementarizeWiringPieces
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ElementarizeWiringSystem
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ElementarizeWiring

/-!
# The piece system of one old piece with an orientable base

Lane P1W (P1 wiring), tier T2.

Let `T` be a torus presentation, `i` a component carrying a circle fibration `F` whose base has
Morse data `D` with a planar core `P` (for an orientable base, `exists_planarCore_of_orientable`).
The pieces of the component are

* the synchronised planar pieces `Φ_j` over the pieces of `P` (`exists_planarPieceMap`), with
  base `(P.base j).shrink δ`;
* one collar piece for every owned side `s`: MD5's `exists_oldPortCollarPiece` gives
  `K_s : T² × [0, ℓ] → U` onto the component of `{u ≤ ℓ}` through the side torus, equal to the old
  collar for small `s` and following the lifted flow of the level bicollar near `T² × ℓ`; the
  level bicollar is the one of the bottom side `β s` over the level circle of a point of height `ℓ`
  of that component. The collar piece is `collarPieceMap ℓ K_s` with base
  `(planarBase 2).shrink (10 δ / ℓ)`, so that both its ports read `K_s` at depth `δ s`.

The seams are the cuts of `P` and, for every owned side, the torus `K_s (T² × ℓ)` where the collar
piece meets the planar piece of `β s`; all of them are synchronised at rate `δ`. The external
sides are the ports `0` of the collar pieces, and they agree with the old side collars of
`(T.reparam id).shrink δ` on the whole collar. Topology (`ElementarizeWiringTopology`): every
point of height `≤ ℓ` lies in the component of a side torus, distinct sides have distinct
components, and the points of height `ℓ` of a component are its top torus, which is the preimage
of one level circle; so `β` is a bijection from the owned sides onto the bottom sides.
`exists_componentRefinement` assembles the `SyncedData` and returns, for every small `δ`, a
`ComponentRefinement` of `(T.reparam id).shrink δ` at `i`.
-/

set_option autoImplicit false

noncomputable section
open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.Wiring

theorem exists_pos_le_of_finite {ι : Type*} [Finite ι] (f : ι → ℝ) (hf : ∀ x, 0 < f x) :
    ∃ m > 0, ∀ x, m ≤ f x := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun x => isEmptyElim x⟩
  · obtain ⟨x₀, hx₀⟩ := Finite.exists_min f
    exact ⟨f x₀, hf x₀, hx₀⟩

section LocalDiffeo

variable {E E' E'' H H' H'' X M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup E''] [NormedSpace ℝ E'']
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'} {K : ModelWithCorners ℝ E'' H''}
  [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace M] [ChartedSpace H' M]
  [TopologicalSpace N] [ChartedSpace H'' N]

theorem isLocalDiffeomorphAt_of_comp_eq (map : M → N) (A : PartialDiffeomorph I J X M ∞)
    (c : PartialDiffeomorph I K X N ∞) {p : X} (hpA : p ∈ A.source) (hpc : p ∈ c.source)
    (heq : ∀ q ∈ A.source ∩ c.source, map (A q) = c q) :
    IsLocalDiffeomorphAt J K ∞ map (A p) := by
  have e : (A.symm.toPartialEquiv : M → X) (A.toPartialEquiv p) = p := A.left_inv hpA
  have h1 : IsLocalDiffeomorphAt J I ∞ A.symm (A p) :=
    A.symm.isLocalDiffeomorphAt _ _ _ (A.map_source hpA)
  have h2 : IsLocalDiffeomorphAt I K ∞ c (A.symm (A p)) := by
    rw [e]
    exact c.isLocalDiffeomorphAt _ _ _ hpc
  refine DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq ?_ (h1.comp _ _ h2)
  have hopen : IsOpen (A.target ∩ A.symm ⁻¹' c.source) :=
    A.toOpenPartialHomeomorph.isOpen_inter_preimage_symm c.open_source
  have hmem : A p ∈ A.target ∩ A.symm ⁻¹' c.source := by
    refine ⟨A.map_source hpA, ?_⟩
    change (A.symm.toPartialEquiv : M → X) (A.toPartialEquiv p) ∈ c.source
    rw [e]
    exact hpc
  filter_upwards [hopen.mem_nhds hmem] with y hy
  have e' : (A.toPartialEquiv : X → M) (A.symm.toPartialEquiv y) = y := A.right_inv hy.1
  have h := heq (A.symm y) ⟨A.map_target hy.1, hy.2⟩
  change map ((A.toPartialEquiv : X → M) (A.symm.toPartialEquiv y)) = _ at h
  rw [e'] at h
  exact h

end LocalDiffeo

section Sweep

variable {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier} (F : CircleFibration C U)

theorem injOn_liftSweep {cB : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ))
      (SurfaceModel.model F.base.kind) (Circle × ℝ) F.base.Carrier ∞}
    (hc : cB.source = {p | -1 < p.2 ∧ p.2 < 1}) (L : LiftedBicollar F cB) {y : Torus → U}
    (hy : Injective y) (hyc : ∀ t, ∃ θ, F.projection (y t) = cB (θ, 0)) {d : ℝ} (hd : 0 < d)
    (hdw : d ≤ L.width) :
    InjOn (fun z : Torus × ℝ => L.flow (d * z.2) (y z.1)) signedCollarSource := by
  rintro ⟨t, s⟩ ⟨hs1, hs2⟩ ⟨t', s'⟩ ⟨hs1', hs2'⟩ h
  change L.flow (d * s) (y t) = L.flow (d * s') (y t') at h
  have hw : ∀ r : ℝ, -1 < r → r < 1 → |d * r| < L.width := fun r h1 h2 => by
    rw [abs_mul, abs_of_pos hd]
    calc d * |r| < d * 1 := mul_lt_mul_of_pos_left (abs_lt.mpr ⟨h1, h2⟩) hd
      _ = d := mul_one d
      _ ≤ L.width := hdw
  obtain ⟨θ, hθ⟩ := hyc t
  obtain ⟨θ', hθ'⟩ := hyc t'
  have hp := congrArg F.projection h
  rw [L.projection_flow, L.projection_flow, hθ, hθ',
    L.baseFlow_apply θ 0 (d * s) (by simpa using L.width_pos) (by simpa using hw s hs1 hs2),
    L.baseFlow_apply θ' 0 (d * s') (by simpa using L.width_pos) (by simpa using hw s' hs1' hs2'),
    zero_add, zero_add] at hp
  have hsrc : ∀ (φ : Circle) (r : ℝ), -1 < r → r < 1 → (φ, d * r) ∈ cB.source := fun φ r h1 h2 => by
    rw [hc]
    have := hw r h1 h2
    have hlt := L.lt_one_of_lt_width hc this
    exact hlt
  have he := cB.injOn (hsrc θ s hs1 hs2) (hsrc θ' s' hs1' hs2') hp
  have hss : s = s' := mul_left_cancel₀ hd.ne' (congrArg Prod.snd he)
  subst hss
  have htt := hy ((L.flow (d * s)).injective h)
  rw [htt]

end Sweep

section CollarPiece

variable (L : ℝ) [Fact (0 < L)] {X : Type*}

theorem collarPieceMap_shrink_zero (Kp : Torus × Icc (0 : ℝ) L → X) {η : ℝ} (hη : 0 < η)
    (hη1 : η ≤ 1) (t v : Circle) {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) :
    collarPieceMap L Kp (((planarBase.{u} 2 (Or.inl rfl)).shrink hη hη1).collar 0
      (t, halfPoint s hs), v) =
      Kp ((t, v), Set.projIcc 0 L (Fact.out : (0 : ℝ) < L).le (L * (η * s) / 10)) := by
  rw [shrink_collar_halfPoint]
  exact collarPieceMap_collar_zero L Kp t v _ (by nlinarith)

theorem collarPieceMap_shrink_one (Kp : Torus × Icc (0 : ℝ) L → X) {η : ℝ} (hη : 0 < η)
    (hη1 : η ≤ 1) (t v : Circle) {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) :
    collarPieceMap L Kp (((planarBase.{u} 2 (Or.inl rfl)).shrink hη hη1).collar 1
      (t, halfPoint s hs), v) =
      Kp ((t⁻¹, v), Set.projIcc 0 L (Fact.out : (0 : ℝ) < L).le (L - L * (η * s) / 10)) := by
  rw [shrink_collar_halfPoint]
  exact collarPieceMap_collar_one L Kp t v _ (by nlinarith)

theorem sideTorus_collarPiece (Kp : Torus × Icc (0 : ℝ) L → X) {η : ℝ} (hη : 0 < η)
    (hη1 : η ≤ 1) (t : Torus) :
    sideTorus ((planarBase.{u} 2 (Or.inl rfl)).shrink hη hη1) 1 (collarPieceMap L Kp) t =
      Kp ((t.1⁻¹, t.2), ⟨L, (Fact.out : (0 : ℝ) < L).le, le_rfl⟩) := by
  rw [sideTorus_shrink]
  change collarPieceMap L Kp ((planarBase.{u} 2 (Or.inl rfl)).collar 1
    (t.1, halfPoint 0 le_rfl), t.2) = _
  rw [collarPieceMap_collar_one L Kp t.1 t.2 le_rfl one_pos]
  congr 2
  rw [Set.projIcc_of_mem _ ⟨by linarith [(Fact.out : (0 : ℝ) < L)], by linarith⟩]
  exact Subtype.ext (by simp)

theorem shrink_collar_halfZero {k : ℕ} (Q : PlanarBase.{u} k) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (l : Fin k) (t : Circle) :
    (Q.shrink hδ hδ1).collar l (t, halfZero) = Q.collar l (t, halfZero) := by
  change Q.collar l (t, halfSpaceScale hδ halfZero) = _
  rw [halfSpaceScale_halfZero]

theorem collarPiece_sync_one (Kp : Torus × Icc (0 : ℝ) L → X) (φ : ℝ → X → X) {δ' δ : ℝ}
    (hδ : 0 < δ) (hδδ' : δ ≤ δ') (hδL : δ ≤ L / 10)
    (htop : ∀ p (s : Icc (0 : ℝ) L), L - δ' < s.1 →
      Kp (p, s) = φ (s.1 - L) (Kp (p, ⟨L, (Fact.out : (0 : ℝ) < L).le, le_rfl⟩)))
    (hη : 0 < 10 * δ / L) (hη1 : 10 * δ / L ≤ 1) (t v : Circle) {r : ℝ} (hr : 0 ≤ r)
    (hr1 : r < 1) :
    collarPieceMap L Kp (((planarBase.{u} 2 (Or.inl rfl)).shrink hη hη1).collar 1
      (t, halfPoint r hr), v) =
      φ (-(δ * r)) (collarPieceMap L Kp (((planarBase.{u} 2 (Or.inl rfl)).shrink hη hη1).collar 1
        (t, halfZero), v)) := by
  have hL : 0 < L := Fact.out
  have e : L * (10 * δ / L * r) / 10 = δ * r := by
    field_simp
  rw [collarPieceMap_shrink_one L Kp hη hη1 t v hr hr1, e,
    show halfZero = halfPoint 0 le_rfl from rfl,
    collarPieceMap_shrink_one L Kp hη hη1 t v le_rfl one_pos, mul_zero, mul_zero, zero_div,
    sub_zero]
  have hm : L - δ * r ∈ Icc (0 : ℝ) L := ⟨by nlinarith, by nlinarith⟩
  rw [Set.projIcc_of_mem _ hm, Set.projIcc_of_mem _ ⟨hL.le, le_rfl⟩,
    htop _ ⟨L - δ * r, hm⟩ (by change L - δ' < L - δ * r; nlinarith)]
  congr 1
  change L - δ * r - L = -(δ * r)
  ring

theorem collarPiece_port_zero (Kp : Torus × Icc (0 : ℝ) L → X) {δ : ℝ} (hδ : 0 < δ)
    (hδL : δ ≤ L / 10) (hη : 0 < 10 * δ / L) (hη1 : 10 * δ / L ≤ 1) (t v : Circle) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) :
    collarPieceMap L Kp (((planarBase.{u} 2 (Or.inl rfl)).shrink hη hη1).collar 0
      (t, halfPoint r hr), v) =
      Kp ((t, v), ⟨δ * r, mul_nonneg hδ.le hr, by nlinarith [(Fact.out : (0 : ℝ) < L)]⟩) := by
  have hL : 0 < L := Fact.out
  have e : L * (10 * δ / L * r) / 10 = δ * r := by
    field_simp
  rw [collarPieceMap_shrink_zero L Kp hη hη1 t v hr hr1, e,
    Set.projIcc_of_mem _ ⟨mul_nonneg hδ.le hr, by nlinarith⟩]

end CollarPiece

section ZeroSec

variable {B : CompactSurface.{u}} {D : BaseMorseData B} (P : PlanarCore D)

def zeroSec (w : Σ j, Fin (P.kind j)) : Set B.Carrier :=
  range fun t => P.ι w.1 ((P.base w.1).collar w.2 (t, halfZero))

theorem zeroSec_eq {j : Fin P.pieceCount} {l : Fin (P.kind j)} (h : P.IsBottom j l) :
    zeroSec P ⟨j, l⟩ = range (fun θ => P.bottomBicollar j l h (θ, 0)) :=
  P.range_bottom h

theorem level_of_mem_zeroSec {j : Fin P.pieceCount} {l : Fin (P.kind j)} (h : P.IsBottom j l)
    {y : B.Carrier} (hy : y ∈ zeroSec P ⟨j, l⟩) : D.f y = D.level 0 := by
  obtain ⟨t, rfl⟩ := hy
  exact P.level_bottom h t

end ZeroSec

section Assembly

variable {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier} (F : CircleFibration C U)
  {D : BaseMorseData F.base} (P : PlanarCore D)

theorem projection_preimage_zeroSec {j : Fin P.pieceCount} {l : Fin (P.kind j)}
    (h : P.IsBottom j l) {Φ : (P.base j).surface.Carrier × Circle → U}
    (hπ : ∀ q, F.projection (Φ q) = P.ι j q.1) (hrange : range Φ = F.projection ⁻¹' range (P.ι j)) :
    F.projection ⁻¹' zeroSec P ⟨j, l⟩ = range (sideTorus (P.base j) l Φ) := by
  rw [zeroSec_eq P h, range_sideTorus_eq F (P.base j) (P.injective_ι j) hπ hrange l
    (σ := P.bottomSigma j l h) fun t => P.bottomSigma_spec j l h t 0 le_rfl one_pos]

end Assembly

section Sides

def wiringSide {n m : ℕ} (kindP : Fin n → ℕ) (cutSide : Fin m → Bool → Σ j, Fin (kindP j))
    {ε : Type*} (βs : ε → Σ j, Fin (kindP j)) :
    Fin m ⊕ ε → Bool → Σ x : Fin n ⊕ ε, Fin (Sum.elim kindP (fun _ => 2) x)
  | .inl c, b => ⟨Sum.inl (cutSide c (!b)).1, (cutSide c (!b)).2⟩
  | .inr s, true => ⟨Sum.inr s, (1 : Fin 2)⟩
  | .inr s, false => ⟨Sum.inl (βs s).1, (βs s).2⟩

theorem inl_sigma_injective {n : ℕ} (kindP : Fin n → ℕ) {ε : Type*} {w w' : Σ j, Fin (kindP j)}
    (h : (⟨Sum.inl w.1, w.2⟩ : Σ x : Fin n ⊕ ε, Fin (Sum.elim kindP (fun _ => 2) x)) =
      ⟨Sum.inl w'.1, w'.2⟩) : w = w' := by
  obtain ⟨j, l⟩ := w
  obtain ⟨j', l'⟩ := w'
  have h1 := (Sigma.mk.inj_iff.mp h).1
  obtain rfl : j = j' := Sum.inl_injective h1
  have h2 : l = l' := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  rw [h2]

theorem wiringSide_bijective {n m : ℕ} (kindP : Fin n → ℕ)
    (cutSide : Fin m → Bool → Σ j, Fin (kindP j)) (hcut : Injective (uncurry cutSide))
    {ε : Type*} (βs : ε → Σ j, Fin (kindP j)) (hβbot : ∀ s c b, cutSide c b ≠ βs s)
    (hβinj : Injective βs) (hβsurj : ∀ w, (∀ c b, cutSide c b ≠ w) → ∃ s, βs s = w) :
    Bijective (Sum.elim (uncurry (wiringSide kindP cutSide βs))
      fun e => (⟨Sum.inr e, (0 : Fin 2)⟩ : Σ x : Fin n ⊕ ε,
        Fin (Sum.elim kindP (fun _ => 2) x))) := by
  constructor
  · rintro (⟨c | s, b⟩ | e) (⟨c' | s', b'⟩ | e') h
    · have h' := inl_sigma_injective kindP h
      have he : (c, !b) = (c', !b') := hcut h'
      obtain ⟨rfl, hb⟩ := Prod.mk.inj he
      rw [Bool.not_inj hb]
    · cases b'
      · exact absurd (inl_sigma_injective kindP h) (hβbot s' c (!b))
      · exact absurd (congrArg Sigma.fst h) (by simp [wiringSide])
    · exact absurd (congrArg Sigma.fst h) (by simp [wiringSide])
    · cases b
      · exact absurd (inl_sigma_injective kindP h).symm (hβbot s c' (!b'))
      · exact absurd (congrArg Sigma.fst h) (by simp [wiringSide])
    · cases b <;> cases b'
      · rw [hβinj (inl_sigma_injective kindP h)]
      · exact absurd (congrArg Sigma.fst h) (by simp [wiringSide])
      · exact absurd (congrArg Sigma.fst h) (by simp [wiringSide])
      · have h1 : s = s' := Sum.inr_injective (congrArg Sigma.fst h)
        rw [h1]
    · cases b
      · exact absurd (congrArg Sigma.fst h) (by simp [wiringSide])
      · have h1 : s = e' := Sum.inr_injective (congrArg Sigma.fst h)
        subst h1
        have h2 := congrArg Fin.val (eq_of_heq (Sigma.mk.inj_iff.mp h).2)
        exact absurd h2 one_ne_zero
    · exact absurd (congrArg Sigma.fst h) (by simp [wiringSide])
    · cases b'
      · exact absurd (congrArg Sigma.fst h) (by simp [wiringSide])
      · have h1 : e = s' := Sum.inr_injective (congrArg Sigma.fst h)
        subst h1
        have h2 := congrArg Fin.val (eq_of_heq (Sigma.mk.inj_iff.mp h).2)
        exact absurd h2 zero_ne_one
    · have h1 : e = e' := Sum.inr_injective (congrArg Sigma.fst h)
      rw [h1]
  · rintro ⟨j | s, l⟩
    · by_cases hb : ∀ c b, cutSide c b ≠ ⟨j, l⟩
      · obtain ⟨s, hs⟩ := hβsurj ⟨j, l⟩ hb
        refine ⟨Sum.inl (Sum.inr s, false), ?_⟩
        change (⟨Sum.inl (βs s).1, (βs s).2⟩ : Σ x : Fin n ⊕ ε,
          Fin (Sum.elim kindP (fun _ => 2) x)) = ⟨Sum.inl j, l⟩
        rw [hs]
      · push Not at hb
        obtain ⟨c, b, hcb⟩ := hb
        refine ⟨Sum.inl (Sum.inl c, !b), ?_⟩
        change (⟨Sum.inl (cutSide c (!!b)).1, (cutSide c (!!b)).2⟩ : Σ x : Fin n ⊕ ε,
          Fin (Sum.elim kindP (fun _ => 2) x)) = ⟨Sum.inl j, l⟩
        rw [Bool.not_not, hcb]
    · rcases l with ⟨_ | _ | k, hk⟩
      · exact ⟨Sum.inr s, rfl⟩
      · exact ⟨Sum.inl (Sum.inr s, true), rfl⟩
      · change k + 2 < 2 at hk
        omega

end Sides

section Main

variable {W : CompactCarrier.{u}} (T : TorusPresentation W) (i : Fin T.components.count)
  (F : CircleFibration T.cutCarrier (T.components.piece i)) {D : BaseMorseData F.base}
  (P : PlanarCore D)

structure WiringData [Fact (0 < D.level 0)] where
  Φ : ∀ j, (P.base j).surface.Carrier × Circle → T.components.piece i
  smoothΦ : ∀ j, ContMDiff ((SurfaceModel.model (P.base j).surface.kind).prod (𝓡 1))
    T.cutCarrier.model ∞ (Φ j)
  bijΦ : ∀ j q, Bijective (mfderiv ((SurfaceModel.model (P.base j).surface.kind).prod (𝓡 1))
    T.cutCarrier.model (Φ j) q)
  injΦ : ∀ j, Injective (Φ j)
  projΦ : ∀ j q, F.projection (Φ j q) = P.ι j q.1
  rangeΦ : ∀ j, range (Φ j) = F.projection ⁻¹' range (P.ι j)
  nonempty : Nonempty (Fin P.pieceCount)
  δ₀ : ℝ
  δ₀_pos : 0 < δ₀
  δ₀_le_width : δ₀ ≤ 1 / 16
  δ₀_le_level : δ₀ ≤ D.level 0 / 10
  cutSync : ∀ j l c b, P.cutSide c b = ⟨j, l⟩ → ∀ t v s (hs : 0 ≤ s), s < δ₀ →
    Φ j ((P.base j).collar l (t, halfPoint s hs), v) =
      (PlanarCore.cutLift F P c).flow (if b then s else -s)
        (Φ j ((P.base j).collar l (t, halfZero), v))
  bottomSync : ∀ j l (h : P.IsBottom j l) t v s (hs : 0 ≤ s), s < δ₀ →
    Φ j ((P.base j).collar l (t, halfPoint s hs), v) =
      (PlanarCore.bottomLift F P j l h).flow s (Φ j ((P.base j).collar l (t, halfZero), v))
  βj : T.OwnedSide i → Fin P.pieceCount
  βl : ∀ s, Fin (P.kind (βj s))
  βh : ∀ s, P.IsBottom (βj s) (βl s)
  β_inj : ∀ s s', (⟨βj s, βl s⟩ : Σ j, Fin (P.kind j)) = ⟨βj s', βl s'⟩ → s = s'
  β_surj : ∀ j l, P.IsBottom j l → ∃ s, (⟨βj s, βl s⟩ : Σ j, Fin (P.kind j)) = ⟨j, l⟩
  K : T.OwnedSide i → Torus × Icc (0 : ℝ) (D.level 0) → T.components.piece i
  smoothK : ∀ s, ContMDiff (torusModel.prod (𝓡∂ 1)) T.cutCarrier.model ∞ (K s)
  bijK : ∀ s q, Bijective (mfderiv (torusModel.prod (𝓡∂ 1)) T.cutCarrier.model (K s) q)
  injK : ∀ s, Injective (K s)
  lowK : ∀ s p (r : Icc (0 : ℝ) (D.level 0)), r.1 < δ₀ →
    (K s (p, r)).val = T.sideCollar s.val (p, halfPoint r.1 r.2.1)
  topK : ∀ s p (r : Icc (0 : ℝ) (D.level 0)), D.level 0 - δ₀ < r.1 →
    K s (p, r) = (PlanarCore.bottomLift F P (βj s) (βl s) (βh s)).flow (r.1 - D.level 0)
      (K s (p, topPoint D))
  region : ∀ s, range (fun q => (K s q).val) =
    connectedComponentIn (lowSet F D) (T.sideCollar s.val (1, halfZero))
  top_eq : ∀ s q, portHeight F D (K s q) = D.level 0 → q.2 = topPoint D
  top_range : ∀ s, range (fun p => K s (p, topPoint D)) = F.projection ⁻¹' zeroSec P ⟨βj s, βl s⟩
  disjoint : ∀ (s s' : T.OwnedSide i) (z : T.components.piece i),
    z.val ∈ connectedComponentIn (lowSet F D) (T.sideCollar s.val (1, halfZero)) →
    z.val ∈ connectedComponentIn (lowSet F D) (T.sideCollar s'.val (1, halfZero)) → s = s'
  cover : ∀ z : T.components.piece i, portHeight F D z ≤ D.level 0 →
    ∃ s : T.OwnedSide i,
      z.val ∈ connectedComponentIn (lowSet F D) (T.sideCollar s.val (1, halfZero))

theorem nonempty_wiringData [Fact (0 < D.level 0)] : Nonempty (WiringData T i F P) := by
  classical
  have hℓ : 0 < D.level 0 := D.level_zero_pos
  have hUc : IsClosed (T.components.piece i : Set T.cutCarrier.Carrier) := T.components.closed i
  have : ConnectedSpace (T.components.piece i) := T.components.connected i
  have hc₀src : ∀ s : T.OwnedSide i, (T.sideCollar s.val).source = halfCollarSource :=
    fun s => T.sideCollar_source s.val
  have hc₀b : ∀ (s : T.OwnedSide i) t,
      T.cutCarrier.model.IsBoundaryPoint (T.sideCollar s.val (t, halfZero)) :=
    fun s t => (T.sideCollar_zero_mem s.val t).1
  have hc₀own : ∀ s : T.OwnedSide i, (T.sideCollar s.val).target ⊆ T.components.piece i :=
    T.sideCollar_target_subset_of_owned i
  have hc₀mem : ∀ (s : T.OwnedSide i) t, T.sideCollar s.val (t, halfZero) ∈ T.components.piece i :=
    fun s t => hc₀own s ((T.sideCollar s.val).map_source (T.zero_mem_sideCollar_source s.val t))
  have hc₀low : ∀ (s : T.OwnedSide i) t, T.sideCollar s.val (t, halfZero) ∈ lowSet F D := by
    intro s t
    refine ⟨hc₀mem s t, ?_⟩
    rw [(BaseMorseData.f_projection_eq_zero_iff F D ⟨_, hc₀mem s t⟩).mpr (hc₀b s t)]
    exact hℓ.le
  choose Φ hΦs hΦi hΦb hΦπ hΦr δP hδP hΦsync using PlanarCore.exists_planarPieceMap F P
  choose xs hxsR hxsu using fun s : T.OwnedSide i => exists_level_mem_component hUc (hc₀low s 1)
  choose βj βl βh βt hβ using fun s : T.OwnedSide i => P.exists_bottom_of_level (hxsu s)
  have htie : ∀ s : T.OwnedSide i, F.projection (xs s) =
      P.bottomBicollar (βj s) (βl s) (βh s) (P.bottomSigma (βj s) (βl s) (βh s) (βt s), 0) :=
    fun s => (hβ s).symm.trans (P.bottomSigma_spec _ _ _ (βt s) 0 le_rfl one_pos)
  choose δK hδK K hKs hKi hKb hKR hKlow hKtop using fun s : T.OwnedSide i =>
    exists_oldPortCollarPiece F D (T.sideCollar s.val) (hc₀src s) (hc₀b s) (hc₀own s)
      (P.bottomBicollar (βj s) (βl s) (βh s)) (P.bottomBicollar_spec _ _ _).1
      (P.bottomBicollar_spec _ _ _).2.2.1 ⟨_, xs s, htie s, hxsR s⟩
      (PlanarCore.bottomLift F P (βj s) (βl s) (βh s))
  have hKc : ∀ s, Continuous (K s) := fun s => continuous_induced_rng.mpr (hKs s).continuous
  have hKR' : ∀ s, range (fun q => (K s q).val) =
      connectedComponentIn (lowSet F D) (T.sideCollar s.val (1, halfZero)) := hKR
  have hRlow : ∀ s, range (fun q => (K s q).val) ⊆ lowSet F D := fun s =>
    (hKR' s).trans_subset (connectedComponentIn_subset _ _)
  have hK0 : ∀ s p (r : Icc (0 : ℝ) (D.level 0)), r.1 = 0 →
      portHeight F D (K s (p, r)) ≠ D.level 0 := by
    intro s p r hr hu
    have h1 := hKlow s p r (by rw [hr]; exact hδK s)
    have e : halfPoint r.1 r.2.1 = halfZero := by
      unfold halfZero
      congr 1
    rw [e] at h1
    have hb : T.cutCarrier.model.IsBoundaryPoint (K s (p, r)).val := by
      rw [h1]
      exact hc₀b s p
    have h0 := (BaseMorseData.f_projection_eq_zero_iff F D _).mpr hb
    change portHeight F D _ = 0 at h0
    rw [h0] at hu
    linarith
  have htopK : ∀ s p, portHeight F D (K s (p, topPoint D)) = D.level 0 := fun s =>
    portHeight_top (hKc s) (hKi s) (hKR' s)
      (φ := fun r x => (PlanarCore.bottomLift F P (βj s) (βl s) (βh s)).flow r x)
      (fun x => (PlanarCore.bottomLift F P (βj s) (βl s) (βh s)).smooth.continuous.comp
        (continuous_id.prodMk continuous_const))
      (PlanarCore.bottomLift F P (βj s) (βl s) (βh s)).flow_zero
      (PlanarCore.bottomLift F P (βj s) (βl s) (βh s)).flow_add (hδK s) (hKtop s)
  have hKtopeq : ∀ s q, portHeight F D (K s q) = D.level 0 → q.2 = topPoint D := by
    rintro s ⟨p, r⟩ hq
    exact Subtype.ext (eq_top_of_portHeight (hKs s) (hKb s) (hRlow s) (hK0 s) hq)
  have hxsZ : ∀ s, F.projection (xs s) ∈ zeroSec P ⟨βj s, βl s⟩ := fun s => ⟨βt s, hβ s⟩
  have hZpre : ∀ s, F.projection ⁻¹' zeroSec P ⟨βj s, βl s⟩ =
      range (sideTorus (P.base (βj s)) (βl s) (Φ (βj s))) := fun s =>
    projection_preimage_zeroSec F P (βh s) (hΦπ _) (hΦr _)
  have hΦU : ∀ j, ContMDiff ((SurfaceModel.model (P.base j).surface.kind).prod (𝓡 1))
      T.cutCarrier.model ∞ (Φ j) := fun j => (ContMDiff.subtypeVal_comp_iff _ _).mp (hΦs j)
  have hZconn : ∀ s, IsPreconnected (F.projection ⁻¹' zeroSec P ⟨βj s, βl s⟩) := fun s => by
    rw [hZpre s]
    exact isPreconnected_range (contMDiff_sideTorus _ _ (hΦU _)).continuous
  have hsubR : ∀ s, Subtype.val '' (F.projection ⁻¹' zeroSec P ⟨βj s, βl s⟩) ⊆
      connectedComponentIn (lowSet F D) (T.sideCollar s.val (1, halfZero)) := fun s =>
    image_val_subset_component (hZconn s) (fun z hz => (level_of_mem_zeroSec P (βh s) hz).le)
      (hxsZ s) (hxsR s)
  have hτ : ∀ s, range (fun p => K s (p, topPoint D)) =
      F.projection ⁻¹' zeroSec P ⟨βj s, βl s⟩ := by
    intro s
    apply subset_antisymm
    · obtain ⟨q, hq⟩ : (xs s).val ∈ range (fun q => (K s q).val) := by
        rw [hKR' s]
        exact hxsR s
      have hq' : K s q = xs s := Subtype.ext hq
      have htq := hKtopeq s q (by rw [hq']; exact hxsu s)
      have hp₀ : K s (q.1, topPoint D) = xs s := by
        rw [← htq]
        exact hq'
      rintro _ ⟨p, rfl⟩
      change F.projection (K s (p, topPoint D)) ∈ zeroSec P ⟨βj s, βl s⟩
      rw [zeroSec_eq P (βh s), (P.bottomBicollar_spec _ _ _).2.1]
      have hS : IsPreconnected (range fun p => F.projection (K s (p, topPoint D))) :=
        isPreconnected_range (F.projection.continuous.comp
          ((hKc s).comp (continuous_id.prodMk continuous_const)))
      have hmem0 : F.projection (xs s) ∈ connectedComponentIn (D.f ⁻¹' {D.level 0})
          (P.bottomPoint (βj s) (βl s) (βh s)) := by
        rw [← (P.bottomBicollar_spec _ _ _).2.1, ← zeroSec_eq P (βh s)]
        exact hxsZ s
      rw [connectedComponentIn_eq hmem0]
      exact hS.subset_connectedComponentIn ⟨q.1, congrArg F.projection hp₀⟩
        (by rintro _ ⟨p', rfl⟩; exact htopK s p') ⟨p, rfl⟩
    · intro z hz
      obtain ⟨q, hq⟩ : z.val ∈ range (fun q => (K s q).val) := by
        rw [hKR' s]
        exact hsubR s ⟨z, hz, rfl⟩
      have hq' : K s q = z := Subtype.ext hq
      have hu : portHeight F D (K s q) = D.level 0 := by
        rw [hq']
        exact level_of_mem_zeroSec P (βh s) hz
      refine ⟨q.1, ?_⟩
      rw [← hKtopeq s q hu]
      exact hq'
  have hdist : ∀ (s s' : T.OwnedSide i) (z : T.components.piece i),
      z.val ∈ connectedComponentIn (lowSet F D) (T.sideCollar s.val (1, halfZero)) →
      z.val ∈ connectedComponentIn (lowSet F D) (T.sideCollar s'.val (1, halfZero)) → s = s' := by
    intro s s' z hz hz'
    by_contra hne
    have hRR := (connectedComponentIn_eq hz).trans (connectedComponentIn_eq hz').symm
    obtain ⟨⟨p, r⟩, hq⟩ : T.sideCollar s'.val (1, halfZero) ∈ range (fun q => (K s q).val) := by
      rw [hKR' s, hRR]
      exact mem_connectedComponentIn (hc₀low s' 1)
    have hqb : T.cutCarrier.model.IsBoundaryPoint (K s (p, r)).val := by
      change (K s (p, r)).val = _ at hq
      rw [hq]
      exact hc₀b s' 1
    have hr0 := eq_zero_of_isBoundaryPoint (hKs s) (hKb s) (htopK s) hqb
    have h1 := hKlow s p r (by rw [hr0]; exact hδK s)
    have hne' : s.val ≠ s'.val := fun e => hne (Subtype.ext e)
    refine Set.disjoint_left.mp (T.sideCollar_disjoint hne') ?_
      ((T.sideCollar s'.val).map_source (T.zero_mem_sideCollar_source s'.val 1))
    change (K s (p, r)).val = _ at hq
    rw [← hq, h1]
    refine (T.sideCollar s.val).map_source ?_
    rw [hc₀src s]
    change r.1 < 1
    rw [hr0]
    exact one_pos
  have hcov : ∀ z : T.components.piece i, portHeight F D z ≤ D.level 0 →
      ∃ s : T.OwnedSide i, z.val ∈ connectedComponentIn (lowSet F D)
        (T.sideCollar s.val (1, halfZero)) := by
    intro z hz
    obtain ⟨y, hyb, hyR⟩ := exists_isBoundaryPoint_mem_component hUc z hz
    obtain ⟨s₀, t, hst⟩ := T.exists_sideCollar_zero_eq hyb
    have hsi : T.sidePiece s₀ = i := by
      by_contra hne
      exact (T.components.disjoint hne).le_bot ⟨hst ▸ (T.sideCollar_zero_mem s₀ t).2, y.property⟩
    refine ⟨⟨s₀, hsi⟩, ?_⟩
    have htor : IsPreconnected (range fun t => T.sideCollar s₀ (t, halfZero)) :=
      isPreconnected_range ((T.sideCollar s₀).toOpenPartialHomeomorph.continuousOn.comp_continuous
        (continuous_id.prodMk continuous_const) fun t => T.zero_mem_sideCollar_source s₀ t)
    have hyR' : y.val ∈ connectedComponentIn (lowSet F D) (T.sideCollar s₀ (1, halfZero)) :=
      htor.subset_connectedComponentIn ⟨1, rfl⟩
        (by rintro _ ⟨t', rfl⟩; exact hc₀low ⟨s₀, hsi⟩ t') ⟨t, hst⟩
    change z.val ∈ connectedComponentIn (lowSet F D) (T.sideCollar s₀ (1, halfZero))
    rw [connectedComponentIn_eq hyR', ← connectedComponentIn_eq hyR]
    exact mem_connectedComponentIn (val_mem_lowSet.mpr hz)
  have hβinj : ∀ s s', (⟨βj s, βl s⟩ : Σ j, Fin (P.kind j)) = ⟨βj s', βl s'⟩ → s = s' := by
    intro s s' he
    have hz : xs s ∈ F.projection ⁻¹' zeroSec P ⟨βj s', βl s'⟩ := by
      rw [← he]
      exact hxsZ s
    exact hdist s s' (xs s) (hxsR s) (hsubR s' ⟨_, hz, rfl⟩)
  have hβsurj : ∀ j l, P.IsBottom j l →
      ∃ s, (⟨βj s, βl s⟩ : Σ j, Fin (P.kind j)) = ⟨j, l⟩ := by
    intro j l h
    obtain ⟨z₀, hz₀⟩ := F.surjective (P.ι j ((P.base j).collar l (1, halfZero)))
    have hu : portHeight F D z₀ = D.level 0 := by
      change D.f (F.projection z₀) = _
      rw [hz₀]
      exact P.level_bottom h 1
    obtain ⟨s, hs⟩ := hcov z₀ hu.le
    refine ⟨s, ?_⟩
    obtain ⟨q, hq⟩ : z₀.val ∈ range (fun q => (K s q).val) := by
      rw [hKR' s]
      exact hs
    have hq' : K s q = z₀ := Subtype.ext hq
    have hτm : z₀ ∈ range (fun p => K s (p, topPoint D)) :=
      ⟨q.1, by rw [← hKtopeq s q (by rw [hq']; exact hu)]; exact hq'⟩
    rw [hτ s] at hτm
    obtain ⟨t', ht'⟩ := hτm
    exact P.bottom_unique (βh s) h (ht'.trans hz₀)
  have hne : Nonempty (Fin P.pieceCount) := by
    obtain ⟨b, hb⟩ := D.exists_level_zero_lt
    have hb' : b ∈ ⋃ j, range (P.ι j) := by
      rw [P.iUnion_range_ι]
      exact hb.le
    obtain ⟨j, -⟩ := mem_iUnion.mp hb'
    exact ⟨j⟩
  have hΦbU : ∀ j q, Bijective (mfderiv ((SurfaceModel.model (P.base j).surface.kind).prod (𝓡 1))
      T.cutCarrier.model (Φ j) q) := fun j q => by
    have h := hΦb j q
    rwa [DifferentialGeometry.mfderiv_subtypeVal_comp (Φ j) q] at h
  have hKU : ∀ s, ContMDiff (torusModel.prod (𝓡∂ 1)) T.cutCarrier.model ∞ (K s) := fun s =>
    (ContMDiff.subtypeVal_comp_iff _ _).mp (hKs s)
  have hKbU : ∀ s q, Bijective (mfderiv (torusModel.prod (𝓡∂ 1)) T.cutCarrier.model (K s) q) :=
    fun s q => by
      have h := hKb s q
      rwa [DifferentialGeometry.mfderiv_subtypeVal_comp (K s) q] at h
  obtain ⟨mP, hmP, hmPle⟩ := exists_pos_le_of_finite δP hδP
  obtain ⟨mK, hmK, hmKle⟩ := exists_pos_le_of_finite δK hδK
  set δ₀ := min (min (1 / 16) (D.level 0 / 10)) (min mP mK) with hδ₀
  have hδP' : ∀ j, δ₀ ≤ δP j := fun j =>
    ((min_le_right _ _).trans (min_le_left _ _)).trans (hmPle j)
  have hδK' : ∀ s, δ₀ ≤ δK s := fun s =>
    ((min_le_right _ _).trans (min_le_right _ _)).trans (hmKle s)
  exact ⟨{ Φ := Φ
           smoothΦ := hΦU
           bijΦ := hΦbU
           injΦ := hΦi
           projΦ := hΦπ
           rangeΦ := hΦr
           nonempty := hne
           δ₀ := δ₀
           δ₀_pos := by positivity
           δ₀_le_width := (min_le_left _ _).trans (min_le_left _ _)
           δ₀_le_level := (min_le_left _ _).trans (min_le_right _ _)
           cutSync := fun j l c b h t v s hs hs1 =>
             (hΦsync j).1 l c b h t v s hs (hs1.trans_le (hδP' j))
           bottomSync := fun j l h t v s hs hs1 =>
             (hΦsync j).2 l h t v s hs (hs1.trans_le (hδP' j))
           βj := βj
           βl := βl
           βh := βh
           β_inj := hβinj
           β_surj := hβsurj
           K := K
           smoothK := hKU
           bijK := hKbU
           injK := hKi
           lowK := fun s p r hr => hKlow s p r (hr.trans_le (hδK' s))
           topK := fun s p r hr => hKtop s p r (by linarith [hδK' s])
           region := hKR'
           top_eq := hKtopeq
           top_range := hτ
           disjoint := hdist
           cover := hcov }⟩

end Main

end GC.Seifert.Wiring
