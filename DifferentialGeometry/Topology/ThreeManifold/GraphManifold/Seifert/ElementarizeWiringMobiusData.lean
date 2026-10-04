import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ElementarizeWiringMobiusCore

/-!
# The wiring data of one old piece with planar and Möbius core pieces

Lane P1X2 (P1 wiring, the Möbius branch). The analogue of P1W's `WiringData` for a `MobiusCore`.

Let `T` be a torus presentation, `i` a component carrying a circle fibration `F` whose base has
Morse data `D` with a Möbius core `P`. A `MixedWiringData T i F P` collects

* the synchronised planar piece maps `Φ j` over the planar pieces of `P`
  (`MobiusCore.exists_planarPieceMap`);
* the synchronised Möbius piece maps `χ m : mobiusBundleCarrier → U` over the Möbius pieces
  (`MobiusCore.exists_mobiusPieceMap`, from the frozen hypothesis `hMD5`), with range
  `π⁻¹ (range ιM m)`, boundary torus `π⁻¹` of the zero section of the side, and synchronised
  with the flow of the cut or of the level bicollar of the side near the boundary torus;
* for every owned side `s` the collar piece `K s` of MD5's `exists_oldPortCollarPiece` and the
  bottom side `β s` (a side of `P`, planar or Möbius) on which it ends;
* a common width `δ₀` below which all synchronisations hold.

`nonempty_mixedWiringData` builds it as P1W's `nonempty_wiringData` does: the topology of
`ElementarizeWiringTopology` shows that `β` is a bijection from the owned sides onto the bottom
sides; the preimage of the zero section of every side is the image of a torus (`Φ` or `χ`), hence
preconnected.
-/

set_option autoImplicit false

noncomputable section
open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.MobiusCore

theorem zeroSec_eq_bicollar {B : CompactSurface.{u}} {D : BaseMorseData B} (P : MobiusCore D)
    {w : P.pieces.Side} {cB : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model B.kind)
      (Circle × ℝ) B.Carrier ∞} {b : Bool} {σ : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle}
    (hcol : ∀ t s (hs : 0 ≤ s), s < 1 →
      P.pieces.sidePt w (t, halfPoint s hs) = cB (σ t, if b then s else -s)) :
    P.zeroSec w = range (fun θ => cB (θ, 0)) := by
  ext y
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨σ t, ?_⟩
    change cB (σ t, 0) = P.pieces.sidePt w (t, halfPoint 0 le_rfl)
    rw [hcol t 0 le_rfl one_pos]
    cases b <;> simp
  · rintro ⟨θ, rfl⟩
    refine ⟨σ.symm θ, ?_⟩
    change P.pieces.sidePt w (σ.symm θ, halfPoint 0 le_rfl) = _
    rw [hcol _ 0 le_rfl one_pos, Diffeomorph.apply_symm_apply]
    cases b <;> simp

end GC.Seifert.MobiusCore

namespace GC.Seifert.Wiring

section Main

variable {W : CompactCarrier.{u}} (T : TorusPresentation W) (i : Fin T.components.count)
  (F : CircleFibration T.cutCarrier (T.components.piece i)) {D : BaseMorseData F.base}
  (P : MobiusCore D)

structure MixedWiringData [Fact (0 < D.level 0)] where
  Φ : ∀ j, (P.pieces.base j).surface.Carrier × Circle → T.components.piece i
  smoothΦ : ∀ j, ContMDiff ((SurfaceModel.model (P.pieces.base j).surface.kind).prod (𝓡 1))
    T.cutCarrier.model ∞ (Φ j)
  bijΦ : ∀ j q, Bijective (mfderiv ((SurfaceModel.model (P.pieces.base j).surface.kind).prod (𝓡 1))
    T.cutCarrier.model (Φ j) q)
  injΦ : ∀ j, Injective (Φ j)
  projΦ : ∀ j q, F.projection (Φ j q) = P.pieces.ιP j q.1
  rangeΦ : ∀ j, range (Φ j) = F.projection ⁻¹' range (P.pieces.ιP j)
  χ : P.pieces.MI → mobiusBundleCarrier.{u}.Carrier → T.components.piece i
  smoothχ : ∀ m, ContMDiff mobiusBundleCarrier.{u}.model T.cutCarrier.model ∞ (χ m)
  bijχ : ∀ m q, Bijective (mfderiv mobiusBundleCarrier.{u}.model T.cutCarrier.model (χ m) q)
  injχ : ∀ m, Injective (χ m)
  rangeχ : ∀ m, range (χ m) = F.projection ⁻¹' range (P.pieces.ιM m)
  zeroχ : ∀ m, range (fun t => χ m (mobiusExternalCollar (t, halfZero))) =
    F.projection ⁻¹' P.zeroSec (.inr m)
  nonempty : Nonempty (P.pieces.PI ⊕ P.pieces.MI)
  δ₀ : ℝ
  δ₀_pos : 0 < δ₀
  δ₀_le_width : δ₀ ≤ 1 / 16
  δ₀_le_level : δ₀ ≤ D.level 0 / 10
  cutSync : ∀ j l c b, P.cutSide c b = .inl ⟨j, l⟩ → ∀ t v s (hs : 0 ≤ s), s < δ₀ →
    Φ j ((P.pieces.base j).collar l (t, halfPoint s hs), v) =
      (MobiusCore.cutLift F P c).flow (if b then s else -s)
        (Φ j ((P.pieces.base j).collar l (t, halfZero), v))
  bottomSync : ∀ j l (h : P.IsBottom (.inl ⟨j, l⟩)) t v s (hs : 0 ≤ s), s < δ₀ →
    Φ j ((P.pieces.base j).collar l (t, halfPoint s hs), v) =
      (MobiusCore.bottomLift F P _ h).flow s (Φ j ((P.pieces.base j).collar l (t, halfZero), v))
  cutSyncχ : ∀ m c b, P.cutSide c b = .inr m → ∀ t s (hs : 0 ≤ s), s < δ₀ →
    χ m (mobiusExternalCollar (t, halfPoint s hs)) =
      (MobiusCore.cutLift F P c).flow (if b then s else -s)
        (χ m (mobiusExternalCollar (t, halfZero)))
  bottomSyncχ : ∀ m (h : P.IsBottom (.inr m)) t s (hs : 0 ≤ s), s < δ₀ →
    χ m (mobiusExternalCollar (t, halfPoint s hs)) =
      (MobiusCore.bottomLift F P _ h).flow s (χ m (mobiusExternalCollar (t, halfZero)))
  β : T.OwnedSide i → P.pieces.Side
  βh : ∀ s, P.IsBottom (β s)
  β_inj : Injective β
  β_surj : ∀ w, P.IsBottom w → ∃ s, β s = w
  K : T.OwnedSide i → Torus × Icc (0 : ℝ) (D.level 0) → T.components.piece i
  smoothK : ∀ s, ContMDiff (torusModel.prod (𝓡∂ 1)) T.cutCarrier.model ∞ (K s)
  bijK : ∀ s q, Bijective (mfderiv (torusModel.prod (𝓡∂ 1)) T.cutCarrier.model (K s) q)
  injK : ∀ s, Injective (K s)
  lowK : ∀ s p (r : Icc (0 : ℝ) (D.level 0)), r.1 < δ₀ →
    (K s (p, r)).val = T.sideCollar s.val (p, halfPoint r.1 r.2.1)
  topK : ∀ s p (r : Icc (0 : ℝ) (D.level 0)), D.level 0 - δ₀ < r.1 →
    K s (p, r) = (MobiusCore.bottomLift F P (β s) (βh s)).flow (r.1 - D.level 0)
      (K s (p, topPoint D))
  region : ∀ s, range (fun q => (K s q).val) =
    connectedComponentIn (lowSet F D) (T.sideCollar s.val (1, halfZero))
  top_eq : ∀ s q, portHeight F D (K s q) = D.level 0 → q.2 = topPoint D
  top_range : ∀ s, range (fun p => K s (p, topPoint D)) = F.projection ⁻¹' P.zeroSec (β s)
  disjoint : ∀ (s s' : T.OwnedSide i) (z : T.components.piece i),
    z.val ∈ connectedComponentIn (lowSet F D) (T.sideCollar s.val (1, halfZero)) →
    z.val ∈ connectedComponentIn (lowSet F D) (T.sideCollar s'.val (1, halfZero)) → s = s'
  cover : ∀ z : T.components.piece i, portHeight F D z ≤ D.level 0 →
    ∃ s : T.OwnedSide i,
      z.val ∈ connectedComponentIn (lowSet F D) (T.sideCollar s.val (1, halfZero))

theorem range_sideTorus_planar {j : P.pieces.PI} (l : Fin (P.pieces.kind j))
    {Φ : (P.pieces.base j).surface.Carrier × Circle → T.components.piece i}
    (hπ : ∀ q, F.projection (Φ q) = P.pieces.ιP j q.1)
    (hrange : range Φ = F.projection ⁻¹' range (P.pieces.ιP j)) :
    range (sideTorus (P.pieces.base j) l Φ) = F.projection ⁻¹' P.zeroSec (.inl ⟨j, l⟩) := by
  obtain ⟨cB, -, b, σ, -, hcol, -, -⟩ := MobiusCore.exists_sideData F P (.inl ⟨j, l⟩)
  rw [P.zeroSec_eq_bicollar hcol]
  refine range_sideTorus_eq F (P.pieces.base j) (P.pieces.injective_ιP j) hπ hrange l
    (σ := σ) fun t => ?_
  have h := hcol t 0 le_rfl one_pos
  rw [CorePieces.sidePt_inl] at h
  rw [show halfZero = halfPoint 0 le_rfl from rfl, h]
  cases b <;> simp

theorem nonempty_mixedWiringData [Fact (0 < D.level 0)]
    (hMD5 : ∀ {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier}
      (F : CircleFibration C U) (M : MobiusBase.{u}) {ι : M.surface.Carrier → F.base.Carrier}
      (_hι : Manifold.IsSmoothEmbedding
        (SurfaceModel.model M.surface.kind) (SurfaceModel.model F.base.kind) ∞ ι)
      (c : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model F.base.kind) (Circle × ℝ)
        F.base.Carrier ∞)
      (_hc : c.source = {p | -1 < p.2 ∧ p.2 < 1}) (b : Bool) (σ : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle)
      (_hcol : ∀ t s (hs : 0 ≤ s), s < 1 →
        ι (M.collar (t, halfPoint s hs)) = c (σ t, if b then s else -s))
      (_hint : ∀ q, (SurfaceModel.model F.base.kind).IsInteriorPoint (ι q))
      (L : LiftedBicollar F c),
      ∃ χ : mobiusBundleCarrier.{u}.Carrier → U, ContMDiff (𝓡∂ 3) C.model ∞ (fun q => (χ q).val) ∧
        Function.Injective χ ∧
        (∀ q, Function.Bijective (mfderiv (𝓡∂ 3) C.model (fun q => (χ q).val) q)) ∧
        range χ = F.projection ⁻¹' range ι ∧
        range (fun t => χ (mobiusExternalCollar (t, halfZero))) =
          F.projection ⁻¹' range (fun θ => c (θ, 0)) ∧
        ∃ δ > 0, ∀ t s (hs : 0 ≤ s), s < δ → χ (mobiusExternalCollar (t, halfPoint s hs)) =
          L.flow (if b then s else -s) (χ (mobiusExternalCollar (t, halfZero)))) :
    Nonempty (MixedWiringData T i F P) := by
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
  choose Φ hΦs hΦi hΦb hΦπ hΦr δP hδP hΦsync using MobiusCore.exists_planarPieceMap F P
  choose χ hχs hχi hχb hχr hχz δM hδM hχsync using MobiusCore.exists_mobiusPieceMap F P hMD5
  choose xs hxsR hxsu using fun s : T.OwnedSide i => exists_level_mem_component hUc (hc₀low s 1)
  choose β βh βt hβ using fun s : T.OwnedSide i => P.exists_bottom_of_level (hxsu s)
  have htie : ∀ s : T.OwnedSide i, F.projection (xs s) =
      P.bottomBicollar (β s) (βh s) (P.bottomSigma (β s) (βh s) (βt s), 0) :=
    fun s => (hβ s).symm.trans (P.bottomSigma_spec _ _ (βt s) 0 le_rfl one_pos)
  choose δK hδK K hKs hKi hKb hKR hKlow hKtop using fun s : T.OwnedSide i =>
    exists_oldPortCollarPiece F D (T.sideCollar s.val) (hc₀src s) (hc₀b s) (hc₀own s)
      (P.bottomBicollar (β s) (βh s)) (P.bottomBicollar_spec _ _).1
      (P.bottomBicollar_spec _ _).2.2.1 ⟨_, xs s, htie s, hxsR s⟩
      (MobiusCore.bottomLift F P (β s) (βh s))
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
      (φ := fun r x => (MobiusCore.bottomLift F P (β s) (βh s)).flow r x)
      (fun x => (MobiusCore.bottomLift F P (β s) (βh s)).smooth.continuous.comp
        (continuous_id.prodMk continuous_const))
      (MobiusCore.bottomLift F P (β s) (βh s)).flow_zero
      (MobiusCore.bottomLift F P (β s) (βh s)).flow_add (hδK s) (hKtop s)
  have hKtopeq : ∀ s q, portHeight F D (K s q) = D.level 0 → q.2 = topPoint D := by
    rintro s ⟨p, r⟩ hq
    exact Subtype.ext (eq_top_of_portHeight (hKs s) (hKb s) (hRlow s) (hK0 s) hq)
  have hxsZ : ∀ s, F.projection (xs s) ∈ P.zeroSec (β s) := fun s => ⟨βt s, hβ s⟩
  have hΦU : ∀ j, ContMDiff ((SurfaceModel.model (P.pieces.base j).surface.kind).prod (𝓡 1))
      T.cutCarrier.model ∞ (Φ j) := fun j => (ContMDiff.subtypeVal_comp_iff _ _).mp (hΦs j)
  have hχU : ∀ m, ContMDiff mobiusBundleCarrier.{u}.model T.cutCarrier.model ∞ (χ m) :=
    fun m => (ContMDiff.subtypeVal_comp_iff _ _).mp (hχs m)
  have hZconn : ∀ w : P.pieces.Side, IsPreconnected (F.projection ⁻¹' P.zeroSec w) := by
    rintro (⟨j, l⟩ | m)
    · rw [← range_sideTorus_planar T i F P l (hΦπ j) (hΦr j)]
      exact isPreconnected_range (contMDiff_sideTorus _ _ (hΦU j)).continuous
    · rw [← hχz m]
      refine isPreconnected_range ((hχU m).continuous.comp ?_)
      exact mobiusExternalCollar.toOpenPartialHomeomorph.continuousOn.comp_continuous
        (continuous_id.prodMk continuous_const) fun t => by
          change (t, halfZero) ∈ mobiusExternalCollar.{u}.source
          rw [mobiusExternalCollar_source]
          exact zero_mem_halfCollarSource t
  have hsubR : ∀ s, Subtype.val '' (F.projection ⁻¹' P.zeroSec (β s)) ⊆
      connectedComponentIn (lowSet F D) (T.sideCollar s.val (1, halfZero)) := fun s =>
    image_val_subset_component (hZconn (β s)) (fun z hz => (P.level_of_mem_zeroSec (βh s) hz).le)
      (hxsZ s) (hxsR s)
  have hτ : ∀ s, range (fun p => K s (p, topPoint D)) = F.projection ⁻¹' P.zeroSec (β s) := by
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
      change F.projection (K s (p, topPoint D)) ∈ P.zeroSec (β s)
      rw [P.zeroSec_eq (βh s), (P.bottomBicollar_spec _ _).2.1]
      have hS : IsPreconnected (range fun p => F.projection (K s (p, topPoint D))) :=
        isPreconnected_range (F.projection.continuous.comp
          ((hKc s).comp (continuous_id.prodMk continuous_const)))
      have hmem0 : F.projection (xs s) ∈ connectedComponentIn (D.f ⁻¹' {D.level 0})
          (P.bottomPoint (β s) (βh s)) := by
        rw [← (P.bottomBicollar_spec _ _).2.1, ← P.zeroSec_eq (βh s)]
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
        exact P.level_of_mem_zeroSec (βh s) hz
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
  have hβinj : Injective β := by
    intro s s' he
    have hz : xs s ∈ F.projection ⁻¹' P.zeroSec (β s') := by
      rw [← he]
      exact hxsZ s
    exact hdist s s' (xs s) (hxsR s) (hsubR s' ⟨_, hz, rfl⟩)
  have hβsurj : ∀ w, P.IsBottom w → ∃ s, β s = w := by
    intro w h
    obtain ⟨z₀, hz₀⟩ := F.surjective (P.pieces.sidePt w (1, halfZero))
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
  have hne : Nonempty (P.pieces.PI ⊕ P.pieces.MI) := by
    obtain ⟨b, hb⟩ := D.exists_level_zero_lt
    obtain ⟨y, -⟩ := P.exists_pt_of_level hb.le
    exact ⟨P.pieces.piece y⟩
  have hΦbU : ∀ j q, Bijective (mfderiv ((SurfaceModel.model (P.pieces.base j).surface.kind).prod
      (𝓡 1)) T.cutCarrier.model (Φ j) q) := fun j q => by
    have h := hΦb j q
    rwa [DifferentialGeometry.mfderiv_subtypeVal_comp (Φ j) q] at h
  have hχbU : ∀ m q, Bijective (mfderiv mobiusBundleCarrier.{u}.model T.cutCarrier.model
      (χ m) q) := fun m q => by
    have h := hχb m q
    rwa [DifferentialGeometry.mfderiv_subtypeVal_comp (χ m) q] at h
  have hKU : ∀ s, ContMDiff (torusModel.prod (𝓡∂ 1)) T.cutCarrier.model ∞ (K s) := fun s =>
    (ContMDiff.subtypeVal_comp_iff _ _).mp (hKs s)
  have hKbU : ∀ s q, Bijective (mfderiv (torusModel.prod (𝓡∂ 1)) T.cutCarrier.model (K s) q) :=
    fun s q => by
      have h := hKb s q
      rwa [DifferentialGeometry.mfderiv_subtypeVal_comp (K s) q] at h
  obtain ⟨mP, hmP, hmPle⟩ := exists_pos_le_of_finite δP hδP
  obtain ⟨mM, hmM, hmMle⟩ := exists_pos_le_of_finite δM hδM
  obtain ⟨mK, hmK, hmKle⟩ := exists_pos_le_of_finite δK hδK
  set δ₀ := min (min (1 / 16) (D.level 0 / 10)) (min (min mP mM) mK) with hδ₀
  have hδP' : ∀ j, δ₀ ≤ δP j := fun j =>
    ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))).trans (hmPle j)
  have hδM' : ∀ m, δ₀ ≤ δM m := fun m =>
    ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))).trans (hmMle m)
  have hδK' : ∀ s, δ₀ ≤ δK s := fun s =>
    ((min_le_right _ _).trans (min_le_right _ _)).trans (hmKle s)
  exact ⟨{ Φ := Φ
           smoothΦ := hΦU
           bijΦ := hΦbU
           injΦ := hΦi
           projΦ := hΦπ
           rangeΦ := hΦr
           χ := χ
           smoothχ := hχU
           bijχ := hχbU
           injχ := hχi
           rangeχ := hχr
           zeroχ := hχz
           nonempty := hne
           δ₀ := δ₀
           δ₀_pos := by positivity
           δ₀_le_width := (min_le_left _ _).trans (min_le_left _ _)
           δ₀_le_level := (min_le_left _ _).trans (min_le_right _ _)
           cutSync := fun j l c b h t v s hs hs1 =>
             (hΦsync j).1 l c b h t v s hs (hs1.trans_le (hδP' j))
           bottomSync := fun j l h t v s hs hs1 =>
             (hΦsync j).2 l h t v s hs (hs1.trans_le (hδP' j))
           cutSyncχ := fun m c b h t s hs hs1 =>
             (hχsync m).1 c b h t s hs (hs1.trans_le (hδM' m))
           bottomSyncχ := fun m h t s hs hs1 =>
             (hχsync m).2 h t s hs (hs1.trans_le (hδM' m))
           β := β
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
