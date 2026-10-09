import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MixedSplitNativeSeams
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedAssembly

/-!
# The native mixed cut system of the capped manifold

Lane MS, tier MS4 (design `handoffs/20261004-design-ms-mixed-split.md` §3.3). The passive pieces,
the two capped solid tori, the sides and the seam charts of `MixedSplitNative*` form a
`MixedClosedSystem` of the capped manifold (`capSystem`). Covering (`capMap_covers`): a core
point lies on an old piece, which is passive or lies in the split region `V ∪ H`, covered by the
solid tori (`SideData.core_mem`); a cap point lies on a solid torus (`SideData.cap_mem`). Overlap
(`capMap_overlap`, lane N2c's `cappedMap_overlap`): two passive points with one image are equal
or glued along an old seam `≠ j`; a passive point on a solid torus is an old core point of
`V ∪ H` (`SideData.image`), hence again on a seam `≠ j`; two solid tori meet only on their
boundary tori (`SideData.boundary_of_eq`), which are host ports. Every old seam point `≠ j` read
through the core is a point of the corresponding seam chart (`capSeam_zero_of_seam`). Every actual
component of the capped manifold contains a piece (`exists_capPiece_comp`, from covering), so the
restriction `capComponentSystem` and its cut system `capCutSystem` exist on every component.
-/

set_option autoImplicit false

noncomputable section
open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.RelativeNormalization.MixedStage

open GC.Seifert.ElementaryPresentation (sideHeight)

variable {Q : ConnectedClosedOrientedManifold.{u} 3} {σ : MixedStage Q}
  {j : Fin σ.toTorus.pairing.count} {b : Bool} {h : σ.IsSplitSeam j b} {S : σ.SplitData h}
  {T : SphericalTubeSystem Q.toClosedOrientedManifold} {N : ClosedOrientedManifold.{u} 3}
  {K : SphericalCapping Q.toClosedOrientedManifold N T} {a : T.Index} {δ₂ : ℝ}
  (D : σ.SideData S K a δ₂) (hC : σ.CappedConditions S a δ₂)

theorem capSeam_zero_of_seam {d : Fin σ.toTorus.pairing.count} (hd : d ≠ j) (τ : Torus) :
    SplitTube.coreMap K (σ.toTorus.seam d (τ, 0)) =
      capSeam D hC ⟨d, hd⟩ ((sideTwist D d true).symm τ, 0) := by
  rw [capSeam_apply]
  change _ = SplitTube.coreMap K (σ.toTorus.seam d (sideTwist D d true
    ((sideTwist D d true).symm τ), δ₂ * 0))
  rw [Diffeomorph.apply_symm_apply, mul_zero]

theorem exists_capSeam_of_sideCollar {c : Fin σ.toTorus.pairing.count} (hc : c ≠ j) (β : Bool)
    (τ : Torus) : ∃ τ', SplitTube.coreMap K (σ.toTorus.cutMap (σ.toTorus.sideCollar
      (σ.seamSide c β) (τ, halfZero))) = capSeam D hC ⟨c, hc⟩ (τ', 0) := by
  have e := σ.cutMap_sideCollar_eq_seam c β τ 0 le_rfl one_pos
  have h0 : sideHeight β 0 = 0 := by cases β <;> simp [sideHeight]
  rw [h0] at e
  refine ⟨(sideTwist D c true).symm (σ.leftOfSide c β τ), ?_⟩
  rw [← capSeam_zero_of_seam D hC hc, ← e]
  rfl

theorem ne_of_mem_block {c : Fin σ.toTorus.pairing.count} {x : σ.toTorus.cutCarrier.Carrier}
    {k₀ : Fin σ.toTorus.components.count} (hk₀ : k₀ ≠ σ.seamPiece j b ∧ k₀ ≠ σ.hostPiece j b)
    (hx : x ∈ σ.toTorus.components.piece k₀)
    (hb : x ∈ σ.toTorus.pairing.gluing.left c ∨ x ∈ σ.toTorus.pairing.gluing.right c) :
    c ≠ j := by
  rintro rfl
  rcases hb with hb | hb
  · have := TorusPresentation.eq_of_mem_piece' _ (σ.toTorus.left_owned c hb) hx
    rcases seamPiece_eq_or (σ := σ) (b := b) c true with e | e
    · exact hk₀.1 (this.symm.trans e)
    · exact hk₀.2 (this.symm.trans e)
  · have := TorusPresentation.eq_of_mem_piece' _ (σ.toTorus.right_owned c hb) hx
    rcases seamPiece_eq_or (σ := σ) (b := b) c false with e | e
    · exact hk₀.1 (this.symm.trans e)
    · exact hk₀.2 (this.symm.trans e)

theorem exists_capSeam_of_cutMap_eq {k₀ : Fin σ.toTorus.components.count}
    (hk₀ : k₀ ≠ σ.seamPiece j b ∧ k₀ ≠ σ.hostPiece j b) {x y : σ.toTorus.cutCarrier.Carrier}
    (hx : x ∈ σ.toTorus.components.piece k₀) (hxy : x ≠ y)
    (he : σ.toTorus.cutMap x = σ.toTorus.cutMap y) :
    ∃ c t, SplitTube.coreMap K (σ.toTorus.cutMap x) = capSeam D hC c (t, 0) := by
  obtain ⟨d, τ, hτ, hb⟩ := σ.toTorus.exists_seam_of_cutMap_eq_of_ne hxy he
  have hd : d ≠ j := ne_of_mem_block hk₀ hx hb
  exact ⟨⟨d, hd⟩, _, by rw [hτ]; exact capSeam_zero_of_seam D hC hd τ⟩

theorem passive_eq_solid (k : {k : Fin σ.toTorus.components.count //
    k ≠ σ.seamPiece j b ∧ k ≠ σ.hostPiece j b}) (q : (capCut D hC).Piece k.1) (t : Bool)
    (q' : (discPlanarBase.{u} 1).surface.Carrier × Circle)
    (he : SplitTube.coreMap K (σ.toTorus.cutMap (passivePt D hC q)) = D.solid t q') :
    ∃ c τ, SplitTube.coreMap K (σ.toTorus.cutMap (passivePt D hC q)) = capSeam D hC c (τ, 0) := by
  obtain ⟨hcore, hne⟩ := passive_core D hC k q
  rcases D.image t q' with ⟨w, hw⟩ | ⟨y, hy, hycore, hyq⟩
  · rw [hw, SplitTube.coreMap_of_mem K hcore] at he
    exact absurd he (SplitTube.coreInclusion_ne_cap_of_forall_ne K ⟨_, hcore⟩ hne _ w)
  · rw [hyq] at he
    have hcut := SplitTube.coreMap_injOn K hcore hycore he
    have hxy : passivePt D hC q ≠ y := by
      intro hxy
      have hk := passivePt_mem D hC q
      rw [hxy] at hk
      rcases hy with hy | hy
      · exact k.2.1 (TorusPresentation.eq_of_mem_piece' _ hk hy)
      · exact k.2.2 (TorusPresentation.eq_of_mem_piece' _ hk hy)
    exact exists_capSeam_of_cutMap_eq D hC k.2 (passivePt_mem D hC q) hxy hcut

theorem solid_boundary_seam (t : Bool) (p : Torus) :
    ∃ c τ, D.solid t ((discPlanarBase.{u} 1).collar 0 (p.1, halfZero), p.2) =
      capSeam D hC c (τ, 0) := by
  have hlt : δ₂ * 0 < S.δ := by rw [mul_zero]; exact S.hδ
  rw [show halfZero = halfPoint 0 le_rfl from rfl, D.collar t p 0 le_rfl one_pos,
    ← σ.cutMap_sideCollar_hostPort S _ _ (by rw [mul_zero]) hlt (by rw [mul_zero]; exact one_pos)]
  obtain ⟨c, β, hcβ⟩ := σ.exists_seamSide_eq
    (σ.standardPort (σ.hostPiece j b) (σ.hostPiece_not_frozen h) h.2.2.1 (D.port t)).val
  have hc : c ≠ j := by
    rintro rfl
    exact standardPort_port_ne_seamSide D t β hcβ.symm
  obtain ⟨τ, hτ⟩ := exists_capSeam_of_sideCollar D hC hc β (D.holonomy t p)
  refine ⟨⟨c, hc⟩, τ, ?_⟩
  rw [← hcβ, halfPoint_congr (mul_nonneg hC.pos.le le_rfl) le_rfl (mul_zero δ₂)]
  exact hτ

theorem capMap_overlap : ∀ (i i' : CapPiece σ j b) (q : capPart D hC i) (q' : capPart D hC i'),
    capMap D hC i q = capMap D hC i' q' →
      (⟨i, q⟩ : Σ i, capPart D hC i) = ⟨i', q'⟩ ∨ ∃ c t, capMap D hC i q = capSeam D hC c (t, 0)
  | .inl k, .inl k', q, q', he => by
    change SplitTube.coreMap K (σ.toTorus.cutMap (passivePt D hC q)) =
      SplitTube.coreMap K (σ.toTorus.cutMap (passivePt D hC q')) at he
    have hcut := SplitTube.coreMap_injOn K (passive_core D hC k q).1
      (passive_core D hC k' q').1 he
    by_cases hxy : passivePt D hC q = passivePt D hC q'
    · left
      have hk : k = k' := Subtype.ext (TorusPresentation.eq_of_mem_piece' _
        (passivePt_mem D hC q) (hxy ▸ passivePt_mem D hC q'))
      subst hk
      have hq : q = q' := Subtype.ext hxy
      subst hq
      rfl
    · exact Or.inr (exists_capSeam_of_cutMap_eq D hC k.2 (passivePt_mem D hC q) hxy hcut)
  | .inl k, .inr t, q, q', he => Or.inr (passive_eq_solid D hC k q t _ he)
  | .inr t, .inl k, q, q', he => by
    right
    obtain ⟨c, τ, hc⟩ := passive_eq_solid D hC k q' t _ he.symm
    exact ⟨c, τ, he.trans hc⟩
  | .inr t, .inr t', q, q', he => by
    change D.solid t (discTheta.symm q) = D.solid t' (discTheta.symm q') at he
    by_cases htt : t = t'
    · subst htt
      left
      have hq := discTheta.symm.injective (D.injective t he)
      subst hq
      rfl
    · right
      have hfb : (t = false ∧ t' = true) ∨ (t = true ∧ t' = false) := by
        cases t <;> cases t' <;> simp_all
      change ∃ c τ, D.solid t (discTheta.symm q) = capSeam D hC c (τ, 0)
      rcases hfb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · obtain ⟨⟨p, hp⟩, -⟩ := D.boundary_of_eq _ _ he
        rw [hp]
        exact solid_boundary_seam D hC false p
      · obtain ⟨-, ⟨p, hp⟩⟩ := D.boundary_of_eq _ _ he.symm
        rw [hp]
        exact solid_boundary_seam D hC true p

theorem capMap_covers : ⋃ i, range (capMap D hC i) = univ := by
  refine eq_univ_of_forall fun x => ?_
  have hx : x ∈ range K.coreInclusion ∪ ⋃ b', range (K.cap b') := K.exhaustive ▸ mem_univ x
  rcases hx with ⟨y, rfl⟩ | hx
  · have hy : y.val ∈ ⋃ k, range fun z : σ.toTorus.components.piece k =>
        σ.toTorus.cutMap z.val := σ.toTorus.covers_cutMap ▸ mem_univ y.val
    obtain ⟨k, z, hz⟩ := mem_iUnion.mp hy
    have hz : σ.toTorus.cutMap z.val = y.val := hz
    by_cases hk : k = σ.seamPiece j b ∨ k = σ.hostPiece j b
    · have hreg : σ.InSplitRegion (j := j) (b := b) z.val := by
        rcases hk with rfl | rfl
        · exact Or.inl z.2
        · exact Or.inr z.2
      obtain ⟨t, q, hq⟩ := D.core_mem z.val hreg (by rw [hz]; exact y.2)
      refine mem_iUnion.mpr ⟨.inr t, discTheta q, ?_⟩
      change D.solid t (discTheta.symm (discTheta q)) = _
      rw [Diffeomorph.symm_apply_apply, hq, hz, SplitTube.coreMap_val]
    · push Not at hk
      refine mem_iUnion.mpr ⟨.inl ⟨k, hk⟩, (z : (capCut D hC).Piece k), ?_⟩
      change SplitTube.coreMap K (σ.toTorus.cutMap z.val) = _
      rw [hz, SplitTube.coreMap_val]
  · obtain ⟨⟨a', t'⟩, w, rfl⟩ := mem_iUnion.mp hx
    obtain rfl := hC.index a'
    obtain ⟨q, hq⟩ := D.cap_mem t' w
    refine mem_iUnion.mpr ⟨.inr t', discTheta q, ?_⟩
    change D.solid t' (discTheta.symm (discTheta q)) = _
    rw [Diffeomorph.symm_apply_apply, hq]

def capSystem : MixedClosedSystem.{u} N.Carrier .withBoundary where
  Piece := CapPiece σ j b
  Seam := CapSeam σ j
  nonempty := ⟨.inr true⟩
  Part := capPart D hC
  map := capMap D hC
  smooth := capMap_smooth D hC
  mfderiv_bijective := capMap_mfderiv_bijective D hC
  covers := capMap_covers D hC
  torusCount := capTorusCount D hC
  collar := capCollar D hC
  collar_source := capCollar_source D hC
  collar_disjoint := capCollar_disjoint D hC
  boundary_exhausted := capCollar_boundary_exhausted D hC
  side := capSide D hC
  side_bijective := capSide_bijective D hC
  matching := capMatching D hC
  seam := capSeam D hC
  seam_source := capSeam_source D hC
  seam_neg := capSeam_neg D hC
  seam_pos := capSeam_pos D hC
  overlap := capMap_overlap D hC

theorem exists_capPiece_comp (c : ConnectedComponents N.Carrier) :
    ∃ i, (capSystem D hC).pieceComp i = c := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  obtain ⟨i, q, hq⟩ := mem_iUnion.mp ((capSystem D hC).covers ▸ mem_univ x :
    x ∈ ⋃ i, range ((capSystem D hC).map i))
  exact ⟨i, by rw [← (capSystem D hC).mk_map i q, hq]⟩

def capComponentSystem (c : ConnectedComponents N.Carrier) :
    MixedClosedSystem.{u} (N.component c).Carrier .withBoundary :=
  (capSystem D hC).restrict c (exists_capPiece_comp D hC c)

def capCutSystem (c : ConnectedComponents N.Carrier) :
    EmbeddedCutSystem (NoCuts.carrier (N.component c)) .withBoundary :=
  (capComponentSystem D hC c).toCutSystem

end GC.Seifert.RelativeNormalization.MixedStage
