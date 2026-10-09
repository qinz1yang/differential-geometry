import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.Elementary

/-!
# Circle bundles over a disc

Chapter 6, lane RG01a: the disc case of RG01′ (`CircleBundlesOverPlanarBasesStandard`,
`Seifert/Elementary.lean`), in the form the Morse decomposition outputs, plus two reductions.

(1) Disc pieces. A chart domain `neighborhood b` of a `CircleFibration` is a neighbourhood of `b`
(`neighborhood_mem_nhds`), so a small disc piece around an extremum `b` lies in it. For such a
piece `ι : P → base`, `P : PlanarBase 1` smoothly embedded with `range ι ⊆ neighborhood b`,
`discPieceChart` `(z, t) ↦ τ_b⁻¹(ι z, t)` is a smooth closed embedding `P × S¹ → U` over `ι` onto
`π⁻¹(range ι)` (`exists_discPieceTrivialization`), and `restrictTrivialization` restricts `τ_b` to
any open set of the base inside its domain. If the domain is the whole base,
`productOfGlobalTrivialization` is a product `U ≃ base × S¹` over the projection.

(2) The global disc statement. `CircleBundlesOverDiscStandard` is the `k = 1` clause of RG01′
(`circleBundlesOverDiscStandard_of_planarBases`); by `circleBundlesOverDiscStandard_iff` it says
that every circle fibration over a base diffeomorphic to a `PlanarBase 1` `IsGloballyTrivial`.
A `PrincipalAtlas` is a finite atlas whose transitions are rotations `τᵢ = gᵢⱼ · τⱼ`; the `gᵢⱼ`
are smooth cocycles (`transition_smooth`, `transition_cocycle`). A smooth coboundary
`gᵢⱼ = hᵢ hⱼ⁻¹` glues the charts `τᵢ · hᵢ⁻¹` to `productOfCoboundary`, and a smooth section `s`
gives `hᵢ = τᵢ ∘ s` (`isGloballyTrivial_iff_exists_section`). `DiscCircleCocycleTrivial` (finite
smooth circle-valued Čech cocycles on a disc are smooth coboundaries) is a classical input not
proved here; under it the disc statement is equivalent to the existence of principal atlases
(`circleBundlesOverDiscStandard_iff_principalAtlas`, with `PrincipalAtlas.ofProduct`).

(3) `SolidTorusPiece T i` is `ProductFibredPiece T i 1` by definition (`solidTorusPiece_eq`), the
fibration of every product piece is globally trivial, and a product over a `PlanarBase 1` whose
port collar is matched is a solid torus piece (`solidTorusPieceOfProduct`) whose fibration is the
given one through the base diffeomorphism (`solidTorusPieceOfProduct_globalChart_projection`).
-/

set_option autoImplicit false

noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

variable {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier}

def CircleFibration.IsGloballyTrivial (F : CircleFibration C U) : Prop :=
  ∃ Φ : U ≃ₘ⟮C.model, (SurfaceModel.model F.base.kind).prod (𝓡 1)⟯ F.base.Carrier × Circle,
    ∀ x, (Φ x).1 = F.projection x

def CircleFibration.productOfGlobalTrivialization (F : CircleFibration C U)
    (b : F.base.Carrier) (hb : ∀ y, y ∈ F.neighborhood b) :
    U ≃ₘ⟮C.model, (SurfaceModel.model F.base.kind).prod (𝓡 1)⟯ F.base.Carrier × Circle :=
  (openDiffeomorphOfForall (TopologicalSpace.Opens.comap F.projection (F.neighborhood b))
      (fun x => hb (F.projection x))).symm.trans
    ((F.trivialization b).trans ((openDiffeomorphOfForall (F.neighborhood b) hb).prodCongr
      (Diffeomorph.refl (𝓡 1) Circle ∞)))

theorem CircleFibration.productOfGlobalTrivialization_fst (F : CircleFibration C U)
    (b : F.base.Carrier) (hb : ∀ y, y ∈ F.neighborhood b) (x : U) :
    (CircleFibration.productOfGlobalTrivialization F b hb x).1 = F.projection x :=
  F.projection_trivialization b _

theorem CircleFibration.neighborhood_mem_nhds (F : CircleFibration C U) (b : F.base.Carrier) :
    (F.neighborhood b : Set F.base.Carrier) ∈ 𝓝 b :=
  (F.neighborhood b).isOpen.mem_nhds (F.mem_neighborhood b)

theorem CircleFibration.projection_trivialization_symm (F : CircleFibration C U)
    (b : F.base.Carrier) (q : F.neighborhood b × Circle) :
    F.projection ((F.trivialization b).symm q).val = q.1.val := by
  rw [← F.projection_trivialization, Diffeomorph.apply_symm_apply]

def CircleFibration.restrictTrivialization (F : CircleFibration C U) (b : F.base.Carrier)
    (V : TopologicalSpace.Opens F.base.Carrier) (hV : V ≤ F.neighborhood b) :
    TopologicalSpace.Opens.comap F.projection V ≃ₘ⟮C.model,
      (SurfaceModel.model F.base.kind).prod (𝓡 1)⟯ (V × Circle) where
  toFun x := (⟨(F.trivialization b (TopologicalSpace.Opens.inclusion
      (TopologicalSpace.Opens.comap_mono F.projection hV) x)).1.val, by
        rw [F.projection_trivialization]
        exact x.2⟩,
    (F.trivialization b (TopologicalSpace.Opens.inclusion
      (TopologicalSpace.Opens.comap_mono F.projection hV) x)).2)
  invFun q := ⟨((F.trivialization b).symm (TopologicalSpace.Opens.inclusion hV q.1, q.2)).val, by
    change F.projection _ ∈ V
    rw [CircleFibration.projection_trivialization_symm F]
    exact q.1.2⟩
  left_inv x := by
    apply Subtype.ext
    dsimp only
    have h : ((TopologicalSpace.Opens.inclusion hV ⟨(F.trivialization b
        (TopologicalSpace.Opens.inclusion (TopologicalSpace.Opens.comap_mono F.projection hV)
          x)).1.val, by rw [F.projection_trivialization]; exact x.2⟩ : F.neighborhood b),
        (F.trivialization b (TopologicalSpace.Opens.inclusion
          (TopologicalSpace.Opens.comap_mono F.projection hV) x)).2) =
        F.trivialization b (TopologicalSpace.Opens.inclusion
          (TopologicalSpace.Opens.comap_mono F.projection hV) x) := rfl
    rw [h, Diffeomorph.symm_apply_apply]
  right_inv q := by
    have h : TopologicalSpace.Opens.inclusion (TopologicalSpace.Opens.comap_mono F.projection hV)
        ⟨((F.trivialization b).symm (TopologicalSpace.Opens.inclusion hV q.1, q.2)).val, by
          change F.projection _ ∈ V
          rw [CircleFibration.projection_trivialization_symm F]
          exact q.1.2⟩ =
        (F.trivialization b).symm (TopologicalSpace.Opens.inclusion hV q.1, q.2) := rfl
    simp only [h, Diffeomorph.apply_symm_apply]
  contMDiff_toFun := by
    have hc := (F.trivialization b).contMDiff.comp
      (contMDiff_inclusion (I := C.model) (TopologicalSpace.Opens.comap_mono F.projection hV))
    refine ContMDiff.prodMk ?_ (contMDiff_snd.comp hc)
    apply (ContMDiff.subtypeVal_comp_iff V _).mp
    have h : ContMDiff C.model (SurfaceModel.model F.base.kind) ∞
        (fun x => (F.trivialization b (TopologicalSpace.Opens.inclusion
          (TopologicalSpace.Opens.comap_mono F.projection hV) x)).1.val) :=
      contMDiff_subtype_val.comp (contMDiff_fst.comp hc)
    exact h
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff _ _).mp
    have h : ContMDiff ((SurfaceModel.model F.base.kind).prod (𝓡 1)) C.model ∞
        (fun q : V × Circle =>
          ((F.trivialization b).symm (TopologicalSpace.Opens.inclusion hV q.1, q.2)).val) :=
      contMDiff_subtype_val.comp ((F.trivialization b).symm.contMDiff.comp
        (((contMDiff_inclusion hV).comp contMDiff_fst).prodMk contMDiff_snd))
    exact h

theorem CircleFibration.restrictTrivialization_fst (F : CircleFibration C U)
    (b : F.base.Carrier) (V : TopologicalSpace.Opens F.base.Carrier) (hV : V ≤ F.neighborhood b)
    (x : TopologicalSpace.Opens.comap F.projection V) :
    (CircleFibration.restrictTrivialization F b V hV x).1.val = F.projection x.val :=
  F.projection_trivialization b _

def CircleFibration.discPieceChart (F : CircleFibration C U) (b : F.base.Carrier) {Q : Type*}
    (ι : Q → F.base.Carrier) (hι : ∀ z, ι z ∈ F.neighborhood b) (q : Q × Circle) : U :=
  ((F.trivialization b).symm (⟨ι q.1, hι q.1⟩, q.2)).val

section DiscPiece

variable (F : CircleFibration C U) (b : F.base.Carrier) {Q : Type*} (ι : Q → F.base.Carrier)
  (hι : ∀ z, ι z ∈ F.neighborhood b)

theorem CircleFibration.projection_discPieceChart (q : Q × Circle) :
    F.projection (CircleFibration.discPieceChart F b ι hι q) = ι q.1 :=
  CircleFibration.projection_trivialization_symm F b _

theorem CircleFibration.discPieceChart_injective (hinj : Function.Injective ι) :
    Function.Injective (CircleFibration.discPieceChart F b ι hι) := by
  intro q q' h
  obtain ⟨h1, h2⟩ := Prod.mk.inj ((F.trivialization b).symm.injective (Subtype.ext h))
  exact Prod.ext (hinj (congrArg Subtype.val h1)) h2

theorem CircleFibration.range_discPieceChart :
    range (CircleFibration.discPieceChart F b ι hι) = F.projection ⁻¹' range ι := by
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨q.1, (CircleFibration.projection_discPieceChart F b ι hι q).symm⟩
  · rintro ⟨z, hz⟩
    have hx : F.projection x ∈ F.neighborhood b := by
      rw [← hz]
      exact hι z
    refine ⟨(z, (F.trivialization b ⟨x, hx⟩).2), ?_⟩
    have h : ((⟨ι z, hι z⟩ : F.neighborhood b), (F.trivialization b ⟨x, hx⟩).2) =
        F.trivialization b ⟨x, hx⟩ :=
      Prod.ext (Subtype.ext (hz.trans (F.projection_trivialization b ⟨x, hx⟩).symm)) rfl
    change ((F.trivialization b).symm (_, _)).val = x
    rw [h, Diffeomorph.symm_apply_apply]

variable {EQ HQ : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [TopologicalSpace HQ]
  {IQ : ModelWithCorners ℝ EQ HQ} [TopologicalSpace Q] [ChartedSpace HQ Q]

theorem CircleFibration.contMDiff_discPieceChart
    (hs : ContMDiff IQ (SurfaceModel.model F.base.kind) ∞ ι) :
    ContMDiff (IQ.prod (𝓡 1)) C.model ∞ (CircleFibration.discPieceChart F b ι hι) := by
  have h1 : ContMDiff IQ (SurfaceModel.model F.base.kind) ∞
      (fun z => (⟨ι z, hι z⟩ : F.neighborhood b)) :=
    (ContMDiff.subtypeVal_comp_iff (F.neighborhood b) _).mp hs
  exact contMDiff_subtype_val.comp ((F.trivialization b).symm.contMDiff.comp
    ((h1.comp contMDiff_fst).prodMk contMDiff_snd))

theorem CircleFibration.isClosedEmbedding_discPieceChart [CompactSpace Q]
    (hs : ContMDiff IQ (SurfaceModel.model F.base.kind) ∞ ι) (hinj : Function.Injective ι) :
    _root_.Topology.IsClosedEmbedding (CircleFibration.discPieceChart F b ι hι) :=
  (CircleFibration.contMDiff_discPieceChart F b ι hι hs).continuous.isClosedEmbedding
    (CircleFibration.discPieceChart_injective F b ι hι hinj)

end DiscPiece

theorem CircleFibration.exists_discPieceTrivialization (F : CircleFibration C U)
    (P : PlanarBase.{u} 1) (ι : P.surface.Carrier → F.base.Carrier)
    (hι : Manifold.IsSmoothEmbedding (SurfaceModel.model P.surface.kind)
      (SurfaceModel.model F.base.kind) ∞ ι)
    (b : F.base.Carrier) (hb : range ι ⊆ F.neighborhood b) :
    ∃ Ψ : P.surface.Carrier × Circle → U,
      ContMDiff ((SurfaceModel.model P.surface.kind).prod (𝓡 1)) C.model ∞ Ψ ∧
        _root_.Topology.IsClosedEmbedding Ψ ∧ (∀ q, F.projection (Ψ q) = ι q.1) ∧
          range Ψ = F.projection ⁻¹' range ι ∧
            ∀ q, Ψ q = ((F.trivialization b).symm (⟨ι q.1, hb ⟨q.1, rfl⟩⟩, q.2)).val :=
  ⟨CircleFibration.discPieceChart F b ι fun z => hb ⟨z, rfl⟩,
    CircleFibration.contMDiff_discPieceChart F b ι _ hι.contMDiff,
    CircleFibration.isClosedEmbedding_discPieceChart F b ι _ hι.contMDiff hι.isEmbedding.injective,
    CircleFibration.projection_discPieceChart F b ι _,
    CircleFibration.range_discPieceChart F b ι _, fun _ => rfl⟩

theorem CircleFibration.isGloballyTrivial_of_forall_mem (F : CircleFibration C U)
    (b : F.base.Carrier) (hb : ∀ y, y ∈ F.neighborhood b) : CircleFibration.IsGloballyTrivial F :=
  ⟨CircleFibration.productOfGlobalTrivialization F b hb,
    CircleFibration.productOfGlobalTrivialization_fst F b hb⟩

theorem CircleFibration.exists_product_of_isGloballyTrivial {F : CircleFibration C U}
    (hF : CircleFibration.IsGloballyTrivial F) {k : ℕ} (P : PlanarBase.{u} k)
    (e : F.base.Carrier ≃ₘ⟮SurfaceModel.model F.base.kind,
      SurfaceModel.model P.surface.kind⟯ P.surface.Carrier) :
    ∃ Φ : U ≃ₘ⟮C.model, (SurfaceModel.model P.surface.kind).prod (𝓡 1)⟯
      P.surface.Carrier × Circle, ∀ x, (Φ x).1 = e (F.projection x) := by
  obtain ⟨Φ, hΦ⟩ := hF
  exact ⟨Φ.trans (e.prodCongr (Diffeomorph.refl (𝓡 1) Circle ∞)),
    fun x => congrArg e (hΦ x)⟩

theorem CircleFibration.isGloballyTrivial_of_exists_product (F : CircleFibration C U) {k : ℕ}
    (P : PlanarBase.{u} k) (e : F.base.Carrier ≃ₘ⟮SurfaceModel.model F.base.kind,
      SurfaceModel.model P.surface.kind⟯ P.surface.Carrier)
    (h : ∃ Φ : U ≃ₘ⟮C.model, (SurfaceModel.model P.surface.kind).prod (𝓡 1)⟯
      P.surface.Carrier × Circle, ∀ x, (Φ x).1 = e (F.projection x)) :
    CircleFibration.IsGloballyTrivial F := by
  obtain ⟨Φ, hΦ⟩ := h
  refine ⟨Φ.trans (e.symm.prodCongr (Diffeomorph.refl (𝓡 1) Circle ∞)), fun x => ?_⟩
  change e.symm (Φ x).1 = F.projection x
  rw [hΦ, Diffeomorph.symm_apply_apply]

def CircleBundlesOverDiscStandard : Prop :=
  ∀ (C : CompactCarrier.{u}) (U : TopologicalSpace.Opens C.Carrier) (F : CircleFibration C U)
    (P : PlanarBase.{u} 1) (e : F.base.Carrier ≃ₘ⟮SurfaceModel.model F.base.kind,
      SurfaceModel.model P.surface.kind⟯ P.surface.Carrier),
    ∃ Φ : U ≃ₘ⟮C.model, (SurfaceModel.model P.surface.kind).prod (𝓡 1)⟯
      P.surface.Carrier × Circle, ∀ x, (Φ x).1 = e (F.projection x)

theorem circleBundlesOverDiscStandard_of_planarBases
    (h : CircleBundlesOverPlanarBasesStandard.{u}) : CircleBundlesOverDiscStandard.{u} :=
  fun C U F P e => (h C U F).1 1 (by simp) P e

theorem circleBundlesOverDiscStandard_iff : CircleBundlesOverDiscStandard.{u} ↔
    ∀ (C : CompactCarrier.{u}) (U : TopologicalSpace.Opens C.Carrier) (F : CircleFibration C U)
      (P : PlanarBase.{u} 1), Nonempty (F.base.Carrier ≃ₘ⟮SurfaceModel.model F.base.kind,
        SurfaceModel.model P.surface.kind⟯ P.surface.Carrier) →
      CircleFibration.IsGloballyTrivial F :=
  ⟨fun h C U F P ⟨e⟩ => CircleFibration.isGloballyTrivial_of_exists_product F P e (h C U F P e),
    fun h C U F P e => CircleFibration.exists_product_of_isGloballyTrivial (h C U F P ⟨e⟩) P e⟩

structure PrincipalAtlas (F : CircleFibration C U) where
  count : ℕ
  domain : Fin count → TopologicalSpace.Opens F.base.Carrier
  covers : ∀ y, ∃ i, y ∈ domain i
  chart : (i : Fin count) → TopologicalSpace.Opens.comap F.projection (domain i) ≃ₘ⟮C.model,
    (SurfaceModel.model F.base.kind).prod (𝓡 1)⟯ (domain i × Circle)
  chart_fst : ∀ i x, ((chart i x).1).val = F.projection x.val
  transition : Fin count → Fin count → F.base.Carrier → Circle
  chart_snd : ∀ i j (x : U) (hi : F.projection x ∈ domain i) (hj : F.projection x ∈ domain j),
    (chart i ⟨x, hi⟩).2 = transition i j (F.projection x) * (chart j ⟨x, hj⟩).2

def DiscCircleCocycleTrivial : Prop :=
  ∀ (B : CompactSurface.{u}) (P : PlanarBase.{u} 1), Nonempty (B.Carrier ≃ₘ⟮SurfaceModel.model
      B.kind, SurfaceModel.model P.surface.kind⟯ P.surface.Carrier) →
    ∀ (n : ℕ) (V : Fin n → TopologicalSpace.Opens B.Carrier), (∀ y, ∃ i, y ∈ V i) →
    ∀ g : Fin n → Fin n → B.Carrier → Circle,
      (∀ i j, ContMDiffOn (SurfaceModel.model B.kind) (𝓡 1) ∞ (g i j) (V i ∩ V j)) →
      (∀ i j k y, y ∈ V i → y ∈ V j → y ∈ V k → g i j y * g j k y = g i k y) →
      ∃ h : Fin n → B.Carrier → Circle,
        (∀ i, ContMDiffOn (SurfaceModel.model B.kind) (𝓡 1) ∞ (h i) (V i)) ∧
          ∀ i j y, y ∈ V i → y ∈ V j → g i j y = h i y * (h j y)⁻¹

namespace PrincipalAtlas

variable {F : CircleFibration C U} (A : PrincipalAtlas F)

theorem projection_chart_symm (i : Fin A.count) (q : A.domain i × Circle) :
    F.projection ((A.chart i).symm q).val = q.1.val := by
  rw [← A.chart_fst, Diffeomorph.apply_symm_apply]

theorem chart_mk (i : Fin A.count) (x : U) (hi : F.projection x ∈ A.domain i) :
    A.chart i ⟨x, hi⟩ = (⟨F.projection x, hi⟩, (A.chart i ⟨x, hi⟩).2) :=
  Prod.ext (Subtype.ext (A.chart_fst i _)) rfl

theorem transition_eq (i j : Fin A.count) (x : U) (hi : F.projection x ∈ A.domain i)
    (hj : F.projection x ∈ A.domain j) :
    A.transition i j (F.projection x) = (A.chart i ⟨x, hi⟩).2 * ((A.chart j ⟨x, hj⟩).2)⁻¹ := by
  rw [A.chart_snd i j x hi hj, mul_inv_cancel_right]

theorem transition_cocycle (i j k : Fin A.count) (y : F.base.Carrier) (hi : y ∈ A.domain i)
    (hj : y ∈ A.domain j) (hk : y ∈ A.domain k) :
    A.transition i j y * A.transition j k y = A.transition i k y := by
  obtain ⟨x, rfl⟩ := F.surjective y
  apply mul_right_cancel (b := (A.chart k ⟨x, hk⟩).2)
  rw [mul_assoc, ← A.chart_snd j k x hj hk, ← A.chart_snd i j x hi hj,
    ← A.chart_snd i k x hi hk]

theorem transition_smooth (i j : Fin A.count) :
    ContMDiffOn (SurfaceModel.model F.base.kind) (𝓡 1) ∞ (A.transition i j)
      (A.domain i ∩ A.domain j) := by
  intro y hy
  let W : TopologicalSpace.Opens F.base.Carrier := A.domain i ⊓ A.domain j
  have hWj : W ≤ A.domain j := inf_le_right
  let σ : W → TopologicalSpace.Opens.comap F.projection (A.domain i) := fun w =>
    ⟨((A.chart j).symm (TopologicalSpace.Opens.inclusion hWj w, 1)).val, by
      change F.projection _ ∈ A.domain i
      rw [A.projection_chart_symm]
      exact w.2.1⟩
  have hσ : ContMDiff (SurfaceModel.model F.base.kind) C.model ∞ σ := by
    apply (ContMDiff.subtypeVal_comp_iff _ σ).mp
    have h : ContMDiff (SurfaceModel.model F.base.kind) C.model ∞
        (fun w : W => ((A.chart j).symm (TopologicalSpace.Opens.inclusion hWj w, 1)).val) :=
      contMDiff_subtype_val.comp ((A.chart j).symm.contMDiff.comp
        ((contMDiff_inclusion hWj).prodMk contMDiff_const))
    exact h
  have heq : (fun w : W => A.transition i j w) = fun w => (A.chart i (σ w)).2 := by
    funext w
    have hw : F.projection (σ w).val = w.val := A.projection_chart_symm j _
    have hj : F.projection (σ w).val ∈ A.domain j := by
      rw [hw]
      exact w.2.2
    have h1 := A.transition_eq i j (σ w).val (σ w).2 hj
    have h2 : (A.chart j ⟨(σ w).val, hj⟩).2 = 1 := by
      have h3 : (⟨(σ w).val, hj⟩ : TopologicalSpace.Opens.comap F.projection (A.domain j)) =
          (A.chart j).symm (TopologicalSpace.Opens.inclusion hWj w, 1) := Subtype.ext rfl
      rw [h3, Diffeomorph.apply_symm_apply]
    rw [h2, inv_one, mul_one, hw] at h1
    exact h1
  have hW : ContMDiffAt (SurfaceModel.model F.base.kind) (𝓡 1) ∞
      (fun w : W => A.transition i j w) ⟨y, hy⟩ := by
    rw [heq]
    exact (contMDiff_snd.comp ((A.chart i).contMDiff.comp hσ)).contMDiffAt
  exact (contMDiffAt_subtype_iff.mp hW).contMDiffWithinAt

def index (y : F.base.Carrier) : Fin A.count := Classical.choose (A.covers y)

theorem index_mem (y : F.base.Carrier) : y ∈ A.domain (A.index y) :=
  Classical.choose_spec (A.covers y)

variable (h : Fin A.count → F.base.Carrier → Circle)

def productMap (x : U) : F.base.Carrier × Circle :=
  (F.projection x, (A.chart (A.index (F.projection x)) ⟨x, A.index_mem _⟩).2 *
    (h (A.index (F.projection x)) (F.projection x))⁻¹)

def productInv (p : F.base.Carrier × Circle) : U :=
  ((A.chart (A.index p.1)).symm (⟨p.1, A.index_mem p.1⟩, p.2 * h (A.index p.1) p.1)).val

theorem productInv_productMap (x : U) : A.productInv h (A.productMap h x) = x := by
  unfold productInv productMap
  dsimp only
  rw [inv_mul_cancel_right, ← A.chart_mk, Diffeomorph.symm_apply_apply]

variable {h}
variable (hcob : ∀ i j y, y ∈ A.domain i → y ∈ A.domain j →
  A.transition i j y = h i y * (h j y)⁻¹)
include hcob

theorem productMap_eq (x : U) (i : Fin A.count) (hi : F.projection x ∈ A.domain i) :
    A.productMap h x = (F.projection x, (A.chart i ⟨x, hi⟩).2 * (h i (F.projection x))⁻¹) := by
  unfold productMap
  refine Prod.ext rfl ?_
  dsimp only
  rw [A.chart_snd _ i x (A.index_mem _) hi, hcob _ i _ (A.index_mem _) hi, mul_right_comm,
    mul_right_comm (h _ _), mul_inv_cancel, one_mul, mul_comm]

theorem productInv_eq (p : F.base.Carrier × Circle) (i : Fin A.count) (hi : p.1 ∈ A.domain i) :
    A.productInv h p = ((A.chart i).symm (⟨p.1, hi⟩, p.2 * h i p.1)).val := by
  let x := (A.chart (A.index p.1)).symm (⟨p.1, A.index_mem p.1⟩, p.2 * h (A.index p.1) p.1)
  have hx : F.projection x.val = p.1 := A.projection_chart_symm _ _
  have hxi : F.projection x.val ∈ A.domain i := by
    rw [hx]
    exact hi
  have hxk : (A.chart (A.index p.1) ⟨x.val, x.2⟩).2 = p.2 * h (A.index p.1) p.1 := by
    rw [Subtype.coe_eta, Diffeomorph.apply_symm_apply]
  have hc : A.chart i ⟨x.val, hxi⟩ = (⟨p.1, hi⟩, p.2 * h i p.1) := by
    rw [A.chart_mk]
    refine Prod.ext (Subtype.ext hx) ?_
    dsimp only
    rw [A.chart_snd i (A.index p.1) x.val hxi x.2, hxk, hcob i _ _ hxi x.2, hx,
      mul_comm p.2, ← mul_assoc, inv_mul_cancel_right, mul_comm]
  have hy : (⟨x.val, hxi⟩ : TopologicalSpace.Opens.comap F.projection (A.domain i)) =
      (A.chart i).symm (⟨p.1, hi⟩, p.2 * h i p.1) := by
    rw [← hc, Diffeomorph.symm_apply_apply]
  exact congrArg Subtype.val hy

theorem productMap_productInv (p : F.base.Carrier × Circle) :
    A.productMap h (A.productInv h p) = p := by
  let x := (A.chart (A.index p.1)).symm (⟨p.1, A.index_mem p.1⟩, p.2 * h (A.index p.1) p.1)
  have hx : F.projection x.val = p.1 := A.projection_chart_symm _ _
  change A.productMap h x.val = p
  rw [A.productMap_eq hcob x.val (A.index p.1) x.2, Subtype.coe_eta, Diffeomorph.apply_symm_apply,
    hx]
  exact Prod.ext rfl (mul_inv_cancel_right _ _)

variable (hh : ∀ i, ContMDiffOn (SurfaceModel.model F.base.kind) (𝓡 1) ∞ (h i) (A.domain i))
include hh

omit hcob in
theorem contMDiff_restrict (i : Fin A.count) :
    ContMDiff (SurfaceModel.model F.base.kind) (𝓡 1) ∞ (fun v : A.domain i => h i v) :=
  fun v => contMDiffAt_subtype_iff.mpr
    ((hh i v v.2).contMDiffAt ((A.domain i).isOpen.mem_nhds v.2))

theorem contMDiff_productMap :
    ContMDiff C.model ((SurfaceModel.model F.base.kind).prod (𝓡 1)) ∞ (A.productMap h) := by
  intro x
  let i := A.index (F.projection x)
  let W := TopologicalSpace.Opens.comap F.projection (A.domain i)
  have heq : (fun w : W => A.productMap h w.val) = fun w =>
      ((A.chart i w).1.val, (A.chart i w).2 * (h i (A.chart i w).1.val)⁻¹) := by
    funext w
    rw [A.productMap_eq hcob w.val i w.2, A.chart_fst]
  have hc := (A.chart i).contMDiff
  have hW : ContMDiffAt C.model ((SurfaceModel.model F.base.kind).prod (𝓡 1)) ∞
      (fun w : W => A.productMap h w.val) ⟨x, A.index_mem _⟩ := by
    rw [heq]
    exact ((contMDiff_subtype_val.comp (contMDiff_fst.comp hc)).prodMk
      ((contMDiff_snd.comp hc).mul
        ((A.contMDiff_restrict hh i).comp (contMDiff_fst.comp hc)).inv)).contMDiffAt
  exact contMDiffAt_subtype_iff.mp hW

theorem contMDiff_productInv :
    ContMDiff ((SurfaceModel.model F.base.kind).prod (𝓡 1)) C.model ∞ (A.productInv h) := by
  intro p
  let i := A.index p.1
  let W : TopologicalSpace.Opens (F.base.Carrier × Circle) :=
    ⟨(A.domain i : Set F.base.Carrier) ×ˢ univ, (A.domain i).isOpen.prod isOpen_univ⟩
  let s : W → A.domain i × Circle := fun w => (⟨w.val.1, w.2.1⟩, w.val.2 * h i w.val.1)
  have h1 : ContMDiff ((SurfaceModel.model F.base.kind).prod (𝓡 1))
      (SurfaceModel.model F.base.kind) ∞ (fun w : W => (⟨w.val.1, w.2.1⟩ : A.domain i)) :=
    (ContMDiff.subtypeVal_comp_iff (A.domain i) _).mp (contMDiff_fst.comp contMDiff_subtype_val)
  have hs : ContMDiff ((SurfaceModel.model F.base.kind).prod (𝓡 1))
      ((SurfaceModel.model F.base.kind).prod (𝓡 1)) ∞ s :=
    h1.prodMk ((contMDiff_snd.comp contMDiff_subtype_val).mul
      ((A.contMDiff_restrict hh i).comp h1))
  have heq : (fun w : W => A.productInv h w.val) = fun w => ((A.chart i).symm (s w)).val := by
    funext w
    exact A.productInv_eq hcob w.val i w.2.1
  have hW : ContMDiffAt ((SurfaceModel.model F.base.kind).prod (𝓡 1)) C.model ∞
      (fun w : W => A.productInv h w.val) ⟨p, A.index_mem p.1, trivial⟩ := by
    rw [heq]
    exact (contMDiff_subtype_val.comp ((A.chart i).symm.contMDiff.comp hs)).contMDiffAt
  exact contMDiffAt_subtype_iff.mp hW

def productOfCoboundary :
    U ≃ₘ⟮C.model, (SurfaceModel.model F.base.kind).prod (𝓡 1)⟯ F.base.Carrier × Circle where
  toFun := A.productMap h
  invFun := A.productInv h
  left_inv := A.productInv_productMap h
  right_inv := A.productMap_productInv hcob
  contMDiff_toFun := A.contMDiff_productMap hcob hh
  contMDiff_invFun := A.contMDiff_productInv hcob hh

theorem productOfCoboundary_fst (x : U) :
    (A.productOfCoboundary hcob hh x).1 = F.projection x :=
  rfl

end PrincipalAtlas

theorem PrincipalAtlas.isGloballyTrivial (hcoc : DiscCircleCocycleTrivial.{u})
    {F : CircleFibration C U} (A : PrincipalAtlas F) (P : PlanarBase.{u} 1)
    (e : F.base.Carrier ≃ₘ⟮SurfaceModel.model F.base.kind,
      SurfaceModel.model P.surface.kind⟯ P.surface.Carrier) :
    CircleFibration.IsGloballyTrivial F := by
  obtain ⟨h, hh, hcob⟩ := hcoc F.base P ⟨e⟩ A.count A.domain A.covers A.transition
    A.transition_smooth A.transition_cocycle
  exact ⟨A.productOfCoboundary hcob hh, A.productOfCoboundary_fst hcob hh⟩

theorem circleBundlesOverDiscStandard_of_principalAtlas (hcoc : DiscCircleCocycleTrivial.{u})
    (hA : ∀ (C : CompactCarrier.{u}) (U : TopologicalSpace.Opens C.Carrier)
      (F : CircleFibration C U) (P : PlanarBase.{u} 1),
      Nonempty (F.base.Carrier ≃ₘ⟮SurfaceModel.model F.base.kind,
        SurfaceModel.model P.surface.kind⟯ P.surface.Carrier) → Nonempty (PrincipalAtlas F)) :
    CircleBundlesOverDiscStandard.{u} :=
  circleBundlesOverDiscStandard_iff.mpr fun C U F P ⟨e⟩ =>
    (hA C U F P ⟨e⟩).some.isGloballyTrivial hcoc P e

def PrincipalAtlas.ofProduct {F : CircleFibration C U}
    (Φ : U ≃ₘ⟮C.model, (SurfaceModel.model F.base.kind).prod (𝓡 1)⟯ F.base.Carrier × Circle)
    (hΦ : ∀ x, (Φ x).1 = F.projection x) : PrincipalAtlas F where
  count := 1
  domain _ := ⊤
  covers _ := ⟨0, trivial⟩
  chart _ := (openDiffeomorphOfForall (TopologicalSpace.Opens.comap F.projection ⊤)
      (fun _ => trivial)).trans (Φ.trans ((openDiffeomorphOfForall
        (⊤ : TopologicalSpace.Opens F.base.Carrier) (fun _ => trivial)).symm.prodCongr
          (Diffeomorph.refl (𝓡 1) Circle ∞)))
  chart_fst _ x := hΦ x.val
  transition _ _ _ := 1
  chart_snd i j x hi hj := by
    obtain rfl := Subsingleton.elim i j
    rw [one_mul]

theorem circleBundlesOverDiscStandard_iff_principalAtlas (hcoc : DiscCircleCocycleTrivial.{u}) :
    CircleBundlesOverDiscStandard.{u} ↔
      ∀ (C : CompactCarrier.{u}) (U : TopologicalSpace.Opens C.Carrier)
        (F : CircleFibration C U) (P : PlanarBase.{u} 1),
        Nonempty (F.base.Carrier ≃ₘ⟮SurfaceModel.model F.base.kind,
          SurfaceModel.model P.surface.kind⟯ P.surface.Carrier) → Nonempty (PrincipalAtlas F) := by
  refine ⟨fun h C U F P he => ?_, circleBundlesOverDiscStandard_of_principalAtlas hcoc⟩
  obtain ⟨Φ, hΦ⟩ := circleBundlesOverDiscStandard_iff.mp h C U F P he
  exact ⟨PrincipalAtlas.ofProduct Φ hΦ⟩

theorem CircleFibration.exists_section_of_isGloballyTrivial {F : CircleFibration C U}
    (hF : CircleFibration.IsGloballyTrivial F) :
    ∃ s : F.base.Carrier → U, ContMDiff (SurfaceModel.model F.base.kind) C.model ∞ s ∧
      ∀ y, F.projection (s y) = y := by
  obtain ⟨Φ, hΦ⟩ := hF
  refine ⟨fun y => Φ.symm (y, 1), Φ.symm.contMDiff.comp (contMDiff_id.prodMk contMDiff_const),
    fun y => ?_⟩
  rw [← hΦ, Diffeomorph.apply_symm_apply]

namespace PrincipalAtlas

variable {F : CircleFibration C U} (A : PrincipalAtlas F)

open scoped Classical in
def sectionCoboundary (s : F.base.Carrier → U) (i : Fin A.count) (y : F.base.Carrier) :
    Circle :=
  if hy : F.projection (s y) ∈ A.domain i then (A.chart i ⟨s y, hy⟩).2 else 1

variable {s : F.base.Carrier → U} (hs : ∀ y, F.projection (s y) = y)
include hs

theorem transition_eq_sectionCoboundary (i j : Fin A.count) (y : F.base.Carrier)
    (hi : y ∈ A.domain i) (hj : y ∈ A.domain j) :
    A.transition i j y = A.sectionCoboundary s i y * (A.sectionCoboundary s j y)⁻¹ := by
  have hi' : F.projection (s y) ∈ A.domain i := by
    rw [hs]
    exact hi
  have hj' : F.projection (s y) ∈ A.domain j := by
    rw [hs]
    exact hj
  unfold sectionCoboundary
  rw [dite_eq_left hi', dite_eq_left hj', ← A.transition_eq i j (s y) hi' hj', hs]

theorem sectionCoboundary_smooth (hsm : ContMDiff (SurfaceModel.model F.base.kind) C.model ∞ s)
    (i : Fin A.count) : ContMDiffOn (SurfaceModel.model F.base.kind) (𝓡 1) ∞
      (A.sectionCoboundary s i) (A.domain i) := by
  intro y hy
  let σ : A.domain i → TopologicalSpace.Opens.comap F.projection (A.domain i) := fun v =>
    ⟨s v, by
      change F.projection (s v) ∈ A.domain i
      rw [hs]
      exact v.2⟩
  have hσ : ContMDiff (SurfaceModel.model F.base.kind) C.model ∞ σ :=
    (ContMDiff.subtypeVal_comp_iff _ σ).mp (hsm.comp contMDiff_subtype_val)
  have heq : (fun v : A.domain i => A.sectionCoboundary s i v) =
      fun v => (A.chart i (σ v)).2 := by
    funext v
    have hv : F.projection (s v) ∈ A.domain i := (σ v).2
    unfold sectionCoboundary
    rw [dite_eq_left hv]
  have hW : ContMDiffAt (SurfaceModel.model F.base.kind) (𝓡 1) ∞
      (fun v : A.domain i => A.sectionCoboundary s i v) ⟨y, hy⟩ := by
    rw [heq]
    exact (contMDiff_snd.comp ((A.chart i).contMDiff.comp hσ)).contMDiffAt
  exact (contMDiffAt_subtype_iff.mp hW).contMDiffWithinAt

include A in
theorem isGloballyTrivial_of_section
    (hsm : ContMDiff (SurfaceModel.model F.base.kind) C.model ∞ s) :
    CircleFibration.IsGloballyTrivial F :=
  ⟨A.productOfCoboundary (A.transition_eq_sectionCoboundary hs)
      (A.sectionCoboundary_smooth hs hsm),
    A.productOfCoboundary_fst _ _⟩

omit hs

include A in
theorem isGloballyTrivial_iff_exists_section : CircleFibration.IsGloballyTrivial F ↔
    ∃ s : F.base.Carrier → U, ContMDiff (SurfaceModel.model F.base.kind) C.model ∞ s ∧
      ∀ y, F.projection (s y) = y :=
  ⟨CircleFibration.exists_section_of_isGloballyTrivial,
    fun ⟨_, hsm, hs⟩ => A.isGloballyTrivial_of_section hs hsm⟩

end PrincipalAtlas

section Pieces

theorem solidTorusPiece_eq {W : CompactCarrier.{u}} (T : TorusPresentation.{u} W)
    (i : Fin T.components.count) : SolidTorusPiece T i = ProductFibredPiece T i 1 :=
  rfl

variable {W : CompactCarrier.{u}} {T : TorusPresentation.{u} W} {i : Fin T.components.count}

theorem ProductFibredPiece.fibration_isGloballyTrivial {k : ℕ} (P : ProductFibredPiece T i k) :
    CircleFibration.IsGloballyTrivial P.fibration :=
  ⟨P.trivialization.symm, fun _ => rfl⟩

def solidTorusPieceOfProduct (P : PlanarBase.{u} 1) (port : Fin 1 ≃ T.OwnedSide i)
    (Φ : T.components.piece i ≃ₘ⟮T.cutCarrier.model,
      (SurfaceModel.model P.surface.kind).prod (𝓡 1)⟯ P.surface.Carrier × Circle)
    (hcollar : ∀ p, p ∈ halfCollarSource →
      T.pieceCollar i (port 0) p = Φ.symm (P.collar 0 (p.1.1, p.2), p.1.2)) :
    SolidTorusPiece T i where
  base := P
  port := port
  trivialization := Φ.symm
  collar_eq j p hp := by
    rw [Subsingleton.elim j 0]
    exact hcollar p hp

theorem solidTorusPieceOfProduct_projection (P : PlanarBase.{u} 1)
    (port : Fin 1 ≃ T.OwnedSide i)
    (Φ : T.components.piece i ≃ₘ⟮T.cutCarrier.model,
      (SurfaceModel.model P.surface.kind).prod (𝓡 1)⟯ P.surface.Carrier × Circle)
    (hcollar : ∀ p, p ∈ halfCollarSource →
      T.pieceCollar i (port 0) p = Φ.symm (P.collar 0 (p.1.1, p.2), p.1.2))
    (x : T.components.piece i) :
    (solidTorusPieceOfProduct P port Φ hcollar).fibration.projection x = (Φ x).1 :=
  rfl

def productOfGlobalChart (F : CircleFibration T.cutCarrier (T.components.piece i))
    (b : F.base.Carrier) (hb : ∀ y, y ∈ F.neighborhood b) (P : PlanarBase.{u} 1)
    (e : F.base.Carrier ≃ₘ⟮SurfaceModel.model F.base.kind,
      SurfaceModel.model P.surface.kind⟯ P.surface.Carrier) :
    T.components.piece i ≃ₘ⟮T.cutCarrier.model,
      (SurfaceModel.model P.surface.kind).prod (𝓡 1)⟯ P.surface.Carrier × Circle :=
  (CircleFibration.productOfGlobalTrivialization F b hb).trans
    (e.prodCongr (Diffeomorph.refl (𝓡 1) Circle ∞))

theorem solidTorusPieceOfProduct_globalChart_projection
    (F : CircleFibration T.cutCarrier (T.components.piece i))
    (b : F.base.Carrier) (hb : ∀ y, y ∈ F.neighborhood b) (P : PlanarBase.{u} 1)
    (e : F.base.Carrier ≃ₘ⟮SurfaceModel.model F.base.kind,
      SurfaceModel.model P.surface.kind⟯ P.surface.Carrier) (port : Fin 1 ≃ T.OwnedSide i)
    (hcollar : ∀ p, p ∈ halfCollarSource → T.pieceCollar i (port 0) p =
      (productOfGlobalChart F b hb P e).symm (P.collar 0 (p.1.1, p.2), p.1.2))
    (x : T.components.piece i) :
    (solidTorusPieceOfProduct P port _ hcollar).fibration.projection x = e (F.projection x) := by
  rw [solidTorusPieceOfProduct_projection]
  exact congrArg e (CircleFibration.productOfGlobalTrivialization_fst F b hb x)

end Pieces

end GC.Seifert
