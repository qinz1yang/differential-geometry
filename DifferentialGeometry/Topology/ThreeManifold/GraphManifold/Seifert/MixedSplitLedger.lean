import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MixedSplitStage
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeSeifertNormalizationMoves

/-!
# The ledgers of a mixed split

Lane MS-b, tier MS5b (design `handoffs/20261004-design-ms-mixed-split.md` §3.6, review 30 §1.4,
§6.2, §6.3). Fix side data `D` and capping conditions `hC` of a split seam `j` on side `b` of a
mixed stage `σ` along a spherical cut-cap transition `X`, and the mixed stages `capStage D hC c`
on the components `c` of the capped manifold (`MixedSplitStage`).

Bijections. A closed system whose components each contain a piece splits its seams and its pieces
over the components (`MixedClosedSystem.seamSigma`, `pieceSigma`). On the protected seams (the
seams `≠ j` lying in `σ.prot`, since `j` is inner) and on the frozen pieces (all passive) this
gives `protEquiv : σ.ProtSeam ≃ Σ c, (capStage D hC c).ProtSeam` and
`frozenEquiv : σ.Frozen ≃ Σ c, (capStage D hC c).Frozen`. The image of a protected seam is the
same old seam (`seamEquiv_protEquiv`), the image of a frozen piece the same old piece
(`pieceEquiv_frozenEquiv`), and the protected seams of `capStage D hC c` are exactly the images of
the old ones (`mem_capStage_prot_iff`).

Collar ledger (`capCollarLedger`). The new seam is the old seam at `(sideTwist D k true t, δ₂ s)`
read through the core, so the ledger has `reparam = sideTwist D k true`, the holonomy of the
capped solid torus when the left side is a host port (`capCollarLedger_reparam_of_host`) and the
identity otherwise (`capCollarLedger_reparam_of_not_host`), and `scale = δ₂`; a host port on the
right side only enters the new matching, so a seam with host ports on both sides is covered. The
old collar may be any map agreeing with the seam of `σ` below height `δ₂`.

Frozen ledger (`capFrozenLedger`). The diffeomorphism runs old → native → new: the recast of the
old component carrier onto the passive native piece, the identification with the piece of the
restricted system, and `relativeCapNativePieceDiffeomorph` (`frozenDiffeo`); it commutes with
the cut maps through the core (`frozenDiffeo_cutMap`). It preserves orientation
(`frozenDiffeo_oriented`): the old cut map is oriented (`quotient_oriented`), the core map is
oriented at interior core points (`core_positive`, `coreMap_orientedAt`), the new cut map is
oriented by construction and the component inclusion is oriented, and a diffeomorphism through
which two oriented maps into the capped manifold commute is positive.

Counts. Every component contains a piece, so there are finitely many components; the inner seams
of all `capStage D hC c` are in bijection with the inner seams `≠ j` of `σ` (`capInnerEquiv`),
hence `∑ c, innerCount + 1 = innerCount σ` (`sum_innerCount_capStage`) and the inner count drops
on every component (`innerCount_capStage_lt`).
-/

set_option autoImplicit false

noncomputable section
open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open GC.Topology (componentCarrier)
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

namespace MixedClosedSystem

variable {kind : CarrierModel} {N : ClosedOrientedManifold.{u} 3}
  (P : MixedClosedSystem.{u} N.Carrier kind) (hK : ∀ K, ∃ i, P.pieceComp i = K)

def seamSigma : P.Seam ≃ Σ K, Fin (Fintype.card (P.restrict K (hK K)).Seam) where
  toFun x := ⟨P.seamComp x, (P.restrict _ (hK _)).seamEquiv.symm ⟨x, rfl⟩⟩
  invFun y := ((P.restrict y.1 (hK y.1)).seamEquiv y.2).1
  left_inv x := congrArg Subtype.val ((P.restrict _ (hK _)).seamEquiv.apply_symm_apply ⟨x, rfl⟩)
  right_inv := by
    rintro ⟨K, d⟩
    have key : ∀ x : {c : P.Seam // P.seamComp c = K}, (P.restrict K (hK K)).seamEquiv d = x →
        (⟨P.seamComp x.1, (P.restrict _ (hK _)).seamEquiv.symm ⟨x.1, rfl⟩⟩ :
          Σ K, Fin (Fintype.card (P.restrict K (hK K)).Seam)) = ⟨K, d⟩ := by
      rintro ⟨x, rfl⟩ hx
      exact Sigma.ext rfl (heq_of_eq ((Equiv.symm_apply_eq _).mpr hx.symm))
    exact key _ rfl

theorem seamEquiv_seamSigma (x : P.Seam) :
    ((P.restrict (P.seamSigma hK x).1 (hK _)).seamEquiv (P.seamSigma hK x).2).1 = x :=
  (P.seamSigma hK).symm_apply_apply x

def pieceSigma : P.Piece ≃ Σ K, Fin (Fintype.card (P.restrict K (hK K)).Piece) where
  toFun x := ⟨P.pieceComp x, (P.restrict _ (hK _)).pieceEquiv.symm ⟨x, rfl⟩⟩
  invFun y := ((P.restrict y.1 (hK y.1)).pieceEquiv y.2).1
  left_inv x := congrArg Subtype.val ((P.restrict _ (hK _)).pieceEquiv.apply_symm_apply ⟨x, rfl⟩)
  right_inv := by
    rintro ⟨K, d⟩
    have key : ∀ x : {i : P.Piece // P.pieceComp i = K}, (P.restrict K (hK K)).pieceEquiv d = x →
        (⟨P.pieceComp x.1, (P.restrict _ (hK _)).pieceEquiv.symm ⟨x.1, rfl⟩⟩ :
          Σ K, Fin (Fintype.card (P.restrict K (hK K)).Piece)) = ⟨K, d⟩ := by
      rintro ⟨x, rfl⟩ hx
      exact Sigma.ext rfl (heq_of_eq ((Equiv.symm_apply_eq _).mpr hx.symm))
    exact key _ rfl

theorem pieceEquiv_pieceSigma (x : P.Piece) :
    ((P.restrict (P.pieceSigma hK x).1 (hK _)).pieceEquiv (P.pieceSigma hK x).2).1 = x :=
  (P.pieceSigma hK).symm_apply_apply x

end MixedClosedSystem

def sigmaSubtypeEquiv {ι : Type*} {A : ι → Type*} (p : ∀ i, A i → Prop) :
    {x : Σ i, A i // p x.1 x.2} ≃ Σ i, {a : A i // p i a} where
  toFun x := ⟨x.1.1, x.1.2, x.2⟩
  invFun y := ⟨⟨y.1, y.2.1⟩, y.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

namespace RelativeNormalization.MixedStage

variable {Q : ConnectedClosedOrientedManifold.{u} 3} {σ : MixedStage Q}
  {j : Fin σ.toTorus.pairing.count} {b : Bool} {h : σ.IsSplitSeam j b} {S : σ.SplitData h}
  {P : ClosedOrientedManifold.{u} 3} {X : SphericalCutCapTransition Q.toClosedOrientedManifold P}
  {a : X.tubes.Index} {δ₂ : ℝ}
  (D : σ.SideData S X.capping a δ₂) (hC : σ.CappedConditions S a δ₂)

section Bijections

def protCapSeam (hj : j ∉ σ.prot) : σ.ProtSeam ≃ {c : CapSeam σ j // c.1 ∈ σ.prot} where
  toFun k := ⟨⟨k.1, fun he => hj (he ▸ k.2)⟩, k.2⟩
  invFun c := ⟨c.1.1, c.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem mem_capStage_prot_iff (c : ConnectedComponents X.capped.Carrier)
    (d : Fin (capCutSystem D hC c).seamCount) :
    d ∈ (capStage D hC c).prot ↔ ((capComponentSystem D hC c).seamEquiv d).1.1 ∈ σ.prot :=
  ⟨fun hd => (Finset.mem_filter.mp hd).2, fun hd => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩⟩

open Classical in
theorem mem_capStage_frozen_iff (c : ConnectedComponents X.capped.Carrier)
    (z : Fin (capCutSystem D hC c).count) :
    z ∈ (capStage D hC c).frozen ↔ capFrozen σ j b ((capComponentSystem D hC c).pieceEquiv z).1 :=
  ⟨fun hz => (Finset.mem_filter.mp hz).2, fun hz => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩⟩

def capSeamSigma : CapSeam σ j ≃ Σ c, Fin (capCutSystem D hC c).seamCount :=
  (capSystem D hC).seamSigma (exists_capPiece_comp D hC)

theorem seamEquiv_capSeamSigma (x : CapSeam σ j) :
    ((capComponentSystem D hC (capSeamSigma D hC x).1).seamEquiv (capSeamSigma D hC x).2).1 = x :=
  (capSystem D hC).seamEquiv_seamSigma (exists_capPiece_comp D hC) x

def capSeamSub (p : CapSeam σ j → Prop) : {x // p x} ≃
    Σ c, {d : Fin (capCutSystem D hC c).seamCount //
      p ((capComponentSystem D hC c).seamEquiv d).1} :=
  ((capSeamSigma D hC).subtypeEquiv
    (q := fun y => p ((capComponentSystem D hC y.1).seamEquiv y.2).1)
    fun x => by rw [seamEquiv_capSeamSigma]).trans
    (sigmaSubtypeEquiv fun c d => p ((capComponentSystem D hC c).seamEquiv d).1)

theorem seamEquiv_capSeamSub (p : CapSeam σ j → Prop) (x : {x // p x}) :
    ((capComponentSystem D hC (capSeamSub D hC p x).1).seamEquiv (capSeamSub D hC p x).2.1).1 =
      x.1 :=
  seamEquiv_capSeamSigma D hC x.1

def protEquiv : σ.ProtSeam ≃ Σ c, (capStage D hC c).ProtSeam :=
  (protCapSeam h.1).trans <| (capSeamSub D hC fun x => x.1 ∈ σ.prot).trans <|
    Equiv.sigmaCongrRight fun c => Equiv.subtypeEquivRight fun d =>
      (mem_capStage_prot_iff D hC c d).symm

theorem seamEquiv_protEquiv (k : σ.ProtSeam) :
    ((capComponentSystem D hC (protEquiv D hC k).1).seamEquiv (protEquiv D hC k).2.1).1.1 = k.1 :=
  congrArg Subtype.val (seamEquiv_capSeamSub D hC (fun x => x.1 ∈ σ.prot) (protCapSeam h.1 k))

variable (h) in
def frozenCap (i : σ.Frozen) :
    {k : Fin σ.toTorus.components.count // k ≠ σ.seamPiece j b ∧ k ≠ σ.hostPiece j b} :=
  ⟨i.1, fun he => σ.seamPiece_not_frozen h (he ▸ i.2),
    fun he => σ.hostPiece_not_frozen h (he ▸ i.2)⟩

variable (h) in
def frozenCapPiece : σ.Frozen ≃ {x : CapPiece σ j b // capFrozen σ j b x} where
  toFun i := ⟨.inl (frozenCap h i), i.2⟩
  invFun
    | ⟨.inl k, hk⟩ => ⟨k.1, hk⟩
    | ⟨.inr _, hf⟩ => False.elim hf
  left_inv _ := rfl
  right_inv
    | ⟨.inl _, _⟩ => rfl
    | ⟨.inr _, hf⟩ => False.elim hf

def capPieceSigma : CapPiece σ j b ≃ Σ c, Fin (capCutSystem D hC c).count :=
  (capSystem D hC).pieceSigma (exists_capPiece_comp D hC)

theorem pieceEquiv_capPieceSigma (x : CapPiece σ j b) :
    ((capComponentSystem D hC (capPieceSigma D hC x).1).pieceEquiv
      (capPieceSigma D hC x).2).1 = x :=
  (capSystem D hC).pieceEquiv_pieceSigma (exists_capPiece_comp D hC) x

def capPieceSub (p : CapPiece σ j b → Prop) : {x // p x} ≃
    Σ c, {z : Fin (capCutSystem D hC c).count // p ((capComponentSystem D hC c).pieceEquiv z).1} :=
  ((capPieceSigma D hC).subtypeEquiv
    (q := fun y => p ((capComponentSystem D hC y.1).pieceEquiv y.2).1)
    fun x => by rw [pieceEquiv_capPieceSigma]).trans
    (sigmaSubtypeEquiv fun c z => p ((capComponentSystem D hC c).pieceEquiv z).1)

theorem pieceEquiv_capPieceSub (p : CapPiece σ j b → Prop) (x : {x // p x}) :
    ((capComponentSystem D hC (capPieceSub D hC p x).1).pieceEquiv
      (capPieceSub D hC p x).2.1).1 = x.1 :=
  pieceEquiv_capPieceSigma D hC x.1

def frozenEquiv : σ.Frozen ≃ Σ c, (capStage D hC c).Frozen :=
  (frozenCapPiece h).trans <| (capPieceSub D hC (capFrozen σ j b)).trans <|
    Equiv.sigmaCongrRight fun c => Equiv.subtypeEquivRight fun z =>
      (mem_capStage_frozen_iff D hC c z).symm

theorem pieceEquiv_frozenEquiv (i : σ.Frozen) :
    ((capComponentSystem D hC (frozenEquiv D hC i).1).pieceEquiv (frozenEquiv D hC i).2.1).1 =
      .inl (frozenCap h i) :=
  pieceEquiv_capPieceSub D hC (capFrozen σ j b) (frozenCapPiece h i)

end Bijections

section Collar

theorem capStage_seam_val (c : ConnectedComponents X.capped.Carrier)
    (d : Fin (capCutSystem D hC c).seamCount) {p : Torus × ℝ} (hp : p ∈ signedCollarSource) :
    ((capStage D hC c).toTorus.seam d p).val =
      capSeam D hC ((capComponentSystem D hC c).seamEquiv d).1 p :=
  codRestrictOpens_apply _ _ _ ((capSystem D hC).seam_mem c _
    (by rw [(capSystem D hC).seam_source]; exact hp))

def capCollarLedger (c : ConnectedComponents X.capped.Carrier)
    (d : Fin (capCutSystem D hC c).seamCount) (σ₀ : Torus × ℝ → Q.Carrier)
    (h₀ : ∀ t s, |s| < δ₂ →
      σ₀ (t, s) = σ.toTorus.seam ((capComponentSystem D hC c).seamEquiv d).1.1 (t, s)) :
    CollarLedger (coreTrack X c) σ₀ ((capStage D hC c).toTorus.seam d) where
  reparam := sideTwist D ((capComponentSystem D hC c).seamEquiv d).1.1 true
  scale := δ₂
  scale_pos := hC.pos
  scale_le_one := hC.le_one
  tracked p hp := by
    obtain ⟨hcore, -⟩ := capSeam_core D hC ((capComponentSystem D hC c).seamEquiv d).1 hp
    have hlt : |δ₂ * p.2| < δ₂ := by
      have hp' : |p.2| < 1 := abs_lt.mpr ⟨hp.1, hp.2⟩
      rw [abs_mul, abs_of_pos hC.pos]
      nlinarith [abs_nonneg p.2, hC.pos]
    refine ⟨⟨_, hcore⟩, ?_, ?_⟩
    · rw [h₀ _ _ hlt]
      exact fixedCapPresentation_seam D hC.pos hC.le_one _ p
    · exact ((capStage_seam_val D hC c d hp).trans ((capSeam_apply D hC _ p).trans
        (SplitTube.coreMap_of_mem X.capping hcore))).symm

theorem capCollarLedger_reparam_of_host (c : ConnectedComponents X.capped.Carrier)
    (d : Fin (capCutSystem D hC c).seamCount) (σ₀ : Torus × ℝ → Q.Carrier)
    (h₀ : ∀ t s, |s| < δ₂ →
      σ₀ (t, s) = σ.toTorus.seam ((capComponentSystem D hC c).seamEquiv d).1.1 (t, s))
    (hH : σ.seamPiece ((capComponentSystem D hC c).seamEquiv d).1.1 true = σ.hostPiece j b) :
    (capCollarLedger D hC c d σ₀ h₀).reparam = D.holonomy (D.solidOf (σ.hostPortOf h hH)) :=
  sideTwist_of_host D _ hH

theorem capCollarLedger_reparam_of_not_host (c : ConnectedComponents X.capped.Carrier)
    (d : Fin (capCutSystem D hC c).seamCount) (σ₀ : Torus × ℝ → Q.Carrier)
    (h₀ : ∀ t s, |s| < δ₂ →
      σ₀ (t, s) = σ.toTorus.seam ((capComponentSystem D hC c).seamEquiv d).1.1 (t, s))
    (hH : ¬ σ.seamPiece ((capComponentSystem D hC c).seamEquiv d).1.1 true = σ.hostPiece j b) :
    (capCollarLedger D hC c d σ₀ h₀).reparam = Diffeomorph.refl torusModel Torus ∞ :=
  sideTwist_of_not_host D _ hH

theorem capCollarLedger_scale (c : ConnectedComponents X.capped.Carrier)
    (d : Fin (capCutSystem D hC c).seamCount) (σ₀ : Torus × ℝ → Q.Carrier)
    (h₀ : ∀ t s, |s| < δ₂ →
      σ₀ (t, s) = σ.toTorus.seam ((capComponentSystem D hC c).seamEquiv d).1.1 (t, s)) :
    (capCollarLedger D hC c d σ₀ h₀).scale = δ₂ :=
  rfl

end Collar

section Orient

private theorem orientation_map_trans_three {A B C : Type*} [AddCommGroup A] [Module ℝ A]
    [AddCommGroup B] [Module ℝ B] [AddCommGroup C] [Module ℝ C] (e : A ≃ₗ[ℝ] B)
    (f : B ≃ₗ[ℝ] C) (o : Orientation ℝ A (Fin 3)) :
    Orientation.map (Fin 3) (e.trans f) o =
      Orientation.map (Fin 3) f (Orientation.map (Fin 3) e o) := by
  induction o using Module.Ray.ind with | h v hv => rfl

private theorem preservesOrientation_of_oriented {E H E' H' F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [FiniteDimensional ℝ E'] [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
    {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace G]
    {J : ModelWithCorners ℝ F G} {Y : Type*} [TopologicalSpace Y] [ChartedSpace G Y]
    [IsManifold J ∞ Y] (f : M ≃ₘ⟮I, I'⟯ N) (FM : M → Y) (FN : N → Y)
    (hFN : ∀ y, MDifferentiableAt I' J FN y) (hcomp : ∀ x, FN (f x) = FM x)
    (oM : ManifoldOrientation I M 3) (oN : ManifoldOrientation I' N 3)
    (O : ManifoldOrientation J Y 3)
    (hM : ∀ x, ∃ L : TangentSpace I x ≃ₗ[ℝ] TangentSpace J (FM x),
      (∀ v, L v = mfderiv I J FM x v) ∧
        Orientation.map (Fin 3) L (oM.orientation x) = O.orientation (FM x))
    (hN : ∀ y, ∃ L : TangentSpace I' y ≃ₗ[ℝ] TangentSpace J (FN y),
      (∀ v, L v = mfderiv I' J FN y v) ∧
        Orientation.map (Fin 3) L (oN.orientation y) = O.orientation (FN y)) :
    f.preservesOrientation oM oN := by
  intro x
  obtain ⟨LM, hLM, hoM⟩ := hM x
  obtain ⟨LN, hLN, hoN⟩ := hN (f x)
  let Df := (f.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
  have hFM : FM = FN ∘ f := funext fun x => (hcomp x).symm
  have key : ∀ v, LN (Df v) = LM v := by
    intro v
    rw [hLM, hLN]
    have hc := mfderiv_comp x (hFN (f x)) (f.mdifferentiable (by simp) x)
    rw [← hFM] at hc
    rw [hc]
    rfl
  have hDL : Df.trans LN = LM := LinearEquiv.ext key
  apply (Orientation.map (Fin 3) LN).injective
  have h1 := orientation_map_trans_three Df LN (oM.orientation x)
  have e3 : O.orientation (FN (f x)) = O.orientation (FM x) := by rw [hcomp x]
  exact h1.symm.trans ((congrArg (fun L => Orientation.map (Fin 3) L (oM.orientation x))
    hDL).trans (hoM.trans (e3.symm.trans hoN.symm)))

private theorem cutMap_orientedAt {W : CompactCarrier.{u}} (G : TorusPresentation W)
    (U : TopologicalSpace.Opens G.cutCarrier.Carrier) (x : U) :
    ∃ L : TangentSpace G.cutCarrier.model x ≃ₗ[ℝ] TangentSpace W.model (G.cutMap x.val),
      (∀ v, L v = mfderiv G.cutCarrier.model W.model (G.cutMap ∘ Subtype.val) x v) ∧
        Orientation.map (Fin 3) L ((G.cutCarrier.orientation.restrictOpen U).orientation x) =
          W.orientation.orientation (G.cutMap x.val) := by
  obtain ⟨L, hL, ho⟩ := G.quotient_oriented x.val
  refine ⟨L, fun v => ?_, ho⟩
  rw [DifferentialGeometry.Topology.Manifold.mfderiv_restrict_open G.cutCarrier.model W.model U
    G.cutMap G.quotient_smooth x]
  exact hL v

theorem orientedAt_comp {E H E' H' E'' H'' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    [NormedAddCommGroup E''] [NormedSpace ℝ E''] [TopologicalSpace H'']
    {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
    {I'' : ModelWithCorners ℝ E'' H''} {A B C : Type*} [TopologicalSpace A] [ChartedSpace H A]
    [TopologicalSpace B] [ChartedSpace H' B] [TopologicalSpace C] [ChartedSpace H'' C]
    {f : A → B} {g : B → C} {x : A} (hf : MDifferentiableAt I I' f x)
    (hg : MDifferentiableAt I' I'' g (f x)) {oA : Orientation ℝ (TangentSpace I x) (Fin 3)}
    {oB : Orientation ℝ (TangentSpace I' (f x)) (Fin 3)}
    {oC : Orientation ℝ (TangentSpace I'' (g (f x))) (Fin 3)}
    (Hf : ∃ L : TangentSpace I x ≃ₗ[ℝ] TangentSpace I' (f x),
      (∀ v, L v = mfderiv I I' f x v) ∧ Orientation.map (Fin 3) L oA = oB)
    (Hg : ∃ L : TangentSpace I' (f x) ≃ₗ[ℝ] TangentSpace I'' (g (f x)),
      (∀ v, L v = mfderiv I' I'' g (f x) v) ∧ Orientation.map (Fin 3) L oB = oC) :
    ∃ L : TangentSpace I x ≃ₗ[ℝ] TangentSpace I'' (g (f x)),
      (∀ v, L v = mfderiv I I'' (g ∘ f) x v) ∧ Orientation.map (Fin 3) L oA = oC := by
  obtain ⟨L₁, h₁, o₁⟩ := Hf
  obtain ⟨L₂, h₂, o₂⟩ := Hg
  refine ⟨L₁.trans L₂, fun v => ?_, ?_⟩
  · rw [mfderiv_comp x hg hf, ContinuousLinearMap.comp_apply, ← h₁, ← h₂]
    rfl
  · rw [orientation_map_trans_three, o₁, o₂]

theorem coreMap_orientedAt {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
    (K : SphericalCapping M N T) (y : T.core)
    (hint : letI := K.coreCharts; (𝓡∂ 3).IsInteriorPoint y) :
    ∃ L : TangentSpace (𝓡 3) y.val ≃ₗ[ℝ] TangentSpace (𝓡 3) (SplitTube.coreMap K y.val),
      (∀ v, L v = mfderiv (𝓡 3) (𝓡 3) (SplitTube.coreMap K) y.val v) ∧
        Orientation.map (Fin 3) L (M.orientation.orientation y.val) =
          N.orientation.orientation (SplitTube.coreMap K y.val) := by
  let _ := K.coreCharts
  let _ := K.coreSmooth
  obtain ⟨hi, hj, hpos⟩ := K.core_positive y hint
  have hval : MDifferentiableAt (𝓡∂ 3) (𝓡 3) (Subtype.val : T.core → M.Carrier) y :=
    K.core_induced.contMDiff.mdifferentiableAt (by simp)
  have hcm : MDifferentiableAt (𝓡 3) (𝓡 3) (SplitTube.coreMap K) y.val :=
    (SplitTube.isLocalDiffeomorphAt_coreMap K y hint).mdifferentiableAt (by simp)
  have heq : SplitTube.coreMap K ∘ (Subtype.val : T.core → M.Carrier) = K.coreInclusion :=
    funext (SplitTube.coreMap_val K)
  have hcomp : mfderiv (𝓡∂ 3) (𝓡 3) K.coreInclusion y =
      (mfderiv (𝓡 3) (𝓡 3) (SplitTube.coreMap K) y.val).comp
        (mfderiv (𝓡∂ 3) (𝓡 3) (Subtype.val : T.core → M.Carrier) y) := by
    rw [← mfderiv_comp y hcm hval, heq]
  let eV := LinearEquiv.ofBijective
    (mfderiv (𝓡∂ 3) (𝓡 3) (Subtype.val : T.core → M.Carrier) y).toLinearMap hi
  let eJ := LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) (𝓡 3) K.coreInclusion y).toLinearMap hj
  have key : ∀ p (_ : K.coreInclusion y = p),
      ∃ L : TangentSpace (𝓡 3) y.val ≃ₗ[ℝ] TangentSpace (𝓡 3) p,
        (∀ v, L v = mfderiv (𝓡∂ 3) (𝓡 3) K.coreInclusion y (eV.symm v)) ∧
          Orientation.map (Fin 3) L (M.orientation.orientation y.val) =
            N.orientation.orientation p := by
    rintro p rfl
    exact ⟨eV.symm.trans eJ, fun v => rfl, hpos⟩
  obtain ⟨L, hL, ho⟩ := key _ (SplitTube.coreMap_val K y).symm
  refine ⟨L, fun v => ?_, ho⟩
  rw [hL, hcomp]
  exact congrArg (mfderiv (𝓡 3) (𝓡 3) (SplitTube.coreMap K) y.val) (eV.apply_symm_apply v)

end Orient

section Frozen

def partCongr {i i' : (capSystem D hC).Piece} (e : i = i') :
    (capSystem D hC).Part i ≃ₘ⟮CarrierModel.withBoundary.model,
      CarrierModel.withBoundary.model⟯ (capSystem D hC).Part i' := by
  subst e
  exact Diffeomorph.refl _ _ ∞

theorem map_partCongr {i i' : (capSystem D hC).Piece} (e : i = i')
    (q : (capSystem D hC).Part i) :
    (capSystem D hC).map i' (partCongr D hC e q) = (capSystem D hC).map i q := by
  subst e
  rfl

def frozenDiffeo (c : ConnectedComponents X.capped.Carrier) (z : Fin (capCutSystem D hC c).count)
    (k : {k : Fin σ.toTorus.components.count // k ≠ σ.seamPiece j b ∧ k ≠ σ.hostPiece j b})
    (hz : ((capComponentSystem D hC c).pieceEquiv z).1 = .inl k) :
    (componentCarrier σ.toTorus.cutCarrier σ.toTorus.components k.1).Carrier ≃ₘ⟮
      (componentCarrier σ.toTorus.cutCarrier σ.toTorus.components k.1).model,
      (componentCarrier (capStage D hC c).toTorus.cutCarrier (capStage D hC c).toTorus.components
        z).model⟯
      (componentCarrier (capStage D hC c).toTorus.cutCarrier (capStage D hC c).toTorus.components
        z).Carrier :=
  (passiveRecast D hC k.1).trans ((partCongr D hC hz.symm).trans
    (relativeCapNativePieceDiffeomorph (capCutSystem D hC c) z))

theorem frozenDiffeo_cutMap (c : ConnectedComponents X.capped.Carrier)
    (z : Fin (capCutSystem D hC c).count)
    (k : {k : Fin σ.toTorus.components.count // k ≠ σ.seamPiece j b ∧ k ≠ σ.hostPiece j b})
    (hz : ((capComponentSystem D hC c).pieceEquiv z).1 = .inl k)
    (x : (componentCarrier σ.toTorus.cutCarrier σ.toTorus.components k.1).Carrier) :
    ((capStage D hC c).toTorus.cutMap (frozenDiffeo D hC c z k hz x).val).val =
      SplitTube.coreMap X.capping (σ.toTorus.cutMap x.val) := by
  change (capSystem D hC).map _ (partCongr D hC hz.symm (passiveRecast D hC k.1 x)) = _
  exact (map_partCongr D hC hz.symm _).trans ((capMap_inl D hC k _).trans
    (congrArg (fun y => SplitTube.coreMap X.capping (σ.toTorus.cutMap y))
      (passivePt_passiveRecast D hC k.1 x)))

theorem frozenDiffeo_oriented (c : ConnectedComponents X.capped.Carrier)
    (z : Fin (capCutSystem D hC c).count)
    (k : {k : Fin σ.toTorus.components.count // k ≠ σ.seamPiece j b ∧ k ≠ σ.hostPiece j b})
    (hz : ((capComponentSystem D hC c).pieceEquiv z).1 = .inl k) :
    (frozenDiffeo D hC c z k hz).preservesOrientation
      (componentCarrier σ.toTorus.cutCarrier σ.toTorus.components k.1).orientation
      (componentCarrier (capStage D hC c).toTorus.cutCarrier (capStage D hC c).toTorus.components
        z).orientation := by
  refine preservesOrientation_of_oriented (frozenDiffeo D hC c z k hz)
    (SplitTube.coreMap X.capping ∘ (σ.toTorus.cutMap ∘ Subtype.val))
    (Subtype.val ∘ ((capStage D hC c).toTorus.cutMap ∘ Subtype.val))
    (fun y => ?_) (frozenDiffeo_cutMap D hC c z k hz) _ _ X.capped.orientation
    (fun x => ?_) (fun y => ?_)
  · exact (contMDiff_subtype_val.comp ((capStage D hC c).toTorus.quotient_smooth.comp
      contMDiff_subtype_val)).mdifferentiableAt (by simp)
  · obtain ⟨hcore, hne⟩ := hC.piece k.1 k.2.1 k.2.2 x.val x.2
    have hint := SplitTube.isInteriorPoint_of_forall_ne X.capping ⟨_, hcore⟩ hne
    exact orientedAt_comp
      ((σ.toTorus.quotient_smooth.comp contMDiff_subtype_val).mdifferentiableAt (by simp))
      ((SplitTube.isLocalDiffeomorphAt_coreMap X.capping ⟨_, hcore⟩ hint).mdifferentiableAt
        (by simp))
      (cutMap_orientedAt σ.toTorus _ x)
      (coreMap_orientedAt X.capping ⟨_, hcore⟩ hint)
  · exact orientedAt_comp
      (((capStage D hC c).toTorus.quotient_smooth.comp contMDiff_subtype_val).mdifferentiableAt
        (by simp))
      ((contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp))
      (cutMap_orientedAt (capStage D hC c).toTorus _ y)
      ⟨_, fun v => ClosedOrientedManifold.componentInclusionTangentEquiv_apply X.capped c _ v,
        ClosedOrientedManifold.componentInclusion_preservesOrientation X.capped c _⟩

def capFrozenLedger (c : ConnectedComponents X.capped.Carrier)
    (z : Fin (capCutSystem D hC c).count)
    (k : {k : Fin σ.toTorus.components.count // k ≠ σ.seamPiece j b ∧ k ≠ σ.hostPiece j b})
    (hz : ((capComponentSystem D hC c).pieceEquiv z).1 = .inl k) :
    FrozenLedger (coreTrack X c) σ k.1 (capStage D hC c) z where
  diffeo := frozenDiffeo D hC c z k hz
  oriented := frozenDiffeo_oriented D hC c z k hz
  map x := by
    obtain ⟨hcore, -⟩ := hC.piece k.1 k.2.1 k.2.2 x.val x.2
    refine ⟨⟨_, hcore⟩, rfl, ?_⟩
    rw [← SplitTube.coreMap_of_mem X.capping hcore]
    exact (frozenDiffeo_cutMap D hC c z k hz x).symm

end Frozen

section Count

include D hC in
theorem finite_capComponents : Finite (ConnectedComponents X.capped.Carrier) :=
  Finite.of_surjective _ fun c => exists_capPiece_comp D hC c

theorem card_inner_capSeam (hj : j ∉ σ.prot) :
    Fintype.card {x : CapSeam σ j // x.1 ∉ σ.prot} + 1 = σ.innerCount := by
  classical
  let e : {x : CapSeam σ j // x.1 ∉ σ.prot} ≃ (σ.protᶜ.erase j) :=
    { toFun x := ⟨x.1.1, Finset.mem_erase.mpr ⟨x.1.2, Finset.mem_compl.mpr x.2⟩⟩
      invFun y := ⟨⟨y.1, (Finset.mem_erase.mp y.2).1⟩,
        Finset.mem_compl.mp (Finset.mem_erase.mp y.2).2⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  rw [Fintype.card_congr e, Fintype.card_coe, innerCount,
    Finset.card_erase_add_one (Finset.mem_compl.mpr hj)]

def capInnerEquiv : (Σ c, {d : Fin (capStage D hC c).toTorus.pairing.count //
      d ∉ (capStage D hC c).prot}) ≃ {x : CapSeam σ j // x.1 ∉ σ.prot} :=
  ((capSeamSub D hC fun x => x.1 ∉ σ.prot).trans (Equiv.sigmaCongrRight fun c =>
    Equiv.subtypeEquivRight fun d => not_congr (mem_capStage_prot_iff D hC c d).symm)).symm

theorem capInnerEquiv_symm_seamEquiv (x : {x : CapSeam σ j // x.1 ∉ σ.prot}) :
    ((capComponentSystem D hC ((capInnerEquiv D hC).symm x).1).seamEquiv
      ((capInnerEquiv D hC).symm x).2.1).1 = x.1 :=
  seamEquiv_capSeamSub D hC _ x

theorem innerCount_capStage_eq_card (c : ConnectedComponents X.capped.Carrier) :
    (capStage D hC c).innerCount = Fintype.card {d : Fin (capStage D hC c).toTorus.pairing.count //
      d ∉ (capStage D hC c).prot} :=
  (Fintype.card_coe _).symm.trans
    (Fintype.card_congr (Equiv.subtypeEquivRight fun _ => Finset.mem_compl))

theorem sum_innerCount_capStage :
    (haveI := finite_capComponents D hC; letI := Fintype.ofFinite (ConnectedComponents
      X.capped.Carrier); ∑ c, (capStage D hC c).innerCount) + 1 = σ.innerCount := by
  have := finite_capComponents D hC
  let _ := Fintype.ofFinite (ConnectedComponents X.capped.Carrier)
  calc (∑ c, (capStage D hC c).innerCount) + 1 = Fintype.card
        (Σ c, {d : Fin (capStage D hC c).toTorus.pairing.count //
          d ∉ (capStage D hC c).prot}) + 1 := by
        rw [Fintype.card_sigma]
        simp only [innerCount_capStage_eq_card]
    _ = Fintype.card {x : CapSeam σ j // x.1 ∉ σ.prot} + 1 := by
        rw [Fintype.card_congr (capInnerEquiv D hC)]
    _ = σ.innerCount := card_inner_capSeam h.1

theorem innerCount_capStage_lt (c : ConnectedComponents X.capped.Carrier) :
    (capStage D hC c).innerCount < σ.innerCount := by
  have := finite_capComponents D hC
  let _ := Fintype.ofFinite (ConnectedComponents X.capped.Carrier)
  have h1 : (∑ c', (capStage D hC c').innerCount) + 1 = σ.innerCount :=
    sum_innerCount_capStage D hC
  have h2 : (capStage D hC c).innerCount ≤ ∑ c', (capStage D hC c').innerCount :=
    Finset.single_le_sum (f := fun c' => (capStage D hC c').innerCount)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
  omega

end Count

end RelativeNormalization.MixedStage

end GC.Seifert
