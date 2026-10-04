import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TwoSolidTori
import Mathlib.GroupTheory.FreeGroup.Basic

/-!
# Free ports of a block with one filling

Chapter 6, packet K10b: the one-filling case of `FilledBlockGoodness`.

Algebra. `FilledBlockGroup p q r s` is the `Monoid.PushoutI` over `Bool`, the shape of K09's
`seamVanKampen`, of the solid-torus group `ℤ` (`false`) and `F(a, b) × ℤ` (`true`, `h` the
generator of `ℤ`) over the seam group `ℤ × ℤ` (meridian, longitude): `filledBlockEdge` sends the
meridian to `1`, resp. `a^p h^q`, and the longitude to the generator, resp. `a^r h^s`; so it is
`⟨a, b, h | h central, a^p h^q⟩`. Instead of normal forms in `ℤ/p ∗ ℤ` the ports are detected
abelianly: `filledBlockAbelianization` (`a ↦ (-q, 0)`, `b ↦ (0, 1)`, `h ↦ (p, 0)`, the solid
generator `↦ (ps - qr, 0)`) is well defined (`filledBlockDetect_comp`), and the free port
`filledBlockPort w : (m, n) ↦ (w^m, h^n)` composed with it is `(m, n) ↦ (α m + p n, β m)`, `β` the
`b`-exponent of `w` (`bExponent`). Hence `filledBlockPort_injective` for `p ≠ 0` and `β ≠ 0`,
in particular for `w = b` and `w = ab` (`filledBlockPort_b_injective`,
`filledBlockPort_ab_injective`); `p ≥ 2` is not needed. `injective_pushoutI_of_comp` is the
general detection principle.

Topology. `exists_hom_of_openCover`: homomorphisms out of the π₁ of two open sets agreeing on the
intersection extend to π₁ of the union (`fundamentalGroupEquivAmalgamatedProduct`, then
`Monoid.PushoutI.lift`); `exists_seamHom` is the seam version, compatibility tested on the seam
torus. `injective_map_comp_of_hom` moves injectivity through such an extension at any basepoint.
For one separating seam with distinct sides, each piece lies in its region once `W` is connected
(`pieceImage_left_subset_leftRegion`, via `compl_seamSurface_eq`), so the region retractions of
`TwoSolidTori.lean` exist without its hypothesis `externalCount = 0`
(`exists_leftRegionRetraction`, `regionEquivPiece_of_connectedSpace`). Torus maps are compared by
K02's `torusMapMatrix`: equal matrices give equal `torusAut`, nonzero determinant gives
π₁-injectivity at every basepoint (`injective_map_of_det_ne_zero`). `injective_of_torusMaps`: if
maps `ΘL`, `ΘR` from the two pieces to the torus satisfy the seam condition
`M(ΘL ∘ leftPort) = M(ΘR ∘ rightPort ∘ matching)`, every torus map `g` into the right piece with
`det M(ΘR ∘ g) ≠ 0` stays π₁-injective in `W`.

A Seifert block with one filling is connected (`connectedSpace_of_fillingCount_eq_one`), and
`isGoodBlock_of_fillingCount_eq_one` reduces its goodness to two piece maps `ΘS`, `ΘP` with
`M(ΘS ∘ solid port) = M(ΘP ∘ filled port) · torusMatrix(matching)` and `det M(ΘP ∘ free port) ≠ 0`.
The maps themselves (`ΘS = (fibre^{det}, 1)`, `ΘP = (r_f^{-q} · fibre^p, v)`, `r_f` the boundary
retraction of the filled circle, `v` an angle map trivial on it) and their matrices are not
constructed here; they need the degree calculus of circle maps.
-/

set_option autoImplicit false

noncomputable section
open Set Multiplicative
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open DifferentialGeometry.Topology.VanKampen
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

section Detection
variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Monoid (G i)] [Monoid H]
  {φ : ∀ i, H →* G i} {K : Type*} [Monoid K]

theorem injective_pushoutI_of_comp {L : Type*} [Monoid L] (f : ∀ i, G i →* K) (k : H →* K)
    (hf : ∀ i, (f i).comp (φ i) = k) (i : ι) (g : L →* G i)
    (hg : Function.Injective ((f i).comp g)) :
    Function.Injective ((Monoid.PushoutI.of (φ := φ) i).comp g) := by
  intro x y h
  apply hg
  have := congrArg (Monoid.PushoutI.lift f k hf) h
  simpa only [MonoidHom.coe_comp, Function.comp_apply, Monoid.PushoutI.lift_of] using this

end Detection

abbrev SeamGroup := Multiplicative ℤ × Multiplicative ℤ

abbrev filledBlockFactor : Bool → Type
  | false => Multiplicative ℤ
  | true => FreeGroup (Fin 2) × Multiplicative ℤ

instance filledBlockFactorGroup (i : Bool) : Group (filledBlockFactor i) := by
  cases i <;> simp only [filledBlockFactor] <;> infer_instance

def seamLinearForm (x y : ℤ) : SeamGroup →* Multiplicative ℤ :=
  MonoidHom.coprod (zpowersHom _ (ofAdd x)) (zpowersHom _ (ofAdd y))

theorem toAdd_seamLinearForm (x y : ℤ) (g : SeamGroup) :
    toAdd (seamLinearForm x y g) = toAdd g.1 * x + toAdd g.2 * y := by
  simp [seamLinearForm, mul_comm]

def filledBlockEdge (p q r s : ℤ) : ∀ i, SeamGroup →* filledBlockFactor i
  | false => MonoidHom.snd _ _
  | true => MonoidHom.prod ((zpowersHom _ (FreeGroup.of 0)).comp (seamLinearForm p r))
      (seamLinearForm q s)

abbrev FilledBlockGroup (p q r s : ℤ) := Monoid.PushoutI (filledBlockEdge p q r s)

def bExponent : FreeGroup (Fin 2) →* Multiplicative ℤ := FreeGroup.lift ![1, ofAdd 1]

def freeFactorDetect (q : ℤ) : FreeGroup (Fin 2) →* SeamGroup :=
  FreeGroup.lift ![(ofAdd (-q), 1), (1, ofAdd 1)]

theorem snd_freeFactorDetect (q : ℤ) (w : FreeGroup (Fin 2)) :
    (freeFactorDetect q w).2 = bExponent w := by
  change (MonoidHom.snd _ _).comp (freeFactorDetect q) w = bExponent w
  congr 1
  ext i
  fin_cases i <;> rfl

def filledBlockDetect (p q r s : ℤ) : ∀ i, filledBlockFactor i →* SeamGroup
  | false => zpowersHom _ (ofAdd (p * s - q * r), 1)
  | true => MonoidHom.coprod (freeFactorDetect q) (zpowersHom _ (ofAdd p, 1))

def filledBlockSeamDetect (p q r s : ℤ) : SeamGroup →* SeamGroup :=
  (zpowersHom _ (ofAdd (p * s - q * r), 1)).comp (MonoidHom.snd _ _)

theorem filledBlockDetect_comp (p q r s : ℤ) (i : Bool) :
    (filledBlockDetect p q r s i).comp (filledBlockEdge p q r s i) =
      filledBlockSeamDetect p q r s := by
  cases i with
  | false => rfl
  | true =>
    refine MonoidHom.ext fun g => Prod.ext (toAdd.injective ?_) (toAdd.injective ?_)
    · simp [filledBlockDetect, filledBlockEdge, filledBlockSeamDetect, freeFactorDetect,
        toAdd_seamLinearForm]
      ring
    · simp [filledBlockDetect, filledBlockEdge, filledBlockSeamDetect, freeFactorDetect,
        toAdd_seamLinearForm]

def filledBlockAbelianization (p q r s : ℤ) : FilledBlockGroup p q r s →* SeamGroup :=
  Monoid.PushoutI.lift (filledBlockDetect p q r s) (filledBlockSeamDetect p q r s)
    (filledBlockDetect_comp p q r s)

def filledBlockPort (p q r s : ℤ) (w : FreeGroup (Fin 2)) : SeamGroup →* FilledBlockGroup p q r s :=
  (Monoid.PushoutI.of (φ := filledBlockEdge p q r s) true).comp
    ((zpowersHom _ w).prodMap (MonoidHom.id _))

theorem filledBlockPort_injective {p : ℤ} (hp : p ≠ 0) (q r s : ℤ) {w : FreeGroup (Fin 2)}
    (hw : toAdd (bExponent w) ≠ 0) : Function.Injective (filledBlockPort p q r s w) := by
  refine injective_pushoutI_of_comp (filledBlockDetect p q r s) (filledBlockSeamDetect p q r s)
    (filledBlockDetect_comp p q r s) true _ ?_
  intro x y h
  have h1 := congrArg (fun z => toAdd z.1) h
  have h2 := congrArg (fun z => toAdd z.2) h
  simp only [filledBlockDetect, MonoidHom.coe_comp, MonoidHom.coe_prodMap, MonoidHom.coe_id,
    Function.comp_apply, MonoidHom.coprod_apply, Prod.map_fst, zpowersHom_apply, map_zpow,
    Prod.map_snd, id_eq, Prod.pow_mk, one_zpow, Prod.fst_mul, Prod.pow_fst, toAdd_mul, toAdd_zpow,
    Int.zsmul_eq_mul, toAdd_ofAdd, Prod.snd_mul, Prod.pow_snd, snd_freeFactorDetect, mul_one,
    mul_eq_mul_right_iff, EmbeddingLike.apply_eq_iff_eq, toAdd_eq_zero] at h1 h2
  have hx1 : x.1 = y.1 := h2.resolve_right fun he => hw (by rw [he]; rfl)
  rw [hx1] at h1
  have hx2 : toAdd x.2 = toAdd y.2 := mul_right_cancel₀ hp (by linarith)
  exact Prod.ext hx1 (toAdd.injective hx2)

theorem toAdd_bExponent_conj (g w : FreeGroup (Fin 2)) :
    toAdd (bExponent (g * w * g⁻¹)) = toAdd (bExponent w) := by
  simp

theorem toAdd_bExponent_inv (w : FreeGroup (Fin 2)) :
    toAdd (bExponent w⁻¹) = -toAdd (bExponent w) := by
  simp

theorem filledBlockPort_b_injective {p : ℤ} (hp : p ≠ 0) (q r s : ℤ) :
    Function.Injective (filledBlockPort p q r s (FreeGroup.of 1)) :=
  filledBlockPort_injective hp q r s (by simp [bExponent])

theorem filledBlockPort_ab_injective {p : ℤ} (hp : p ≠ 0) (q r s : ℤ) :
    Function.Injective (filledBlockPort p q r s (FreeGroup.of 0 * FreeGroup.of 1)) :=
  filledBlockPort_injective hp q r s (by simp [bExponent])

section OpenCover
variable {X : Type u} [TopologicalSpace X]

private theorem mapOfEq_rfl {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(Y, Z)) (y : Y) :
    FundamentalGroup.mapOfEq f (rfl : f y = f y) = FundamentalGroup.map f y := by
  ext p
  rw [FundamentalGroup.mapOfEq_apply]
  exact Path.Homotopic.Quotient.cast_rfl_rfl _

theorem exists_hom_of_openCover (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (x : ↑(U ∩ V)) [PathConnectedSpace U] [PathConnectedSpace V]
    [PathConnectedSpace (↑(U ∩ V))] {A : Type*} [Monoid A]
    (fL : FundamentalGroup U (interToLeft U V x) →* A)
    (fR : FundamentalGroup V (interToRight U V x) →* A)
    (h : fL.comp (FundamentalGroup.map (interToLeft U V) x) =
      fR.comp (FundamentalGroup.map (interToRight U V) x)) :
    ∃ F : FundamentalGroup X x.1 →* A,
      F.comp (FundamentalGroup.map (subsetToAmbient U) (interToLeft U V x)) = fL ∧
        F.comp (FundamentalGroup.map (subsetToAmbient V) (interToRight U V x)) = fR := by
  let f : ∀ i, fundamentalGroupFactor U V x.1 x.2 i →* A := fun i => match i with
    | false => fL
    | true => fR
  have hf : ∀ i, (f i).comp (fundamentalGroupAmalgamation U V x.1 x.2 i) =
      fL.comp (FundamentalGroup.map (interToLeft U V) x) := by
    intro i
    cases i with
    | false =>
      change fL.comp (FundamentalGroup.mapOfEq (interToLeft U V)
        (rfl : interToLeft U V x = interToLeft U V x)) = _
      rw [mapOfEq_rfl]
    | true =>
      change fR.comp (FundamentalGroup.mapOfEq (interToRight U V)
        (rfl : interToRight U V x = interToRight U V x)) = _
      rw [mapOfEq_rfl]
      exact h.symm
  let e := fundamentalGroupEquivAmalgamatedProduct U V hU hV hcover x.1 x.2
  refine ⟨(Monoid.PushoutI.lift f _ hf).comp e.symm.toMonoidHom, MonoidHom.ext fun g => ?_,
    MonoidHom.ext fun g => ?_⟩
  · change Monoid.PushoutI.lift f _ hf (e.symm (FundamentalGroup.map (subsetToAmbient U)
      (interToLeft U V x) g)) = fL g
    rw [← fundamentalGroupEquivAmalgamatedProduct_of_false U V hU hV hcover x g,
      MulEquiv.symm_apply_apply]
    exact Monoid.PushoutI.lift_of f _ hf (i := false) g
  · change Monoid.PushoutI.lift f _ hf (e.symm (FundamentalGroup.map (subsetToAmbient V)
      (interToRight U V x) g)) = fR g
    rw [← fundamentalGroupEquivAmalgamatedProduct_of_true U V hU hV hcover x g,
      MulEquiv.symm_apply_apply]
    exact Monoid.PushoutI.lift_of f _ hf (i := true) g

theorem injective_map_comp_of_hom {Y T : Type*} [TopologicalSpace Y] [TopologicalSpace T]
    (i : C(Y, X)) (y₀ : Y) {A : Type*} [Monoid A] (F : FundamentalGroup X (i y₀) →* A)
    (fY : FundamentalGroup Y y₀ →* A) (hF : F.comp (FundamentalGroup.map i y₀) = fY)
    (g : C(T, Y)) (t : T) (γ : Path y₀ (g t))
    (hinj : Function.Injective (fY.comp
      ((FundamentalGroup.fundamentalGroupMulEquivOfPath γ).symm.toMonoidHom.comp
        (FundamentalGroup.map g t)))) :
    Function.Injective (FundamentalGroup.map (i.comp g) t) := by
  rw [GC.Topology.fundamentalGroup_map_comp]
  intro a b hab
  apply hinj
  have key : ∀ c, fY ((FundamentalGroup.fundamentalGroupMulEquivOfPath γ).symm c) =
      F ((FundamentalGroup.fundamentalGroupMulEquivOfPath (γ.map i.continuous)).symm
        (FundamentalGroup.map i (g t) c)) := by
    intro c
    obtain ⟨c, rfl⟩ := (FundamentalGroup.fundamentalGroupMulEquivOfPath γ).surjective c
    rw [GC.Topology.fundamentalGroup_map_mulEquivOfPath, MulEquiv.symm_apply_apply,
      MulEquiv.symm_apply_apply, ← hF]
    rfl
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at hab ⊢
  rw [key, key, hab]

end OpenCover

section TorusMatrix

theorem mulVec_injective_of_det_ne_zero {A : Matrix (Fin 2) (Fin 2) ℤ} (h : A.det ≠ 0) :
    Function.Injective A.mulVec := by
  intro v w hvw
  have hc := congrArg A.adjugate.mulVec hvw
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.one_mulVec] at hc
  exact smul_right_injective _ h hc

theorem torusAut_eq_of_torusMapMatrix_eq {f g : C(Torus, Torus)}
    (h : torusMapMatrix f = torusMapMatrix g) : torusAut f = torusAut g := by
  refine MonoidHom.ext fun a => torusCoordinates.injective (toAdd.injective ?_)
  rw [← torusMapMatrix_mulVec, ← torusMapMatrix_mulVec, h]

theorem injective_torusAut_of_det_ne_zero {f : C(Torus, Torus)}
    (h : (torusMapMatrix f).det ≠ 0) : Function.Injective (torusAut f) := by
  intro a b hab
  refine torusCoordinates.injective (toAdd.injective (mulVec_injective_of_det_ne_zero h ?_))
  rw [torusMapMatrix_mulVec, torusMapMatrix_mulVec, hab]

theorem injective_map_of_det_ne_zero {f : C(Torus, Torus)} (h : (torusMapMatrix f).det ≠ 0)
    (x : Torus) : Function.Injective (FundamentalGroup.map f x) := by
  rw [← GC.Topology.injective_fundamentalGroup_map_iff f torusBase x,
    ← GC.Topology.markedMap_injective_iff f torusBase (PathConnectedSpace.somePath _ _)]
  exact injective_torusAut_of_det_ne_zero h

theorem markedMap_comp_map {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (f : C(X, Y)) (g : C(Y, Z)) (x : X) {z : Z} (β : Path z (g (f x))) :
    (GC.Topology.markedMap g (f x) β).comp (FundamentalGroup.map f x) =
      GC.Topology.markedMap (g.comp f) x β := by
  rw [GC.Topology.markedMap, GC.Topology.markedMap, GC.Topology.fundamentalGroup_map_comp,
    MonoidHom.comp_assoc]

end TorusMatrix

namespace TorusPresentation
variable {W : CompactCarrier.{u}} (G : TorusPresentation W) (j : Fin G.pairing.count)

theorem pieceImage_left_subset_leftRegion [ConnectedSpace W.Carrier] (hc : G.pairing.count = 1)
    (hLR : G.leftPiece j ≠ G.rightPiece j) : G.pieceImage (G.leftPiece j) ⊆ G.leftRegion j := by
  intro w hw
  by_cases hS : w ∈ G.seamSurface j
  · exact Or.inr (G.seamSurface_subset_seamCollar j hS)
  · have h : w ∈ (G.seamSurface j)ᶜ := hS
    rw [G.compl_seamSurface_eq j] at h
    rcases h with h | h
    · exact Or.inl h
    · exact (hS (G.pieceImage_inter_pieceComplImage_subset j hc _
        ⟨hw, G.pieceImage_subset_pieceComplImage hLR (G.rightSide_subset_pieceImage j hc h)⟩)).elim

theorem pieceImage_right_subset_rightRegion [ConnectedSpace W.Carrier]
    (hc : G.pairing.count = 1) (hLR : G.leftPiece j ≠ G.rightPiece j) :
    G.pieceImage (G.rightPiece j) ⊆ G.rightRegion j := by
  intro w hw
  by_cases hS : w ∈ G.seamSurface j
  · exact Or.inr (G.seamSurface_subset_seamCollar j hS)
  · have h : w ∈ (G.seamSurface j)ᶜ := hS
    rw [G.compl_seamSurface_eq j] at h
    rcases h with h | h
    · exact (hS (G.pieceImage_inter_pieceComplImage_subset j hc _
        ⟨hw, G.pieceImage_subset_pieceComplImage (Ne.symm hLR)
          (G.leftSide_subset_pieceImage j hc h)⟩)).elim
    · exact Or.inl h

theorem exists_leftRegionRetraction [ConnectedSpace W.Carrier] (hc : G.pairing.count = 1)
    (hLR : G.leftPiece j ≠ G.rightPiece j) :
    ∃ f : C(G.leftRegion j, G.components.piece (G.leftPiece j)),
      (∀ y, Function.Bijective (FundamentalGroup.map f y)) ∧
        ∀ (x : G.components.piece (G.leftPiece j)) (hx : G.cutMap x ∈ G.leftRegion j),
          f ⟨G.cutMap x, hx⟩ = x := by
  have hKK := G.pieceImage_inter_pieceComplImage_subset j hc
  have hSL : G.seamSurface j ⊆ G.pieceImage (G.leftPiece j) := by
    rintro _ ⟨t, rfl⟩
    exact ⟨_, G.left_owned j (G.pairing.leftParam j t).2, (G.seamTorus_eq_cutMap j t).symm⟩
  exact G.exists_regionRetraction j hc (G.leftPiece j) (G.leftRegion j)
    (G.injOn_cutMap j hc hLR _) hSL (G.pieceImage_left_subset_leftRegion j hc hLR)
    subset_union_right (fun w hw => hw.1.elim (fun h => G.seamSurface_subset_seamCollar j
      (hKK _ ⟨G.leftSide_subset_pieceImage j hc h, hw.2⟩)) id)

theorem exists_rightRegionRetraction [ConnectedSpace W.Carrier] (hc : G.pairing.count = 1)
    (hLR : G.leftPiece j ≠ G.rightPiece j) :
    ∃ f : C(G.rightRegion j, G.components.piece (G.rightPiece j)),
      (∀ y, Function.Bijective (FundamentalGroup.map f y)) ∧
        ∀ (x : G.components.piece (G.rightPiece j)) (hx : G.cutMap x ∈ G.rightRegion j),
          f ⟨G.cutMap x, hx⟩ = x := by
  have hKK := G.pieceImage_inter_pieceComplImage_subset j hc
  have hSR : G.seamSurface j ⊆ G.pieceImage (G.rightPiece j) := by
    rintro _ ⟨t, rfl⟩
    exact ⟨_, G.right_owned j (G.pairing.rightParam j _).2,
      (G.seamTorus_eq_cutMap_right j t).symm⟩
  exact G.exists_regionRetraction j hc (G.rightPiece j) (G.rightRegion j)
    (G.injOn_cutMap j hc hLR _) hSR (G.pieceImage_right_subset_rightRegion j hc hLR)
    subset_union_right (fun w hw => hw.1.elim (fun h => G.seamSurface_subset_seamCollar j
      (hKK _ ⟨G.rightSide_subset_pieceImage j hc h, hw.2⟩)) id)

theorem leftRegionRetraction_seamTorus {f : C(G.leftRegion j, G.components.piece (G.leftPiece j))}
    (hf : ∀ (x : G.components.piece (G.leftPiece j)) (hx : G.cutMap x ∈ G.leftRegion j),
      f ⟨G.cutMap x, hx⟩ = x) : f.comp (G.seamTorusToLeft j) = G.leftPortTorus j := by
  refine ContinuousMap.ext fun t => ?_
  let x : G.components.piece (G.leftPiece j) :=
    ⟨G.pairing.leftParam j t, G.left_owned j (G.pairing.leftParam j t).2⟩
  have hx : G.seamTorusToLeft j t = ⟨G.cutMap x, (G.seamTorus_eq_cutMap j t) ▸
      (G.seamTorusToLeft j t).2⟩ :=
    Subtype.ext (G.seamTorus_eq_cutMap j t)
  rw [ContinuousMap.comp_apply, hx, hf]
  exact Subtype.ext (G.leftPortTorus_apply j t).symm

theorem rightRegionRetraction_seamTorus
    {f : C(G.rightRegion j, G.components.piece (G.rightPiece j))}
    (hf : ∀ (x : G.components.piece (G.rightPiece j)) (hx : G.cutMap x ∈ G.rightRegion j),
      f ⟨G.cutMap x, hx⟩ = x) :
    f.comp (G.seamTorusToRight j) = (G.rightPortTorus j).comp (G.matchingMap j) := by
  refine ContinuousMap.ext fun t => ?_
  let x : G.components.piece (G.rightPiece j) :=
    ⟨G.pairing.rightParam j (G.pairing.matching j t),
      G.right_owned j (G.pairing.rightParam j _).2⟩
  have hx : G.seamTorusToRight j t = ⟨G.cutMap x, (G.seamTorus_eq_cutMap_right j t) ▸
      (G.seamTorusToRight j t).2⟩ :=
    Subtype.ext (G.seamTorus_eq_cutMap_right j t)
  rw [ContinuousMap.comp_apply, hx, hf]
  exact Subtype.ext (G.rightPortTorus_apply j _).symm

theorem regionEquivPiece_of_connectedSpace [ConnectedSpace W.Carrier] (hc : G.pairing.count = 1)
    (hLR : G.leftPiece j ≠ G.rightPiece j) : G.RegionEquivPiece j := by
  obtain ⟨f, hf, hfx⟩ := G.exists_leftRegionRetraction j hc hLR
  obtain ⟨g, hg, hgx⟩ := G.exists_rightRegionRetraction j hc hLR
  exact ⟨⟨f, hf, G.leftRegionRetraction_seamTorus j hfx⟩,
    ⟨g, hg, G.rightRegionRetraction_seamTorus j hgx⟩⟩

theorem exists_seamHom [ConnectedSpace W.Carrier] (h : G.IsSeparating j) (t : Torus)
    {A : Type*} [Monoid A]
    (fL : FundamentalGroup (G.leftRegion j) (G.seamTorusToLeft j t) →* A)
    (fR : FundamentalGroup (G.rightRegion j) (G.seamTorusToRight j t) →* A)
    (hLR : fL.comp (FundamentalGroup.map (G.seamTorusToLeft j) t) =
      fR.comp (FundamentalGroup.map (G.seamTorusToRight j) t)) :
    ∃ F : FundamentalGroup W.Carrier (G.seamTorus j t) →* A,
      F.comp (FundamentalGroup.map (subsetToAmbient (G.leftRegion j)) (G.seamTorusToLeft j t)) =
          fL ∧
        F.comp (FundamentalGroup.map (subsetToAmbient (G.rightRegion j))
          (G.seamTorusToRight j t)) = fR := by
  have := G.pathConnectedSpace_inter j h
  have hinter := G.leftRegion_inter_rightRegion j h
  let x : ↑(G.leftRegion j ∩ G.rightRegion j) := G.seamTorusIn j _ hinter.ge t
  have hsurj := (G.bijective_seamTorusIn j _ hinter t).2
  refine exists_hom_of_openCover _ _ (G.isOpen_leftRegion j) (G.isOpen_rightRegion j)
    (G.leftRegion_union_rightRegion j) x fL fR (MonoidHom.ext fun c => ?_)
  obtain ⟨c, rfl⟩ := hsurj c
  have h1 : FundamentalGroup.map (interToLeft (G.leftRegion j) (G.rightRegion j)) x
      (FundamentalGroup.map (G.seamTorusIn j _ hinter.ge) t c) =
        FundamentalGroup.map (G.seamTorusToLeft j) t c :=
    (congrArg (fun φ => φ c) (GC.Topology.fundamentalGroup_map_comp
      (G.seamTorusIn j _ hinter.ge) (interToLeft (G.leftRegion j) (G.rightRegion j)) t)).symm
  have h2 : FundamentalGroup.map (interToRight (G.leftRegion j) (G.rightRegion j)) x
      (FundamentalGroup.map (G.seamTorusIn j _ hinter.ge) t c) =
        FundamentalGroup.map (G.seamTorusToRight j) t c :=
    (congrArg (fun φ => φ c) (GC.Topology.fundamentalGroup_map_comp
      (G.seamTorusIn j _ hinter.ge) (interToRight (G.leftRegion j) (G.rightRegion j)) t)).symm
  change fL (FundamentalGroup.map (interToLeft (G.leftRegion j) (G.rightRegion j)) x
      (FundamentalGroup.map (G.seamTorusIn j _ hinter.ge) t c)) =
    fR (FundamentalGroup.map (interToRight (G.leftRegion j) (G.rightRegion j)) x
      (FundamentalGroup.map (G.seamTorusIn j _ hinter.ge) t c))
  rw [h1, h2]
  exact congrArg (fun φ => φ c) hLR

def pieceToCarrier (i : Fin G.components.count) : C(G.components.piece i, W.Carrier) :=
  ⟨fun y => G.cutMap y, G.continuous_cutMap.comp continuous_subtype_val⟩

theorem injective_of_torusMaps [ConnectedSpace W.Carrier] (hc : G.pairing.count = 1)
    (hLR : G.leftPiece j ≠ G.rightPiece j)
    (ΘL : C(G.components.piece (G.leftPiece j), Torus))
    (ΘR : C(G.components.piece (G.rightPiece j), Torus))
    (hseam : torusMapMatrix (ΘL.comp (G.leftPortTorus j)) =
      torusMapMatrix ((ΘR.comp (G.rightPortTorus j)).comp (G.matchingMap j)))
    (g : C(Torus, G.components.piece (G.rightPiece j)))
    (hg : (torusMapMatrix (ΘR.comp g)).det ≠ 0) (x : Torus) :
    Function.Injective (FundamentalGroup.map ((G.pieceToCarrier (G.rightPiece j)).comp g) x) := by
  have hsep := G.isSeparating_of_count_eq_one j hc hLR
  obtain ⟨fU, -, hfU⟩ := G.exists_leftRegionRetraction j hc hLR
  obtain ⟨fV, -, hfV⟩ := G.exists_rightRegionRetraction j hc hLR
  let fL := GC.Topology.markedMap (ΘL.comp fU) (G.seamTorusToLeft j torusBase)
    (PathConnectedSpace.somePath torusBase _)
  let fR := GC.Topology.markedMap (ΘR.comp fV) (G.seamTorusToRight j torusBase)
    (PathConnectedSpace.somePath torusBase _)
  have hL : fL.comp (FundamentalGroup.map (G.seamTorusToLeft j) torusBase) =
      torusAut (ΘL.comp (G.leftPortTorus j)) := by
    rw [markedMap_comp_map, ← torusAut_eq, ContinuousMap.comp_assoc,
      G.leftRegionRetraction_seamTorus j hfU]
  have hR : fR.comp (FundamentalGroup.map (G.seamTorusToRight j) torusBase) =
      torusAut ((ΘR.comp (G.rightPortTorus j)).comp (G.matchingMap j)) := by
    rw [markedMap_comp_map, ← torusAut_eq, ContinuousMap.comp_assoc,
      G.rightRegionRetraction_seamTorus j hfV, ContinuousMap.comp_assoc]
  obtain ⟨F, -, hF⟩ := G.exists_seamHom j hsep torusBase fL fR
    (by rw [hL, hR, torusAut_eq_of_torusMapMatrix_eq hseam])
  have hmem : ∀ y : G.components.piece (G.rightPiece j), G.cutMap y ∈ G.rightRegion j :=
    fun y => G.pieceImage_right_subset_rightRegion j hc hLR ⟨y, y.2, rfl⟩
  let g' : C(Torus, G.rightRegion j) :=
    ⟨fun t => ⟨G.cutMap (g t), hmem (g t)⟩,
      ((G.pieceToCarrier (G.rightPiece j)).comp g).continuous.subtype_mk _⟩
  have hg' : (ΘR.comp fV).comp g' = ΘR.comp g :=
    ContinuousMap.ext fun t => congrArg ΘR (hfV (g t) (hmem (g t)))
  have hinj : Function.Injective (FundamentalGroup.map ((ΘR.comp fV).comp g') x) := by
    rw [hg']
    exact injective_map_of_det_ne_zero hg x
  change Function.Injective
    (FundamentalGroup.map ((subsetToAmbient (G.rightRegion j)).comp g') x)
  let γ := PathConnectedSpace.somePath (G.seamTorusToRight j torusBase) (g' x)
  refine injective_map_comp_of_hom (subsetToAmbient (G.rightRegion j))
    (G.seamTorusToRight j torusBase) F fR hF g' x γ fun a b hab => ?_
  have key : ∀ c, FundamentalGroup.map (ΘR.comp fV) (G.seamTorusToRight j torusBase)
      ((FundamentalGroup.fundamentalGroupMulEquivOfPath γ).symm c) =
      (FundamentalGroup.fundamentalGroupMulEquivOfPath (γ.map (ΘR.comp fV).continuous)).symm
        (FundamentalGroup.map (ΘR.comp fV) (g' x) c) := by
    intro c
    obtain ⟨c, rfl⟩ := (FundamentalGroup.fundamentalGroupMulEquivOfPath γ).surjective c
    rw [GC.Topology.fundamentalGroup_map_mulEquivOfPath, MulEquiv.symm_apply_apply,
      MulEquiv.symm_apply_apply]
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at hab
  change (fundamentalGroupChangeBasepoint _) (FundamentalGroup.map (ΘR.comp fV) _ _) =
    (fundamentalGroupChangeBasepoint _) (FundamentalGroup.map (ΘR.comp fV) _ _) at hab
  rw [key, key] at hab
  have hab' := (FundamentalGroup.fundamentalGroupMulEquivOfPath _).symm.injective
    ((fundamentalGroupChangeBasepoint _).injective hab)
  apply hinj
  rw [GC.Topology.fundamentalGroup_map_comp, MonoidHom.comp_apply, MonoidHom.comp_apply]
  exact hab'

theorem injective_of_torusMaps_of_eq [ConnectedSpace W.Carrier] (hc : G.pairing.count = 1)
    {iL iR : Fin G.components.count} (hiL : G.leftPiece j = iL) (hiR : G.rightPiece j = iR)
    (hLR : iL ≠ iR) (ΘL : C(G.components.piece iL, Torus)) (ΘR : C(G.components.piece iR, Torus))
    (PL : C(Torus, G.components.piece iL))
    (hPL : ∀ t, (PL t : G.cutCarrier.Carrier) = G.pairing.leftParam j t)
    (PR : C(Torus, G.components.piece iR))
    (hPR : ∀ t, (PR t : G.cutCarrier.Carrier) = G.pairing.rightParam j t)
    (hseam : torusMapMatrix (ΘL.comp PL) =
      torusMapMatrix (ΘR.comp PR) * torusMatrix (G.pairing.matching j))
    (g : C(Torus, G.components.piece iR)) (hg : (torusMapMatrix (ΘR.comp g)).det ≠ 0)
    (x : Torus) :
    Function.Injective (FundamentalGroup.map ((G.pieceToCarrier iR).comp g) x) := by
  subst hiL hiR
  have hL : PL = G.leftPortTorus j :=
    ContinuousMap.ext fun t => Subtype.ext ((hPL t).trans (G.leftPortTorus_apply j t).symm)
  have hR : PR = G.rightPortTorus j :=
    ContinuousMap.ext fun t => Subtype.ext ((hPR t).trans (G.rightPortTorus_apply j t).symm)
  subst hL hR
  refine G.injective_of_torusMaps j hc hLR ΘL ΘR ?_ g hg x
  rw [hseam, torusMapMatrix_comp]
  rfl

theorem connectedSpace_of_forall_piece (hcover : ∀ i, i = G.leftPiece j ∨ i = G.rightPiece j) :
    ConnectedSpace W.Carrier := by
  have himage : ∀ i, IsConnected (G.pieceImage i) := fun i =>
    (isConnected_iff_connectedSpace.mpr (G.components.connected i)).image _
      G.continuous_cutMap.continuousOn
  have hI : (G.pieceImage (G.leftPiece j) ∩ G.pieceImage (G.rightPiece j)).Nonempty :=
    ⟨G.seamTorus j torusBase,
      ⟨_, G.left_owned j (G.pairing.leftParam j _).2, (G.seamTorus_eq_cutMap j _).symm⟩,
      ⟨_, G.right_owned j (G.pairing.rightParam j _).2, (G.seamTorus_eq_cutMap_right j _).symm⟩⟩
  have hU : G.pieceImage (G.leftPiece j) ∪ G.pieceImage (G.rightPiece j) = univ := by
    refine eq_univ_of_forall fun w => ?_
    obtain ⟨x, rfl⟩ := G.surjective_cutMap w
    obtain ⟨i, hi⟩ := mem_iUnion.1 (G.components.covers.symm ▸ mem_univ x)
    rcases hcover i with rfl | rfl
    · exact Or.inl ⟨x, hi, rfl⟩
    · exact Or.inr ⟨x, hi, rfl⟩
  rw [connectedSpace_iff_univ, ← hU]
  exact (himage _).union hI (himage _)

end TorusPresentation

namespace ProductFibredPiece

variable {W : CompactCarrier.{u}} {T : TorusPresentation.{u} W} {i : Fin T.components.count}
  {k : ℕ}

theorem portMap_val (P : ProductFibredPiece T i k) (a : Fin k) (t : Torus) :
    (P.portMap a t : T.cutCarrier.Carrier) = T.sideCollar (P.port a).val (t, halfZero) := by
  have h := T.pieceBoundaryTori_torusMap i (Fintype.equivFin _ (P.port a)) t
  rw [Equiv.symm_apply_apply] at h
  rw [← P.pieceBoundaryTori_boundaryMap a]
  exact h

end ProductFibredPiece

namespace SeifertBlock

variable {W : CompactCarrier.{u}} {d : SeifertData}

theorem leftPiece_seam (B : SeifertBlock W d) (m : Fin d.fillingCount) :
    B.presentation.leftPiece (B.seam m) = B.piece (some m) := by
  have h := ((B.solid m).port 0).property
  rw [B.solid_port] at h
  exact h

theorem rightPiece_seam (B : SeifertBlock W d) (m : Fin d.fillingCount) :
    B.presentation.rightPiece (B.seam m) = B.piece none := by
  have h := (B.product.port (B.port (.inr m))).property
  rw [B.filled_port] at h
  exact h

theorem connectedSpace_of_fillingCount_eq_one (B : SeifertBlock W d)
    (hd : d.fillingCount = 1) : ConnectedSpace W.Carrier := by
  let m : Fin d.fillingCount := ⟨0, by omega⟩
  refine B.presentation.connectedSpace_of_forall_piece (B.seam m) fun i => ?_
  rw [B.leftPiece_seam, B.rightPiece_seam, ← B.piece.apply_symm_apply i]
  rcases B.piece.symm i with _ | m'
  · exact Or.inr rfl
  · exact Or.inl (congrArg (fun n => B.piece (some n)) (Fin.ext (by omega)))

theorem isGoodBlock_of_fillingCount_eq_one (B : SeifertBlock W d) (hd : d.fillingCount = 1)
    (ΘS : C(B.presentation.components.piece (B.piece (some ⟨0, by omega⟩)), Torus))
    (ΘP : C(B.presentation.components.piece (B.piece none), Torus))
    (hseam : torusMapMatrix (ΘS.comp ((B.solid ⟨0, by omega⟩).portMap 0)) =
      torusMapMatrix (ΘP.comp (B.product.portMap (B.port (.inr ⟨0, by omega⟩)))) *
        torusMatrix (B.presentation.pairing.matching (B.seam ⟨0, by omega⟩)))
    (hport : ∀ r, (torusMapMatrix (ΘP.comp (B.product.portMap (B.port (.inl r))))).det ≠ 0) :
    B.IsGoodBlock := by
  have := B.connectedSpace_of_fillingCount_eq_one hd
  refine B.isGoodBlock_iff.2 fun r x => ?_
  rw [B.external_boundaryMap_free r]
  refine B.presentation.injective_of_torusMaps_of_eq (B.seam ⟨0, by omega⟩)
    (B.pairing_count.trans hd) (B.leftPiece_seam _) (B.rightPiece_seam _)
    (fun h => Option.some_ne_none _ (B.piece.injective h)) ΘS ΘP _ (fun t => ?_) _
    (fun t => ?_) hseam _ (hport r) x
  · rw [ProductFibredPiece.portMap_val, B.solid_port]
    exact B.presentation.pairing.left_zero _ t
  · rw [ProductFibredPiece.portMap_val, B.filled_port]
    exact B.presentation.pairing.right_zero _ t

end SeifertBlock

end GC.Seifert
