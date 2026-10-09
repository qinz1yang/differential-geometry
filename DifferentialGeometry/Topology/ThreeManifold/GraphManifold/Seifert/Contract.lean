import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RestrictCarrier

/-!
# Contracting a set of pieces of a torus presentation

Chapter 6, P2a (the contract half of the relative replacement P2). For a torus presentation `T`
of `W`, a finset `S` of pieces owning no external torus of `W` (`hext`, automatic when `W` is
closed), a cut carrier with boundary (`hk : T.cutCarrier.kind = .withBoundary`) and an S region
whose interior `range \ crossingSurface` is connected (`hconn`), `T.contract S hext hk hconn` is a
torus presentation of the same `W` in which the pieces of `S` are merged into one piece.

The new cut carrier `contractCut` is the disjoint sum of the cut pieces not in `S`
(`subCarrier Sᶜ`) and the S region of K22b (`restrictCarrier`, recast to the kind of the cut
carrier by `recastCarrier`), oriented by pullback along the fold map `contractFold` (the cut map
on the first summand, the inclusion on the second), whose differential is bijective everywhere
(`mfderiv_contractFold_bijective`). The pieces are those not in `S` and the S region
(`contractComponents`, the region last); a piece is connected because its interior is
(`range_subset_closure_diff_crossing`). `contractMap` sends the cut carrier of `T` to the new
one (identity off `S`, the cut map on `S`), and `contractFold ∘ contractMap` is the cut map.

The seams are those of `T` not internal to `S` (`NonInternal`); a side in `S` has as collar the
half collar of the crossing seam in seam coordinates (K22b), a side not in `S` keeps its collar
(`contractLeftCollar`, `contractRightCollar`, `sumInlPD`, `sumInrPD`). The boundary reversal is
transferred from `T` through the two orientation-compatible fold maps
(`collar_orientation_transfer`). The external tori are those of `T`. The gluing is equivariant
for `contractMap` (`contractMap_flip`), so `contractFold` descends to a homeomorphism from the
quotient onto `W` (`contractReconstruction`), and the interior diffeomorphism is the fold map on
the interior, an injective local diffeomorphism (`isLocalDiffeomorph_contractInteriorFold`).
Counts: `contract_components_count`, `contract_pairing_count`, `contract_externalCount`; the
reconstruction is unchanged (`contract_reconstruction_eq`).
-/

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

def recastCarrier (C : CompactCarrier.{u}) (k : CarrierModel) (h : C.kind = k) :
    CompactCarrier.{u} where
  kind := k
  Carrier := C.Carrier
  charts := h ▸ C.charts
  smooth := by
    subst h
    exact C.smooth
  orientation := by
    subst h
    exact C.orientation

section Recast
variable {F G X : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
  {J : ModelWithCorners ℝ F G} [TopologicalSpace X] [ChartedSpace G X]

theorem recast_contMDiff_iff_left (C : CompactCarrier.{u}) (k : CarrierModel) (h : C.kind = k)
    (f : (recastCarrier C k h).Carrier → X) :
    ContMDiff (recastCarrier C k h).model J ∞ f ↔
      ContMDiff C.model J ∞ (fun x : C.Carrier => f x) := by
  subst h
  exact Iff.rfl

theorem recast_contMDiffOn_iff_right (C : CompactCarrier.{u}) (k : CarrierModel)
    (h : C.kind = k) (f : X → (recastCarrier C k h).Carrier) (s : Set X) :
    ContMDiffOn J (recastCarrier C k h).model ∞ f s ↔
      ContMDiffOn J C.model ∞ (fun x => @id C.Carrier (f x)) s := by
  subst h
  exact Iff.rfl

theorem recast_contMDiff_iff_right (C : CompactCarrier.{u}) (k : CarrierModel)
    (h : C.kind = k) (f : X → (recastCarrier C k h).Carrier) :
    ContMDiff J (recastCarrier C k h).model ∞ f ↔
      ContMDiff J C.model ∞ (fun x => @id C.Carrier (f x)) := by
  subst h
  exact Iff.rfl

theorem recast_mfderiv_left (C : CompactCarrier.{u}) (k : CarrierModel) (h : C.kind = k)
    (f : (recastCarrier C k h).Carrier → X) (x : (recastCarrier C k h).Carrier) :
    @Eq (EuclideanSpace ℝ (Fin 3) →L[ℝ] F) (mfderiv (recastCarrier C k h).model J f x)
      (mfderiv C.model J (fun x : C.Carrier => f x) x) := by
  subst h
  rfl

theorem recast_isBoundaryPoint_iff (C : CompactCarrier.{u}) (k : CarrierModel)
    (h : C.kind = k) (x : (recastCarrier C k h).Carrier) :
    (recastCarrier C k h).model.IsBoundaryPoint x ↔ C.model.IsBoundaryPoint (@id C.Carrier x) := by
  subst h
  exact Iff.rfl

theorem recast_isLocalDiffeomorphAt_iff (C : CompactCarrier.{u}) (k : CarrierModel)
    (h : C.kind = k) [IsManifold J ∞ X] (f : (recastCarrier C k h).Carrier → X)
    (x : (recastCarrier C k h).Carrier) :
    IsLocalDiffeomorphAt (recastCarrier C k h).model J ∞ f x ↔
      IsLocalDiffeomorphAt C.model J ∞ (fun y : C.Carrier => f y) x := by
  subst h
  exact Iff.rfl

def recastPD (C : CompactCarrier.{u}) (k : CarrierModel) (h : C.kind = k)
    (φ : PartialDiffeomorph J C.model X C.Carrier ∞) :
    PartialDiffeomorph J (recastCarrier C k h).model X (recastCarrier C k h).Carrier ∞ := by
  subst h
  exact φ

theorem recastPD_apply (C : CompactCarrier.{u}) (k : CarrierModel) (h : C.kind = k)
    (φ : PartialDiffeomorph J C.model X C.Carrier ∞) (p : X) :
    (recastPD C k h φ p : C.Carrier) = φ p := by
  subst h
  rfl

theorem recastPD_source (C : CompactCarrier.{u}) (k : CarrierModel) (h : C.kind = k)
    (φ : PartialDiffeomorph J C.model X C.Carrier ∞) :
    (recastPD C k h φ).source = φ.source := by
  subst h
  rfl

theorem recastPD_target (C : CompactCarrier.{u}) (k : CarrierModel) (h : C.kind = k)
    (φ : PartialDiffeomorph J C.model X C.Carrier ∞) :
    ((recastPD C k h φ).target : Set C.Carrier) = φ.target := by
  subst h
  rfl

end Recast

section SumHelpers
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M M' : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace M'] [ChartedSpace H M']
  {F G N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
  {J : ModelWithCorners ℝ F G} [TopologicalSpace N] [ChartedSpace G N]

theorem contMDiffAt_of_comp_inl {f : M ⊕ M' → N} {a : M}
    (h : ContMDiffAt I J ∞ (f ∘ Sum.inl) a) : ContMDiffAt I J ∞ f (Sum.inl a) := by
  have hr : ContMDiff I I ∞ (Sum.elim id (fun _ => a) : M ⊕ M' → M) :=
    ContMDiff.sumElim contMDiff_id contMDiff_const
  have h1 : ContMDiffAt I J ∞ ((f ∘ Sum.inl) ∘ (Sum.elim id (fun _ => a) : M ⊕ M' → M))
      (Sum.inl a) := h.comp (Sum.inl a) (hr _)
  apply h1.congr_of_eventuallyEq
  filter_upwards [isOpen_range_inl.mem_nhds (Set.mem_range_self a)] with y hy
  obtain ⟨b, rfl⟩ := hy
  rfl

theorem contMDiffAt_of_comp_inr {f : M ⊕ M' → N} {a : M'}
    (h : ContMDiffAt I J ∞ (f ∘ Sum.inr) a) : ContMDiffAt I J ∞ f (Sum.inr a) := by
  have hr : ContMDiff I I ∞ (Sum.elim (fun _ => a) id : M ⊕ M' → M') :=
    ContMDiff.sumElim contMDiff_const contMDiff_id
  have h1 : ContMDiffAt I J ∞ ((f ∘ Sum.inr) ∘ (Sum.elim (fun _ => a) id : M ⊕ M' → M'))
      (Sum.inr a) := h.comp (Sum.inr a) (hr _)
  apply h1.congr_of_eventuallyEq
  filter_upwards [isOpen_range_inr.mem_nhds (Set.mem_range_self a)] with y hy
  obtain ⟨b, rfl⟩ := hy
  rfl

def sumInlPD (φ : PartialDiffeomorph J I N M ∞) (x0 : N) :
    PartialDiffeomorph J I N (M ⊕ M') ∞ where
  toFun p := Sum.inl (φ p)
  invFun := Sum.elim φ.symm (fun _ => x0)
  source := φ.source
  target := Sum.inl '' φ.target
  map_source' p hp := ⟨φ p, φ.map_source' hp, rfl⟩
  map_target' := by
    rintro _ ⟨b, hb, rfl⟩
    exact φ.map_target' hb
  left_inv' p hp := φ.left_inv' hp
  right_inv' := by
    rintro _ ⟨b, hb, rfl⟩
    exact congrArg Sum.inl (φ.right_inv' hb)
  open_source := φ.open_source
  open_target := isOpenMap_inl _ φ.open_target
  contMDiffOn_toFun := (ContMDiff.inl : ContMDiff I I ∞ (@Sum.inl M M')).comp_contMDiffOn
    φ.contMDiffOn_toFun
  contMDiffOn_invFun := by
    rintro _ ⟨b, hb, rfl⟩
    exact (contMDiffAt_of_comp_inl ((φ.contMDiffOn_invFun.contMDiffAt
      (φ.open_target.mem_nhds hb)))).contMDiffWithinAt

def sumInrPD (φ : PartialDiffeomorph J I N M' ∞) (x0 : N) :
    PartialDiffeomorph J I N (M ⊕ M') ∞ where
  toFun p := Sum.inr (φ p)
  invFun := Sum.elim (fun _ => x0) φ.symm
  source := φ.source
  target := Sum.inr '' φ.target
  map_source' p hp := ⟨φ p, φ.map_source' hp, rfl⟩
  map_target' := by
    rintro _ ⟨b, hb, rfl⟩
    exact φ.map_target' hb
  left_inv' p hp := φ.left_inv' hp
  right_inv' := by
    rintro _ ⟨b, hb, rfl⟩
    exact congrArg Sum.inr (φ.right_inv' hb)
  open_source := φ.open_source
  open_target := isOpenMap_inr _ φ.open_target
  contMDiffOn_toFun := (ContMDiff.inr : ContMDiff I I ∞ (@Sum.inr M M')).comp_contMDiffOn
    φ.contMDiffOn_toFun
  contMDiffOn_invFun := by
    rintro _ ⟨b, hb, rfl⟩
    exact (contMDiffAt_of_comp_inr ((φ.contMDiffOn_invFun.contMDiffAt
      (φ.open_target.mem_nhds hb)))).contMDiffWithinAt

end SumHelpers

section Transfer
variable {W C C' : CompactCarrier.{u}} (F : C.Carrier → W.Carrier) (F' : C'.Carrier → W.Carrier)

theorem collar_orientation_transfer
    (hF : ∀ x, ∃ A : TangentSpace C.model x ≃ₗ[ℝ] TangentSpace W.model (F x),
      (∀ v, A v = mfderiv C.model W.model F x v) ∧
      Orientation.map (Fin 3) A (C.orientation.orientation x) = W.orientation.orientation (F x))
    (hF' : ∀ x, ∃ A : TangentSpace C'.model x ≃ₗ[ℝ] TangentSpace W.model (F' x),
      (∀ v, A v = mfderiv C'.model W.model F' x v) ∧
      Orientation.map (Fin 3) A (C'.orientation.orientation x) = W.orientation.orientation (F' x))
    (hFd : ∀ x, MDifferentiableAt C.model W.model F x)
    (hF'd : ∀ x, MDifferentiableAt C'.model W.model F' x)
    {f : Torus × EuclideanHalfSpace 1 → C.Carrier} {f' : Torus × EuclideanHalfSpace 1 → C'.Carrier}
    {p : Torus × EuclideanHalfSpace 1} (hfd : MDifferentiableAt halfCollarModel C.model f p)
    (hf'd : MDifferentiableAt halfCollarModel C'.model f' p)
    (hff : F' ∘ f' =ᶠ[𝓝 p] F ∘ f)
    (L : TangentSpace halfCollarModel p ≃ₗ[ℝ] TangentSpace C.model (f p))
    (hL : ∀ v, L v = mfderiv halfCollarModel C.model f p v) :
    ∃ L' : TangentSpace halfCollarModel p ≃ₗ[ℝ] TangentSpace C'.model (f' p),
      (∀ v, L' v = mfderiv halfCollarModel C'.model f' p v) ∧
      Orientation.map (Fin 3) L'.symm (C'.orientation.orientation (f' p)) =
        Orientation.map (Fin 3) L.symm (C.orientation.orientation (f p)) := by
  obtain ⟨A, hA, hoA⟩ := hF (f p)
  obtain ⟨A', hA', hoA'⟩ := hF' (f' p)
  have hpt : F' (f' p) = F (f p) := hff.eq_of_nhds
  have hc1 := mfderiv_comp p (hF'd (f' p)) hf'd
  have hc2 := mfderiv_comp p (hFd (f p)) hfd
  have key : ∀ v, A' (mfderiv halfCollarModel C'.model f' p v) = A (L v) := by
    intro v
    have e1 : A' (mfderiv halfCollarModel C'.model f' p v) =
        mfderiv halfCollarModel W.model (F' ∘ f') p v := by
      rw [hA', hc1]
      rfl
    have e2 : A (L v) = mfderiv halfCollarModel W.model (F ∘ f) p v := by
      rw [hL, hA, hc2]
      rfl
    have e3 := congrArg (fun T => T v)
      (Filter.EventuallyEq.mfderiv_eq (I := halfCollarModel) (I' := W.model) hff)
    exact e1.trans (e3.trans e2.symm)
  refine ⟨L.trans (A.trans A'.symm), fun v => ?_, ?_⟩
  · change A'.symm (A (L v)) = _
    rw [← key v]
    exact A'.symm_apply_apply _
  · have e1 : ∀ o, Orientation.map (Fin 3) (L.trans (A.trans A'.symm)).symm o =
        Orientation.map (Fin 3) L.symm
          (Orientation.map (Fin 3) A.symm (Orientation.map (Fin 3) A' o)) := by
      intro o
      induction o using Module.Ray.ind with
      | h v hv => rfl
    have e2 : Orientation.map (Fin 3) A.symm (Orientation.map (Fin 3) A
        (C.orientation.orientation (f p))) = C.orientation.orientation (f p) := by
      rw [← Orientation.map_symm]
      exact (Orientation.map (Fin 3) A).symm_apply_apply _
    have h3 : W.orientation.orientation (F' (f' p)) =
        Orientation.map (Fin 3) A (C.orientation.orientation (f p)) := by
      rw [hoA, hpt]
    rw [e1, hoA', h3, e2]

end Transfer

namespace TorusPresentation
variable {W : CompactCarrier.{u}} (T : TorusPresentation W)
  (S : Finset (Fin T.components.count))

def contractRegion (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) : CompactCarrier.{u} :=
  recastCarrier (T.restrictCarrier S hext) T.cutCarrier.kind hk.symm

instance subCarrierChartsKind (S' : Finset (Fin T.components.count)) :
    ChartedSpace T.cutCarrier.kind.Space (T.subCarrier S').Carrier :=
  (T.subCarrier S').charts

instance subCarrierSmoothKind (S' : Finset (Fin T.components.count)) :
    IsManifold T.cutCarrier.model ∞ (T.subCarrier S').Carrier :=
  (T.subCarrier S').smooth

instance contractRegionCharts (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) :
    ChartedSpace T.cutCarrier.kind.Space (T.contractRegion S hext hk).Carrier :=
  (T.contractRegion S hext hk).charts

instance contractRegionSmooth (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) :
    IsManifold T.cutCarrier.model ∞ (T.contractRegion S hext hk).Carrier :=
  (T.contractRegion S hext hk).smooth

abbrev ContractCut (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) : Type u :=
  (T.subCarrier Sᶜ).Carrier ⊕ (T.contractRegion S hext hk).Carrier

def contractFold (hext : ∀ i, T.externalPiece i ∉ S) (hk : T.cutCarrier.kind = .withBoundary) :
    T.ContractCut S hext hk → W.Carrier :=
  Sum.elim (fun a => T.cutMap a.val) (fun r => r.val)

theorem contMDiff_region_val (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) :
    ContMDiff (T.contractRegion S hext hk).model W.model ∞
      (fun r : (T.contractRegion S hext hk).Carrier => r.val) :=
  (recast_contMDiff_iff_left _ _ _ _).mpr (T.contMDiff_restrictCarrier_val S hext)

theorem contMDiff_sub_cutMap (S' : Finset (Fin T.components.count)) :
    ContMDiff (T.subCarrier S').model W.model ∞
      (fun a : (T.subCarrier S').Carrier => T.cutMap a.val) :=
  T.quotient_smooth.comp (contMDiff_subtype_val (I := T.cutCarrier.model) (U := T.subPiece S'))

theorem contMDiff_contractFold (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) :
    ContMDiff T.cutCarrier.model W.model ∞ (T.contractFold S hext hk) :=
  ContMDiff.sumElim (T.contMDiff_sub_cutMap Sᶜ) (T.contMDiff_region_val S hext hk)

theorem mfderiv_sub_cutMap_bijective (S' : Finset (Fin T.components.count))
    (a : (T.subCarrier S').Carrier) :
    Function.Bijective (mfderiv (T.subCarrier S').model W.model
      (fun a : (T.subCarrier S').Carrier => T.cutMap a.val) a) := by
  obtain ⟨L, hL, -⟩ := T.quotient_oriented a.val
  have hres := DifferentialGeometry.Topology.Manifold.mfderiv_restrict_open
    T.cutCarrier.model W.model (T.subPiece S') (T.reconstruction ∘ T.pairing.quotientMap)
    T.quotient_smooth a
  have he : mfderiv (T.subCarrier S').model W.model
      (fun a : (T.subCarrier S').Carrier => T.cutMap a.val) a =
      mfderiv T.cutCarrier.model W.model (T.reconstruction ∘ T.pairing.quotientMap) a.val :=
    hres
  rw [he]
  constructor
  · intro v w hvw
    apply L.injective
    exact (hL v).trans (hvw.trans (hL w).symm)
  · intro w
    obtain ⟨v, rfl⟩ := L.surjective w
    exact ⟨v, (hL v).symm⟩

theorem mfderiv_region_val_bijective (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) (r : (T.contractRegion S hext hk).Carrier) :
    Function.Bijective (mfderiv (T.contractRegion S hext hk).model W.model
      (fun r : (T.contractRegion S hext hk).Carrier => r.val) r) := by
  have e := recast_mfderiv_left (T.restrictCarrier S hext) T.cutCarrier.kind hk.symm
    (J := W.model) (fun r : (T.contractRegion S hext hk).Carrier => r.val) r
  have hb := (T.restrictAtlas S hext).mfderiv_subtypeVal_bijective r
  exact e ▸ hb

theorem mfderiv_contractFold_bijective (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) (x : T.ContractCut S hext hk) :
    Function.Bijective (mfderiv T.cutCarrier.model W.model (T.contractFold S hext hk) x) := by
  have hf : MDifferentiableAt T.cutCarrier.model W.model (T.contractFold S hext hk) x :=
    (T.contMDiff_contractFold S hext hk).mdifferentiableAt (by simp)
  rcases x with a | r
  · have hi : MDifferentiableAt T.cutCarrier.model T.cutCarrier.model
        (Sum.inl : (T.subCarrier Sᶜ).Carrier → T.ContractCut S hext hk) a :=
      (ContMDiff.inl : ContMDiff T.cutCarrier.model T.cutCarrier.model ∞
        (Sum.inl : (T.subCarrier Sᶜ).Carrier → T.ContractCut S hext hk)).mdifferentiableAt
        (by simp)
    have h := mfderiv_comp a hf hi
    rw [hasMFDerivAt_inl.mfderiv] at h
    have hb : Function.Bijective (mfderiv T.cutCarrier.model W.model
        (T.contractFold S hext hk ∘ Sum.inl) a) := T.mfderiv_sub_cutMap_bijective Sᶜ a
    rw [h] at hb
    exact hb
  · have hi : MDifferentiableAt T.cutCarrier.model T.cutCarrier.model
        (Sum.inr : (T.contractRegion S hext hk).Carrier → T.ContractCut S hext hk) r :=
      (ContMDiff.inr : ContMDiff T.cutCarrier.model T.cutCarrier.model ∞
        (Sum.inr : (T.contractRegion S hext hk).Carrier →
          T.ContractCut S hext hk)).mdifferentiableAt (by simp)
    have h := mfderiv_comp r hf hi
    rw [hasMFDerivAt_inr.mfderiv] at h
    have hb : Function.Bijective (mfderiv T.cutCarrier.model W.model
        (T.contractFold S hext hk ∘ Sum.inr) r) := T.mfderiv_region_val_bijective S hext hk r
    rw [h] at hb
    exact hb

def contractCutOrientation (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) :
    ManifoldOrientation T.cutCarrier.model (T.ContractCut S hext hk) 3 :=
  Manifold.manifoldOrientationPullback T.cutCarrier.model W.model finrank_euclideanSpace_fin
    (T.contractFold S hext hk) (T.contMDiff_contractFold S hext hk)
    (T.mfderiv_contractFold_bijective S hext hk) W.orientation

abbrev contractCut (hext : ∀ i, T.externalPiece i ∉ S) (hk : T.cutCarrier.kind = .withBoundary) :
    CompactCarrier.{u} where
  kind := T.cutCarrier.kind
  Carrier := T.ContractCut S hext hk
  orientation := T.contractCutOrientation S hext hk

theorem contractCut_orientation_map (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) (x : T.ContractCut S hext hk) :
    Orientation.map (Fin 3) (Manifold.differentialEquivOfBijective T.cutCarrier.model W.model
      (T.contractFold S hext hk) (T.mfderiv_contractFold_bijective S hext hk) x).toLinearEquiv
      ((T.contractCut S hext hk).orientation.orientation x) =
        W.orientation.orientation (T.contractFold S hext hk x) :=
  Manifold.orientation_map_manifoldOrientationPullback T.cutCarrier.model W.model
    finrank_euclideanSpace_fin (T.contractFold S hext hk) (T.contMDiff_contractFold S hext hk)
    (T.mfderiv_contractFold_bijective S hext hk) W.orientation x

private theorem seam_mem_closure (k : Fin T.pairing.count) (t : Torus) (c : ℝ)
    (P : Set W.Carrier)
    (hP : ∀ a : ℝ, a ∈ Set.Ioo (-1 : ℝ) 0 → T.seam k (t, c * a) ∈ P) :
    T.seam k (t, 0) ∈ closure P := by
  have hcont : ContinuousAt (fun a : ℝ => T.seam k (t, c * a)) 0 := by
    have h0 : (t, c * 0) ∈ (T.seam k).source :=
      T.mem_seam_source k ⟨by simp, by simp⟩
    have hf : ContinuousAt (fun a : ℝ => (t, c * a)) 0 :=
      (continuous_const.prodMk (continuous_const.mul continuous_id)).continuousAt
    have hg : ContinuousAt (T.seam k) (t, c * 0) :=
      (T.continuousOn_seam k).continuousAt ((T.seam k).open_source.mem_nhds h0)
    have hgf := ContinuousAt.comp (f := fun a : ℝ => (t, c * a)) (x := 0) hg hf
    exact hgf
  have ht : Filter.Tendsto (fun a : ℝ => T.seam k (t, c * a)) (𝓝[<] 0) (𝓝 (T.seam k (t, 0))) := by
    have := hcont.tendsto
    rw [mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsLT (show (-1 : ℝ) < 0 by norm_num)] with a ha
  exact hP a ha

theorem range_subset_closure_diff_crossing :
    Set.range (T.restrictMap S) ⊆ closure (Set.range (T.restrictMap S) \ T.crossingSurface S) := by
  intro x hx
  by_cases hcx : x ∈ T.crossingSurface S
  · obtain ⟨k, hk, t, rfl⟩ := Set.mem_iUnion₂.mp hcx
    rcases hk with ⟨hl, -⟩ | ⟨hr, -⟩
    · refine T.seam_mem_closure k t 1 _ fun a ha => ⟨?_, fun h => ?_⟩
      · exact T.seam_mem_range_of_nonpos S k hl ⟨by simp; linarith [ha.1], by simp; linarith [ha.2]⟩
          (by simp; linarith [ha.2])
      · have := T.snd_eq_zero_of_seam_mem_crossingSurface S k
          ⟨by simp; linarith [ha.1], by simp; linarith [ha.2]⟩ h
        simp at this
        linarith [ha.2]
    · refine T.seam_mem_closure k t (-1) _ fun a ha => ⟨?_, fun h => ?_⟩
      · exact T.seam_mem_range_of_nonneg S k hr ⟨by simp; linarith [ha.2], by simp; linarith [ha.1]⟩
          (by simp; linarith [ha.2])
      · have := T.snd_eq_zero_of_seam_mem_crossingSurface S k
          ⟨by simp; linarith [ha.2], by simp; linarith [ha.1]⟩ h
        simp at this
        linarith [ha.2]
  · exact subset_closure ⟨hx, hcx⟩

theorem isConnected_range_of_diff
    (hconn : IsConnected (Set.range (T.restrictMap S) \ T.crossingSurface S)) :
    IsConnected (Set.range (T.restrictMap S)) :=
  hconn.subset_closure Set.sdiff_subset (T.range_subset_closure_diff_crossing S)

def contractPiece (hext : ∀ i, T.externalPiece i ∉ S) (hk : T.cutCarrier.kind = .withBoundary) :
    Fin (Sᶜ.card + 1) → TopologicalSpace.Opens (T.contractCut S hext hk).Carrier :=
  Fin.lastCases ⟨Set.range Sum.inr, isOpen_range_inr⟩
    fun j => ⟨Sum.inl '' (T.subPieceOf Sᶜ j : Set (T.subCarrier Sᶜ).Carrier),
      isOpenMap_inl _ (T.subPieceOf Sᶜ j).isOpen⟩

theorem contractPiece_last (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) :
    (T.contractPiece S hext hk (Fin.last _) : Set (T.ContractCut S hext hk)) =
      Set.range Sum.inr := by
  simp only [contractPiece, Fin.lastCases_last]
  rfl

theorem contractPiece_castSucc (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) (j : Fin Sᶜ.card) :
    (T.contractPiece S hext hk j.castSucc : Set (T.ContractCut S hext hk)) =
      Sum.inl '' (T.subPieceOf Sᶜ j : Set (T.subCarrier Sᶜ).Carrier) := by
  simp only [contractPiece, Fin.lastCases_castSucc]
  rfl

theorem region_isInteriorPoint_iff (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) (r : (T.contractRegion S hext hk).Carrier) :
    (T.contractRegion S hext hk).model.IsInteriorPoint r ↔ r.val ∉ T.crossingSurface S := by
  rw [ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint, not_iff_not]
  exact (recast_isBoundaryPoint_iff _ _ _ r).trans (T.restrictCarrier_isBoundaryPoint_iff S hext r)

theorem isConnected_contractPiece (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary)
    (hconn : IsConnected (Set.range (T.restrictMap S) \ T.crossingSurface S))
    (j : Fin (Sᶜ.card + 1)) :
    IsConnected (T.contractPiece S hext hk j : Set (T.contractCut S hext hk).Carrier) := by
  induction j using Fin.lastCases with
  | last =>
    rw [contractPiece_last]
    have : ConnectedSpace (T.contractRegion S hext hk).Carrier :=
      isConnected_iff_connectedSpace.mp (T.isConnected_range_of_diff S hconn)
    exact isConnected_range continuous_inr
  | cast j =>
    rw [contractPiece_castSucc]
    have : ConnectedSpace (T.subPieceOf Sᶜ j) :=
      (T.subPieceOfHomeomorph Sᶜ j).connectedSpace_iff.mpr (T.components.connected _)
    exact (isConnected_iff_connectedSpace.mpr this).image _ continuous_inl.continuousOn

theorem isConnected_contractPieceInterior (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary)
    (hconn : IsConnected (Set.range (T.restrictMap S) \ T.crossingSurface S))
    (j : Fin (Sᶜ.card + 1)) :
    IsConnected ((T.contractPiece S hext hk j : Set (T.contractCut S hext hk).Carrier) ∩
      {x | T.cutCarrier.model.IsInteriorPoint x}) := by
  induction j using Fin.lastCases with
  | last =>
    rw [contractPiece_last]
    have hset : Set.range (Sum.inr : (T.contractRegion S hext hk).Carrier → _) ∩
        {x : T.ContractCut S hext hk | T.cutCarrier.model.IsInteriorPoint x} =
        Sum.inr '' {r : (T.contractRegion S hext hk).Carrier | r.val ∉ T.crossingSurface S} := by
      ext x
      constructor
      · rintro ⟨⟨r, rfl⟩, hx⟩
        refine ⟨r, (T.region_isInteriorPoint_iff S hext hk r).mp ?_, rfl⟩
        exact ModelWithCorners.isInteriorPoint_disjointUnion_right hx rfl
      · rintro ⟨r, hr, rfl⟩
        exact ⟨⟨r, rfl⟩, ModelWithCorners.interiorPoint_inr r
          ((T.region_isInteriorPoint_iff S hext hk r).mpr hr)⟩
    rw [hset]
    have himg : Subtype.val '' {r : (T.contractRegion S hext hk).Carrier |
        r.val ∉ T.crossingSurface S} = Set.range (T.restrictMap S) \ T.crossingSurface S := by
      ext y
      constructor
      · rintro ⟨r, hr, rfl⟩
        exact ⟨r.property, hr⟩
      · rintro ⟨hy, hc⟩
        exact ⟨⟨y, hy⟩, hc, rfl⟩
    have hQ : IsConnected {r : (T.contractRegion S hext hk).Carrier |
        r.val ∉ T.crossingSurface S} := by
      refine ⟨?_, ?_⟩
      · obtain ⟨y, hy, hc⟩ := hconn.nonempty
        exact ⟨⟨y, hy⟩, hc⟩
      · refine (Topology.IsInducing.subtypeVal.isPreconnected_image).mp ?_
        exact himg ▸ hconn.isPreconnected
    exact hQ.image _ continuous_inr.continuousOn
  | cast j =>
    rw [contractPiece_castSucc]
    have hset : Sum.inl '' (T.subPieceOf Sᶜ j : Set (T.subCarrier Sᶜ).Carrier) ∩
        {x : T.ContractCut S hext hk | T.cutCarrier.model.IsInteriorPoint x} =
        Sum.inl '' ((T.subCarrier Sᶜ).pieceInterior (T.subPieceOf Sᶜ j) :
          Set (T.subCarrier Sᶜ).Carrier) := by
      ext x
      constructor
      · rintro ⟨⟨a, ha, rfl⟩, hx⟩
        exact ⟨a, ⟨ha, ModelWithCorners.isInteriorPoint_disjointUnion_left hx rfl⟩, rfl⟩
      · rintro ⟨a, ⟨ha, hai⟩, rfl⟩
        exact ⟨⟨a, ha, rfl⟩, ModelWithCorners.interiorPoint_inl a hai⟩
    rw [hset]
    have : ConnectedSpace ((T.subCarrier Sᶜ).pieceInterior (T.subPieceOf Sᶜ j)) :=
      (T.subPieceInteriorHomeomorph Sᶜ j).connectedSpace_iff.mpr
        (T.components.interior_connected _)
    exact (isConnected_iff_connectedSpace.mpr this).image _ continuous_inl.continuousOn

theorem contractPiece_disjoint (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) :
    Pairwise (fun i j => Disjoint
      (T.contractPiece S hext hk i : Set (T.contractCut S hext hk).Carrier)
      (T.contractPiece S hext hk j)) := by
  intro i j hij
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => exact (hij rfl).elim
    | cast j =>
      rw [contractPiece_last, contractPiece_castSucc, Set.disjoint_left]
      rintro x ⟨r, rfl⟩ ⟨a, -, h⟩
      exact Sum.inl_ne_inr h
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      rw [contractPiece_last, contractPiece_castSucc, Set.disjoint_left]
      rintro x ⟨a, -, rfl⟩ ⟨r, h⟩
      exact Sum.inl_ne_inr h.symm
    | cast j =>
      rw [contractPiece_castSucc, contractPiece_castSucc]
      have hne : i ≠ j := fun e => hij (congrArg Fin.castSucc e)
      exact (Set.disjoint_image_iff Sum.inl_injective).mpr
        ((T.components.disjoint fun e => hne (T.subIndex_injective Sᶜ e)).preimage Subtype.val)

def contractComponents (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary)
    (hconn : IsConnected (Set.range (T.restrictMap S) \ T.crossingSurface S)) :
    (T.contractCut S hext hk).Components where
  count := Sᶜ.card + 1
  count_pos := Nat.succ_pos _
  piece := T.contractPiece S hext hk
  closed j := by
    induction j using Fin.lastCases with
    | last =>
      rw [contractPiece_last]
      exact isClosed_range_inr
    | cast j =>
      rw [contractPiece_castSucc]
      exact isClosedMap_inl _ ((T.components.closed _).preimage continuous_subtype_val)
  connected j := isConnected_iff_connectedSpace.mp (T.isConnected_contractPiece S hext hk hconn j)
  disjoint := T.contractPiece_disjoint S hext hk
  covers := by
    refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr ?_
    rcases x with a | r
    · obtain ⟨i, hi, hx⟩ := (T.mem_subPiece Sᶜ).mp a.property
      refine ⟨(T.subIndexOf Sᶜ hi).castSucc, ?_⟩
      change Sum.inl a ∈ (T.contractPiece S hext hk (T.subIndexOf Sᶜ hi).castSucc :
        Set (T.contractCut S hext hk).Carrier)
      rw [contractPiece_castSucc]
      refine ⟨a, ?_, rfl⟩
      change a.val ∈ T.components.piece (T.subIndex Sᶜ (T.subIndexOf Sᶜ hi))
      rw [subIndex_subIndexOf]
      exact hx
    · refine ⟨Fin.last _, ?_⟩
      change Sum.inr r ∈ (T.contractPiece S hext hk (Fin.last _) :
        Set (T.contractCut S hext hk).Carrier)
      rw [contractPiece_last]
      exact ⟨r, rfl⟩
  interior_connected j :=
    isConnected_iff_connectedSpace.mp (T.isConnected_contractPieceInterior S hext hk hconn j)

theorem mem_subPiece_of_not_mem_compl {x : T.cutCarrier.Carrier} (hx : x ∉ T.subPiece Sᶜ) :
    x ∈ T.subPiece S := by
  have hcov : x ∈ ⋃ i, (T.components.piece i : Set T.cutCarrier.Carrier) := by
    rw [T.components.covers]
    exact Set.mem_univ x
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hcov
  by_cases hiS : i ∈ S
  · exact T.piece_subset_subPiece S hiS hi
  · exact (hx (T.piece_subset_subPiece Sᶜ (Finset.mem_compl.mpr hiS) hi)).elim

theorem cutMap_mem_range_of_mem {x : T.cutCarrier.Carrier} (hx : x ∈ T.subPiece S) :
    T.cutMap x ∈ Set.range (T.restrictMap S) :=
  ⟨(T.restrictPairing S).quotientMap ⟨x, hx⟩, rfl⟩

open Classical in
def contractMap (hext : ∀ i, T.externalPiece i ∉ S) (hk : T.cutCarrier.kind = .withBoundary)
    (x : T.cutCarrier.Carrier) : T.ContractCut S hext hk :=
  if h : x ∈ T.subPiece Sᶜ then Sum.inl ⟨x, h⟩
  else Sum.inr ⟨T.cutMap x, T.cutMap_mem_range_of_mem S (T.mem_subPiece_of_not_mem_compl S h)⟩

theorem contractMap_of_mem (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) {x : T.cutCarrier.Carrier}
    (h : x ∈ T.subPiece Sᶜ) : T.contractMap S hext hk x = Sum.inl ⟨x, h⟩ := by
  simp [contractMap, h]

theorem contractMap_of_not_mem (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) {x : T.cutCarrier.Carrier}
    (h : x ∉ T.subPiece Sᶜ) : T.contractMap S hext hk x =
      Sum.inr ⟨T.cutMap x, T.cutMap_mem_range_of_mem S (T.mem_subPiece_of_not_mem_compl S h)⟩ := by
  simp [contractMap, h]

theorem contractFold_contractMap (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) (x : T.cutCarrier.Carrier) :
    T.contractFold S hext hk (T.contractMap S hext hk x) = T.cutMap x := by
  by_cases h : x ∈ T.subPiece Sᶜ
  · rw [T.contractMap_of_mem S hext hk h]
    rfl
  · rw [T.contractMap_of_not_mem S hext hk h]
    rfl

abbrev NonInternal := {k : Fin T.pairing.count // ¬(T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)}

def nonInternal (j : Fin (Fintype.card (T.NonInternal S))) : T.NonInternal S :=
  (Fintype.equivFin _).symm j

@[simp]
theorem nonInternal_equivFin (a : T.NonInternal S) : T.nonInternal S (Fintype.equivFin _ a) = a :=
  (Fintype.equivFin _).symm_apply_apply a

def contractLeftCollar (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) (j : Fin (Fintype.card (T.NonInternal S))) :
    PartialDiffeomorph halfCollarModel (T.contractCut S hext hk).model
      (Torus × EuclideanHalfSpace 1) (T.contractCut S hext hk).Carrier ∞ :=
  if hl : T.leftPiece (T.nonInternal S j).val ∈ S then
    sumInrPD (I := T.cutCarrier.model)
      (recastPD (T.restrictCarrier S hext) _ hk.symm (T.leftCrossCollar S hext _ hl
        fun hr => (T.nonInternal S j).property ⟨hl, hr⟩)) (1, halfZero)
  else
    sumInlPD (I := T.cutCarrier.model)
      (T.subCollar Sᶜ (.inl (T.nonInternal S j).val) (Finset.mem_compl.mpr hl)) (1, halfZero)

def contractRightCollar (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) (j : Fin (Fintype.card (T.NonInternal S))) :
    PartialDiffeomorph halfCollarModel (T.contractCut S hext hk).model
      (Torus × EuclideanHalfSpace 1) (T.contractCut S hext hk).Carrier ∞ :=
  if hr : T.rightPiece (T.nonInternal S j).val ∈ S then
    sumInrPD (I := T.cutCarrier.model)
      (recastPD (T.restrictCarrier S hext) _ hk.symm (T.rightCrossCollar S hext _ hr
        fun hl => (T.nonInternal S j).property ⟨hl, hr⟩)) (1, halfZero)
  else
    sumInlPD (I := T.cutCarrier.model)
      (T.subCollar Sᶜ (.inr (.inl (T.nonInternal S j).val)) (Finset.mem_compl.mpr hr))
      (1, halfZero)

theorem contractLeftCollar_source (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) (j : Fin (Fintype.card (T.NonInternal S))) :
    (T.contractLeftCollar S hext hk j).source = halfCollarSource := by
  unfold contractLeftCollar
  split_ifs with hl
  · exact recastPD_source _ _ _ _
  · exact T.subCollar_source Sᶜ (.inl _) (Finset.mem_compl.mpr hl)

theorem contractRightCollar_source (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) (j : Fin (Fintype.card (T.NonInternal S))) :
    (T.contractRightCollar S hext hk j).source = halfCollarSource := by
  unfold contractRightCollar
  split_ifs with hr
  · exact recastPD_source _ _ _ _
  · exact T.subCollar_source Sᶜ (.inr (.inl _)) (Finset.mem_compl.mpr hr)

theorem contractMap_sideCollar (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) (s : T.Side) {p : Torus × EuclideanHalfSpace 1}
    (hp : p ∈ halfCollarSource) (hs : T.sidePiece s ∈ Sᶜ) :
    T.contractMap S hext hk (T.sideCollar s p) = Sum.inl (T.subCollar Sᶜ s hs p) := by
  have hmem : T.sideCollar s p ∈ T.subPiece Sᶜ :=
    T.sideCollar_target_subset_subPiece Sᶜ hs
      ((T.sideCollar s).map_source' ((T.sideCollar_source s).symm ▸ hp))
  rw [T.contractMap_of_mem S hext hk hmem]
  exact congrArg Sum.inl (Subtype.ext (T.subCollar_apply Sᶜ s hs hp).symm)

theorem contractMap_sideCollar_of_mem (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) (s : T.Side) {p : Torus × EuclideanHalfSpace 1}
    (hp : p ∈ halfCollarSource) (hs : T.sidePiece s ∈ S) :
    T.contractMap S hext hk (T.sideCollar s p) =
      Sum.inr ⟨T.cutMap (T.sideCollar s p), T.cutMap_mem_range_of_mem S
        (T.sideCollar_target_subset_subPiece S hs
          ((T.sideCollar s).map_source' ((T.sideCollar_source s).symm ▸ hp)))⟩ := by
  have hmem : T.sideCollar s p ∈ T.components.piece (T.sidePiece s) :=
    T.sideCollar_target_subset s ((T.sideCollar s).map_source' ((T.sideCollar_source s).symm ▸ hp))
  have hnot : T.sideCollar s p ∉ T.subPiece Sᶜ := fun h =>
    (Finset.mem_compl.mp (T.mem_of_mem_subPiece Sᶜ h hmem)) hs
  exact T.contractMap_of_not_mem S hext hk hnot

theorem contractLeftCollar_apply (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) (j : Fin (Fintype.card (T.NonInternal S)))
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    T.contractLeftCollar S hext hk j p =
      T.contractMap S hext hk (T.pairing.leftCollar (T.nonInternal S j).val p) := by
  by_cases hl : T.leftPiece (T.nonInternal S j).val ∈ S
  · rw [show T.pairing.leftCollar (T.nonInternal S j).val p =
      T.sideCollar (.inl (T.nonInternal S j).val) p from rfl,
      T.contractMap_sideCollar_of_mem S hext hk (.inl (T.nonInternal S j).val) hp hl]
    unfold contractLeftCollar
    rw [dite_eq_left hl]
    exact congrArg Sum.inr (Subtype.ext ((congrArg Subtype.val (recastPD_apply _ _ _ _ p)).trans
      (congrArg T.cutMap (T.subCollar_apply S (.inl _) hl hp))))
  · rw [show T.pairing.leftCollar (T.nonInternal S j).val p =
      T.sideCollar (.inl (T.nonInternal S j).val) p from rfl,
      T.contractMap_sideCollar S hext hk (.inl (T.nonInternal S j).val) hp
        (Finset.mem_compl.mpr hl)]
    unfold contractLeftCollar
    rw [dite_eq_right hl]
    rfl

theorem contractRightCollar_apply (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) (j : Fin (Fintype.card (T.NonInternal S)))
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    T.contractRightCollar S hext hk j p =
      T.contractMap S hext hk (T.pairing.rightCollar (T.nonInternal S j).val p) := by
  by_cases hr : T.rightPiece (T.nonInternal S j).val ∈ S
  · rw [show T.pairing.rightCollar (T.nonInternal S j).val p =
      T.sideCollar (.inr (.inl (T.nonInternal S j).val)) p from rfl,
      T.contractMap_sideCollar_of_mem S hext hk (.inr (.inl (T.nonInternal S j).val)) hp hr]
    unfold contractRightCollar
    rw [dite_eq_left hr]
    exact congrArg Sum.inr (Subtype.ext ((congrArg Subtype.val (recastPD_apply _ _ _ _ p)).trans
      (congrArg T.cutMap (T.subCollar_apply S (.inr (.inl _)) hr hp))))
  · rw [show T.pairing.rightCollar (T.nonInternal S j).val p =
      T.sideCollar (.inr (.inl (T.nonInternal S j).val)) p from rfl,
      T.contractMap_sideCollar S hext hk (.inr (.inl (T.nonInternal S j).val)) hp
        (Finset.mem_compl.mpr hr)]
    unfold contractRightCollar
    rw [dite_eq_right hr]
    rfl

theorem contractMap_inj_of_mem (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) {a b : T.cutCarrier.Carrier}
    (ha : a ∈ T.subPiece Sᶜ) (h : T.contractMap S hext hk a = T.contractMap S hext hk b) :
    a = b := by
  rw [T.contractMap_of_mem S hext hk ha] at h
  by_cases hb : b ∈ T.subPiece Sᶜ
  · rw [T.contractMap_of_mem S hext hk hb] at h
    exact congrArg Subtype.val (Sum.inl_injective h)
  · rw [T.contractMap_of_not_mem S hext hk hb] at h
    exact (Sum.inl_ne_inr h).elim

theorem contractMap_ne_of_mem (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) {a b : T.cutCarrier.Carrier}
    (ha : a ∈ T.subPiece Sᶜ) (hb : b ∉ T.subPiece Sᶜ) :
    T.contractMap S hext hk a ≠ T.contractMap S hext hk b := by
  rw [T.contractMap_of_mem S hext hk ha, T.contractMap_of_not_mem S hext hk hb]
  exact Sum.inl_ne_inr

theorem not_mem_subPiece_compl_of_piece {x : T.cutCarrier.Carrier} {i : Fin T.components.count}
    (hx : x ∈ T.components.piece i) (hi : i ∈ S) : x ∉ T.subPiece Sᶜ := fun h =>
  (Finset.mem_compl.mp (T.mem_of_mem_subPiece Sᶜ h hx)) hi

def contractLeftPoint (hext : ∀ i, T.externalPiece i ∉ S) (hk : T.cutCarrier.kind = .withBoundary)
    (j : Fin (Fintype.card (T.NonInternal S))) (t : Torus) : T.ContractCut S hext hk :=
  T.contractMap S hext hk (T.pairing.leftParam (T.nonInternal S j).val t).val

def contractRightPoint (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) (j : Fin (Fintype.card (T.NonInternal S)))
    (t : Torus) : T.ContractCut S hext hk :=
  T.contractMap S hext hk (T.pairing.rightParam (T.nonInternal S j).val t).val

theorem contractLeftCollar_zero (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) (j : Fin (Fintype.card (T.NonInternal S)))
    (t : Torus) :
    T.contractLeftCollar S hext hk j (t, halfZero) = T.contractLeftPoint S hext hk j t := by
  rw [T.contractLeftCollar_apply S hext hk j (zero_mem_halfCollarSource t), T.pairing.left_zero]
  rfl

theorem contractRightCollar_zero (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) (j : Fin (Fintype.card (T.NonInternal S)))
    (t : Torus) :
    T.contractRightCollar S hext hk j (t, halfZero) = T.contractRightPoint S hext hk j t := by
  rw [T.contractRightCollar_apply S hext hk j (zero_mem_halfCollarSource t), T.pairing.right_zero]
  rfl

theorem continuous_contractLeftPoint (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) (j : Fin (Fintype.card (T.NonInternal S))) :
    Continuous (T.contractLeftPoint S hext hk j) := by
  have h : Continuous (fun t : Torus => T.contractLeftCollar S hext hk j (t, halfZero)) :=
    (T.contractLeftCollar S hext hk j).contMDiffOn.continuousOn.comp_continuous
      (continuous_id.prodMk continuous_const) fun t => by
        rw [T.contractLeftCollar_source]
        exact zero_mem_halfCollarSource t
  exact h.congr fun t => T.contractLeftCollar_zero S hext hk j t

theorem continuous_contractRightPoint (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) (j : Fin (Fintype.card (T.NonInternal S))) :
    Continuous (T.contractRightPoint S hext hk j) := by
  have h : Continuous (fun t : Torus => T.contractRightCollar S hext hk j (t, halfZero)) :=
    (T.contractRightCollar S hext hk j).contMDiffOn.continuousOn.comp_continuous
      (continuous_id.prodMk continuous_const) fun t => by
        rw [T.contractRightCollar_source]
        exact zero_mem_halfCollarSource t
  exact h.congr fun t => T.contractRightCollar_zero S hext hk j t

theorem contractFold_leftPoint (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) (j : Fin (Fintype.card (T.NonInternal S)))
    (t : Torus) :
    T.contractFold S hext hk (T.contractLeftPoint S hext hk j t) =
      T.seamTorus (T.nonInternal S j).val t := by
  rw [contractLeftPoint, contractFold_contractMap, seamTorus_eq_cutMap]

theorem contractFold_rightPoint (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) (j : Fin (Fintype.card (T.NonInternal S)))
    (t : Torus) :
    T.contractFold S hext hk (T.contractRightPoint S hext hk j t) =
      T.seamTorus (T.nonInternal S j).val
        ((T.pairing.matching (T.nonInternal S j).val).symm t) := by
  rw [contractRightPoint, contractFold_contractMap, seamTorus_eq_cutMap_right,
    Diffeomorph.apply_symm_apply]

theorem seamTorus_injective (k : Fin T.pairing.count) : Function.Injective (T.seamTorus k) := by
  intro t t' h
  have := (T.seam k).toPartialEquiv.injOn (T.mem_seam_source k ⟨by norm_num, by norm_num⟩)
    (T.mem_seam_source k ⟨by norm_num, by norm_num⟩) h
  exact congrArg Prod.fst this

theorem injective_contractLeftPoint (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) (j : Fin (Fintype.card (T.NonInternal S))) :
    Function.Injective (T.contractLeftPoint S hext hk j) := fun t t' h =>
  T.seamTorus_injective _ ((T.contractFold_leftPoint S hext hk j t).symm.trans
    ((congrArg (T.contractFold S hext hk) h).trans (T.contractFold_leftPoint S hext hk j t')))

theorem injective_contractRightPoint (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) (j : Fin (Fintype.card (T.NonInternal S))) :
    Function.Injective (T.contractRightPoint S hext hk j) := fun t t' h =>
  (T.pairing.matching _).symm.injective (T.seamTorus_injective _
    ((T.contractFold_rightPoint S hext hk j t).symm.trans
      ((congrArg (T.contractFold S hext hk) h).trans (T.contractFold_rightPoint S hext hk j t'))))

def contractLeftParam (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) (j : Fin (Fintype.card (T.NonInternal S))) :
    Torus ≃ₜ Set.range (T.contractLeftPoint S hext hk j) :=
  ((T.continuous_contractLeftPoint S hext hk j).isClosedEmbedding
    (T.injective_contractLeftPoint S hext hk j)).isEmbedding.toHomeomorph

def contractRightParam (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) (j : Fin (Fintype.card (T.NonInternal S))) :
    Torus ≃ₜ Set.range (T.contractRightPoint S hext hk j) :=
  ((T.continuous_contractRightPoint S hext hk j).isClosedEmbedding
    (T.injective_contractRightPoint S hext hk j)).isEmbedding.toHomeomorph

theorem contractFold_mem_seamSurface (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) (j : Fin (Fintype.card (T.NonInternal S)))
    {x : T.ContractCut S hext hk}
    (hx : x ∈ Set.range (T.contractLeftPoint S hext hk j) ∪
      Set.range (T.contractRightPoint S hext hk j)) :
    T.contractFold S hext hk x ∈ T.seamSurface (T.nonInternal S j).val := by
  rcases hx with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · rw [contractFold_leftPoint]
    exact ⟨t, rfl⟩
  · rw [contractFold_rightPoint]
    exact ⟨_, rfl⟩

def contractGluing (hext : ∀ i, T.externalPiece i ∉ S) (hk : T.cutCarrier.kind = .withBoundary) :
    BoundaryGluing (T.contractCut S hext hk).Carrier (Fin (Fintype.card (T.NonInternal S))) where
  left j := Set.range (T.contractLeftPoint S hext hk j)
  right j := Set.range (T.contractRightPoint S hext hk j)
  attaching j := (T.contractLeftParam S hext hk j).symm.trans
    ((T.pairing.matching (T.nonInternal S j).val).toHomeomorph.trans
      (T.contractRightParam S hext hk j))
  isClosed_left j := (isCompact_range (T.continuous_contractLeftPoint S hext hk j)).isClosed
  isClosed_right j := (isCompact_range (T.continuous_contractRightPoint S hext hk j)).isClosed
  disjoint_left_right j := by
    rw [Set.disjoint_left]
    rintro _ ⟨t, rfl⟩ ⟨t', h⟩
    set k := (T.nonInternal S j).val
    have hlp : (T.pairing.leftParam k t).val ∈ T.components.piece (T.leftPiece k) :=
      T.left_owned k (T.pairing.leftParam k t).property
    have hrp : (T.pairing.rightParam k t').val ∈ T.components.piece (T.rightPiece k) :=
      T.right_owned k (T.pairing.rightParam k t').property
    by_cases hl : T.leftPiece k ∈ S
    · have hr : T.rightPiece k ∉ S := fun hr => (T.nonInternal S j).property ⟨hl, hr⟩
      have hrc : (T.pairing.rightParam k t').val ∈ T.subPiece Sᶜ :=
        T.piece_subset_subPiece Sᶜ (Finset.mem_compl.mpr hr) hrp
      exact T.contractMap_ne_of_mem S hext hk hrc
        (T.not_mem_subPiece_compl_of_piece S hlp hl) h
    · have hlc : (T.pairing.leftParam k t).val ∈ T.subPiece Sᶜ :=
        T.piece_subset_subPiece Sᶜ (Finset.mem_compl.mpr hl) hlp
      have he := T.contractMap_inj_of_mem S hext hk hlc h.symm
      exact (T.pairing.gluing.disjoint_left_right k).le_bot
        ⟨(T.pairing.leftParam k t).property, he ▸ (T.pairing.rightParam k t').property⟩
  disjoint_blocks i j hij := by
    rw [Set.disjoint_left]
    intro x hi hj
    have hne : (T.nonInternal S i).val ≠ (T.nonInternal S j).val := fun e =>
      hij ((Fintype.equivFin _).symm.injective (Subtype.ext e))
    exact (T.seam_disjoint hne).le_bot
      ⟨T.seamSurface_subset_seamCollar _ (T.contractFold_mem_seamSurface S hext hk i hi),
        T.seamSurface_subset_seamCollar _ (T.contractFold_mem_seamSurface S hext hk j hj)⟩

theorem contractCut_oriented (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) (x : (T.contractCut S hext hk).Carrier) :
    ∃ A : TangentSpace (T.contractCut S hext hk).model x ≃ₗ[ℝ]
        TangentSpace W.model (T.contractFold S hext hk x),
      (∀ v, A v = mfderiv (T.contractCut S hext hk).model W.model (T.contractFold S hext hk) x v) ∧
      Orientation.map (Fin 3) A ((T.contractCut S hext hk).orientation.orientation x) =
        W.orientation.orientation (T.contractFold S hext hk x) :=
  ⟨(Manifold.differentialEquivOfBijective T.cutCarrier.model W.model (T.contractFold S hext hk)
    (T.mfderiv_contractFold_bijective S hext hk) x).toLinearEquiv, fun _ => rfl,
    T.contractCut_orientation_map S hext hk x⟩

private theorem isOpen_halfCollarSource' : IsOpen halfCollarSource :=
  isOpen_lt ((EuclideanSpace.proj 0).continuous.comp (continuous_subtype_val.comp continuous_snd))
    continuous_const

private theorem eventuallyEq_contractLeftCollar (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) (j : Fin (Fintype.card (T.NonInternal S)))
    (t : Torus) :
    T.contractFold S hext hk ∘ T.contractLeftCollar S hext hk j =ᶠ[𝓝 (t, halfZero)]
      (T.reconstruction ∘ T.pairing.quotientMap) ∘
        T.pairing.leftCollar (T.nonInternal S j).val := by
  filter_upwards [isOpen_halfCollarSource'.mem_nhds (zero_mem_halfCollarSource t)] with p hp
  change T.contractFold S hext hk (T.contractLeftCollar S hext hk j p) = T.cutMap _
  rw [T.contractLeftCollar_apply S hext hk j hp, contractFold_contractMap]

private theorem eventuallyEq_contractRightCollar (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) (j : Fin (Fintype.card (T.NonInternal S)))
    (t : Torus) :
    T.contractFold S hext hk ∘ (fun p => T.contractRightCollar S hext hk j
      (T.pairing.matching (T.nonInternal S j).val p.1, p.2)) =ᶠ[𝓝 (t, halfZero)]
      (T.reconstruction ∘ T.pairing.quotientMap) ∘ (fun p => T.pairing.rightCollar
        (T.nonInternal S j).val (T.pairing.matching (T.nonInternal S j).val p.1, p.2)) := by
  filter_upwards [isOpen_halfCollarSource'.mem_nhds (zero_mem_halfCollarSource t)] with p hp
  have hp' : (T.pairing.matching (T.nonInternal S j).val p.1, p.2) ∈ halfCollarSource := hp
  change T.contractFold S hext hk (T.contractRightCollar S hext hk j
    (T.pairing.matching (T.nonInternal S j).val p.1, p.2)) =
      T.cutMap (T.pairing.rightCollar _ (T.pairing.matching (T.nonInternal S j).val p.1, p.2))
  rw [T.contractRightCollar_apply S hext hk j hp', contractFold_contractMap]

private theorem mdifferentiableAt_collar {C : CompactCarrier.{u}}
    (φ : PartialDiffeomorph halfCollarModel C.model (Torus × EuclideanHalfSpace 1) C.Carrier ∞)
    (hφ : φ.source = halfCollarSource) (g : Torus → Torus)
    (hg : ContMDiff torusModel torusModel ∞ g) (t : Torus) :
    MDifferentiableAt halfCollarModel C.model (fun p => φ (g p.1, p.2)) (t, halfZero) := by
  have hφd : MDifferentiableAt halfCollarModel C.model φ (g t, halfZero) :=
    (φ.contMDiffOn.contMDiffAt (φ.open_source.mem_nhds
      (hφ ▸ zero_mem_halfCollarSource (g t)))).mdifferentiableAt (by simp)
  have hgd : MDifferentiableAt halfCollarModel halfCollarModel
      (fun p : Torus × EuclideanHalfSpace 1 => (g p.1, p.2)) (t, halfZero) :=
    ((hg.comp contMDiff_fst).prodMk contMDiff_snd).mdifferentiableAt (by simp)
  exact hφd.comp (t, halfZero) hgd

def contractPairing (hext : ∀ i, T.externalPiece i ∉ S) (hk : T.cutCarrier.kind = .withBoundary) :
    TorusPairing (T.contractCut S hext hk) where
  count := Fintype.card (T.NonInternal S)
  gluing := T.contractGluing S hext hk
  leftParam := T.contractLeftParam S hext hk
  rightParam := T.contractRightParam S hext hk
  matching j := T.pairing.matching (T.nonInternal S j).val
  matching_eq j t := by
    change (T.contractRightParam S hext hk j) ((T.pairing.matching _)
      ((T.contractLeftParam S hext hk j).symm ((T.contractLeftParam S hext hk j) t))) = _
    rw [Homeomorph.symm_apply_apply]
    rfl
  leftCollar := T.contractLeftCollar S hext hk
  rightCollar := T.contractRightCollar S hext hk
  left_source := T.contractLeftCollar_source S hext hk
  right_source := T.contractRightCollar_source S hext hk
  left_zero j t := T.contractLeftCollar_zero S hext hk j t
  right_zero j t := T.contractRightCollar_zero S hext hk j t
  reversing j := by
    intro t
    obtain ⟨L, R, hL, hR, ho⟩ := T.pairing.reversing (T.nonInternal S j).val t
    have hFd : ∀ x, MDifferentiableAt T.cutCarrier.model W.model
        (T.reconstruction ∘ T.pairing.quotientMap) x :=
      fun x => T.quotient_smooth.mdifferentiableAt (by simp)
    have hF'd : ∀ x, MDifferentiableAt (T.contractCut S hext hk).model W.model
        (T.contractFold S hext hk) x :=
      fun x => (T.contMDiff_contractFold S hext hk).mdifferentiableAt (by simp)
    obtain ⟨L', hL', hoL'⟩ := collar_orientation_transfer
      (T.reconstruction ∘ T.pairing.quotientMap) (T.contractFold S hext hk)
      T.quotient_oriented (T.contractCut_oriented S hext hk) hFd hF'd
      (mdifferentiableAt_collar (T.pairing.leftCollar _) (T.pairing.left_source _) id
        contMDiff_id t)
      (mdifferentiableAt_collar (T.contractLeftCollar S hext hk j)
        (T.contractLeftCollar_source S hext hk j) id contMDiff_id t)
      (T.eventuallyEq_contractLeftCollar S hext hk j t) L hL
    obtain ⟨R', hR', hoR'⟩ := collar_orientation_transfer
      (T.reconstruction ∘ T.pairing.quotientMap) (T.contractFold S hext hk)
      T.quotient_oriented (T.contractCut_oriented S hext hk) hFd hF'd
      (mdifferentiableAt_collar (T.pairing.rightCollar _) (T.pairing.right_source _)
        (T.pairing.matching _) (T.pairing.matching _).contMDiff t)
      (mdifferentiableAt_collar (T.contractRightCollar S hext hk j)
        (T.contractRightCollar_source S hext hk j) (T.pairing.matching _)
        (T.pairing.matching _).contMDiff t)
      (T.eventuallyEq_contractRightCollar S hext hk j t) R hR
    exact ⟨L', R', hL', hR', hoL'.trans (ho.trans (congrArg Neg.neg hoR'.symm))⟩

theorem externalPiece_mem_compl (hext : ∀ i, T.externalPiece i ∉ S) (i : Fin T.externalCount) :
    T.sidePiece (.inr (.inr i)) ∈ Sᶜ :=
  Finset.mem_compl.mpr (hext i)

def contractExternalCollar (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) (i : Fin T.externalCount) :
    PartialDiffeomorph halfCollarModel (T.contractCut S hext hk).model
      (Torus × EuclideanHalfSpace 1) (T.contractCut S hext hk).Carrier ∞ :=
  sumInlPD (I := T.cutCarrier.model)
    (T.subCollar Sᶜ (.inr (.inr i)) (T.externalPiece_mem_compl S hext i)) (1, halfZero)

theorem contractExternalCollar_apply (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) (i : Fin T.externalCount)
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    T.contractExternalCollar S hext hk i p =
      T.contractMap S hext hk (T.cutExternal.collar i p) :=
  (T.contractMap_sideCollar S hext hk (.inr (.inr i)) hp
    (T.externalPiece_mem_compl S hext i)).symm

def contractCutExternal (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) :
    BoundaryTori (T.contractCut S hext hk) T.externalCount where
  collar := T.contractExternalCollar S hext hk
  source_eq i := T.subCollar_source Sᶜ _ (T.externalPiece_mem_compl S hext i)
  boundary_zero i t := by
    refine ModelWithCorners.boundaryPoint_inl _ ?_
    refine (ModelWithCorners.isBoundaryPoint_iff_isBoundaryPoint_val (I := T.cutCarrier.model)
      (u := T.subPiece Sᶜ)).mpr ?_
    rw [T.subCollar_apply Sᶜ _ (T.externalPiece_mem_compl S hext i)
      (zero_mem_halfCollarSource t)]
    exact T.cutExternal.boundary_zero i t
  disjoint i i' h := by
    change Disjoint (Sum.inl '' (T.subCollar Sᶜ _ _).target)
      (Sum.inl '' (T.subCollar Sᶜ _ _).target)
    rw [Set.disjoint_image_iff Sum.inl_injective, T.subCollar_target, T.subCollar_target]
    exact (T.sideCollar_disjoint fun e => h (Sum.inr_injective (Sum.inr_injective e))).preimage _

private theorem cutMap_mem_seamSurface_of_block' (k : Fin T.pairing.count)
    {x : T.cutCarrier.Carrier} (hx : x ∈ T.pairing.gluing.block k) :
    T.cutMap x ∈ T.seamSurface k := by
  rcases hx with hx | hx
  · refine ⟨(T.pairing.leftParam k).symm ⟨x, hx⟩, ?_⟩
    rw [seamTorus_eq_cutMap, Homeomorph.apply_symm_apply]
  · refine ⟨(T.pairing.matching k).symm ((T.pairing.rightParam k).symm ⟨x, hx⟩), ?_⟩
    rw [seamTorus_eq_cutMap_right, Diffeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]

theorem boundaryPoint_inl_iff (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) (a : (T.subCarrier Sᶜ).Carrier) :
    T.cutCarrier.model.IsBoundaryPoint (Sum.inl a : T.ContractCut S hext hk) ↔
      T.cutCarrier.model.IsBoundaryPoint a.val := by
  have hv := ModelWithCorners.isBoundaryPoint_iff_isBoundaryPoint_val (I := T.cutCarrier.model)
    (u := T.subPiece Sᶜ) (x := a)
  constructor
  · intro h
    by_contra h'
    have hi : T.cutCarrier.model.IsInteriorPoint a :=
      (T.cutCarrier.model.isInteriorPoint_iff_not_isBoundaryPoint a).mpr fun hb => h' (hv.mp hb)
    exact (T.cutCarrier.model.isInteriorPoint_iff_not_isBoundaryPoint _).mp
      (ModelWithCorners.interiorPoint_inl a hi) h
  · intro h
    exact ModelWithCorners.boundaryPoint_inl a (hv.mpr h)

theorem boundaryPoint_inr_iff (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) (r : (T.contractRegion S hext hk).Carrier) :
    T.cutCarrier.model.IsBoundaryPoint (Sum.inr r : T.ContractCut S hext hk) ↔
      r.val ∈ T.crossingSurface S := by
  have hr : T.cutCarrier.model.IsBoundaryPoint r ↔ r.val ∈ T.crossingSurface S := by
    rw [ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint]
    exact not_iff_comm.mp (T.region_isInteriorPoint_iff S hext hk r).symm
  constructor
  · intro h
    by_contra h'
    have hi : T.cutCarrier.model.IsInteriorPoint r :=
      (T.cutCarrier.model.isInteriorPoint_iff_not_isBoundaryPoint r).mpr fun hb => h' (hr.mp hb)
    exact (T.cutCarrier.model.isInteriorPoint_iff_not_isBoundaryPoint _).mp
      (ModelWithCorners.interiorPoint_inr r hi) h
  · intro h
    exact ModelWithCorners.boundaryPoint_inr r (hr.mpr h)

theorem contractMap_mem_boundary (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) {x : T.cutCarrier.Carrier}
    (hx : x ∈ T.cutCarrier.model.boundary T.cutCarrier.Carrier)
    (hni : ∀ k, x ∈ T.pairing.gluing.block k → ¬(T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)) :
    T.cutCarrier.model.IsBoundaryPoint (T.contractMap S hext hk x) := by
  by_cases hc : x ∈ T.subPiece Sᶜ
  · rw [T.contractMap_of_mem S hext hk hc]
    exact (T.boundaryPoint_inl_iff S hext hk ⟨x, hc⟩).mpr hx
  · rw [T.contractMap_of_not_mem S hext hk hc]
    refine (T.boundaryPoint_inr_iff S hext hk _).mpr ?_
    have hxS := T.mem_subPiece_of_not_mem_compl S hc
    have hx' := hx
    rw [T.cut_boundary_exhausted] at hx'
    rcases hx' with hb | he
    · obtain ⟨k, hkb⟩ := Set.mem_iUnion.mp hb
      have hnk := hni k hkb
      refine Set.mem_iUnion₂.mpr ⟨k, ?_, T.cutMap_mem_seamSurface_of_block' k hkb⟩
      rcases hkb with hl | hr
      · have hlS := T.mem_of_mem_subPiece S hxS (T.left_owned k hl)
        exact Or.inl ⟨hlS, fun hrS => hnk ⟨hlS, hrS⟩⟩
      · have hrS := T.mem_of_mem_subPiece S hxS (T.right_owned k hr)
        exact Or.inr ⟨hrS, fun hlS => hnk ⟨hlS, hrS⟩⟩
    · obtain ⟨i, t, rfl⟩ := Set.mem_iUnion.mp he
      exact (hext i (T.mem_of_mem_subPiece S hxS (T.external_owned i ⟨t, rfl⟩))).elim

theorem block_unique {x : T.cutCarrier.Carrier} {k k' : Fin T.pairing.count}
    (hk : x ∈ T.pairing.gluing.block k) (hk' : x ∈ T.pairing.gluing.block k') : k' = k := by
  by_contra h
  exact (T.pairing.gluing.disjoint_blocks k' k h).le_bot ⟨hk', hk⟩

theorem contractLeftPoint_equivFin (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) (b : T.NonInternal S) (t : Torus) :
    T.contractLeftPoint S hext hk (Fintype.equivFin _ b) t =
      T.contractMap S hext hk (T.pairing.leftParam b.val t).val := by
  unfold contractLeftPoint
  rw [nonInternal_equivFin]

theorem contractRightPoint_equivFin (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) (b : T.NonInternal S) (t : Torus) :
    T.contractRightPoint S hext hk (Fintype.equivFin _ b) t =
      T.contractMap S hext hk (T.pairing.rightParam b.val t).val := by
  unfold contractRightPoint
  rw [nonInternal_equivFin]

theorem contractMap_mem_boundary_of_block (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) (j : Fin (Fintype.card (T.NonInternal S)))
    {x : T.cutCarrier.Carrier} (hx : x ∈ T.pairing.gluing.block (T.nonInternal S j).val) :
    T.cutCarrier.model.IsBoundaryPoint (T.contractMap S hext hk x) := by
  refine T.contractMap_mem_boundary S hext hk ?_ fun k' hk' => ?_
  · rw [T.cut_boundary_exhausted]
    exact Or.inl (Set.mem_iUnion.mpr ⟨_, hx⟩)
  · rw [T.block_unique hx hk']
    exact (T.nonInternal S j).property

theorem contractCut_boundary (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) :
    (T.contractCut S hext hk).model.boundary (T.contractCut S hext hk).Carrier =
      (⋃ j, (T.contractPairing S hext hk).gluing.block j) ∪
        (T.contractCutExternal S hext hk).image := by
  ext y
  constructor
  · intro hy
    rcases y with a | r
    · have ha : T.cutCarrier.model.IsBoundaryPoint a.val :=
        (T.boundaryPoint_inl_iff S hext hk a).mp hy
      obtain ⟨s, t, hst⟩ := T.exists_sideCollar_zero_eq ha
      have hpiece := (T.sideCollar_zero_mem s t).2
      rw [hst] at hpiece
      have hsc : T.sidePiece s ∉ S := fun h =>
        Finset.mem_compl.mp (T.mem_of_mem_subPiece Sᶜ a.property hpiece) h
      have ha' : T.contractMap S hext hk a.val = Sum.inl a :=
        T.contractMap_of_mem S hext hk a.property
      rcases s with k | k | i
      · let b : T.NonInternal S := ⟨k, fun h => hsc h.1⟩
        refine Or.inl (Set.mem_iUnion.mpr ⟨Fintype.equivFin _ b, Or.inl ⟨t, ?_⟩⟩)
        rw [T.contractLeftPoint_equivFin S hext hk b t, ← T.pairing.left_zero]
        change T.contractMap S hext hk (T.sideCollar (.inl k) (t, halfZero)) = _
        rw [hst, ha']
      · let b : T.NonInternal S := ⟨k, fun h => hsc h.2⟩
        refine Or.inl (Set.mem_iUnion.mpr ⟨Fintype.equivFin _ b, Or.inr ⟨t, ?_⟩⟩)
        rw [T.contractRightPoint_equivFin S hext hk b t, ← T.pairing.right_zero]
        change T.contractMap S hext hk (T.sideCollar (.inr (.inl k)) (t, halfZero)) = _
        rw [hst, ha']
      · refine Or.inr (Set.mem_iUnion.mpr ⟨i, t, ?_⟩)
        change T.contractExternalCollar S hext hk i (t, halfZero) = _
        rw [T.contractExternalCollar_apply S hext hk i (zero_mem_halfCollarSource t)]
        change T.contractMap S hext hk (T.sideCollar (.inr (.inr i)) (t, halfZero)) = _
        rw [hst, ha']
    · have hr : r.val ∈ T.crossingSurface S := (T.boundaryPoint_inr_iff S hext hk r).mp hy
      obtain ⟨k, hkc, t, ht⟩ := Set.mem_iUnion₂.mp hr
      rcases hkc with ⟨hl, hr'⟩ | ⟨hr', hl⟩
      · let b : T.NonInternal S := ⟨k, fun h => hr' h.2⟩
        refine Or.inl (Set.mem_iUnion.mpr ⟨Fintype.equivFin _ b, Or.inl ⟨t, ?_⟩⟩)
        rw [T.contractLeftPoint_equivFin S hext hk b t,
          T.contractMap_of_not_mem S hext hk (T.not_mem_subPiece_compl_of_piece S
            (T.left_owned k (T.pairing.leftParam k t).property) hl)]
        refine congrArg Sum.inr (Subtype.ext ?_)
        change T.cutMap (T.pairing.leftParam k t).val = r.val
        rw [← ht, seamTorus_eq_cutMap]
      · let b : T.NonInternal S := ⟨k, fun h => hl h.1⟩
        refine Or.inl (Set.mem_iUnion.mpr ⟨Fintype.equivFin _ b,
          Or.inr ⟨T.pairing.matching k t, ?_⟩⟩)
        rw [T.contractRightPoint_equivFin S hext hk b,
          T.contractMap_of_not_mem S hext hk (T.not_mem_subPiece_compl_of_piece S
            (T.right_owned k (T.pairing.rightParam k _).property) hr')]
        refine congrArg Sum.inr (Subtype.ext ?_)
        change T.cutMap (T.pairing.rightParam k (T.pairing.matching k t)).val = r.val
        rw [← ht, seamTorus_eq_cutMap_right]
  · rintro (hy | hy)
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hy
      rcases hj with ⟨t, rfl⟩ | ⟨t, rfl⟩
      · exact T.contractMap_mem_boundary_of_block S hext hk j
          (Or.inl (T.pairing.leftParam _ t).property)
      · exact T.contractMap_mem_boundary_of_block S hext hk j
          (Or.inr (T.pairing.rightParam _ t).property)
    · obtain ⟨i, t, rfl⟩ := Set.mem_iUnion.mp hy
      exact (T.contractCutExternal S hext hk).boundary_zero i t

theorem contract_external_disjoint (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) :
    Disjoint (⋃ j, (T.contractPairing S hext hk).gluing.block j)
      (T.contractCutExternal S hext hk).image := by
  rw [Set.disjoint_left]
  intro y hy hy'
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hy
  obtain ⟨i, t', rfl⟩ := Set.mem_iUnion.mp hy'
  have he : (T.contractCutExternal S hext hk).torusMap i t' =
      T.contractMap S hext hk (T.cutExternal.torusMap i t') :=
    T.contractExternalCollar_apply S hext hk i (zero_mem_halfCollarSource t')
  have hmem : T.cutExternal.torusMap i t' ∈ T.subPiece Sᶜ :=
    T.piece_subset_subPiece Sᶜ (T.externalPiece_mem_compl S hext i) (T.external_owned i ⟨t', rfl⟩)
  have himg : T.cutExternal.torusMap i t' ∈ T.cutExternal.image := Set.mem_iUnion.mpr ⟨i, t', rfl⟩
  rcases hj with ⟨t, ht⟩ | ⟨t, ht⟩
  · have hx := T.contractMap_inj_of_mem S hext hk hmem (he.symm.trans ht.symm)
    exact (T.external_disjoint).le_bot ⟨Set.mem_iUnion.mpr ⟨_, hx ▸ Or.inl
      (T.pairing.leftParam _ t).property⟩, himg⟩
  · have hx := T.contractMap_inj_of_mem S hext hk hmem (he.symm.trans ht.symm)
    exact (T.external_disjoint).le_bot ⟨Set.mem_iUnion.mpr ⟨_, hx ▸ Or.inr
      (T.pairing.rightParam _ t).property⟩, himg⟩

theorem contractLeftParam_apply (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) (j : Fin (Fintype.card (T.NonInternal S)))
    (t : Torus) :
    ((T.contractLeftParam S hext hk j t) : T.ContractCut S hext hk) =
      T.contractLeftPoint S hext hk j t := rfl

theorem contractRightParam_apply (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) (j : Fin (Fintype.card (T.NonInternal S)))
    (t : Torus) :
    ((T.contractRightParam S hext hk j t) : T.ContractCut S hext hk) =
      T.contractRightPoint S hext hk j t := rfl

theorem contractGluing_flip_left (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) (j : Fin (Fintype.card (T.NonInternal S)))
    (t : Torus) :
    (T.contractGluing S hext hk).flip j (T.contractLeftPoint S hext hk j t) =
      T.contractRightPoint S hext hk j (T.pairing.matching (T.nonInternal S j).val t) := by
  have hmem : T.contractLeftPoint S hext hk j t ∈ (T.contractGluing S hext hk).left j := ⟨t, rfl⟩
  rw [(T.contractGluing S hext hk).flip_of_mem_left hmem]
  have e : (T.contractLeftParam S hext hk j).symm ⟨T.contractLeftPoint S hext hk j t, ⟨t, rfl⟩⟩ =
      t := (T.contractLeftParam S hext hk j).symm_apply_apply t
  change ((T.contractRightParam S hext hk j) ((T.pairing.matching _)
    ((T.contractLeftParam S hext hk j).symm ⟨T.contractLeftPoint S hext hk j t, ⟨t, rfl⟩⟩)) :
      T.ContractCut S hext hk) = _
  rw [e]
  rfl

theorem contractGluing_flip_right (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) (j : Fin (Fintype.card (T.NonInternal S)))
    (t : Torus) :
    (T.contractGluing S hext hk).flip j (T.contractRightPoint S hext hk j t) =
      T.contractLeftPoint S hext hk j ((T.pairing.matching (T.nonInternal S j).val).symm t) := by
  have hmem : T.contractRightPoint S hext hk j t ∈ (T.contractGluing S hext hk).right j :=
    ⟨t, rfl⟩
  rw [(T.contractGluing S hext hk).flip_of_mem_right hmem]
  have e : (T.contractRightParam S hext hk j).symm ⟨T.contractRightPoint S hext hk j t, ⟨t, rfl⟩⟩ =
      t := (T.contractRightParam S hext hk j).symm_apply_apply t
  change ((T.contractLeftParam S hext hk j) ((T.pairing.matching _).toHomeomorph.symm
    ((T.contractRightParam S hext hk j).symm ⟨T.contractRightPoint S hext hk j t, ⟨t, rfl⟩⟩)) :
      T.ContractCut S hext hk) = _
  rw [e]
  rfl

theorem contractMap_flip (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) (j : Fin (Fintype.card (T.NonInternal S)))
    {x : T.cutCarrier.Carrier} (hx : x ∈ T.pairing.gluing.block (T.nonInternal S j).val) :
    T.contractMap S hext hk x ∈ (T.contractGluing S hext hk).block j ∧
      (T.contractGluing S hext hk).flip j (T.contractMap S hext hk x) =
        T.contractMap S hext hk (T.pairing.gluing.flip (T.nonInternal S j).val x) := by
  set k := (T.nonInternal S j).val
  rcases hx with hl | hr
  · obtain ⟨t, ht⟩ : ∃ t, (T.pairing.leftParam k t).val = x :=
      ⟨(T.pairing.leftParam k).symm ⟨x, hl⟩, by rw [Homeomorph.apply_symm_apply]⟩
    subst ht
    refine ⟨Or.inl ⟨t, rfl⟩, ?_⟩
    rw [show T.contractMap S hext hk (T.pairing.leftParam k t).val =
      T.contractLeftPoint S hext hk j t from rfl, T.contractGluing_flip_left,
      T.pairing.gluing.flip_of_mem_left (T.pairing.leftParam k t).property]
    change T.contractMap S hext hk (T.pairing.rightParam k (T.pairing.matching k t)).val = _
    rw [← T.pairing.matching_eq]
  · obtain ⟨t, ht⟩ : ∃ t, (T.pairing.rightParam k t).val = x :=
      ⟨(T.pairing.rightParam k).symm ⟨x, hr⟩, by rw [Homeomorph.apply_symm_apply]⟩
    subst ht
    refine ⟨Or.inr ⟨t, rfl⟩, ?_⟩
    rw [show T.contractMap S hext hk (T.pairing.rightParam k t).val =
      T.contractRightPoint S hext hk j t from rfl, T.contractGluing_flip_right,
      T.pairing.gluing.flip_of_mem_right (T.pairing.rightParam k t).property]
    change T.contractMap S hext hk (T.pairing.leftParam k ((T.pairing.matching k).symm t)).val = _
    have h := T.pairing.matching_eq k ((T.pairing.matching k).symm t)
    rw [Diffeomorph.apply_symm_apply] at h
    have h2 : (T.pairing.gluing.attaching k).symm (T.pairing.rightParam k t) =
        T.pairing.leftParam k ((T.pairing.matching k).symm t) := by
      rw [← h, Homeomorph.symm_apply_apply]
    rw [h2]

theorem not_mem_compl_of_mem {x : T.cutCarrier.Carrier} (hx : x ∈ T.subPiece S) :
    x ∉ T.subPiece Sᶜ := by
  obtain ⟨i, hi, hxi⟩ := (T.mem_subPiece S).mp hx
  exact T.not_mem_subPiece_compl_of_piece S hxi hi

theorem contractMap_surjective (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) : Function.Surjective (T.contractMap S hext hk) := by
  intro y
  rcases y with a | r
  · exact ⟨a.val, T.contractMap_of_mem S hext hk a.property⟩
  · obtain ⟨q, hq⟩ := r.property
    obtain ⟨z, rfl⟩ := Quotient.exists_rep q
    have hz : z.val ∉ T.subPiece Sᶜ := T.not_mem_compl_of_mem S z.property
    refine ⟨z.val, ?_⟩
    rw [T.contractMap_of_not_mem S hext hk hz]
    exact congrArg Sum.inr (Subtype.ext hq)

theorem contract_rel_of_cutMap_eq (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) {a b : T.cutCarrier.Carrier}
    (h : T.cutMap a = T.cutMap b) :
    (T.contractGluing S hext hk).rel (T.contractMap S hext hk a) (T.contractMap S hext hk b) := by
  rcases Quotient.exact (T.reconstruction.injective h) with hab | ⟨k, hka, hb⟩
  · exact Or.inl (congrArg _ hab)
  by_cases hint : T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S
  · have hblock : ∀ x ∈ T.pairing.gluing.block k, x ∉ T.subPiece Sᶜ := by
      rintro x (hl | hr)
      · exact T.not_mem_subPiece_compl_of_piece S (T.left_owned k hl) hint.1
      · exact T.not_mem_subPiece_compl_of_piece S (T.right_owned k hr) hint.2
    have hbk : b ∈ T.pairing.gluing.block k := hb ▸ T.pairing.gluing.flip_mem_block hka
    left
    rw [T.contractMap_of_not_mem S hext hk (hblock a hka),
      T.contractMap_of_not_mem S hext hk (hblock b hbk)]
    exact congrArg Sum.inr (Subtype.ext h)
  · have hx : a ∈ T.pairing.gluing.block (T.nonInternal S (Fintype.equivFin _ ⟨k, hint⟩)).val := by
      rw [nonInternal_equivFin]
      exact hka
    obtain ⟨hmem, hflip⟩ := T.contractMap_flip S hext hk _ hx
    rw [nonInternal_equivFin] at hflip
    refine Or.inr ⟨_, hmem, ?_⟩
    rw [hflip, hb]

theorem contractFold_rel (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) {x y : T.ContractCut S hext hk}
    (h : (T.contractGluing S hext hk).rel x y) :
    T.contractFold S hext hk x = T.contractFold S hext hk y := by
  rcases h with rfl | ⟨j, hx, rfl⟩
  · rfl
  have key : ∀ z ∈ T.pairing.gluing.block (T.nonInternal S j).val,
      T.contractFold S hext hk ((T.contractGluing S hext hk).flip j (T.contractMap S hext hk z)) =
        T.contractFold S hext hk (T.contractMap S hext hk z) := by
    intro z hz
    rw [(T.contractMap_flip S hext hk j hz).2, contractFold_contractMap, contractFold_contractMap]
    exact congrArg T.reconstruction (Quotient.sound'
      (Or.inr ⟨_, hz, rfl⟩ : T.pairing.gluing.rel z _)).symm
  rcases hx with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · exact (key _ (Or.inl (T.pairing.leftParam _ t).property)).symm
  · exact (key _ (Or.inr (T.pairing.rightParam _ t).property)).symm

def contractQuotientFold (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) :
    (T.contractPairing S hext hk).QuotientSpace → W.Carrier :=
  Quotient.lift (T.contractFold S hext hk) fun _ _ h => T.contractFold_rel S hext hk h

private theorem cutMap_surjective_aux : Function.Surjective T.cutMap := by
  intro w
  obtain ⟨x, hx⟩ := Quotient.exists_rep (T.reconstruction.symm w)
  refine ⟨x, ?_⟩
  change T.reconstruction (Quotient.mk _ x) = w
  rw [hx, Homeomorph.apply_symm_apply]

theorem contractQuotientFold_bijective (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) :
    Function.Bijective (T.contractQuotientFold S hext hk) := by
  constructor
  · intro p q h
    obtain ⟨x, rfl⟩ := Quotient.exists_rep p
    obtain ⟨y, rfl⟩ := Quotient.exists_rep q
    obtain ⟨a, rfl⟩ := T.contractMap_surjective S hext hk x
    obtain ⟨b, rfl⟩ := T.contractMap_surjective S hext hk y
    have hab : T.cutMap a = T.cutMap b := by
      have h' : T.contractFold S hext hk (T.contractMap S hext hk a) =
          T.contractFold S hext hk (T.contractMap S hext hk b) := h
      rwa [contractFold_contractMap, contractFold_contractMap] at h'
    exact Quotient.sound (T.contract_rel_of_cutMap_eq S hext hk hab)
  · intro w
    obtain ⟨a, rfl⟩ := T.cutMap_surjective_aux w
    exact ⟨Quotient.mk _ (T.contractMap S hext hk a), T.contractFold_contractMap S hext hk a⟩

def contractReconstruction (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) :
    (T.contractPairing S hext hk).QuotientSpace ≃ₜ W.Carrier :=
  @Continuous.homeoOfEquivCompactToT2 _ _ _ _ _ _
    (Equiv.ofBijective _ (T.contractQuotientFold_bijective S hext hk))
    (continuous_quot_lift _ (T.contMDiff_contractFold S hext hk).continuous)

theorem contractReconstruction_quotientMap (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) (x : T.ContractCut S hext hk) :
    T.contractReconstruction S hext hk ((T.contractPairing S hext hk).quotientMap x) =
      T.contractFold S hext hk x := rfl

theorem contract_seam_zero (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) (j : Fin (Fintype.card (T.NonInternal S)))
    (t : Torus) :
    T.seam (T.nonInternal S j).val (t, 0) = T.contractReconstruction S hext hk
      ((T.contractPairing S hext hk).quotientMap ((T.contractPairing S hext hk).leftParam j t)) :=
  (T.contractFold_leftPoint S hext hk j t).symm

theorem contract_seam_positive (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) (j : Fin (Fintype.card (T.NonInternal S)))
    (t : Torus) (s : ℝ) (hs : 0 ≤ s) (h : s < 1) :
    T.seam (T.nonInternal S j).val (t, s) = T.contractReconstruction S hext hk
      ((T.contractPairing S hext hk).quotientMap ((T.contractPairing S hext hk).rightCollar j
        ((T.contractPairing S hext hk).matching j t, halfPoint s hs))) := by
  rw [contractReconstruction_quotientMap]
  change _ = T.contractFold S hext hk (T.contractRightCollar S hext hk j
    (T.pairing.matching _ t, halfPoint s hs))
  rw [T.contractRightCollar_apply S hext hk j (show (T.pairing.matching _ t, halfPoint s hs) ∈
    halfCollarSource from h), contractFold_contractMap]
  exact T.seam_positive _ t s hs h

theorem contract_seam_negative (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) (j : Fin (Fintype.card (T.NonInternal S)))
    (t : Torus) (s : ℝ) (hs : s ≤ 0) (h : -1 < s) :
    T.seam (T.nonInternal S j).val (t, s) = T.contractReconstruction S hext hk
      ((T.contractPairing S hext hk).quotientMap ((T.contractPairing S hext hk).leftCollar j
        (t, halfPoint (-s) (neg_nonneg.mpr hs)))) := by
  rw [contractReconstruction_quotientMap]
  change _ = T.contractFold S hext hk (T.contractLeftCollar S hext hk j
    (t, halfPoint (-s) (neg_nonneg.mpr hs)))
  rw [T.contractLeftCollar_apply S hext hk j (show (t, halfPoint (-s) (neg_nonneg.mpr hs)) ∈
    halfCollarSource from show -s < 1 by linarith), contractFold_contractMap]
  exact T.seam_negative _ t s hs h

theorem contract_marked_collar (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) (i : Fin T.externalCount)
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    T.contractReconstruction S hext hk ((T.contractPairing S hext hk).quotientMap
      ((T.contractCutExternal S hext hk).collar i p)) = T.external.collar i p := by
  rw [contractReconstruction_quotientMap]
  change T.contractFold S hext hk (T.contractExternalCollar S hext hk i p) = _
  rw [T.contractExternalCollar_apply S hext hk i hp, contractFold_contractMap]
  exact T.marked_collar i p hp

open Classical in
def contractLeftPiece (j : Fin (Fintype.card (T.NonInternal S))) : Fin (Sᶜ.card + 1) :=
  if hl : T.leftPiece (T.nonInternal S j).val ∈ S then Fin.last _
  else (T.subIndexOf Sᶜ (Finset.mem_compl.mpr hl)).castSucc

open Classical in
def contractRightPiece (j : Fin (Fintype.card (T.NonInternal S))) : Fin (Sᶜ.card + 1) :=
  if hr : T.rightPiece (T.nonInternal S j).val ∈ S then Fin.last _
  else (T.subIndexOf Sᶜ (Finset.mem_compl.mpr hr)).castSucc

def contractExternalPiece (hext : ∀ i, T.externalPiece i ∉ S) (i : Fin T.externalCount) :
    Fin (Sᶜ.card + 1) :=
  (T.subIndexOf Sᶜ (T.externalPiece_mem_compl S hext i)).castSucc

theorem contractMap_mem_piece (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) {x : T.cutCarrier.Carrier}
    {i : Fin T.components.count} (hx : x ∈ T.components.piece i) :
    T.contractMap S hext hk x ∈ (T.contractPiece S hext hk
      (if hi : i ∈ S then Fin.last _ else (T.subIndexOf Sᶜ (Finset.mem_compl.mpr hi)).castSucc) :
        Set (T.contractCut S hext hk).Carrier) := by
  by_cases hi : i ∈ S
  · rw [dite_eq_left hi, contractPiece_last,
      T.contractMap_of_not_mem S hext hk (T.not_mem_subPiece_compl_of_piece S hx hi)]
    exact ⟨_, rfl⟩
  · have hxc : x ∈ T.subPiece Sᶜ := T.piece_subset_subPiece Sᶜ (Finset.mem_compl.mpr hi) hx
    rw [dite_eq_right hi, contractPiece_castSucc, T.contractMap_of_mem S hext hk hxc]
    refine ⟨⟨x, hxc⟩, ?_, rfl⟩
    change x ∈ T.components.piece (T.subIndex Sᶜ (T.subIndexOf Sᶜ _))
    rw [subIndex_subIndexOf]
    exact hx

theorem contract_left_owned (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary)
    (hconn : IsConnected (Set.range (T.restrictMap S) \ T.crossingSurface S))
    (j : Fin (Fintype.card (T.NonInternal S))) :
    (T.contractPairing S hext hk).gluing.left j ⊆
      (T.contractComponents S hext hk hconn).piece (T.contractLeftPiece S j) := by
  rintro _ ⟨t, rfl⟩
  exact T.contractMap_mem_piece S hext hk (T.left_owned _ (T.pairing.leftParam _ t).property)

theorem contract_right_owned (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary)
    (hconn : IsConnected (Set.range (T.restrictMap S) \ T.crossingSurface S))
    (j : Fin (Fintype.card (T.NonInternal S))) :
    (T.contractPairing S hext hk).gluing.right j ⊆
      (T.contractComponents S hext hk hconn).piece (T.contractRightPiece S j) := by
  rintro _ ⟨t, rfl⟩
  exact T.contractMap_mem_piece S hext hk (T.right_owned _ (T.pairing.rightParam _ t).property)

theorem contract_external_owned (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary)
    (hconn : IsConnected (Set.range (T.restrictMap S) \ T.crossingSurface S))
    (i : Fin T.externalCount) :
    Set.range ((T.contractCutExternal S hext hk).torusMap i) ⊆
      (T.contractComponents S hext hk hconn).piece (T.contractExternalPiece S hext i) := by
  rintro _ ⟨t, rfl⟩
  have h := T.contractMap_mem_piece S hext hk (T.external_owned i ⟨t, rfl⟩)
  rw [dite_eq_right (hext i)] at h
  have he : (T.contractCutExternal S hext hk).torusMap i t =
      T.contractMap S hext hk (T.cutExternal.torusMap i t) :=
    T.contractExternalCollar_apply S hext hk i (zero_mem_halfCollarSource t)
  rw [he]
  exact h

theorem contractComponents_count (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary)
    (hconn : IsConnected (Set.range (T.restrictMap S) \ T.crossingSurface S)) :
    (T.contractComponents S hext hk hconn).count = T.components.count - S.card + 1 := by
  change Sᶜ.card + 1 = _
  rw [Finset.card_compl, Fintype.card_fin]

theorem contractPairing_count (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) :
    (T.contractPairing S hext hk).count = T.pairing.count -
      (Finset.univ.filter fun k => T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S).card := by
  change Fintype.card (T.NonInternal S) = _
  rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype]

theorem isLocalDiffeomorphAt_cutMap {y : T.cutCarrier.Carrier}
    (hy : T.cutCarrier.model.IsInteriorPoint y) :
    IsLocalDiffeomorphAt T.cutCarrier.model W.model ∞ T.cutMap y := by
  have hne : Nonempty T.cutCarrier.interior := ⟨⟨y, hy⟩⟩
  have hne' : Nonempty T.interiorImage := ⟨T.interiorDiffeomorph ⟨y, hy⟩⟩
  let Φ := ((DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph T.cutCarrier.model
    T.cutCarrier.interior hne).symm.trans T.interiorDiffeomorph.toPartialDiffeomorph).trans
    (DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph W.model T.interiorImage hne')
  have hsrc : (T.cutCarrier.interior : Set T.cutCarrier.Carrier) ⊆ Φ.source := by
    intro z hz
    refine ⟨⟨?_, trivial⟩, trivial⟩
    change z ∈ (DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph T.cutCarrier.model
      T.cutCarrier.interior hne).target
    rw [DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target]
    exact hz
  refine IsLocalDiffeomorphAt.of_eventuallyEq ?_
    (Φ.isLocalDiffeomorphAt T.cutCarrier.model W.model ∞ (hsrc hy))
  filter_upwards [T.cutCarrier.interior.isOpen.mem_nhds hy] with z hz
  change T.cutMap z = (T.interiorDiffeomorph
    ((DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph
      T.cutCarrier.model T.cutCarrier.interior hne).symm z)).val
  rw [DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_symm_apply _ _ _ hz,
    T.interior_map]
  rfl

theorem isLocalDiffeomorphAt_contractFold_inl (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) (a : (T.subCarrier Sᶜ).Carrier)
    (ha : T.cutCarrier.model.IsInteriorPoint a.val) :
    IsLocalDiffeomorphAt T.cutCarrier.model W.model ∞ (T.contractFold S hext hk)
      (Sum.inl a) := by
  let P : PartialDiffeomorph T.cutCarrier.model T.cutCarrier.model (T.subCarrier Sᶜ).Carrier
      (T.ContractCut S hext hk) ∞ :=
    sumInlPD (I := T.cutCarrier.model)
      (Diffeomorph.refl T.cutCarrier.model (T.subCarrier Sᶜ).Carrier ∞).toPartialDiffeomorph a
  have hP : IsLocalDiffeomorphAt T.cutCarrier.model T.cutCarrier.model ∞ P.symm (Sum.inl a) :=
    P.symm.isLocalDiffeomorphAt T.cutCarrier.model T.cutCarrier.model ∞ ⟨a, trivial, rfl⟩
  have hne : Nonempty (T.subPiece Sᶜ) := ⟨a⟩
  have hsub : IsLocalDiffeomorphAt T.cutCarrier.model T.cutCarrier.model ∞
      (Subtype.val : T.subPiece Sᶜ → T.cutCarrier.Carrier) a :=
    (DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph T.cutCarrier.model
      (T.subPiece Sᶜ) hne).isLocalDiffeomorphAt T.cutCarrier.model T.cutCarrier.model ∞
      (Set.mem_univ _)
  have hsub' : IsLocalDiffeomorphAt T.cutCarrier.model T.cutCarrier.model ∞
      (fun b : (T.subCarrier Sᶜ).Carrier => b.val) (P.symm (Sum.inl a)) := hsub
  have hcut' : IsLocalDiffeomorphAt T.cutCarrier.model W.model ∞ T.cutMap
      ((fun b : (T.subCarrier Sᶜ).Carrier => b.val) (P.symm (Sum.inl a))) :=
    T.isLocalDiffeomorphAt_cutMap ha
  have hc1 := hP.comp (K := T.cutCarrier.model) (P := T.cutCarrier.Carrier) hsub'
  have hc := hc1.comp (K := W.model) (P := W.Carrier) hcut'
  refine IsLocalDiffeomorphAt.of_eventuallyEq ?_ hc
  filter_upwards [isOpen_range_inl.mem_nhds (Set.mem_range_self a)] with z hz
  obtain ⟨b, rfl⟩ := hz
  rfl

theorem isLocalDiffeomorphAt_contractFold_inr (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) (r : (T.contractRegion S hext hk).Carrier)
    (hr : r.val ∉ T.crossingSurface S) :
    IsLocalDiffeomorphAt T.cutCarrier.model W.model ∞ (T.contractFold S hext hk)
      (Sum.inr r) := by
  have hrint : r.val ∈ interior (Set.range (T.restrictMap S)) :=
    interior_maximal Set.sdiff_subset (T.isOpen_range_diff_crossingSurface S) ⟨r.property, hr⟩
  let P : PartialDiffeomorph T.cutCarrier.model T.cutCarrier.model
      (T.contractRegion S hext hk).Carrier (T.ContractCut S hext hk) ∞ :=
    sumInrPD (I := T.cutCarrier.model)
      (Diffeomorph.refl T.cutCarrier.model (T.contractRegion S hext hk).Carrier
        ∞).toPartialDiffeomorph r
  have hP : IsLocalDiffeomorphAt T.cutCarrier.model T.cutCarrier.model ∞ P.symm (Sum.inr r) :=
    P.symm.isLocalDiffeomorphAt T.cutCarrier.model T.cutCarrier.model ∞ ⟨r, trivial, rfl⟩
  have hreg : IsLocalDiffeomorphAt T.cutCarrier.model W.model ∞
      (fun z : (T.contractRegion S hext hk).Carrier => z.val) r :=
    (recast_isLocalDiffeomorphAt_iff _ _ _ _ r).mpr
      ((T.restrictAtlas S hext).isLocalDiffeomorphAt_subtype_val hrint)
  have hreg' : IsLocalDiffeomorphAt T.cutCarrier.model W.model ∞
      (fun z : (T.contractRegion S hext hk).Carrier => z.val) (P.symm (Sum.inr r)) := hreg
  have hc := hP.comp (K := W.model) (P := W.Carrier) hreg'
  refine IsLocalDiffeomorphAt.of_eventuallyEq ?_ hc
  filter_upwards [isOpen_range_inr.mem_nhds (Set.mem_range_self r)] with z hz
  obtain ⟨b, rfl⟩ := hz
  rfl

private theorem eq_of_cutMap_eq_of_isInteriorPoint' {y x : T.cutCarrier.Carrier}
    (hy : T.cutCarrier.model.IsInteriorPoint y) (h : T.cutMap y = T.cutMap x) : y = x := by
  refine T.pairing.gluing.eq_of_rel_of_notMem (fun i hi => ?_)
    (Quotient.exact (T.reconstruction.injective h))
  have hb : y ∈ T.cutCarrier.model.boundary T.cutCarrier.Carrier := by
    rw [T.cut_boundary_exhausted]
    exact Or.inl (Set.mem_iUnion.mpr ⟨i, hi⟩)
  exact (T.cutCarrier.model.isInteriorPoint_iff_not_isBoundaryPoint y).mp hy hb

theorem isLocalDiffeomorph_contractInteriorFold (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) :
    IsLocalDiffeomorph (T.contractCut S hext hk).model W.model ∞
      (fun x : (T.contractCut S hext hk).interior => T.contractFold S hext hk x.val) := by
  intro x
  have hne : Nonempty (T.contractCut S hext hk).interior := ⟨x⟩
  have hval : IsLocalDiffeomorphAt T.cutCarrier.model T.cutCarrier.model ∞
      (Subtype.val : (T.contractCut S hext hk).interior → T.ContractCut S hext hk) x :=
    (DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph T.cutCarrier.model
      (T.contractCut S hext hk).interior hne).isLocalDiffeomorphAt T.cutCarrier.model
      T.cutCarrier.model ∞ (Set.mem_univ x)
  have hfold : IsLocalDiffeomorphAt T.cutCarrier.model W.model ∞ (T.contractFold S hext hk)
      x.val := by
    have hxi : T.cutCarrier.model.IsInteriorPoint x.val := x.property
    rcases hx : x.val with a | r
    · rw [hx] at hxi
      have ha : T.cutCarrier.model.IsInteriorPoint a :=
        ModelWithCorners.isInteriorPoint_disjointUnion_left hxi rfl
      exact T.isLocalDiffeomorphAt_contractFold_inl S hext hk a
        ((ModelWithCorners.isInteriorPoint_iff_isInteriorPoint_val (I := T.cutCarrier.model)
          (u := T.subPiece Sᶜ) (x := a)).mp ha)
    · rw [hx] at hxi
      have hr : T.cutCarrier.model.IsInteriorPoint r :=
        ModelWithCorners.isInteriorPoint_disjointUnion_right hxi rfl
      exact T.isLocalDiffeomorphAt_contractFold_inr S hext hk r
        ((T.region_isInteriorPoint_iff S hext hk r).mp hr)
  exact hval.comp (K := W.model) (P := W.Carrier) hfold

theorem injective_contractInteriorFold (hext : ∀ i, T.externalPiece i ∉ S)
    (hk : T.cutCarrier.kind = .withBoundary) :
    Function.Injective
      (fun x : (T.contractCut S hext hk).interior => T.contractFold S hext hk x.val) := by
  have key : ∀ (a : (T.subCarrier Sᶜ).Carrier) (r : (T.contractRegion S hext hk).Carrier),
      T.cutCarrier.model.IsInteriorPoint r → T.cutMap a.val ≠ r.val := by
    intro a r hr h
    have hrc := (T.region_isInteriorPoint_iff S hext hk r).mp hr
    have ha : a.val ∉ T.subPiece S := by
      have := T.not_mem_compl_of_mem Sᶜ a.property
      rwa [compl_compl] at this
    exact hrc (T.range_inter_complImage_subset_crossing S ⟨r.property, ⟨a.val, ha, h⟩⟩)
  intro x y h
  have hxi : T.cutCarrier.model.IsInteriorPoint x.val := x.property
  have hyi : T.cutCarrier.model.IsInteriorPoint y.val := y.property
  apply Subtype.ext
  change T.contractFold S hext hk x.val = T.contractFold S hext hk y.val at h
  rcases hx : x.val with a | r <;> rcases hy : y.val with b | r' <;> rw [hx, hy] at h <;>
    rw [hx] at hxi <;> rw [hy] at hyi
  · have ha : T.cutCarrier.model.IsInteriorPoint a.val :=
      (ModelWithCorners.isInteriorPoint_iff_isInteriorPoint_val (I := T.cutCarrier.model)
        (u := T.subPiece Sᶜ) (x := a)).mp
        (ModelWithCorners.isInteriorPoint_disjointUnion_left hxi rfl)
    exact congrArg Sum.inl (Subtype.ext (T.eq_of_cutMap_eq_of_isInteriorPoint' ha h))
  · exact (key a r' (ModelWithCorners.isInteriorPoint_disjointUnion_right hyi rfl) h).elim
  · exact (key b r (ModelWithCorners.isInteriorPoint_disjointUnion_right hxi rfl) h.symm).elim
  · exact congrArg Sum.inr (Subtype.ext h)

def contract (hext : ∀ i, T.externalPiece i ∉ S) (hk : T.cutCarrier.kind = .withBoundary)
    (hconn : IsConnected (Set.range (T.restrictMap S) \ T.crossingSurface S)) :
    TorusPresentation W where
  cutCarrier := T.contractCut S hext hk
  components := T.contractComponents S hext hk hconn
  pairing := T.contractPairing S hext hk
  externalCount := T.externalCount
  external := T.external
  cutExternal := T.contractCutExternal S hext hk
  external_exhausted := T.external_exhausted
  cut_boundary_exhausted := T.contractCut_boundary S hext hk
  external_disjoint := T.contract_external_disjoint S hext hk
  reconstruction := T.contractReconstruction S hext hk
  quotient_smooth := T.contMDiff_contractFold S hext hk
  quotient_oriented := T.contractCut_oriented S hext hk
  interiorImage := (T.isLocalDiffeomorph_contractInteriorFold S hext hk).image
  interiorDiffeomorph := DifferentialGeometry.Topology.Manifold.diffeomorphOntoImage _
    (T.isLocalDiffeomorph_contractInteriorFold S hext hk)
    (T.injective_contractInteriorFold S hext hk)
  interior_map _ := rfl
  seam j := T.seam (T.nonInternal S j).val
  seam_source _ := T.seam_source _
  seam_zero := T.contract_seam_zero S hext hk
  seam_positive := T.contract_seam_positive S hext hk
  seam_negative := T.contract_seam_negative S hext hk
  seam_interior _ := T.seam_interior _
  seam_disjoint _ _ h := T.seam_disjoint fun e =>
    h ((Fintype.equivFin _).symm.injective (Subtype.ext e))
  marked_collar i _ hp := T.contract_marked_collar S hext hk i hp
  external_seam_disjoint i _ := T.external_seam_disjoint i _
  leftPiece := T.contractLeftPiece S
  rightPiece := T.contractRightPiece S
  left_owned := T.contract_left_owned S hext hk hconn
  right_owned := T.contract_right_owned S hext hk hconn
  externalPiece := T.contractExternalPiece S hext
  external_owned := T.contract_external_owned S hext hk hconn

section Contract
variable (hext : ∀ i, T.externalPiece i ∉ S) (hk : T.cutCarrier.kind = .withBoundary)
  (hconn : IsConnected (Set.range (T.restrictMap S) \ T.crossingSurface S))

theorem contract_components_count :
    (T.contract S hext hk hconn).components.count = T.components.count - S.card + 1 :=
  T.contractComponents_count S hext hk hconn

theorem contract_pairing_count :
    (T.contract S hext hk hconn).pairing.count = T.pairing.count -
      (Finset.univ.filter fun k => T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S).card :=
  T.contractPairing_count S hext hk

@[simp]
theorem contract_externalCount :
    (T.contract S hext hk hconn).externalCount = T.externalCount := rfl

theorem contract_external : (T.contract S hext hk hconn).external = T.external := rfl

theorem contract_reconstruction_eq (x : T.cutCarrier.Carrier) :
    (T.contract S hext hk hconn).reconstruction
      ((T.contract S hext hk hconn).pairing.quotientMap (T.contractMap S hext hk x)) =
        T.reconstruction (T.pairing.quotientMap x) :=
  T.contractFold_contractMap S hext hk x

theorem contract_seam (j : Fin (T.contract S hext hk hconn).pairing.count) :
    (T.contract S hext hk hconn).seam j = T.seam (T.nonInternal S j).val := rfl

end Contract

end TorusPresentation

end GC.Seifert
