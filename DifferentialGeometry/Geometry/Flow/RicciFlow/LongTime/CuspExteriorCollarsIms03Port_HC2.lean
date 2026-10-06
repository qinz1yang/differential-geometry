import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspExterior
import DifferentialGeometry.Geometry.Boundary.EmbeddingFrontier
import DifferentialGeometry.Geometry.Boundary.Model.EuclideanHalfSpace
import DifferentialGeometry.Topology.Manifold.OpenEmbedding
import DifferentialGeometry.Topology.Manifold.HalfCollarExtension
import DifferentialGeometry.Topology.Manifold.HalfLine
import DifferentialGeometry.Topology.Manifold.SmoothTwoSidedCollarRestriction
import DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem.ManifoldDerivative
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorphTrans
import DifferentialGeometry.Topology.OpenPartialHomeomorph.FiniteCollarFrontier
import DifferentialGeometry.Topology.LocallyFinite.Frontier
import DifferentialGeometry.Topology.Compactness.ProductChartThickening

import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.PersistentHyperbolicCores
import DifferentialGeometry.Geometry.Metric.Distance.Topology
import Mathlib.Topology.MetricSpace.Bounded
import DifferentialGeometry.Topology.Manifold.FiniteCollarDefiningFunction
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# S-MIRRORS port of IMS03 `CuspExteriorCollars` (`_HC2`)

This is `DifferentialGeometry/Geometry/Flow/RicciFlow/LongTime/CuspExteriorCollars.lean` of branch
`gc/juihuichung/ims03-astra-20261005` (tip `f49e541fb`).  That source does not compile against
this tree's toolchain and Mathlib (the lakefile, `lean-toolchain` and the Mathlib revision are
identical on both branches), so this port carries ten local repairs, each a one-line change of
elaboration details; no statement, no definition and no proof idea is altered:
* `include ht in` for `core_domain` (a section variable only used in the proof body);
* `change _ = interior (⋃ i, A i)` before `rw [hinner]`, `simp only [image_image]` plus `exact`
  instead of `simpa only [coreMap, ...]`, and `simp only [coreUnion, ← Set.range_comp']; rfl`
  (partial applications of the private `coreMap` are not unfolded by `simp`);
* `(image_subset_range _ _).trans` (two sites; the Mathlib lemma has explicit arguments);
* explicit `(q := (z, h))` and `(a := (s, h))` for two anonymous-constructor membership proofs;
* `dite_eq_left` / `dite_eq_right` for the deprecated `dif_pos` / `dif_neg`;
* a local `RegularSpace (C.model i).Carrier` instance from
  `DifferentialGeometry.Topology.Manifold.regularSpace_of_chartedSpace`.
The module `CuspExteriorCollars` (the IMS03 path) is a shim re-exporting this file.
-/

set_option autoImplicit false
noncomputable section

open Set Manifold Filter Topology DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.Endpoint GC.GraphManifold GC.LongTime
open scoped Manifold ContDiff Topology

namespace GC.LongTime

universe u v
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

/- The closed carrier model has no smooth-boundary instance. Handle it by
its genuine open embedding, and use the boundary theorem only for the
half-space carrier model. -/
private theorem compact_fullRank_image_geometry
    (kind : CarrierModel) {S : Type u} [TopologicalSpace S]
    [ChartedSpace kind.Space S] [IsManifold kind.model ∞ S] [CompactSpace S]
    {M : Type v} [TopologicalSpace M] [ChartedSpace E3 M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M]
    (f : S → M) (hf : ContMDiff kind.model (𝓡 3) ∞ f)
    (hemb : _root_.Topology.IsEmbedding f)
    (hinj : ∀ x, Function.Injective (mfderiv kind.model (𝓡 3) f x)) :
    IsCompact (range f) ∧ _root_.Topology.IsClosedEmbedding f ∧
      f '' kind.model.interior S = interior (range f) ∧
      f '' kind.model.boundary S = frontier (range f) ∧
      closure (interior (range f)) = range f := by
  have hcompact : IsCompact (range f) := isCompact_range hf.continuous
  have hclosed : _root_.Topology.IsClosedEmbedding f :=
    hf.continuous.isClosedEmbedding hemb.injective
  cases kind with
  | closed =>
    have hopen := DifferentialGeometry.Topology.Manifold.isOpenEmbedding_of_injective_immersion
      f hf hemb.injective hinj rfl
    have hclopen : IsClopen (range f) := ⟨hclosed.isClosed_range, hopen.isOpen_range⟩
    refine ⟨hcompact, hclosed, ?_, ?_, ?_⟩
    · rw [ModelWithCorners.interior_eq_univ, image_univ, hopen.isOpen_range.interior_eq]
    · rw [ModelWithCorners.Boundaryless.boundary_eq_empty, image_empty]
      exact hclopen.frontier_eq.symm
    · rw [hopen.isOpen_range.interior_eq, hclosed.isClosed_range.closure_eq]
  | withBoundary =>
    exact ⟨hcompact, hclosed,
      DifferentialGeometry.Geometry.Boundary.image_interior_eq_of_fullRank_embedding f hf hemb hinj rfl,
      DifferentialGeometry.Geometry.Boundary.image_boundary_eq_frontier_of_fullRank_closedEmbedding f hf hclosed hinj rfl,
      DifferentialGeometry.Geometry.Boundary.closure_interior_range_of_fullRank_closedEmbedding f hf hclosed hinj rfl⟩

private theorem truncation_core_image_geometry
    (H : FiniteVolumeHyperbolicModel.{u}) (D : HyperbolicTruncation H)
    {M : Type v} [TopologicalSpace M] [ChartedSpace E3 M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M]
    (κ : H.Carrier → M)
    (hs : ContMDiff D.core.model (𝓡 3) ∞ (fun x => κ (D.inclusion x)))
    (he : _root_.Topology.IsEmbedding (fun x => κ (D.inclusion x)))
    (hi : ∀ x, Function.Injective
      (mfderiv D.core.model (𝓡 3) (fun y => κ (D.inclusion y)) x)) :
    let j : D.core.Carrier → M := fun x => κ (D.inclusion x)
    IsCompact (range j) ∧ _root_.Topology.IsClosedEmbedding j ∧
      j '' (D.core.interior : Set D.core.Carrier) = interior (range j) ∧
      frontier (range j) = ⋃ p : Fin D.count,
        range (fun s : Torus => κ (D.cuspMap p (s, halfZero))) ∧
      closure (interior (range j)) = range j := by
  obtain ⟨hc, hemb, hint, hboundary, hregular⟩ :=
    compact_fullRank_image_geometry D.core.kind (fun x => κ (D.inclusion x)) hs he hi
  refine ⟨hc, hemb, hint, ?_, hregular⟩
  rw [← hboundary, D.boundary_exhausted]
  change (fun x => κ (D.inclusion x)) '' (⋃ p, range (D.boundary.torusMap p)) = _
  simp only [image_iUnion, ← Set.range_comp', D.cusp_zero]

/-- The original compact truncation has the actual cusp zero slices as its
frontier, with its literal intrinsic interior and regular-closed image. -/
private theorem actual_truncation_core_frontier
    (H : FiniteVolumeHyperbolicModel.{u}) (D : HyperbolicTruncation H) :
    IsCompact (range D.inclusion) ∧ _root_.Topology.IsClosedEmbedding D.inclusion ∧
      D.inclusion '' (D.core.interior : Set D.core.Carrier) = interior (range D.inclusion) ∧
      frontier (range D.inclusion) = ⋃ p : Fin D.count,
        range (fun s : Torus => D.cuspMap p (s, halfZero)) ∧
      closure (interior (range D.inclusion)) = range D.inclusion := by
  exact truncation_core_image_geometry H D id D.embedding.contMDiff D.embedding.isEmbedding
    (fun x => D.embedding.isImmersion.mfderiv_injective (by simp) x)

/- Only the restriction to the actual open domain is used. The total map κ
outside that domain is not assumed continuous, injective, or immersive. -/
private theorem transported_core_image_geometry
    (H : FiniteVolumeHyperbolicModel.{u}) (D : HyperbolicTruncation H)
    {M : Type v} [TopologicalSpace M] [ChartedSpace E3 M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M]
    (U : TopologicalSpace.Opens H.Carrier) (κ : H.Carrier → M)
    (hκ : IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => κ x))
    (hU : range D.inclusion ⊆ U) :
    let j : D.core.Carrier → M := fun x => κ (D.inclusion x)
    IsCompact (range j) ∧ _root_.Topology.IsClosedEmbedding j ∧
      j '' (D.core.interior : Set D.core.Carrier) = interior (range j) ∧
      frontier (range j) = ⋃ p : Fin D.count,
        range (fun s : Torus => κ (D.cuspMap p (s, halfZero))) ∧
      closure (interior (range j)) = range j := by
  let e : D.core.Carrier → U := fun x => ⟨D.inclusion x, hU (mem_range_self x)⟩
  let f : U → M := fun x => κ x
  have he : ContMDiff D.core.model (𝓡 3) ∞ e :=
    (ContMDiff.subtypeVal_comp_iff U e).mp D.embedding.contMDiff
  have hemb : _root_.Topology.IsEmbedding e :=
    _root_.Topology.IsEmbedding.subtypeVal.of_comp_iff.mp D.embedding.isEmbedding
  have hde (x : D.core.Carrier) :
      (mfderiv D.core.model (𝓡 3) e x : E3 →L[ℝ] E3) =
        (mfderiv D.core.model (𝓡 3) D.inclusion x : E3 →L[ℝ] E3) :=
    (DifferentialGeometry.mfderiv_subtypeVal_comp (U := U) e x).symm
  have hein (x : D.core.Carrier) : Function.Injective
      (mfderiv D.core.model (𝓡 3) e x : E3 →L[ℝ] E3) := by
    rw [hde]
    exact D.embedding.isImmersion.mfderiv_injective (by simp) x
  have hjs : ContMDiff D.core.model (𝓡 3) ∞ (fun x => κ (D.inclusion x)) :=
    hκ.contMDiff.comp he
  have hje : _root_.Topology.IsEmbedding (fun x => κ (D.inclusion x)) :=
    hκ.isEmbedding.comp hemb
  apply truncation_core_image_geometry H D κ hjs hje
  intro x
  have hc : (mfderiv D.core.model (𝓡 3) (fun y => κ (D.inclusion y)) x : E3 →L[ℝ] E3) =
      (mfderiv (𝓡 3) (𝓡 3) f (e x) : E3 →L[ℝ] E3).comp
        (mfderiv D.core.model (𝓡 3) e x : E3 →L[ℝ] E3) :=
    mfderiv_comp x (hκ.contMDiff.mdifferentiableAt (by simp))
      (he.mdifferentiableAt (by simp))
  have hfi : Function.Injective (mfderiv (𝓡 3) (𝓡 3) f (e x) : E3 →L[ℝ] E3) :=
    hκ.isImmersion.mfderiv_injective (by simp) (e x)
  rw [hc]
  exact hfi.comp (hein x)

end GC.LongTime

namespace GC.LongTime.PersistentCuspExterior

universe u
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev CI := torusModel.prod 𝓘(ℝ, ℝ)

private abbrev TorusE := EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)

private theorem halfSpaceOneLift_eq_halfPoint {r : ℝ} (hr : 0 ≤ r) :
    halfSpaceOneLift r = halfPoint r hr := by
  apply Subtype.ext
  apply (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)).injective
  change max r 0 = r
  exact max_eq_left hr

private theorem exists_model_signed_collar
    (H : FiniteVolumeHyperbolicModel) (T : HyperbolicTruncation H) (i : Fin T.count)
    (w : ℝ) (hw : 0 < w) :
    ∃ d : SmoothTwoSidedCollar torusModel (𝓡 3) (fun s => T.cuspMap i (s, halfZero)),
      d.radius ≤ w ∧
      ∀ (p : Torus × symmetricOpenInterval d.radius) (hp : 0 ≤ p.2.val),
        d.toFun p = T.cuspMap i (p.1, halfPoint p.2.val hp) := by
  let := halfClosedIntervalChartedSpace hw
  have := halfClosedInterval_isManifold hw
  let e : Ico (0 : ℝ) w → EuclideanHalfSpace 1 := fun r => halfPoint r.val r.property.1
  let j : Torus × Ico (0 : ℝ) w → CuspHalfSpace := Prod.map id e
  let c : Torus × Ico (0 : ℝ) w → H.Carrier := T.cuspMap i ∘ j
  have hval := isSmoothEmbedding_halfClosedInterval_inclusion hw
  have he : ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ e := by
    have heq : e = halfSpaceOneLift ∘ (Subtype.val : Ico (0 : ℝ) w → ℝ) :=
      funext (fun r => (halfSpaceOneLift_eq_halfPoint r.property.1).symm)
    rw [heq]
    exact contMDiffOn_halfSpaceOneLift.comp_contMDiff hval.contMDiff (fun r => r.property.1)
  have hj : ContMDiff halfCollarModel halfCollarModel ∞ j := contMDiff_id.prodMap he
  have hc : ContMDiff halfCollarModel (𝓡 3) ∞ c := (T.cuspEmbedding i).contMDiff.comp hj
  have heinj (r : Ico (0 : ℝ) w) :
      Function.Injective (mfderiv (𝓡∂ 1) (𝓡∂ 1) e r) := by
    let A : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
      mfderiv (𝓡∂ 1) (𝓡∂ 1) e r
    let B : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ :=
      mfderiv (𝓡∂ 1) 𝓘(ℝ) (fun t : EuclideanHalfSpace 1 => t.val 0) (e r)
    let C : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ :=
      mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : Ico (0 : ℝ) w → ℝ) r
    have hC : Function.Injective C :=
      (hval.isImmersion.isImmersionAt r).mfderiv_injective (by simp)
    have hcomp : C = B.comp A :=
      mfderiv_comp r (contMDiff_halfSpaceOneCoordinate.mdifferentiableAt (by simp))
        (he.mdifferentiableAt (by simp))
    change Function.Injective A
    intro a b hab
    apply hC
    rw [hcomp]
    exact congrArg B hab
  have hcinj : Function.Injective (fun s => c (s, ⟨0, le_rfl, hw⟩)) := by
    intro s t hst
    have hpair := (T.cuspEmbedding i).isEmbedding.injective hst
    exact congrArg Prod.fst hpair
  have hcderiv (s : Torus) : Function.Bijective
      (mfderiv halfCollarModel (𝓡 3) c (s, ⟨0, le_rfl, hw⟩)) := by
    let p : Torus × Ico (0 : ℝ) w := (s, ⟨0, le_rfl, hw⟩)
    let A : TorusE × EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
      mfderiv halfCollarModel (𝓡 3) c p
    have hA : Function.Injective A := by
      have hDj : Function.Injective (mfderiv halfCollarModel halfCollarModel j p) := by
        rw [mfderiv_prodMap mdifferentiableAt_id (he.mdifferentiableAt (by simp)), mfderiv_id]
        exact Function.injective_id.prodMap (heinj p.2)
      have hDc := (T.cuspEmbedding i).isImmersion.isImmersionAt (j p)
      have hcomp := mfderiv_comp p
        ((T.cuspEmbedding i).contMDiff.mdifferentiableAt (by simp))
        (hj.mdifferentiableAt (by simp))
      change A = _ at hcomp
      rw [hcomp]
      exact (hDc.mfderiv_injective (by simp)).comp hDj
    exact A.toLinearMap.linearEquivOfInjective hA (by simp [TorusE, Module.finrank_prod]) |>.bijective
  obtain ⟨d, hdwidth, hd⟩ := exists_smoothTwoSidedCollar_of_halfClosedInterval hw c hc hcinj hcderiv
  exact ⟨d, hdwidth, hd⟩


private theorem common_positive_radius {ι : Type*} [Finite ι]
    {R : ℝ} (hR : 0 < R) (f : ι → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧ ∀ i, r < f i := by
  have hnear : ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ i, r < f i := by
    apply Filter.eventually_all.mpr
    intro i
    exact (eventually_lt_nhds (hf i)).filter_mono nhdsWithin_le_nhds
  have hnearR : ∀ᶠ r : ℝ in 𝓝[>] 0, r < R :=
    (eventually_lt_nhds hR).filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r := eventually_mem_nhdsWithin
  exact (hpos.and (hnearR.and hnear)).exists

section FiniteCollars
variable {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M]
  {ι : Type*} [Finite ι]

omit [IsManifold (𝓡 3) ∞ M] in
private theorem finite_outward_band
    (e : ι → PartialDiffeomorph CI (𝓡 3) (Torus × ℝ) M ∞)
    {L : Set M} (hregular : closure (interior L) = L)
    (hfront : frontier L = ⋃ i, range (fun s : Torus => e i (s, 0)))
    (hdisjoint : Pairwise (fun i j => Disjoint
      (range (fun s : Torus => e i (s, 0))) (range (fun s : Torus => e j (s, 0)))))
    {R : ℝ} (hR : 0 < R)
    (hsource : ∀ i, univ ×ˢ Icc (-R) R ⊆ (e i).source)
    (hpositive : ∀ i s r, r ∈ Ioc (0 : ℝ) R → e i (s, r) ∉ L) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧
      (∀ i, univ ×ˢ Icc (-r) r ⊆ (e i).source) ∧
      Pairwise (fun i j => Disjoint
        (e i '' (univ ×ˢ Ioo (-r) r)) (e j '' (univ ×ˢ Ioo (-r) r))) ∧
      ∀ i s h, h ∈ Ioo (-r) r →
        (e i (s, h) ∈ L ↔ h ≤ 0) ∧
        (e i (s, h) ∈ interior L ↔ h < 0) := by
  classical
  let f i := (e i).toOpenPartialHomeomorph
  have hz (i : ι) (s : Torus) : (s, (0 : ℝ)) ∈ (f i).source :=
    hsource i ⟨mem_univ _, neg_nonpos.mpr hR.le, hR.le⟩
  have hm (i : ι) : (range (fun s : Torus => f i (s, 0)) ∩ frontier L).Nonempty := by
    refine ⟨f i (1, 0), mem_range_self 1, ?_⟩
    rw [hfront]
    exact mem_iUnion.mpr ⟨i, mem_range_self 1⟩
  obtain ⟨_, hsides⟩ := frontier_eq_iUnion_of_finite_disjoint_collars
    f hz hdisjoint hregular hfront.subset
  choose w σ hw hσ hws hside hinterior using fun i => hsides i (hm i)
  have hσone (i : ι) : σ i = 1 := by
    rcases hσ i with h | h
    · exact h
    · let z := min (w i) R / 2
      have hzpos : 0 < z := half_pos (lt_min (hw i) hR)
      have hzw : z < w i := (half_lt_self (lt_min (hw i) hR)).trans_le (min_le_left _ _)
      have hzR : z ≤ R := ((half_lt_self (lt_min (hw i) hR)).trans_le (min_le_right _ _)).le
      have hzmem : z ∈ Ioo (-w i) (w i) := ⟨(neg_lt_zero.mpr (hw i)).trans hzpos, hzw⟩
      have hin := (hside i (1 : Torus) z hzmem).mpr (by rw [h]; linarith)
      exact False.elim (hpositive i 1 z ⟨hzpos, hzR⟩ hin)
  have hzeroBand (i : ι) :
      f i '' (univ ×ˢ Icc (0 : ℝ) 0) = range (fun s : Torus => f i (s, 0)) := by
    ext x
    constructor
    · rintro ⟨⟨s, h⟩, hh, rfl⟩
      have hh0 : h = 0 := le_antisymm hh.2.2 hh.2.1
      subst h
      exact mem_range_self s
    · rintro ⟨s, rfl⟩
      exact ⟨(s, 0), ⟨mem_univ _, le_rfl, le_rfl⟩, rfl⟩
  obtain ⟨a, b, hab, hsrc, hsep⟩ :=
    Compactness.exists_larger_product_chart_bands_preserving_disjointness f
      (fun _ => 0) (fun _ => 0) (fun _ => le_rfl)
      (fun i p hp => by
        rcases p with ⟨s, h⟩
        have hh0 : h = 0 := le_antisymm hp.2.2 hp.2.1
        subst h
        exact hz i s)
      (fun i j => i ≠ j) (fun i j hij => by
        rw [hzeroBand, hzeroBand]
        simpa only [f, PartialDiffeomorph.toFun'_toOpenPartialHomeomorph] using hdisjoint hij)
  obtain ⟨r, hr, hrR, hrall⟩ := common_positive_radius hR
    (fun i => min (w i) (min (-a i) (b i)))
    (fun i => lt_min (hw i) (lt_min (neg_pos.mpr (hab i).1) (hab i).2))
  have hrw (i : ι) : r < w i := (hrall i).trans_le (min_le_left _ _)
  have hrsmall (i : ι) : (univ : Set Torus) ×ˢ Ioo (-r) r ⊆ univ ×ˢ Ioo (a i) (b i) := by
    intro p hp
    have hleft := (hrall i).trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hright := (hrall i).trans_le ((min_le_right _ _).trans (min_le_right _ _))
    exact ⟨hp.1, by linarith [hp.2.1], hp.2.2.trans hright⟩
  refine ⟨r, hr, hrR, ?_, ?_, ?_⟩
  · intro i p hp
    exact hsource i ⟨hp.1, by linarith [hp.2.1], hp.2.2.trans hrR.le⟩
  · intro i j hij
    exact (hsep i j hij).mono (image_mono (hrsmall i)) (image_mono (hrsmall j))
  · intro i s h hh
    have hhw : h ∈ Ioo (-w i) (w i) := ⟨by linarith [hh.1, hrw i], hh.2.trans (hrw i)⟩
    have hs := hside i s h hhw
    have hi := hinterior i s h hhw
    simp only [f, PartialDiffeomorph.toFun'_toOpenPartialHomeomorph,
      hσone i, one_mul] at hs hi
    exact ⟨hs, hi⟩

end FiniteCollars

/- Each compact cover is made from the OLD closed half-radius band. The
new open collar is therefore entirely covered, including its negative side. -/
private theorem exists_precompact_model_collar
    (H : FiniteVolumeHyperbolicModel.{u}) (D : HyperbolicTruncation H) (j : Fin D.count) :
    ∃ d : SmoothTwoSidedCollar torusModel (𝓡 3) (fun s => D.cuspMap j (s, halfZero)),
      ∃ B : Set H.Carrier,
        (∀ (p : Torus × symmetricOpenInterval d.radius) (hp : 0 ≤ p.2.val),
          d.toFun p = D.cuspMap j (p.1, halfPoint p.2.val hp)) ∧
        IsCompact B ∧ (d.neighborhood : Set H.Carrier) ⊆ B := by
  obtain ⟨c, _, hc⟩ := exists_model_signed_collar H D j 1 zero_lt_one
  let q := c.radius / 2
  have hq : 0 < q := half_pos c.radius_pos
  have hqc : q < c.radius := half_lt_self c.radius_pos
  let d := c.restrictRadius q hq hqc.le
  let B := c.toPartialDiffeomorph '' (univ ×ˢ Icc (-q) q)
  have hsource : univ ×ˢ Icc (-q) q ⊆ c.toPartialDiffeomorph.source := by
    rw [c.toPartialDiffeomorph_source]
    intro p hp
    exact ⟨hp.1, by linarith [hp.2.1], hp.2.2.trans_lt hqc⟩
  have hB : IsCompact B := (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
    (c.toPartialDiffeomorph.contMDiffOn_toFun.continuousOn.mono hsource)
  refine ⟨d, B, ?_, hB, ?_⟩
  · intro p hp
    change c.toFun (p.1, ⟨p.2.val, _⟩) = _
    exact hc _ hp
  · intro y hy
    change y ∈ ((c.restrictRadius q hq hqc.le).neighborhood : Set H.Carrier) at hy
    rw [c.restrictRadius_neighborhood] at hy
    obtain ⟨p, rfl⟩ := hy
    refine ⟨(p.1, p.2.val), ⟨mem_univ _, p.2.property.1.le, p.2.property.2.le⟩, ?_⟩
    exact c.toPartialDiffeomorph_apply (p.1, ⟨p.2.val, _⟩)

private theorem model_collar_zero
    (H : FiniteVolumeHyperbolicModel.{u}) (D : HyperbolicTruncation H) (j : Fin D.count)
    (d : SmoothTwoSidedCollar torusModel (𝓡 3) (fun s => D.cuspMap j (s, halfZero)))
    (s : Torus) : d.toPartialDiffeomorph (s, 0) = D.cuspMap j (s, halfZero) :=
  (d.toPartialDiffeomorph_apply (s, ⟨0, neg_lt_zero.mpr d.radius_pos, d.radius_pos⟩)).trans
    (d.toFun_zero s)

private theorem model_collar_mem_neighborhood
    (H : FiniteVolumeHyperbolicModel.{u}) (D : HyperbolicTruncation H) (j : Fin D.count)
    (d : SmoothTwoSidedCollar torusModel (𝓡 3) (fun s => D.cuspMap j (s, halfZero)))
    {p : Torus × ℝ} (hp : p ∈ d.toPartialDiffeomorph.source) :
    d.toPartialDiffeomorph p ∈ d.neighborhood := by
  have h := d.toPartialDiffeomorph.map_source hp
  rwa [d.toPartialDiffeomorph_target] at h

private theorem positive_model_cusp_not_in_core
    (H : FiniteVolumeHyperbolicModel.{u}) (D : HyperbolicTruncation H)
    (j : Fin D.count) (s : Torus) {r : ℝ} (hr : 0 < r) :
    D.cuspMap j (s, halfPoint r hr.le) ∉ range D.inclusion := by
  intro hx
  have hm : D.cuspMap j (s, halfPoint r hr.le) ∈
      range (fun v : Torus => D.cuspMap j (v, halfZero)) := by
    rw [← D.intersection]
    exact ⟨hx, mem_range_self _⟩
  obtain ⟨v, hv⟩ := hm
  have hi := (D.cuspEmbedding j).isEmbedding.injective hv
  have hz := congrArg (fun z : CuspHalfSpace => z.2.val 0) hi
  change (0 : ℝ) = r at hz
  exact hr.ne' hz.symm

private theorem prepare_model_collars
    (H : FiniteVolumeHyperbolicModel.{u}) (D : HyperbolicTruncation H) :
    ∃ d : (j : Fin D.count) → SmoothTwoSidedCollar torusModel (𝓡 3)
        (fun s => D.cuspMap j (s, halfZero)),
      ∃ B : Set H.Carrier, ∃ s : ℝ, 0 < s ∧
        (∀ j, s < (d j).radius) ∧
        (∀ j (p : Torus × symmetricOpenInterval (d j).radius) (hp : 0 ≤ p.2.val),
          (d j).toFun p = D.cuspMap j (p.1, halfPoint p.2.val hp)) ∧
        IsCompact B ∧ range D.inclusion ⊆ B ∧
        (∀ j, ((d j).neighborhood : Set H.Carrier) ⊆ B) ∧
        Pairwise (fun j k => Disjoint
          ((d j).toPartialDiffeomorph '' (univ ×ˢ Ioo (-s) s))
          ((d k).toPartialDiffeomorph '' (univ ×ˢ Ioo (-s) s))) ∧
        ∀ j z h, h ∈ Ioo (-s) s →
          ((d j).toPartialDiffeomorph (z, h) ∈ range D.inclusion ↔ h ≤ 0) ∧
          ((d j).toPartialDiffeomorph (z, h) ∈ interior (range D.inclusion) ↔ h < 0) := by
  classical
  choose d A hd hA hn using fun j => exists_precompact_model_collar H D j
  let B : Set H.Carrier := range D.inclusion ∪ ⋃ j, A j
  have hcore := GC.LongTime.actual_truncation_core_frontier H D
  have hB : IsCompact B := hcore.1.union (isCompact_iUnion hA)
  obtain ⟨R, hR, _, hRall⟩ := common_positive_radius zero_lt_one
    (fun j => (d j).radius) (fun j => (d j).radius_pos)
  have hsource (j : Fin D.count) : univ ×ˢ Icc (-R) R ⊆ (d j).toPartialDiffeomorph.source := by
    rw [(d j).toPartialDiffeomorph_source]
    intro p hp
    exact ⟨hp.1, by linarith [hp.2.1, hRall j], hp.2.2.trans_lt (hRall j)⟩
  have hzero (j : Fin D.count) :
      (fun z : Torus => (d j).toPartialDiffeomorph (z, 0)) =
        fun z => D.cuspMap j (z, halfZero) := funext (model_collar_zero H D j (d j))
  have hfront : frontier (range D.inclusion) =
      ⋃ j, range (fun z : Torus => (d j).toPartialDiffeomorph (z, 0)) := by
    simp_rw [hzero]
    exact hcore.2.2.2.1
  have hdisj : Pairwise (fun j k => Disjoint
      (range (fun z : Torus => (d j).toPartialDiffeomorph (z, 0)))
      (range (fun z : Torus => (d k).toPartialDiffeomorph (z, 0)))) := by
    intro j k hjk
    rw [hzero j, hzero k]
    exact (D.cusp_disjoint hjk).mono
      (by rintro _ ⟨z, rfl⟩; exact mem_range_self _)
      (by rintro _ ⟨z, rfl⟩; exact mem_range_self _)
  have hpositive (j : Fin D.count) (z : Torus) (h : ℝ) (hh : h ∈ Ioc (0 : ℝ) R) :
      (d j).toPartialDiffeomorph (z, h) ∉ range D.inclusion := by
    have hh' : h ∈ Ioo (-(d j).radius) (d j).radius :=
      ⟨(neg_lt_zero.mpr (d j).radius_pos).trans hh.1, hh.2.trans_lt (hRall j)⟩
    have heq := ((d j).toPartialDiffeomorph_apply (z, ⟨h, hh'⟩)).trans (hd j _ hh.1.le)
    rw [heq]
    exact positive_model_cusp_not_in_core H D j z hh.1
  obtain ⟨s, hs, hsR, _, hsep, hside⟩ := finite_outward_band
    (fun j => (d j).toPartialDiffeomorph) hcore.2.2.2.2 hfront hdisj hR hsource hpositive
  refine ⟨d, B, s, hs, fun j => hsR.trans (hRall j), hd, hB, subset_union_left, ?_, hsep, hside⟩
  intro j x hx
  exact Or.inr (mem_iUnion.mpr ⟨j, hn j hx⟩)

/- The derivative is inverted only on the genuine open persistent domain. -/
private theorem partialDiffeomorph_of_open_embedding
    {M N : Type*} [TopologicalSpace M] [ChartedSpace E3 M]
    [IsManifold (𝓡 3) ∞ M] [TopologicalSpace N] [ChartedSpace E3 N]
    [IsManifold (𝓡 3) ∞ N]
    (U : TopologicalSpace.Opens M) (f : M → N)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hemb : IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x))
    (hne : (U : Set M).Nonempty) :
    ∃ Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) M N ∞,
      Φ.source = U ∧ Φ.target = f '' U ∧ Φ.toFun = f := by
  have hlocal : IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ f U := by
    apply hf.isLocalDiffeomorphOn_of_isInvertible_mfderiv U.isOpen (by simp)
    intro x hx
    let A : E3 →L[ℝ] E3 := mfderiv (𝓡 3) (𝓡 3) f x
    have hA : Function.Injective A := by
      have hi : Function.Injective
          (mfderiv (𝓡 3) (𝓡 3) (fun y : U => f y) (⟨x, hx⟩ : U) : E3 →L[ℝ] E3) :=
        hemb.isImmersion.mfderiv_injective (by simp) (⟨x, hx⟩ : U)
      have heq : (mfderiv (𝓡 3) (𝓡 3) (fun y : U => f y) (⟨x, hx⟩ : U) : E3 →L[ℝ] E3) = A :=
        DifferentialGeometry.mfderiv_restrict_open f U ⟨x, hx⟩
      rw [heq] at hi
      exact hi
    let L : E3 ≃L[ℝ] E3 := (A.toLinearMap.linearEquivOfInjective hA rfl).toContinuousLinearEquiv
    refine ⟨L, ?_⟩
    ext v
    rfl
  apply hlocal.exists_partialDiffeomorph_of_injOn U.isOpen hne
  intro x hx y hy hxy
  exact congrArg Subtype.val
    (hemb.isEmbedding.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)

section ActualCores
variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {K : ℕ} (C : PersistentHyperbolicCores F K) (ext : PersistentCuspExterior C)
  (t : ℝ) (ht : ext.start ≤ t)

private abbrev Port := (i : Fin C.count) × Fin (ext.truncation i).count
private def coreMap (i : Fin C.count) (x : (ext.truncation i).core.Carrier) :=
  C.map i t (ext.after_cores.trans ht) ((ext.truncation i).inclusion x)
private def coreUnion : Set (postStage F.observation t).Carrier :=
  ⋃ i, range (coreMap C ext t ht i)
private def zeroMap (p : Port C ext) (s : Torus) :=
  C.map p.1 t (ext.after_cores.trans ht)
    ((ext.truncation p.1).cuspMap p.2 (s, halfZero))

include ht in
private theorem core_domain (i : Fin C.count) :
    range (ext.truncation i).inclusion ⊆ C.domain i t :=
  (ext.in_ball i t ht).trans (C.advertised_ball i t (ext.after_cores.trans ht))

private theorem actual_finite_core_geometry :
    IsCompact (coreUnion C ext t ht) ∧
      closure (interior (coreUnion C ext t ht)) = coreUnion C ext t ht ∧
      frontier (coreUnion C ext t ht) = ⋃ p : Port C ext, range (zeroMap C ext t ht p) ∧
      ext.region t = (interior (coreUnion C ext t ht))ᶜ := by
  classical
  let A (i : Fin C.count) := range (coreMap C ext t ht i)
  have hA (i : Fin C.count) :=
    GC.LongTime.transported_core_image_geometry
      (C.model i) (ext.truncation i) (C.domain i t)
      (C.map i t (ext.after_cores.trans ht))
      (C.embedding i t (ext.after_cores.trans ht)) (core_domain C ext t ht i)
  have hc (i : Fin C.count) : IsCompact (A i) := (hA i).1
  have hd : Pairwise (fun i j => Disjoint (A i) (A j)) := by
    intro i j hij
    apply (C.disjoint t (ext.after_cores.trans ht) hij).mono
    · rintro x ⟨y, rfl⟩
      exact ⟨(ext.truncation i).inclusion y, core_domain C ext t ht i (mem_range_self y), rfl⟩
    · rintro x ⟨y, rfl⟩
      exact ⟨(ext.truncation j).inclusion y, core_domain C ext t ht j (mem_range_self y), rfl⟩
  have hlocal : LocallyFinite A := locallyFinite_of_finite _
  have hfront : frontier (⋃ i, A i) = ⋃ i, frontier (A i) := by
    apply hlocal.frontier_iUnion_of_disjoint_closure
    intro i j hij
    simpa only [(hc i).isClosed.closure_eq, (hc j).isClosed.closure_eq] using hd hij
  have hregular : closure (interior (⋃ i, A i)) = ⋃ i, A i :=
    hlocal.closure_interior_iUnion (fun i => (hA i).2.2.2.2)
  have hinner : interior (⋃ i, A i) = ⋃ i, interior (A i) := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp (interior_subset hx)
      apply mem_iUnion.mpr
      refine ⟨i, ?_⟩
      by_contra hn
      have hf : x ∈ frontier (A i) := ⟨subset_closure hi, hn⟩
      have hf' : x ∈ frontier (⋃ i, A i) := hfront.symm ▸ mem_iUnion.mpr ⟨i, hf⟩
      exact hf'.2 hx
    · exact iUnion_subset (fun i => interior_mono (subset_iUnion A i))
  refine ⟨isCompact_iUnion hc, hregular, ?_, ?_⟩
  · change frontier (⋃ i, A i) = _
    rw [hfront]
    have hFi (i : Fin C.count) : frontier (A i) =
        ⋃ p : Fin (ext.truncation i).count, range (fun s : Torus =>
          C.map i t (ext.after_cores.trans ht) ((ext.truncation i).cuspMap p (s, halfZero))) :=
      (hA i).2.2.2.1
    simp_rw [hFi]
    ext x
    simp only [mem_iUnion, mem_range, zeroMap, Port, Sigma.exists]
  · rw [PersistentCuspExterior.region, dite_eq_left ht]
    congr 1
    change _ = interior (⋃ i, A i)
    rw [hinner]
    apply iUnion_congr
    intro i
    simp only [image_image]
    exact (hA i).2.2.1


private theorem stage_core_union_eq :
    coreUnion C ext t ht = ⋃ i, C.map i t (ext.after_cores.trans ht) ''
      range (ext.truncation i).inclusion := by
  simp only [coreUnion, ← Set.range_comp']
  rfl

private theorem stage_interior_eq :
    interior (coreUnion C ext t ht) = ⋃ i, C.map i t (ext.after_cores.trans ht) ''
      ((ext.truncation i).inclusion '' ((ext.truncation i).core.interior : Set _)) := by
  apply compl_injective
  rw [← (actual_finite_core_geometry C ext t ht).2.2.2]
  simp only [PersistentCuspExterior.region, dite_eq_left ht]

private theorem mem_stage_union_images_iff
    (S : (i : Fin C.count) → Set (C.model i).Carrier)
    (hS : ∀ i, S i ⊆ C.domain i t) (i : Fin C.count)
    (x : (C.model i).Carrier) (hx : x ∈ C.domain i t) :
    C.map i t (ext.after_cores.trans ht) x ∈
        ⋃ j, C.map j t (ext.after_cores.trans ht) '' S j ↔ x ∈ S i := by
  constructor
  · intro h
    obtain ⟨j, y, hy, heq⟩ := mem_iUnion.mp h
    by_cases hji : j = i
    · subst j
      have hyx : y = x := congrArg Subtype.val
        ((C.embedding i t (ext.after_cores.trans ht)).isEmbedding.injective
          (a₁ := ⟨y, hS i hy⟩) (a₂ := ⟨x, hx⟩) heq)
      exact hyx ▸ hy
    · exact False.elim (disjoint_left.mp
        (C.disjoint t (ext.after_cores.trans ht) hji)
        ⟨y, hS j hy, heq⟩ ⟨x, hx, rfl⟩)
  · intro h
    exact mem_iUnion.mpr ⟨i, x, h, rfl⟩

end ActualCores

section EventualTransport
variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {K : ℕ} (C : PersistentHyperbolicCores F K) (ext : PersistentCuspExterior C)

/-- Original signed collars, their common radius, and their whole-neighborhood
compact covers are chosen before one exhaustion threshold. Every later
transport is the literal persistent map on the whole signed collar. This
statement makes no joint time regularity or metric estimate claim. -/
theorem exists_eventual_signed_collar_transport (tmin : ℝ) :
    ∃ d : (p : (i : Fin C.count) × Fin (ext.truncation i).count) → SmoothTwoSidedCollar torusModel (𝓡 3)
        (fun s => (ext.truncation p.1).cuspMap p.2 (s, halfZero)),
      (∀ p (q : Torus × symmetricOpenInterval (d p).radius) (hq : 0 ≤ q.2.val),
        (d p).toFun q = (ext.truncation p.1).cuspMap p.2 (q.1, halfPoint q.2.val hq)) ∧
      ∃ r : ℝ, 0 < r ∧ (∀ p, 2 * r < (d p).radius) ∧
      ∃ B : (i : Fin C.count) → Set (C.model i).Carrier,
        (∀ i, IsCompact (B i)) ∧
        (∀ i, range (ext.truncation i).inclusion ⊆ B i) ∧
        (∀ p, ((d p).neighborhood : Set (C.model p.1).Carrier) ⊆ B p.1) ∧
        ∃ T₀ : ℝ, ∃ hstart : ext.start ≤ T₀, tmin ≤ T₀ ∧
        ∀ t : ℝ, ∀ ht : T₀ ≤ t,
          (∀ i, B i ⊆ C.domain i t) ∧
          ∃ Φ : (p : (i : Fin C.count) × Fin (ext.truncation i).count) → PartialDiffeomorph (𝓡 3) (𝓡 3)
              (C.model p.1).Carrier (postStage F.observation t).Carrier ∞,
            (∀ p, (Φ p).source = C.domain p.1 t ∧
              (Φ p).target = C.map p.1 t (ext.after_cores.trans (hstart.trans ht)) '' C.domain p.1 t ∧
              (Φ p).toFun = C.map p.1 t (ext.after_cores.trans (hstart.trans ht))) ∧
            let e := fun p => (d p).toPartialDiffeomorph.trans (Φ p)
            let L := ⋃ i, C.map i t (ext.after_cores.trans (hstart.trans ht)) ''
              range (ext.truncation i).inclusion
            IsCompact L ∧ closure (interior L) = L ∧
            (∀ p, (e p).source = (d p).toPartialDiffeomorph.source) ∧
            (∀ p, univ ×ˢ Icc (-(2 * r)) (2 * r) ⊆ (e p).source) ∧
            (∀ p q, e p q = C.map p.1 t (ext.after_cores.trans (hstart.trans ht))
              ((d p).toPartialDiffeomorph q)) ∧
            Pairwise (fun p q => Disjoint
              (e p '' (univ ×ˢ Ioo (-r) r)) (e q '' (univ ×ˢ Ioo (-r) r))) ∧
            (∀ p s h, h ∈ Ioo (-r) r →
              (e p (s, h) ∈ L ↔ h ≤ 0) ∧ (e p (s, h) ∈ interior L ↔ h < 0)) ∧
            frontier L = ⋃ p, range (fun s : Torus => e p (s, 0)) ∧
            ext.region t = (interior L)ᶜ := by
  classical
  choose d₀ B s hs hsr hzero hB hcore hneigh hsep hside using
    fun i : Fin C.count => prepare_model_collars (C.model i) (ext.truncation i)
  let d (p : Port C ext) := d₀ p.1 p.2
  obtain ⟨r, hr, _, hrs⟩ := common_positive_radius zero_lt_one
    (fun i => s i / 2) (fun i => half_pos (hs i))
  have h2rs (i : Fin C.count) : 2 * r < s i := by linarith [hrs i]
  have hrd (p : Port C ext) : 2 * r < (d p).radius := (h2rs p.1).trans (hsr p.1 p.2)
  have hdn (p : Port C ext) : ((d p).neighborhood : Set (C.model p.1).Carrier) ⊆ B p.1 :=
    hneigh p.1 p.2
  choose S hS using fun i => C.exhausts i (B i) (hB i)
  obtain ⟨T₀, hT₀⟩ := (Set.finite_range S).bddAbove
  let T := max (max ext.start tmin) T₀
  have hstart : ext.start ≤ T := (le_max_left _ _).trans (le_max_left _ _)
  have htmin : tmin ≤ T := (le_max_right _ _).trans (le_max_left _ _)
  refine ⟨d, (fun p => hzero p.1 p.2), r, hr, hrd, B, hB, hcore, hdn,
    T, hstart, htmin, ?_⟩
  intro t ht
  have hEt : ext.start ≤ t := hstart.trans ht
  have hdom (i : Fin C.count) : B i ⊆ C.domain i t :=
    hS i t ((hT₀ (mem_range_self i)).trans ((le_max_right _ _).trans ht))
  have hdDom (p : Port C ext) : ((d p).neighborhood : Set (C.model p.1).Carrier) ⊆
      C.domain p.1 t := (hdn p).trans (hdom p.1)
  have hex (p : Port C ext) :
      ∃ Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) (C.model p.1).Carrier
          (postStage F.observation t).Carrier ∞,
        Φ.source = C.domain p.1 t ∧
        Φ.target = C.map p.1 t (ext.after_cores.trans hEt) '' C.domain p.1 t ∧
        Φ.toFun = C.map p.1 t (ext.after_cores.trans hEt) := by
    have hn : (C.domain p.1 t : Set (C.model p.1).Carrier).Nonempty := by
      refine ⟨(d p).toFun (1, ⟨0, neg_lt_zero.mpr (d p).radius_pos, (d p).radius_pos⟩), ?_⟩
      exact hdDom p ((d p).toDiffeomorph _).property
    exact partialDiffeomorph_of_open_embedding (C.domain p.1 t)
      (C.map p.1 t (ext.after_cores.trans hEt)) (C.smooth p.1 t (ext.after_cores.trans hEt))
      (C.embedding p.1 t (ext.after_cores.trans hEt)) hn
  choose Φ hΦs hΦt hΦf using hex
  let e (p : Port C ext) := (d p).toPartialDiffeomorph.trans (Φ p)
  have heSource (p : Port C ext) : (e p).source = (d p).toPartialDiffeomorph.source := by
    rw [show (e p).source = ((d p).toPartialDiffeomorph.trans (Φ p)).source from rfl,
      PartialDiffeomorph.trans_source, hΦs p]
    apply inter_eq_left.mpr
    intro q hq
    exact hdDom p (model_collar_mem_neighborhood (C.model p.1) (ext.truncation p.1) p.2 (d p) hq)
  have heApply (p : Port C ext) (q : Torus × ℝ) :
      e p q = C.map p.1 t (ext.after_cores.trans hEt) ((d p).toPartialDiffeomorph q) := by
    change Φ p ((d p).toPartialDiffeomorph q) = _
    exact congrFun (hΦf p) _
  have heBand (p : Port C ext) : univ ×ˢ Icc (-(2 * r)) (2 * r) ⊆ (e p).source := by
    rw [heSource p, (d p).toPartialDiffeomorph_source]
    intro q hq
    exact ⟨hq.1, by linarith [hq.2.1, hrd p], hq.2.2.trans_lt (hrd p)⟩
  have hrSmall (p : Port C ext) : univ ×ˢ Ioo (-r) r ⊆ (d p).toPartialDiffeomorph.source := by
    rw [(d p).toPartialDiffeomorph_source]
    intro q hq
    have hrr : r < (d p).radius := by linarith [hrd p]
    exact ⟨hq.1, by linarith [hq.2.1], hq.2.2.trans hrr⟩
  have hpDom (p : Port C ext) {q : Torus × ℝ} (hq : q ∈ univ ×ˢ Ioo (-r) r) :
      (d p).toPartialDiffeomorph q ∈ C.domain p.1 t :=
    hdDom p (model_collar_mem_neighborhood (C.model p.1) (ext.truncation p.1) p.2 (d p)
      (hrSmall p hq))
  refine ⟨hdom, Φ, fun p => ⟨hΦs p, hΦt p, hΦf p⟩,
    ?_, ?_, heSource, heBand, heApply, ?_, ?_, ?_, ?_⟩
  · rw [← stage_core_union_eq C ext t hEt]
    exact (actual_finite_core_geometry C ext t hEt).1
  · rw [← stage_core_union_eq C ext t hEt]
    exact (actual_finite_core_geometry C ext t hEt).2.1
  · intro p q hpq
    apply disjoint_left.mpr
    rintro x ⟨a, ha, hax⟩ ⟨b, hb, hbx⟩
    have hab := hax.trans hbx.symm
    rw [heApply, heApply] at hab
    rcases p with ⟨i, j⟩
    rcases q with ⟨k, l⟩
    by_cases hik : i = k
    · subst k
      have hjl : j ≠ l := by
        intro h
        subst l
        exact hpq rfl
      have hm : (d ⟨i, j⟩).toPartialDiffeomorph a = (d ⟨i, l⟩).toPartialDiffeomorph b :=
        congrArg Subtype.val ((C.embedding i t (ext.after_cores.trans hEt)).isEmbedding.injective
          (a₁ := ⟨_, hpDom ⟨i, j⟩ ha⟩) (a₂ := ⟨_, hpDom ⟨i, l⟩ hb⟩) hab)
      have hra : a ∈ univ ×ˢ Ioo (-(s i)) (s i) :=
        ⟨ha.1, by linarith [ha.2.1, h2rs i], by linarith [ha.2.2, h2rs i]⟩
      have hrb : b ∈ univ ×ˢ Ioo (-(s i)) (s i) :=
        ⟨hb.1, by linarith [hb.2.1, h2rs i], by linarith [hb.2.2, h2rs i]⟩
      exact disjoint_left.mp (hsep i hjl) ⟨a, hra, rfl⟩ ⟨b, hrb, hm.symm⟩
    · exact disjoint_left.mp (C.disjoint t (ext.after_cores.trans hEt) hik)
        ⟨_, hpDom ⟨i, j⟩ ha, (heApply ⟨i, j⟩ a).symm.trans hax⟩
        ⟨_, hpDom ⟨k, l⟩ hb, (heApply ⟨k, l⟩ b).symm.trans hbx⟩
  · intro p z h hh
    have hx := hpDom p (q := (z, h)) ⟨mem_univ _, hh⟩
    have hh' : h ∈ Ioo (-(s p.1)) (s p.1) :=
      ⟨by linarith [hh.1, h2rs p.1], by linarith [hh.2, h2rs p.1]⟩
    have hside' := hside p.1 p.2 z h hh'
    rw [heApply]
    refine ⟨?_, ?_⟩
    · rw [mem_stage_union_images_iff C ext t hEt
        (fun i => range (ext.truncation i).inclusion)
        (fun i => (hcore i).trans (hdom i)) p.1 _ hx]
      exact hside'.1
    · rw [← stage_core_union_eq C ext t hEt, stage_interior_eq C ext t hEt]
      rw [mem_stage_union_images_iff C ext t hEt
        (fun i => (ext.truncation i).inclusion '' ((ext.truncation i).core.interior : Set _))
        (fun i => (image_subset_range _ _).trans ((hcore i).trans (hdom i))) p.1 _ hx]
      rw [(GC.LongTime.actual_truncation_core_frontier
        (C.model p.1) (ext.truncation p.1)).2.2.1]
      exact hside'.2
  · rw [← stage_core_union_eq C ext t hEt,
      (actual_finite_core_geometry C ext t hEt).2.2.1]
    apply iUnion_congr
    intro p
    congr 1
    funext z
    rw [heApply, model_collar_zero]
    rfl
  · rw [← stage_core_union_eq C ext t hEt]
    exact (actual_finite_core_geometry C ext t hEt).2.2.2

end EventualTransport
end GC.LongTime.PersistentCuspExterior

namespace GC.LongTime

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric}
  {F : GC.Interface.RawSurgery P g} {K : ℕ}

/-- The persistent map is an open embedding on its genuine open domain. -/
theorem PersistentHyperbolicCores.isOpenEmbedding_domainMap
    (C : PersistentHyperbolicCores F K) (i : Fin C.count)
    (t : ℝ) (ht : C.start ≤ t) :
    _root_.Topology.IsOpenEmbedding (fun x : C.domain i t => C.map i t ht x) := by
  have he := C.embedding i t ht
  exact DifferentialGeometry.Topology.Manifold.isOpenEmbedding_of_injective_immersion
    (fun x : C.domain i t => C.map i t ht x) he.contMDiff he.isEmbedding.injective
    (fun x => he.isImmersion.mfderiv_injective (by simp) x) rfl

variable {C : PersistentHyperbolicCores F K}

/-- Every original compact core lies in the genuine persistent domain from the
exterior's already fixed start time. -/
theorem PersistentCuspExterior.truncation_range_subset_domain
    (E : PersistentCuspExterior C) (i : Fin C.count) (t : ℝ) (ht : E.start ≤ t) :
    range (E.truncation i).inclusion ⊆ C.domain i t :=
  (E.in_ball i t ht).trans (C.advertised_ball i t (E.after_cores.trans ht))

/-- The original core-interior image remains open in the full post-surgery stage,
including when that stage has several connected components. -/
theorem PersistentCuspExterior.isOpen_coreInteriorImage
    (E : PersistentCuspExterior C) (i : Fin C.count) (t : ℝ) (ht : E.start ≤ t) :
    IsOpen (C.map i t (E.after_cores.trans ht) ''
      ((E.truncation i).inclusion '' ((E.truncation i).core.interior : Set _))) := by
  let S := (E.truncation i).inclusion '' ((E.truncation i).core.interior : Set _)
  have hS : S ⊆ C.domain i t :=
    (image_subset_range _ _).trans (E.truncation_range_subset_domain i t ht)
  have hopen := (C.isOpenEmbedding_domainMap i t (E.after_cores.trans ht)).isOpenMap
    (Subtype.val ⁻¹' S) ((E.truncation i).interior_image.preimage continuous_subtype_val)
  have heq : (fun x : C.domain i t => C.map i t (E.after_cores.trans ht) x) ''
      (Subtype.val ⁻¹' S) = C.map i t (E.after_cores.trans ht) '' S := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.val, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hS hx⟩, hx, rfl⟩
  rw [heq] at hopen
  exact hopen

/-- The literal prescribed exterior is closed at every time. -/
theorem PersistentCuspExterior.isClosed_region (E : PersistentCuspExterior C) (t : ℝ) :
    IsClosed (E.region t) := by
  by_cases ht : E.start ≤ t
  · rw [PersistentCuspExterior.region, dite_eq_left ht]
    exact (isOpen_iUnion (fun i => E.isOpen_coreInteriorImage i t ht)).isClosed_compl
  · rw [PersistentCuspExterior.region, dite_eq_right ht]
    exact isClosed_univ

/-- Compactness of the literal prescribed exterior requires no connectedness
assumption on the post-surgery stage. -/
theorem PersistentCuspExterior.isCompact_region (E : PersistentCuspExterior C) (t : ℝ) :
    IsCompact (E.region t) :=
  (E.isClosed_region t).isCompact

end GC.LongTime

open DifferentialGeometry.Analysis

namespace GC.LongTime

universe u

private theorem compact_subset_model_ball
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RegularSpace M] [PreconnectedSpace M]
    (g : SmoothRiemannianMetric I M) (x : M) {B : Set M} (hB : IsCompact B) :
    ∃ R : ℝ, 0 < R ∧ B ⊆ riemannianBallOf g x R := by
  let : PseudoMetricSpace M := g.toPseudoMetricSpace
  obtain ⟨R, hR, hBR⟩ := hB.isBounded.subset_ball_lt 0 x
  refine ⟨R, hR, ?_⟩
  intro y hy
  change edist x y < ENNReal.ofReal R
  rw [edist_lt_ofReal, dist_comm]
  exact hBR hy

/-- A fixed finite family of compact model buffers eventually lies in the
advertised metric-error balls. The same threshold makes any prescribed finite
number of derivative orders available, regardless of the initial order `K`. -/
theorem PersistentHyperbolicCores.eventually_compact_subset_advertised_ball
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {K : ℕ} (C : PersistentHyperbolicCores F K)
    (B : (i : Fin C.count) → Set (C.model i).Carrier)
    (hB : ∀ i, IsCompact (B i)) (tmin : ℝ) (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, C.start ≤ T ∧ tmin ≤ T ∧
      ∀ t : ℝ, T ≤ t →
        C.accuracy t < ε ∧
        n ≤ max K ⌈(C.accuracy t)⁻¹⌉₊ ∧
        (∀ i, B i ⊆ riemannianBallOf (C.model i).metric
          (C.model i).basepoint (C.accuracy t)⁻¹) ∧
        ∀ i, B i ⊆ C.domain i t := by
  classical
  let _ : ∀ i, RegularSpace (C.model i).Carrier := fun i =>
    DifferentialGeometry.Topology.Manifold.regularSpace_of_chartedSpace (𝓡 3)
  choose R hR hBR using fun i =>
    compact_subset_model_ball (C.model i).metric (C.model i).basepoint (hB i)
  obtain ⟨S, hS⟩ := (finite_range R).bddAbove
  let A : ℝ := max (max S (n + 1)) 1
  have hA : 0 < A := zero_lt_one.trans_le (le_max_right _ _)
  have hRA (i : Fin C.count) : R i ≤ A :=
    (hS (mem_range_self i)).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hnA : (n : ℝ) < A := by
    have h := (le_max_right S (n + 1)).trans (le_max_left (max S (n + 1)) 1)
    dsimp only [A]
    linarith
  obtain ⟨T₀, hT₀⟩ := C.accuracy_decay (min ε A⁻¹) (lt_min hε (inv_pos.mpr hA))
  let T := max (max C.start tmin) T₀
  have hstart : C.start ≤ T := (le_max_left _ _).trans (le_max_left _ _)
  refine ⟨T, hstart, (le_max_right _ _).trans (le_max_left _ _), ?_⟩
  intro t ht
  have hCt : C.start ≤ t := hstart.trans ht
  have hsmall := hT₀ t ((le_max_right _ _).trans ht)
  have hεt : C.accuracy t < ε := hsmall.trans_le (min_le_left _ _)
  have hinv : A < (C.accuracy t)⁻¹ :=
    (lt_inv_comm₀ hA (C.accuracy_pos t hCt)).mpr
      (hsmall.trans_le (min_le_right _ _))
  have hball (i : Fin C.count) : B i ⊆ riemannianBallOf (C.model i).metric
      (C.model i).basepoint (C.accuracy t)⁻¹ :=
    (hBR i).trans (riemannianBallOf_mono _ _ ((hRA i).trans_lt hinv).le)
  refine ⟨hεt, (Nat.lt_ceil.mpr (hnA.trans hinv)).le.trans (le_max_right _ _),
    hball, ?_⟩
  intro i
  exact (hball i).trans (C.advertised_ball i t hCt)

end GC.LongTime

namespace GC.LongTime

private theorem mfderiv_exp_neg_collar_height_ne_zero
    {E F H G N M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace G]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    [TopologicalSpace N] [ChartedSpace G N]
    [TopologicalSpace M] [ChartedSpace H M]
    (e : PartialDiffeomorph (J.prod 𝓘(ℝ)) I (N × ℝ) M ∞)
    {x : M} (hx : x ∈ e.target) :
    mfderiv I 𝓘(ℝ) (fun y => Real.exp (-(e.symm y).2) - 1) x ≠ 0 := by
  have hloc := e.symm.isLocalDiffeomorphAt _ _ _ hx
  have hdiff := hloc.mdifferentiableAt (by simp)
  obtain ⟨v, hv⟩ := (hloc.isInvertible_mfderiv (by simp)).surjective
    (0, (1 : ℝ))
  have hexp : HasDerivAt (fun h : ℝ => Real.exp (-h) - 1)
      (-(Real.exp (-(e.symm x).2))) (e.symm x).2 := by
    simpa only [mul_neg, mul_one] using!
      (((hasDerivAt_id (e.symm x).2).neg).exp.sub_const 1)
  have hh := (hexp.hasFDerivAt.hasMFDerivAt.comp (e.symm x)
    (hasMFDerivAt_snd (I := J) (I' := 𝓘(ℝ)) (e.symm x))).comp x
      hdiff.hasMFDerivAt
  intro hz
  have heq : mfderiv I 𝓘(ℝ) (fun y => Real.exp (-(e.symm y).2) - 1) x v =
      -(Real.exp (-(e.symm x).2)) := by
    have hraw := congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L v) hh.mfderiv
    change mfderiv I 𝓘(ℝ) (fun y => Real.exp (-(e.symm y).2) - 1) x v =
      (mfderiv I (J.prod 𝓘(ℝ)) e.symm x v).2 •
        (-(Real.exp (-(e.symm x).2))) at hraw
    rw [hv] at hraw
    simpa only [one_smul] using! hraw
  rw [hz, zero_apply] at heq
  exact (neg_ne_zero.mpr (Real.exp_ne_zero _)) heq.symm

open scoped Classical in
/-- The finite-collar construction at a previously fixed radius, with the
whole positive strip contained in the central bands and regular there. -/
private theorem exists_profile_at_radius
    {E F H G N M ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace G]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    [TopologicalSpace N] [ChartedSpace G N] [CompactSpace N]
    [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [Finite ι]
    (e : ι → PartialDiffeomorph (J.prod 𝓘(ℝ)) I (N × ℝ) M ∞)
    {L : Set M} (hclosed : IsClosed L)
    (hfront : frontier L ⊆ ⋃ i, range (fun s : N => e i (s, 0)))
    {r : ℝ} (hr : 0 < r)
    (hsource : ∀ i, univ ×ˢ Icc (-r) r ⊆ (e i).source)
    (hdisjoint : Pairwise (fun i j => Disjoint
      (e i '' (univ ×ˢ Ioo (-r) r)) (e j '' (univ ×ˢ Ioo (-r) r))))
    (hside : ∀ i s h, h ∈ Ioo (-r) r →
      (e i (s, h) ∈ L ↔ h ≤ 0) ∧
      (e i (s, h) ∈ interior L ↔ h < 0)) :
    let a : ℝ := (Real.exp (r / 2) - 1) / 2
    0 < a ∧ Real.log (1 + a) < r / 2 ∧
    ∃ ρ : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ ρ ∧
      (interior L)ᶜ = {x | ρ x ≤ 0} ∧
      (∀ i s h, h ∈ Ioo (-r) r →
        ρ (e i (s, h)) = flattenedExponentialProfile r h) ∧
      (∀ x, x ∉ ⋃ i, e i '' (univ ×ˢ Ioo (-r) r) →
        ρ x = if x ∈ L then Real.exp (r / 2) - 1 else Real.exp (-r / 2) - 1) ∧
      ∀ x, 0 ≤ ρ x → ρ x < a →
        mfderiv I 𝓘(ℝ) ρ x ≠ 0 ∧
        ∃ i, x ∈ e i '' (univ ×ˢ Ioo (-r / 2) (r / 2)) ∧
          ρ =ᶠ[𝓝 x] (fun y => Real.exp (-((e i).symm y).2) - 1) := by
  obtain ⟨ha, hlog, ρ, hρ, hregion, hformula, hoff, hstrip⟩ :=
    exists_smooth_defining_function_of_oriented_finite_collars e hclosed hfront
      hr hsource hdisjoint hside
  refine ⟨ha, hlog, ρ, hρ, hregion, hformula, hoff, ?_⟩
  intro x hx0 hxa
  obtain ⟨i, hxi, hgerm⟩ := hstrip x hx0 hxa
  have htarget : x ∈ (e i).target := by
    obtain ⟨z, hz, rfl⟩ := hxi
    exact (e i).map_source (hsource i ⟨hz.1, hz.2.1.le, hz.2.2.le⟩)
  have hregular : mfderiv I 𝓘(ℝ) ρ x ≠ 0 := by
    rw [hgerm.mfderiv_eq]
    exact mfderiv_exp_neg_collar_height_ne_zero (e i) htarget
  refine ⟨hregular, i, ?_, hgerm⟩
  obtain ⟨⟨s, h⟩, hh, rfl⟩ := hxi
  refine ⟨(s, h), ⟨mem_univ _, ?_⟩, rfl⟩
  apply mem_central_interval_of_flattenedExponentialProfile_mem_Ico hr
    (half_lt_self (sub_pos.mpr (by simpa using Real.exp_lt_exp.mpr (half_pos hr))))
  rw [← hformula i s h hh.2]
  exact ⟨hx0, hxa⟩

end GC.LongTime

namespace GC.LongTime

/-- Equality on an open model collar band gives the model germ directly.
The ambient transport is an arbitrary function; its continuity is not needed. -/
private theorem pullback_profile_eventuallyEq_of_collar_formula
    {S M X : Type*} [TopologicalSpace S] [TopologicalSpace M]
    (d : OpenPartialHomeomorph (S × ℝ) M) (κ : M → X) (ρ : X → ℝ)
    {r : ℝ}
    (hsource : univ ×ˢ Ioo (-r / 2) (r / 2) ⊆ d.source)
    (hformula : ∀ s h, h ∈ Ioo (-r / 2) (r / 2) →
      ρ (κ (d (s, h))) = Real.exp (-h) - 1)
    {z : M} (hz : z ∈ d '' (univ ×ˢ Ioo (-r / 2) (r / 2))) :
    (ρ ∘ κ) =ᶠ[𝓝 z] (fun y => Real.exp (-(d.symm y).2) - 1) := by
  have hopen : IsOpen (d '' (univ ×ˢ Ioo (-r / 2) (r / 2))) :=
    d.isOpen_image_of_subset_source (isOpen_univ.prod isOpen_Ioo) hsource
  filter_upwards [hopen.mem_nhds hz] with y hy
  obtain ⟨⟨s, h⟩, hh, rfl⟩ := hy
  change ρ (κ (d (s, h))) = Real.exp (-(d.symm (d (s, h))).2) - 1
  rw [d.left_inv (hsource hh)]
  exact hformula s h hh.2

/-- Lift a point in the transported central band to the very same model collar,
retaining both the transport equation and the model pullback germ. -/
private theorem exists_model_profile_germ_of_mem_transported_collar
    {E H F G S M X : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    [TopologicalSpace S] [ChartedSpace H S] [Nonempty S]
    [TopologicalSpace M] [ChartedSpace G M]
    {b : S → M} (d : SmoothTwoSidedCollar I J b)
    (κ : M → X) (e : S × ℝ → X) (ρ : X → ℝ)
    {r : ℝ} (hradius : r / 2 ≤ d.radius)
    (htransport : ∀ q, e q = κ (d.toPartialDiffeomorph q))
    (hformula : ∀ s h, h ∈ Ioo (-r / 2) (r / 2) →
      ρ (κ (d.toPartialDiffeomorph (s, h))) = Real.exp (-h) - 1)
    {x : X} (hx : x ∈ e '' (univ ×ˢ Ioo (-r / 2) (r / 2))) :
    ∃ z : M,
      z ∈ d.toPartialDiffeomorph '' (univ ×ˢ Ioo (-r / 2) (r / 2)) ∧
      κ z = x ∧
      (ρ ∘ κ) =ᶠ[𝓝 z]
        (fun y => Real.exp (-((d.toPartialDiffeomorph).symm y).2) - 1) := by
  obtain ⟨q, hq, hqx⟩ := hx
  have hz : d.toPartialDiffeomorph q ∈
      d.toPartialDiffeomorph '' (univ ×ˢ Ioo (-r / 2) (r / 2)) :=
    ⟨q, hq, rfl⟩
  refine ⟨d.toPartialDiffeomorph q, hz, (htransport q).symm.trans hqx, ?_⟩
  have hsource : univ ×ˢ Ioo (-r / 2) (r / 2) ⊆ d.toPartialDiffeomorph.source := by
    rw [d.toPartialDiffeomorph_source]
    intro p hp
    have hneg : -d.radius ≤ -r / 2 := by
      simpa only [neg_div] using neg_le_neg hradius
    exact ⟨hp.1, hneg.trans_lt hp.2.1, hp.2.2.trans_le hradius⟩
  exact pullback_profile_eventuallyEq_of_collar_formula
    d.toPartialDiffeomorph.toOpenPartialHomeomorph κ ρ hsource hformula hz

end GC.LongTime

namespace GC.LongTime

universe u

open scoped Classical in
/-- The original finite cusp exterior has actual smooth defining profiles at
every sufficiently small fixed model radius. Model collars and compact buffers
are chosen before the accuracy tolerance and the common late-time threshold. -/
theorem PersistentCuspExterior.exists_eventual_collar_profiles
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {K : ℕ} (C : PersistentHyperbolicCores F K) (ext : PersistentCuspExterior C) :
    ∃ d : (p : (i : Fin C.count) × Fin (ext.truncation i).count) →
        SmoothTwoSidedCollar torusModel (𝓡 3)
          (fun s => (ext.truncation p.1).cuspMap p.2 (s, halfZero)),
      (∀ p (q : Torus × symmetricOpenInterval (d p).radius) (hq : 0 ≤ q.2.val),
        (d p).toFun q = (ext.truncation p.1).cuspMap p.2 (q.1, halfPoint q.2.val hq)) ∧
      ∃ R : ℝ, 0 < R ∧ (∀ p, 2 * R < (d p).radius) ∧
      ∃ B : (i : Fin C.count) → Set (C.model i).Carrier,
        (∀ i, IsCompact (B i)) ∧
        (∀ i, range (ext.truncation i).inclusion ⊆ B i) ∧
        (∀ p, ((d p).neighborhood : Set (C.model p.1).Carrier) ⊆ B p.1) ∧
        ∀ (tmin : ℝ) (n : ℕ) (ε : ℝ), 0 < ε →
        ∃ T : ℝ, ∃ hstart : ext.start ≤ T, tmin ≤ T ∧ 1 ≤ T ∧
        ∀ (t : ℝ) (ht : T ≤ t),
          C.accuracy t < ε ∧ n ≤ max K ⌈(C.accuracy t)⁻¹⌉₊ ∧
          (∀ i, B i ⊆ riemannianBallOf (C.model i).metric
            (C.model i).basepoint (C.accuracy t)⁻¹) ∧
          (∀ i, B i ⊆ C.domain i t) ∧ IsCompact (ext.region t) ∧
          ∃ Φ : (p : (i : Fin C.count) × Fin (ext.truncation i).count) →
              PartialDiffeomorph (𝓡 3) (𝓡 3)
                (C.model p.1).Carrier (postStage F.observation t).Carrier ∞,
            (∀ p, (Φ p).source = C.domain p.1 t ∧
              (Φ p).target = C.map p.1 t (ext.after_cores.trans (hstart.trans ht)) ''
                C.domain p.1 t ∧
              (Φ p).toFun = C.map p.1 t (ext.after_cores.trans (hstart.trans ht))) ∧
            let e := fun p => (d p).toPartialDiffeomorph.trans (Φ p)
            let L := ⋃ i, C.map i t (ext.after_cores.trans (hstart.trans ht)) ''
              range (ext.truncation i).inclusion
            IsCompact L ∧ closure (interior L) = L ∧
            (∀ p, (e p).source = (d p).toPartialDiffeomorph.source) ∧
            (∀ p, univ ×ˢ Icc (-(2 * R)) (2 * R) ⊆ (e p).source) ∧
            (∀ p q, e p q = C.map p.1 t (ext.after_cores.trans (hstart.trans ht))
              ((d p).toPartialDiffeomorph q)) ∧
            Pairwise (fun p q => Disjoint
              (e p '' (univ ×ˢ Ioo (-R) R)) (e q '' (univ ×ˢ Ioo (-R) R))) ∧
            (∀ p s h, h ∈ Ioo (-R) R →
              (e p (s, h) ∈ L ↔ h ≤ 0) ∧
              (e p (s, h) ∈ interior L ↔ h < 0)) ∧
            frontier L = ⋃ p, range (fun s : Torus => e p (s, 0)) ∧
            ext.region t = (interior L)ᶜ ∧
            ∀ r : ℝ, 0 < r → r ≤ R →
            let a : ℝ := (Real.exp (r / 2) - 1) / 2
            0 < a ∧ Real.log (1 + a) < r / 2 ∧
            ∃ ρ : (postStage F.observation t).Carrier → ℝ,
              ContMDiff (𝓡 3) 𝓘(ℝ) ∞ ρ ∧
              ext.region t = {x | ρ x ≤ 0} ∧
              (∀ p s h, h ∈ Ioo (-r) r →
                ρ (e p (s, h)) = flattenedExponentialProfile r h) ∧
              (∀ x, x ∉ ⋃ p, e p '' (univ ×ˢ Ioo (-r) r) →
                ρ x = if x ∈ L then Real.exp (r / 2) - 1 else Real.exp (-r / 2) - 1) ∧
              (∀ p s h, h ∈ Ioo (-r / 2) (r / 2) →
                ρ (C.map p.1 t (ext.after_cores.trans (hstart.trans ht))
                  ((d p).toPartialDiffeomorph (s, h))) = Real.exp (-h) - 1) ∧
              (∀ x, ρ x = 0 → mfderiv (𝓡 3) 𝓘(ℝ) ρ x ≠ 0) ∧
              ∀ x, 0 ≤ ρ x → ρ x < a →
                mfderiv (𝓡 3) 𝓘(ℝ) ρ x ≠ 0 ∧
                ∃ p, x ∈ e p '' (univ ×ˢ Ioo (-r / 2) (r / 2)) ∧
                  ρ =ᶠ[𝓝 x] (fun y => Real.exp (-((e p).symm y).2) - 1) ∧
                  ∃ z : (C.model p.1).Carrier,
                    z ∈ (d p).toPartialDiffeomorph ''
                      (univ ×ˢ Ioo (-r / 2) (r / 2)) ∧
                    C.map p.1 t (ext.after_cores.trans (hstart.trans ht)) z = x ∧
                    (ρ ∘ C.map p.1 t (ext.after_cores.trans (hstart.trans ht))) =ᶠ[𝓝 z]
                      (fun y => Real.exp (-((d p).toPartialDiffeomorph.symm y).2) - 1) := by
  classical
  obtain ⟨d, hd, R, hR, hRd, B, hB, hcore, hneigh, T₀, hstart₀, _, htransport⟩ :=
    PersistentCuspExterior.exists_eventual_signed_collar_transport C ext 0
  refine ⟨d, hd, R, hR, hRd, B, hB, hcore, hneigh, ?_⟩
  intro tmin n ε hε
  obtain ⟨T, _, hT, haccuracy⟩ :=
    C.eventually_compact_subset_advertised_ball B hB (max (max T₀ tmin) 1) n hε
  have hT₀ : T₀ ≤ T := (le_max_left _ _).trans ((le_max_left _ _).trans hT)
  have hstart : ext.start ≤ T := hstart₀.trans hT₀
  refine ⟨T, hstart, (le_max_right _ _).trans ((le_max_left _ _).trans hT),
    (le_max_right _ _).trans hT, ?_⟩
  intro t ht
  obtain ⟨hεt, horder, hball, hdomain⟩ := haccuracy t ht
  obtain ⟨_, Φ, hΦ, hcompact, hregular, hsource, hband, happly, hdisj, hside,
    hfront, hregion⟩ := htransport t (hT₀.trans ht)
  refine ⟨hεt, horder, hball, hdomain, ext.isCompact_region t, Φ, hΦ,
    hcompact, hregular, hsource, hband, happly, hdisj, hside, hfront, hregion, ?_⟩
  intro r hr hrR
  let e := fun p => (d p).toPartialDiffeomorph.trans (Φ p)
  have hsmall : (univ : Set Torus) ×ˢ Ioo (-r) r ⊆ univ ×ˢ Ioo (-R) R := by
    intro z hz
    exact ⟨hz.1, (neg_le_neg hrR).trans_lt hz.2.1, hz.2.2.trans_le hrR⟩
  have hsrc (p : (i : Fin C.count) × Fin (ext.truncation i).count) :
      univ ×ˢ Icc (-r) r ⊆ (e p).source := by
    intro z hz
    exact hband p ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  have hsep : Pairwise (fun p q => Disjoint
      (e p '' (univ ×ˢ Ioo (-r) r)) (e q '' (univ ×ˢ Ioo (-r) r))) :=
    fun p q hpq => (hdisj hpq).mono (image_mono hsmall) (image_mono hsmall)
  obtain ⟨ha, hlog, ρ, hρ, hreg, hformula, hoff, hstrip⟩ := exists_profile_at_radius
    e hcompact.isClosed hfront.subset hr hsrc hsep
      (fun p s h hh => hside p s h (hsmall (a := (s, h)) ⟨mem_univ _, hh⟩).2)
  have hcentralFormula (p : (i : Fin C.count) × Fin (ext.truncation i).count)
      (s : Torus) (h : ℝ) (hh : h ∈ Ioo (-r / 2) (r / 2)) :
      ρ (C.map p.1 t (ext.after_cores.trans (hstart.trans ht))
        ((d p).toPartialDiffeomorph (s, h))) = Real.exp (-h) - 1 := by
    rw [← happly p (s, h), hformula p s h (by constructor <;> linarith [hh.1, hh.2])]
    exact flattenedExponentialProfile_eq_exp hr ⟨hh.1.le, hh.2.le⟩
  refine ⟨ha, hlog, ρ, hρ, hregion.trans hreg, hformula, hoff, hcentralFormula, ?_, ?_⟩
  · intro x hx
    exact (hstrip x (by rw [hx]) (by rw [hx]; exact ha)).1
  · intro x hx0 hxa
    obtain ⟨hne, p, hxp, hstage⟩ := hstrip x hx0 hxa
    have hradius : r / 2 ≤ (d p).radius := by linarith [hRd p]
    obtain ⟨z, hz, hmap, hmodel⟩ := exists_model_profile_germ_of_mem_transported_collar
      (d p) (C.map p.1 t (ext.after_cores.trans (hstart.trans ht))) (e p) ρ hradius
        (happly p) (hcentralFormula p) hxp
    exact ⟨hne, p, hxp, hstage, z, hz, hmap, hmodel⟩

end GC.LongTime
