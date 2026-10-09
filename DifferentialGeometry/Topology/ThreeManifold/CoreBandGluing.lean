import DifferentialGeometry.Topology.ThreeManifold.CutCapCoreTubeGluing
import DifferentialGeometry.Topology.Attachment.Union

set_option autoImplicit false

noncomputable section

open Set Function

namespace DifferentialGeometry.Topology.SphericalTubeSystem

universe u

local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "Band" => S2 × Icc (-1 : ℝ) 1
local notation "Tube" => S2 × Icc (-2 : ℝ) 2

local instance : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩

variable {M : ClosedOrientedManifold.{u} 3} (T : SphericalTubeSystem M)

private def bandInclusion (q : Band) : Tube :=
  (q.1, ⟨q.2.val, by constructor <;> linarith [q.2.property.1, q.2.property.2]⟩)

private theorem bandInclusion_injective : Injective bandInclusion := by
  intro q q' h
  exact Prod.ext (congrArg (fun q : Tube => q.1) h)
    (Subtype.ext (congrArg (fun q : Tube => q.2.val) h))

private theorem continuous_bandInclusion : Continuous bandInclusion :=
  continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _)

private def bandEndLevel (side : Bool) : Icc (-1 : ℝ) 1 :=
  if side then ⟨1, by norm_num⟩ else ⟨-1, by norm_num⟩

private theorem bandInclusion_end (side : Bool) (z : S2) :
    bandInclusion (z, bandEndLevel side) = (z, boundaryLevel side) := by
  cases side <;> rfl

def coreBandBoundaryInclusion (S : Finset T.Index) :
    (Σ _a : S, Bool × S2) → (Σ _a : S, Band) :=
  fun q => ⟨q.1, q.2.2, bandEndLevel q.2.1⟩

def coreBandAttachingMap (S : Finset T.Index) :
    (Σ _a : S, Bool × S2) → T.core :=
  fun q => T.coreBoundarySphere (q.1.val, q.2.1) q.2.2

def coreBandMap (S : Finset T.Index) : C((Σ _a : S, Band), M.Carrier) where
  toFun q := T.tube q.1.val (bandInclusion q.2)
  continuous_toFun := continuous_sigma fun a =>
    (T.tube a.val).continuous.comp continuous_bandInclusion

theorem coreBandMap_boundary (S : Finset T.Index) (q : Σ _a : S, Bool × S2) :
    T.coreBandMap S (T.coreBandBoundaryInclusion S q) = (T.coreBandAttachingMap S q).val := by
  change T.tube q.1.val (bandInclusion (q.2.2, bandEndLevel q.2.1)) = _
  rw [bandInclusion_end]
  rfl

theorem coreBandMap_injective (S : Finset T.Index) : Injective (T.coreBandMap S) := by
  rintro ⟨a, q⟩ ⟨a', q'⟩ h
  have haa : a = a' := by
    apply Subtype.ext
    by_contra hne
    exact (Set.disjoint_left.mp (T.disjoint hne) (mem_range_self (bandInclusion q)))
      ⟨bandInclusion q', h.symm⟩
  subst a'
  have hqq : q = q' := bandInclusion_injective ((T.smooth a.val).isEmbedding.injective h)
  cases hqq
  rfl

theorem range_coreBandMap (S : Finset T.Index) :
    range (T.coreBandMap S) = ⋃ a ∈ S, T.band a := by
  ext x
  constructor
  · rintro ⟨⟨a, q⟩, rfl⟩
    exact mem_iUnion.mpr ⟨a.val, mem_iUnion.mpr ⟨a.property,
      ⟨bandInclusion q, q.2.property, rfl⟩⟩⟩
  · intro hx
    obtain ⟨a, ha⟩ := mem_iUnion.mp hx
    obtain ⟨haS, q, hq, rfl⟩ := mem_iUnion.mp ha
    refine ⟨⟨⟨a, haS⟩, q.1, ⟨q.2.val, hq⟩⟩, ?_⟩
    apply congrArg (T.tube a)
    exact Prod.ext rfl (Subtype.ext rfl)

theorem coreBandMap_mem_core_iff (S : Finset T.Index) (q : Σ _a : S, Band) :
    T.coreBandMap S q ∈ T.core ↔ q ∈ range (T.coreBandBoundaryInclusion S) := by
  constructor
  · intro hq
    have hband : -1 ≤ ((bandInclusion q.2).2 : ℝ) ∧
        ((bandInclusion q.2).2 : ℝ) ≤ 1 := q.2.2.property
    rcases T.eq_boundaryLevel_of_mem_band_of_mem_core hband hq with h | h
    · refine ⟨⟨q.1, false, q.2.1⟩, ?_⟩
      exact congrArg (fun t : Icc (-1 : ℝ) 1 =>
        (⟨q.1, q.2.1, t⟩ : Σ _a : S, Band)) (Subtype.ext h.symm)
    · refine ⟨⟨q.1, true, q.2.1⟩, ?_⟩
      exact congrArg (fun t : Icc (-1 : ℝ) 1 =>
        (⟨q.1, q.2.1, t⟩ : Σ _a : S, Band)) (Subtype.ext h.symm)
  · rintro ⟨b, rfl⟩
    rw [T.coreBandMap_boundary]
    exact (T.coreBandAttachingMap S b).property

abbrev CoreBandGluing (S : Finset T.Index) :=
  AdjunctionSpace (T.coreBandBoundaryInclusion S) (T.coreBandAttachingMap S)

noncomputable def coreBandHomeomorph (S : Finset T.Index) :
    T.CoreBandGluing S ≃ₜ (T.core ∪ ⋃ a ∈ S, T.band a : Set M.Carrier) :=
  (adjunctionHomeomorphUnionImage (T.coreBandBoundaryInclusion S)
    (T.coreBandAttachingMap S) (T.coreBandMap S)
    (fun q => (T.coreBandMap_boundary S q).symm)
    (T.coreBandMap_injective S) (T.coreBandMap S).continuous
    (fun q hq => (T.coreBandMap_mem_core_iff S q).mp hq)
    (isOpen_iUnion T.removedBand_isOpen).isClosed_compl).trans
    (Homeomorph.setCongr (by rw [T.range_coreBandMap]))

theorem coreBandHomeomorph_core (S : Finset T.Index) (x : T.core) :
    (T.coreBandHomeomorph S (adjunctionLower (i := T.coreBandBoundaryInclusion S)
      (T.coreBandAttachingMap S) x)).val = x.val := rfl

theorem coreBandHomeomorph_band (S : Finset T.Index) (q : Σ _a : S, Band) :
    (T.coreBandHomeomorph S (adjunctionCell (T.coreBandBoundaryInclusion S)
      (T.coreBandAttachingMap S) q)).val = T.coreBandMap S q := rfl

theorem coreBandGluing_seam (S : Finset T.Index) (q : Σ _a : S, Bool × S2) :
    adjunctionCell (T.coreBandBoundaryInclusion S) (T.coreBandAttachingMap S)
        (T.coreBandBoundaryInclusion S q) =
      adjunctionLower (i := T.coreBandBoundaryInclusion S) (T.coreBandAttachingMap S)
        (T.coreBandAttachingMap S q) :=
  adjunction_coherence _ _ q

theorem coreBandGluing_seam_insert [DecidableEq T.Index] (S : Finset T.Index)
    (e a : T.Index) (ha : a ∈ S) (b : Bool) (z : S2) :
    adjunctionCell (T.coreBandBoundaryInclusion (insert e S))
        (T.coreBandAttachingMap (insert e S))
        (T.coreBandBoundaryInclusion (insert e S) ⟨⟨a, Finset.mem_insert_of_mem ha⟩, b, z⟩) =
      adjunctionLower (i := T.coreBandBoundaryInclusion (insert e S))
        (T.coreBandAttachingMap (insert e S))
        (T.coreBoundarySphere (a, b) z) :=
  T.coreBandGluing_seam (insert e S) ⟨⟨a, Finset.mem_insert_of_mem ha⟩, b, z⟩

noncomputable def coreBandHomeomorphSource : T.CoreBandGluing Finset.univ ≃ₜ M.Carrier :=
  (T.coreBandHomeomorph Finset.univ).trans
    ((Homeomorph.setCongr (by simpa only [Set.iUnion_true, Finset.mem_univ, bandRange] using T.core_union_bandRange)).trans
      (Homeomorph.Set.univ M.Carrier))

theorem coreBandHomeomorphSource_core (x : T.core) :
    T.coreBandHomeomorphSource (adjunctionLower (i := T.coreBandBoundaryInclusion Finset.univ)
      (T.coreBandAttachingMap Finset.univ) x) = x.val :=
  T.coreBandHomeomorph_core Finset.univ x

theorem coreBandHomeomorphSource_band (q : Σ _a : (Finset.univ : Finset T.Index), Band) :
    T.coreBandHomeomorphSource (adjunctionCell (T.coreBandBoundaryInclusion Finset.univ)
      (T.coreBandAttachingMap Finset.univ) q) = T.coreBandMap Finset.univ q :=
  T.coreBandHomeomorph_band Finset.univ q

end DifferentialGeometry.Topology.SphericalTubeSystem
