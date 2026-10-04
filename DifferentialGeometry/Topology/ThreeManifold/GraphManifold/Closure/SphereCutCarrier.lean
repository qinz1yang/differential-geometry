import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SphereCapCoordinates
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SphereCapHalfFold
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CarrierSurgeryCutSpace
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CarrierSurgeryAtlas
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.RegularSublevelAtlas

/-!
Actual bounded spherical cuts retain old torus collars and have oriented folds, full spherical
half collars, mixed boundary exhaustion and the original carrier as their actual quotient.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

variable {W : CompactCarrier.{u}}

def sphereCutSign (b : Bool) (s : ℝ) : ℝ := if b then -s else s

def sphereCutTag (j : Fin 1) (b : Bool) (s : ℝ) : Fin 1 → ℝ :=
  fun i => if i = j then sphereCutSign b (1 - seamCut s) else 0

def sphereCutBand (c : Fin 1 → PartialDiffeomorph sphereSignedCollarModel W.model
    (ClosureSphere.{u} × ℝ) W.Carrier ∞) (j : Fin 1) (b : Bool) (p : ClosureSphere.{u} × ℝ) :
    W.Carrier × (Fin 1 → ℝ) :=
  (c j (p.1, sphereCutSign b p.2), sphereCutTag j b p.2)

def sphereCutOutside (c : Fin 1 → PartialDiffeomorph sphereSignedCollarModel W.model
    (ClosureSphere.{u} × ℝ) W.Carrier ∞) : Set W.Carrier :=
  (⋃ j, c j '' ((univ : Set ClosureSphere.{u}) ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2)))ᶜ

def sphereCutSet (c : Fin 1 → PartialDiffeomorph sphereSignedCollarModel W.model
    (ClosureSphere.{u} × ℝ) W.Carrier ∞) : Set (W.Carrier × (Fin 1 → ℝ)) :=
  (fun x : W.Carrier => (x, (0 : Fin 1 → ℝ))) '' sphereCutOutside c ∪
    ⋃ j, ⋃ b : Bool, sphereCutBand c j b ''
      ((univ : Set ClosureSphere.{u}) ×ˢ Icc (0 : ℝ) (1 / 2))

abbrev SphereCutSpace (c : Fin 1 → PartialDiffeomorph sphereSignedCollarModel W.model
    (ClosureSphere.{u} × ℝ) W.Carrier ∞) := sphereCutSet c

theorem sphereCutOutside_closed (c : Fin 1 → PartialDiffeomorph sphereSignedCollarModel W.model
    (ClosureSphere.{u} × ℝ) W.Carrier ∞) (hs : ∀ j, (c j).source = sphereSignedCollarSource) :
    IsClosed (sphereCutOutside c) := by
  apply IsOpen.isClosed_compl
  apply isOpen_iUnion
  intro j
  apply (c j).toOpenPartialHomeomorph.isOpen_image_of_subset_source
    (isOpen_univ.prod isOpen_Ioo)
  intro p hp
  change p ∈ (c j).source
  rw [hs j]
  simp only [sphereSignedCollarSource, mem_prod, mem_univ, true_and]
  change -1 < p.2 ∧ p.2 < 1
  constructor <;> linarith [hp.2.1, hp.2.2]

theorem sphereCutBand_continuousOn
    (c : Fin 1 → PartialDiffeomorph sphereSignedCollarModel W.model
      (ClosureSphere.{u} × ℝ) W.Carrier ∞)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource) (j : Fin 1) (b : Bool) :
    ContinuousOn (sphereCutBand c j b) ((univ : Set ClosureSphere.{u}) ×ˢ Icc (0 : ℝ) (1 / 2)) := by
  have hsign : Continuous (sphereCutSign b) := by
    cases b
    · exact continuous_id
    · exact continuous_neg
  have hp : Continuous fun p : ClosureSphere.{u} × ℝ => (p.1, sphereCutSign b p.2) :=
    continuous_fst.prodMk (hsign.comp continuous_snd)
  have hmap : ∀ p ∈ ((univ : Set ClosureSphere.{u}) ×ˢ Icc (0 : ℝ) (1 / 2)),
      (p.1, sphereCutSign b p.2) ∈ (c j).source := by
    intro p h
    rw [hs j]
    simp only [sphereSignedCollarSource, mem_prod, mem_univ, true_and]
    change -1 < sphereCutSign b p.2 ∧ sphereCutSign b p.2 < 1
    cases b <;> simp only [sphereCutSign, Bool.false_eq_true, ↓reduceIte] <;>
      constructor <;> linarith [h.2.1, h.2.2]
  have htag : Continuous fun p : ClosureSphere.{u} × ℝ => sphereCutTag j b p.2 := by
    apply continuous_pi
    intro i
    by_cases hi : i = j
    · simp only [sphereCutTag, hi, ↓reduceIte]
      exact hsign.comp ((continuous_const.sub contDiff_seamCut.continuous).comp continuous_snd)
    · simp only [sphereCutTag, hi, ↓reduceIte]
      exact continuous_const
  exact ((c j).contMDiffOn.continuousOn.comp hp.continuousOn hmap).prodMk
    htag.continuousOn

theorem sphereCutSet_compact (c : Fin 1 → PartialDiffeomorph sphereSignedCollarModel W.model
    (ClosureSphere.{u} × ℝ) W.Carrier ∞) (hs : ∀ j, (c j).source = sphereSignedCollarSource) :
    IsCompact (sphereCutSet c) := by
  apply IsCompact.union
  · exact (sphereCutOutside_closed c hs).isCompact.image
      (continuous_id.prodMk continuous_const)
  · apply isCompact_iUnion
    intro j
    apply isCompact_iUnion
    intro b
    exact (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
      (sphereCutBand_continuousOn c hs j b)

theorem sphereCut_projection_surjective
    (c : Fin 1 → PartialDiffeomorph sphereSignedCollarModel W.model
      (ClosureSphere.{u} × ℝ) W.Carrier ∞) :
    Function.Surjective (fun x : SphereCutSpace c => x.val.1) := by
  intro x
  by_cases hx : x ∈ sphereCutOutside c
  · exact ⟨⟨(x, 0), Or.inl ⟨x, hx, rfl⟩⟩, rfl⟩
  · have hu : x ∈ ⋃ j, c j '' ((univ : Set ClosureSphere.{u}) ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2)) :=
      not_not.mp hx
    obtain ⟨j, p, hp, hpx⟩ := mem_iUnion.mp hu
    by_cases hneg : p.2 < 0
    · let q := (p.1, -p.2)
      have hq : q ∈ (univ : Set ClosureSphere.{u}) ×ˢ Icc (0 : ℝ) (1 / 2) :=
        ⟨mem_univ _, neg_nonneg.mpr hneg.le, by dsimp only [q]; linarith [hp.2.1]⟩
      refine ⟨⟨sphereCutBand c j true q,
        Or.inr (mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨true, q, hq, rfl⟩⟩)⟩, ?_⟩
      change c j (p.1, -(-p.2)) = x
      simpa only [neg_neg] using hpx
    · have hq : p ∈ (univ : Set ClosureSphere.{u}) ×ˢ Icc (0 : ℝ) (1 / 2) :=
        ⟨mem_univ _, le_of_not_gt hneg, hp.2.2.le⟩
      exact ⟨⟨sphereCutBand c j false p,
        Or.inr (mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨false, p, hq, rfl⟩⟩)⟩, hpx⟩

theorem sphereCutCompactSpace
    (c : Fin 1 → PartialDiffeomorph sphereSignedCollarModel W.model
      (ClosureSphere.{u} × ℝ) W.Carrier ∞)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource) : CompactSpace (SphereCutSpace c) :=
  isCompact_iff_compactSpace.mp (sphereCutSet_compact c hs)

def sphereCutFold
    (c : Fin 1 → PartialDiffeomorph sphereSignedCollarModel W.model
      (ClosureSphere.{u} × ℝ) W.Carrier ∞) :
    SphereCutSpace c → W.Carrier := fun x => x.val.1

theorem sphereCutFold_continuous
    (c : Fin 1 → PartialDiffeomorph sphereSignedCollarModel W.model
      (ClosureSphere.{u} × ℝ) W.Carrier ∞) :
    Continuous (sphereCutFold c) := continuous_subtype_val.fst

theorem sphereCutFold_isQuotientMap
    (c : Fin 1 → PartialDiffeomorph sphereSignedCollarModel W.model
      (ClosureSphere.{u} × ℝ) W.Carrier ∞)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource) :
    _root_.Topology.IsQuotientMap (sphereCutFold c) := by
  let : CompactSpace (SphereCutSpace c) := sphereCutCompactSpace c hs
  exact (sphereCutFold_continuous c).isClosedMap.isQuotientMap
    (sphereCutFold_continuous c) (sphereCut_projection_surjective c)

def sphereCutZero
    (c : Fin 1 → PartialDiffeomorph sphereSignedCollarModel W.model
      (ClosureSphere.{u} × ℝ) W.Carrier ∞)
    (j : Fin 1) (b : Bool) (t : ClosureSphere.{u}) : SphereCutSpace c :=
  ⟨sphereCutBand c j b (t, 0), Or.inr (mem_iUnion.mpr ⟨j,
    mem_iUnion.mpr ⟨b, (t, 0), ⟨mem_univ _, le_rfl, by norm_num⟩, rfl⟩⟩)⟩

theorem sphereCutZero_fold
    (c : Fin 1 → PartialDiffeomorph sphereSignedCollarModel W.model
      (ClosureSphere.{u} × ℝ) W.Carrier ∞)
    (j : Fin 1) (b : Bool) (t : ClosureSphere.{u}) : sphereCutFold c (sphereCutZero c j b t) =
      c j (t, 0) := by
  cases b <;> simp [sphereCutFold, sphereCutZero, sphereCutBand, sphereCutSign]

theorem sphereCutZero_ne
    (c : Fin 1 → PartialDiffeomorph sphereSignedCollarModel W.model
      (ClosureSphere.{u} × ℝ) W.Carrier ∞)
   
    (j : Fin 1) (t t' : ClosureSphere.{u}) :
    sphereCutZero c j true t ≠ sphereCutZero c j false t' := by
  intro h
  have he := congrArg (fun x : SphereCutSpace c => x.val.2 j) h
  have hc : seamCut 0 = 0 := seamCut_of_le (by norm_num)
  simp [sphereCutZero, sphereCutBand, sphereCutTag, sphereCutSign, hc] at he
  norm_num at he

theorem sphereCutOutside_coordinate
    (c : Fin 1 → PartialDiffeomorph sphereSignedCollarModel W.model
      (ClosureSphere.{u} × ℝ) W.Carrier ∞)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target)
    (j : Fin 1) (p : ClosureSphere.{u} × ℝ) (hp : p ∈ (c j).source) :
    c j p ∈ sphereCutOutside c ↔ ¬ (-(1 / 2 : ℝ) < p.2 ∧ p.2 < 1 / 2) := by
  have hi : c j p ∈ ⋃ k, c k '' ((univ : Set ClosureSphere.{u}) ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2)) ↔
      -(1 / 2 : ℝ) < p.2 ∧ p.2 < 1 / 2 := by
    constructor
    · intro h
      obtain ⟨k, q, hq, he⟩ := mem_iUnion.mp h
      have hqsrc : q ∈ (c k).source := by
        rw [hs k]
        simp only [sphereSignedCollarSource, mem_prod, mem_univ, true_and]
        change -1 < q.2 ∧ q.2 < 1
        constructor <;> linarith [hq.2.1, hq.2.2]
      have hkj : k = j := by
        by_contra hne
        have ht : c j p ∈ (c k).target := he ▸ (c k).map_source hqsrc
        exact disjoint_left.mp (hd hne) ht ((c j).map_source hp)
      subst k
      have heq := (c j).toOpenPartialHomeomorph.injOn hqsrc hp he
      rw [heq] at hq
      exact hq.2
    · intro h
      exact mem_iUnion.mpr ⟨j, p, ⟨mem_univ _, h⟩, rfl⟩
  exact not_congr hi

theorem sphereCutTag_zero_of_ge (j : Fin 1) (b : Bool) {s : ℝ} (hs : 1 / 2 ≤ s) :
    sphereCutTag j b s = 0 := by
  ext i
  simp [sphereCutTag, sphereCutSign, seamCut_of_ge hs]

theorem sphereCutBand_mem_of_height
    (c : Fin 1 → PartialDiffeomorph sphereSignedCollarModel W.model
      (ClosureSphere.{u} × ℝ) W.Carrier ∞)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target)
    (j : Fin 1) (b : Bool) (p : ClosureSphere.{u} × ℝ) (hp0 : 0 ≤ p.2) (hp1 : p.2 < 1) :
    sphereCutBand c j b p ∈ sphereCutSet c := by
  by_cases hsmall : p.2 ≤ 1 / 2
  · exact Or.inr (mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨b, p,
      ⟨mem_univ _, hp0, hsmall⟩, rfl⟩⟩)
  · have hsrc : (p.1, sphereCutSign b p.2) ∈ (c j).source := by
      rw [hs j]
      simp only [sphereSignedCollarSource, mem_prod, mem_univ, true_and]
      change -1 < sphereCutSign b p.2 ∧ sphereCutSign b p.2 < 1
      cases b <;> simp only [sphereCutSign, Bool.false_eq_true, ↓reduceIte] <;>
        constructor <;> linarith
    have hout : c j (p.1, sphereCutSign b p.2) ∈ sphereCutOutside c := by
      apply (sphereCutOutside_coordinate c hs hd j _ hsrc).mpr
      cases b <;> simp only [sphereCutSign, Bool.false_eq_true, ↓reduceIte] <;>
        intro h <;> linarith [h.1, h.2, lt_of_not_ge hsmall]
    refine Or.inl ⟨c j (p.1, sphereCutSign b p.2), hout, ?_⟩
    exact Prod.ext rfl (sphereCutTag_zero_of_ge j b (lt_of_not_ge hsmall).le).symm

def sphereCutHalfLift
    (c : Fin 1 → PartialDiffeomorph sphereSignedCollarModel W.model
      (ClosureSphere.{u} × ℝ) W.Carrier ∞)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target)
    (j : Fin 1) (b : Bool) (p : sphereHalfCollarSource) : SphereCutSpace c :=
  ⟨sphereCutBand c j b (p.val.1, p.val.2.val 0),
    sphereCutBand_mem_of_height c hs hd j b _ (p.val.2.property) p.property⟩

theorem sphereCutHalfLift_fold
    (c : Fin 1 → PartialDiffeomorph sphereSignedCollarModel W.model
      (ClosureSphere.{u} × ℝ) W.Carrier ∞)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target)
    (j : Fin 1) (b : Bool) (p : sphereHalfCollarSource) :
    sphereCutFold c (sphereCutHalfLift c hs hd j b p) =
      c j (p.val.1, sphereCutSign b (p.val.2.val 0)) := rfl

theorem sphereCutZero_continuous
    (c : Fin 1 → PartialDiffeomorph sphereSignedCollarModel W.model
      (ClosureSphere.{u} × ℝ) W.Carrier ∞)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource) (j : Fin 1) (b : Bool) :
    Continuous (sphereCutZero c j b) := by
  apply Continuous.subtype_mk
  apply (sphereCutBand_continuousOn c hs j b).comp_continuous
    (continuous_id.prodMk continuous_const)
  intro t
  exact ⟨mem_univ _, le_rfl, by norm_num⟩

theorem sphereCutZero_injective
    (c : Fin 1 → PartialDiffeomorph sphereSignedCollarModel W.model
      (ClosureSphere.{u} × ℝ) W.Carrier ∞)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource) (j : Fin 1) (b : Bool) :
    Function.Injective (sphereCutZero c j b) := by
  intro t t' h
  have hh := congrArg (sphereCutFold c) h
  rw [sphereCutZero_fold, sphereCutZero_fold] at hh
  have hz (t : ClosureSphere.{u}) : (t, (0 : ℝ)) ∈ (c j).source := by
    rw [hs j]
    simp only [sphereSignedCollarSource, mem_prod, mem_univ, true_and]
    change -1 < (0 : ℝ) ∧ (0 : ℝ) < 1
    norm_num
  exact congrArg Prod.fst ((c j).toOpenPartialHomeomorph.injOn (hz t) (hz t') hh)

theorem sphereCutZero_isClosedEmbedding
    (c : Fin 1 → PartialDiffeomorph sphereSignedCollarModel W.model
      (ClosureSphere.{u} × ℝ) W.Carrier ∞)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource) (j : Fin 1) (b : Bool) :
    _root_.Topology.IsClosedEmbedding (sphereCutZero c j b) :=
  (sphereCutZero_continuous c hs j b).isClosedEmbedding (sphereCutZero_injective c hs j b)



abbrev SphereCutSignedCollars (W : CompactCarrier.{u}) :=
  Fin 1 → PartialDiffeomorph sphereSignedCollarModel W.model
    (ClosureSphere.{u} × ℝ) W.Carrier ∞


theorem sphereCutBand_source (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource) (j : Fin 1) (b : Bool)
    (p : ClosureSphere.{u} × ℝ) (hp : p ∈ (univ : Set ClosureSphere.{u}) ×ˢ Icc (0 : ℝ) (1 / 2)) :
    (p.1, sphereCutSign b p.2) ∈ (c j).source := by
  rw [hs j]
  simp only [sphereSignedCollarSource, mem_prod, mem_univ, true_and]
  change -1 < sphereCutSign b p.2 ∧ sphereCutSign b p.2 < 1
  cases b <;> simp only [sphereCutSign, Bool.false_eq_true, ↓reduceIte] <;>
    constructor <;> linarith [hp.2.1, hp.2.2]

theorem sphereCutBand_injOn (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource) (j : Fin 1) (b : Bool) :
    InjOn (sphereCutBand c j b) ((univ : Set ClosureSphere.{u}) ×ˢ Icc (0 : ℝ) (1 / 2)) := by
  intro p hp q hq h
  have hc := (c j).toOpenPartialHomeomorph.injOn
    (sphereCutBand_source c hs j b p hp) (sphereCutBand_source c hs j b q hq)
    (congrArg Prod.fst h)
  have ht := congrArg Prod.fst hc
  refine Prod.ext ht ?_
  have hz := congrArg Prod.snd hc
  cases b <;> simpa only [sphereCutSign, Bool.false_eq_true, ↓reduceIte, neg_inj] using hz

def sphereCutCompactBand (c : SphereCutSignedCollars W) (a : Fin 1 × Bool) :
    Set (W.Carrier × (Fin 1 → ℝ)) :=
  sphereCutBand c a.1 a.2 '' ((univ : Set ClosureSphere.{u}) ×ˢ Icc (0 : ℝ) (1 / 2))

theorem sphereCutCompactBand_compact (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource) (a : Fin 1 × Bool) :
    IsCompact (sphereCutCompactBand c a) :=
  (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
    (sphereCutBand_continuousOn c hs a.1 a.2)

theorem sphereCutCompactBand_disjoint (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) :
    Pairwise fun a a' : Fin 1 × Bool =>
      Disjoint (sphereCutCompactBand c a) (sphereCutCompactBand c a') := by
  intro a a' hne
  apply disjoint_left.mpr
  intro x hx hx'
  obtain ⟨p, hp, hpx⟩ := hx
  obtain ⟨q, hq, hqx⟩ := hx'
  have he : sphereCutBand c a.1 a.2 p = sphereCutBand c a'.1 a'.2 q := hpx.trans hqx.symm
  have hbase := congrArg Prod.fst he
  change c a.1 (p.1, sphereCutSign a.2 p.2) =
    c a'.1 (q.1, sphereCutSign a'.2 q.2) at hbase
  have hpS := sphereCutBand_source c hs a.1 a.2 p hp
  have hqS := sphereCutBand_source c hs a'.1 a'.2 q hq
  by_cases hj : a.1 = a'.1
  · obtain ⟨j, b⟩ := a
    obtain ⟨j', b'⟩ := a'
    dsimp only at hj hbase hpS hqS
    subst j'
    have hb : b ≠ b' := fun h => hne (Prod.ext rfl h)
    have hcoord := congrArg Prod.snd ((c j).toOpenPartialHomeomorph.injOn hpS hqS hbase)
    have hz : p.2 = 0 ∧ q.2 = 0 := by
      cases b <;> cases b' <;> try exact (hb rfl).elim
      all_goals
        simp only [sphereCutSign, Bool.false_eq_true, ↓reduceIte] at hcoord
        constructor <;> linarith [hp.2.1, hq.2.1]
    have htag := congrArg (fun y : W.Carrier × (Fin 1 → ℝ) => y.2 j) he
    have hcut : seamCut 0 = 0 := seamCut_of_le (by norm_num)
    cases b <;> cases b' <;> try exact (hb rfl).elim
    all_goals
      simp [sphereCutBand, sphereCutTag, sphereCutSign, hz.1, hz.2, hcut] at htag
      norm_num at htag
  · have ht : c a.1 (p.1, sphereCutSign a.2 p.2) ∈ (c a'.1).target :=
      by rw [hbase]; exact (c a'.1).map_source hqS
    exact disjoint_left.mp (hd hj) ((c a.1).map_source hpS) ht

theorem sphereCutBand_exterior_height (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target)
    (j : Fin 1) (b : Bool) (p : ClosureSphere.{u} × ℝ)
    (hp : p ∈ (univ : Set ClosureSphere.{u}) ×ˢ Icc (0 : ℝ) (1 / 2))
    (hout : (sphereCutBand c j b p).1 ∈ sphereCutOutside c) : p.2 = 1 / 2 := by
  have hn := (sphereCutOutside_coordinate c hs hd j _
    (sphereCutBand_source c hs j b p hp)).mp hout
  cases b <;> simp only [sphereCutSign, Bool.false_eq_true, ↓reduceIte] at hn
  all_goals
    by_contra hne
    have hlt := lt_of_le_of_ne hp.2.2 hne
    apply hn
    constructor <;> linarith [hp.2.1, hlt]

def sphereCutBandRest (c : SphereCutSignedCollars W) (a : Fin 1 × Bool) :
    Set (W.Carrier × (Fin 1 → ℝ)) :=
  (fun x : W.Carrier => (x, (0 : Fin 1 → ℝ))) '' sphereCutOutside c ∪
    ⋃ a' : Fin 1 × Bool, sphereCutBand c a'.1 a'.2 ''
      ((univ : Set ClosureSphere.{u}) ×ˢ if a' = a then Icc (1 / 4 : ℝ) (1 / 2)
        else Icc (0 : ℝ) (1 / 2))

theorem sphereCutBandRest_compact (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource) (a : Fin 1 × Bool) :
    IsCompact (sphereCutBandRest c a) := by
  apply IsCompact.union
  · exact (sphereCutOutside_closed c hs).isCompact.image
      (continuous_id.prodMk continuous_const)
  · apply isCompact_iUnion
    intro a'
    by_cases ha : a' = a
    · simp only [ha, ↓reduceIte]
      apply (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
      apply (sphereCutBand_continuousOn c hs a.1 a.2).mono
      intro p hp
      exact ⟨mem_univ _, by linarith [hp.2.1], hp.2.2⟩
    · simp only [ha, ↓reduceIte]
      exact (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
        (sphereCutBand_continuousOn c hs a'.1 a'.2)

theorem sphereCutSmallBand_disjoint_rest (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) (a : Fin 1 × Bool) :
    Disjoint (sphereCutBand c a.1 a.2 ''
      ((univ : Set ClosureSphere.{u}) ×ˢ Ico (0 : ℝ) (1 / 4))) (sphereCutBandRest c a) := by
  apply disjoint_left.mpr
  intro x hx hr
  obtain ⟨p, hp, hpx⟩ := hx
  have hpB : p ∈ (univ : Set ClosureSphere.{u}) ×ˢ Icc (0 : ℝ) (1 / 2) :=
    ⟨mem_univ _, hp.2.1, by linarith [hp.2.2]⟩
  rcases hr with hout | hr
  · obtain ⟨q, hq, hqx⟩ := hout
    have hbase : (sphereCutBand c a.1 a.2 p).1 = q :=
      congrArg Prod.fst (hpx.trans hqx.symm)
    have hpH := sphereCutBand_exterior_height c hs hd a.1 a.2 p hpB (hbase ▸ hq)
    linarith [hp.2.2]
  · obtain ⟨a', q, hq, hqx⟩ := mem_iUnion.mp hr
    by_cases ha : a' = a
    · subst a'
      simp only [↓reduceIte] at hq
      have hqB : q ∈ (univ : Set ClosureSphere.{u}) ×ˢ Icc (0 : ℝ) (1 / 2) :=
        ⟨mem_univ _, by linarith [hq.2.1], hq.2.2⟩
      have hqp := sphereCutBand_injOn c hs a.1 a.2 hpB hqB (hpx.trans hqx.symm)
      rw [← hqp] at hq
      linarith [hp.2.2, hq.2.1]
    · simp only [ha, ↓reduceIte] at hq
      exact disjoint_left.mp (sphereCutCompactBand_disjoint c hs hd (Ne.symm ha))
        ⟨p, hpB, hpx⟩ ⟨q, hq, hqx⟩

theorem sphereCutSet_diff_rest (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) (a : Fin 1 × Bool) :
    sphereCutSet c \ sphereCutBandRest c a = sphereCutBand c a.1 a.2 ''
      ((univ : Set ClosureSphere.{u}) ×ˢ Ico (0 : ℝ) (1 / 4)) := by
  ext x
  constructor
  · rintro ⟨hx, hn⟩
    rcases hx with hx | hx
    · exact (hn (Or.inl hx)).elim
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      obtain ⟨b, p, hp, hpx⟩ := mem_iUnion.mp hj
      have ha : (j, b) = a := by
        by_contra hne
        apply hn
        refine Or.inr (mem_iUnion.mpr ⟨(j, b), p, ?_, hpx⟩)
        simpa only [hne, ↓reduceIte] using hp
      cases ha
      have hlt : p.2 < 1 / 4 := by
        by_contra hnot
        apply hn
        refine Or.inr (mem_iUnion.mpr ⟨(j, b), p, ?_, hpx⟩)
        simpa only [↓reduceIte] using
          (show p ∈ (univ : Set ClosureSphere.{u}) ×ˢ Icc (1 / 4 : ℝ) (1 / 2) from
            ⟨mem_univ _, le_of_not_gt hnot, hp.2.2⟩)
      exact ⟨p, ⟨mem_univ _, hp.2.1, hlt⟩, hpx⟩
  · intro hx
    refine ⟨?_, fun h => disjoint_left.mp (sphereCutSmallBand_disjoint_rest c hs hd a) hx h⟩
    obtain ⟨p, hp, hpx⟩ := hx
    exact Or.inr (mem_iUnion.mpr ⟨a.1, mem_iUnion.mpr ⟨a.2, p,
      ⟨mem_univ _, hp.2.1, by linarith [hp.2.2]⟩, hpx⟩⟩)

theorem sphereCutSmallBand_open (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) (a : Fin 1 × Bool) :
    IsOpen ((Subtype.val : SphereCutSpace c → W.Carrier × (Fin 1 → ℝ)) ⁻¹'
      (sphereCutBand c a.1 a.2 '' ((univ : Set ClosureSphere.{u}) ×ˢ Ico (0 : ℝ) (1 / 4)))) := by
  have he : (Subtype.val : SphereCutSpace c → W.Carrier × (Fin 1 → ℝ)) ⁻¹'
      (sphereCutBand c a.1 a.2 '' ((univ : Set ClosureSphere.{u}) ×ˢ Ico (0 : ℝ) (1 / 4))) =
      (Subtype.val : SphereCutSpace c → W.Carrier × (Fin 1 → ℝ)) ⁻¹'
        (sphereCutBandRest c a)ᶜ := by
    ext x
    have hx := x.property
    rw [← sphereCutSet_diff_rest c hs hd a]
    exact (and_iff_right hx)
  rw [he]
  exact (sphereCutBandRest_compact c hs a).isClosed.isOpen_compl.preimage
    continuous_subtype_val


abbrev SphereCutHalfBand := ClosureSphere.{u} × Icc (0 : ℝ) (1 / 2)

def sphereCutClosedHalf (c : SphereCutSignedCollars W) (j : Fin 1) (b : Bool)
    (p : SphereCutHalfBand) : SphereCutSpace c :=
  ⟨sphereCutBand c j b (p.1, p.2.val), Or.inr (mem_iUnion.mpr ⟨j,
    mem_iUnion.mpr ⟨b, (p.1, p.2.val), ⟨mem_univ _, p.2.property⟩, rfl⟩⟩)⟩

theorem sphereCutClosedHalf_continuous (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource) (j : Fin 1) (b : Bool) :
    Continuous (sphereCutClosedHalf c j b) := by
  apply Continuous.subtype_mk
  apply (sphereCutBand_continuousOn c hs j b).comp_continuous
    (continuous_fst.prodMk continuous_snd.subtype_val)
  intro p
  exact ⟨mem_univ _, p.2.property⟩

theorem sphereCutClosedHalf_injective (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource) (j : Fin 1) (b : Bool) :
    Function.Injective (sphereCutClosedHalf c j b) := by
  intro p q h
  have hp : (p.1, p.2.val) ∈ (univ : Set ClosureSphere.{u}) ×ˢ Icc (0 : ℝ) (1 / 2) :=
    ⟨mem_univ _, p.2.property⟩
  have hq : (q.1, q.2.val) ∈ (univ : Set ClosureSphere.{u}) ×ˢ Icc (0 : ℝ) (1 / 2) :=
    ⟨mem_univ _, q.2.property⟩
  have hh := sphereCutBand_injOn c hs j b hp hq (congrArg Subtype.val h)
  have ht := congrArg Prod.fst hh
  have hr := congrArg Prod.snd hh
  exact Prod.ext ht (Subtype.ext hr)

theorem sphereCutClosedHalf_isClosedEmbedding (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource) (j : Fin 1) (b : Bool) :
    _root_.Topology.IsClosedEmbedding (sphereCutClosedHalf c j b) :=
  (sphereCutClosedHalf_continuous c hs j b).isClosedEmbedding
    (sphereCutClosedHalf_injective c hs j b)

def sphereCutSmallHalf : Set SphereCutHalfBand := {p | p.2.val < 1 / 4}

theorem sphereCutSmallHalf_open : IsOpen sphereCutSmallHalf :=
  isOpen_lt continuous_snd.subtype_val continuous_const

theorem sphereCutClosedHalf_image_small (c : SphereCutSignedCollars W)
    (j : Fin 1) (b : Bool) :
    sphereCutClosedHalf c j b '' sphereCutSmallHalf =
      (Subtype.val : SphereCutSpace c → W.Carrier × (Fin 1 → ℝ)) ⁻¹'
        (sphereCutBand c j b '' ((univ : Set ClosureSphere.{u}) ×ˢ Ico (0 : ℝ) (1 / 4))) := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨(p.1, p.2.val), ⟨mem_univ _, p.2.property.1, hp⟩, rfl⟩
  · rintro ⟨p, hp, hpx⟩
    let q : SphereCutHalfBand := (p.1, ⟨p.2, hp.2.1, by linarith [hp.2.2]⟩)
    exact ⟨q, hp.2.2, Subtype.ext hpx⟩

def sphereCutSmallHalfMap (c : SphereCutSignedCollars W) (j : Fin 1) (b : Bool) :
    sphereCutSmallHalf → SphereCutSpace c := fun p => sphereCutClosedHalf c j b p.val

theorem sphereCutSmallHalfMap_openEmbedding (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) (j : Fin 1) (b : Bool) :
    _root_.Topology.IsOpenEmbedding (sphereCutSmallHalfMap c j b) := by
  refine ⟨(sphereCutClosedHalf_isClosedEmbedding c hs j b).isEmbedding.comp
    _root_.Topology.IsEmbedding.subtypeVal, ?_⟩
  have hr : range (sphereCutSmallHalfMap c j b) =
      sphereCutClosedHalf c j b '' sphereCutSmallHalf := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p.val, p.property, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p, hp⟩, rfl⟩
  rw [hr, sphereCutClosedHalf_image_small]
  exact sphereCutSmallBand_open c hs hd (j, b)


def sphereCutAmbientZero (c : SphereCutSignedCollars W) : Set W.Carrier :=
  ⋃ j, range (fun t : ClosureSphere.{u} => c j (t, 0))

theorem sphereCutAmbientZero_closed (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource) : IsClosed (sphereCutAmbientZero c) := by
  apply isClosed_iUnion_of_finite
  intro j
  have hc : Continuous (fun t : ClosureSphere.{u} => c j (t, 0)) := by
    simpa only [Function.comp_def, sphereCutZero_fold] using
      (sphereCutFold_continuous c).comp (sphereCutZero_continuous c hs j false)
  exact (isCompact_range hc).isClosed

def sphereCutOffZero (c : SphereCutSignedCollars W) : Set (SphereCutSpace c) :=
  sphereCutFold c ⁻¹' (sphereCutAmbientZero c)ᶜ

theorem sphereCutOffZero_open (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource) : IsOpen (sphereCutOffZero c) :=
  (sphereCutAmbientZero_closed c hs).isOpen_compl.preimage (sphereCutFold_continuous c)

theorem sphereCutBand_eq_of_fold_eq_offZero (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target)
    (j k : Fin 1) (b d : Bool) (p q : ClosureSphere.{u} × ℝ)
    (hp : p ∈ (univ : Set ClosureSphere.{u}) ×ˢ Icc (0 : ℝ) (1 / 2))
    (hq : q ∈ (univ : Set ClosureSphere.{u}) ×ˢ Icc (0 : ℝ) (1 / 2))
    (he : (sphereCutBand c j b p).1 = (sphereCutBand c k d q).1)
    (hz : (sphereCutBand c j b p).1 ∉ sphereCutAmbientZero c) :
    sphereCutBand c j b p = sphereCutBand c k d q := by
  have hpS := sphereCutBand_source c hs j b p hp
  have hqS := sphereCutBand_source c hs k d q hq
  change c j (p.1, sphereCutSign b p.2) = c k (q.1, sphereCutSign d q.2) at he
  have hj : j = k := by
    by_contra hn
    exact disjoint_left.mp (hd hn) ((c j).map_source hpS)
      (he ▸ (c k).map_source hqS)
  subst k
  have hcoord := (c j).toOpenPartialHomeomorph.injOn hpS hqS he
  have ht := congrArg Prod.fst hcoord
  have hr := congrArg Prod.snd hcoord
  by_cases hb : b = d
  · subst d
    have hpq : p = q := by
      apply Prod.ext (show p.1 = q.1 from ht)
      cases b <;> simpa only [sphereCutSign, Bool.false_eq_true, ↓reduceIte, neg_inj] using hr
    exact congrArg (sphereCutBand c j b) hpq
  · have hp0 : p.2 = 0 := by
      cases b <;> cases d <;> try exact (hb rfl).elim
      all_goals
        simp only [sphereCutSign, Bool.false_eq_true, ↓reduceIte] at hr
        linarith [hp.2.1, hq.2.1]
    apply (hz ?_).elim
    refine mem_iUnion.mpr ⟨j, p.1, ?_⟩
    cases b <;> simp [sphereCutBand, sphereCutSign, hp0]

theorem sphereCutFold_injOn_offZero (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) :
    InjOn (sphereCutFold c) (sphereCutOffZero c) := by
  intro x hx y hy he
  apply Subtype.ext
  have hx0 : x.val.1 ∉ sphereCutAmbientZero c := hx
  have hxy : x.val.1 = y.val.1 := he
  rcases x.property with hxE | hxB
  · obtain ⟨a, ha, hax⟩ := hxE
    rcases y.property with hyE | hyB
    · obtain ⟨a', ha', hay⟩ := hyE
      rw [← hax, ← hay] at hxy ⊢
      exact Prod.ext hxy rfl
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hyB
      obtain ⟨b, p, hp, hpy⟩ := mem_iUnion.mp hj
      have hpE : (sphereCutBand c j b p).1 ∈ sphereCutOutside c := by
        rw [hpy, ← hxy, ← hax]
        exact ha
      have hpH := sphereCutBand_exterior_height c hs hd j b p hp hpE
      rw [← hax, ← hpy] at hxy ⊢
      apply Prod.ext hxy
      exact (sphereCutTag_zero_of_ge j b (by linarith [hpH])).symm
  · obtain ⟨j, hj⟩ := mem_iUnion.mp hxB
    obtain ⟨b, p, hp, hpx⟩ := mem_iUnion.mp hj
    rcases y.property with hyE | hyB
    · obtain ⟨a, ha, hay⟩ := hyE
      have hpE : (sphereCutBand c j b p).1 ∈ sphereCutOutside c := by
        rw [hpx, hxy, ← hay]
        exact ha
      have hpH := sphereCutBand_exterior_height c hs hd j b p hp hpE
      rw [← hpx, ← hay] at hxy ⊢
      apply Prod.ext hxy
      exact sphereCutTag_zero_of_ge j b (by linarith [hpH])
    · obtain ⟨k, hk⟩ := mem_iUnion.mp hyB
      obtain ⟨d, q, hq, hqy⟩ := mem_iUnion.mp hk
      rw [← hpx, ← hqy] at hxy ⊢
      exact sphereCutBand_eq_of_fold_eq_offZero c hs hd j k b d p q hp hq hxy
        (by simpa only [hpx] using hx0)

def sphereCutOffZeroHomeomorph (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) :
    sphereCutOffZero c ≃ₜ {x : W.Carrier // x ∉ sphereCutAmbientZero c} := by
  let : CompactSpace (SphereCutSpace c) := sphereCutCompactSpace c hs
  let f := ((sphereCutAmbientZero c)ᶜ).restrictPreimage (sphereCutFold c)
  have hi : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact sphereCutFold_injOn_offZero c hs hd x.property y.property (congrArg Subtype.val h)
  have hb : Function.Bijective f :=
    ⟨hi, (sphereCut_projection_surjective c).restrictPreimage _⟩
  exact (Equiv.ofBijective f hb).toHomeomorphOfContinuousClosed
    (sphereCutFold_continuous c).restrictPreimage
    ((sphereCutFold_continuous c).isClosedMap.restrictPreimage _)


def sphereCutHalfPatchSource : Set (ClosureSphere.{u} × EuclideanHalfSpace 1) :=
  {p | p.2.val 0 < 1 / 4}

theorem sphereCutHalfPatchSource_open : IsOpen sphereCutHalfPatchSource :=
  isOpen_lt (contMDiff_halfSpaceOneCoordinate.continuous.comp continuous_snd) continuous_const

def sphereCutSmallHalfHomeomorph :
    sphereCutHalfPatchSource ≃ₜ sphereCutSmallHalf :=
  { toFun p := ⟨(p.val.1, ⟨p.val.2.val 0, p.val.2.property, by
        have hp : p.val.2.val 0 < 1 / 4 := p.property
        linarith [hp]⟩),
      p.property⟩
    invFun p := ⟨(p.val.1, halfSpaceOneHomeomorph.symm ⟨p.val.2.val, p.val.2.property.1⟩),
      by
        change (halfSpaceOneHomeomorph (halfSpaceOneHomeomorph.symm _)).val < 1 / 4
        rw [Homeomorph.apply_symm_apply]
        exact p.property⟩
    left_inv p := by
      apply Subtype.ext
      change (p.val.1, halfSpaceOneHomeomorph.symm
        ⟨p.val.2.val 0, p.val.2.property⟩) = p.val
      exact congrArg (fun h : EuclideanHalfSpace 1 => (p.val.1, h))
        (halfSpaceOneHomeomorph.symm_apply_apply p.val.2)
    right_inv p := by
      apply Subtype.ext
      apply Prod.ext rfl
      apply Subtype.ext
      rfl
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact (continuous_subtype_val.fst).prodMk
        ((contMDiff_halfSpaceOneCoordinate.continuous.comp
          continuous_subtype_val.snd).subtype_mk _)
    continuous_invFun := by
      apply Continuous.subtype_mk
      exact (continuous_subtype_val.fst).prodMk
        (halfSpaceOneHomeomorph.symm.continuous.comp
          (continuous_subtype_val.snd.subtype_val.subtype_mk _)) }

def sphereCutHalfPatchMap (c : SphereCutSignedCollars W) (j : Fin 1) (b : Bool) :
    sphereCutHalfPatchSource → SphereCutSpace c :=
  sphereCutSmallHalfMap c j b ∘ sphereCutSmallHalfHomeomorph

theorem sphereCutHalfPatchMap_openEmbedding (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) (j : Fin 1) (b : Bool) :
    _root_.Topology.IsOpenEmbedding (sphereCutHalfPatchMap c j b) :=
  (sphereCutSmallHalfMap_openEmbedding c hs hd j b).comp
    sphereCutSmallHalfHomeomorph.isOpenEmbedding

def sphereCutHalfPatch (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) (j : Fin 1) (b : Bool) :
    OpenPartialHomeomorph (ClosureSphere.{u} × EuclideanHalfSpace 1) (SphereCutSpace c) := by
  letI : Nonempty sphereCutHalfPatchSource :=
    ⟨⟨(Classical.arbitrary ClosureSphere.{u}, halfZero), by change (0 : ℝ) < 1 / 4; norm_num⟩⟩
  exact (sphereCutHalfPatchSource_open.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph
    (Subtype.val : sphereCutHalfPatchSource → ClosureSphere.{u} × EuclideanHalfSpace 1)).symm.trans
    ((sphereCutHalfPatchMap_openEmbedding c hs hd j b).toOpenPartialHomeomorph
      (sphereCutHalfPatchMap c j b))


theorem sphereCutHalfPatch_source (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) (j : Fin 1) (b : Bool) :
    (sphereCutHalfPatch c hs hd j b).source = sphereCutHalfPatchSource := by
  simp [sphereCutHalfPatch]

theorem sphereCutHalfPatch_apply (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) (j : Fin 1) (b : Bool)
    (p : ClosureSphere.{u} × EuclideanHalfSpace 1) (hp : p ∈ sphereCutHalfPatchSource) :
    (sphereCutHalfPatch c hs hd j b p).val = sphereCutBand c j b (p.1, p.2.val 0) := by
  let : Nonempty sphereCutHalfPatchSource :=
    ⟨⟨(Classical.arbitrary ClosureSphere.{u}, halfZero), by change (0 : ℝ) < 1 / 4; norm_num⟩⟩
  let G := sphereCutHalfPatchSource_open.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph
    (Subtype.val : sphereCutHalfPatchSource → ClosureSphere.{u} × EuclideanHalfSpace 1)
  have hg : G.symm p = (⟨p, hp⟩ : sphereCutHalfPatchSource) := by
    simpa only [G, _root_.Topology.IsOpenEmbedding.toOpenPartialHomeomorph_apply] using
      G.left_inv (x := (⟨p, hp⟩ : sphereCutHalfPatchSource)) (mem_univ _)
  change (sphereCutHalfPatchMap c j b (G.symm p)).val = _
  rw [hg]
  rfl


theorem sphereCutHalfPatch_target (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) (j : Fin 1) (b : Bool) :
    (sphereCutHalfPatch c hs hd j b).target =
      (Subtype.val : SphereCutSpace c → W.Carrier × (Fin 1 → ℝ)) ⁻¹'
        (sphereCutBand c j b '' ((univ : Set ClosureSphere.{u}) ×ˢ Ico (0 : ℝ) (1 / 4))) := by
  let e := sphereCutHalfPatch c hs hd j b
  ext x
  constructor
  · intro hx
    let p := e.symm x
    have hp : p ∈ sphereCutHalfPatchSource := by
      rw [← sphereCutHalfPatch_source c hs hd j b]
      exact e.map_target hx
    refine ⟨(p.1, p.2.val 0), ⟨mem_univ _, p.2.property, hp⟩, ?_⟩
    rw [← sphereCutHalfPatch_apply c hs hd j b p hp]
    exact congrArg Subtype.val (e.right_inv hx)
  · rintro ⟨p, hp, hpx⟩
    let q : ClosureSphere.{u} × EuclideanHalfSpace 1 := (p.1, halfPoint p.2 hp.2.1)
    have hq : q ∈ e.source := by
      rw [sphereCutHalfPatch_source]
      exact hp.2.2
    have he : e q = x := by
      apply Subtype.ext
      rw [sphereCutHalfPatch_apply c hs hd j b q hp.2.2]
      exact hpx
    exact he ▸ e.map_source hq


theorem sphereCutSignedPoint_not_zero (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target)
    (j : Fin 1) (p : ClosureSphere.{u} × ℝ) (hp : p ∈ (c j).source) (hp0 : p.2 ≠ 0) :
    c j p ∉ sphereCutAmbientZero c := by
  intro hz
  obtain ⟨k, t, ht⟩ := mem_iUnion.mp hz
  have htS : (t, (0 : ℝ)) ∈ (c k).source := by
    rw [hs k]
    simp only [sphereSignedCollarSource, mem_prod, mem_univ, true_and]
    change -1 < (0 : ℝ) ∧ (0 : ℝ) < 1
    norm_num
  by_cases hj : j = k
  · subst k
    have he := (c j).toOpenPartialHomeomorph.injOn hp htS ht.symm
    exact hp0 (congrArg Prod.snd he)
  · exact disjoint_left.mp (hd hj) ((c j).map_source hp)
      (ht ▸ (c k).map_source htS)

theorem sphereCutAmbientOffZero_nonempty (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) :
    Nonempty {x : W.Carrier // x ∉ sphereCutAmbientZero c} := by
  classical
  let j : Fin 1 := 0
  let p : ClosureSphere.{u} × ℝ := (Classical.arbitrary ClosureSphere.{u}, 1 / 8)
  have hp : p ∈ (c j).source := by
    rw [hs j]
    simp only [sphereSignedCollarSource, mem_prod, mem_univ, true_and]
    change -1 < (1 / 8 : ℝ) ∧ (1 / 8 : ℝ) < 1
    norm_num
  exact ⟨⟨c j p, sphereCutSignedPoint_not_zero c hs hd j p hp (by norm_num [p])⟩⟩

def sphereCutAmbientPatchMap (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) :
    {x : W.Carrier // x ∉ sphereCutAmbientZero c} → SphereCutSpace c :=
  Subtype.val ∘ (sphereCutOffZeroHomeomorph c hs hd).symm

theorem sphereCutAmbientPatchMap_openEmbedding (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) :
    _root_.Topology.IsOpenEmbedding (sphereCutAmbientPatchMap c hs hd) :=
  (sphereCutOffZero_open c hs).isOpenEmbedding_subtypeVal.comp
    (sphereCutOffZeroHomeomorph c hs hd).symm.isOpenEmbedding

def sphereCutAmbientPatch (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) :
    OpenPartialHomeomorph W.Carrier (SphereCutSpace c) := by
  letI := sphereCutAmbientOffZero_nonempty c hs hd
  let h := (sphereCutAmbientZero_closed c hs).isOpen_compl.isOpenEmbedding_subtypeVal
  exact (h.toOpenPartialHomeomorph
      (Subtype.val : {x : W.Carrier // x ∉ sphereCutAmbientZero c} → W.Carrier)).symm.trans
    ((sphereCutAmbientPatchMap_openEmbedding c hs hd).toOpenPartialHomeomorph
      (sphereCutAmbientPatchMap c hs hd))


theorem sphereCutAmbientPatch_source (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) :
    (sphereCutAmbientPatch c hs hd).source = (sphereCutAmbientZero c)ᶜ := by
  simp [sphereCutAmbientPatch]
  rfl

theorem sphereCutAmbientPatch_target (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) :
    (sphereCutAmbientPatch c hs hd).target = sphereCutOffZero c := by
  simp [sphereCutAmbientPatch, sphereCutAmbientPatchMap, range_comp]

theorem sphereCutAmbientPatchMap_fold (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target)
    (p : {x : W.Carrier // x ∉ sphereCutAmbientZero c}) :
    sphereCutFold c (sphereCutAmbientPatchMap c hs hd p) = p.val :=
  congrArg Subtype.val ((sphereCutOffZeroHomeomorph c hs hd).apply_symm_apply p)

theorem sphereCutAmbientPatch_fold (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target)
    (p : W.Carrier) (hp : p ∉ sphereCutAmbientZero c) :
    sphereCutFold c (sphereCutAmbientPatch c hs hd p) = p := by
  let := sphereCutAmbientOffZero_nonempty c hs hd
  let h := (sphereCutAmbientZero_closed c hs).isOpen_compl.isOpenEmbedding_subtypeVal
  let G := h.toOpenPartialHomeomorph
      (Subtype.val : {x : W.Carrier // x ∉ sphereCutAmbientZero c} → W.Carrier)
  have hg : G.symm p = (⟨p, hp⟩ : {x : W.Carrier // x ∉ sphereCutAmbientZero c}) := by
    simpa only [G, _root_.Topology.IsOpenEmbedding.toOpenPartialHomeomorph_apply] using
      G.left_inv (x := (⟨p, hp⟩ : {x : W.Carrier // x ∉ sphereCutAmbientZero c})) (mem_univ _)
  change sphereCutFold c (sphereCutAmbientPatchMap c hs hd (G.symm p)) = p
  rw [hg]
  exact sphereCutAmbientPatchMap_fold c hs hd _

theorem sphereCutPatches_cover (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) (x : SphereCutSpace c) :
    x ∈ (sphereCutAmbientPatch c hs hd).target ∨
      ∃ j b, x ∈ (sphereCutHalfPatch c hs hd j b).target := by
  rcases x.property with hxE | hxB
  · left
    rw [sphereCutAmbientPatch_target]
    change x.val.1 ∉ sphereCutAmbientZero c
    obtain ⟨a, ha, hax⟩ := hxE
    rintro hz
    obtain ⟨j, t, ht⟩ := mem_iUnion.mp hz
    have hp : (t, (0 : ℝ)) ∈ (c j).source := by
      rw [hs j]
      simp only [sphereSignedCollarSource, mem_prod, mem_univ, true_and]
      change -1 < (0 : ℝ) ∧ (0 : ℝ) < 1
      norm_num
    change c j (t, 0) = x.val.1 at ht
    have hout : c j (t, 0) ∈ sphereCutOutside c := by
      rw [ht, ← hax]
      exact ha
    have hn := (sphereCutOutside_coordinate c hs hd j _ hp).mp hout
    exact hn (by norm_num)
  · obtain ⟨j, hj⟩ := mem_iUnion.mp hxB
    obtain ⟨b, p, hp, hpx⟩ := mem_iUnion.mp hj
    by_cases hsmall : p.2 < 1 / 4
    · right
      refine ⟨j, b, ?_⟩
      rw [sphereCutHalfPatch_target]
      exact ⟨p, ⟨mem_univ _, hp.2.1, hsmall⟩, hpx⟩
    · left
      rw [sphereCutAmbientPatch_target]
      change x.val.1 ∉ sphereCutAmbientZero c
      rw [← hpx]
      apply sphereCutSignedPoint_not_zero c hs hd j _
        (sphereCutBand_source c hs j b p hp)
      have hp0 : 0 < p.2 := by linarith [le_of_not_gt hsmall]
      cases b <;> simp only [sphereCutSign, Bool.false_eq_true, ↓reduceIte]
      · exact ne_of_gt hp0
      · exact neg_ne_zero.mpr (ne_of_gt hp0)



def sphereCutHalfSigned (b : Bool) (p :
    ClosureSphere.{u} × EuclideanHalfSpace 1) : ClosureSphere.{u} × ℝ :=
  (p.1, sphereCutSign b (p.2.val 0))

def sphereCutSignedHalf (b : Bool) (p :
    ClosureSphere.{u} × ℝ) : ClosureSphere.{u} × EuclideanHalfSpace 1 :=
  (p.1, halfSpaceOneLift (sphereCutSign b p.2))

theorem sphereCutSign_involutive (b : Bool) (s : ℝ) :
    sphereCutSign b (sphereCutSign b s) = s := by
  cases b <;> simp [sphereCutSign]

theorem sphereCutHalfSigned_smooth (b : Bool) :
    ContMDiff sphereHalfCollarModel sphereSignedCollarModel ∞ (sphereCutHalfSigned.{u} b) := by
  have h : ContMDiff sphereHalfCollarModel 𝓘(ℝ) ∞
      (fun p : ClosureSphere.{u} × EuclideanHalfSpace 1 => p.2.val 0) :=
    contMDiff_halfSpaceOneCoordinate.comp contMDiff_snd
  cases b
  · exact contMDiff_fst.prodMk h
  · exact contMDiff_fst.prodMk h.neg

theorem sphereCutHalfSigned_source (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource) (j : Fin 1) (b : Bool)
    (p : ClosureSphere.{u} × EuclideanHalfSpace 1) (hp : p ∈ sphereCutHalfPatchSource) :
    sphereCutHalfSigned b p ∈ (c j).source :=
  sphereCutBand_source c hs j b (p.1, p.2.val 0)
    ⟨mem_univ _, p.2.property, by have h : p.2.val 0 < 1 / 4 := hp; linarith [h]⟩

theorem sphereCutAmbientPatch_symm (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target)
    (x : SphereCutSpace c) (hx : x ∈ (sphereCutAmbientPatch c hs hd).target) :
    (sphereCutAmbientPatch c hs hd).symm x = sphereCutFold c x := by
  let e := sphereCutAmbientPatch c hs hd
  have hp : e.symm x ∉ sphereCutAmbientZero c := by
    change e.symm x ∈ (sphereCutAmbientZero c)ᶜ
    rw [← sphereCutAmbientPatch_source c hs hd]
    exact e.map_target hx
  have he := sphereCutAmbientPatch_fold c hs hd (e.symm x) hp
  rw [e.right_inv hx] at he
  exact he.symm

theorem sphereCutHalfPatch_symm_signed (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) (j : Fin 1) (b : Bool)
    (x : SphereCutSpace c) (hx : x ∈ (sphereCutHalfPatch c hs hd j b).target) :
    (c j).symm (sphereCutFold c x) =
      sphereCutHalfSigned b ((sphereCutHalfPatch c hs hd j b).symm x) := by
  let e := sphereCutHalfPatch c hs hd j b
  let p := e.symm x
  have hp : p ∈ sphereCutHalfPatchSource := by
    rw [← sphereCutHalfPatch_source c hs hd j b]
    exact e.map_target hx
  have he : sphereCutFold c x = c j (sphereCutHalfSigned b p) := by
    rw [← e.right_inv hx]
    exact congrArg Prod.fst (sphereCutHalfPatch_apply c hs hd j b p hp)
  rw [he]
  exact (c j).left_inv (sphereCutHalfSigned_source c hs j b p hp)

theorem sphereCutHalfSpaceLift_self (h : EuclideanHalfSpace 1) :
    halfSpaceOneLift (h.val 0) = h := by
  rw [halfSpaceOneLift_eq]
  have he : (⟨max 0 (h.val 0), le_max_left 0 (h.val 0)⟩ : Ici (0 : ℝ)) =
      halfSpaceOneHomeomorph h := Subtype.ext (max_eq_right h.property)
  rw [he]
  exact halfSpaceOneHomeomorph.symm_apply_apply h

theorem sphereCutSignedHalf_halfSigned (b : Bool) (p : ClosureSphere.{u} × EuclideanHalfSpace 1) :
    sphereCutSignedHalf b (sphereCutHalfSigned b p) = p := by
  change (p.1, halfSpaceOneLift (sphereCutSign b (sphereCutSign b (p.2.val 0)))) = p
  rw [sphereCutSign_involutive, sphereCutHalfSpaceLift_self]

theorem sphereCutHalfPatch_symm (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) (j : Fin 1) (b : Bool)
    (x : SphereCutSpace c) (hx : x ∈ (sphereCutHalfPatch c hs hd j b).target) :
    (sphereCutHalfPatch c hs hd j b).symm x =
      sphereCutSignedHalf b ((c j).symm (sphereCutFold c x)) := by
  rw [sphereCutHalfPatch_symm_signed c hs hd j b x hx, sphereCutSignedHalf_halfSigned]


theorem sphereCutHalf_to_ambient_smooth (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) (j : Fin 1) (b : Bool) :
    ContMDiffOn sphereHalfCollarModel W.model ∞
      ((sphereCutHalfPatch c hs hd j b).trans (sphereCutAmbientPatch c hs hd).symm)
      ((sphereCutHalfPatch c hs hd j b).trans (sphereCutAmbientPatch c hs hd).symm).source := by
  have hf : ContMDiffOn sphereHalfCollarModel W.model ∞
      (c j ∘ sphereCutHalfSigned b) sphereCutHalfPatchSource :=
    (c j).contMDiffOn.comp (sphereCutHalfSigned_smooth b).contMDiffOn
      (sphereCutHalfSigned_source c hs j b)
  apply (hf.mono ?_).congr
  · intro p hp
    change (sphereCutAmbientPatch c hs hd).symm (sphereCutHalfPatch c hs hd j b p) = _
    have hpt := hp.2
    change sphereCutHalfPatch c hs hd j b p ∈
      (sphereCutAmbientPatch c hs hd).target at hpt
    have hb := sphereCutAmbientPatch_symm c hs hd
      (sphereCutHalfPatch c hs hd j b p) hpt
    have hps : p ∈ sphereCutHalfPatchSource :=
      (sphereCutHalfPatch_source c hs hd j b).subset hp.1
    exact hb.trans (congrArg Prod.fst (sphereCutHalfPatch_apply c hs hd j b p hps))
  · intro p hp
    exact (sphereCutHalfPatch_source c hs hd j b).subset hp.1

theorem sphereCutHalfInverse_height_pos (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) (j : Fin 1) (b : Bool)
    (x : SphereCutSpace c) (hx : x ∈ (sphereCutHalfPatch c hs hd j b).target)
    (hz : sphereCutFold c x ∉ sphereCutAmbientZero c) :
    0 < sphereCutSign b ((c j).symm (sphereCutFold c x)).2 := by
  let q := (sphereCutHalfPatch c hs hd j b).symm x
  have he := sphereCutHalfPatch_symm_signed c hs hd j b x hx
  have hr : sphereCutSign b ((c j).symm (sphereCutFold c x)).2 = q.2.val 0 := by
    rw [he]
    exact sphereCutSign_involutive b _
  rw [hr]
  apply lt_of_le_of_ne q.2.property
  intro hq0
  have hqs : q ∈ sphereCutHalfPatchSource := by
    rw [← sphereCutHalfPatch_source c hs hd j b]
    exact (sphereCutHalfPatch c hs hd j b).map_target hx
  have hf : sphereCutFold c x = c j (sphereCutHalfSigned b q) := by
    rw [← (sphereCutHalfPatch c hs hd j b).right_inv hx]
    exact congrArg Prod.fst (sphereCutHalfPatch_apply c hs hd j b q hqs)
  apply hz
  refine mem_iUnion.mpr ⟨j, q.1, ?_⟩
  rw [hf]
  cases b <;> simp [sphereCutHalfSigned, sphereCutSign, ← hq0]


theorem sphereCutHalfPatch_fold_mem_target (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) (j : Fin 1) (b : Bool)
    (x : SphereCutSpace c) (hx : x ∈ (sphereCutHalfPatch c hs hd j b).target) :
    sphereCutFold c x ∈ (c j).target := by
  let e := sphereCutHalfPatch c hs hd j b
  let q := e.symm x
  have hq : q ∈ sphereCutHalfPatchSource :=
    (sphereCutHalfPatch_source c hs hd j b).subset (e.map_target hx)
  have hf : sphereCutFold c x = c j (sphereCutHalfSigned b q) := by
    rw [← e.right_inv hx]
    exact congrArg Prod.fst (sphereCutHalfPatch_apply c hs hd j b q hq)
  rw [hf]
  exact (c j).map_source (sphereCutHalfSigned_source c hs j b q hq)

theorem sphereCutAmbient_to_half_smooth (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) (j : Fin 1) (b : Bool) :
    ContMDiffOn W.model sphereHalfCollarModel ∞
      ((sphereCutAmbientPatch c hs hd).trans (sphereCutHalfPatch c hs hd j b).symm)
      ((sphereCutAmbientPatch c hs hd).trans (sphereCutHalfPatch c hs hd j b).symm).source := by
  intro p hp
  have hps : p ∉ sphereCutAmbientZero c :=
    (sphereCutAmbientPatch_source c hs hd).subset hp.1
  have hpt := hp.2
  change sphereCutAmbientPatch c hs hd p ∈
    (sphereCutHalfPatch c hs hd j b).target at hpt
  have hf := sphereCutAmbientPatch_fold c hs hd p hps
  have hcp : p ∈ (c j).target := by
    rw [← hf]
    exact sphereCutHalfPatch_fold_mem_target c hs hd j b _ hpt
  have hpos : 0 < sphereCutSign b ((c j).symm p).2 := by
    rw [← hf]
    exact sphereCutHalfInverse_height_pos c hs hd j b _ hpt (hf.symm ▸ hps)
  have hc := (c j).contMDiffOn_invFun.contMDiffAt ((c j).open_target.mem_nhds hcp)
  have hr : ContMDiffAt W.model 𝓘(ℝ) ∞
      (fun y => sphereCutSign b ((c j).symm y).2) p := by
    cases b
    · exact hc.snd
    · exact hc.snd.neg
  have hl : ContMDiffAt 𝓘(ℝ) (𝓡∂ 1) ∞ halfSpaceOneLift
      (sphereCutSign b ((c j).symm p).2) :=
    contMDiffOn_halfSpaceOneLift.contMDiffAt (Ici_mem_nhds hpos)
  have hg := hc.fst.prodMk (hl.comp p hr)
  apply (hg.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [((sphereCutAmbientPatch c hs hd).trans
    (sphereCutHalfPatch c hs hd j b).symm).open_source.mem_nhds hp] with y hy
  have hys : y ∉ sphereCutAmbientZero c :=
    (sphereCutAmbientPatch_source c hs hd).subset hy.1
  have hyt := hy.2
  change sphereCutAmbientPatch c hs hd y ∈
    (sphereCutHalfPatch c hs hd j b).target at hyt
  change (sphereCutHalfPatch c hs hd j b).symm (sphereCutAmbientPatch c hs hd y) = _
  rw [sphereCutHalfPatch_symm c hs hd j b _ hyt, sphereCutAmbientPatch_fold c hs hd y hys]
  rfl


theorem sphereCutHalfPatch_disjoint (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) :
    Pairwise fun a a' : Fin 1 × Bool =>
      Disjoint (sphereCutHalfPatch c hs hd a.1 a.2).target
        (sphereCutHalfPatch c hs hd a'.1 a'.2).target := by
  intro a a' hne
  apply disjoint_left.mpr
  intro x hx hx'
  rw [sphereCutHalfPatch_target] at hx hx'
  obtain ⟨p, hp, hpx⟩ := hx
  obtain ⟨q, hq, hqx⟩ := hx'
  exact disjoint_left.mp (sphereCutCompactBand_disjoint c hs hd hne)
    ⟨p, ⟨mem_univ _, hp.2.1, by linarith [hp.2.2]⟩, hpx⟩
    ⟨q, ⟨mem_univ _, hq.2.1, by linarith [hq.2.2]⟩, hqx⟩

theorem sphereCutHalf_to_half_smooth (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target)
    (a a' : Fin 1 × Bool) :
    ContMDiffOn sphereHalfCollarModel sphereHalfCollarModel ∞
      ((sphereCutHalfPatch c hs hd a.1 a.2).trans
        (sphereCutHalfPatch c hs hd a'.1 a'.2).symm)
      ((sphereCutHalfPatch c hs hd a.1 a.2).trans
        (sphereCutHalfPatch c hs hd a'.1 a'.2).symm).source := by
  by_cases ha : a = a'
  · subst a'
    apply contMDiffOn_id.congr
    intro p hp
    exact (sphereCutHalfPatch c hs hd a.1 a.2).left_inv hp.1
  · intro p hp
    have hpt := hp.2
    change sphereCutHalfPatch c hs hd a.1 a.2 p ∈
      (sphereCutHalfPatch c hs hd a'.1 a'.2).target at hpt
    exact (disjoint_left.mp (sphereCutHalfPatch_disjoint c hs hd ha)
      ((sphereCutHalfPatch c hs hd a.1 a.2).map_source hp.1) hpt).elim



attribute [local instance] uliftChartedSpace isManifold_ulift

section LiftTransitions

variable {E F H K M N M' N' Q : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace K]
  [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace M']
  [TopologicalSpace N'] [TopologicalSpace Q]
  [ChartedSpace H M] [ChartedSpace K N] [ChartedSpace H M'] [ChartedSpace K N']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}

private theorem contMDiffOn_sphereCutLiftedTransition
    (a : M' ≃ₘ⟮I, I⟯ M) (b : N' ≃ₘ⟮J, J⟯ N)
    (e : OpenPartialHomeomorph M Q) (f : OpenPartialHomeomorph N Q)
    (hf : ContMDiffOn I J ∞ (e.trans f.symm) (e.trans f.symm).source)
    (hb : ContMDiffOn J I ∞ (f.trans e.symm) (f.trans e.symm).source) :
    ContMDiffOn I J ∞
      ((a.toHomeomorph.toOpenPartialHomeomorph.trans e).trans
        (b.toHomeomorph.toOpenPartialHomeomorph.trans f).symm)
      ((a.toHomeomorph.toOpenPartialHomeomorph.trans e).trans
        (b.toHomeomorph.toOpenPartialHomeomorph.trans f).symm).source := by
  let t : PartialDiffeomorph I J M N ∞ :=
    { toPartialEquiv := (e.trans f.symm).toPartialEquiv
      open_source := (e.trans f.symm).open_source
      open_target := (e.trans f.symm).open_target
      contMDiffOn_toFun := hf
      contMDiffOn_invFun := hb }
  have h := ((a.toPartialDiffeomorph.trans t).trans b.symm.toPartialDiffeomorph).contMDiffOn
  change ContMDiffOn I J ∞
    ((a.toHomeomorph.toOpenPartialHomeomorph.trans (e.trans f.symm)).trans
      b.symm.toHomeomorph.toOpenPartialHomeomorph)
    ((a.toHomeomorph.toOpenPartialHomeomorph.trans (e.trans f.symm)).trans
      b.symm.toHomeomorph.toOpenPartialHomeomorph).source at h
  simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.trans_assoc, Diffeomorph.symm_toHomeomorph,
    Homeomorph.symm_toOpenPartialHomeomorph] using h

end LiftTransitions


abbrev SphereCutPatchIndex := Option (Fin 1 × Bool)

abbrev SphereCutPatchVector : SphereCutPatchIndex → Type
  | none => EuclideanSpace ℝ (Fin 3)
  | some _ => EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1)

abbrev SphereCutPatchModelSpace (W : CompactCarrier.{u}) : SphereCutPatchIndex → Type
  | none => W.kind.Space
  | some _ => ModelProd (EuclideanSpace ℝ (Fin 2)) (EuclideanHalfSpace 1)

abbrev SphereCutPatchSpace (W : CompactCarrier.{u}) :
    SphereCutPatchIndex → Type u
  | none => W.Carrier
  | some _ => ULift.{u} (ClosureSphere.{u} × EuclideanHalfSpace 1)

instance sphereCutPatchVectorNormed (i : SphereCutPatchIndex) :
    NormedAddCommGroup (SphereCutPatchVector i) := by
  cases i <;> exact inferInstance

instance sphereCutPatchVectorNormedSpace (i : SphereCutPatchIndex) :
    NormedSpace ℝ (SphereCutPatchVector i) := by
  cases i <;> exact inferInstance

instance sphereCutPatchModelTopology (i : SphereCutPatchIndex) :
    TopologicalSpace (SphereCutPatchModelSpace W i) := by
  cases i <;> exact inferInstance

instance sphereCutPatchTopology (i : SphereCutPatchIndex) :
    TopologicalSpace (SphereCutPatchSpace W i) := by
  cases i <;> exact inferInstance

instance sphereCutPatchChartedSpace (i : SphereCutPatchIndex) :
    ChartedSpace (SphereCutPatchModelSpace W i) (SphereCutPatchSpace W i) := by
  cases i
  · exact inferInstanceAs (ChartedSpace W.kind.Space W.Carrier)
  · exact uliftChartedSpace _ (ClosureSphere.{u} × EuclideanHalfSpace 1)

abbrev sphereCutPatchModel (W : CompactCarrier.{u}) (i : SphereCutPatchIndex) :
    ModelWithCorners ℝ (SphereCutPatchVector i) (SphereCutPatchModelSpace W i) := by
  cases i
  · exact W.model
  · exact sphereHalfCollarModel

def sphereCutPatch (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) :
    ∀ i : SphereCutPatchIndex,
      OpenPartialHomeomorph (SphereCutPatchSpace W i) (SphereCutSpace c) := by
  intro i
  cases i with
  | none => exact sphereCutAmbientPatch c hs hd
  | some a =>
      let l := (uliftDiffeomorph.{u, u} sphereHalfCollarModel
        (ClosureSphere.{u} × EuclideanHalfSpace 1)).symm
      exact l.toHomeomorph.toOpenPartialHomeomorph.trans (sphereCutHalfPatch c hs hd a.1 a.2)

theorem sphereCutPatch_compatible (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target)
    (i j : SphereCutPatchIndex) :
    ContMDiffOn (sphereCutPatchModel W i) (sphereCutPatchModel W j) ∞
      ((sphereCutPatch c hs hd i).trans (sphereCutPatch c hs hd j).symm)
      ((sphereCutPatch c hs hd i).trans (sphereCutPatch c hs hd j).symm).source := by
  cases i with
  | none =>
      cases j with
      | none =>
          apply contMDiffOn_id.congr
          intro p hp
          exact (sphereCutAmbientPatch c hs hd).left_inv hp.1
      | some a =>
          have h := contMDiffOn_sphereCutLiftedTransition
            (Diffeomorph.refl W.model W.Carrier ∞)
            (uliftDiffeomorph.{u, u} sphereHalfCollarModel
              (ClosureSphere.{u} × EuclideanHalfSpace 1)).symm
            (sphereCutAmbientPatch c hs hd) (sphereCutHalfPatch c hs hd a.1 a.2)
            (sphereCutAmbient_to_half_smooth c hs hd a.1 a.2)
            (sphereCutHalf_to_ambient_smooth c hs hd a.1 a.2)
          simpa [sphereCutPatch] using h
  | some a =>
      cases j with
      | none =>
          have h := contMDiffOn_sphereCutLiftedTransition
            (uliftDiffeomorph.{u, u} sphereHalfCollarModel
              (ClosureSphere.{u} × EuclideanHalfSpace 1)).symm
            (Diffeomorph.refl W.model W.Carrier ∞)
            (sphereCutHalfPatch c hs hd a.1 a.2) (sphereCutAmbientPatch c hs hd)
            (sphereCutHalf_to_ambient_smooth c hs hd a.1 a.2)
            (sphereCutAmbient_to_half_smooth c hs hd a.1 a.2)
          simpa [sphereCutPatch] using h
      | some a' =>
          exact contMDiffOn_sphereCutLiftedTransition
            (uliftDiffeomorph.{u, u} sphereHalfCollarModel
              (ClosureSphere.{u} × EuclideanHalfSpace 1)).symm
            (uliftDiffeomorph.{u, u} sphereHalfCollarModel
              (ClosureSphere.{u} × EuclideanHalfSpace 1)).symm
            (sphereCutHalfPatch c hs hd a.1 a.2) (sphereCutHalfPatch c hs hd a'.1 a'.2)
            (sphereCutHalf_to_half_smooth c hs hd a a')
            (sphereCutHalf_to_half_smooth c hs hd a' a)

theorem sphereCutPatch_cover (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) (x : SphereCutSpace c) :
    ∃ i, x ∈ (sphereCutPatch c hs hd i).target := by
  rcases sphereCutPatches_cover c hs hd x with hx | ⟨j, b, hx⟩
  · exact ⟨none, hx⟩
  · refine ⟨some (j, b), ?_⟩
    simpa [sphereCutPatch] using hx

theorem sphereCutPatch_half_coordinates (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target)
    (i : SphereCutPatchIndex) (x : SphereCutPatchSpace W i)
    (hx : x ∈ (sphereCutPatch c hs hd i).source) :
    ∃ d : PartialDiffeomorph (sphereCutPatchModel W i) (𝓡∂ 3)
      (SphereCutPatchSpace W i) (EuclideanHalfSpace 3) ∞, x ∈ d.source := by
  cases i with
  | none =>
      obtain ⟨d, hdx⟩ := exists_sphereCapCarrierCoordinates W x
      exact ⟨d.restrict (sphereCutPatch c hs hd none).source
        (sphereCutPatch c hs hd none).open_source, hdx, hx⟩
  | some a =>
      obtain ⟨d, hdx⟩ := exists_sphereCapHalfCoordinates x.down
      let l := (uliftDiffeomorph.{u, u} sphereHalfCollarModel
        (ClosureSphere.{u} × EuclideanHalfSpace 1)).symm
      let e := l.toPartialDiffeomorph.trans d
      exact ⟨e.restrict (sphereCutPatch c hs hd (some a)).source
        (sphereCutPatch c hs hd (some a)).open_source, ⟨mem_univ x, hdx⟩, hx⟩

theorem exists_sphereCutAtlas (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) :
    ∃ A : ChartedSpace (EuclideanHalfSpace 3) (SphereCutSpace c), letI := A
      IsManifold (𝓡∂ 3) ∞ (SphereCutSpace c) ∧ ∀ i,
        ContMDiffOn (sphereCutPatchModel W i) (𝓡∂ 3) ∞
          (sphereCutPatch c hs hd i) (sphereCutPatch c hs hd i).source ∧
        ContMDiffOn (𝓡∂ 3) (sphereCutPatchModel W i) ∞
          (sphereCutPatch c hs hd i).symm (sphereCutPatch c hs hd i).target :=
  exists_carrierSurgeryAtlas_of_openCover (𝓡∂ 3) (sphereCutPatch c hs hd)
    (sphereCutPatch_cover c hs hd) (sphereCutPatch_compatible c hs hd)
    (sphereCutPatch_half_coordinates c hs hd)



@[instance_reducible]
def sphereCutChartedSpace (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) :
    ChartedSpace (EuclideanHalfSpace 3) (SphereCutSpace c) :=
  (exists_sphereCutAtlas c hs hd).choose

theorem sphereCutIsManifold (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) :
    letI := sphereCutChartedSpace c hs hd
    IsManifold (𝓡∂ 3) ∞ (SphereCutSpace c) :=
  (exists_sphereCutAtlas c hs hd).choose_spec.1

theorem sphereCutPatch_smooth (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) :
    letI := sphereCutChartedSpace c hs hd
    ∀ i, ContMDiffOn (sphereCutPatchModel W i) (𝓡∂ 3) ∞
        (sphereCutPatch c hs hd i) (sphereCutPatch c hs hd i).source ∧
      ContMDiffOn (𝓡∂ 3) (sphereCutPatchModel W i) ∞
        (sphereCutPatch c hs hd i).symm (sphereCutPatch c hs hd i).target :=
  (exists_sphereCutAtlas c hs hd).choose_spec.2

theorem sphereCutFold_comp_patch_smooth (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target)
    (i : SphereCutPatchIndex) :
    ContMDiffOn (sphereCutPatchModel W i) W.model ∞
      (sphereCutFold c ∘ sphereCutPatch c hs hd i) (sphereCutPatch c hs hd i).source := by
  cases i with
  | none =>
      apply contMDiffOn_id.congr
      intro p hp
      exact sphereCutAmbientPatch_fold c hs hd p
        ((sphereCutAmbientPatch_source c hs hd).subset hp)
  | some a =>
      let l := (uliftDiffeomorph.{u, u} sphereHalfCollarModel
        (ClosureSphere.{u} × EuclideanHalfSpace 1)).symm
      have hf : ContMDiffOn sphereHalfCollarModel W.model ∞
          (c a.1 ∘ sphereCutHalfSigned a.2) sphereCutHalfPatchSource :=
        (c a.1).contMDiffOn.comp (sphereCutHalfSigned_smooth a.2).contMDiffOn
          (sphereCutHalfSigned_source c hs a.1 a.2)
      have hg : ContMDiffOn sphereHalfCollarModel W.model ∞
          ((c a.1 ∘ sphereCutHalfSigned a.2) ∘ l)
          (sphereCutPatch c hs hd (some a)).source :=
        hf.comp l.contMDiff.contMDiffOn (by
          intro p hp
          exact (sphereCutHalfPatch_source c hs hd a.1 a.2).subset hp.2)
      apply hg.congr
      intro p hp
      have hps : l p ∈ sphereCutHalfPatchSource :=
        (sphereCutHalfPatch_source c hs hd a.1 a.2).subset hp.2
      exact congrArg Prod.fst (sphereCutHalfPatch_apply c hs hd a.1 a.2 (l p) hps)

theorem sphereCutFold_smooth (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) :
    letI := sphereCutChartedSpace c hs hd
    ContMDiff (𝓡∂ 3) W.model ∞ (sphereCutFold c) := by
  let atlas := sphereCutChartedSpace c hs hd
  let smooth := sphereCutIsManifold c hs hd
  intro x
  obtain ⟨i, hx⟩ := sphereCutPatch_cover c hs hd x
  let e := sphereCutPatch c hs hd i
  have hp := e.map_target hx
  have hg := (sphereCutFold_comp_patch_smooth c hs hd i).contMDiffAt
    (e.open_source.mem_nhds hp)
  have hi := ((sphereCutPatch_smooth c hs hd i).2).contMDiffAt
    (e.open_target.mem_nhds hx)
  apply (hg.comp x hi).congr_of_eventuallyEq
  filter_upwards [e.open_target.mem_nhds hx] with y hy
  exact congrArg (sphereCutFold c) (e.right_inv hy).symm


theorem sphereCutHalfSigned_mfderiv_injective (b : Bool)
    (p : ClosureSphere.{u} × EuclideanHalfSpace 1) :
    Function.Injective (mfderiv sphereHalfCollarModel sphereSignedCollarModel
      (sphereCutHalfSigned b) p) := by
  cases b
  · have h := injective_mfderiv_scaledHalfSpaceOneProductCoordinate (𝓡 2)
      (σ := 1) (by norm_num) p
    have he : (fun z : ClosureSphere.{u} × EuclideanHalfSpace 1 => (z.1, 1 * z.2.val 0)) =
        sphereCutHalfSigned false := by
      funext z
      simp [sphereCutHalfSigned, sphereCutSign]
    rw [he] at h
    exact h
  · have h := injective_mfderiv_scaledHalfSpaceOneProductCoordinate (𝓡 2)
      (σ := -1) (by norm_num) p
    have he : (fun z : ClosureSphere.{u} × EuclideanHalfSpace 1 => (z.1, -1 * z.2.val 0)) =
        sphereCutHalfSigned true := by
      funext z
      simp [sphereCutHalfSigned, sphereCutSign]
    rw [he] at h
    exact h

theorem sphereCutCollarHalf_mfderiv_injective (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource) (j : Fin 1) (b : Bool)
    (p : ClosureSphere.{u} × EuclideanHalfSpace 1) (hp : p ∈ sphereCutHalfPatchSource) :
    Function.Injective (mfderiv sphereHalfCollarModel W.model (c j ∘ sphereCutHalfSigned b) p) := by
  have hps := sphereCutHalfSigned_source c hs j b p hp
  have hc := (c j).isLocalDiffeomorphAt sphereSignedCollarModel W.model ∞ hps
  rw [mfderiv_comp p ((c j).mdifferentiableAt (by simp) hps)
    ((sphereCutHalfSigned_smooth b).mdifferentiableAt (by simp))]
  exact (hc.mfderivToContinuousLinearEquiv (by simp)).injective.comp
    (sphereCutHalfSigned_mfderiv_injective b p)


theorem sphereCutFold_comp_patch_mfderiv_injective (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target)
    (i : SphereCutPatchIndex) (p : SphereCutPatchSpace W i)
    (hp : p ∈ (sphereCutPatch c hs hd i).source) :
    Function.Injective (mfderiv (sphereCutPatchModel W i) W.model
      (sphereCutFold c ∘ sphereCutPatch c hs hd i) p) := by
  cases i with
  | none =>
      have he : sphereCutFold c ∘ sphereCutPatch c hs hd none =ᶠ[𝓝 p] id := by
        filter_upwards [(sphereCutAmbientPatch c hs hd).open_source.mem_nhds hp] with q hq
        exact sphereCutAmbientPatch_fold c hs hd q
          ((sphereCutAmbientPatch_source c hs hd).subset hq)
      rw [he.mfderiv_eq, mfderiv_id]
      exact Function.injective_id
  | some a =>
      let l := (uliftDiffeomorph.{u, u} sphereHalfCollarModel
        (ClosureSphere.{u} × EuclideanHalfSpace 1)).symm
      have hps : l p ∈ sphereCutHalfPatchSource :=
        (sphereCutHalfPatch_source c hs hd a.1 a.2).subset hp.2
      have he : sphereCutFold c ∘ sphereCutPatch c hs hd (some a) =ᶠ[𝓝 p]
          (c a.1 ∘ sphereCutHalfSigned a.2) ∘ l := by
        filter_upwards [(sphereCutPatch c hs hd (some a)).open_source.mem_nhds hp] with q hq
        exact congrArg Prod.fst (sphereCutHalfPatch_apply c hs hd a.1 a.2 (l q)
          ((sphereCutHalfPatch_source c hs hd a.1 a.2).subset hq.2))
      have hraw : MDifferentiableAt sphereHalfCollarModel W.model
          (c a.1 ∘ sphereCutHalfSigned a.2) (l p) :=
        ((c a.1).mdifferentiableAt (by simp)
          (sphereCutHalfSigned_source c hs a.1 a.2 (l p) hps)).comp (l p)
          ((sphereCutHalfSigned_smooth a.2).mdifferentiableAt (by simp))
      rw [he.mfderiv_eq, mfderiv_comp p hraw (l.contMDiff.mdifferentiableAt (by simp))]
      exact (sphereCutCollarHalf_mfderiv_injective c hs a.1 a.2 (l p) hps).comp
        ((l.isLocalDiffeomorph p).mfderivToContinuousLinearEquiv (by simp)).injective


theorem sphereCutFold_mfderiv_bijective (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) :
    letI := sphereCutChartedSpace c hs hd
    ∀ x, Function.Bijective (mfderiv (𝓡∂ 3) W.model (sphereCutFold c) x) := by
  let atlas := sphereCutChartedSpace c hs hd
  let smooth := sphereCutIsManifold c hs hd
  intro x
  obtain ⟨i, hx⟩ := sphereCutPatch_cover c hs hd x
  let e := sphereCutPatch c hs hd i
  let p := e.symm x
  have hp : p ∈ e.source := e.map_target hx
  let d : PartialDiffeomorph (sphereCutPatchModel W i) (𝓡∂ 3)
      (SphereCutPatchSpace W i) (SphereCutSpace c) ∞ :=
    { toPartialEquiv := e.toPartialEquiv
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := (sphereCutPatch_smooth c hs hd i).1
      contMDiffOn_invFun := (sphereCutPatch_smooth c hs hd i).2 }
  have hdif := d.isLocalDiffeomorphAt (sphereCutPatchModel W i) (𝓡∂ 3) ∞ hp
  have hdb := (hdif.mfderivToContinuousLinearEquiv (by simp)).bijective
  change Function.Bijective (mfderiv (sphereCutPatchModel W i) (𝓡∂ 3) d p) at hdb
  have hdf := (sphereCutFold_smooth c hs hd).mdifferentiableAt (x := d p) (by simp)
  have hchain := mfderiv_comp p hdf (d.mdifferentiableAt (by simp) hp)
  have hinj := sphereCutFold_comp_patch_mfderiv_injective c hs hd i p hp
  change Function.Injective
    (mfderiv (sphereCutPatchModel W i) W.model (sphereCutFold c ∘ d) p) at hinj
  have hcomp : Function.Injective
      ((mfderiv (𝓡∂ 3) W.model (sphereCutFold c) (d p)).comp
        (mfderiv (sphereCutPatchModel W i) (𝓡∂ 3) d p)) := by
    rw [← hchain]
    exact hinj
  have hfi : Function.Injective (mfderiv (𝓡∂ 3) W.model (sphereCutFold c) (d p)) := by
    intro v w hvw
    obtain ⟨v', hv'⟩ := hdb.2 v
    obtain ⟨w', hw'⟩ := hdb.2 w
    have heq : v' = w' := hcomp (by
      change mfderiv (𝓡∂ 3) W.model (sphereCutFold c) (d p)
        (mfderiv (sphereCutPatchModel W i) (𝓡∂ 3) d p v') =
        mfderiv (𝓡∂ 3) W.model (sphereCutFold c) (d p)
          (mfderiv (sphereCutPatchModel W i) (𝓡∂ 3) d p w')
      rw [hv', hw']
      exact hvw)
    have hdw := congrArg (mfderiv (sphereCutPatchModel W i) (𝓡∂ 3) d p) heq
    exact hv'.symm.trans (hdw.trans hw')
  have hdp : d p = x := e.right_inv hx
  rw [← hdp]
  exact ⟨hfi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rfl)).mp hfi⟩



theorem isOpen_sphereHalfCollar_lt (a : ℝ) :
    IsOpen {p : ClosureSphere.{u} × EuclideanHalfSpace 1 | p.2.val 0 < a} :=
  isOpen_lt (contMDiff_halfSpaceOneCoordinate.continuous.comp continuous_snd) continuous_const


section LocalOpenMap
variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]

private theorem sphereCut_openMap_of_local_patches (s : Set M) (hs : IsOpen s)
    (f : s → N) (hloc : ∀ p : s, ∃ e : OpenPartialHomeomorph M N,
      p.val ∈ e.source ∧ ∀ q : s, q.val ∈ e.source → f q = e q.val) :
    IsOpenMap f := by
  apply IsOpenMap.of_nhds_le
  intro p
  obtain ⟨e, hp, hmap⟩ := hloc p
  have he : f =ᶠ[𝓝 p] e ∘ Subtype.val := by
    filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds
      (e.open_source.mem_nhds hp)] with q hq
    exact hmap q hq
  have hf : map f (𝓝 p) = 𝓝 (f p) := by
    rw [Filter.map_congr he, ← map_map,
      hs.isOpenEmbedding_subtypeVal.map_nhds_eq p, e.map_nhds_eq hp, hmap p hp]
  exact hf.ge

end LocalOpenMap


def sphereCutSignedReflection :
    (ClosureSphere.{u} × ℝ) ≃ₘ⟮sphereSignedCollarModel, sphereSignedCollarModel⟯
    ClosureSphere.{u} × ℝ :=
  { toFun := fun p => (p.1, -p.2)
    invFun := fun p => (p.1, -p.2)
    left_inv := fun p => by simp
    right_inv := fun p => by simp
    contMDiff_toFun := contMDiff_fst.prodMk contMDiff_snd.neg
    contMDiff_invFun := contMDiff_fst.prodMk contMDiff_snd.neg }

def sphereCutHalfHeight : PartialDiffeomorph sphereHalfCollarModel sphereSignedCollarModel
    (ClosureSphere.{u} × EuclideanHalfSpace 1) (ClosureSphere.{u} × ℝ) ∞ :=
  PartialDiffeomorph.prod (Diffeomorph.refl (𝓡 2) ClosureSphere.{u} ∞).toPartialDiffeomorph
    halfSpaceOneInteriorDiffeomorph.symm

def sphereCutPositiveHeight (b : Bool) :
    PartialDiffeomorph sphereHalfCollarModel sphereSignedCollarModel
    (ClosureSphere.{u} × EuclideanHalfSpace 1) (ClosureSphere.{u} × ℝ) ∞ :=
  if b then sphereCutHalfHeight.trans sphereCutSignedReflection.toPartialDiffeomorph
  else sphereCutHalfHeight

theorem sphereCutPositiveHeight_source (b : Bool) :
    (sphereCutPositiveHeight b).source =
      {p : ClosureSphere.{u} × EuclideanHalfSpace 1 | 0 < p.2.val 0} := by
  cases b <;> ext p <;> simp [sphereCutPositiveHeight, sphereCutHalfHeight,
    PartialDiffeomorph.prod, halfSpaceOneInteriorDiffeomorph, Diffeomorph.toPartialDiffeomorph]

theorem sphereCutPositiveHeight_apply (b : Bool) (p : ClosureSphere.{u} × EuclideanHalfSpace 1) :
    sphereCutPositiveHeight b p = sphereCutHalfSigned b p := by
  cases b <;> rfl

def sphereCutPositiveHalfPatch (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) (j : Fin 1) (b : Bool) :
    OpenPartialHomeomorph (ClosureSphere.{u} × EuclideanHalfSpace 1) (SphereCutSpace c) :=
  ((sphereCutPositiveHeight b).toOpenPartialHomeomorph.trans
    (c j).toOpenPartialHomeomorph).trans (sphereCutAmbientPatch c hs hd)

theorem sphereCutFullHalfSigned_source (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource) (j : Fin 1) (b : Bool)
    (p : ClosureSphere.{u} × EuclideanHalfSpace 1) (hp : p ∈ sphereHalfCollarSource) :
    sphereCutHalfSigned b p ∈ (c j).source := by
  rw [hs j]
  simp only [sphereSignedCollarSource, mem_prod, mem_univ, true_and]
  have h0 := p.2.property
  have h1 : p.2.val 0 < 1 := hp
  change -1 < sphereCutSign b (p.2.val 0) ∧ sphereCutSign b (p.2.val 0) < 1
  cases b <;> simp only [sphereCutSign, Bool.false_eq_true, ↓reduceIte] <;>
    constructor <;> linarith [h0, h1]

theorem sphereCutPositiveHalfPatch_source (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) (j : Fin 1) (b : Bool) :
    (sphereCutPositiveHalfPatch c hs hd j b).source =
      {p : ClosureSphere.{u} × EuclideanHalfSpace 1 | 0 < p.2.val 0 ∧ p.2.val 0 < 1} := by
  ext p
  constructor
  · intro hp
    have hp0 : 0 < p.2.val 0 := (sphereCutPositiveHeight_source b).subset hp.1.1
    have hpS := hp.1.2
    change sphereCutPositiveHeight b p ∈ (c j).source at hpS
    rw [sphereCutPositiveHeight_apply, hs j] at hpS
    simp only [sphereSignedCollarSource, mem_prod, mem_univ, true_and] at hpS
    change -1 < sphereCutSign b (p.2.val 0) ∧ sphereCutSign b (p.2.val 0) < 1 at hpS
    refine ⟨hp0, ?_⟩
    cases b <;> simp only [sphereCutSign, Bool.false_eq_true, ↓reduceIte] at hpS
    · exact hpS.2
    · linarith [hpS.1]
  · rintro ⟨hp0, hp1⟩
    have hpS := sphereCutFullHalfSigned_source c hs j b p hp1
    have hz : c j (sphereCutHalfSigned b p) ∉ sphereCutAmbientZero c :=
      sphereCutSignedPoint_not_zero c hs hd j _ hpS (by
        cases b <;> simp only [sphereCutHalfSigned, sphereCutSign, Bool.false_eq_true, ↓reduceIte]
        · exact ne_of_gt hp0
        · exact neg_ne_zero.mpr (ne_of_gt hp0))
    have hheight : p ∈ (sphereCutPositiveHeight b).source := by
      rw [sphereCutPositiveHeight_source]
      exact hp0
    refine ⟨⟨hheight, ?_⟩, ?_⟩
    · change sphereCutPositiveHeight b p ∈ (c j).source
      rw [sphereCutPositiveHeight_apply]
      exact hpS
    · change c j (sphereCutPositiveHeight b p) ∈ (sphereCutAmbientPatch c hs hd).source
      rw [sphereCutPositiveHeight_apply, sphereCutAmbientPatch_source]
      exact hz


theorem sphereCutPositiveHalfPatch_fold (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) (j : Fin 1) (b : Bool)
    (p : ClosureSphere.{u} × EuclideanHalfSpace 1)
    (hp : p ∈ (sphereCutPositiveHalfPatch c hs hd j b).source) :
    sphereCutFold c (sphereCutPositiveHalfPatch c hs hd j b p) =
      c j (sphereCutHalfSigned b p) := by
  have hzero := hp.2
  change c j (sphereCutPositiveHeight b p) ∈ (sphereCutAmbientPatch c hs hd).source at hzero
  rw [sphereCutAmbientPatch_source, sphereCutPositiveHeight_apply] at hzero
  change sphereCutFold c (sphereCutAmbientPatch c hs hd (c j (sphereCutPositiveHeight b p))) = _
  rw [sphereCutPositiveHeight_apply]
  exact sphereCutAmbientPatch_fold c hs hd _ hzero

theorem sphereCutHalfLift_continuous (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) (j : Fin 1) (b : Bool) :
    Continuous (sphereCutHalfLift c hs hd j b) := by
  apply Continuous.subtype_mk
  have hsign : Continuous (sphereCutSign b) := by
    cases b
    · exact continuous_id
    · exact continuous_neg
  have hheight : Continuous (fun p : sphereHalfCollarSource => p.val.2.val 0) :=
    contMDiff_halfSpaceOneCoordinate.continuous.comp continuous_subtype_val.snd
  have hc : Continuous (fun p : sphereHalfCollarSource => c j (sphereCutHalfSigned b p.val)) :=
    (c j).toOpenPartialHomeomorph.continuousOn.comp_continuous
      ((sphereCutHalfSigned_smooth b).continuous.comp continuous_subtype_val)
      (fun p => sphereCutFullHalfSigned_source c hs j b p.val p.property)
  apply hc.prodMk
  apply continuous_pi
  intro i
  by_cases hi : i = j
  · simp only [sphereCutTag, hi, ↓reduceIte]
    exact hsign.comp (continuous_const.sub (contDiff_seamCut.continuous.comp hheight))
  · simp only [sphereCutTag, hi, ↓reduceIte]
    exact continuous_const

theorem sphereCutHalfLift_injective (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) (j : Fin 1) (b : Bool) :
    Function.Injective (sphereCutHalfLift c hs hd j b) := by
  intro p q he
  have hbase := congrArg (sphereCutFold c) he
  have hcoord := (c j).toOpenPartialHomeomorph.injOn
    (sphereCutFullHalfSigned_source c hs j b p.val p.property)
    (sphereCutFullHalfSigned_source c hs j b q.val q.property) hbase
  apply Subtype.ext
  have ht := congrArg Prod.fst hcoord
  have hr := congrArg Prod.snd hcoord
  have hr' : p.val.2.val 0 = q.val.2.val 0 := by
    cases b <;> simpa only [sphereCutHalfSigned, sphereCutSign,
      Bool.false_eq_true, ↓reduceIte, neg_inj] using hr
  have hh : p.val.2 = q.val.2 :=
    halfSpaceOneHomeomorph.injective (Subtype.ext hr')
  exact Prod.ext ht hh

theorem sphereCutPositiveHalfPatch_eq_lift (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) (j : Fin 1) (b : Bool)
    (p : ClosureSphere.{u} × EuclideanHalfSpace 1)
    (hp : p ∈ (sphereCutPositiveHalfPatch c hs hd j b).source) :
    sphereCutPositiveHalfPatch c hs hd j b p = sphereCutHalfLift c hs hd j b
      ⟨p, ((sphereCutPositiveHalfPatch_source c hs hd j b).subset hp).2⟩ := by
  have hf := sphereCutPositiveHalfPatch_fold c hs hd j b p hp
  have hz := hp.2
  change c j (sphereCutPositiveHeight b p) ∈ (sphereCutAmbientPatch c hs hd).source at hz
  rw [sphereCutAmbientPatch_source, sphereCutPositiveHeight_apply] at hz
  apply sphereCutFold_injOn_offZero c hs hd
  · change sphereCutFold c (sphereCutPositiveHalfPatch c hs hd j b p) ∉ sphereCutAmbientZero c
    rw [hf]
    exact hz
  · exact hz
  · exact hf

theorem sphereCutSmallHalfPatch_eq_lift (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) (j : Fin 1) (b : Bool)
    (p : ClosureSphere.{u} × EuclideanHalfSpace 1) (hp : p ∈ sphereCutHalfPatchSource) :
    sphereCutHalfPatch c hs hd j b p =
      sphereCutHalfLift c hs hd j b ⟨p, by
        change p.2.val 0 < 1
        have h : p.2.val 0 < 1 / 4 := hp
        linarith [h]⟩ := by
  apply Subtype.ext
  exact sphereCutHalfPatch_apply c hs hd j b p hp


theorem sphereCutHalfLift_isOpenMap (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) (j : Fin 1) (b : Bool) :
    IsOpenMap (sphereCutHalfLift c hs hd j b) := by
  apply sphereCut_openMap_of_local_patches sphereHalfCollarSource (isOpen_sphereHalfCollar_lt 1)
  intro p
  by_cases hp : p.val.2.val 0 < 1 / 4
  · refine ⟨sphereCutHalfPatch c hs hd j b, ?_, ?_⟩
    · rw [sphereCutHalfPatch_source]
      exact hp
    · intro q hq
      exact (sphereCutSmallHalfPatch_eq_lift c hs hd j b q.val
        ((sphereCutHalfPatch_source c hs hd j b).subset hq)).symm
  · have hp0 : 0 < p.val.2.val 0 := by linarith [le_of_not_gt hp]
    refine ⟨sphereCutPositiveHalfPatch c hs hd j b, ?_, ?_⟩
    · rw [sphereCutPositiveHalfPatch_source]
      exact ⟨hp0, p.property⟩
    · intro q hq
      exact (sphereCutPositiveHalfPatch_eq_lift c hs hd j b q.val hq).symm

theorem sphereCutHalfLift_openEmbedding (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) (j : Fin 1) (b : Bool) :
    _root_.Topology.IsOpenEmbedding (sphereCutHalfLift c hs hd j b) :=
  _root_.Topology.isOpenEmbedding_iff_continuous_injective_isOpenMap.mpr
    ⟨sphereCutHalfLift_continuous c hs hd j b, sphereCutHalfLift_injective c hs hd j b,
      sphereCutHalfLift_isOpenMap c hs hd j b⟩


def sphereCutFullHalfPatch (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) (j : Fin 1) (b : Bool) :
    OpenPartialHomeomorph (ClosureSphere.{u} × EuclideanHalfSpace 1) (SphereCutSpace c) := by
  letI : Nonempty sphereHalfCollarSource :=
    ⟨⟨(Classical.arbitrary ClosureSphere.{u}, halfZero), by change (0 : ℝ) < 1; norm_num⟩⟩
  have hopen : IsOpen sphereHalfCollarSource := isOpen_sphereHalfCollar_lt 1
  exact (hopen.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph
    (Subtype.val : sphereHalfCollarSource → ClosureSphere.{u} × EuclideanHalfSpace 1)).symm.trans
    ((sphereCutHalfLift_openEmbedding c hs hd j b).toOpenPartialHomeomorph
      (sphereCutHalfLift c hs hd j b))

theorem sphereCutFullHalfPatch_source (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) (j : Fin 1) (b : Bool) :
    (sphereCutFullHalfPatch c hs hd j b).source = sphereHalfCollarSource := by
  simp [sphereCutFullHalfPatch]

theorem sphereCutFullHalfPatch_target (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) (j : Fin 1) (b : Bool) :
    (sphereCutFullHalfPatch c hs hd j b).target = range (sphereCutHalfLift c hs hd j b) := by
  simp [sphereCutFullHalfPatch]

theorem sphereCutFullHalfPatch_apply (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) (j : Fin 1) (b : Bool)
    (p : ClosureSphere.{u} × EuclideanHalfSpace 1) (hp : p ∈ sphereHalfCollarSource) :
    sphereCutFullHalfPatch c hs hd j b p = sphereCutHalfLift c hs hd j b ⟨p, hp⟩ := by
  let sourceNonempty : Nonempty sphereHalfCollarSource :=
    ⟨⟨(Classical.arbitrary ClosureSphere.{u}, halfZero), by change (0 : ℝ) < 1; norm_num⟩⟩
  have hopen : IsOpen sphereHalfCollarSource := isOpen_sphereHalfCollar_lt 1
  let G : OpenPartialHomeomorph sphereHalfCollarSource (ClosureSphere.{u} × EuclideanHalfSpace 1) :=
    hopen.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph
    (Subtype.val : sphereHalfCollarSource → ClosureSphere.{u} × EuclideanHalfSpace 1)
  have hg : G.symm p = (⟨p, hp⟩ : sphereHalfCollarSource) := by
    simpa only [G, _root_.Topology.IsOpenEmbedding.toOpenPartialHomeomorph_apply] using
      G.left_inv (x := (⟨p, hp⟩ : sphereHalfCollarSource)) (mem_univ _)
  change sphereCutHalfLift c hs hd j b (G.symm p) = _
  rw [hg]

theorem sphereCutFullHalfPatch_fold (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) (j : Fin 1) (b : Bool)
    (p : ClosureSphere.{u} × EuclideanHalfSpace 1) (hp : p ∈ sphereHalfCollarSource) :
    sphereCutFold c (sphereCutFullHalfPatch c hs hd j b p) =
      c j (sphereCutHalfSigned b p) := by
  rw [sphereCutFullHalfPatch_apply c hs hd j b p hp]
  rfl

theorem sphereCutFullHalfPatch_zero (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) (j : Fin 1) (b : Bool)
    (t : ClosureSphere.{u}) : sphereCutFullHalfPatch c hs hd j b (t, halfZero) =
      sphereCutZero c j b t := by
  rw [sphereCutFullHalfPatch_apply c hs hd j b _ (by change (0 : ℝ) < 1; norm_num)]
  rfl


def sphereCutCarrier (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) : CompactCarrier.{u} := by
  letI := sphereCutChartedSpace c hs hd
  letI := sphereCutIsManifold c hs hd
  exact
    { kind := .withBoundary
      Carrier := SphereCutSpace c
      charts := sphereCutChartedSpace c hs hd
      smooth := sphereCutIsManifold c hs hd
      compact := sphereCutCompactSpace c hs
      orientation := Manifold.manifoldOrientationPullback (𝓡∂ 3) W.model
        finrank_euclideanSpace_fin (sphereCutFold c) (sphereCutFold_smooth c hs hd)
        (sphereCutFold_mfderiv_bijective c hs hd) W.orientation }

def sphereCutAmbientPartialDiffeomorph (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) :
    PartialDiffeomorph W.model (sphereCutCarrier c hs hd).model
      W.Carrier (sphereCutCarrier c hs hd).Carrier ∞ where
  toPartialEquiv := (sphereCutAmbientPatch c hs hd).toPartialEquiv
  open_source := (sphereCutAmbientPatch c hs hd).open_source
  open_target := (sphereCutAmbientPatch c hs hd).open_target
  contMDiffOn_toFun := (sphereCutPatch_smooth c hs hd none).1
  contMDiffOn_invFun := (sphereCutPatch_smooth c hs hd none).2

def sphereCutSmallHalfPartialDiffeomorph (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) (j : Fin 1) (b : Bool) :
    PartialDiffeomorph sphereHalfCollarModel (sphereCutCarrier c hs hd).model
      (ClosureSphere.{u} × EuclideanHalfSpace 1) (sphereCutCarrier c hs hd).Carrier ∞ where
  toPartialEquiv := (sphereCutHalfPatch c hs hd j b).toPartialEquiv
  open_source := (sphereCutHalfPatch c hs hd j b).open_source
  open_target := (sphereCutHalfPatch c hs hd j b).open_target
  contMDiffOn_toFun := by
    let atlas := sphereCutChartedSpace c hs hd
    let l := uliftDiffeomorph.{u, u} sphereHalfCollarModel
      (ClosureSphere.{u} × EuclideanHalfSpace 1)
    have h := ((sphereCutPatch_smooth c hs hd (some (j, b))).1).comp
      l.contMDiff.contMDiffOn (by
        intro p hp
        change True ∧ p ∈ (sphereCutHalfPatch c hs hd j b).source
        exact ⟨trivial, hp⟩)
    exact h
  contMDiffOn_invFun := by
    let atlas := sphereCutChartedSpace c hs hd
    let l := uliftDiffeomorph.{u, u} sphereHalfCollarModel
      (ClosureSphere.{u} × EuclideanHalfSpace 1)
    have h := l.symm.contMDiff.comp_contMDiffOn
      ((sphereCutPatch_smooth c hs hd (some (j, b))).2)
    exact h.mono (fun p hp => ⟨hp, mem_univ _⟩)

theorem sphereCutAmbientPartialDiffeomorph_toOpenPartialHomeomorph
    (c : SphereCutSignedCollars W) (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) :
    (sphereCutAmbientPartialDiffeomorph c hs hd).toOpenPartialHomeomorph =
      sphereCutAmbientPatch c hs hd := rfl

theorem sphereCutSmallHalfPartialDiffeomorph_toOpenPartialHomeomorph
    (c : SphereCutSignedCollars W) (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) (j : Fin 1) (b : Bool) :
    (sphereCutSmallHalfPartialDiffeomorph c hs hd j b).toOpenPartialHomeomorph =
      sphereCutHalfPatch c hs hd j b := rfl


section LocalSmooth

variable {E F H K M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace K] [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace H M] [ChartedSpace K N]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}

private theorem sphereCut_smooth_of_local_diffeomorphisms
    (e : OpenPartialHomeomorph M N)
    (hloc : ∀ p, p ∈ e.source → ∃ d : PartialDiffeomorph I J M N ∞,
      p ∈ d.source ∧ d.source ⊆ e.source ∧ ∀ q, q ∈ d.source → e q = d q) :
    ContMDiffOn I J ∞ e e.source ∧ ContMDiffOn J I ∞ e.symm e.target := by
  constructor
  · intro p hp
    obtain ⟨d, hd, hsub, heq⟩ := hloc p hp
    apply ContMDiffAt.contMDiffWithinAt
    apply (d.contMDiffOn.contMDiffAt (d.open_source.mem_nhds hd)).congr_of_eventuallyEq
    filter_upwards [d.open_source.mem_nhds hd] with q hq
    exact heq q hq
  · intro p hp
    let q := e.symm p
    have hq : q ∈ e.source := e.map_target hp
    obtain ⟨d, hd, hsub, heq⟩ := hloc q hq
    have hdq : p ∈ d.target := by
      have h := d.map_source hd
      rw [← heq q hd, e.right_inv hp] at h
      exact h
    apply ContMDiffAt.contMDiffWithinAt
    apply (d.symm.contMDiffOn.contMDiffAt
      (d.open_target.mem_nhds hdq)).congr_of_eventuallyEq
    filter_upwards [d.open_target.mem_nhds hdq] with y hy
    have hdy : d.symm y ∈ d.source := d.map_target hy
    have hfold : e (d.symm y) = y := (heq (d.symm y) hdy).trans (d.right_inv hy)
    exact (congrArg e.symm hfold).symm.trans (e.left_inv (hsub hdy))

end LocalSmooth



def sphereCutPositiveHalfPartialDiffeomorph (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) (j : Fin 1) (b : Bool) :
    PartialDiffeomorph sphereHalfCollarModel (sphereCutCarrier c hs hd).model
      (ClosureSphere.{u} × EuclideanHalfSpace 1) (sphereCutCarrier c hs hd).Carrier ∞ :=
  ((sphereCutPositiveHeight b).trans (c j)).trans
    (sphereCutAmbientPartialDiffeomorph c hs hd)

theorem sphereCutPositiveHalfPartialDiffeomorph_toOpenPartialHomeomorph
    (c : SphereCutSignedCollars W) (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) (j : Fin 1) (b : Bool) :
    (sphereCutPositiveHalfPartialDiffeomorph c hs hd j b).toOpenPartialHomeomorph =
      sphereCutPositiveHalfPatch c hs hd j b := rfl

theorem sphereCutFullHalfPatch_smooth (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) (j : Fin 1) (b : Bool) :
    letI := sphereCutChartedSpace c hs hd
    ContMDiffOn sphereHalfCollarModel (𝓡∂ 3) ∞ (sphereCutFullHalfPatch c hs hd j b)
      (sphereCutFullHalfPatch c hs hd j b).source ∧
    ContMDiffOn (𝓡∂ 3) sphereHalfCollarModel ∞ (sphereCutFullHalfPatch c hs hd j b).symm
      (sphereCutFullHalfPatch c hs hd j b).target := by
  let atlas := sphereCutChartedSpace c hs hd
  apply sphereCut_smooth_of_local_diffeomorphisms
  intro p hp
  have hp1 : p ∈ sphereHalfCollarSource := (sphereCutFullHalfPatch_source c hs hd j b).subset hp
  by_cases hpSmall : p.2.val 0 < 1 / 4
  · let d := sphereCutSmallHalfPartialDiffeomorph c hs hd j b
    have hdsource : d.source = sphereCutHalfPatchSource := sphereCutHalfPatch_source c hs hd j b
    refine ⟨d, hdsource.symm.subset hpSmall, ?_, ?_⟩
    · intro q hq
      rw [sphereCutFullHalfPatch_source]
      have h : q.2.val 0 < 1 / 4 := hdsource.subset hq
      change q.2.val 0 < 1
      linarith [h]
    · intro q hq
      have hqs : q ∈ sphereCutHalfPatchSource := hdsource.subset hq
      have hq1 : q ∈ sphereHalfCollarSource := by
        change q.2.val 0 < 1
        have h : q.2.val 0 < 1 / 4 := hqs
        linarith [h]
      exact (sphereCutFullHalfPatch_apply c hs hd j b q hq1).trans
        (sphereCutSmallHalfPatch_eq_lift c hs hd j b q hqs).symm
  · let d := sphereCutPositiveHalfPartialDiffeomorph c hs hd j b
    have hdsource : d.source = {q : ClosureSphere.{u} × EuclideanHalfSpace 1 |
        0 < q.2.val 0 ∧ q.2.val 0 < 1} := sphereCutPositiveHalfPatch_source c hs hd j b
    have hp0 : 0 < p.2.val 0 := by linarith [le_of_not_gt hpSmall]
    refine ⟨d, hdsource.symm.subset ⟨hp0, hp1⟩, ?_, ?_⟩
    · intro q hq
      exact (sphereCutFullHalfPatch_source c hs hd j b).symm.subset ((hdsource.subset hq).2)
    · intro q hq
      have hq1 : q ∈ sphereHalfCollarSource := (hdsource.subset hq).2
      exact (sphereCutFullHalfPatch_apply c hs hd j b q hq1).trans
        (sphereCutPositiveHalfPatch_eq_lift c hs hd j b q hq).symm

def sphereCutFullCollar (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) (j : Fin 1) (b : Bool) :
    PartialDiffeomorph sphereHalfCollarModel (sphereCutCarrier c hs hd).model
      (ClosureSphere.{u} × EuclideanHalfSpace 1) (sphereCutCarrier c hs hd).Carrier ∞ where
  toPartialEquiv := (sphereCutFullHalfPatch c hs hd j b).toPartialEquiv
  open_source := (sphereCutFullHalfPatch c hs hd j b).open_source
  open_target := (sphereCutFullHalfPatch c hs hd j b).open_target
  contMDiffOn_toFun := (sphereCutFullHalfPatch_smooth c hs hd j b).1
  contMDiffOn_invFun := (sphereCutFullHalfPatch_smooth c hs hd j b).2

theorem sphereCutFullCollar_toOpenPartialHomeomorph (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) (j : Fin 1) (b : Bool) :
    (sphereCutFullCollar c hs hd j b).toOpenPartialHomeomorph =
      sphereCutFullHalfPatch c hs hd j b := rfl

theorem sphereCutFullCollar_source (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) (j : Fin 1) (b : Bool) :
    (sphereCutFullCollar c hs hd j b).source = sphereHalfCollarSource :=
  sphereCutFullHalfPatch_source c hs hd j b

theorem sphereCutFullCollar_target (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) (j : Fin 1) (b : Bool) :
    (sphereCutFullCollar c hs hd j b).target = range (sphereCutHalfLift c hs hd j b) :=
  sphereCutFullHalfPatch_target c hs hd j b

theorem sphereCutFullCollar_apply (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) (j : Fin 1) (b : Bool)
    (p : ClosureSphere.{u} × EuclideanHalfSpace 1) (hp : p ∈ sphereHalfCollarSource) :
    sphereCutFullCollar c hs hd j b p = sphereCutHalfLift c hs hd j b ⟨p, hp⟩ :=
  sphereCutFullHalfPatch_apply c hs hd j b p hp

theorem sphereCutFullCollar_fold (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) (j : Fin 1) (b : Bool)
    (p : ClosureSphere.{u} × EuclideanHalfSpace 1) (hp : p ∈ sphereHalfCollarSource) :
    sphereCutFold c (sphereCutFullCollar c hs hd j b p) = c j (sphereCutHalfSigned b p) :=
  sphereCutFullHalfPatch_fold c hs hd j b p hp

theorem sphereCutFullCollar_zero (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) (j : Fin 1) (b : Bool)
    (t : ClosureSphere.{u}) :
    sphereCutFullCollar c hs hd j b (t, halfZero) = sphereCutZero c j b t :=
  sphereCutFullHalfPatch_zero c hs hd j b t


def sphereCutFoldTangentEquiv (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target)
    (x : (sphereCutCarrier c hs hd).Carrier) :
    TangentSpace (sphereCutCarrier c hs hd).model x ≃L[ℝ]
      TangentSpace W.model (sphereCutFold c x) := by
  letI := sphereCutChartedSpace c hs hd
  letI := sphereCutIsManifold c hs hd
  exact Manifold.differentialEquivOfBijective (𝓡∂ 3) W.model
    (sphereCutFold c) (sphereCutFold_mfderiv_bijective c hs hd) x

theorem sphereCutFold_orientation_map (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target)
    (x : (sphereCutCarrier c hs hd).Carrier) :
    Orientation.map (Fin 3) (sphereCutFoldTangentEquiv c hs hd x).toLinearEquiv
      ((sphereCutCarrier c hs hd).orientation.orientation x) =
        W.orientation.orientation (sphereCutFold c x) := by
  let atlas := sphereCutChartedSpace c hs hd
  let smooth := sphereCutIsManifold c hs hd
  exact Manifold.orientation_map_manifoldOrientationPullback (𝓡∂ 3) W.model
    finrank_euclideanSpace_fin (sphereCutFold c) (sphereCutFold_smooth c hs hd)
    (sphereCutFold_mfderiv_bijective c hs hd) W.orientation x


theorem sphereCutFold_fiber_zero (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target)
    (j : Fin 1) (t : ClosureSphere.{u}) (x : SphereCutSpace c)
    (he : sphereCutFold c x = c j (t, 0)) :
    ∃ b : Bool, x = sphereCutZero c j b t := by
  have hz : (t, (0 : ℝ)) ∈ (c j).source := by
    rw [hs j]
    simp only [sphereSignedCollarSource, mem_prod, mem_univ, true_and]
    change -1 < (0 : ℝ) ∧ (0 : ℝ) < 1
    norm_num
  rcases x.property with hxE | hxB
  · obtain ⟨a, ha, hax⟩ := hxE
    have hout : c j (t, 0) ∈ sphereCutOutside c := by
      change x.val.1 = c j (t, 0) at he
      rw [← he, ← hax]
      exact ha
    have hn := (sphereCutOutside_coordinate c hs hd j (t, 0) hz).mp hout
    exact (hn (by norm_num)).elim
  · obtain ⟨k, hk⟩ := mem_iUnion.mp hxB
    obtain ⟨b, p, hp, hpx⟩ := mem_iUnion.mp hk
    have hpS := sphereCutBand_source c hs k b p hp
    have he' : c k (p.1, sphereCutSign b p.2) = c j (t, 0) := by
      change x.val.1 = c j (t, 0) at he
      simpa only [← hpx, sphereCutBand] using he
    have hkj : k = j := by
      by_contra hn
      exact disjoint_left.mp (hd hn) ((c k).map_source hpS)
        (he' ▸ (c j).map_source hz)
    subst k
    have hcoord := (c j).toOpenPartialHomeomorph.injOn hpS hz he'
    have ht : p.1 = t := congrArg Prod.fst hcoord
    have hr : p.2 = 0 := by
      have hh := congrArg Prod.snd hcoord
      cases b <;> simpa [sphereCutSign] using hh
    refine ⟨b, Subtype.ext ?_⟩
    rw [← hpx]
    exact congrArg (sphereCutBand c j b) (Prod.ext ht hr)


theorem sphereCutHalf_isBoundaryPoint_iff (p : ClosureSphere.{u} × EuclideanHalfSpace 1) :
    sphereHalfCollarModel.IsBoundaryPoint p ↔ p.2.val 0 = 0 := by
  have hi : sphereHalfCollarModel.IsInteriorPoint p ↔ 0 < p.2.val 0 := by
    change p ∈ sphereHalfCollarModel.interior (ClosureSphere.{u} × EuclideanHalfSpace 1) ↔
      0 < p.2.val 0
    rw [ModelWithCorners.interior_prod]
    constructor
    · intro hp
      have hh := hp.2
      change (modelWithCornersEuclideanHalfSpace 1).IsInteriorPoint p.2 at hh
      rw [ModelWithCorners.IsInteriorPoint,
        interior_range_modelWithCornersEuclideanHalfSpace] at hh
      exact hh
    · intro hp
      refine ⟨BoundarylessManifold.isInteriorPoint, ?_⟩
      change (modelWithCornersEuclideanHalfSpace 1).IsInteriorPoint p.2
      rw [ModelWithCorners.IsInteriorPoint, interior_range_modelWithCornersEuclideanHalfSpace]
      exact hp
  rw [ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint, hi, not_lt]
  exact ⟨fun hp => le_antisymm hp p.2.property, fun hp => hp.le⟩

theorem sphereCutZero_union_eq_preimage (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) :
    (⋃ j, ⋃ b, range (sphereCutZero c j b)) =
      sphereCutFold c ⁻¹' sphereCutAmbientZero c := by
  ext x
  constructor
  · intro hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    obtain ⟨b, t, ht⟩ := mem_iUnion.mp hj
    rw [← ht]
    exact mem_iUnion.mpr ⟨j, t, (sphereCutZero_fold c j b t).symm⟩
  · intro hx
    rcases sphereCutPatches_cover c hs hd x with ha | ⟨j, b, hb⟩
    · rw [sphereCutAmbientPatch_target] at ha
      exact (ha hx).elim
    · rw [sphereCutHalfPatch_target] at hb
      obtain ⟨p, hp, hpx⟩ := hb
      have hpS := sphereCutBand_source c hs j b p
        ⟨hp.1, hp.2.1, by linarith [hp.2.2]⟩
      have he : sphereCutFold c x = c j (p.1, sphereCutSign b p.2) := by
        change x.val.1 = (sphereCutBand c j b p).1
        exact congrArg Prod.fst hpx.symm
      have h0 : p.2 = 0 := by
        by_contra hn
        have hsign : sphereCutSign b p.2 ≠ 0 := by
          cases b <;> simpa [sphereCutSign] using hn
        exact sphereCutSignedPoint_not_zero c hs hd j _ hpS hsign (he ▸ hx)
      refine mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨b, p.1, ?_⟩⟩
      apply Subtype.ext
      change sphereCutBand c j b (p.1, 0) = x.val
      rw [← hpx]
      exact congrArg (sphereCutBand c j b) (Prod.ext rfl h0.symm)

theorem sphereCutOffZero_eq_compl_zero (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) :
    sphereCutOffZero c = (⋃ j, ⋃ b, range (sphereCutZero c j b))ᶜ := by
  rw [sphereCutZero_union_eq_preimage c hs hd]
  rfl


theorem sphereCutZero_isBoundaryPoint (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) (j : Fin 1) (b : Bool)
    (t : ClosureSphere.{u}) :
    sphereCutZero c j b t ∈
      (sphereCutCarrier c hs hd).model.boundary (sphereCutCarrier c hs hd).Carrier := by
  let e := sphereCutSmallHalfPartialDiffeomorph c hs hd j b
  have hp : (t, halfZero) ∈ e.source := by
    change (t, halfZero) ∈ (sphereCutHalfPatch c hs hd j b).source
    rw [sphereCutHalfPatch_source]
    change (0 : ℝ) < 1 / 4
    norm_num
  have he : e (t, halfZero) = sphereCutZero c j b t := by
    apply Subtype.ext
    exact sphereCutHalfPatch_apply c hs hd j b (t, halfZero) (by
      change (0 : ℝ) < 1 / 4
      norm_num)
  have hl := e.isLocalDiffeomorphAt sphereHalfCollarModel (sphereCutCarrier c hs hd).model ∞ hp
  have hb := hl.isBoundaryPoint_iff (by simp)
  rw [← he]
  exact hb.mp ((sphereCutHalf_isBoundaryPoint_iff (t, halfZero)).mpr rfl)



theorem sphereCutAmbientPartialDiffeomorph_source (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) :
    (sphereCutAmbientPartialDiffeomorph c hs hd).source = (sphereCutAmbientZero c)ᶜ :=
  sphereCutAmbientPatch_source c hs hd

theorem sphereCutAmbientPartialDiffeomorph_fold (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target)
    (x : W.Carrier) (hx : x ∉ sphereCutAmbientZero c) :
    sphereCutFold c (sphereCutAmbientPartialDiffeomorph c hs hd x) = x :=
  sphereCutAmbientPatch_fold c hs hd x hx

theorem sphereCutCarrier_boundary_iff (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target)
    (x : (sphereCutCarrier c hs hd).Carrier) :
    (sphereCutCarrier c hs hd).model.IsBoundaryPoint x ↔
      W.model.IsBoundaryPoint (sphereCutFold c x) ∨ x ∈ ⋃ j, ⋃ b, range (sphereCutZero c j b) := by
  by_cases hx : x ∈ sphereCutOffZero c
  · have ht : x ∈ (sphereCutAmbientPartialDiffeomorph c hs hd).target := by
      change x ∈ (sphereCutAmbientPatch c hs hd).target
      rwa [sphereCutAmbientPatch_target]
    have hl := (sphereCutAmbientPartialDiffeomorph c hs hd).symm.isLocalDiffeomorphAt
      (sphereCutCarrier c hs hd).model W.model ∞ ht
    have he := hl.isBoundaryPoint_iff (by simp)
    change (sphereCutCarrier c hs hd).model.IsBoundaryPoint x ↔
      W.model.IsBoundaryPoint ((sphereCutAmbientPatch c hs hd).symm x) at he
    rw [sphereCutAmbientPatch_symm c hs hd x ht] at he
    have hn : x ∉ ⋃ j, ⋃ b, range (sphereCutZero c j b) := by
      rwa [sphereCutOffZero_eq_compl_zero] at hx
    simpa only [hn, or_false] using he
  · have hz : x ∈ ⋃ j, ⋃ b, range (sphereCutZero c j b) := by
      rw [sphereCutOffZero_eq_compl_zero c hs hd] at hx
      exact not_not.mp hx
    have hb : (sphereCutCarrier c hs hd).model.IsBoundaryPoint x := by
      obtain ⟨j, hj⟩ := mem_iUnion.mp hz
      obtain ⟨b, z, rfl⟩ := mem_iUnion.mp hj
      exact sphereCutZero_isBoundaryPoint c hs hd j b z
    exact iff_of_true hb (Or.inr hz)

theorem sphereCutFold_fibre_relation (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target)
    (x y : SphereCutSpace c) : sphereCutFold c x = sphereCutFold c y ↔ x = y ∨ ∃ z,
      (x = sphereCutZero c 0 false z ∧ y = sphereCutZero c 0 true z) ∨
      (x = sphereCutZero c 0 true z ∧ y = sphereCutZero c 0 false z) := by
  constructor
  · intro he
    by_cases hz : sphereCutFold c x ∈ sphereCutAmbientZero c
    · obtain ⟨j, z, hzx⟩ := mem_iUnion.mp hz
      have hj : j = 0 := Subsingleton.elim j 0
      subst j
      obtain ⟨b, rfl⟩ := sphereCutFold_fiber_zero c hs hd 0 z x hzx.symm
      obtain ⟨b', rfl⟩ := sphereCutFold_fiber_zero c hs hd 0 z y (he.symm.trans hzx.symm)
      cases b <;> cases b'
      · exact Or.inl rfl
      · exact Or.inr ⟨z, Or.inl ⟨rfl, rfl⟩⟩
      · exact Or.inr ⟨z, Or.inr ⟨rfl, rfl⟩⟩
      · exact Or.inl rfl
    · have hy : y ∈ sphereCutOffZero c := by
        change sphereCutFold c y ∉ sphereCutAmbientZero c
        rwa [← he]
      exact Or.inl (sphereCutFold_injOn_offZero c hs hd hz hy he)
  · rintro (rfl | ⟨z, h | h⟩)
    · rfl
    · rw [h.1, h.2, sphereCutZero_fold, sphereCutZero_fold]
    · rw [h.1, h.2, sphereCutZero_fold, sphereCutZero_fold]

def sphereCutKernelQuotientHomeomorph (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource) :
    Quotient (Setoid.ker (sphereCutFold c)) ≃ₜ W.Carrier := by
  letI := sphereCutCompactSpace c hs
  let f : Quotient (Setoid.ker (sphereCutFold c)) → W.Carrier :=
    Quotient.lift (sphereCutFold c) (fun x y h => h)
  have hi : Injective f := by
    intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro a b he
    exact Quotient.sound he
  have hj : Surjective f := by
    intro x
    obtain ⟨y, hy⟩ := sphereCut_projection_surjective c x
    exact ⟨Quotient.mk'' y, hy⟩
  have hc : Continuous f := (sphereCutFold_continuous c).quotient_lift _
  exact (Equiv.ofBijective f ⟨hi, hj⟩).toHomeomorphOfContinuousClosed hc hc.isClosedMap

theorem sphereCutKernelQuotientHomeomorph_apply (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource) (x : SphereCutSpace c) :
    sphereCutKernelQuotientHomeomorph c hs (Quotient.mk'' x) = sphereCutFold c x := rfl

def sphereCutRetainedCollar (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target)
    {n : ℕ} (E : BoundaryTori W n) (i : Fin n) :
    PartialDiffeomorph halfCollarModel (sphereCutCarrier c hs hd).model
      (Torus × EuclideanHalfSpace 1) (sphereCutCarrier c hs hd).Carrier ∞ :=
  (E.collar i).trans (sphereCutAmbientPartialDiffeomorph c hs hd)

theorem sphereCutOldPoint_offZero (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    {n : ℕ} (E : BoundaryTori W n)
    (havoid : ∀ i j, Disjoint (E.collar i).target (c j).target)
    (i : Fin n) {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ (E.collar i).source) :
    E.collar i p ∉ sphereCutAmbientZero c := by
  intro hzero
  obtain ⟨j, z, he⟩ := mem_iUnion.mp hzero
  have hz : (z, (0 : ℝ)) ∈ (c j).source := by
    rw [hs j]
    exact ⟨mem_univ _, by norm_num, by norm_num⟩
  exact disjoint_left.mp (havoid i j) ((E.collar i).map_source hp)
    (he ▸ (c j).map_source hz)

theorem sphereCutRetainedCollar_source (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target)
    {n : ℕ} (E : BoundaryTori W n)
    (havoid : ∀ i j, Disjoint (E.collar i).target (c j).target) (i : Fin n) :
    (sphereCutRetainedCollar c hs hd E i).source = halfCollarSource := by
  ext p
  constructor
  · intro hp
    exact (E.source_eq i).subset hp.1
  · intro hp
    have hps : p ∈ (E.collar i).source := (E.source_eq i).symm.subset hp
    exact ⟨hps, (sphereCutAmbientPartialDiffeomorph_source c hs hd).symm.subset
      (sphereCutOldPoint_offZero c hs E havoid i hps)⟩

theorem sphereCutRetainedCollar_fold (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target)
    {n : ℕ} (E : BoundaryTori W n)
    (havoid : ∀ i j, Disjoint (E.collar i).target (c j).target) (i : Fin n)
    (p : Torus × EuclideanHalfSpace 1) (hp : p ∈ halfCollarSource) :
    sphereCutFold c (sphereCutRetainedCollar c hs hd E i p) = E.collar i p :=
  sphereCutAmbientPartialDiffeomorph_fold c hs hd (E.collar i p)
    (sphereCutOldPoint_offZero c hs E havoid i ((E.source_eq i).symm.subset hp))

def sphereCutRetainedTori (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target)
    {n : ℕ} (E : BoundaryTori W n)
    (havoid : ∀ i j, Disjoint (E.collar i).target (c j).target) :
    BoundaryTori (sphereCutCarrier c hs hd) n where
  collar := sphereCutRetainedCollar c hs hd E
  source_eq := sphereCutRetainedCollar_source c hs hd E havoid
  boundary_zero i t := by
    have hp : (t, halfZero) ∈ halfCollarSource := by change (0 : ℝ) < 1; norm_num
    have hf := sphereCutRetainedCollar_fold c hs hd E havoid i (t, halfZero) hp
    exact (sphereCutCarrier_boundary_iff c hs hd _).mpr (Or.inl (hf ▸ E.boundary_zero i t))
  disjoint := by
    intro i j hij
    apply disjoint_left.mpr
    intro x hix hjx
    let e := sphereCutRetainedCollar c hs hd E i
    let f := sphereCutRetainedCollar c hs hd E j
    have hi : e.symm x ∈ halfCollarSource :=
      (sphereCutRetainedCollar_source c hs hd E havoid i).subset (e.map_target hix)
    have hj : f.symm x ∈ halfCollarSource :=
      (sphereCutRetainedCollar_source c hs hd E havoid j).subset (f.map_target hjx)
    have hei := sphereCutRetainedCollar_fold c hs hd E havoid i (e.symm x) hi
    have hej := sphereCutRetainedCollar_fold c hs hd E havoid j (f.symm x) hj
    change sphereCutFold c (e (e.symm x)) = E.collar i (e.symm x) at hei
    change sphereCutFold c (f (f.symm x)) = E.collar j (f.symm x) at hej
    have heix : e (e.symm x) = x := e.right_inv hix
    have hejx : f (f.symm x) = x := f.right_inv hjx
    rw [heix] at hei
    rw [hejx] at hej
    exact disjoint_left.mp (E.disjoint hij)
      (hei ▸ (E.collar i).map_source ((E.source_eq i).symm.subset hi))
      (hej ▸ (E.collar j).map_source ((E.source_eq j).symm.subset hj))


theorem sphereCutFullCollar_opposite_disjoint (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target) (j : Fin 1) :
    Disjoint (sphereCutFullCollar c hs hd j false).target
      (sphereCutFullCollar c hs hd j true).target := by
  apply disjoint_left.mpr
  intro x hfalse htrue
  let e := sphereCutFullCollar c hs hd j false
  let f := sphereCutFullCollar c hs hd j true
  let p := e.symm x
  let q := f.symm x
  have hp : p ∈ sphereHalfCollarSource :=
    (sphereCutFullCollar_source c hs hd j false).subset (e.map_target hfalse)
  have hq : q ∈ sphereHalfCollarSource :=
    (sphereCutFullCollar_source c hs hd j true).subset (f.map_target htrue)
  have he := sphereCutFullCollar_fold c hs hd j false p hp
  have hf := sphereCutFullCollar_fold c hs hd j true q hq
  change sphereCutFold c (e p) = c j (sphereCutHalfSigned false p) at he
  change sphereCutFold c (f q) = c j (sphereCutHalfSigned true q) at hf
  have hep : e p = x := e.right_inv hfalse
  have hfq : f q = x := f.right_inv htrue
  rw [hep] at he
  rw [hfq] at hf
  have hc := (c j).injOn (sphereCutFullHalfSigned_source c hs j false p hp)
    (sphereCutFullHalfSigned_source c hs j true q hq) (he.symm.trans hf)
  have hr : p.2.val 0 = -q.2.val 0 := congrArg Prod.snd hc
  have hp0 : p.2.val 0 = 0 := by linarith [p.2.property, q.2.property]
  have hq0 : q.2.val 0 = 0 := by linarith [p.2.property, q.2.property]
  have hpz : p.2 = halfZero := halfSpaceOneHomeomorph.injective (Subtype.ext hp0)
  have hqz : q.2 = halfZero := halfSpaceOneHomeomorph.injective (Subtype.ext hq0)
  have hex : e (p.1, halfZero) = x := by
    change e (p.1, p.2) = x at hep
    simpa only [hpz] using hep
  have hfx : f (q.1, halfZero) = x := by
    change f (q.1, q.2) = x at hfq
    simpa only [hqz] using hfq
  change sphereCutFullCollar c hs hd j false (p.1, halfZero) = x at hex
  change sphereCutFullCollar c hs hd j true (q.1, halfZero) = x at hfx
  rw [sphereCutFullCollar_zero] at hex hfx
  exact sphereCutZero_ne c j q.1 p.1 (hfx.trans hex.symm)

theorem sphereCutRetained_full_disjoint (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target)
    {n : ℕ} (E : BoundaryTori W n)
    (havoid : ∀ i j, Disjoint (E.collar i).target (c j).target) (i : Fin n)
    (j : Fin 1) (b : Bool) :
    Disjoint (sphereCutRetainedCollar c hs hd E i).target
      (sphereCutFullCollar c hs hd j b).target := by
  apply disjoint_left.mpr
  intro x hix hjx
  let e := sphereCutRetainedCollar c hs hd E i
  let f := sphereCutFullCollar c hs hd j b
  have hp : e.symm x ∈ halfCollarSource :=
    (sphereCutRetainedCollar_source c hs hd E havoid i).subset (e.map_target hix)
  have hq : f.symm x ∈ sphereHalfCollarSource :=
    (sphereCutFullCollar_source c hs hd j b).subset (f.map_target hjx)
  have he := sphereCutRetainedCollar_fold c hs hd E havoid i (e.symm x) hp
  have hf := sphereCutFullCollar_fold c hs hd j b (f.symm x) hq
  change sphereCutFold c (e (e.symm x)) = E.collar i (e.symm x) at he
  change sphereCutFold c (f (f.symm x)) = c j (sphereCutHalfSigned b (f.symm x)) at hf
  have her : e (e.symm x) = x := e.right_inv hix
  have hfr : f (f.symm x) = x := f.right_inv hjx
  rw [her] at he
  rw [hfr] at hf
  exact disjoint_left.mp (havoid i j)
    (he ▸ (E.collar i).map_source ((E.source_eq i).symm.subset hp))
    (hf ▸ (c j).map_source (sphereCutFullHalfSigned_source c hs j b (f.symm x) hq))

def sphereCutBoundarySide (i : Fin 2) : Bool := decide (i.val ≠ 0)

set_option backward.isDefEq.respectTransparency false in
theorem sphereCutRetainedTori_exhaust (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target)
    (hI : ∀ j, (c j).target ⊆ W.interior)
    {n : ℕ} (E : BoundaryTori W n) (hE : W.model.boundary W.Carrier = E.image)
    (havoid : ∀ i j, Disjoint (E.collar i).target (c j).target) :
    (sphereCutCarrier c hs hd).model.boundary (sphereCutCarrier c hs hd).Carrier =
      (sphereCutRetainedTori c hs hd E havoid).image ∪
        ⋃ i : Fin 2, range (fun z => sphereCutFullCollar c hs hd 0
          (sphereCutBoundarySide i) (z, halfZero)) := by
  ext x
  constructor
  · intro hx
    rcases (sphereCutCarrier_boundary_iff c hs hd x).mp hx with hold | hnew
    · change sphereCutFold c x ∈ W.model.boundary W.Carrier at hold
      rw [hE] at hold
      obtain ⟨i, t, ht⟩ := mem_iUnion.mp hold
      have hp : (t, halfZero) ∈ halfCollarSource := by change (0 : ℝ) < 1; norm_num
      let y := sphereCutRetainedCollar c hs hd E i (t, halfZero)
      have hy : sphereCutFold c y = E.collar i (t, halfZero) :=
        sphereCutRetainedCollar_fold c hs hd E havoid i _ hp
      have hxoff : x ∈ sphereCutOffZero c := by
        intro hz
        obtain ⟨j, z, hzj⟩ := mem_iUnion.mp hz
        have hzS : (z, (0 : ℝ)) ∈ (c j).source := by
          rw [hs j]
          exact ⟨mem_univ _, by norm_num, by norm_num⟩
        have hi := hI j ((c j).map_source hzS)
        have hb : W.model.IsBoundaryPoint (c j (z, 0)) := by
          change c j (z, 0) = sphereCutFold c x at hzj
          rw [hzj]
          rw [← hE] at hold
          exact hold
        exact (W.model.isInteriorPoint_iff_not_isBoundaryPoint _).mp hi hb
      have hyoff : y ∈ sphereCutOffZero c := by
        change sphereCutFold c y ∉ sphereCutAmbientZero c
        rw [hy]
        exact sphereCutOldPoint_offZero c hs E havoid i ((E.source_eq i).symm.subset hp)
      have hyx : y = x := sphereCutFold_injOn_offZero c hs hd hyoff hxoff (hy.trans ht)
      exact Or.inl (mem_iUnion.mpr ⟨i, t, hyx⟩)
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hnew
      obtain ⟨b, z, rfl⟩ := mem_iUnion.mp hj
      have hj0 : j = 0 := Subsingleton.elim j 0
      subst j
      right
      cases b
      · exact mem_iUnion.mpr ⟨0, z, sphereCutFullCollar_zero c hs hd 0 false z⟩
      · exact mem_iUnion.mpr ⟨1, z, sphereCutFullCollar_zero c hs hd 0 true z⟩
  · rintro (hold | hnew)
    · obtain ⟨i, t, rfl⟩ := mem_iUnion.mp hold
      exact (sphereCutRetainedTori c hs hd E havoid).boundary_zero i t
    · obtain ⟨i, z, rfl⟩ := mem_iUnion.mp hnew
      change (sphereCutCarrier c hs hd).model.IsBoundaryPoint
        (sphereCutFullCollar c hs hd 0 (sphereCutBoundarySide i) (z, halfZero))
      rw [sphereCutFullCollar_zero]
      exact sphereCutZero_isBoundaryPoint c hs hd 0 (sphereCutBoundarySide i) z

def sphereCutMixedBoundary (c : SphereCutSignedCollars W)
    (hs : ∀ j, (c j).source = sphereSignedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target)
    (hI : ∀ j, (c j).target ⊆ W.interior)
    {n : ℕ} (E : BoundaryTori W n) (hE : W.model.boundary W.Carrier = E.image)
    (havoid : ∀ i j, Disjoint (E.collar i).target (c j).target) :
    MixedBoundaryCertificate (sphereCutCarrier c hs hd) where
  torusCount := n
  tori := sphereCutRetainedTori c hs hd E havoid
  sphereCount := 2
  sphere i := sphereCutFullCollar c hs hd 0 (sphereCutBoundarySide i)
  sphere_source i := sphereCutFullCollar_source c hs hd 0 (sphereCutBoundarySide i)
  sphere_disjoint := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact sphereCutFullCollar_opposite_disjoint c hs hd 0
    · exact (sphereCutFullCollar_opposite_disjoint c hs hd 0).symm
    · exact (hij rfl).elim
  sphere_zero_boundary i z := by
    rw [sphereCutFullCollar_zero]
    exact sphereCutZero_isBoundaryPoint c hs hd 0 (sphereCutBoundarySide i) z
  cross_disjoint i j := sphereCutRetained_full_disjoint c hs hd E havoid i 0
    (sphereCutBoundarySide j)
  exhausted := sphereCutRetainedTori_exhaust c hs hd hI E hE havoid


set_option backward.isDefEq.respectTransparency false in
theorem exists_sphereCutCarrier
    (W : CompactCarrier.{u})
    (d : PartialDiffeomorph sphereSignedCollarModel W.model
      (ClosureSphere.{u} × ℝ) W.Carrier ∞)
    (hs : d.source = sphereSignedCollarSource) (hI : d.target ⊆ W.interior)
    {n : ℕ} (E : BoundaryTori W n) (hE : W.model.boundary W.Carrier = E.image)
    (havoid : ∀ i, Disjoint (E.collar i).target d.target) :
    ∃ (C : CompactCarrier.{u}) (B : MixedBoundaryCertificate C)
      (hn : B.torusCount = n) (h2 : B.sphereCount = 2) (fold : C.Carrier → W.Carrier),
      C.kind = .withBoundary ∧ ContMDiff C.model W.model ∞ fold ∧ Surjective fold ∧
      (∀ x, ∃ A : TangentSpace C.model x ≃ₗ[ℝ] TangentSpace W.model (fold x),
        (∀ v, A v = mfderiv C.model W.model fold x v) ∧
        Orientation.map (Fin 3) A (C.orientation.orientation x) =
          W.orientation.orientation (fold x)) ∧
      (∀ i p, p ∈ halfCollarSource →
        fold (B.tori.collar (Fin.cast hn.symm i) p) = E.collar i p) ∧
      (∀ i z s (hs0 : 0 ≤ s), s < 1 →
        fold (B.sphere (Fin.cast h2.symm i) (z, halfPoint s hs0)) =
          d (z, if i.val = 0 then s else -s)) ∧
      (∀ x y, fold x = fold y ↔ x = y ∨ ∃ z,
        (x = B.sphere (Fin.cast h2.symm 0) (z, halfZero) ∧
          y = B.sphere (Fin.cast h2.symm 1) (z, halfZero)) ∨
        (x = B.sphere (Fin.cast h2.symm 1) (z, halfZero) ∧
          y = B.sphere (Fin.cast h2.symm 0) (z, halfZero))) ∧
      ∃ ρ : Quotient (Setoid.ker fold) ≃ₜ W.Carrier,
        ∀ x : C.Carrier, ρ (Quotient.mk'' x) = fold x
 := by
  let c : SphereCutSignedCollars W := Function.const (Fin 1) d
  have hs' : ∀ j, (c j).source = sphereSignedCollarSource := by
    intro j
    simpa only [c, Function.const] using hs
  have hd : Pairwise fun i j => Disjoint (c i).target (c j).target := by
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  have hI' : ∀ j, (c j).target ⊆ W.interior := by
    intro j
    simpa only [c, Function.const] using hI
  have havoid' : ∀ i j, Disjoint (E.collar i).target (c j).target := by
    intro i j
    simpa only [c, Function.const] using havoid i
  let atlas := sphereCutChartedSpace c hs' hd
  let smooth := sphereCutIsManifold c hs' hd
  let C := sphereCutCarrier c hs' hd
  let B := sphereCutMixedBoundary c hs' hd hI' E hE havoid'
  refine ⟨C, B, rfl, rfl, sphereCutFold c, rfl,
    sphereCutFold_smooth c hs' hd, sphereCut_projection_surjective c, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    let A := Manifold.differentialEquivOfBijective (𝓡∂ 3) W.model
      (sphereCutFold c) (sphereCutFold_mfderiv_bijective c hs' hd) x
    exact ⟨A.toLinearEquiv, fun v => rfl, sphereCutFold_orientation_map c hs' hd x⟩
  · intro i p hp
    exact sphereCutRetainedCollar_fold c hs' hd E havoid' i p hp
  · intro i z s hs0 hs1
    have hp : (z, halfPoint s hs0) ∈ sphereHalfCollarSource := hs1
    have hf := sphereCutFullCollar_fold c hs' hd 0 (sphereCutBoundarySide i) _ hp
    change sphereCutFold c (sphereCutFullCollar c hs' hd 0 (sphereCutBoundarySide i)
      (z, halfPoint s hs0)) = d (z, if i.val = 0 then s else -s)
    rw [hf]
    fin_cases i <;> rfl
  · intro x y
    change sphereCutFold c x = sphereCutFold c y ↔ x = y ∨ ∃ z,
      (x = sphereCutFullCollar c hs' hd 0 false (z, halfZero) ∧
        y = sphereCutFullCollar c hs' hd 0 true (z, halfZero)) ∨
      (x = sphereCutFullCollar c hs' hd 0 true (z, halfZero) ∧
        y = sphereCutFullCollar c hs' hd 0 false (z, halfZero))
    simpa only [sphereCutFullCollar_zero] using sphereCutFold_fibre_relation c hs' hd x y
  · exact ⟨sphereCutKernelQuotientHomeomorph c hs', fun x => rfl⟩

end GC.GraphManifold
