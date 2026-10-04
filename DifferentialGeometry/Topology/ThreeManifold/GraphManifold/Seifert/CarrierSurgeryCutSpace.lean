import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.LinearSeams
import DifferentialGeometry.Topology.ThreeManifold.TorusCut.NoCuts
import DifferentialGeometry.Topology.Manifold.FiniteCollarBoundaryAtlas

/-!
# Actual compact carrier underlying cutting along signed torus collars

A finite union in the product of the known carrier and a finite real coordinate space duplicates
only the zero levels. Each side has its own nonzero label near zero; the smooth labels vanish at
the outer edge of its compact half band. Projection reconstructs the given carrier.
-/

set_option autoImplicit false
noncomputable section
open Set Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology
universe u
namespace GC.Seifert

variable {Q : ConnectedClosedOrientedManifold.{u} 3} {n : ℕ}

def carrierCutSign (b : Bool) (s : ℝ) : ℝ := if b then -s else s

def carrierCutTag (j : Fin n) (b : Bool) (s : ℝ) : Fin n → ℝ :=
  fun i => if i = j then carrierCutSign b (1 - seamCut s) else 0

def carrierCutBand (c : Fin n → PartialDiffeomorph signedCollarModel (𝓡 3)
    (Torus × ℝ) Q.Carrier ∞) (j : Fin n) (b : Bool) (p : Torus × ℝ) :
    Q.Carrier × (Fin n → ℝ) :=
  (c j (p.1, carrierCutSign b p.2), carrierCutTag j b p.2)

def carrierCutOutside (c : Fin n → PartialDiffeomorph signedCollarModel (𝓡 3)
    (Torus × ℝ) Q.Carrier ∞) : Set Q.Carrier :=
  (⋃ j, c j '' ((univ : Set Torus) ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2)))ᶜ

def carrierCutSet (c : Fin n → PartialDiffeomorph signedCollarModel (𝓡 3)
    (Torus × ℝ) Q.Carrier ∞) : Set (Q.Carrier × (Fin n → ℝ)) :=
  (fun x : Q.Carrier => (x, (0 : Fin n → ℝ))) '' carrierCutOutside c ∪
    ⋃ j, ⋃ b : Bool, carrierCutBand c j b ''
      ((univ : Set Torus) ×ˢ Icc (0 : ℝ) (1 / 2))

abbrev CarrierCutSpace (c : Fin n → PartialDiffeomorph signedCollarModel (𝓡 3)
    (Torus × ℝ) Q.Carrier ∞) := carrierCutSet c

theorem carrierCutOutside_closed (c : Fin n → PartialDiffeomorph signedCollarModel (𝓡 3)
    (Torus × ℝ) Q.Carrier ∞) (hs : ∀ j, (c j).source = signedCollarSource) :
    IsClosed (carrierCutOutside c) := by
  apply IsOpen.isClosed_compl
  apply isOpen_iUnion
  intro j
  apply (c j).toOpenPartialHomeomorph.isOpen_image_of_subset_source
    (isOpen_univ.prod isOpen_Ioo)
  intro p hp
  change p ∈ (c j).source
  rw [hs j]
  change -1 < p.2 ∧ p.2 < 1
  constructor <;> linarith [hp.2.1, hp.2.2]

theorem carrierCutBand_continuousOn
    (c : Fin n → PartialDiffeomorph signedCollarModel (𝓡 3) (Torus × ℝ) Q.Carrier ∞)
    (hs : ∀ j, (c j).source = signedCollarSource) (j : Fin n) (b : Bool) :
    ContinuousOn (carrierCutBand c j b) ((univ : Set Torus) ×ˢ Icc (0 : ℝ) (1 / 2)) := by
  have hsign : Continuous (carrierCutSign b) := by
    cases b
    · exact continuous_id
    · exact continuous_neg
  have hp : Continuous fun p : Torus × ℝ => (p.1, carrierCutSign b p.2) :=
    continuous_fst.prodMk (hsign.comp continuous_snd)
  have hmap : ∀ p ∈ ((univ : Set Torus) ×ˢ Icc (0 : ℝ) (1 / 2)),
      (p.1, carrierCutSign b p.2) ∈ (c j).source := by
    intro p h
    rw [hs j]
    change -1 < carrierCutSign b p.2 ∧ carrierCutSign b p.2 < 1
    cases b <;> simp only [carrierCutSign, Bool.false_eq_true, ↓reduceIte] <;>
      constructor <;> linarith [h.2.1, h.2.2]
  have htag : Continuous fun p : Torus × ℝ => carrierCutTag j b p.2 := by
    apply continuous_pi
    intro i
    by_cases hi : i = j
    · simp only [carrierCutTag, hi, ↓reduceIte]
      exact hsign.comp ((continuous_const.sub contDiff_seamCut.continuous).comp continuous_snd)
    · simp only [carrierCutTag, hi, ↓reduceIte]
      exact continuous_const
  exact ((c j).contMDiffOn.continuousOn.comp hp.continuousOn hmap).prodMk
    htag.continuousOn

theorem carrierCutSet_compact (c : Fin n → PartialDiffeomorph signedCollarModel (𝓡 3)
    (Torus × ℝ) Q.Carrier ∞) (hs : ∀ j, (c j).source = signedCollarSource) :
    IsCompact (carrierCutSet c) := by
  apply IsCompact.union
  · exact (carrierCutOutside_closed c hs).isCompact.image
      (continuous_id.prodMk continuous_const)
  · apply isCompact_iUnion
    intro j
    apply isCompact_iUnion
    intro b
    exact (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
      (carrierCutBand_continuousOn c hs j b)

theorem carrierCut_projection_surjective
    (c : Fin n → PartialDiffeomorph signedCollarModel (𝓡 3) (Torus × ℝ) Q.Carrier ∞) :
    Function.Surjective (fun x : CarrierCutSpace c => x.val.1) := by
  intro x
  by_cases hx : x ∈ carrierCutOutside c
  · exact ⟨⟨(x, 0), Or.inl ⟨x, hx, rfl⟩⟩, rfl⟩
  · have hu : x ∈ ⋃ j, c j '' ((univ : Set Torus) ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2)) :=
      not_not.mp hx
    obtain ⟨j, p, hp, hpx⟩ := mem_iUnion.mp hu
    by_cases hneg : p.2 < 0
    · let q := (p.1, -p.2)
      have hq : q ∈ (univ : Set Torus) ×ˢ Icc (0 : ℝ) (1 / 2) :=
        ⟨mem_univ _, neg_nonneg.mpr hneg.le, by dsimp only [q]; linarith [hp.2.1]⟩
      refine ⟨⟨carrierCutBand c j true q,
        Or.inr (mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨true, q, hq, rfl⟩⟩)⟩, ?_⟩
      change c j (p.1, -(-p.2)) = x
      simpa only [neg_neg] using hpx
    · have hq : p ∈ (univ : Set Torus) ×ˢ Icc (0 : ℝ) (1 / 2) :=
        ⟨mem_univ _, le_of_not_gt hneg, hp.2.2.le⟩
      exact ⟨⟨carrierCutBand c j false p,
        Or.inr (mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨false, p, hq, rfl⟩⟩)⟩, hpx⟩

theorem carrierCutCompactSpace
    (c : Fin n → PartialDiffeomorph signedCollarModel (𝓡 3) (Torus × ℝ) Q.Carrier ∞)
    (hs : ∀ j, (c j).source = signedCollarSource) : CompactSpace (CarrierCutSpace c) :=
  isCompact_iff_compactSpace.mp (carrierCutSet_compact c hs)

def carrierCutFold
    (c : Fin n → PartialDiffeomorph signedCollarModel (𝓡 3) (Torus × ℝ) Q.Carrier ∞) :
    CarrierCutSpace c → Q.Carrier := fun x => x.val.1

theorem carrierCutFold_continuous
    (c : Fin n → PartialDiffeomorph signedCollarModel (𝓡 3) (Torus × ℝ) Q.Carrier ∞) :
    Continuous (carrierCutFold c) := continuous_subtype_val.fst

theorem carrierCutFold_isQuotientMap
    (c : Fin n → PartialDiffeomorph signedCollarModel (𝓡 3) (Torus × ℝ) Q.Carrier ∞)
    (hs : ∀ j, (c j).source = signedCollarSource) :
    _root_.Topology.IsQuotientMap (carrierCutFold c) := by
  let : CompactSpace (CarrierCutSpace c) := carrierCutCompactSpace c hs
  exact (carrierCutFold_continuous c).isClosedMap.isQuotientMap
    (carrierCutFold_continuous c) (carrierCut_projection_surjective c)

def carrierCutZero
    (c : Fin n → PartialDiffeomorph signedCollarModel (𝓡 3) (Torus × ℝ) Q.Carrier ∞)
    (j : Fin n) (b : Bool) (t : Torus) : CarrierCutSpace c :=
  ⟨carrierCutBand c j b (t, 0), Or.inr (mem_iUnion.mpr ⟨j,
    mem_iUnion.mpr ⟨b, (t, 0), ⟨mem_univ _, le_rfl, by norm_num⟩, rfl⟩⟩)⟩

theorem carrierCutZero_fold
    (c : Fin n → PartialDiffeomorph signedCollarModel (𝓡 3) (Torus × ℝ) Q.Carrier ∞)
    (j : Fin n) (b : Bool) (t : Torus) : carrierCutFold c (carrierCutZero c j b t) =
      c j (t, 0) := by
  cases b <;> simp [carrierCutFold, carrierCutZero, carrierCutBand, carrierCutSign]

theorem carrierCutZero_ne
    (c : Fin n → PartialDiffeomorph signedCollarModel (𝓡 3) (Torus × ℝ) Q.Carrier ∞)
    (j : Fin n) (t t' : Torus) : carrierCutZero c j true t ≠ carrierCutZero c j false t' := by
  intro h
  have he := congrArg (fun x : CarrierCutSpace c => x.val.2 j) h
  have hc : seamCut 0 = 0 := seamCut_of_le (by norm_num)
  simp [carrierCutZero, carrierCutBand, carrierCutTag, carrierCutSign, hc] at he
  norm_num at he

theorem carrierCutOutside_coordinate
    (c : Fin n → PartialDiffeomorph signedCollarModel (𝓡 3) (Torus × ℝ) Q.Carrier ∞)
    (hs : ∀ j, (c j).source = signedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target)
    (j : Fin n) (p : Torus × ℝ) (hp : p ∈ (c j).source) :
    c j p ∈ carrierCutOutside c ↔ ¬ (-(1 / 2 : ℝ) < p.2 ∧ p.2 < 1 / 2) := by
  have hi : c j p ∈ ⋃ k, c k '' ((univ : Set Torus) ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2)) ↔
      -(1 / 2 : ℝ) < p.2 ∧ p.2 < 1 / 2 := by
    constructor
    · intro h
      obtain ⟨k, q, hq, he⟩ := mem_iUnion.mp h
      have hqsrc : q ∈ (c k).source := by
        rw [hs k]
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

theorem carrierCutTag_zero_of_ge (j : Fin n) (b : Bool) {s : ℝ} (hs : 1 / 2 ≤ s) :
    carrierCutTag j b s = 0 := by
  ext i
  simp [carrierCutTag, carrierCutSign, seamCut_of_ge hs]

theorem carrierCutBand_mem_of_height
    (c : Fin n → PartialDiffeomorph signedCollarModel (𝓡 3) (Torus × ℝ) Q.Carrier ∞)
    (hs : ∀ j, (c j).source = signedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target)
    (j : Fin n) (b : Bool) (p : Torus × ℝ) (hp0 : 0 ≤ p.2) (hp1 : p.2 < 1) :
    carrierCutBand c j b p ∈ carrierCutSet c := by
  by_cases hsmall : p.2 ≤ 1 / 2
  · exact Or.inr (mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨b, p,
      ⟨mem_univ _, hp0, hsmall⟩, rfl⟩⟩)
  · have hsrc : (p.1, carrierCutSign b p.2) ∈ (c j).source := by
      rw [hs j]
      change -1 < carrierCutSign b p.2 ∧ carrierCutSign b p.2 < 1
      cases b <;> simp only [carrierCutSign, Bool.false_eq_true, ↓reduceIte] <;>
        constructor <;> linarith
    have hout : c j (p.1, carrierCutSign b p.2) ∈ carrierCutOutside c := by
      apply (carrierCutOutside_coordinate c hs hd j _ hsrc).mpr
      cases b <;> simp only [carrierCutSign, Bool.false_eq_true, ↓reduceIte] <;>
        intro h <;> linarith [h.1, h.2, lt_of_not_ge hsmall]
    refine Or.inl ⟨c j (p.1, carrierCutSign b p.2), hout, ?_⟩
    exact Prod.ext rfl (carrierCutTag_zero_of_ge j b (lt_of_not_ge hsmall).le).symm

def carrierCutHalfLift
    (c : Fin n → PartialDiffeomorph signedCollarModel (𝓡 3) (Torus × ℝ) Q.Carrier ∞)
    (hs : ∀ j, (c j).source = signedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target)
    (j : Fin n) (b : Bool) (p : halfCollarSource) : CarrierCutSpace c :=
  ⟨carrierCutBand c j b (p.val.1, p.val.2.val 0),
    carrierCutBand_mem_of_height c hs hd j b _ (p.val.2.property) p.property⟩

theorem carrierCutHalfLift_fold
    (c : Fin n → PartialDiffeomorph signedCollarModel (𝓡 3) (Torus × ℝ) Q.Carrier ∞)
    (hs : ∀ j, (c j).source = signedCollarSource)
    (hd : Pairwise fun i j => Disjoint (c i).target (c j).target)
    (j : Fin n) (b : Bool) (p : halfCollarSource) :
    carrierCutFold c (carrierCutHalfLift c hs hd j b p) =
      c j (p.val.1, carrierCutSign b (p.val.2.val 0)) := rfl

theorem carrierCutZero_continuous
    (c : Fin n → PartialDiffeomorph signedCollarModel (𝓡 3) (Torus × ℝ) Q.Carrier ∞)
    (hs : ∀ j, (c j).source = signedCollarSource) (j : Fin n) (b : Bool) :
    Continuous (carrierCutZero c j b) := by
  apply Continuous.subtype_mk
  apply (carrierCutBand_continuousOn c hs j b).comp_continuous
    (continuous_id.prodMk continuous_const)
  intro t
  exact ⟨mem_univ _, le_rfl, by norm_num⟩

theorem carrierCutZero_injective
    (c : Fin n → PartialDiffeomorph signedCollarModel (𝓡 3) (Torus × ℝ) Q.Carrier ∞)
    (hs : ∀ j, (c j).source = signedCollarSource) (j : Fin n) (b : Bool) :
    Function.Injective (carrierCutZero c j b) := by
  intro t t' h
  have hh := congrArg (carrierCutFold c) h
  rw [carrierCutZero_fold, carrierCutZero_fold] at hh
  have hz (t : Torus) : (t, (0 : ℝ)) ∈ (c j).source := by
    rw [hs j]
    change -1 < (0 : ℝ) ∧ (0 : ℝ) < 1
    norm_num
  exact congrArg Prod.fst ((c j).toOpenPartialHomeomorph.injOn (hz t) (hz t') hh)

theorem carrierCutZero_isClosedEmbedding
    (c : Fin n → PartialDiffeomorph signedCollarModel (𝓡 3) (Torus × ℝ) Q.Carrier ∞)
    (hs : ∀ j, (c j).source = signedCollarSource) (j : Fin n) (b : Bool) :
    _root_.Topology.IsClosedEmbedding (carrierCutZero c j b) :=
  (carrierCutZero_continuous c hs j b).isClosedEmbedding (carrierCutZero_injective c hs j b)

end GC.Seifert
