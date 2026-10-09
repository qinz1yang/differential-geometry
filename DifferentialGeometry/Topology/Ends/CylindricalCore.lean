import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Maps.Proper.Basic

noncomputable section

open Set

namespace DifferentialGeometry.Topology

def cylindricalCore {ι X : Type*} {C : ι → Type*}
    (e : ∀ i, C i × Ici (0 : ℝ) → X) (R : ι → ℝ) : Set X :=
  (⋃ i, e i '' {p | R i < p.2.val})ᶜ

theorem exists_retraction_cylindricalCore
    {ι X : Type*} [Finite ι] [TopologicalSpace X]
    {C : ι → Type*} [∀ i, TopologicalSpace (C i)]
    (e : ∀ i, C i × Ici (0 : ℝ) → X)
    (he : ∀ i, _root_.Topology.IsClosedEmbedding (e i))
    (hopen : ∀ i, IsOpen (e i '' {p | 0 < p.2.val}))
    (hdisjoint : Pairwise fun i j ↦ Disjoint (range (e i)) (range (e j)))
    (R : ι → ℝ) (hR : ∀ i, 0 ≤ R i) :
    ∃ r : C(X, X),
      (∀ i p, r (e i p) = e i (p.1, ⟨min p.2.val (R i), le_min p.2.property (hR i)⟩)) ∧
      EqOn r id (cylindricalCore e R) ∧ range r = cylindricalCore e R := by
  classical
  let E : (Σ i, C i × Ici (0 : ℝ)) → X := fun p ↦ e p.1 p.2
  have hE : Function.Injective E := by
    rintro ⟨i, p⟩ ⟨j, q⟩ hpq
    have hij : i = j := by
      by_contra hne
      exact Set.disjoint_left.mp (hdisjoint hne) ⟨p, rfl⟩ ⟨q, hpq.symm⟩
    subst j
    exact congrArg (Sigma.mk i) ((he i).injective hpq)
  let clamp (i : ι) (p : C i × Ici (0 : ℝ)) : C i × Ici (0 : ℝ) :=
    (p.1, ⟨min p.2.val (R i), le_min p.2.property (hR i)⟩)
  have hclamp (i : ι) : Continuous (clamp i) :=
    continuous_fst.prodMk
      (((continuous_subtype_val.comp continuous_snd).min continuous_const).subtype_mk _)
  let r : X → X := Function.extend E (fun p ↦ e p.1 (clamp p.1 p.2)) id
  have hformula (i : ι) (p : C i × Ici (0 : ℝ)) :
      r (e i p) = e i (clamp i p) := hE.extend_apply _ _ ⟨i, p⟩
  have hfix (S : ι → ℝ) (hS : ∀ i, S i ≤ R i) : EqOn r id (cylindricalCore e S) := by
    intro x hx
    by_cases hex : ∃ p, E p = x
    · obtain ⟨⟨i, p⟩, rfl⟩ := hex
      have hp : p.2.val ≤ S i := le_of_not_gt fun ht ↦
        hx (mem_iUnion.mpr ⟨i, p, ht, rfl⟩)
      rw [show E ⟨i, p⟩ = e i p from rfl, hformula]
      congr 1
      exact Prod.ext rfl (Subtype.ext (min_eq_left (hp.trans (hS i))))
    · exact Function.extend_apply' _ _ x hex
  let cover : Option ι → Set X
    | none => cylindricalCore e (fun _ ↦ 0)
    | some i => range (e i)
  have hcover : ⋃ i, cover i = univ := by
    apply eq_univ_of_forall
    intro x
    by_cases hx : ∃ i, x ∈ range (e i)
    · obtain ⟨i, hi⟩ := hx
      exact mem_iUnion.mpr ⟨some i, hi⟩
    · refine mem_iUnion.mpr ⟨none, ?_⟩
      rintro h
      obtain ⟨i, p, _, hp⟩ := mem_iUnion.mp h
      exact hx ⟨i, p, hp⟩
  have hclosed : ∀ i, IsClosed (cover i)
    | none => (isOpen_iUnion hopen).isClosed_compl
    | some i => (he i).isClosed_range
  have hcont : ∀ i, ContinuousOn r (cover i)
    | none => continuousOn_id.congr (hfix (fun _ ↦ 0) hR)
    | some i => by
      change ContinuousOn r (range (e i))
      rw [← image_univ]
      apply (he i).isInducing.continuousOn_image_iff.mpr
      have heq : r ∘ e i = e i ∘ clamp i := funext (hformula i)
      rw [heq]
      exact ((he i).continuous.comp (hclamp i)).continuousOn
  have hr : Continuous r := (locallyFinite_of_finite cover).continuous hcover hclosed hcont
  have hmaps (x : X) : r x ∈ cylindricalCore e R := by
    intro hx
    obtain ⟨j, q, hq, hqr⟩ := mem_iUnion.mp hx
    by_cases hex : ∃ p, E p = x
    · obtain ⟨⟨i, p⟩, rfl⟩ := hex
      rw [show E ⟨i, p⟩ = e i p from rfl, hformula] at hqr
      have hij : i = j := by
        by_contra hne
        exact Set.disjoint_left.mp (hdisjoint hne) ⟨clamp i p, rfl⟩ ⟨q, hqr⟩
      subst j
      have ht := congrArg (fun z : C i × Ici (0 : ℝ) ↦ z.2.val) ((he i).injective hqr)
      change q.2.val = min p.2.val (R i) at ht
      exact hq.not_ge (ht ▸ min_le_right p.2.val (R i))
    · have hrx : r x = x := Function.extend_apply' _ _ x hex
      exact hex ⟨⟨j, q⟩, hqr.trans hrx⟩
  refine ⟨⟨r, hr⟩, hformula, hfix R (fun _ ↦ le_rfl), ?_⟩
  apply Subset.antisymm
  · rintro x ⟨y, rfl⟩
    exact hmaps y
  · intro x hx
    exact ⟨x, hfix R (fun _ ↦ le_rfl) hx⟩

theorem isClosed_cylindricalCore
    {ι X : Type*} [TopologicalSpace X]
    {C : ι → Type*} [∀ i, TopologicalSpace (C i)]
    (e : ∀ i, C i × Ici (0 : ℝ) → X)
    (he : ∀ i, _root_.Topology.IsClosedEmbedding (e i))
    (hopen : ∀ i, IsOpen (e i '' {p | 0 < p.2.val}))
    (R : ι → ℝ) (hR : ∀ i, 0 ≤ R i) : IsClosed (cylindricalCore e R) := by
  have htail (i : ι) : e i '' {p | R i < p.2.val} =
      (e i '' {p | 0 < p.2.val}) \ (e i '' {p | p.2.val ≤ R i}) := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨⟨p, (hR i).trans_lt hp, rfl⟩, ?_⟩
      rintro ⟨q, hq, hqp⟩
      have h := (he i).injective hqp
      change R i < p.2.val at hp
      change q.2.val ≤ R i at hq
      exact hp.not_ge (h ▸ hq)
    · rintro ⟨⟨p, hp, rfl⟩, hn⟩
      refine ⟨p, ?_, rfl⟩
      change R i < p.2.val
      exact lt_of_not_ge fun h ↦ hn ⟨p, h, rfl⟩
  have hopenR (i : ι) : IsOpen (e i '' {p | R i < p.2.val}) := by
    rw [htail]
    exact (hopen i).sdiff ((he i).isClosedMap _
      (isClosed_le (continuous_subtype_val.comp continuous_snd) continuous_const))
  exact (isOpen_iUnion hopenR).isClosed_compl

theorem isCompact_cylindricalCore
    {ι X : Type*} [Finite ι] [TopologicalSpace X]
    {C : ι → Type*} [∀ i, TopologicalSpace (C i)] [∀ i, CompactSpace (C i)]
    (e : ∀ i, C i × Ici (0 : ℝ) → X)
    (he : ∀ i, _root_.Topology.IsClosedEmbedding (e i))
    (hopen : ∀ i, IsOpen (e i '' {p | 0 < p.2.val}))
    (hcore : IsCompact (cylindricalCore e (fun _ ↦ 0)))
    (R : ι → ℝ) (hR : ∀ i, 0 ≤ R i) : IsCompact (cylindricalCore e R) := by
  have hclosed := isClosed_cylindricalCore e he hopen R hR
  have hslab (i : ι) : IsCompact (e i '' {p | p.2.val ≤ R i}) := by
    apply IsCompact.image _ (he i).continuous
    have ht : IsCompact {t : Ici (0 : ℝ) | t.val ≤ R i} := by
      have h := (isClosed_Ici : IsClosed (Ici (0 : ℝ))).isClosedEmbedding_subtypeVal.isCompact_preimage
        (isCompact_Icc : IsCompact (Icc (0 : ℝ) (R i)))
      convert h using 1
      ext t
      exact ⟨fun ht ↦ ⟨t.property, ht⟩, fun ht ↦ ht.2⟩
    convert (isCompact_univ : IsCompact (univ : Set (C i))).prod ht using 1
    ext p
    simp only [mem_ofPred_eq, mem_prod, mem_univ, true_and]
  apply (hcore.union (isCompact_iUnion hslab)).of_isClosed_subset hclosed
  intro x hx
  by_cases hx0 : x ∈ cylindricalCore e (fun _ ↦ 0)
  · exact Or.inl hx0
  · have hxU : x ∈ ⋃ i, e i '' {p | 0 < p.2.val} := not_not.mp hx0
    obtain ⟨i, p, hp, rfl⟩ := mem_iUnion.mp hxU
    refine Or.inr (mem_iUnion.mpr ⟨i, p, ?_, rfl⟩)
    change p.2.val ≤ R i
    exact le_of_not_gt fun h ↦ hx (mem_iUnion.mpr ⟨i, p, h, rfl⟩)

theorem isConnected_cylindricalCore
    {ι X : Type*} [Finite ι] [TopologicalSpace X] [ConnectedSpace X]
    {C : ι → Type*} [∀ i, TopologicalSpace (C i)]
    (e : ∀ i, C i × Ici (0 : ℝ) → X)
    (he : ∀ i, _root_.Topology.IsClosedEmbedding (e i))
    (hopen : ∀ i, IsOpen (e i '' {p | 0 < p.2.val}))
    (hdisjoint : Pairwise fun i j ↦ Disjoint (range (e i)) (range (e j)))
    (R : ι → ℝ) (hR : ∀ i, 0 ≤ R i) : IsConnected (cylindricalCore e R) := by
  obtain ⟨r, _, _, hr⟩ := exists_retraction_cylindricalCore e he hopen hdisjoint R hR
  rw [← hr]
  exact isConnected_range r.continuous

end DifferentialGeometry.Topology
