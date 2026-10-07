import DifferentialGeometry.Topology.Ends.CylindricalCore
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Tactic.Ring

noncomputable section

open Set unitInterval

namespace DifferentialGeometry.Topology

theorem exists_deformation_retraction_cylindricalCore
    {ι X : Type*} [Finite ι] [TopologicalSpace X]
    {C : ι → Type*} [∀ i, TopologicalSpace (C i)]
    (e : ∀ i, C i × Ici (0 : ℝ) → X)
    (he : ∀ i, _root_.Topology.IsClosedEmbedding (e i))
    (hopen : ∀ i, IsOpen (e i '' {p | 0 < p.2.val}))
    (hdisjoint : Pairwise fun i j ↦ Disjoint (range (e i)) (range (e j)))
    (R : ι → ℝ) (hR : ∀ i, 0 ≤ R i) :
    ∃ r : C(X, X), range r = cylindricalCore e R ∧
      Nonempty ((ContinuousMap.id X).HomotopyRel r (cylindricalCore e R)) := by
  classical
  obtain ⟨r, hr, hfix, hrange⟩ := exists_retraction_cylindricalCore e he hopen hdisjoint R hR
  let E : (Σ i, C i × Ici (0 : ℝ)) → X := fun p ↦ e p.1 p.2
  have hE : Function.Injective E := by
    rintro ⟨i, p⟩ ⟨j, q⟩ hpq
    have hij : i = j := by
      by_contra hne
      exact Set.disjoint_left.mp (hdisjoint hne) ⟨p, rfl⟩ ⟨q, hpq.symm⟩
    subst j
    exact congrArg (Sigma.mk i) ((he i).injective hpq)
  let clamp (i : ι) (t : I) (p : C i × Ici (0 : ℝ)) : C i × Ici (0 : ℝ) :=
    (p.1, ⟨(1 - t.val) * p.2.val + t.val * min p.2.val (R i),
      add_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) p.2.property)
        (mul_nonneg t.property.1 (le_min p.2.property (hR i)))⟩)
  have hclamp (i : ι) : Continuous (fun q : I × (C i × Ici (0 : ℝ)) ↦
      clamp i q.1 q.2) := by
    exact (continuous_fst.comp continuous_snd).prodMk
      ((((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
        (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))).add
        ((continuous_subtype_val.comp continuous_fst).mul
          ((continuous_subtype_val.comp (continuous_snd.comp continuous_snd)).min
            continuous_const))).subtype_mk _)
  let H : I × X → X := fun q ↦
    Function.extend E (fun p ↦ e p.1 (clamp p.1 q.1 p.2)) id q.2
  have hformula (t : I) (i : ι) (p : C i × Ici (0 : ℝ)) :
      H (t, e i p) = e i (clamp i t p) := hE.extend_apply _ _ ⟨i, p⟩
  have hfixed (t : I) (S : ι → ℝ) (hS : ∀ i, S i ≤ R i)
      {x : X} (hx : x ∈ cylindricalCore e S) : H (t, x) = x := by
    by_cases hex : ∃ p, E p = x
    · obtain ⟨⟨i, p⟩, rfl⟩ := hex
      have hp : p.2.val ≤ S i := le_of_not_gt fun ht ↦
        hx (mem_iUnion.mpr ⟨i, p, ht, rfl⟩)
      rw [show E ⟨i, p⟩ = e i p from rfl, hformula]
      congr 1
      refine Prod.ext (by rfl) ?_
      apply Subtype.ext
      change (1 - t.val) * p.2.val + t.val * min p.2.val (R i) = p.2.val
      rw [min_eq_left (hp.trans (hS i))]
      ring
    · exact Function.extend_apply' _ _ x hex
  let cover : Option ι → Set (I × X)
    | none => Prod.snd ⁻¹' cylindricalCore e (fun _ ↦ 0)
    | some i => Prod.snd ⁻¹' range (e i)
  have hcover : ⋃ i, cover i = univ := by
    apply eq_univ_of_forall
    intro q
    by_cases hx : ∃ i, q.2 ∈ range (e i)
    · obtain ⟨i, hi⟩ := hx
      exact mem_iUnion.mpr ⟨some i, hi⟩
    · refine mem_iUnion.mpr ⟨none, ?_⟩
      rintro h
      obtain ⟨i, p, _, hp⟩ := mem_iUnion.mp h
      exact hx ⟨i, p, hp⟩
  have hclosed : ∀ i, IsClosed (cover i)
    | none => (isOpen_iUnion hopen).isClosed_compl.preimage continuous_snd
    | some i => (he i).isClosed_range.preimage continuous_snd
  have hcont : ∀ i, ContinuousOn H (cover i)
    | none => continuous_snd.continuousOn.congr (fun q hq ↦ hfixed q.1 _ hR hq)
    | some i => by
      have hset : cover (some i) = (Prod.map id (e i)) '' (univ : Set (I × (C i × Ici (0 : ℝ)))) := by
        ext q
        constructor
        · rintro ⟨p, hp⟩
          exact ⟨(q.1, p), mem_univ _, Prod.ext rfl hp⟩
        · rintro ⟨p, _, rfl⟩
          exact ⟨p.2, rfl⟩
      rw [hset]
      apply (_root_.Topology.IsInducing.id.prodMap (he i).isInducing).continuousOn_image_iff.mpr
      have heq : H ∘ Prod.map id (e i) = fun q ↦ e i (clamp i q.1 q.2) :=
        funext fun q ↦ hformula q.1 i q.2
      rw [heq]
      exact ((he i).continuous.comp (hclamp i)).continuousOn
  have hH : Continuous H := (locallyFinite_of_finite cover).continuous hcover hclosed hcont
  refine ⟨r, hrange, ⟨{
    toFun := H
    continuous_toFun := hH
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩⟩
  · intro x
    by_cases hex : ∃ p, E p = x
    · obtain ⟨⟨i, p⟩, rfl⟩ := hex
      rw [show E ⟨i, p⟩ = e i p from rfl, hformula]
      congr 1
      refine Prod.ext (by rfl) ?_
      apply Subtype.ext
      simp [clamp]
    · exact Function.extend_apply' _ _ x hex
  · intro x
    by_cases hex : ∃ p, E p = x
    · obtain ⟨⟨i, p⟩, rfl⟩ := hex
      rw [show E ⟨i, p⟩ = e i p from rfl, hformula, hr]
      congr 1
      refine Prod.ext (by rfl) ?_
      apply Subtype.ext
      simp [clamp]
    · rw [show H (1, x) = x from Function.extend_apply' _ _ x hex]
      exact (hfix (by
        rintro hx
        obtain ⟨i, p, _, hp⟩ := mem_iUnion.mp hx
        exact hex ⟨⟨i, p⟩, hp⟩)).symm
  · intro t x hx
    exact hfixed t R (fun _ ↦ le_rfl) hx


theorem exists_homotopyEquiv_cylindricalCore
    {ι X : Type*} [Finite ι] [TopologicalSpace X]
    {C : ι → Type*} [∀ i, TopologicalSpace (C i)]
    (e : ∀ i, C i × Ici (0 : ℝ) → X)
    (he : ∀ i, _root_.Topology.IsClosedEmbedding (e i))
    (hopen : ∀ i, IsOpen (e i '' {p | 0 < p.2.val}))
    (hdisjoint : Pairwise fun i j ↦ Disjoint (range (e i)) (range (e j)))
    (R : ι → ℝ) (hR : ∀ i, 0 ≤ R i) :
    ∃ F : ContinuousMap.HomotopyEquiv (cylindricalCore e R) X,
      (∀ x, F x = x.val) ∧ (∀ x, F.symm x.val = x) := by
  obtain ⟨r, hrange, ⟨H⟩⟩ :=
    exists_deformation_retraction_cylindricalCore e he hopen hdisjoint R hR
  let f : C(cylindricalCore e R, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let g : C(X, cylindricalCore e R) :=
    ⟨fun x ↦ ⟨r x, hrange ▸ mem_range_self x⟩, r.continuous.subtype_mk _⟩
  have hgf : g.comp f = ContinuousMap.id (cylindricalCore e R) := by
    ext x
    exact (H.fst_eq_snd x.property).symm
  refine ⟨{ toFun := f, invFun := g, left_inv := ?_, right_inv := ?_ },
    fun _ ↦ rfl, fun x ↦ ?_⟩
  · rw [hgf]
  · exact ⟨H.toHomotopy.symm⟩
  · exact Subtype.ext ((H.fst_eq_snd x.property).symm)

theorem exists_homotopyEquiv_of_cylindricalCore
    {ι κ X Y : Type*} [Finite ι] [Finite κ] [TopologicalSpace X] [TopologicalSpace Y]
    {C : ι → Type*} {D : κ → Type*}
    [∀ i, TopologicalSpace (C i)] [∀ j, TopologicalSpace (D j)]
    (e : ∀ i, C i × Ici (0 : ℝ) → X)
    (f : ∀ j, D j × Ici (0 : ℝ) → Y)
    (he : ∀ i, _root_.Topology.IsClosedEmbedding (e i))
    (hf : ∀ j, _root_.Topology.IsClosedEmbedding (f j))
    (hopenX : ∀ i, IsOpen (e i '' {p | 0 < p.2.val}))
    (hopenY : ∀ j, IsOpen (f j '' {p | 0 < p.2.val}))
    (hdisjointX : Pairwise fun i j ↦ Disjoint (range (e i)) (range (e j)))
    (hdisjointY : Pairwise fun i j ↦ Disjoint (range (f i)) (range (f j)))
    (R : ι → ℝ) (S : κ → ℝ) (hR : ∀ i, 0 ≤ R i) (hS : ∀ j, 0 ≤ S j)
    (u : ContinuousMap.HomotopyEquiv (cylindricalCore e R) (cylindricalCore f S)) :
    ∃ F : ContinuousMap.HomotopyEquiv X Y,
      (∀ x : cylindricalCore e R, F x.val = (u x).val) ∧
      (∀ y : cylindricalCore f S, F.symm y.val = (u.symm y).val) := by
  obtain ⟨a, ha, ha'⟩ := exists_homotopyEquiv_cylindricalCore e he hopenX hdisjointX R hR
  obtain ⟨b, hb, hb'⟩ := exists_homotopyEquiv_cylindricalCore f hf hopenY hdisjointY S hS
  refine ⟨(a.symm.trans u).trans b, ?_, ?_⟩
  · intro x
    change b (u (a.symm x.val)) = (u x).val
    rw [ha', hb]
  · intro y
    change a (u.symm (b.symm y.val)) = (u.symm y).val
    rw [hb', ha]

end DifferentialGeometry.Topology
