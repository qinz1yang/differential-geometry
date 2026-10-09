import DifferentialGeometry.Topology.Ends.CylindricalCore
import Mathlib.Topology.Order.DenselyOrdered

noncomputable section

open Set

namespace DifferentialGeometry.Topology

theorem mem_cylindricalCore_image_iff
    {ι X : Type*} {C : ι → Type*}
    (e : ∀ i, C i × Ici (0 : ℝ) → X)
    (hinj : ∀ i, Function.Injective (e i))
    (hdisjoint : Pairwise fun i j ↦ Disjoint (range (e i)) (range (e j)))
    (R : ι → ℝ) (i : ι) (p : C i × Ici (0 : ℝ)) :
    e i p ∈ cylindricalCore e R ↔ p.2.val ≤ R i := by
  constructor
  · intro hp
    exact le_of_not_gt fun h ↦ hp (mem_iUnion.mpr ⟨i, p, h, rfl⟩)
  · intro hp hx
    obtain ⟨j, q, hq, heq⟩ := mem_iUnion.mp hx
    by_cases hij : i = j
    · subst j
      have hqp := hinj i heq
      change R i < q.2.val at hq
      exact hq.not_ge (hqp.symm ▸ hp)
    · exact disjoint_left.mp (hdisjoint hij) ⟨p, rfl⟩ ⟨q, heq⟩

private theorem closure_cylinder_tail
    {C : Type*} [TopologicalSpace C] (R : ℝ) :
    closure {p : C × Ici (0 : ℝ) | R < p.2.val} = {p | R ≤ p.2.val} := by
  by_cases hR : 0 ≤ R
  · let r : Ici (0 : ℝ) := ⟨R, hR⟩
    have heq : {p : C × Ici (0 : ℝ) | R < p.2.val} = univ ×ˢ Ioi r := by
      ext p
      simp only [mem_ofPred_eq, mem_prod, mem_univ, true_and, mem_Ioi, r]
      rfl
    rw [heq, closure_prod_eq, closure_univ, closure_Ioi]
    ext p
    simp only [mem_prod, mem_univ, true_and, mem_Ici, mem_ofPred_eq, r]
    rfl
  · have hneg : R < 0 := lt_of_not_ge hR
    have htail : {p : C × Ici (0 : ℝ) | R < p.2.val} = univ :=
      eq_univ_of_forall (fun p ↦ hneg.trans_le p.2.property)
    have hclosedTail : {p : C × Ici (0 : ℝ) | R ≤ p.2.val} = univ :=
      eq_univ_of_forall (fun p ↦ hneg.le.trans p.2.property)
    rw [htail, hclosedTail, closure_univ]

private theorem closure_cylinder_lower_slab
    {C : Type*} [TopologicalSpace C] {R : ℝ} (hR : 0 < R) :
    closure {p : C × Ici (0 : ℝ) | p.2.val < R} = {p | p.2.val ≤ R} := by
  let r : Ici (0 : ℝ) := ⟨R, hR.le⟩
  have heq : {p : C × Ici (0 : ℝ) | p.2.val < R} = univ ×ˢ Iio r := by
    ext p
    simp only [mem_ofPred_eq, mem_prod, mem_univ, true_and, mem_Iio, r]
    rfl
  rw [heq, closure_prod_eq, closure_univ,
    closure_Iio' (show (Iio r).Nonempty from ⟨⟨0, by simp⟩, hR⟩)]
  ext p
  simp only [mem_prod, mem_univ, true_and, mem_Iic, mem_ofPred_eq, r]
  rfl

theorem interior_cylindricalCore
    {ι X : Type*} [Finite ι] [TopologicalSpace X]
    {C : ι → Type*} [∀ i, TopologicalSpace (C i)]
    (e : ∀ i, C i × Ici (0 : ℝ) → X)
    (he : ∀ i, _root_.Topology.IsClosedEmbedding (e i))
    (R : ι → ℝ) :
    interior (cylindricalCore e R) = (⋃ i, e i '' {p | R i ≤ p.2.val})ᶜ := by
  unfold cylindricalCore
  rw [interior_compl, closure_iUnion_of_finite]
  congr 1
  apply iUnion_congr
  intro i
  rw [(he i).closure_image_eq, closure_cylinder_tail (R i)]

theorem mem_interior_cylindricalCore_image_iff
    {ι X : Type*} [Finite ι] [TopologicalSpace X]
    {C : ι → Type*} [∀ i, TopologicalSpace (C i)]
    (e : ∀ i, C i × Ici (0 : ℝ) → X)
    (he : ∀ i, _root_.Topology.IsClosedEmbedding (e i))
    (hdisjoint : Pairwise fun i j ↦ Disjoint (range (e i)) (range (e j)))
    (R : ι → ℝ) (i : ι) (p : C i × Ici (0 : ℝ)) :
    e i p ∈ interior (cylindricalCore e R) ↔ p.2.val < R i := by
  rw [interior_cylindricalCore e he R]
  constructor
  · intro hp
    exact lt_of_not_ge fun h ↦ hp (mem_iUnion.mpr ⟨i, p, h, rfl⟩)
  · intro hp hx
    obtain ⟨j, q, hq, heq⟩ := mem_iUnion.mp hx
    by_cases hij : i = j
    · subst j
      have hqp := (he i).injective heq
      change R i ≤ q.2.val at hq
      exact hp.not_ge (hqp ▸ hq)
    · exact disjoint_left.mp (hdisjoint hij) ⟨p, rfl⟩ ⟨q, heq⟩

theorem cylindricalCore_subset_interior_of_lt
    {ι X : Type*} [Finite ι] [TopologicalSpace X]
    {C : ι → Type*} [∀ i, TopologicalSpace (C i)]
    (e : ∀ i, C i × Ici (0 : ℝ) → X)
    (he : ∀ i, _root_.Topology.IsClosedEmbedding (e i))
    (S R : ι → ℝ) (hSR : ∀ i, S i < R i) :
    cylindricalCore e S ⊆ interior (cylindricalCore e R) := by
  rw [interior_cylindricalCore e he R]
  intro x hx hnot
  obtain ⟨i, p, hp, rfl⟩ := mem_iUnion.mp hnot
  exact hx (mem_iUnion.mpr ⟨i, p, (hSR i).trans_le hp, rfl⟩)

theorem frontier_cylindricalCore
    {ι X : Type*} [Finite ι] [TopologicalSpace X]
    {C : ι → Type*} [∀ i, TopologicalSpace (C i)]
    (e : ∀ i, C i × Ici (0 : ℝ) → X)
    (he : ∀ i, _root_.Topology.IsClosedEmbedding (e i))
    (hopen : ∀ i, IsOpen (e i '' {p | 0 < p.2.val}))
    (hdisjoint : Pairwise fun i j ↦ Disjoint (range (e i)) (range (e j)))
    (R : ι → ℝ) (hR : ∀ i, 0 ≤ R i) :
    frontier (cylindricalCore e R) = ⋃ i, e i '' {p | p.2.val = R i} := by
  rw [(isClosed_cylindricalCore e he hopen R hR).frontier_eq]
  ext x
  constructor
  · rintro ⟨hx, hnot⟩
    rw [interior_cylindricalCore e he R] at hnot
    obtain ⟨i, p, hp, rfl⟩ := mem_iUnion.mp (not_not.mp hnot)
    have hle := (mem_cylindricalCore_image_iff e (fun j ↦ (he j).injective)
      hdisjoint R i p).mp hx
    exact mem_iUnion.mpr ⟨i, p, le_antisymm hle hp, rfl⟩
  · intro hx
    obtain ⟨i, p, hp, rfl⟩ := mem_iUnion.mp hx
    have hp' : p.2.val = R i := hp
    refine ⟨(mem_cylindricalCore_image_iff e (fun j ↦ (he j).injective)
      hdisjoint R i p).mpr hp'.le, ?_⟩
    rw [mem_interior_cylindricalCore_image_iff e he hdisjoint R i p]
    exact not_lt_of_ge hp'.ge

theorem closure_interior_cylindricalCore
    {ι X : Type*} [Finite ι] [TopologicalSpace X]
    {C : ι → Type*} [∀ i, TopologicalSpace (C i)]
    (e : ∀ i, C i × Ici (0 : ℝ) → X)
    (he : ∀ i, _root_.Topology.IsClosedEmbedding (e i))
    (hopen : ∀ i, IsOpen (e i '' {p | 0 < p.2.val}))
    (hdisjoint : Pairwise fun i j ↦ Disjoint (range (e i)) (range (e j)))
    (R : ι → ℝ) (hR : ∀ i, 0 < R i) :
    closure (interior (cylindricalCore e R)) = cylindricalCore e R := by
  apply Subset.antisymm (closure_minimal interior_subset
    (isClosed_cylindricalCore e he hopen R (fun i ↦ (hR i).le)))
  intro x hx
  by_cases hi : x ∈ interior (cylindricalCore e R)
  · exact subset_closure hi
  · rw [interior_cylindricalCore e he R] at hi
    obtain ⟨i, p, -, rfl⟩ := mem_iUnion.mp (not_not.mp hi)
    have hp : p ∈ closure {q : C i × Ici (0 : ℝ) | q.2.val < R i} := by
      rw [closure_cylinder_lower_slab (hR i)]
      exact (mem_cylindricalCore_image_iff e (fun j ↦ (he j).injective)
        hdisjoint R i p).mp hx
    have himage : e i p ∈ closure (e i '' {q | q.2.val < R i}) :=
      image_closure_subset_closure_image (he i).continuous ⟨p, hp, rfl⟩
    apply closure_mono (t := interior (cylindricalCore e R)) ?_ himage
    rintro y ⟨q, hq, rfl⟩
    exact (mem_interior_cylindricalCore_image_iff e he hdisjoint R i q).mpr hq

theorem isConnected_interior_cylindricalCore
    {ι X : Type*} [Finite ι] [TopologicalSpace X] [ConnectedSpace X]
    {C : ι → Type*} [∀ i, TopologicalSpace (C i)]
    (e : ∀ i, C i × Ici (0 : ℝ) → X)
    (he : ∀ i, _root_.Topology.IsClosedEmbedding (e i))
    (hopen : ∀ i, IsOpen (e i '' {p | 0 < p.2.val}))
    (hdisjoint : Pairwise fun i j ↦ Disjoint (range (e i)) (range (e j)))
    (R : ι → ℝ) (hR : ∀ i, 0 < R i) :
    IsConnected (interior (cylindricalCore e R)) := by
  let V : Ico (0 : ℝ) 1 → Set X := fun s ↦ cylindricalCore e (fun i ↦ s.val * R i)
  have hV (s : Ico (0 : ℝ) 1) : IsConnected (V s) :=
    isConnected_cylindricalCore e he hopen hdisjoint (fun i ↦ s.val * R i)
      (fun i ↦ mul_nonneg s.property.1 (hR i).le)
  have hzero (s : Ico (0 : ℝ) 1) : cylindricalCore e (fun _ ↦ 0) ⊆ V s := by
    intro x hx hnot
    obtain ⟨i, p, hp, rfl⟩ := mem_iUnion.mp hnot
    exact hx (mem_iUnion.mpr ⟨i, p,
      lt_of_le_of_lt (mul_nonneg s.property.1 (hR i).le) hp, rfl⟩)
  have hsub (s : Ico (0 : ℝ) 1) : V s ⊆ interior (cylindricalCore e R) :=
    cylindricalCore_subset_interior_of_lt e he (fun i ↦ s.val * R i) R (fun i ↦ by
        simpa only [one_mul] using mul_lt_mul_of_pos_right s.property.2 (hR i))
  let s₀ : Ico (0 : ℝ) 1 := ⟨0, by simp⟩
  have hunion : ⋃ s, V s = interior (cylindricalCore e R) := by
    apply Subset.antisymm (iUnion_subset hsub)
    intro x hx
    by_cases hcore : x ∈ cylindricalCore e (fun _ ↦ 0)
    · exact mem_iUnion.mpr ⟨s₀, hzero s₀ hcore⟩
    · obtain ⟨i, p, -, rfl⟩ := mem_iUnion.mp (not_not.mp hcore)
      have hp := (mem_interior_cylindricalCore_image_iff e he hdisjoint R i p).mp hx
      let s : Ico (0 : ℝ) 1 := ⟨p.2.val / R i,
        div_nonneg p.2.property (hR i).le, (div_lt_one (hR i)).mpr hp⟩
      refine mem_iUnion.mpr ⟨s, ?_⟩
      apply (mem_cylindricalCore_image_iff e (fun j ↦ (he j).injective)
        hdisjoint (fun j ↦ s.val * R j) i p).mpr
      change p.2.val ≤ p.2.val / R i * R i
      rw [div_mul_cancel₀ _ (hR i).ne']
  obtain ⟨x₀, hx₀⟩ :=
    (isConnected_cylindricalCore e he hopen hdisjoint (fun _ ↦ 0) (fun _ ↦ le_rfl)).nonempty
  refine ⟨⟨x₀, hsub s₀ (hzero s₀ hx₀)⟩, ?_⟩
  rw [← hunion]
  exact isPreconnected_iUnion ⟨x₀, mem_iInter.mpr (fun s ↦ hzero s hx₀)⟩
    (fun s ↦ (hV s).isPreconnected)

end DifferentialGeometry.Topology
