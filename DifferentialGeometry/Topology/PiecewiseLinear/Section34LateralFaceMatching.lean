import DifferentialGeometry.Topology.PiecewiseLinear.Section34LateralFaceDisk
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ReturningArcComponent

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLHomeomorphOn.top_arc_eq_of_disjoint_spanning_family
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {P C A : Set E} {δ : ℝ → E} (hδ : IsPLHomeomorphOn δ (Icc 0 1) A)
    (hPC : P ⊆ C) {x y : P} (hδ₀ : δ 0 = x) (hδ₁ : δ 1 = y)
    {a b : ℝ} {Z : P → Set (E × ℝ)}
    (hZ : ∀ z, IsPreconnected (Z z)) (hZside : ∀ z, Z z ⊆ P ×ˢ Icc a b)
    (hZa : ∀ z, Z z ∩ (P ×ˢ ({a} : Set ℝ)) = {((z : E), a)})
    (hZb : ∀ z, ((z : E), b) ∈ Z z)
    (hdis : Pairwise fun z w => Disjoint (Z z) (Z w))
    {F B : Set (E × ℝ)} (hB : IsPreconnected B)
    (hFB : F ∩ (P ×ˢ ({b} : Set ℝ)) = B)
    (hxB : ((x : E), b) ∈ B) (hyB : ((y : E), b) ∈ B)
    (havoid : ∀ W : Set (E × ℝ), IsPreconnected W → W ⊆ P ×ˢ Icc a b →
      Disjoint W ((Z x ∪ (A ×ˢ ({a} : Set ℝ))) ∪ Z y) →
      (W ∩ (C ×ˢ ({a} : Set ℝ))).Nonempty → Disjoint F W) :
    B = A ×ˢ ({b} : Set ℝ) ∧ ∀ z : P, (z : E) ∉ A → Disjoint F (Z z) := by
  have hxA : (x : E) ∈ A := hδ₀ ▸ hδ.bijOn.mapsTo ⟨le_rfl, zero_le_one⟩
  have hyA : (y : E) ∈ A := hδ₁ ▸ hδ.bijOn.mapsTo ⟨zero_le_one, le_rfl⟩
  have hout (z : P) (hz : (z : E) ∉ A) : Disjoint F (Z z) := by
    have hzx : z ≠ x := fun heq => hz (heq.symm ▸ hxA)
    have hzy : z ≠ y := fun heq => hz (heq.symm ▸ hyA)
    have hZA : Disjoint (Z z) (A ×ˢ ({a} : Set ℝ)) := by
      apply disjoint_left.mpr
      intro w hwZ hwA
      have heq : w = ((z : E), a) := (hZa z).subset ⟨hwZ, (hZside z hwZ).1, hwA.2⟩
      have hwz : w.1 = (z : E) := congrArg Prod.fst heq
      exact hz (hwz ▸ hwA.1)
    apply havoid (Z z) (hZ z) (hZside z)
      (disjoint_union_right.mpr ⟨disjoint_union_right.mpr ⟨hdis hzx, hZA⟩, hdis hzy⟩)
    exact ⟨((z : E), a), ((hZa z).symm.subset rfl).1, hPC z.2, rfl⟩
  have hBA : B ⊆ A ×ˢ ({b} : Set ℝ) := by
    intro w hw
    have hwF := (hFB.symm.subset hw).1
    have hwP := (hFB.symm.subset hw).2
    refine ⟨?_, hwP.2⟩
    by_contra hwA
    let z : P := ⟨w.1, hwP.1⟩
    have hwZ : w ∈ Z z := by
      have heq : ((z : E), b) = w := Prod.ext rfl hwP.2.symm
      exact heq ▸ hZb z
    exact disjoint_left.mp (hout z hwA) hwF hwZ
  have hA : IsPolyhedron A :=
    ((isPLBall_Icc zero_lt_one).of_isPLHomeomorphOn hδ).isPolyhedron
  have hδb : IsPLHomeomorphOn (fun t => (δ t, b)) (Icc 0 1) (A ×ˢ ({b} : Set ℝ)) :=
    hδ.trans (hA.isPLHomeomorphOn_prod_const b)
  exact ⟨hδb.eq_of_preconnected_of_mem_endpoints hB hBA
    (hδ₀.symm ▸ hxB) (hδ₁.symm ▸ hyB), hout⟩

theorem exists_lateral_disk_with_matching_rim_arcs
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {P A : Set E} {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) P) {a b : ℝ} (hab : a < b)
    {Z : (r '' stdSimplexBoundary 2) → Set (E × ℝ)}
    (hZ : ∀ z, IsPreconnected (Z z))
    (hZside : ∀ z, Z z ⊆ (r '' stdSimplexBoundary 2) ×ˢ Icc a b)
    (hZa : ∀ z, Z z ∩ ((r '' stdSimplexBoundary 2) ×ˢ ({a} : Set ℝ)) = {((z : E), a)})
    (hZb : ∀ z, Z z ∩ ((r '' stdSimplexBoundary 2) ×ˢ ({b} : Set ℝ)) = {((z : E), b)})
    (hdis : Pairwise fun z w => Disjoint (Z z) (Z w))
    {x y : r '' stdSimplexBoundary 2} {α β : ℝ → E × ℝ} {δ : ℝ → E}
    (hα : IsPLHomeomorphOn α (Icc 0 1) (Z x))
    (hβ : IsPLHomeomorphOn β (Icc 0 1) (Z y))
    (hδ : IsPLHomeomorphOn δ (Icc 0 1) A)
    (hα₀ : α 0 = ((x : E), a)) (hα₁ : α 1 = ((x : E), b))
    (hβ₀ : β 0 = ((y : E), a)) (hβ₁ : β 1 = ((y : E), b))
    (hδ₀ : δ 0 = x) (hδ₁ : δ 1 = y) (hAP : A ⊆ r '' stdSimplexBoundary 2) :
    ∃ (F : Set (E × ℝ)) (q : (Fin 3 → ℝ) → E × ℝ),
      IsPLHomeomorphOn q (stdSimplex ℝ (Fin 3)) F ∧
      F ⊆ (r '' stdSimplexBoundary 2) ×ˢ Icc a b ∧
      q '' stdSimplexBoundary 2 =
        ((Z x ∪ (A ×ˢ ({a} : Set ℝ))) ∪ Z y) ∪ (A ×ˢ ({b} : Set ℝ)) ∧
      F ∩ ((r '' stdSimplexBoundary 2) ×ˢ ({b} : Set ℝ)) = A ×ˢ ({b} : Set ℝ) ∧
      F ∩ (P ×ˢ ({a} : Set ℝ)) = A ×ˢ ({a} : Set ℝ) ∧
      ∀ z : r '' stdSimplexBoundary 2, (z : E) ∉ A → Disjoint F (Z z) := by
  have hxy : x ≠ y := by
    intro heq
    exact zero_ne_one (hδ.bijOn.injOn ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩
      (hδ₀.trans ((congrArg Subtype.val heq).trans hδ₁.symm)))
  obtain ⟨F, B, q, hq, hF, hside, hbd, htop, hbottom, hcorners, havoid⟩ :=
    exists_lateral_disk_between_spanning_arcs hr hab hα hβ hδ hα₀ hα₁ hβ₀ hβ₁ hδ₀ hδ₁
      (hZside x) (hZside y) hAP (hZa x) (hZb x) (hZa y) (hZb y) (hdis hxy)
  have hrP : r '' stdSimplexBoundary 2 ⊆ P :=
    (image_mono (fun _ hx => hx.1)).trans hr.image_eq.subset
  obtain ⟨hB, hout⟩ := hδ.top_arc_eq_of_disjoint_spanning_family hrP hδ₀ hδ₁ hZ hZside hZa
    (fun z => ((hZb z).symm.subset rfl).1) hdis hF.isConnected.isPreconnected htop
    ((hcorners.symm.subset (Or.inl rfl)).2) ((hcorners.symm.subset (Or.inr rfl)).2) havoid
  exact ⟨F, q, hq, hside, hB ▸ hbd, htop.trans hB, hbottom, hout⟩

end DifferentialGeometry.Topology.PiecewiseLinear
