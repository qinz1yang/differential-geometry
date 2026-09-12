import DifferentialGeometry.Topology.Attachment.Basic
import Mathlib.Geometry.Manifold.LocalDiffeomorph

open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

private theorem adjunction_cell_injective {A B X : Type*} (i : A → B) (φ : A → X)
    (hφ : Function.Injective φ) : Function.Injective (adjunctionCell i φ) := by
  intro b b' h
  let f : B ⊕ X → Prop := Sum.elim (fun z => z = b) (fun x => ∃ a, φ a = x ∧ i a = b)
  have hf (a : A) : f (Sum.inl (i a)) = f (Sum.inr (φ a)) := by
    simp [f, hφ.eq_iff]
  let g : AdjunctionSpace i φ → Prop := Quot.lift f (by
    intro u v huv
    rcases huv with ⟨a, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact hf a
    · exact (hf a).symm)
  have hh := congrArg g h
  change (b = b) = (b' = b) at hh
  exact (Eq.mp hh rfl).symm

private theorem adjunction_lower_injective {A B X : Type*} (i : A → B) (φ : A → X)
    (hi : Function.Injective i) : Function.Injective (adjunctionLower (i := i) φ) := by
  intro x x' h
  let f : B ⊕ X → Prop := Sum.elim (fun b => ∃ a, i a = b ∧ φ a = x) (fun z => z = x)
  have hf (a : A) : f (Sum.inl (i a)) = f (Sum.inr (φ a)) := by
    simp [f, hi.eq_iff]
  let g : AdjunctionSpace i φ → Prop := Quot.lift f (by
    intro u v huv
    rcases huv with ⟨a, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact hf a
    · exact (hf a).symm)
  have hh := congrArg g h
  change (x = x) = (x' = x) at hh
  exact (Eq.mp hh rfl).symm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]

structure BallChart (n : ℕ) (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] where
  chart : PartialDiffeomorph (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) I
    (EuclideanSpace ℝ (Fin n)) M ∞
  closedBall_subset_source : Metric.closedBall 0 2 ⊆ chart.source

namespace BallChart

variable {n : ℕ} {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] (c : BallChart n I M)

theorem ball_subset_source : Metric.ball 0 1 ⊆ c.chart.source := by
  intro x hx
  apply c.closedBall_subset_source
  change dist x 0 ≤ 2
  exact le_trans (le_of_lt (Metric.mem_ball.mp hx)) (by norm_num)

theorem sphere_subset_source : Metric.sphere 0 1 ⊆ c.chart.source := by
  intro x hx
  apply c.closedBall_subset_source
  change dist x 0 ≤ 2
  rw [Metric.mem_sphere.mp hx]
  norm_num

abbrev Punctured := {x : M // x ∉ c.chart '' Metric.ball 0 1}

def boundaryMap (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) : c.Punctured :=
  ⟨c.chart z, by
    rintro ⟨x, hx, h⟩
    have heq : x = (z : EuclideanSpace ℝ (Fin n)) :=
      c.chart.toPartialEquiv.injOn (c.ball_subset_source hx)
        (c.sphere_subset_source z.2) h
    subst x
    have hz := Metric.mem_sphere.mp z.2
    exact (not_lt_of_ge (le_of_eq hz.symm)) hx⟩

@[simp]
theorem boundaryMap_val (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    (c.boundaryMap z : M) = c.chart z := rfl

theorem boundaryMap_injective : Function.Injective c.boundaryMap := by
  intro x y h
  apply Subtype.ext
  exact c.chart.toPartialEquiv.injOn (c.sphere_subset_source x.2)
    (c.sphere_subset_source y.2) (congrArg Subtype.val h)

theorem continuous_boundaryMap : Continuous c.boundaryMap := by
  apply Continuous.subtype_mk
  exact c.chart.contMDiffOn_toFun.continuousOn.comp_continuous
    continuous_subtype_val (fun x => c.sphere_subset_source x.2)

theorem continuous_inclusion : Continuous (Subtype.val : c.Punctured → M) :=
  continuous_subtype_val

theorem inclusion_injective : Function.Injective (Subtype.val : c.Punctured → M) :=
  Subtype.val_injective

end BallChart

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {K : Type*} [TopologicalSpace K]
  {n : ℕ} {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace K N]

abbrev ConnectedSumQuotient (c : BallChart n I M) (d : BallChart n J N)
    (a : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
  AdjunctionSpace c.boundaryMap (d.boundaryMap ∘ a)

namespace ConnectedSumQuotient

variable (c : BallChart n I M) (d : BallChart n J N)
  (a : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ≃ₜ
    Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)

def mk : c.Punctured ⊕ d.Punctured → ConnectedSumQuotient c d a :=
  adjunctionMk c.boundaryMap (d.boundaryMap ∘ a)

def inl : c.Punctured → ConnectedSumQuotient c d a :=
  adjunctionCell c.boundaryMap (d.boundaryMap ∘ a)

def inr : d.Punctured → ConnectedSumQuotient c d a :=
  adjunctionLower (d.boundaryMap ∘ a)

@[simp]
theorem mk_inl (x : c.Punctured) : mk c d a (Sum.inl x) = inl c d a x := rfl

@[simp]
theorem mk_inr (x : d.Punctured) : mk c d a (Sum.inr x) = inr c d a x := rfl

theorem boundary_eq (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    inl c d a (c.boundaryMap z) = inr c d a (d.boundaryMap (a z)) :=
  adjunction_coherence c.boundaryMap (d.boundaryMap ∘ a) z

theorem continuous_inl : Continuous (inl c d a) :=
  continuous_adjunctionCell c.boundaryMap (d.boundaryMap ∘ a)

theorem continuous_inr : Continuous (inr c d a) :=
  continuous_adjunctionLower c.boundaryMap (d.boundaryMap ∘ a)

theorem inl_injective : Function.Injective (inl c d a) :=
  adjunction_cell_injective c.boundaryMap (d.boundaryMap ∘ a)
    (d.boundaryMap_injective.comp a.injective)

theorem inr_injective : Function.Injective (inr c d a) :=
  adjunction_lower_injective c.boundaryMap (d.boundaryMap ∘ a) c.boundaryMap_injective

theorem isQuotientMap_mk : _root_.Topology.IsQuotientMap (mk c d a) :=
  isQuotientMap_adjunctionMk c.boundaryMap (d.boundaryMap ∘ a)

theorem jointly_surjective (z : ConnectedSumQuotient c d a) :
    (∃ x, inl c d a x = z) ∨ (∃ y, inr c d a y = z) := by
  refine Quot.induction_on z ?_
  intro s
  rcases s with x | y
  · exact Or.inl ⟨x, rfl⟩
  · exact Or.inr ⟨y, rfl⟩

theorem inl_eq_inr_iff (p : c.Punctured) (q : d.Punctured) :
    inl c d a p = inr c d a q ↔
      ∃ z, c.boundaryMap z = p ∧ d.boundaryMap (a z) = q :=
  adjunction_cell_eq_lower_iff c.boundaryMap (d.boundaryMap ∘ a)
    (d.boundaryMap_injective.comp a.injective) p q

theorem inl_ne_inr_of_forall (p : c.Punctured) (q : d.Punctured)
    (h : ∀ z, c.boundaryMap z = p → d.boundaryMap (a z) ≠ q) :
    inl c d a p ≠ inr c d a q := by
  intro hpq
  obtain ⟨z, hz, hz'⟩ := (inl_eq_inr_iff c d a p q).mp hpq
  exact h z hz hz'

theorem isOpen_image_inl {U : Set c.Punctured} (hU : IsOpen U)
    (hdisj : ∀ z, c.boundaryMap z ∉ U) :
    IsOpen (inl c d a '' U) := by
  have hcoe : (adjunctionMk c.boundaryMap (d.boundaryMap ∘ a)) ⁻¹'
      (inl c d a '' U) = Sum.inl '' U := by
    ext s
    constructor
    · rintro ⟨p, hpU, hp⟩
      cases s with
      | inl x =>
          refine ⟨x, ?_, rfl⟩
          rwa [← (inl_injective c d a hp)]
      | inr y =>
          obtain ⟨z, hz, -⟩ := (inl_eq_inr_iff c d a p y).mp hp
          exact absurd (hz.symm ▸ hpU) (hdisj z)
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
  change IsOpen[TopologicalSpace.coinduced
    (adjunctionMk c.boundaryMap (d.boundaryMap ∘ a)) inferInstance] (inl c d a '' U)
  rw [isOpen_coinduced, hcoe]
  exact isOpenMap_inl U hU

theorem isOpen_image_inr {V : Set d.Punctured} (hV : IsOpen V)
    (hdisj : ∀ z, d.boundaryMap z ∉ V) :
    IsOpen (inr c d a '' V) := by
  have hcoe : (adjunctionMk c.boundaryMap (d.boundaryMap ∘ a)) ⁻¹'
      (inr c d a '' V) = Sum.inr '' V := by
    ext s
    constructor
    · rintro ⟨q, hqV, hq⟩
      cases s with
      | inr y =>
          refine ⟨y, ?_, rfl⟩
          rwa [← (inr_injective c d a hq)]
      | inl x =>
          obtain ⟨z, -, hz⟩ := (inl_eq_inr_iff c d a x q).mp hq.symm
          exact absurd (hz.symm ▸ hqV) (hdisj (a z))
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
  change IsOpen[TopologicalSpace.coinduced
    (adjunctionMk c.boundaryMap (d.boundaryMap ∘ a)) inferInstance] (inr c d a '' V)
  rw [isOpen_coinduced, hcoe]
  exact isOpenMap_inr V hV

theorem isOpen_image_union {U : Set c.Punctured} {V : Set d.Punctured} (hU : IsOpen U)
    (hV : IsOpen V) (hdisjU : ∀ z, c.boundaryMap z ∉ U)
    (hdisjV : ∀ z, d.boundaryMap z ∉ V) :
    IsOpen (inl c d a '' U ∪ inr c d a '' V) := by
  have hcoe : (adjunctionMk c.boundaryMap (d.boundaryMap ∘ a)) ⁻¹'
      (inl c d a '' U ∪ inr c d a '' V) = Sum.inl '' U ∪ Sum.inr '' V := by
    ext s
    constructor
    · rintro (⟨p, hpU, hp⟩ | ⟨q, hqV, hq⟩)
      · cases s with
        | inl x =>
            refine Or.inl ⟨x, ?_, rfl⟩
            rwa [← (inl_injective c d a hp)]
        | inr y =>
            obtain ⟨z, hz, -⟩ := (inl_eq_inr_iff c d a p y).mp hp
            exact absurd (hz.symm ▸ hpU) (hdisjU z)
      · cases s with
        | inl x =>
            obtain ⟨z, -, hz⟩ := (inl_eq_inr_iff c d a x q).mp hq.symm
            exact absurd (hz.symm ▸ hqV) (hdisjV (a z))
        | inr y =>
            refine Or.inr ⟨y, ?_, rfl⟩
            rwa [← (inr_injective c d a hq)]
    · rintro (⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩)
      · exact Or.inl ⟨x, hx, rfl⟩
      · exact Or.inr ⟨y, hy, rfl⟩
  change IsOpen[TopologicalSpace.coinduced
    (adjunctionMk c.boundaryMap (d.boundaryMap ∘ a)) inferInstance]
    (inl c d a '' U ∪ inr c d a '' V)
  rw [isOpen_coinduced, hcoe]
  exact (isOpenMap_inl U hU).union (isOpenMap_inr V hV)

end ConnectedSumQuotient

theorem frontier_half_le_subset_eq_zero {α : Type*} [TopologicalSpace α] (f : α → ℝ)
    (hf : Continuous f) : frontier {p : α | 0 ≤ f p} ⊆ {p | f p = 0} := by
  intro p hp
  have hcl : p ∈ closure {q : α | 0 ≤ f q} := frontier_subset_closure hp
  have hcl' : p ∈ closure ({q : α | 0 ≤ f q}ᶜ) := by
    have h : p ∈ frontier ({q : α | 0 ≤ f q}ᶜ) := by
      rwa [frontier_compl]
    exact frontier_subset_closure h
  have hge : 0 ≤ f p :=
    closure_minimal (fun q hq => hq) (isClosed_le continuous_const hf) hcl
  have hle : f p ≤ 0 := by
    refine closure_minimal (fun q hq => ?_) (isClosed_le hf continuous_const) hcl'
    have hq' : ¬ (0 ≤ f q) := hq
    exact le_of_lt (not_le.mp hq')
  exact le_antisymm hle hge

end DifferentialGeometry.Topology
