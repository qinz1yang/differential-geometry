import DifferentialGeometry.Topology.Manifold.SmoothCompatibleAtlas.Defs
import DifferentialGeometry.Analysis.Calculus.SmoothApproximation.SmoothingHomeomorph

set_option autoImplicit false

noncomputable section

open Set Function
open scoped ContDiff

namespace DifferentialGeometry.Topology.Manifold

theorem contDiffOn_trans_homeomorph {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : OpenPartialHomeomorph E E) {n : ℕ∞ω} (he : ContDiffOn ℝ n e e.source) (g : E ≃ₜ E)
    (hg : ContDiff ℝ n g) :
    ContDiffOn ℝ n (e.trans g.toOpenPartialHomeomorph)
      (e.trans g.toOpenPartialHomeomorph).source := by
  have hsub : (e.trans g.toOpenPartialHomeomorph).source ⊆ e.source := by
    rw [OpenPartialHomeomorph.trans_source]
    exact inter_subset_left
  exact hg.comp_contDiffOn (he.mono hsub)

theorem contDiffOn_homeomorph_symm_trans {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : OpenPartialHomeomorph E E) {n : ℕ∞ω} (he : ContDiffOn ℝ n e e.source) (g : E ≃ₜ E)
    (hg : ContDiff ℝ n g.symm) :
    ContDiffOn ℝ n (g.toOpenPartialHomeomorph.symm.trans e)
      (g.toOpenPartialHomeomorph.symm.trans e).source := by
  have hmaps : MapsTo g.symm (g.toOpenPartialHomeomorph.symm.trans e).source e.source := by
    intro y hy
    rw [OpenPartialHomeomorph.trans_source] at hy
    exact hy.2
  exact he.comp hg.contDiffOn hmaps

theorem contDiffOn_symm_trans_trans_homeomorph {E X : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace X] (p q : OpenPartialHomeomorph X E) (g : E ≃ₜ E)
    {n : ℕ∞ω} (hpq : ContDiffOn ℝ n (p.symm.trans q) (p.symm.trans q).source)
    (hg : ContDiff ℝ n g) :
    ContDiffOn ℝ n (p.symm.trans (q.trans g.toOpenPartialHomeomorph))
      (p.symm.trans (q.trans g.toOpenPartialHomeomorph)).source := by
  rw [← OpenPartialHomeomorph.trans_assoc]
  exact contDiffOn_trans_homeomorph (p.symm.trans q) hpq g hg

theorem contDiffOn_trans_homeomorph_symm_trans {E X : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace X] (q p : OpenPartialHomeomorph X E) (g : E ≃ₜ E)
    {n : ℕ∞ω} (hqp : ContDiffOn ℝ n (q.symm.trans p) (q.symm.trans p).source)
    (hg : ContDiff ℝ n g.symm) :
    ContDiffOn ℝ n ((q.trans g.toOpenPartialHomeomorph).symm.trans p)
      ((q.trans g.toOpenPartialHomeomorph).symm.trans p).source := by
  rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc]
  exact contDiffOn_homeomorph_symm_trans (q.symm.trans p) hqp g hg

private theorem contDiffOn_symm_trans_trans_homeomorph_symm {E X : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace X] (p q : OpenPartialHomeomorph X E) (g : E ≃ₜ E)
    {n : ℕ∞ω} (hqp : ContDiffOn ℝ n (q.symm.trans p) (q.symm.trans p).source)
    (hg : ContDiff ℝ n g.symm) :
    ContDiffOn ℝ n (p.symm.trans (q.trans g.toOpenPartialHomeomorph)).symm
      (p.symm.trans (q.trans g.toOpenPartialHomeomorph)).target :=
  contDiffOn_trans_homeomorph_symm_trans q p g hqp hg

theorem contDiffOn_symm_trans_symm_trans {E X : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace X] (p α β : OpenPartialHomeomorph X E) {n : ℕ∞ω}
    (h : ContDiffOn ℝ n (α.symm.trans β) (α.symm.trans β).source) :
    ContDiffOn ℝ n ((p.symm.trans α).symm.trans (p.symm.trans β))
      ((p.symm.trans α).symm.trans (p.symm.trans β)).source := by
  refine h.congr_mono (fun y hy => ?_) (fun y hy => ?_)
  · obtain ⟨⟨-, h2⟩, -⟩ := hy
    have h2' : α.symm y ∈ p.source := h2
    change β (p.symm (p (α.symm y))) = β (α.symm y)
    rw [p.left_inv h2']
  · obtain ⟨⟨h1, h2⟩, -, h3⟩ := hy
    have h1' : y ∈ α.target := h1
    have h2' : α.symm y ∈ p.source := h2
    have h3' : p.symm (p (α.symm y)) ∈ β.source := h3
    rw [p.left_inv h2'] at h3'
    exact ⟨h1', h3'⟩

private theorem contDiffOn_symm_trans_trans_homeomorph_of_chart {E X : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace X] (p θ : OpenPartialHomeomorph X E) (g : E ≃ₜ E)
    {n : ℕ∞ω}
    (h : ContDiffOn ℝ n ((p.symm.trans θ).symm.trans g.toOpenPartialHomeomorph)
      ((p.symm.trans θ).symm.trans g.toOpenPartialHomeomorph).source) :
    ContDiffOn ℝ n (θ.symm.trans (p.trans g.toOpenPartialHomeomorph))
      (θ.symm.trans (p.trans g.toOpenPartialHomeomorph)).source := by
  refine h.congr_mono (fun y _ => rfl) (fun y hy => ?_)
  obtain ⟨h1, h2, -⟩ := hy
  have h1' : y ∈ θ.target := h1
  have h2' : θ.symm y ∈ p.source := h2
  exact ⟨⟨h1', h2'⟩, trivial⟩

private theorem contDiffOn_trans_homeomorph_symm_trans_of_chart {E X : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace X] (p θ : OpenPartialHomeomorph X E) (g : E ≃ₜ E)
    {n : ℕ∞ω}
    (h : ContDiffOn ℝ n (g.toOpenPartialHomeomorph.symm.trans (p.symm.trans θ))
      (g.toOpenPartialHomeomorph.symm.trans (p.symm.trans θ)).source) :
    ContDiffOn ℝ n ((p.trans g.toOpenPartialHomeomorph).symm.trans θ)
      ((p.trans g.toOpenPartialHomeomorph).symm.trans θ).source := by
  refine h.congr_mono (fun y _ => rfl) (fun y hy => ?_)
  obtain ⟨⟨-, h1⟩, h2⟩ := hy
  have h1' : g.symm y ∈ p.target := h1
  have h2' : p.symm (g.symm y) ∈ θ.source := h2
  exact ⟨trivial, h1', h2'⟩

theorem contDiffOn_symm_trans_self {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace X] (θ : OpenPartialHomeomorph X E) {n : ℕ∞ω} :
    ContDiffOn ℝ n (θ.symm.trans θ) (θ.symm.trans θ).source := by
  refine contDiffOn_id.congr fun y hy => ?_
  obtain ⟨hy1, -⟩ := hy
  have hy1' : y ∈ θ.target := hy1
  exact θ.right_inv hy1'

theorem trans_homeomorph_source {E X : Type*} [NormedAddCommGroup E]
    [TopologicalSpace X] (p : OpenPartialHomeomorph X E) (g : E ≃ₜ E) :
    (p.trans g.toOpenPartialHomeomorph).source = p.source := by
  rw [OpenPartialHomeomorph.trans_source]
  exact inter_eq_left.mpr fun _ _ => trivial

theorem trans_homeomorph_target {E X : Type*} [NormedAddCommGroup E]
    [TopologicalSpace X] (p : OpenPartialHomeomorph X E) (g : E ≃ₜ E)
    (hg : g '' p.target = p.target) :
    (p.trans g.toOpenPartialHomeomorph).target = p.target := by
  rw [OpenPartialHomeomorph.trans_target]
  change univ ∩ ⇑g.symm ⁻¹' p.target = p.target
  rw [univ_inter, Homeomorph.preimage_symm, hg]

def SmoothingGood {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace X]
    (φ : ℕ → OpenPartialHomeomorph X E) (r n : ℕ) (G : ℕ → E ≃ₜ E) : Prop :=
  (∀ j, j < n → ContDiff ℝ r (G j) ∧ ContDiff ℝ r (G j).symm) ∧
    ∀ i j, i < n → j < n →
      ContDiffOn ℝ ∞ (((φ i).trans (G i).toOpenPartialHomeomorph).symm.trans
          ((φ j).trans (G j).toOpenPartialHomeomorph))
        (((φ i).trans (G i).toOpenPartialHomeomorph).symm.trans
          ((φ j).trans (G j).toOpenPartialHomeomorph)).source

def smoothingStepCharts {E X : Type*} [NormedAddCommGroup E]
    [TopologicalSpace X] (φ : ℕ → OpenPartialHomeomorph X E) (n : ℕ) (G : ℕ → E ≃ₜ E)
    (j : Fin n) : OpenPartialHomeomorph E E :=
  (φ n).symm.trans ((φ j).trans (G j).toOpenPartialHomeomorph)

private def SmoothingStepSpec {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}
    (r : ℕ) (χ : ι → OpenPartialHomeomorph E E) (g : E ≃ₜ E) : Prop :=
  (ContDiff ℝ r g ∧ ContDiff ℝ r g.symm) ∧
    (∀ x, x ∉ ⋃ a, (χ a).source → g x = x ∧ g.symm x = x) ∧
    g '' (⋃ a, (χ a).source) = ⋃ a, (χ a).source ∧
    (∀ a, ContDiffOn ℝ ∞ ((χ a).symm.trans g.toOpenPartialHomeomorph)
      ((χ a).symm.trans g.toOpenPartialHomeomorph).source) ∧
    (∀ a, ContDiffOn ℝ ∞ (g.toOpenPartialHomeomorph.symm.trans (χ a))
      (g.toOpenPartialHomeomorph.symm.trans (χ a)).source) ∧
    ∀ x, 0 < (fderiv ℝ g x).det

private theorem smoothingGood_zero {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace X] (φ : ℕ → OpenPartialHomeomorph X E) (r : ℕ) (G : ℕ → E ≃ₜ E) :
    SmoothingGood φ r 0 G :=
  ⟨fun j hj => absurd hj (Nat.not_lt_zero j), fun i _ hi _ => absurd hi (Nat.not_lt_zero i)⟩

private theorem smoothingGood_congr {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace X] {φ : ℕ → OpenPartialHomeomorph X E} {r n : ℕ} {G G' : ℕ → E ≃ₜ E}
    (h : ∀ j, j < n → G j = G' j) (hG : SmoothingGood φ r n G) : SmoothingGood φ r n G' := by
  obtain ⟨h1, h2⟩ := hG
  refine ⟨fun j hj => ?_, fun i j hi hj => ?_⟩
  · rw [← h j hj]
    exact h1 j hj
  · rw [← h i hi, ← h j hj]
    exact h2 i j hi hj

private theorem smoothingStepCharts_congr {E X : Type*} [NormedAddCommGroup E]
    [TopologicalSpace X] (φ : ℕ → OpenPartialHomeomorph X E) {n : ℕ} {G G' : ℕ → E ≃ₜ E}
    (h : ∀ j, j < n → G j = G' j) : smoothingStepCharts φ n G = smoothingStepCharts φ n G' := by
  funext j
  unfold smoothingStepCharts
  rw [h j j.isLt]

theorem smoothingStepCharts_contDiffOn {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace X] {φ : ℕ → OpenPartialHomeomorph X E} {r : ℕ}
    (hφ : ∀ i j, ContDiffOn ℝ r ((φ i).symm.trans (φ j)) ((φ i).symm.trans (φ j)).source)
    {n : ℕ} {G : ℕ → E ≃ₜ E} (hG : SmoothingGood φ r n G) (a : Fin n) :
    ContDiffOn ℝ r (smoothingStepCharts φ n G a) (smoothingStepCharts φ n G a).source :=
  contDiffOn_symm_trans_trans_homeomorph (φ n) (φ a) (G a) (hφ n a) (hG.1 a a.isLt).1

private theorem smoothingStepCharts_contDiffOn_symm {E X : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace X] {φ : ℕ → OpenPartialHomeomorph X E} {r : ℕ}
    (hφ : ∀ i j, ContDiffOn ℝ r ((φ i).symm.trans (φ j)) ((φ i).symm.trans (φ j)).source)
    {n : ℕ} {G : ℕ → E ≃ₜ E} (hG : SmoothingGood φ r n G) (a : Fin n) :
    ContDiffOn ℝ r (smoothingStepCharts φ n G a).symm (smoothingStepCharts φ n G a).target :=
  contDiffOn_symm_trans_trans_homeomorph_symm (φ n) (φ a) (G a) (hφ a n) (hG.1 a a.isLt).2

theorem smoothingStepCharts_transition {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace X] {φ : ℕ → OpenPartialHomeomorph X E} {r n : ℕ} {G : ℕ → E ≃ₜ E}
    (hG : SmoothingGood φ r n G) (a b : Fin n) :
    ContDiffOn ℝ ∞ ((smoothingStepCharts φ n G a).symm.trans (smoothingStepCharts φ n G b))
      ((smoothingStepCharts φ n G a).symm.trans (smoothingStepCharts φ n G b)).source :=
  contDiffOn_symm_trans_symm_trans (φ n) ((φ a).trans (G a).toOpenPartialHomeomorph)
    ((φ b).trans (G b).toOpenPartialHomeomorph) (hG.2 a b a.isLt b.isLt)

private theorem exists_smoothingStep {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {X : Type*} [TopologicalSpace X] {r : ℕ} (hr : 1 ≤ r)
    (φ : ℕ → OpenPartialHomeomorph X E)
    (hφ : ∀ i j, ContDiffOn ℝ r ((φ i).symm.trans (φ j)) ((φ i).symm.trans (φ j)).source)
    (n : ℕ) (G : ℕ → E ≃ₜ E) :
    ∃ g : E ≃ₜ E,
      SmoothingGood φ r n G → SmoothingStepSpec r (smoothingStepCharts φ n G) g := by
  by_cases hG : SmoothingGood φ r n G
  · obtain ⟨g, hg⟩ := DifferentialGeometry.Analysis.exists_smoothing_homeomorph_trans hr
      (smoothingStepCharts φ n G) (smoothingStepCharts_contDiffOn hφ hG)
      (smoothingStepCharts_contDiffOn_symm hφ hG) (smoothingStepCharts_transition hG)
    exact ⟨g, fun _ => hg⟩
  · exact ⟨Homeomorph.refl E, fun h => absurd h hG⟩

def smoothingStep {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {X : Type*} [TopologicalSpace X] {r : ℕ} (hr : 1 ≤ r) (φ : ℕ → OpenPartialHomeomorph X E)
    (hφ : ∀ i j, ContDiffOn ℝ r ((φ i).symm.trans (φ j)) ((φ i).symm.trans (φ j)).source)
    (n : ℕ) (G : ℕ → E ≃ₜ E) : E ≃ₜ E :=
  Classical.choose (exists_smoothingStep hr φ hφ n G)

private theorem smoothingStep_spec {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {X : Type*} [TopologicalSpace X] {r : ℕ} (hr : 1 ≤ r)
    (φ : ℕ → OpenPartialHomeomorph X E)
    (hφ : ∀ i j, ContDiffOn ℝ r ((φ i).symm.trans (φ j)) ((φ i).symm.trans (φ j)).source)
    (n : ℕ) (G : ℕ → E ≃ₜ E) (hG : SmoothingGood φ r n G) :
    SmoothingStepSpec r (smoothingStepCharts φ n G) (smoothingStep hr φ hφ n G) :=
  Classical.choose_spec (exists_smoothingStep hr φ hφ n G) hG

def smoothingSeq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {X : Type*} [TopologicalSpace X] {r : ℕ} (hr : 1 ≤ r) (φ : ℕ → OpenPartialHomeomorph X E)
    (hφ : ∀ i j, ContDiffOn ℝ r ((φ i).symm.trans (φ j)) ((φ i).symm.trans (φ j)).source) :
    ℕ → E ≃ₜ E :=
  Nat.strongRec (motive := fun _ => E ≃ₜ E) fun n prev =>
    smoothingStep hr φ hφ n fun j => if h : j < n then prev j h else Homeomorph.refl E

private theorem smoothingSeq_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {X : Type*} [TopologicalSpace X] {r : ℕ} (hr : 1 ≤ r)
    (φ : ℕ → OpenPartialHomeomorph X E)
    (hφ : ∀ i j, ContDiffOn ℝ r ((φ i).symm.trans (φ j)) ((φ i).symm.trans (φ j)).source)
    (n : ℕ) :
    smoothingSeq hr φ hφ n = smoothingStep hr φ hφ n
      (fun j => if j < n then smoothingSeq hr φ hφ j else Homeomorph.refl E) :=
  Nat.strongRec_eq (motive := fun _ => E ≃ₜ E) (fun n prev =>
    smoothingStep hr φ hφ n fun j => if h : j < n then prev j h else Homeomorph.refl E) n

private theorem smoothingSeq_spec {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {X : Type*} [TopologicalSpace X] {r : ℕ} (hr : 1 ≤ r)
    (φ : ℕ → OpenPartialHomeomorph X E)
    (hφ : ∀ i j, ContDiffOn ℝ r ((φ i).symm.trans (φ j)) ((φ i).symm.trans (φ j)).source)
    (n : ℕ) (hn : SmoothingGood φ r n (smoothingSeq hr φ hφ)) :
    SmoothingStepSpec r (smoothingStepCharts φ n (smoothingSeq hr φ hφ))
      (smoothingSeq hr φ hφ n) := by
  have hagree : ∀ j, j < n → smoothingSeq hr φ hφ j =
      (if j < n then smoothingSeq hr φ hφ j else Homeomorph.refl E) :=
    fun j hj => (ite_eq_left hj).symm
  have hG : SmoothingGood φ r n
      (fun j => if j < n then smoothingSeq hr φ hφ j else Homeomorph.refl E) :=
    smoothingGood_congr hagree hn
  rw [smoothingSeq_eq hr φ hφ n, smoothingStepCharts_congr φ hagree]
  exact smoothingStep_spec hr φ hφ n _ hG

private theorem smoothingGood_succ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {X : Type*} [TopologicalSpace X] {r : ℕ} (hr : 1 ≤ r)
    (φ : ℕ → OpenPartialHomeomorph X E)
    (hφ : ∀ i j, ContDiffOn ℝ r ((φ i).symm.trans (φ j)) ((φ i).symm.trans (φ j)).source)
    (n : ℕ) (hn : SmoothingGood φ r n (smoothingSeq hr φ hφ)) :
    SmoothingGood φ r (n + 1) (smoothingSeq hr φ hφ) := by
  obtain ⟨hreg, -, -, h4, h5, -⟩ := smoothingSeq_spec hr φ hφ n hn
  obtain ⟨hn1, hn2⟩ := hn
  refine ⟨fun j hj => ?_, fun i j hi hj => ?_⟩
  · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj' | hjn
    · exact hn1 j hj'
    · rw [hjn]
      exact hreg
  · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi' | hin
    · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj' | hjn
      · exact hn2 i j hi' hj'
      · rw [hjn]
        exact contDiffOn_symm_trans_trans_homeomorph_of_chart (φ n)
          ((φ i).trans (smoothingSeq hr φ hφ i).toOpenPartialHomeomorph)
          (smoothingSeq hr φ hφ n) (h4 ⟨i, hi'⟩)
    · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj' | hjn
      · rw [hin]
        exact contDiffOn_trans_homeomorph_symm_trans_of_chart (φ n)
          ((φ j).trans (smoothingSeq hr φ hφ j).toOpenPartialHomeomorph)
          (smoothingSeq hr φ hφ n) (h5 ⟨j, hj'⟩)
      · rw [hin, hjn]
        exact contDiffOn_symm_trans_self _

private theorem smoothingGood_all {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {X : Type*} [TopologicalSpace X] {r : ℕ} (hr : 1 ≤ r)
    (φ : ℕ → OpenPartialHomeomorph X E)
    (hφ : ∀ i j, ContDiffOn ℝ r ((φ i).symm.trans (φ j)) ((φ i).symm.trans (φ j)).source)
    (n : ℕ) : SmoothingGood φ r n (smoothingSeq hr φ hφ) := by
  induction n with
  | zero => exact smoothingGood_zero φ r _
  | succ n ih => exact smoothingGood_succ hr φ hφ n ih

private theorem notMem_iUnion_smoothingStepCharts_source {E X : Type*} [NormedAddCommGroup E]
    [TopologicalSpace X] (φ : ℕ → OpenPartialHomeomorph X E) (n : ℕ)
    (G : ℕ → E ≃ₜ E) {x : E} (hx : x ∉ (φ n).target) :
    x ∉ ⋃ a, (smoothingStepCharts φ n G a).source := by
  intro hmem
  obtain ⟨a, ha⟩ := mem_iUnion.mp hmem
  obtain ⟨h1, -⟩ := ha
  exact hx h1

theorem exists_smoothing_homeomorphs_of_contDiff_atlas
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {X : Type*} [TopologicalSpace X] {r : ℕ} (hr : 1 ≤ r)
    (φ : ℕ → OpenPartialHomeomorph X E)
    (hφ : ∀ i j, ContDiffOn ℝ r ((φ i).symm.trans (φ j)) ((φ i).symm.trans (φ j)).source) :
    ∃ g : ℕ → E ≃ₜ E,
      (∀ k, ContDiff ℝ r (g k) ∧ ContDiff ℝ r (g k).symm) ∧
      (∀ k x, x ∉ (φ k).target → g k x = x) ∧
      (∀ k x, x ∉ (φ k).target → (g k).symm x = x) ∧
      (∀ k, g k '' (φ k).target = (φ k).target) ∧
      (∀ k, ((φ k).trans (g k).toOpenPartialHomeomorph).source = (φ k).source ∧
        ((φ k).trans (g k).toOpenPartialHomeomorph).target = (φ k).target) ∧
      (∀ i j, ContDiffOn ℝ ∞
        (((φ i).trans (g i).toOpenPartialHomeomorph).symm.trans
          ((φ j).trans (g j).toOpenPartialHomeomorph))
        (((φ i).trans (g i).toOpenPartialHomeomorph).symm.trans
          ((φ j).trans (g j).toOpenPartialHomeomorph)).source) ∧
      (∀ i j,
        ContDiffOn ℝ r ((φ i).symm.trans ((φ j).trans (g j).toOpenPartialHomeomorph))
          ((φ i).symm.trans ((φ j).trans (g j).toOpenPartialHomeomorph)).source ∧
        ContDiffOn ℝ r (((φ j).trans (g j).toOpenPartialHomeomorph).symm.trans (φ i))
          (((φ j).trans (g j).toOpenPartialHomeomorph).symm.trans (φ i)).source) ∧
      ∀ k x, 0 < (fderiv ℝ (g k) x).det := by
  have hgood := smoothingGood_all hr φ hφ
  have hreg : ∀ k, ContDiff ℝ r (smoothingSeq hr φ hφ k) ∧
      ContDiff ℝ r (smoothingSeq hr φ hφ k).symm :=
    fun k => (hgood (k + 1)).1 k (Nat.lt_add_one k)
  have hfix : ∀ k x, x ∉ (φ k).target →
      smoothingSeq hr φ hφ k x = x ∧ (smoothingSeq hr φ hφ k).symm x = x :=
    fun k x hx => (smoothingSeq_spec hr φ hφ k (hgood k)).2.1 x
      (notMem_iUnion_smoothingStepCharts_source φ k _ hx)
  have himg : ∀ k, smoothingSeq hr φ hφ k '' (φ k).target = (φ k).target :=
    fun k => DifferentialGeometry.Analysis.homeomorph_image_eq_self_of_apply_eq _
      fun x hx => (hfix k x hx).1
  refine ⟨smoothingSeq hr φ hφ, hreg, fun k x hx => (hfix k x hx).1,
    fun k x hx => (hfix k x hx).2, himg,
    fun k => ⟨trans_homeomorph_source (φ k) _, trans_homeomorph_target (φ k) _ (himg k)⟩,
    fun i j => (hgood (max i j + 1)).2 i j (Nat.lt_succ_of_le (le_max_left i j))
      (Nat.lt_succ_of_le (le_max_right i j)),
    fun i j => ⟨contDiffOn_symm_trans_trans_homeomorph (φ i) (φ j) _ (hφ i j) (hreg j).1,
      contDiffOn_trans_homeomorph_symm_trans (φ j) (φ i) _ (hφ j i) (hreg j).2⟩,
    fun k x => (smoothingSeq_spec hr φ hφ k (hgood k)).2.2.2.2.2 x⟩

theorem exists_smoothCompatibleAtlas_of_homeomorphs {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {X : Type*} [TopologicalSpace X] {ι : Type*} {r : ℕ}
    (φ : ι → OpenPartialHomeomorph X E) (hcover : ∀ x, ∃ i, x ∈ (φ i).source)
    (hφ : ∀ i j, ContDiffOn ℝ r ((φ i).symm.trans (φ j)) ((φ i).symm.trans (φ j)).source)
    (g : ι → E ≃ₜ E) (hreg : ∀ i, ContDiff ℝ r (g i) ∧ ContDiff ℝ r (g i).symm)
    (hfix : ∀ i x, x ∉ (φ i).target → g i x = x ∧ (g i).symm x = x)
    (hdet : ∀ i x, 0 < (fderiv ℝ (g i) x).det)
    (htr : ∀ i j, ContDiffOn ℝ ∞
      (((φ i).trans (g i).toOpenPartialHomeomorph).symm.trans
        ((φ j).trans (g j).toOpenPartialHomeomorph))
      (((φ i).trans (g i).toOpenPartialHomeomorph).symm.trans
        ((φ j).trans (g j).toOpenPartialHomeomorph)).source) :
    ∃ A : SmoothCompatibleAtlas E X ι,
      (∀ i, (A.chart i).source = (φ i).source ∧ (A.chart i).target = (φ i).target) ∧
      A.IsCompatible φ r ∧
      ∃ g : ι → E ≃ₜ E,
        (∀ i, A.chart i = (φ i).trans (g i).toOpenPartialHomeomorph) ∧
        (∀ i, ContDiff ℝ r (g i) ∧ ContDiff ℝ r (g i).symm) ∧
        (∀ i x, x ∉ (φ i).target → g i x = x ∧ (g i).symm x = x) ∧
        ∀ i x, 0 < (fderiv ℝ (g i) x).det := by
  have himg : ∀ i, g i '' (φ i).target = (φ i).target :=
    fun i => DifferentialGeometry.Analysis.homeomorph_image_eq_self_of_apply_eq (g i)
      fun x hx => (hfix i x hx).1
  exact ⟨⟨fun i => (φ i).trans (g i).toOpenPartialHomeomorph,
      fun x => (hcover x).imp fun _ hi => ⟨hi, trivial⟩, htr⟩,
    fun i => ⟨trans_homeomorph_source (φ i) (g i), trans_homeomorph_target (φ i) (g i) (himg i)⟩,
    fun i j => ⟨contDiffOn_symm_trans_trans_homeomorph (φ i) (φ j) (g j) (hφ i j) (hreg j).1,
      contDiffOn_trans_homeomorph_symm_trans (φ j) (φ i) (g j) (hφ j i) (hreg j).2⟩,
    g, fun _ => rfl, hreg, hfix, hdet⟩

theorem exists_smoothCompatibleAtlas
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {X : Type*} [TopologicalSpace X] {ι : Type*} [Countable ι] {r : ℕ} (hr : 1 ≤ r)
    (φ : ι → OpenPartialHomeomorph X E) (hcover : ∀ x, ∃ i, x ∈ (φ i).source)
    (hφ : ∀ i j, ContDiffOn ℝ r ((φ i).symm.trans (φ j)) ((φ i).symm.trans (φ j)).source) :
    ∃ A : SmoothCompatibleAtlas E X ι,
      (∀ i, (A.chart i).source = (φ i).source ∧ (A.chart i).target = (φ i).target) ∧
      A.IsCompatible φ r ∧
      ∃ g : ι → E ≃ₜ E,
        (∀ i, A.chart i = (φ i).trans (g i).toOpenPartialHomeomorph) ∧
        (∀ i, ContDiff ℝ r (g i) ∧ ContDiff ℝ r (g i).symm) ∧
        (∀ i x, x ∉ (φ i).target → g i x = x ∧ (g i).symm x = x) ∧
        ∀ i x, 0 < (fderiv ℝ (g i) x).det := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact exists_smoothCompatibleAtlas_of_homeomorphs φ hcover hφ (fun _ => Homeomorph.refl E)
      (fun i => isEmptyElim i) (fun i => isEmptyElim i) (fun i => isEmptyElim i)
      (fun i => isEmptyElim i)
  · obtain ⟨s, hs⟩ := exists_surjective_nat ι
    obtain ⟨g, hreg, hfix1, hfix2, -, -, htr, -, hdet⟩ :=
      exists_smoothing_homeomorphs_of_contDiff_atlas hr (fun k => φ (s k))
        (fun i j => hφ (s i) (s j))
    refine exists_smoothCompatibleAtlas_of_homeomorphs φ hcover hφ (fun i => g (surjInv hs i))
      (fun i => hreg (surjInv hs i)) (fun i x hx => ?_) (fun i x => hdet (surjInv hs i) x)
      (fun i j => ?_)
    · have hx' : x ∉ (φ (s (surjInv hs i))).target := by
        rw [surjInv_eq hs i]
        exact hx
      exact ⟨hfix1 (surjInv hs i) x hx', hfix2 (surjInv hs i) x hx'⟩
    · have h : ContDiffOn ℝ ∞
          (((φ (s (surjInv hs i))).trans (g (surjInv hs i)).toOpenPartialHomeomorph).symm.trans
            ((φ (s (surjInv hs j))).trans (g (surjInv hs j)).toOpenPartialHomeomorph))
          (((φ (s (surjInv hs i))).trans (g (surjInv hs i)).toOpenPartialHomeomorph).symm.trans
            ((φ (s (surjInv hs j))).trans (g (surjInv hs j)).toOpenPartialHomeomorph)).source :=
        htr (surjInv hs i) (surjInv hs j)
      rw [surjInv_eq hs i, surjInv_eq hs j] at h
      exact h

end DifferentialGeometry.Topology.Manifold
