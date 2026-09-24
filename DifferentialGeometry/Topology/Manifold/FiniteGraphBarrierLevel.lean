import DifferentialGeometry.Topology.Manifold.ProductChartCollar
import Mathlib.Topology.Order.Compact

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

theorem exists_level_with_gap_above_finite_graphs
    {X ι : Type*} [TopologicalSpace X] [CompactSpace X] [Finite ι]
    (f : ι → X → ℝ) (hf : ∀ i, Continuous (f i)) {a b : ℝ} (hab : a < b)
    (hfb : ∀ i x, f i x < b) :
    ∃ c r : ℝ, 0 < r ∧ a < c - r ∧ c + r < b ∧ ∀ i x, f i x < c - r := by
  let K : Set ℝ := {a} ∪ ⋃ i, range (f i)
  have hK : IsCompact K := isCompact_singleton.union
    (isCompact_iUnion (fun i => isCompact_range (hf i)))
  have haK : a ∈ K := Or.inl rfl
  obtain ⟨m, hm, hmax⟩ := hK.exists_isMaxOn ⟨a, haK⟩ continuous_id.continuousOn
  have hmb : m < b := by
    rcases hm with hm | hm
    · exact (Set.mem_singleton_iff.mp hm) ▸ hab
    · obtain ⟨i, x, rfl⟩ := mem_iUnion.mp hm
      exact hfb i x
  have ham : a ≤ m := hmax haK
  refine ⟨(m + b) / 2, (b - m) / 4, by linarith, by linarith, by linarith, ?_⟩
  intro i x
  have hfm : f i x ≤ m := hmax (Or.inr (mem_iUnion.mpr ⟨i, mem_range_self x⟩))
  linarith

variable {E F H G N M ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
  {J : ModelWithCorners ℝ F G}
  [TopologicalSpace N] [ChartedSpace H N] [CompactSpace N]
  [TopologicalSpace M] [ChartedSpace G M] [Finite ι]

theorem exists_product_chart_level_collar_disjoint_finite_graphs
    (O : TopologicalSpace.Opens (N × ℝ)) (V : TopologicalSpace.Opens M)
    (Φ : O ≃ₘ⟮I.prod 𝓘(ℝ), J⟯ V)
    (f : ι → N → ℝ) (hf : ∀ i, Continuous (f i))
    {a b : ℝ} (hab : a < b) (hfa : ∀ i p, a ≤ f i p) (hfb : ∀ i p, f i p < b)
    (hslab : ∀ p t, t ∈ Icc a b → (p, t) ∈ O) :
    ∃ c : ℝ, a < c ∧ c < b ∧ ∃ hc : ∀ p, (p, c) ∈ O,
      ∃ C : SmoothTwoSidedCollar I J (fun p => (Φ ⟨(p, c), hc p⟩ : M)),
        (∀ p : N × symmetricOpenInterval C.radius,
          ∃ hp : (p.1, c + (p.2 : ℝ)) ∈ O,
            C.toFun p = (Φ ⟨(p.1, c + (p.2 : ℝ)), hp⟩ : M)) ∧
        (∀ p : N × symmetricOpenInterval C.radius, a < c + (p.2 : ℝ) ∧ c + (p.2 : ℝ) < b) ∧
        (∀ q : O, (∃ i, q.1.2 ≤ f i q.1.1) → q.1.2 < c - C.radius) ∧
        ∀ i, Disjoint
          (range (fun p : N => (Φ ⟨(p, f i p), hslab p _ ⟨hfa i p, (hfb i p).le⟩⟩ : M)))
          (range C.toFun) := by
  obtain ⟨c, r, hr, hac, hcb, hfc⟩ :=
    exists_level_with_gap_above_finite_graphs f hf hab hfb
  have hac' : a < c := by linarith
  have hcb' : c < b := by linarith
  have hc : ∀ p, (p, c) ∈ O := fun p => hslab p c ⟨hac'.le, hcb'.le⟩
  obtain ⟨C, hCr, _, hC⟩ := exists_smoothTwoSidedCollar_of_product_chart_graph
    O V Φ (fun _ => c) contMDiff_const hc hr
  refine ⟨c, hac', hcb', hc, C, hC, ?_, ?_, ?_⟩
  · intro p
    have hp : -C.radius < (p.2 : ℝ) ∧ (p.2 : ℝ) < C.radius := p.2.property
    constructor <;> linarith [hp.1, hp.2]
  · intro q hq
    obtain ⟨i, hi⟩ := hq
    have hfi := hfc i q.1.1
    linarith
  · intro i
    apply Set.disjoint_left.mpr
    rintro x ⟨p, hpx⟩ ⟨q, hqx⟩
    obtain ⟨hq, hqeq⟩ := hC q
    have heq : (Φ ⟨(p, f i p), hslab p _ ⟨hfa i p, (hfb i p).le⟩⟩ : M) =
        (Φ ⟨(q.1, c + (q.2 : ℝ)), hq⟩ : M) := hpx.trans (hqx.symm.trans hqeq)
    have heq' := congrArg Subtype.val (Φ.injective (Subtype.ext heq))
    have hheight : f i p = c + (q.2 : ℝ) := congrArg Prod.snd heq'
    have hqlo := q.2.property.1
    have hfi := hfc i p
    linarith

end DifferentialGeometry.Topology
