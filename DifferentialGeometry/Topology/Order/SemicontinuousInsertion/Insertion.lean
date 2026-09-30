import Mathlib.Topology.Semicontinuity.Michael
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.MetricSpace.PartitionOfUnity
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.UrysohnsLemma

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Topology

theorem exists_closed_support_cutoff {X : Type*} [TopologicalSpace X] [NormalSpace X]
    {A O : Set X} (hA : IsClosed A) (hO : IsOpen O) (hAO : A ⊆ O) :
    ∃ χ : C(X, ℝ), tsupport χ ⊆ O ∧ (∀ x ∈ A, χ x = 1) ∧
      ∀ x, χ x ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨V, hV, hAV, hVO⟩ := normal_exists_closure_subset hA hO hAO
  obtain ⟨χ, hχ0, hχ1, hχb⟩ := exists_continuous_zero_one_of_isClosed
    hV.isClosed_compl hA (disjoint_left.mpr fun x hx hxA => hx (hAV hxA))
  refine ⟨χ, ?_, hχ1, hχb⟩
  apply (closure_mono ?_).trans hVO
  intro x hx
  by_contra hxV
  exact hx (hχ0 hxV)

theorem exists_continuous_between_strict {X : Type*} [TopologicalSpace X]
    [NormalSpace X] [ParacompactSpace X] {f g : X → ℝ}
    (hf : UpperSemicontinuous f) (hg : LowerSemicontinuous g) (hfg : ∀ x, f x < g x) :
    ∃ h : X → ℝ, Continuous h ∧ ∀ x, f x < h x ∧ h x < g x := by
  have hsections : HasOpenLowerSections (fun x => Ioo (f x) (g x)) := by
    rw [hasOpenLowerSections_iff_isOpen]
    intro y
    exact (hf.isOpen_preimage y).inter (hg.isOpen_preimage y)
  exact hsections.exists_continuous_selection
    (fun x => nonempty_Ioo.mpr (hfg x)) (fun x => convex_Ioo (f x) (g x))

theorem exists_continuous_graph_width {X : Type*} [MetricSpace X] {f : X → ℝ}
    (hf : Continuous f) {U : Set (X × ℝ)} (hU : IsOpen U)
    (hgraph : ∀ x, (x, f x) ∈ U) :
    ∃ δ : X → ℝ, Continuous δ ∧ (∀ x, 0 < δ x) ∧
      ∀ x t, |t - f x| ≤ δ x → (x, t) ∈ U := by
  let K : Set (X × ℝ) := {p | p.2 = f p.1}
  have hK : IsClosed K := isClosed_eq continuous_snd (hf.comp continuous_fst)
  have hKU : K ⊆ U := by
    rintro ⟨x, t⟩ hp
    change t = f x at hp
    subst t
    exact hgraph x
  obtain ⟨d, hd, hdU⟩ := Metric.exists_continuous_real_forall_closedBall_subset
    (K := fun _ : Unit => K) (U := fun _ : Unit => U)
    (fun _ => hK) (fun _ => hU) (fun _ => hKU) (locallyFinite_of_finite _)
  refine ⟨fun x => d (x, f x), d.continuous.comp (continuous_id.prodMk hf),
    fun x => hd (x, f x), ?_⟩
  intro x t ht
  apply hdU () (x, f x) rfl
  rw [mem_closedBall, Prod.dist_eq, dist_self, Real.dist_eq, max_eq_right (abs_nonneg _)]
  exact ht

theorem exists_continuous_graph_majorant {X : Type*} [MetricSpace X] {f : X → ℝ}
    (hf : Continuous f) {U : Set (X × ℝ)} (hU : IsOpen U)
    (hgraph : ∀ x, (x, f x) ∈ U) :
    ∃ g : X → ℝ, Continuous g ∧ (∀ x, f x < g x) ∧
      ∀ x t, t ∈ Icc (f x) (g x) → (x, t) ∈ U := by
  obtain ⟨δ, hδc, hδ, hδU⟩ := exists_continuous_graph_width hf hU hgraph
  refine ⟨fun x => f x + δ x, hf.add hδc, fun x => by linarith [hδ x], ?_⟩
  intro x t ht
  apply hδU x t
  rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]
  linarith [ht.2]

end DifferentialGeometry.Topology.Engulfing
