import DifferentialGeometry.Topology.VanKampen.CoveredPath
import Mathlib.Topology.Homotopy.LocallyContractible
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped Topology
namespace GC.Topology
universe u v

theorem normed_stronglyLocallyContractible (E : Type u) [NormedAddCommGroup E]
    [NormedSpace ℝ E] : StronglyLocallyContractibleSpace E := by
  apply StronglyLocallyContractibleSpace.of_bases (fun x : E => nhds_basis_ball)
  intro x r hr
  exact (convex_ball x r).contractibleSpace ⟨x, mem_ball_self hr⟩

theorem charted_stronglyLocallyContractible (H : Type v) [TopologicalSpace H]
    [StronglyLocallyContractibleSpace H] (X : Type u) [TopologicalSpace X]
    [ChartedSpace H X] : StronglyLocallyContractibleSpace X := by
  have hb : ∀ x : X, (𝓝 x).HasBasis
      (fun s : Set H => s ∈ 𝓝 (chartAt H x x) ∧ ContractibleSpace s ∧
        s ⊆ (chartAt H x).target) (fun s => (chartAt H x).symm '' s) := by
    intro x
    rw [← (chartAt H x).symm_map_nhds_eq (mem_chart_source H x)]
    exact ((contractible_basis (chartAt H x x)).hasBasis_self_subset
      (chart_target_mem_nhds H x)).map _
  apply StronglyLocallyContractibleSpace.of_bases hb
  rintro x s ⟨hs, hc, hsub⟩
  let : ContractibleSpace s := hc
  exact ((chartAt H x).symm.homeomorphOfImageSubsetSource hsub rfl).symm.contractibleSpace

theorem exists_finite_pairwise_simplyConnected_cover (X : Type u)
    [MetricSpace X] [CompactSpace X] [StronglyLocallyContractibleSpace X] :
    ∃ (ι : Type u) (_ : Fintype ι) (V : ι → Set X),
      (∀ i, IsOpen (V i) ∧ IsPathConnected (V i)) ∧ (⋃ i, V i) = univ ∧
      ∀ i j, (V i ∩ V j).Nonempty →
        ∃ W : Set X, SimplyConnectedSpace W ∧ V i ∪ V j ⊆ W := by
  classical
  have hc : ∀ x : X, ∃ A : Set X, A ∈ 𝓝 x ∧ ContractibleSpace A :=
    fun x => (contractible_basis x).ex_mem
  choose A hA hAc using hc
  have hcover : (univ : Set X) ⊆ ⋃ x, interior (A x) := by
    intro x _
    exact mem_iUnion.mpr ⟨x, mem_interior_iff_mem_nhds.mpr (hA x)⟩
  obtain ⟨r, hr, hball⟩ := lebesgue_number_lemma_of_metric isCompact_univ
    (fun x => isOpen_interior (s := A x)) hcover
  have hv : ∀ x : X, ∃ V : Set X,
      (IsOpen V ∧ x ∈ V ∧ IsPathConnected V) ∧ V ⊆ ball x (r / 4) := by
    intro x
    exact (isOpen_isPathConnected_basis x).mem_iff.mp (ball_mem_nhds x (by positivity))
  choose V hV hsmall using hv
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover V (fun x => (hV x).1) (by
    intro x _
    exact mem_iUnion.mpr ⟨x, (hV x).2.1⟩)
  refine ⟨↥t, inferInstance, fun i => V i.val, ?_, ?_, ?_⟩
  · intro i
    exact ⟨(hV i.val).1, (hV i.val).2.2⟩
  · apply eq_univ_of_forall
    intro x
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (ht (mem_univ x))
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
  · intro i j hij
    obtain ⟨z, hzi, hzj⟩ := hij
    obtain ⟨a, ha⟩ := hball i.val (mem_univ _)
    let : ContractibleSpace (A a) := hAc a
    refine ⟨A a, SimplyConnectedSpace.ofContractible _, ?_⟩
    apply Subset.trans _ (ha.trans interior_subset)
    rintro q (hqi | hqj)
    · have hq := hsmall i.val hqi
      rw [mem_ball] at hq ⊢
      linarith
    · have hq := hsmall j.val hqj
      have hzj' := hsmall j.val hzj
      have hzi' := hsmall i.val hzi
      rw [mem_ball] at hq hzj' hzi' ⊢
      have htri := (dist_triangle q j.val i.val).trans
        (add_le_add_right (dist_triangle j.val z i.val) _)
      rw [dist_comm j.val z] at htri
      linarith

end GC.Topology
