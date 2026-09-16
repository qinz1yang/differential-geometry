import DifferentialGeometry.Topology.Morse.CriticalPoints
import DifferentialGeometry.Topology.Order.FiniteSeparation
import Mathlib.Topology.Order.IntermediateValue

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Morse

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H}

theorem exists_regular_level_between_of_finite_criticalPoints
    {f : M → ℝ} (hfinite : {p | IsCriticalPointAt I f p}.Finite)
    {a b : ℝ} (hab : a < b) :
    ∃ c ∈ Ioo a b, ∀ p, f p = c → ¬ IsCriticalPointAt I f p := by
  have hvalues : (insert a (insert b (f '' {p | IsCriticalPointAt I f p}))).Finite :=
    ((hfinite.image f).insert b).insert a
  obtain ⟨L, _, hdisj, hbetween⟩ := hvalues.exists_finite_disjoint_inter_Ioo_nonempty
  obtain ⟨c, hcL, hac, hcb⟩ := hbetween a (mem_insert _ _)
    b (mem_insert_of_mem _ (mem_insert _ _)) hab
  refine ⟨c, ⟨hac, hcb⟩, ?_⟩
  intro p hp hc
  exact disjoint_left.mp hdisj
    (mem_insert_of_mem _ (mem_insert_of_mem _ ⟨p, hc, hp⟩)) hcL

theorem exists_finite_regular_levels_separating_criticalPoints
    {f : M → ℝ} (hf : Continuous f) (hfinite : {p | IsCriticalPointAt I f p}.Finite)
    (hinj : InjOn f {p | IsCriticalPointAt I f p}) :
    ∃ L : Set ℝ, L.Finite ∧
      (∀ t ∈ L, ∀ p, f p = t → ¬ IsCriticalPointAt I f p) ∧
      ∀ S : Set M, IsPreconnected S → Disjoint S (f ⁻¹' L) →
        (S ∩ {p | IsCriticalPointAt I f p}).Subsingleton := by
  obtain ⟨L, hL, hdisj, hbetween⟩ := (hfinite.image f).exists_finite_disjoint_inter_Ioo_nonempty
  have hreg (t : ℝ) (ht : t ∈ L) (p : M) (hp : f p = t) :
      ¬ IsCriticalPointAt I f p := by
    intro hc
    exact disjoint_left.mp hdisj ⟨p, hc, hp⟩ ht
  refine ⟨L, hL, hreg, ?_⟩
  intro S hS havoid p hp q hq
  apply hinj hp.2 hq.2
  have horder : OrdConnected (f '' S) := (hS.image f hf.continuousOn).ordConnected
  have hnot (a : M) (ha : a ∈ S) (hac : IsCriticalPointAt I f a)
      (b : M) (hb : b ∈ S) (hbc : IsCriticalPointAt I f b) (hab : f a < f b) : False := by
    obtain ⟨t, htL, ht⟩ := hbetween (f a) (mem_image_of_mem f hac)
      (f b) (mem_image_of_mem f hbc) hab
    have htimage : t ∈ f '' S := horder.out (mem_image_of_mem f ha)
      (mem_image_of_mem f hb) ⟨ht.1.le, ht.2.le⟩
    obtain ⟨x, hx, hxt⟩ := htimage
    exact disjoint_left.mp havoid hx (show f x ∈ L by rw [hxt]; exact htL)
  rcases lt_trichotomy (f p) (f q) with hlt | heq | hgt
  · exact False.elim (hnot p hp.1 hp.2 q hq.1 hq.2 hlt)
  · exact heq
  · exact False.elim (hnot q hq.1 hq.2 p hp.1 hp.2 hgt)

theorem exists_finite_regular_levels_separating_criticalPoints_of_isNondegenerate
    [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I 2 M] [CompactSpace M]
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    (hnd : ∀ p, IsCriticalPointAt I f p → IsNondegenerateCriticalPointAt I f p)
    (hinj : InjOn f {p | IsCriticalPointAt I f p}) :
    ∃ L : Set ℝ, L.Finite ∧
      (∀ t ∈ L, ∀ p, f p = t → ¬ IsCriticalPointAt I f p) ∧
      ∀ S : Set M, IsPreconnected S → Disjoint S (f ⁻¹' L) →
        (S ∩ {p | IsCriticalPointAt I f p}).Subsingleton := by
  have hfinite : {p | IsCriticalPointAt I f p}.Finite := by
    simpa only [univ_inter, criticalPoints] using finite_inter_criticalPoints_of_isCompact hf isCompact_univ
      (fun p _ hp => hnd p hp)
  exact exists_finite_regular_levels_separating_criticalPoints hf.continuous hfinite hinj

theorem exists_pos_regular_strip_sdiff [I.Boundaryless] [IsManifold I 1 M]
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 1 f)
    {K U : Set M} (hK : IsCompact K) (hU : IsOpen U) {c : ℝ}
    (hlevel : ∀ x ∈ K, f x = c → IsCriticalPointAt I f x → x ∈ U) :
    ∃ δ > 0, IsCompact ((K ∩ f ⁻¹' Icc (c - δ) (c + δ)) \ U) ∧
      ∀ x ∈ (K ∩ f ⁻¹' Icc (c - δ) (c + δ)) \ U,
        ¬ IsCriticalPointAt I f x := by
  let B := (K ∩ criticalPoints I f) \ U
  have hB : IsCompact B := (hK.inter_right (isClosed_criticalPoints_of_contMDiff_one f hf)).diff hU
  have hc : c ∉ f '' B := by
    rintro ⟨x, hx, hxc⟩
    exact hx.2 (hlevel x hx.1.1 hxc hx.1.2)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
    ((hB.image hf.continuous).isClosed.isOpen_compl.mem_nhds hc)
  refine ⟨δ / 2, half_pos hδ,
    (hK.inter_right (isClosed_Icc.preimage hf.continuous)).diff hU, ?_⟩
  intro x hx hxcrit
  have hxball : f x ∈ Metric.ball c δ := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hx.1.2.1, hx.1.2.2]
  exact hball hxball ⟨x, ⟨⟨hx.1.1, hxcrit⟩, hx.2⟩, rfl⟩

end DifferentialGeometry.Topology.Morse
