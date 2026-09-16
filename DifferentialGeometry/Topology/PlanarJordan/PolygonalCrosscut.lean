import DifferentialGeometry.Topology.PlanarJordan.CrosscutExtension
import DifferentialGeometry.Topology.Homeomorph.UniformGluing
import DifferentialGeometry.Topology.PiecewiseLinear.InteriorAccess

open Set Topology

namespace DifferentialGeometry.Topology.PlanarJordan

open Schoenflies PiecewiseLinear

theorem exists_homeomorph_polygonal_crosscut
    {D P : Set Plane} {p q : Plane} (hD : IsPLBall 2 D)
    (hP : IsArcBetween P p q) (hp : p ∈ frontier D) (hq : q ∈ frontier D)
    (hPI : P \ {p, q} ⊆ interior D) :
    ∃ e : Plane ≃ₜ Plane, IsPolygonal (e '' P) ∧ EqOn e id (interior D)ᶜ ∧
      ∀ x, dist (e x) x ≤ Metric.diam D := by
  have hpq : p ≠ q := by
    obtain ⟨f, _, hi, _, hf0, hf1⟩ := hP
    intro hpq
    exact zero_ne_one (hi zero_mem_I one_mem_I (hf0.trans (hpq.trans hf1.symm)))
  obtain ⟨Q, hQ⟩ := hD.exists_isCrosscut hp hq hpq
  obtain ⟨f⟩ := exists_arcHomeo hP hQ.arc
  have hinside : inside (frontier D) = interior D := hD.interior_eq_inside_frontier.symm
  obtain ⟨e, heP, hefix, hedist⟩ := exists_homeomorph_extending_crosscut
    (isJordanCurve_of_isPLSphere_one hD.isPLSphere_frontier) hP hQ.arc hp hq
    (hinside.symm ▸ hPI) hQ.sdiff_subset f
  have hclosed : frontier D ∪ inside (frontier D) = D := by
    rw [hinside, union_comm, ← closure_eq_interior_union_frontier, hD.isPolyhedron.isClosed.closure_eq]
  refine ⟨e, ?_, ?_, ?_⟩
  · rw [heP.image_eq, f.image_eq]
    exact hQ.polygonal
  · simpa only [hinside] using hefix
  · simpa only [hclosed] using hedist

theorem exists_homeomorph_polygonal_crosscuts_of_tendsto_diam {ι : Type*}
    {D P : ι → Set Plane} {p q : ι → Plane} (hD : ∀ i, IsPLBall 2 (D i))
    (hdis : Pairwise fun i j => Disjoint (D i) (D j))
    (hcontract : Filter.Tendsto (fun i => Metric.diam (D i)) Filter.cofinite (𝓝 0))
    (hP : ∀ i, IsArcBetween (P i) (p i) (q i))
    (hp : ∀ i, p i ∈ frontier (D i)) (hq : ∀ i, q i ∈ frontier (D i))
    (hPI : ∀ i, P i \ {p i, q i} ⊆ interior (D i))
    {ε : Plane → ℝ} (hε : ∀ x, 0 < ε x)
    (hdiam : ∀ i, ∀ x ∈ D i, Metric.diam (D i) < ε x) :
    ∃ e : Plane ≃ₜ Plane, (∀ i, IsPolygonal (e '' P i)) ∧
      EqOn e id (⋃ i, interior (D i))ᶜ ∧ ∀ x, dist (e x) x < ε x := by
  classical
  choose f hfpoly hffix hfdist using fun i =>
    exists_homeomorph_polygonal_crosscut (hD i) (hP i) (hp i) (hq i) (hPI i)
  have hfix (i : ι) : EqOn (f i) id (D i)ᶜ :=
    (hffix i).mono (compl_subset_compl.mpr interior_subset)
  obtain ⟨e, he, hefix, hedist⟩ :=
    Homeomorph.exists_gluing_dist_lt_of_tendstoUniformly f D hfix hdis
      (Homeomorph.tendstoUniformly_id_of_tendsto_diam f D hfix
        (fun i => (hD i).isPolyhedron.isCompact.isBounded) hcontract) hε
    (fun i x hx => (hfdist i x).trans_lt (hdiam i x hx))
  have hPD (i : ι) : P i ⊆ D i := by
    intro x hx
    by_cases hends : x ∈ ({p i, q i} : Set Plane)
    · rcases hends with rfl | rfl
      · exact (hD i).isPolyhedron.isClosed.frontier_subset (hp i)
      · exact (hD i).isPolyhedron.isClosed.frontier_subset (hq i)
    · exact interior_subset (hPI i ⟨hx, hends⟩)
  refine ⟨e, fun i => ?_, ?_, hedist⟩
  · rw [((he i).mono (hPD i)).image_eq]
    exact hfpoly i
  · intro x hx
    by_cases hxD : x ∈ ⋃ i, D i
    · obtain ⟨i, hxi⟩ := mem_iUnion.mp hxD
      rw [he i hxi]
      exact hffix i (fun hi => hx (mem_iUnion.mpr ⟨i, hi⟩))
    · exact hefix hxD

theorem exists_homeomorph_polygonal_crosscuts {ι : Type*} [Finite ι]
    {D P : ι → Set Plane} {p q : ι → Plane} (hD : ∀ i, IsPLBall 2 (D i))
    (hdis : Pairwise fun i j => Disjoint (D i) (D j))
    (hP : ∀ i, IsArcBetween (P i) (p i) (q i))
    (hp : ∀ i, p i ∈ frontier (D i)) (hq : ∀ i, q i ∈ frontier (D i))
    (hPI : ∀ i, P i \ {p i, q i} ⊆ interior (D i))
    {ε : Plane → ℝ} (hε : ∀ x, 0 < ε x)
    (hdiam : ∀ i, ∀ x ∈ D i, Metric.diam (D i) < ε x) :
    ∃ e : Plane ≃ₜ Plane, (∀ i, IsPolygonal (e '' P i)) ∧
      EqOn e id (⋃ i, interior (D i))ᶜ ∧ ∀ x, dist (e x) x < ε x := by
  apply exists_homeomorph_polygonal_crosscuts_of_tendsto_diam hD hdis _ hP hp hq hPI hε hdiam
  simp only [Filter.cofinite_eq_bot, Filter.tendsto_bot]

end DifferentialGeometry.Topology.PlanarJordan
