import DifferentialGeometry.Geometry.Neck.FiniteFrontierEnd
import DifferentialGeometry.Geometry.Neck.SpatialCapFilling
import DifferentialGeometry.Geometry.Neck.SpatialComponentCollar
import Batteries.Tactic.OpenPrivate

noncomputable section
open Set Manifold
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open private RecordedNeckSphere RecordedNeckSphere.map RecordedNeckSphere.range_map
  RecordedNeckSphere.point RecordedNeckSphere.neck RecordedNeckSphere.level
  RecordedNeckSphere.bound RecordedNeckSphere.param RecordedNeckSphere.mk
  RecordedNeckSphere.isPreconnected_range
  NeckFrontierState.region NeckFrontierState.compact NeckFrontierState.nonempty
  NeckFrontierState.regular NeckFrontierState.alive NeckFrontierState.sphere
  NeckFrontierState.frontier NeckFrontierState.disjoint NeckFrontierState.mk
  NeckFrontierState OrdinaryNeckMoveAtCentral OrdinaryNeckMoveAt OrdinaryNeckMove
  NeckFrontierState.exists_step_at_of_neck_central
  NeckFrontierState.exists_step_at_of_neck_preserving_incident_components NeckFrontierState.alive_nonempty
  NeckFrontierState.exists_saved_end_family_of_fair_process
  NeckFrontierState.exists_scheduled_process_of_transition
  NeckFrontierState.exists_proper_end_of_process from DifferentialGeometry.Geometry.Neck.FiniteFrontierEnd

universe u v
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [PreconnectedSpace M]
  (g : SmoothRiemannianMetric I3 M) (eps : ℝ) (ι : Type v)

omit [PreconnectedSpace M] in
private theorem spatial_cap_frontier_step_of_incident_anchor
    (W : NeckFrontierState g eps ι)
    (i : ι) (hi : i ∈ NeckFrontierState.alive W)
    {U : Set M} (cap : CapCore U)
    (hinside : range (RecordedNeckSphere.map g eps (NeckFrontierState.sphere W i)) ⊆
      interior U)
    (x : M)
    (hincident : (range (RecordedNeckSphere.map g eps (NeckFrontierState.sphere W i)) ∩
      closure (connectedComponentIn (interior (NeckFrontierState.region W)) x)).Nonempty)
    (hanchor : x ∉ interior U) :
    ∃ V : NeckFrontierState g eps ι,
      NeckFrontierState.region W ⊆ NeckFrontierState.region V ∧
      (∀ (k : ι) (a : M),
        (range (RecordedNeckSphere.map g eps (NeckFrontierState.sphere W k)) ∩
          closure (connectedComponentIn (interior (NeckFrontierState.region W)) a)).Nonempty →
        a ∈ interior (NeckFrontierState.region V) ∧
        (range (RecordedNeckSphere.map g eps (NeckFrontierState.sphere V k)) ∩
          closure (connectedComponentIn (interior (NeckFrontierState.region V)) a)).Nonempty) ∧
      NeckFrontierState.alive V ⊂ NeckFrontierState.alive W ∧
      NeckFrontierState.sphere V = NeckFrontierState.sphere W ∧
      i ∉ NeckFrontierState.alive V := by
  classical
  have hfront : frontier (NeckFrontierState.region W) = ⋃ j ∈ NeckFrontierState.alive W,
      range (fun z : Sphere 2 => (RecordedNeckSphere.neck (NeckFrontierState.sphere W j)).map
        (z, RecordedNeckSphere.level (NeckFrontierState.sphere W j))) := by
    simpa only [RecordedNeckSphere.range_map] using NeckFrontierState.frontier W
  have hpair : (NeckFrontierState.alive W : Set ι).Pairwise (fun j k =>
      Disjoint (range (fun z : Sphere 2 => (RecordedNeckSphere.neck (NeckFrontierState.sphere W j)).map
        (z, RecordedNeckSphere.level (NeckFrontierState.sphere W j))))
        (range (fun z : Sphere 2 => (RecordedNeckSphere.neck (NeckFrontierState.sphere W k)).map
          (z, RecordedNeckSphere.level (NeckFrontierState.sphere W k))))) := by
    simpa only [RecordedNeckSphere.range_map] using NeckFrontierState.disjoint W
  have hlevel (j : ι) : |RecordedNeckSphere.level (NeckFrontierState.sphere W j)| < eps⁻¹ := by
    have hlen : (4 : ℝ) < eps⁻¹ :=
      (lt_inv_comm₀ (by norm_num)
        (RecordedNeckSphere.neck (NeckFrontierState.sphere W j)).eps_pos).mpr
        (by linarith [(RecordedNeckSphere.neck (NeckFrontierState.sphere W j)).eps_small])
    exact (RecordedNeckSphere.bound (NeckFrontierState.sphere W j)).trans_lt hlen
  have hx : x ∈ interior (NeckFrontierState.region W) :=
    connectedComponentIn_nonempty_iff.mp (closure_nonempty_iff.mp
      ⟨hincident.choose, hincident.choose_spec.2⟩)
  obtain ⟨K, remaining, _, _, _, _, hVK, hVR, hremaining,
      hVF, _, _, hiout, _, _⟩ :=
    exists_cap_filling_on_finite_spatial_neck_frontier_of_incident_component_avoidance
      (NeckFrontierState.alive W)
      (fun j => RecordedNeckSphere.point (NeckFrontierState.sphere W j))
      (fun j => RecordedNeckSphere.neck (NeckFrontierState.sphere W j))
      (fun j => RecordedNeckSphere.level (NeckFrontierState.sphere W j))
      (fun j _ => hlevel j) hpair i hi cap
      (by simpa only [RecordedNeckSphere.range_map] using hinside)
      (NeckFrontierState.compact W) (NeckFrontierState.regular W) hfront x
      (by simpa only [RecordedNeckSphere.range_map] using hincident)
      ⟨x, mem_connectedComponentIn hx, hanchor⟩
  let V : NeckFrontierState g eps ι :=
    NeckFrontierState.mk (NeckFrontierState.region W ∪ K) hVK
      ((NeckFrontierState.nonempty W).mono subset_union_left) hVR
      remaining (NeckFrontierState.sphere W)
      (by simpa only [RecordedNeckSphere.range_map] using hVF)
      (fun j hj k hk hjk => NeckFrontierState.disjoint W
        (hremaining hj) (hremaining hk) hjk)
  refine ⟨V, subset_union_left, ?_, ?_, rfl, hiout⟩
  · intro k a ha
    have haW : a ∈ interior (NeckFrontierState.region W) :=
      connectedComponentIn_nonempty_iff.mp (closure_nonempty_iff.mp
        ⟨ha.choose, ha.choose_spec.2⟩)
    refine ⟨interior_mono subset_union_left haW, ?_⟩
    obtain ⟨z, hzF, hzC⟩ := ha
    exact ⟨z, hzF,
      closure_mono (connectedComponentIn_mono a (interior_mono subset_union_left)) hzC⟩
  · change remaining ⊂ NeckFrontierState.alive W
    exact Finset.ssubset_iff_subset_ne.mpr
      ⟨hremaining, fun he => hiout (he ▸ hi)⟩


omit [PreconnectedSpace M] in
private theorem spatial_neck_or_cap_frontier_step_of_incident_anchor
    (W : NeckFrontierState g eps ι)
    (heps : eps ≤ Classical.choose (exists_spatial_neck_level_graph_tolerance.{u}))
    (hepsstep : eps ≤ Classical.choose (exists_spatial_neck_finite_frontier_step_tolerance.{u, v}))
    (i : ι) (hi : i ∈ NeckFrontierState.alive W)
    (A : ℝ) (x : M) (hx : metricScalarAt g x ≤ A)
    (hincident : (range (RecordedNeckSphere.map g eps (NeckFrontierState.sphere W i)) ∩
      closure (connectedComponentIn (interior (NeckFrontierState.region W)) x)).Nonempty)
    (halternative :
      Nonempty (SpatialNeck g eps ((RecordedNeckSphere.neck (NeckFrontierState.sphere W i)).map
        ((RecordedNeckSphere.neck (NeckFrontierState.sphere W i)).center,
          RecordedNeckSphere.level (NeckFrontierState.sphere W i)))) ∨
      ∃ U : CompactDomain M, Nonempty (CapCore U.carrier) ∧
        range (RecordedNeckSphere.map g eps (NeckFrontierState.sphere W i)) ⊆ interior U.carrier ∧
        ∀ a : M, metricScalarAt g a ≤ A → a ∉ interior U.carrier) :
    ∃ V : NeckFrontierState g eps ι,
      NeckFrontierState.region W ⊆ NeckFrontierState.region V ∧
      (∀ k a, (range (RecordedNeckSphere.map g eps (NeckFrontierState.sphere W k)) ∩
        closure (connectedComponentIn (interior (NeckFrontierState.region W)) a)).Nonempty →
        a ∈ interior (NeckFrontierState.region V) ∧
          (range (RecordedNeckSphere.map g eps (NeckFrontierState.sphere V k)) ∩
            closure (connectedComponentIn (interior (NeckFrontierState.region V)) a)).Nonempty) ∧
      (OrdinaryNeckMoveAt g eps ι W V i ∨
        (NeckFrontierState.alive V ⊂ NeckFrontierState.alive W ∧
          NeckFrontierState.sphere V = NeckFrontierState.sphere W)) := by
  rcases halternative with hneck | ⟨U, ⟨cap⟩, hinside, hlow⟩
  · obtain ⟨V, hWV, hpreserve, hordinary | hreturn⟩ :=
      NeckFrontierState.exists_step_at_of_neck_preserving_incident_components
        g eps ι W i hi heps hepsstep hneck
    · rcases hordinary with ⟨halive, hi', p, nk, P, hsource, hregion, hP0, hP1, hother,
        hinter, hfill, hcontrolled, hband, hpoint, hcentral⟩
      exact ⟨V, hWV, hpreserve, Or.inl ⟨halive, hi', p, nk, P, hsource, hregion,
        hP0, hP1, hother, hinter, hfill, hcontrolled, hband, hpoint, hcentral⟩⟩
    · exact ⟨V, hWV, hpreserve, Or.inr hreturn⟩
  · obtain ⟨V, hWV, hpreserve, hlt, hsphere, _⟩ :=
      spatial_cap_frontier_step_of_incident_anchor g eps ι W i hi cap hinside x hincident (hlow x hx)
    exact ⟨V, hWV, hpreserve, Or.inr ⟨hlt, hsphere⟩⟩


private theorem spatial_cap_frontier_step
    (W : NeckFrontierState g eps ι)
    (heps : eps ≤ Classical.choose (exists_spatial_neck_level_graph_tolerance.{u}))
    (hepsstep : eps ≤ Classical.choose (exists_spatial_neck_finite_frontier_step_tolerance.{u, v}))
    (i : ι) (hi : i ∈ NeckFrontierState.alive W)
    (A : ℝ)
    (hanchor : ∀ x ∈ interior (NeckFrontierState.region W),
      ∃ a ∈ connectedComponentIn (interior (NeckFrontierState.region W)) x,
        metricScalarAt g a ≤ A)
    (halternative :
      Nonempty (SpatialNeck g eps ((RecordedNeckSphere.neck (NeckFrontierState.sphere W i)).map
        ((RecordedNeckSphere.neck (NeckFrontierState.sphere W i)).center,
          RecordedNeckSphere.level (NeckFrontierState.sphere W i)))) ∨
      ∃ (U : CompactDomain M), Nonempty (CapCore U.carrier) ∧
        range (RecordedNeckSphere.map g eps (NeckFrontierState.sphere W i)) ⊆ interior U.carrier ∧
        ∀ a : M, metricScalarAt g a ≤ A → a ∉ interior U.carrier) :
    ∃ V : NeckFrontierState g eps ι,
      NeckFrontierState.region W ⊆ NeckFrontierState.region V ∧
      (∀ x ∈ interior (NeckFrontierState.region V),
        ∃ a ∈ connectedComponentIn (interior (NeckFrontierState.region V)) x,
          metricScalarAt g a ≤ A) ∧
      (OrdinaryNeckMoveAt g eps ι W V i ∨
        (NeckFrontierState.alive V ⊂ NeckFrontierState.alive W ∧
          NeckFrontierState.sphere V = NeckFrontierState.sphere W)) := by
  classical
  have htransfer {V : NeckFrontierState g eps ι}
      (hWV : NeckFrontierState.region W ⊆ NeckFrontierState.region V)
      (hcomponents : ∀ x ∈ interior (NeckFrontierState.region V),
        (connectedComponentIn (interior (NeckFrontierState.region V)) x ∩
          interior (NeckFrontierState.region W)).Nonempty) :
      ∀ x ∈ interior (NeckFrontierState.region V),
        ∃ a ∈ connectedComponentIn (interior (NeckFrontierState.region V)) x,
          metricScalarAt g a ≤ A := by
    intro x hx
    obtain ⟨z, hzC, hzW⟩ := hcomponents x hx
    obtain ⟨a, haC, haA⟩ := hanchor z hzW
    refine ⟨a, ?_, haA⟩
    rw [connectedComponentIn_eq hzC]
    exact connectedComponentIn_mono z (interior_mono hWV) haC
  rcases halternative with hn | ⟨U, ⟨cap⟩, hinside, hlow⟩
  · obtain ⟨V, hWV, _, _, hcomponents, hm | hr⟩ :=
      NeckFrontierState.exists_step_at_of_neck_central g eps ι W i hi heps hepsstep hn
    · rcases hm with ⟨halive, hia, p, nk, P, hsource, hregion, hP0, hP1, hother,
        hinter, hfill, hcontrolled, hband, hpoint, hcentral⟩
      exact ⟨V, hWV, htransfer hWV hcomponents, Or.inl ⟨halive, hia, p, nk, P, hsource,
        hregion, hP0, hP1, hother, hinter, hfill, hcontrolled, hband, hpoint, hcentral⟩⟩
    · exact ⟨V, hWV, htransfer hWV hcomponents, Or.inr hr⟩
  · have hfront : frontier (NeckFrontierState.region W) = ⋃ j ∈ NeckFrontierState.alive W,
        range (fun z : Sphere 2 => (RecordedNeckSphere.neck (NeckFrontierState.sphere W j)).map
          (z, RecordedNeckSphere.level (NeckFrontierState.sphere W j))) := by
      simpa only [RecordedNeckSphere.range_map] using NeckFrontierState.frontier W
    have hpair : (NeckFrontierState.alive W : Set ι).Pairwise (fun i j =>
        Disjoint (range (fun z : Sphere 2 => (RecordedNeckSphere.neck (NeckFrontierState.sphere W i)).map
          (z, RecordedNeckSphere.level (NeckFrontierState.sphere W i))))
          (range (fun z : Sphere 2 => (RecordedNeckSphere.neck (NeckFrontierState.sphere W j)).map
            (z, RecordedNeckSphere.level (NeckFrontierState.sphere W j))))) := by
      simpa only [RecordedNeckSphere.range_map] using NeckFrontierState.disjoint W
    obtain ⟨K, _, _, _, _, _, hVK, hVR, hVF, _, _, _, hcomponents⟩ :=
      exists_cap_filling_on_finite_spatial_neck_frontier_of_componentwise_avoidance
        (NeckFrontierState.alive W)
        (fun j => RecordedNeckSphere.point (NeckFrontierState.sphere W j))
        (fun j => RecordedNeckSphere.neck (NeckFrontierState.sphere W j))
        (fun j => RecordedNeckSphere.level (NeckFrontierState.sphere W j))
        (fun j _ => RecordedNeckSphere.bound (NeckFrontierState.sphere W j)) hpair i hi cap
        (by simpa only [RecordedNeckSphere.range_map] using hinside)
        (NeckFrontierState.compact W) (NeckFrontierState.regular W) hfront
        (by
          intro x hx
          obtain ⟨a, haC, haA⟩ := hanchor x hx
          exact ⟨a, haC, hlow a haA⟩)
    let V : NeckFrontierState g eps ι :=
      NeckFrontierState.mk (NeckFrontierState.region W ∪ K) hVK
        ((NeckFrontierState.nonempty W).mono subset_union_left) hVR
        ((NeckFrontierState.alive W).erase i) (NeckFrontierState.sphere W)
        (by simpa only [RecordedNeckSphere.range_map] using hVF)
        (fun j hj k hk hjk => (NeckFrontierState.disjoint W)
          (Finset.mem_of_mem_erase hj) (Finset.mem_of_mem_erase hk) hjk)
    exact ⟨V, subset_union_left, htransfer subset_union_left hcomponents,
      Or.inr ⟨Finset.erase_ssubset hi, rfl⟩⟩

private theorem spatial_cap_fair_frontier_process [NoncompactSpace M]
    (W₀ : NeckFrontierState g eps ι)
    (heps : eps ≤ Classical.choose (exists_spatial_neck_level_graph_tolerance.{u}))
    (hepsstep : eps ≤ Classical.choose (exists_spatial_neck_finite_frontier_step_tolerance.{u, v}))
    (A : ℝ)
    (hanchor : ∀ x ∈ interior (NeckFrontierState.region W₀),
      ∃ a ∈ connectedComponentIn (interior (NeckFrontierState.region W₀)) x,
        metricScalarAt g a ≤ A)
    (hmodels : ∀ (p : M) (nk : SpatialNeck g eps p) (level : ℝ), |level| ≤ 4 →
      nk.map (nk.center, level) ∉ interior (NeckFrontierState.region W₀) →
      Nonempty (SpatialNeck g eps (nk.map (nk.center, level))) ∨
      ∃ U : CompactDomain M, Nonempty (CapCore U.carrier) ∧
        range (fun z : Sphere 2 => nk.map (z, level)) ⊆ interior U.carrier ∧
        ∀ a : M, metricScalarAt g a ≤ A → a ∉ interior U.carrier) :
    ∃ (seq : ℕ → NeckFrontierState g eps ι) (selected : ℕ → ι),
      seq 0 = W₀ ∧ Monotone (fun n => NeckFrontierState.region (seq n)) ∧
      Antitone (fun n => NeckFrontierState.alive (seq n)) ∧
      (∀ n, selected n ∈ NeckFrontierState.alive (seq n)) ∧
      (∀ n, OrdinaryNeckMoveAt g eps ι (seq n) (seq (n + 1)) (selected n) ∨
        (NeckFrontierState.alive (seq (n + 1)) ⊂ NeckFrontierState.alive (seq n) ∧
          NeckFrontierState.sphere (seq (n + 1)) = NeckFrontierState.sphere (seq n))) ∧
      ∃ N : ℕ, (NeckFrontierState.alive (seq N)).Nonempty ∧
        (∀ n, N ≤ n → NeckFrontierState.alive (seq n) = NeckFrontierState.alive (seq N)) ∧
        (∀ n, N ≤ n → OrdinaryNeckMoveAt g eps ι (seq n) (seq (n + 1)) (selected n)) ∧
        ∀ i ∈ NeckFrontierState.alive (seq N), {n | selected n = i}.Infinite := by
  classical
  let P (W : NeckFrontierState g eps ι) : Prop :=
    NeckFrontierState.region W₀ ⊆ NeckFrontierState.region W ∧
      ∀ x ∈ interior (NeckFrontierState.region W),
        ∃ a ∈ connectedComponentIn (interior (NeckFrontierState.region W)) x,
          metricScalarAt g a ≤ A
  have hstep : ∀ W, P W → ∀ i ∈ NeckFrontierState.alive W,
      ∃ V : NeckFrontierState g eps ι,
        NeckFrontierState.region W ⊆ NeckFrontierState.region V ∧ P V ∧
        (OrdinaryNeckMoveAt g eps ι W V i ∨
          (NeckFrontierState.alive V ⊂ NeckFrontierState.alive W ∧
            NeckFrontierState.sphere V = NeckFrontierState.sphere W)) := by
    intro W hW i hi
    let f := NeckFrontierState.sphere W i
    have hx : (RecordedNeckSphere.neck f).map
        ((RecordedNeckSphere.neck f).center, RecordedNeckSphere.level f) ∈
        frontier (NeckFrontierState.region W) := by
      rw [NeckFrontierState.frontier W]
      refine mem_iUnion₂.mpr ⟨i, hi, ?_⟩
      rw [RecordedNeckSphere.range_map]
      exact mem_range_self _
    have hlocal := hmodels (RecordedNeckSphere.point f) (RecordedNeckSphere.neck f)
      (RecordedNeckSphere.level f) (RecordedNeckSphere.bound f)
      (fun h => hx.2 (interior_mono hW.1 h))
    have halternative : Nonempty (SpatialNeck g eps
        ((RecordedNeckSphere.neck f).map ((RecordedNeckSphere.neck f).center,
          RecordedNeckSphere.level f))) ∨
        ∃ U : CompactDomain M, Nonempty (CapCore U.carrier) ∧
          range (RecordedNeckSphere.map g eps f) ⊆ interior U.carrier ∧
          ∀ a : M, metricScalarAt g a ≤ A → a ∉ interior U.carrier := by
      simpa only [RecordedNeckSphere.range_map] using hlocal
    obtain ⟨V, hWV, hVA, hmove⟩ :=
      spatial_cap_frontier_step g eps ι W heps hepsstep i hi A hW.2 halternative
    exact ⟨V, hWV, ⟨hW.1.trans hWV, hVA⟩, hmove⟩
  obtain ⟨schedule, _, hfair⟩ :=
    (NeckFrontierState.alive W₀).finite_toSet.countable.exists_sequence_cofinal_fibers
      (NeckFrontierState.alive_nonempty g eps ι W₀)
  obtain ⟨seq, selected, hzero, hmono, hanti, _, hselected, hschedule, hsteps, N, hN⟩ :=
    NeckFrontierState.exists_scheduled_process_of_transition g eps ι W₀ schedule P
      ⟨Subset.rfl, hanchor⟩ hstep
  have hstable (n : ℕ) (hn : N ≤ n) :
      NeckFrontierState.alive (seq n) = NeckFrontierState.alive (seq N) := by
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih => exact (hN n hn).1.trans ih
  refine ⟨seq, selected, hzero, hmono, hanti, hselected, hsteps, N,
    NeckFrontierState.alive_nonempty g eps ι (seq N), hstable, hN, ?_⟩
  intro i hi
  apply Set.infinite_of_forall_exists_gt
  intro a
  have hi0 : i ∈ NeckFrontierState.alive W₀ := by
    simpa only [hzero] using hanti (Nat.zero_le N) hi
  obtain ⟨n, hn, hsi⟩ := hfair i hi0 (max N (a + 1))
  have hNn : N ≤ n := (le_max_left _ _).trans hn
  have hin : i ∈ NeckFrontierState.alive (seq n) := (hstable n hNn).symm ▸ hi
  have hselectedi : selected n = i := (hschedule n (hsi.symm ▸ hin)).trans hsi
  exact ⟨n, hselectedi, lt_of_lt_of_le (Nat.lt_succ_self a) ((le_max_right _ _).trans hn)⟩

section
omit [PreconnectedSpace M]

open scoped Classical in
private def NeckFrontierState.anchoredLabels (S : NeckFrontierState g eps ι) (A : ℝ) : Finset ι :=
  (NeckFrontierState.alive S).filter fun i => ∃ a : M,
    metricScalarAt g a ≤ A ∧
      (range (RecordedNeckSphere.map g eps (NeckFrontierState.sphere S i)) ∩
        closure (connectedComponentIn (interior (NeckFrontierState.region S)) a)).Nonempty

omit [T2Space M] in
private theorem NeckFrontierState.anchoredLabels_nonempty [PreconnectedSpace M] [NoncompactSpace M]
    (S : NeckFrontierState g eps ι) (A : ℝ)
    (ha : ∃ a ∈ interior (NeckFrontierState.region S), metricScalarAt g a ≤ A) :
    (S.anchoredLabels g eps ι A).Nonempty := by
  classical
  obtain ⟨a, ha, haA⟩ := ha
  let _ : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace ThreeSpace M
  have hproper : NeckFrontierState.region S ≠ univ := by
    intro h
    exact noncompact_univ (X := M) (h ▸ NeckFrontierState.compact S)
  obtain ⟨x, hxF, hxC⟩ :=
    DifferentialGeometry.Topology.frontier_inter_closure_interior_component_nonempty hproper ha
  rw [NeckFrontierState.frontier S] at hxF
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hxF
  exact ⟨i, Finset.mem_filter.mpr ⟨hi, a, haA, x, hxi, hxC⟩⟩

private theorem spatial_cap_fair_anchored_frontier_process [PreconnectedSpace M] [NoncompactSpace M]
    (W₀ : NeckFrontierState g eps ι)
    (heps : eps ≤ Classical.choose (exists_spatial_neck_level_graph_tolerance.{u}))
    (hepsstep : eps ≤ Classical.choose (exists_spatial_neck_finite_frontier_step_tolerance.{u, v}))
    (A : ℝ)
    (hanchor : ∃ a ∈ interior (NeckFrontierState.region W₀), metricScalarAt g a ≤ A)
    (hmodels : ∀ (p : M) (nk : SpatialNeck g eps p) (level : ℝ), |level| ≤ 4 →
      nk.map (nk.center, level) ∉ interior (NeckFrontierState.region W₀) →
      Nonempty (SpatialNeck g eps (nk.map (nk.center, level))) ∨
      ∃ U : CompactDomain M, Nonempty (CapCore U.carrier) ∧
        range (fun z : Sphere 2 => nk.map (z, level)) ⊆ interior U.carrier ∧
        ∀ a : M, metricScalarAt g a ≤ A → a ∉ interior U.carrier) :
    ∃ (seq : ℕ → NeckFrontierState g eps ι) (selected : ℕ → ι),
      seq 0 = W₀ ∧ Monotone (fun n => NeckFrontierState.region (seq n)) ∧
      Antitone (fun n => NeckFrontierState.alive (seq n)) ∧
      (∀ n, selected n ∈ (seq n).anchoredLabels g eps ι A) ∧
      (∀ n, OrdinaryNeckMoveAt g eps ι (seq n) (seq (n + 1)) (selected n) ∨
        (NeckFrontierState.alive (seq (n + 1)) ⊂ NeckFrontierState.alive (seq n) ∧
          NeckFrontierState.sphere (seq (n + 1)) = NeckFrontierState.sphere (seq n))) ∧
      (∀ n j, j ∈ (seq n).anchoredLabels g eps ι A →
        j ∈ NeckFrontierState.alive (seq (n + 1)) →
        j ∈ (seq (n + 1)).anchoredLabels g eps ι A) ∧
      (∀ n j, selected n ≠ j →
        NeckFrontierState.sphere (seq (n + 1)) j = NeckFrontierState.sphere (seq n) j) ∧
      (∀ n, NeckFrontierState.alive (seq n) ⊆ NeckFrontierState.alive W₀) ∧
      (∀ n j, (∀ k, k < n → selected k ≠ j) →
        NeckFrontierState.sphere (seq n) j = NeckFrontierState.sphere W₀ j) ∧
      ∃ N : ℕ, ((seq N).anchoredLabels g eps ι A).Nonempty ∧
        (∀ n, N ≤ n → NeckFrontierState.alive (seq n) = NeckFrontierState.alive (seq N)) ∧
        (∀ n, N ≤ n → (seq n).anchoredLabels g eps ι A = (seq N).anchoredLabels g eps ι A) ∧
        (∀ n, N ≤ n → OrdinaryNeckMoveAt g eps ι (seq n) (seq (n + 1)) (selected n)) ∧
        ∀ i ∈ (seq N).anchoredLabels g eps ι A, {n | selected n = i}.Infinite := by
  classical
  let State := {W : NeckFrontierState g eps ι //
    NeckFrontierState.region W₀ ⊆ NeckFrontierState.region W}
  have hanchorW (W : State) :
      ∃ a ∈ interior (NeckFrontierState.region W.val), metricScalarAt g a ≤ A := by
    obtain ⟨a, ha, haA⟩ := hanchor
    exact ⟨a, interior_mono W.property ha, haA⟩
  have hne (W : State) : (W.val.anchoredLabels g eps ι A).Nonempty :=
    NeckFrontierState.anchoredLabels_nonempty g eps ι W.val A (hanchorW W)
  have hne₀ : (NeckFrontierState.alive W₀).Nonempty :=
    (NeckFrontierState.anchoredLabels_nonempty g eps ι W₀ A hanchor).mono
      (Finset.filter_subset _ _)
  obtain ⟨schedule, _, hfair⟩ :=
    (NeckFrontierState.alive W₀).finite_toSet.countable.exists_sequence_cofinal_fibers hne₀
  let pick (n : ℕ) (W : State) : ι :=
    if schedule n ∈ W.val.anchoredLabels g eps ι A then schedule n else (hne W).choose
  have hpick (n : ℕ) (W : State) : pick n W ∈ W.val.anchoredLabels g eps ι A := by
    dsimp only [pick]
    split
    · assumption
    · exact (hne W).choose_spec
  have hnext (n : ℕ) (W : State) : ∃ V : State,
      NeckFrontierState.region W.val ⊆ NeckFrontierState.region V.val ∧
      (∀ j, j ∈ W.val.anchoredLabels g eps ι A → j ∈ NeckFrontierState.alive V.val →
        j ∈ V.val.anchoredLabels g eps ι A) ∧
      (OrdinaryNeckMoveAt g eps ι W.val V.val (pick n W) ∨
        (NeckFrontierState.alive V.val ⊂ NeckFrontierState.alive W.val ∧
          NeckFrontierState.sphere V.val = NeckFrontierState.sphere W.val)) := by
    obtain ⟨hi, a, haA, hincident⟩ := Finset.mem_filter.mp (hpick n W)
    let f := NeckFrontierState.sphere W.val (pick n W)
    have hxfront : (RecordedNeckSphere.neck f).map
        ((RecordedNeckSphere.neck f).center, RecordedNeckSphere.level f) ∈
        frontier (NeckFrontierState.region W.val) := by
      rw [NeckFrontierState.frontier W.val]
      refine mem_iUnion₂.mpr ⟨pick n W, hi, ?_⟩
      rw [RecordedNeckSphere.range_map]
      exact mem_range_self _
    have halt := hmodels (RecordedNeckSphere.point f) (RecordedNeckSphere.neck f)
      (RecordedNeckSphere.level f) (RecordedNeckSphere.bound f)
      (fun h => hxfront.2 (interior_mono W.property h))
    have halt' : Nonempty (SpatialNeck g eps ((RecordedNeckSphere.neck f).map
        ((RecordedNeckSphere.neck f).center, RecordedNeckSphere.level f))) ∨
        ∃ U : CompactDomain M, Nonempty (CapCore U.carrier) ∧
          range (RecordedNeckSphere.map g eps f) ⊆ interior U.carrier ∧
          ∀ a : M, metricScalarAt g a ≤ A → a ∉ interior U.carrier := by
      simpa only [RecordedNeckSphere.range_map] using halt
    obtain ⟨V, hWV, hpreserve, hmove⟩ :=
      spatial_neck_or_cap_frontier_step_of_incident_anchor g eps ι W.val heps hepsstep
        (pick n W) hi A a haA hincident halt'
    refine ⟨⟨V, W.property.trans hWV⟩, hWV, ?_, hmove⟩
    intro j hj hjV
    obtain ⟨_, b, hbA, hb⟩ := Finset.mem_filter.mp hj
    exact Finset.mem_filter.mpr ⟨hjV, b, hbA, (hpreserve j b hb).2⟩
  choose next hnext using hnext
  let states : ℕ → State := Nat.rec ⟨W₀, Subset.rfl⟩ (fun n W => next n W)
  let seq (n) := (states n).val
  let selected (n) := pick n (states n)
  have hmono : Monotone (fun n => NeckFrontierState.region (seq n)) :=
    monotone_nat_of_le_succ (fun n => (hnext n (states n)).1)
  have hsteps (n) : OrdinaryNeckMoveAt g eps ι (seq n) (seq (n + 1)) (selected n) ∨
      (NeckFrontierState.alive (seq (n + 1)) ⊂ NeckFrontierState.alive (seq n) ∧
        NeckFrontierState.sphere (seq (n + 1)) = NeckFrontierState.sphere (seq n)) :=
    (hnext n (states n)).2.2
  have hanti : Antitone (fun n => NeckFrontierState.alive (seq n)) := by
    apply antitone_nat_of_succ_le
    intro n
    rcases hsteps n with hn | hd
    · exact hn.1.le
    · exact hd.1.le
  have hsurvive (n j) (hj : j ∈ (seq n).anchoredLabels g eps ι A)
      (halive : j ∈ NeckFrontierState.alive (seq (n + 1))) :
      j ∈ (seq (n + 1)).anchoredLabels g eps ι A :=
    (hnext n (states n)).2.1 j hj halive
  obtain ⟨N, hN⟩ := DifferentialGeometry.Topology.exists_eventually_eq_of_antitone_surviving
    (alive := fun n => (NeckFrontierState.alive (seq n) : Set ι))
    (active := fun n => ((seq n).anchoredLabels g eps ι A : Set ι))
    (NeckFrontierState.alive W₀).finite_toSet hanti
    (fun _ => Finset.filter_subset _ _) (fun n j hj => hsurvive n j hj.1 hj.2)
  have hstable (n) (hn : N ≤ n) :
      NeckFrontierState.alive (seq n) = NeckFrontierState.alive (seq N) :=
    Finset.coe_injective (hN n hn).1
  have hactive (n) (hn : N ≤ n) :
      (seq n).anchoredLabels g eps ι A = (seq N).anchoredLabels g eps ι A :=
    Finset.coe_injective (hN n hn).2
  have hordinary (n) (hn : N ≤ n) :
      OrdinaryNeckMoveAt g eps ι (seq n) (seq (n + 1)) (selected n) := by
    rcases hsteps n with ho | hd
    · exact ho
    · have heq : NeckFrontierState.alive (seq (n + 1)) = NeckFrontierState.alive (seq n) :=
        (hstable (n + 1) (hn.trans (Nat.le_succ n))).trans (hstable n hn).symm
      exact ((heq ▸ hd.1).ne rfl).elim
  have hunchanged (n j) (hne : selected n ≠ j) :
      NeckFrontierState.sphere (seq (n + 1)) j = NeckFrontierState.sphere (seq n) j := by
    rcases hsteps n with ho | hd
    · obtain ⟨_, _, _, _, _, _, _, _, _, hother, _⟩ := ho
      exact hother j (Ne.symm hne)
    · exact congrFun hd.2 j
  have hinitial (n j) (hnot : ∀ k, k < n → selected k ≠ j) :
      NeckFrontierState.sphere (seq n) j = NeckFrontierState.sphere W₀ j := by
    induction n with
    | zero => rfl
    | succ n ih =>
      exact (hunchanged n j (hnot n (Nat.lt_succ_self n))).trans
        (ih (fun k hk => hnot k (hk.trans (Nat.lt_succ_self n))))
  refine ⟨seq, selected, rfl, hmono, hanti, fun n => hpick n (states n),
    hsteps, hsurvive, hunchanged, fun n => hanti (Nat.zero_le n), hinitial,
    N, hne (states N), hstable, hactive, hordinary, ?_⟩
  intro i hi
  apply Set.infinite_of_forall_exists_gt
  intro k
  have hiN : i ∈ NeckFrontierState.alive (seq N) := (Finset.mem_filter.mp hi).1
  have hi₀ : i ∈ NeckFrontierState.alive W₀ := hanti (Nat.zero_le N) hiN
  obtain ⟨n, hn, hsi⟩ := hfair i hi₀ (max N (k + 1))
  have hNn : N ≤ n := (le_max_left _ _).trans hn
  have hin : i ∈ (seq n).anchoredLabels g eps ι A := (hactive n hNn).symm ▸ hi
  have hselect : selected n = i := (if_pos (hsi.symm ▸ hin)).trans hsi
  exact ⟨n, hselect, lt_of_lt_of_le (Nat.lt_succ_self k) ((le_max_right _ _).trans hn)⟩



private theorem NeckFrontierState.exists_boundaryAtlas (S : NeckFrontierState g eps ι) :
    Nonempty (DifferentialGeometry.Topology.SmoothBoundaryAtlas I3 3 (NeckFrontierState.region S)) := by
  let J := {i // i ∈ (NeckFrontierState.alive S)}
  let _ : Finite J := (NeckFrontierState.alive S).finite_toSet.to_subtype
  have hlevel (i : J) : |(RecordedNeckSphere.level (NeckFrontierState.sphere S i.val))| < eps⁻¹ := by
    have hlen : (4 : ℝ) < eps⁻¹ :=
      (lt_inv_comm₀ (by norm_num) (RecordedNeckSphere.neck (NeckFrontierState.sphere S i.val)).eps_pos).mpr
        (by linarith [(RecordedNeckSphere.neck (NeckFrontierState.sphere S i.val)).eps_small])
    exact (RecordedNeckSphere.bound (NeckFrontierState.sphere S i.val)).trans_lt hlen
  obtain ⟨C, _⟩ := exists_smoothBoundaryAtlas_of_finite_spatial_neck_levels g
    (fun i : J => (RecordedNeckSphere.point (NeckFrontierState.sphere S i.val))) (fun i => (RecordedNeckSphere.neck (NeckFrontierState.sphere S i.val)))
    (fun i => (RecordedNeckSphere.level (NeckFrontierState.sphere S i.val))) hlevel (fun i => (RecordedNeckSphere.param (NeckFrontierState.sphere S i.val)))
    (fun i j hij => (NeckFrontierState.disjoint S) i.property j.property (fun h => hij (Subtype.ext h)))
    (NeckFrontierState.regular S) (by
      intro x hx
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp ((NeckFrontierState.frontier S) ▸ hx)
      exact mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩)
  exact ⟨C⟩

private theorem NeckFrontierState.locallyConnectedSpace (S : NeckFrontierState g eps ι) :
    LocallyConnectedSpace (NeckFrontierState.region S) := by
  obtain ⟨C⟩ := NeckFrontierState.exists_boundaryAtlas g eps ι S
  let _ := C.toChartedSpace
  let _ := C.isManifold
  exact ChartedSpace.locallyConnectedSpace (EuclideanHalfSpace 3) (NeckFrontierState.region S)

private theorem NeckFrontierState.discrete_connectedComponents (S : NeckFrontierState g eps ι) :
    DiscreteTopology (ConnectedComponents (NeckFrontierState.region S)) := by
  let _ := NeckFrontierState.locallyConnectedSpace g eps ι S
  infer_instance

private theorem NeckFrontierState.closure_component_interior
    (S : NeckFrontierState g eps ι) {a : M} (ha : a ∈ interior (NeckFrontierState.region S)) :
    closure (connectedComponentIn (interior (NeckFrontierState.region S)) a) = connectedComponentIn (NeckFrontierState.region S) a := by
  obtain ⟨C⟩ := NeckFrontierState.exists_boundaryAtlas g eps ι S
  let _ := NeckFrontierState.locallyConnectedSpace g eps ι S
  rw [C.connectedComponentIn_interior_eq_interior_connectedComponentIn ha]
  exact DifferentialGeometry.Topology.closure_interior_connectedComponentIn (NeckFrontierState.regular S) a

private theorem NeckFrontierState.mem_anchoredLabels_iff
    (S : NeckFrontierState g eps ι) (A : ℝ)
    (hlow : {a | metricScalarAt g a ≤ A} ⊆ interior (NeckFrontierState.region S)) (i : ι) :
    i ∈ NeckFrontierState.anchoredLabels g eps ι S A ↔ i ∈ (NeckFrontierState.alive S) ∧
      (range (RecordedNeckSphere.map g eps (NeckFrontierState.sphere S i)) ∩
        ⋃ a ∈ {a | metricScalarAt g a ≤ A}, connectedComponentIn (NeckFrontierState.region S) a).Nonempty := by
  classical
  simp only [NeckFrontierState.anchoredLabels, Finset.mem_filter]
  constructor
  · rintro ⟨hi, a, ha, x, hxF, hxC⟩
    rw [NeckFrontierState.closure_component_interior g eps ι S (hlow ha)] at hxC
    exact ⟨hi, x, hxF, mem_iUnion₂.mpr ⟨a, ha, hxC⟩⟩
  · rintro ⟨hi, x, hxF, hxR⟩
    obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.mp hxR
    refine ⟨hi, a, ha, x, hxF, ?_⟩
    rw [NeckFrontierState.closure_component_interior g eps ι S (hlow ha)]
    exact hxa

private theorem NeckFrontierState.anchored_sphere_subset
    (S : NeckFrontierState g eps ι) (A : ℝ) {i : ι}
    (hi : i ∈ NeckFrontierState.anchoredLabels g eps ι S A) :
    range (RecordedNeckSphere.map g eps (NeckFrontierState.sphere S i)) ⊆
      ⋃ a ∈ {a | metricScalarAt g a ≤ A}, connectedComponentIn (NeckFrontierState.region S) a := by
  classical
  obtain ⟨hi, a, ha, x, hxF, hxC⟩ := Finset.mem_filter.mp hi
  have hxCa : x ∈ connectedComponentIn (NeckFrontierState.region S) a :=
    closure_connectedComponentIn_subset (NeckFrontierState.compact S).isClosed
      interior_subset a hxC
  have hFW : range (RecordedNeckSphere.map g eps (NeckFrontierState.sphere S i)) ⊆ (NeckFrontierState.region S) := by
    intro y hy
    exact (NeckFrontierState.compact S).isClosed.frontier_subset
      ((NeckFrontierState.frontier S).symm ▸ mem_iUnion₂.mpr ⟨i, hi, hy⟩)
  have hFC : range (RecordedNeckSphere.map g eps (NeckFrontierState.sphere S i)) ⊆ connectedComponentIn (NeckFrontierState.region S) a := by
    rw [connectedComponentIn_eq hxCa]
    exact (RecordedNeckSphere.isPreconnected_range g eps (NeckFrontierState.sphere S i)).subset_connectedComponentIn hxF hFW
  exact hFC.trans (subset_iUnion₂_of_subset a ha subset_rfl)

private theorem NeckFrontierState.component_union_inter_interior_subset
    (S : NeckFrontierState g eps ι) (L : Set M) :
    (⋃ a ∈ L, connectedComponentIn (NeckFrontierState.region S) a) ∩ interior (NeckFrontierState.region S) ⊆
      interior (⋃ a ∈ L, connectedComponentIn (NeckFrontierState.region S) a) := by
  let _ := NeckFrontierState.discrete_connectedComponents g eps ι S
  rintro x ⟨hxR, hxint⟩
  obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.mp hxR
  have hx : x ∈ interior (connectedComponentIn (NeckFrontierState.region S) a) := by
    rw [DifferentialGeometry.Topology.interior_connectedComponentIn_eq_inter]
    exact ⟨hxint, hxa⟩
  exact interior_mono (subset_iUnion₂_of_subset a ha subset_rfl) hx


private theorem NeckFrontierState.exists_proper_attachment_ends
    (seq : ℕ → NeckFrontierState g eps ι) (label : ℕ → ι)
    (heps : eps ≤ 1 / 156000)
    (hcompact : ∀ B : ℝ, IsCompact {x : M | metricScalarAt g x ≤ B})
    (hmove : ∀ n, OrdinaryNeckMoveAt g eps ι (seq n) (seq (n + 1)) (label n))
    (J : Finset ι) (hfair : ∀ i ∈ J, {n | label n = i}.Infinite) :
    ∃ B : ℕ → Set M,
      (∀ n, IsClosed (B n)) ∧ (∀ n, IsPreconnected (B n)) ∧
      (∀ n, NeckFrontierState.region (seq (n + 1)) = NeckFrontierState.region (seq n) ∪ B n) ∧
      (∀ n, B n ∩ NeckFrontierState.region (seq n) =
        range (RecordedNeckSphere.map g eps (NeckFrontierState.sphere (seq n) (label n)))) ∧
      (∀ n, range (RecordedNeckSphere.map g eps (NeckFrontierState.sphere (seq n) (label n))) ⊆
        interior (NeckFrontierState.region (seq (n + 1)))) ∧
      ∃ ends : {i // i ∈ J} → Sphere 2 × ℝ≥0 → M,
        (∀ i, IsProperMap (ends i)) ∧
        ∀ i, range (ends i) = ⋃ n, ⋃ (_ : label n = i.val), B n := by
  classical
  have hchoice (n) := (hmove n).2.2
  choose point neck P hsource hregion hlower hupper hother hinter hfilled hcontrolled
    hband hpoint using hchoice
  let B (n) := P n '' (univ ×ˢ Icc (0 : ℝ) 1)
  let sphere (n i) := RecordedNeckSphere.map g eps (NeckFrontierState.sphere (seq n) i)
  have hmono : Monotone (fun n => NeckFrontierState.region (seq n)) := by
    apply monotone_nat_of_le_succ
    intro n
    rw [hregion n]
    exact subset_union_left
  have hcontained (n) : B n ⊆ NeckFrontierState.region (seq (n + 1)) := by
    rw [hregion n]
    exact subset_union_right
  have hsphere (n) : range (sphere n (label n)) ⊆ frontier (NeckFrontierState.region (seq n)) := by
    intro x hx
    rw [NeckFrontierState.frontier (seq n)]
    exact mem_iUnion₂.mpr ⟨label n, (hmove n).2.1, hx⟩
  have hend (i : {i // i ∈ J}) := exists_proper_neck_end_of_infinite_updates
    g heps hcompact label i.val (hfair i.val i.property) sphere
    (fun n hn => congrArg (RecordedNeckSphere.map g eps) (hother n i.val (Ne.symm hn)))
    P hsource (fun _ => Diffeomorph.refl I2 (Sphere 2) ∞) hlower hupper
    (fun n => NeckFrontierState.region (seq n)) hmono hcontained hinter hsphere hfilled
    point neck hcontrolled hband
  choose select hselect hlabel hcover Θ hsm hinj hproper hembed hwhole hinitial hfirst hbase hscalar
    using hend
  refine ⟨B, ?_, ?_, hregion, hinter, hfilled,
    (fun i z => Θ i (z.1, z.2.val)), hproper, ?_⟩
  · intro n
    exact ((isCompact_univ.prod isCompact_Icc).image_of_continuousOn
      ((P n).contMDiffOn_toFun.continuousOn.mono (hsource n))).isClosed
  · intro n
    let _ : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
      (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
        (0 : ThreeSpace) zero_le_one)
    exact (isPreconnected_univ.prod isPreconnected_Icc).image (P n)
      ((P n).contMDiffOn_toFun.continuousOn.mono (hsource n))
  · intro i
    have hrange : range (fun z : Sphere 2 × ℝ≥0 => Θ i (z.1, z.2.val)) =
        Θ i '' (univ ×ˢ Ici (0 : ℝ)) := by
      ext x
      constructor
      · rintro ⟨⟨z, t⟩, hx⟩
        exact ⟨(z, t.val), ⟨mem_univ _, t.property⟩, hx⟩
      · rintro ⟨⟨z, t⟩, ⟨_, ht⟩, hx⟩
        exact ⟨(z, ⟨t, ht⟩), hx⟩
    rw [hrange, hwhole i]
    apply subset_antisymm
    · intro x hx
      obtain ⟨n, hxn⟩ := mem_iUnion.mp hx
      exact mem_iUnion₂.mpr ⟨select i n, hlabel i n, hxn⟩
    · intro x hx
      obtain ⟨n, hn, hxn⟩ := mem_iUnion₂.mp hx
      obtain ⟨k, hk⟩ := (hcover i n).mp hn
      exact mem_iUnion.mpr ⟨k, hk.symm ▸ hxn⟩


private theorem NeckFrontierState.alive_eq_anchored_of_recurrent_ordinary_moves
    [PreconnectedSpace M]
    (seq : ℕ → NeckFrontierState g eps ι) (label : ℕ → ι)
    (heps : eps ≤ 1 / 156000)
    (hcompact : ∀ B : ℝ, IsCompact {x : M | metricScalarAt g x ≤ B})
    (hmove : ∀ n, OrdinaryNeckMoveAt g eps ι (seq n) (seq (n + 1)) (label n))
    (A : ℝ)
    (hlow : ∀ n, {a | metricScalarAt g a ≤ A} ⊆ interior (NeckFrontierState.region (seq n)))
    (hselected : ∀ n, label n ∈ (NeckFrontierState.anchoredLabels g eps ι (seq n) A))
    (hactive : ∀ n, (NeckFrontierState.anchoredLabels g eps ι (seq n) A) = (NeckFrontierState.anchoredLabels g eps ι (seq 0) A))
    (hfair : ∀ i ∈ (NeckFrontierState.anchoredLabels g eps ι (seq 0) A), {n | label n = i}.Infinite) :
    ∀ n, NeckFrontierState.alive (seq n) = (NeckFrontierState.anchoredLabels g eps ι (seq n) A) := by
  classical
  obtain ⟨B, hBclosed, hBconnected, hstep, hinter, hfilled, ends, hproper, hrange⟩ :=
    NeckFrontierState.exists_proper_attachment_ends g eps ι seq label heps hcompact hmove
      ((NeckFrontierState.anchoredLabels g eps ι (seq 0) A)) hfair
  let L := {a | metricScalarAt g a ≤ A}
  let W (n) := NeckFrontierState.region (seq n)
  let R (n) := ⋃ a ∈ L, connectedComponentIn (W n) a
  let Ind := {i // i ∈ (NeckFrontierState.anchoredLabels g eps ι (seq 0) A)}
  let _ : Finite Ind := ((NeckFrontierState.anchoredLabels g eps ι (seq 0) A)).finite_toSet.to_subtype
  let _ (n) : DiscreteTopology (ConnectedComponents (W n)) :=
    NeckFrontierState.discrete_connectedComponents g eps ι (seq n)
  let face (n) (i : Ind) :=
    range (RecordedNeckSphere.map g eps (NeckFrontierState.sphere (seq n) i.val))
  let selected (n) : Ind := ⟨label n, hactive n ▸ hselected n⟩
  have hcontact (n) : B n ∩ W n ⊆ R n := by
    rw [hinter n]
    exact NeckFrontierState.anchored_sphere_subset g eps ι (seq n) A (hselected n)
  have hmeet (n) : (B n ∩ R n).Nonempty := by
    let q := (RecordedNeckSphere.neck (NeckFrontierState.sphere (seq n) (label n))).center
    let x := RecordedNeckSphere.map g eps (NeckFrontierState.sphere (seq n) (label n)) q
    have hx : x ∈ B n ∩ W n := (hinter n).symm ▸ mem_range_self q
    exact ⟨x, hx.1, hcontact n hx⟩
  have hfrontier (n) : frontier (R n) ⊆ ⋃ i, face n i := by
    let J := {i // i ∈ NeckFrontierState.alive (seq n)}
    let F (i : J) := range (RecordedNeckSphere.map g eps
      (NeckFrontierState.sphere (seq n) i.val))
    have hF (i : J) : IsPreconnected (F i) :=
      RecordedNeckSphere.isPreconnected_range g eps (NeckFrontierState.sphere (seq n) i.val)
    have hFW : frontier (W n) = ⋃ i : J, F i := by
      rw [NeckFrontierState.frontier (seq n)]
      ext x
      exact ⟨fun hx => by
        obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
        exact mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩,
        fun hx => by
          obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
          exact mem_iUnion₂.mpr ⟨i.val, i.property, hxi⟩⟩
    have hRF := DifferentialGeometry.Topology.frontier_component_union_meeting_eq_iUnion
      (L := L) (NeckFrontierState.compact (seq n)).isClosed F hF hFW
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hRF ▸ hx)
    have hiA : i.val ∈ (NeckFrontierState.anchoredLabels g eps ι (seq n) A) :=
      (NeckFrontierState.mem_anchoredLabels_iff g eps ι (seq n) A (hlow n) i.val).mpr
        ⟨i.property, hi⟩
    exact mem_iUnion.mpr ⟨⟨i.val, hactive n ▸ hiA⟩, hxi⟩
  have hunchanged (n) (i : Ind) (hne : selected n ≠ i) : face (n + 1) i = face n i := by
    rcases hmove n with ⟨_, _, p, nk, P, _, _, _, _, hother, _⟩
    exact congrArg (fun s => range (RecordedNeckSphere.map g eps s))
      (hother i.val (fun h => hne (Subtype.ext h.symm)))
  have hfillR (n) : face n (selected n) ⊆ interior (R (n + 1)) := by
    intro x hx
    apply NeckFrontierState.component_union_inter_interior_subset g eps ι (seq (n + 1)) L
    refine ⟨?_, hfilled n hx⟩
    have hxR := NeckFrontierState.anchored_sphere_subset g eps ι (seq n) A (hselected n) hx
    obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.mp hxR
    exact mem_iUnion₂.mpr ⟨a, ha, connectedComponentIn_mono a
      (by rw [hstep n]; exact subset_union_left) hxa⟩
  have hrecurrent (i : Ind) (k : ℕ) : ∃ n, k ≤ n ∧ selected n = i := by
    obtain ⟨n, hn, hkn⟩ := (hfair i.val i.property).exists_gt k
    exact ⟨n, hkn.le, Subtype.ext hn⟩
  have hranges (i : Ind) : range (ends i) = ⋃ n, ⋃ (_ : selected n = i), B n := by
    rw [hrange i]
    ext x
    simp only [mem_iUnion]
    exact ⟨fun ⟨n, hn, hx⟩ => ⟨n, Subtype.ext hn, hx⟩,
      fun ⟨n, hn, hx⟩ => ⟨n, congrArg Subtype.val hn, hx⟩⟩
  obtain ⟨_, _, hWR⟩ := DifferentialGeometry.Topology.component_union_exhaustion_of_recurrent_attachments
    W B L (fun n => (NeckFrontierState.compact (seq n)).isClosed) hBclosed hBconnected
    hstep hcontact hmeet face selected hfrontier hunchanged hfillR hrecurrent ends hproper hranges
  intro n
  apply Finset.Subset.antisymm
  · intro i hi
    apply (NeckFrontierState.mem_anchoredLabels_iff g eps ι (seq n) A (hlow n) i).mpr
    refine ⟨hi, ?_⟩
    let q := (RecordedNeckSphere.neck (NeckFrontierState.sphere (seq n) i)).center
    refine ⟨RecordedNeckSphere.map g eps (NeckFrontierState.sphere (seq n) i) q, mem_range_self q, ?_⟩
    change RecordedNeckSphere.map g eps (NeckFrontierState.sphere (seq n) i) q ∈ R n
    change ∀ n, W n = R n at hWR
    rw [← hWR n]
    apply (NeckFrontierState.compact (seq n)).isClosed.frontier_subset
    rw [NeckFrontierState.frontier (seq n)]
    exact mem_iUnion₂.mpr ⟨i, hi, mem_range_self q⟩
  · exact Finset.filter_subset _ _


private theorem NeckFrontierState.fair_of_eventually_constant_anchored_process
    [PreconnectedSpace M]
    (process : ℕ → NeckFrontierState g eps ι) (selected : ℕ → ι)
    (heps : eps ≤ 1 / 156000)
    (hcompact : ∀ B : ℝ, IsCompact {x : M | metricScalarAt g x ≤ B})
    (hmono : Monotone (fun n => NeckFrontierState.region (process n)))
    (A : ℝ)
    (hlow : {a | metricScalarAt g a ≤ A} ⊆ interior (NeckFrontierState.region (process 0)))
    (hselected : ∀ n, selected n ∈ (NeckFrontierState.anchoredLabels g eps ι (process n) A))
    (N : ℕ)
    (hactive : ∀ n, N ≤ n →
      (NeckFrontierState.anchoredLabels g eps ι (process n) A) = (NeckFrontierState.anchoredLabels g eps ι (process N) A))
    (hmove : ∀ n, N ≤ n →
      OrdinaryNeckMoveAt g eps ι (process n) (process (n + 1)) (selected n))
    (hfair : ∀ i ∈ (NeckFrontierState.anchoredLabels g eps ι (process N) A), {n | selected n = i}.Infinite) :
    (∀ n, N ≤ n → NeckFrontierState.alive (process n) = (NeckFrontierState.anchoredLabels g eps ι (process n) A)) ∧
      ∀ i ∈ NeckFrontierState.alive (process N), {n | selected n = i}.Infinite := by
  have htailfair (i : ι) (hi : i ∈ (NeckFrontierState.anchoredLabels g eps ι (process (N + 0)) A)) :
      {n | selected (N + n) = i}.Infinite := by
    apply Set.infinite_of_forall_exists_gt
    intro k
    obtain ⟨n, hn, hkn⟩ := (hfair i hi).exists_gt (N + k)
    refine ⟨n - N, ?_, by omega⟩
    change selected (N + (n - N)) = i
    rwa [Nat.add_sub_of_le (by omega)]
  have hall := NeckFrontierState.alive_eq_anchored_of_recurrent_ordinary_moves g eps ι
    (fun n => process (N + n)) (fun n => selected (N + n)) heps hcompact
    (fun n => by simpa only [Nat.add_assoc] using hmove (N + n) (Nat.le_add_right N n))
    A (fun n => hlow.trans (interior_mono (hmono (Nat.zero_le _))))
    (fun n => hselected (N + n)) (fun n => hactive (N + n) (Nat.le_add_right N n)) htailfair
  have hall' (n : ℕ) (hn : N ≤ n) :
      NeckFrontierState.alive (process n) = (NeckFrontierState.anchoredLabels g eps ι (process n) A) := by
    simpa only [Nat.add_sub_of_le hn] using hall (n - N)
  exact ⟨hall', fun i hi => hfair i (hall' N le_rfl ▸ hi)⟩


private theorem spatial_cap_fair_frontier_process_of_low_sublevel
    [PreconnectedSpace M] [NoncompactSpace M]
    (W₀ : NeckFrontierState g eps ι)
    (heps : eps ≤ Classical.choose (exists_spatial_neck_level_graph_tolerance.{u}))
    (hepsstep : eps ≤ Classical.choose (exists_spatial_neck_finite_frontier_step_tolerance.{u, v}))
    (hepsrec : eps ≤ 1 / 156000)
    (hcompact : ∀ B : ℝ, IsCompact {x : M | metricScalarAt g x ≤ B})
    (A : ℝ)
    (hlow : {a | metricScalarAt g a ≤ A} ⊆ interior (NeckFrontierState.region W₀))
    (hne : {a | metricScalarAt g a ≤ A}.Nonempty)
    (hmodels : ∀ (p : M) (nk : SpatialNeck g eps p) (level : ℝ), |level| ≤ 4 →
      nk.map (nk.center, level) ∉ interior (NeckFrontierState.region W₀) →
      Nonempty (SpatialNeck g eps (nk.map (nk.center, level))) ∨
      ∃ U : CompactDomain M, Nonempty (CapCore U.carrier) ∧
        range (fun z : Sphere 2 => nk.map (z, level)) ⊆ interior U.carrier ∧
        ∀ a : M, metricScalarAt g a ≤ A → a ∉ interior U.carrier) :
    ∃ (seq : ℕ → NeckFrontierState g eps ι) (selected : ℕ → ι),
      seq 0 = W₀ ∧ Monotone (fun n => NeckFrontierState.region (seq n)) ∧
      Antitone (fun n => NeckFrontierState.alive (seq n)) ∧
      (∀ n, selected n ∈ NeckFrontierState.alive (seq n)) ∧
      (∀ n, OrdinaryNeckMoveAt g eps ι (seq n) (seq (n + 1)) (selected n) ∨
        (NeckFrontierState.alive (seq (n + 1)) ⊂ NeckFrontierState.alive (seq n) ∧
          NeckFrontierState.sphere (seq (n + 1)) = NeckFrontierState.sphere (seq n))) ∧
      ∃ N : ℕ, (NeckFrontierState.alive (seq N)).Nonempty ∧
        (∀ n, N ≤ n → NeckFrontierState.alive (seq n) = NeckFrontierState.alive (seq N)) ∧
        (∀ n, N ≤ n → OrdinaryNeckMoveAt g eps ι (seq n) (seq (n + 1)) (selected n)) ∧
        ∀ i ∈ NeckFrontierState.alive (seq N), {n | selected n = i}.Infinite := by
  classical
  have hanchor : ∃ a ∈ interior (NeckFrontierState.region W₀), metricScalarAt g a ≤ A :=
    ⟨hne.choose, hlow hne.choose_spec, hne.choose_spec⟩
  obtain ⟨seq, selected, hzero, hmono, hanti, hselected, hsteps, _, _, _, _, N, hactiveNe,
    hstable, hactive, hmove, hfair⟩ :=
    spatial_cap_fair_anchored_frontier_process g eps ι W₀ heps hepsstep A hanchor hmodels
  have hlow0 : {a | metricScalarAt g a ≤ A} ⊆ interior (NeckFrontierState.region (seq 0)) :=
    hzero.symm ▸ hlow
  have hfairall := (NeckFrontierState.fair_of_eventually_constant_anchored_process
    g eps ι seq selected hepsrec hcompact hmono A hlow0 hselected N hactive hmove hfair).2
  exact ⟨seq, selected, hzero, hmono, hanti,
    (fun n => (Finset.mem_filter.mp (hselected n)).1), hsteps,
    N, hactiveNe.mono (Finset.filter_subset _ _), hstable, hmove, hfairall⟩

end

private theorem exists_saved_end_decomposition_of_anchors :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ eps : ℝ, eps ≤ eta →
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M] [PreconnectedSpace M] [NoncompactSpace M]
          (g : SmoothRiemannianMetric I3 M) (W : Set M),
          IsCompact W → W.Nonempty → closure (interior W) = W →
          ∀ (ι : Type v) [Finite ι] (point : ι → M) (neck : ∀ i, SpatialNeck g eps (point i))
          (level : ι → ℝ), (∀ i, |level i| ≤ 4) →
          Pairwise (fun i j => Disjoint (range (fun q => (neck i).map (q, level i)))
            (range (fun q => (neck j).map (q, level j)))) →
          frontier W = ⋃ i, range (fun q => (neck i).map (q, level i)) →
          ∀ A : ℝ,
          ((∀ x ∈ interior W, ∃ a ∈ connectedComponentIn (interior W) x,
            metricScalarAt g a ≤ A) ∨
            ({a : M | metricScalarAt g a ≤ A} ⊆ interior W ∧
              {a : M | metricScalarAt g a ≤ A}.Nonempty)) →
          (∀ (p : M) (nk : SpatialNeck g eps p) (level : ℝ), |level| ≤ 4 →
            nk.map (nk.center, level) ∉ interior W →
            Nonempty (SpatialNeck g eps (nk.map (nk.center, level))) ∨
            ∃ U : CompactDomain M, Nonempty (CapCore U.carrier) ∧
              range (fun z : Sphere 2 => nk.map (z, level)) ⊆ interior U.carrier ∧
              ∀ a ∈ U.carrier, A < metricScalarAt g a) →
          (∀ B : ℝ, IsCompact {x : M | metricScalarAt g x ≤ B}) →
          ∃ (K : Set M) (m : ℕ) (origin : Fin m → ι) (Θ : Fin m → Cylinder → M),
            W ⊆ K ∧ IsCompact K ∧ IsConnected K ∧ closure (interior K) = K ∧ 0 < m ∧
            Function.Injective origin ∧ frontier K ⊆ frontier W ∧
            (∀ i z, Θ i (z, 0) = (neck (origin i)).map (z, level (origin i))) ∧
            (∀ i, ContMDiffOn IC I3 ∞ (Θ i) (univ ×ˢ Ici (0 : ℝ)) ∧
              InjOn (Θ i) (univ ×ˢ Ici (0 : ℝ)) ∧
              IsProperMap (fun z : Sphere 2 × ℝ≥0 => Θ i (z.1, z.2.val)) ∧
              (let U : TopologicalSpace.Opens Cylinder :=
                ⟨univ ×ˢ Ioi (0 : ℝ), isOpen_univ.prod isOpen_Ioi⟩
               IsSmoothEmbedding IC I3 ∞ (fun z : U => Θ i z)) ∧
              Θ i '' (univ ×ˢ Ici (0 : ℝ)) ∩ K = range (fun z => Θ i (z, 0)) ∧
              (∀ B : ℝ, ∃ T : ℝ≥0, ∀ (z : Sphere 2) (s : ℝ≥0),
                T ≤ s → B < metricScalarAt g (Θ i (z, s.val))) ∧
              ∃ (p : M) (nk : SpatialNeck g eps p)
                (P : PartialDiffeomorph IC I3 Cylinder M ∞),
                p ∈ range (fun z => Θ i (z, 0)) ∧
                univ ×ˢ Icc (0 : ℝ) 1 ⊆ P.source ∧
                (∀ z t, t ∈ Icc (0 : ℝ) 1 → Θ i (z, t) = P (z, t)) ∧
                P '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆ nk.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹)) ∧
            Pairwise (fun i j => Disjoint (Θ i '' (univ ×ˢ Ici (0 : ℝ)))
              (Θ j '' (univ ×ˢ Ici (0 : ℝ)))) ∧
            frontier K = ⋃ i, range (fun z => Θ i (z, 0)) ∧
            K ∪ (⋃ i, Θ i '' (univ ×ˢ Ici (0 : ℝ))) = univ ∧
            ∀ alpha : ℝ, alpha < 1 / 11 → 13000 * eps ≤ alpha →
              ∀ i x, x ∈ Θ i '' (univ ×ˢ Ici (0 : ℝ)) →
                Nonempty (SpatialNeck g alpha x) := by
  classical
  let eta₁ := Classical.choose (exists_spatial_neck_level_graph_tolerance.{u})
  let eta₂ := Classical.choose (exists_spatial_neck_finite_frontier_step_tolerance.{u, v})
  have heta₁ : 0 < eta₁ :=
    (Classical.choose_spec (exists_spatial_neck_level_graph_tolerance.{u})).1
  have heta₂ : 0 < eta₂ :=
    (Classical.choose_spec (exists_spatial_neck_finite_frontier_step_tolerance.{u, v})).1
  refine ⟨min eta₁ (min eta₂ (1 / 156000)),
    lt_min heta₁ (lt_min heta₂ (by norm_num)), ?_⟩
  intro eps heps M _ _ _ _ _ _ g W hW hne hreg ι _ point neck level
    hlevel hpair hfront A hanchor hmodels hcompact
  let _ : Fintype ι := Fintype.ofFinite ι
  let sphere : ι → RecordedNeckSphere g eps := fun i =>
    RecordedNeckSphere.mk (point i) (neck i) (level i) (hlevel i)
      (Diffeomorph.refl I2 (Sphere 2) ∞)
  let W₀ : NeckFrontierState g eps ι :=
    NeckFrontierState.mk W hW hne hreg Finset.univ sphere
      (by
        change frontier W = ⋃ i ∈ Finset.univ, range (fun q => (neck i).map (q, level i))
        simpa only [Finset.mem_univ, iUnion_true] using hfront)
      (fun i _ j _ hij => hpair hij)
  have hrec : eps ≤ 1 / 156000 :=
    heps.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hmodels' (p : M) (nk : SpatialNeck g eps p) (level : ℝ)
      (hlevel : |level| ≤ 4) (hout : nk.map (nk.center, level) ∉ interior W) :
      Nonempty (SpatialNeck g eps (nk.map (nk.center, level))) ∨
      ∃ U : CompactDomain M, Nonempty (CapCore U.carrier) ∧
        range (fun z : Sphere 2 => nk.map (z, level)) ⊆ interior U.carrier ∧
        ∀ a : M, metricScalarAt g a ≤ A → a ∉ interior U.carrier := by
    rcases hmodels p nk level hlevel hout with hn | ⟨U, hU, hinside, hscalar⟩
    · exact Or.inl hn
    · exact Or.inr ⟨U, hU, hinside,
        fun a ha hint => (hscalar a (interior_subset hint)).not_ge ha⟩
  have hprocess :
    ∃ (seq : ℕ → NeckFrontierState g eps ι) (selected : ℕ → ι),
      seq 0 = W₀ ∧ Monotone (fun n => NeckFrontierState.region (seq n)) ∧
      Antitone (fun n => NeckFrontierState.alive (seq n)) ∧
      (∀ n, selected n ∈ NeckFrontierState.alive (seq n)) ∧
      (∀ n, OrdinaryNeckMoveAt g eps ι (seq n) (seq (n + 1)) (selected n) ∨
        (NeckFrontierState.alive (seq (n + 1)) ⊂ NeckFrontierState.alive (seq n) ∧
          NeckFrontierState.sphere (seq (n + 1)) = NeckFrontierState.sphere (seq n))) ∧
      ∃ N : ℕ, (NeckFrontierState.alive (seq N)).Nonempty ∧
        (∀ n, N ≤ n → NeckFrontierState.alive (seq n) = NeckFrontierState.alive (seq N)) ∧
        (∀ n, N ≤ n → OrdinaryNeckMoveAt g eps ι (seq n) (seq (n + 1)) (selected n)) ∧
        ∀ i ∈ NeckFrontierState.alive (seq N), {n | selected n = i}.Infinite := by
    rcases hanchor with hanchor | ⟨hlow, hlowne⟩
    · exact spatial_cap_fair_frontier_process g eps ι W₀
        (heps.trans (min_le_left _ _))
        (heps.trans ((min_le_right _ _).trans (min_le_left _ _))) A hanchor hmodels'
    · exact spatial_cap_fair_frontier_process_of_low_sublevel g eps ι W₀
        (heps.trans (min_le_left _ _))
        (heps.trans ((min_le_right _ _).trans (min_le_left _ _)))
        hrec hcompact A hlow hlowne hmodels'
  obtain ⟨seq, selected, hzero, hmono, hanti, hselected, hsteps, N, hne, hstable, hN, hfair⟩ :=
    hprocess
  obtain ⟨T, hsub, halive, hspheres, hconnect, Θ, hends, hdisjoint, hfull, hpointwise⟩ :=
    NeckFrontierState.exists_saved_end_family_of_fair_process g eps ι W₀
      hrec hcompact seq selected hzero hmono hanti hselected hsteps N hne hstable hN hfair
  let Ind := {i // i ∈ (NeckFrontierState.alive T)}
  let _ : Fintype Ind := (NeckFrontierState.alive T).fintypeCoeSort
  let e : Ind ≃ Fin (Fintype.card Ind) := Fintype.equivFin Ind
  let ends (i : Fin (Fintype.card Ind)) := Θ (e.symm i)
  have hneI : Nonempty Ind := (NeckFrontierState.alive_nonempty g eps ι T).to_subtype
  let _ : Nonempty Ind := hneI
  have hbase (i : Ind) : range (fun z => Θ i (z, 0)) = range (RecordedNeckSphere.map g eps (NeckFrontierState.sphere T i.val)) := by
    rw [hspheres]
    exact congrArg range (funext (hends i).2.2.2.2.2.1)
  have hindices : (⋃ i : Fin (Fintype.card Ind), ends i '' (univ ×ˢ Ici (0 : ℝ))) =
      ⋃ i : Ind, Θ i '' (univ ×ˢ Ici (0 : ℝ)) := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨e.symm i, hxi⟩
    · intro hx
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
      refine mem_iUnion.mpr ⟨e i, ?_⟩
      simpa only [ends, Equiv.symm_apply_apply] using hxi
  let origin (i : Fin (Fintype.card Ind)) := (e.symm i).val
  have horigin : Function.Injective origin := fun i j h => e.symm.injective (Subtype.ext h)
  have hfrontsub : frontier (NeckFrontierState.region T) ⊆ frontier W := by
    rw [(NeckFrontierState.frontier T)]
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    rw [hspheres] at hxi
    exact (NeckFrontierState.frontier W₀).symm ▸ mem_iUnion₂.mpr ⟨i, halive hi, hxi⟩
  have hbaseorigin (i z) : ends i (z, 0) = (neck (origin i)).map (z, level (origin i)) :=
    (hends (e.symm i)).2.2.2.2.2.1 z
  refine ⟨(NeckFrontierState.region T), Fintype.card Ind, origin, ends, hsub, (NeckFrontierState.compact T), hconnect, (NeckFrontierState.regular T),
    Fintype.card_pos, horigin, hfrontsub, hbaseorigin, ?_, ?_, ?_, ?_,
      fun alpha hsmall hreserve i x hx => hpointwise alpha hsmall hreserve (e.symm i) x hx⟩
  · intro i
    obtain ⟨hsm, hinj, hp, he, hi, hb, hd, p, nk, P, hpoint, hsource, hfirst, hcontrolled⟩ :=
      hends (e.symm i)
    refine ⟨hsm, hinj, hp, he, hi.trans (by rw [hspheres] at hbase; exact (hbase _).symm),
      hd, p, nk, P, ?_,
      hsource, hfirst, hcontrolled⟩
    have hbaseS : range (fun z => Θ (e.symm i) (z, 0)) = range (RecordedNeckSphere.map g eps (NeckFrontierState.sphere W₀ (e.symm i).val)) := by
      simpa only [hspheres] using hbase (e.symm i)
    exact hbaseS.symm ▸ hpoint
  · intro i j hij
    exact hdisjoint (fun h => hij (e.symm.injective h))
  · rw [(NeckFrontierState.frontier T)]
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
      let j : Ind := ⟨i, hi⟩
      refine mem_iUnion.mpr ⟨e j, ?_⟩
      change x ∈ range (fun z => Θ (e.symm (e j)) (z, 0))
      rw [e.symm_apply_apply, hbase j]
      exact hxi
    · intro hx
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
      rw [show range (fun z => ends i (z, 0)) = range (RecordedNeckSphere.map g eps (NeckFrontierState.sphere T (e.symm i).val)) from
        hbase (e.symm i)] at hxi
      exact mem_iUnion₂.mpr ⟨(e.symm i).val, (e.symm i).property, hxi⟩
  · rw [hindices]
    exact hfull

theorem exists_spatial_neck_saved_end_decomposition_with_pointwise_necks_of_neck_or_cap_core_tolerance :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ eps : ℝ, eps ≤ eta →
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M] [PreconnectedSpace M] [NoncompactSpace M]
          (g : SmoothRiemannianMetric I3 M) (W : Set M),
          IsCompact W → W.Nonempty → closure (interior W) = W →
          ∀ (ι : Type v) [Finite ι] (point : ι → M) (neck : ∀ i, SpatialNeck g eps (point i))
          (level : ι → ℝ), (∀ i, |level i| ≤ 4) →
          Pairwise (fun i j => Disjoint (range (fun q => (neck i).map (q, level i)))
            (range (fun q => (neck j).map (q, level j)))) →
          frontier W = ⋃ i, range (fun q => (neck i).map (q, level i)) →
          ∀ A : ℝ,
          (∀ x ∈ interior W, ∃ a ∈ connectedComponentIn (interior W) x,
            metricScalarAt g a ≤ A) →
          (∀ (p : M) (nk : SpatialNeck g eps p) (level : ℝ), |level| ≤ 4 →
            nk.map (nk.center, level) ∉ interior W →
            Nonempty (SpatialNeck g eps (nk.map (nk.center, level))) ∨
            ∃ U : CompactDomain M, Nonempty (CapCore U.carrier) ∧
              range (fun z : Sphere 2 => nk.map (z, level)) ⊆ interior U.carrier ∧
              ∀ a ∈ U.carrier, A < metricScalarAt g a) →
          (∀ B : ℝ, IsCompact {x : M | metricScalarAt g x ≤ B}) →
          ∃ (K : Set M) (m : ℕ) (origin : Fin m → ι) (Θ : Fin m → Cylinder → M),
            W ⊆ K ∧ IsCompact K ∧ IsConnected K ∧ closure (interior K) = K ∧ 0 < m ∧
            Function.Injective origin ∧ frontier K ⊆ frontier W ∧
            (∀ i z, Θ i (z, 0) = (neck (origin i)).map (z, level (origin i))) ∧
            (∀ i, ContMDiffOn IC I3 ∞ (Θ i) (univ ×ˢ Ici (0 : ℝ)) ∧
              InjOn (Θ i) (univ ×ˢ Ici (0 : ℝ)) ∧
              IsProperMap (fun z : Sphere 2 × ℝ≥0 => Θ i (z.1, z.2.val)) ∧
              (let U : TopologicalSpace.Opens Cylinder :=
                ⟨univ ×ˢ Ioi (0 : ℝ), isOpen_univ.prod isOpen_Ioi⟩
               IsSmoothEmbedding IC I3 ∞ (fun z : U => Θ i z)) ∧
              Θ i '' (univ ×ˢ Ici (0 : ℝ)) ∩ K = range (fun z => Θ i (z, 0)) ∧
              (∀ B : ℝ, ∃ T : ℝ≥0, ∀ (z : Sphere 2) (s : ℝ≥0),
                T ≤ s → B < metricScalarAt g (Θ i (z, s.val))) ∧
              ∃ (p : M) (nk : SpatialNeck g eps p)
                (P : PartialDiffeomorph IC I3 Cylinder M ∞),
                p ∈ range (fun z => Θ i (z, 0)) ∧
                univ ×ˢ Icc (0 : ℝ) 1 ⊆ P.source ∧
                (∀ z t, t ∈ Icc (0 : ℝ) 1 → Θ i (z, t) = P (z, t)) ∧
                P '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆ nk.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹)) ∧
            Pairwise (fun i j => Disjoint (Θ i '' (univ ×ˢ Ici (0 : ℝ)))
              (Θ j '' (univ ×ˢ Ici (0 : ℝ)))) ∧
            frontier K = ⋃ i, range (fun z => Θ i (z, 0)) ∧
            K ∪ (⋃ i, Θ i '' (univ ×ˢ Ici (0 : ℝ))) = univ ∧
            ∀ alpha : ℝ, alpha < 1 / 11 → 13000 * eps ≤ alpha →
              ∀ i x, x ∈ Θ i '' (univ ×ˢ Ici (0 : ℝ)) →
                Nonempty (SpatialNeck g alpha x) := by
  obtain ⟨eta, heta, hproduce⟩ := exists_saved_end_decomposition_of_anchors.{u, v}
  refine ⟨eta, heta, ?_⟩
  intro eps heps M _ _ _ _ _ _ g W hW hne hreg ι _ point neck level
    hlevel hpair hfront A hanchor hmodels hcompact
  exact hproduce eps heps M g W hW hne hreg ι point neck level
    hlevel hpair hfront A (Or.inl hanchor) hmodels hcompact

theorem exists_spatial_neck_saved_end_decomposition_of_neck_or_cap_core_tolerance :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ eps : ℝ, eps ≤ eta →
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M] [PreconnectedSpace M] [NoncompactSpace M]
          (g : SmoothRiemannianMetric I3 M) (W : Set M),
          IsCompact W → W.Nonempty → closure (interior W) = W →
          ∀ (ι : Type v) [Finite ι] (point : ι → M) (neck : ∀ i, SpatialNeck g eps (point i))
          (level : ι → ℝ), (∀ i, |level i| ≤ 4) →
          Pairwise (fun i j => Disjoint (range (fun q => (neck i).map (q, level i)))
            (range (fun q => (neck j).map (q, level j)))) →
          frontier W = ⋃ i, range (fun q => (neck i).map (q, level i)) →
          ∀ A : ℝ,
          (∀ x ∈ interior W, ∃ a ∈ connectedComponentIn (interior W) x,
            metricScalarAt g a ≤ A) →
          (∀ (p : M) (nk : SpatialNeck g eps p) (level : ℝ), |level| ≤ 4 →
            nk.map (nk.center, level) ∉ interior W →
            Nonempty (SpatialNeck g eps (nk.map (nk.center, level))) ∨
            ∃ U : CompactDomain M, Nonempty (CapCore U.carrier) ∧
              range (fun z : Sphere 2 => nk.map (z, level)) ⊆ interior U.carrier ∧
              ∀ a ∈ U.carrier, A < metricScalarAt g a) →
          (∀ B : ℝ, IsCompact {x : M | metricScalarAt g x ≤ B}) →
          ∃ (K : Set M) (m : ℕ) (origin : Fin m → ι) (Θ : Fin m → Cylinder → M),
            W ⊆ K ∧ IsCompact K ∧ IsConnected K ∧ closure (interior K) = K ∧ 0 < m ∧
            Function.Injective origin ∧ frontier K ⊆ frontier W ∧
            (∀ i z, Θ i (z, 0) = (neck (origin i)).map (z, level (origin i))) ∧
            (∀ i, ContMDiffOn IC I3 ∞ (Θ i) (univ ×ˢ Ici (0 : ℝ)) ∧
              InjOn (Θ i) (univ ×ˢ Ici (0 : ℝ)) ∧
              IsProperMap (fun z : Sphere 2 × ℝ≥0 => Θ i (z.1, z.2.val)) ∧
              (let U : TopologicalSpace.Opens Cylinder :=
                ⟨univ ×ˢ Ioi (0 : ℝ), isOpen_univ.prod isOpen_Ioi⟩
               IsSmoothEmbedding IC I3 ∞ (fun z : U => Θ i z)) ∧
              Θ i '' (univ ×ˢ Ici (0 : ℝ)) ∩ K = range (fun z => Θ i (z, 0)) ∧
              (∀ B : ℝ, ∃ T : ℝ≥0, ∀ (z : Sphere 2) (s : ℝ≥0),
                T ≤ s → B < metricScalarAt g (Θ i (z, s.val))) ∧
              ∃ (p : M) (nk : SpatialNeck g eps p)
                (P : PartialDiffeomorph IC I3 Cylinder M ∞),
                p ∈ range (fun z => Θ i (z, 0)) ∧
                univ ×ˢ Icc (0 : ℝ) 1 ⊆ P.source ∧
                (∀ z t, t ∈ Icc (0 : ℝ) 1 → Θ i (z, t) = P (z, t)) ∧
                P '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆ nk.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹)) ∧
            Pairwise (fun i j => Disjoint (Θ i '' (univ ×ˢ Ici (0 : ℝ)))
              (Θ j '' (univ ×ˢ Ici (0 : ℝ)))) ∧
            frontier K = ⋃ i, range (fun z => Θ i (z, 0)) ∧
            K ∪ (⋃ i, Θ i '' (univ ×ˢ Ici (0 : ℝ))) = univ := by
  obtain ⟨eta, heta, hproduce⟩ :=
    exists_spatial_neck_saved_end_decomposition_with_pointwise_necks_of_neck_or_cap_core_tolerance.{u, v}
  refine ⟨eta, heta, ?_⟩
  intro eps heps M _ _ _ _ _ _ g W hW hne hreg ι _ point neck level
    hlevel hpair hfront A hanchor hmodels hcompact
  obtain ⟨K, m, origin, Θ, hWK, hK, hconn, hregK, hm, horigin, hfrontW, hbase,
    hends, hdisjoint, hfrontK, hcover, _⟩ :=
    hproduce eps heps M g W hW hne hreg ι point neck level hlevel hpair hfront
      A hanchor hmodels hcompact
  exact ⟨K, m, origin, Θ, hWK, hK, hconn, hregK, hm, horigin, hfrontW, hbase,
    hends, hdisjoint, hfrontK, hcover⟩

theorem exists_spatial_neck_saved_end_decomposition_covering_scalar_sublevel_tolerance :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ eps : ℝ, eps ≤ eta →
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M] [PreconnectedSpace M] [NoncompactSpace M]
          (g : SmoothRiemannianMetric I3 M) (W : Set M),
          IsCompact W → closure (interior W) = W →
          ∀ (ι : Type v) [Finite ι] (point : ι → M) (neck : ∀ i, SpatialNeck g eps (point i))
          (level : ι → ℝ), (∀ i, |level i| ≤ 4) →
          Pairwise (fun i j => Disjoint (range (fun q => (neck i).map (q, level i)))
            (range (fun q => (neck j).map (q, level j)))) →
          frontier W = ⋃ i, range (fun q => (neck i).map (q, level i)) →
          ∀ A : ℝ,
          {a : M | metricScalarAt g a ≤ A} ⊆ interior W →
          {a : M | metricScalarAt g a ≤ A}.Nonempty →
          (∀ (p : M) (nk : SpatialNeck g eps p) (level : ℝ), |level| ≤ 4 →
            nk.map (nk.center, level) ∉ interior W →
            Nonempty (SpatialNeck g eps (nk.map (nk.center, level))) ∨
            ∃ U : CompactDomain M, Nonempty (CapCore U.carrier) ∧
              range (fun z : Sphere 2 => nk.map (z, level)) ⊆ interior U.carrier ∧
              ∀ a ∈ U.carrier, A < metricScalarAt g a) →
          (∀ B : ℝ, IsCompact {x : M | metricScalarAt g x ≤ B}) →
          ∃ (K : Set M) (m : ℕ) (origin : Fin m → ι) (Θ : Fin m → Cylinder → M),
            W ⊆ K ∧ IsCompact K ∧ IsConnected K ∧ closure (interior K) = K ∧ 0 < m ∧
            Function.Injective origin ∧ frontier K ⊆ frontier W ∧
            (∀ i z, Θ i (z, 0) = (neck (origin i)).map (z, level (origin i))) ∧
            (∀ i, ContMDiffOn IC I3 ∞ (Θ i) (univ ×ˢ Ici (0 : ℝ)) ∧
              InjOn (Θ i) (univ ×ˢ Ici (0 : ℝ)) ∧
              IsProperMap (fun z : Sphere 2 × ℝ≥0 => Θ i (z.1, z.2.val)) ∧
              (let U : TopologicalSpace.Opens Cylinder :=
                ⟨univ ×ˢ Ioi (0 : ℝ), isOpen_univ.prod isOpen_Ioi⟩
               IsSmoothEmbedding IC I3 ∞ (fun z : U => Θ i z)) ∧
              Θ i '' (univ ×ˢ Ici (0 : ℝ)) ∩ K = range (fun z => Θ i (z, 0)) ∧
              (∀ B : ℝ, ∃ T : ℝ≥0, ∀ (z : Sphere 2) (s : ℝ≥0),
                T ≤ s → B < metricScalarAt g (Θ i (z, s.val))) ∧
              ∃ (p : M) (nk : SpatialNeck g eps p)
                (P : PartialDiffeomorph IC I3 Cylinder M ∞),
                p ∈ range (fun z => Θ i (z, 0)) ∧
                univ ×ˢ Icc (0 : ℝ) 1 ⊆ P.source ∧
                (∀ z t, t ∈ Icc (0 : ℝ) 1 → Θ i (z, t) = P (z, t)) ∧
                P '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆ nk.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹)) ∧
            Pairwise (fun i j => Disjoint (Θ i '' (univ ×ˢ Ici (0 : ℝ)))
              (Θ j '' (univ ×ˢ Ici (0 : ℝ)))) ∧
            frontier K = ⋃ i, range (fun z => Θ i (z, 0)) ∧
            K ∪ (⋃ i, Θ i '' (univ ×ˢ Ici (0 : ℝ))) = univ ∧
            ∀ alpha : ℝ, alpha < 1 / 11 → 13000 * eps ≤ alpha →
              ∀ i x, x ∈ Θ i '' (univ ×ˢ Ici (0 : ℝ)) →
                Nonempty (SpatialNeck g alpha x) := by
  obtain ⟨eta, heta, hproduce⟩ := exists_saved_end_decomposition_of_anchors.{u, v}
  refine ⟨eta, heta, ?_⟩
  intro eps heps M _ _ _ _ _ _ g W hW hreg ι _ point neck level
    hlevel hpair hfront A hlow hlowne hmodels hcompact
  have hne : W.Nonempty := hlowne.mono (hlow.trans interior_subset)
  exact hproduce eps heps M g W hW hne hreg ι point neck level
    hlevel hpair hfront A (Or.inr ⟨hlow, hlowne⟩) hmodels hcompact

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
