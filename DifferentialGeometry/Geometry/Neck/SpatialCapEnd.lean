import DifferentialGeometry.Geometry.Neck.FiniteFrontierEnd
import DifferentialGeometry.Geometry.Neck.SpatialCapFilling
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
  NeckFrontierState.region NeckFrontierState.compact NeckFrontierState.nonempty
  NeckFrontierState.regular NeckFrontierState.alive NeckFrontierState.sphere
  NeckFrontierState.frontier NeckFrontierState.disjoint NeckFrontierState.mk
  NeckFrontierState OrdinaryNeckMoveAtCentral OrdinaryNeckMoveAt OrdinaryNeckMove
  NeckFrontierState.exists_step_at_of_neck_central NeckFrontierState.alive_nonempty
  NeckFrontierState.exists_saved_end_family_of_fair_process
  NeckFrontierState.exists_scheduled_process_of_transition
  NeckFrontierState.exists_proper_end_of_process from DifferentialGeometry.Geometry.Neck.FiniteFrontierEnd

universe u v
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [PreconnectedSpace M]
  (g : SmoothRiemannianMetric I3 M) (eps : ℝ) (ι : Type v)

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
        hinter, hfill, hcontrolled, hband, hpoint, _⟩
      exact ⟨V, hWV, htransfer hWV hcomponents, Or.inl ⟨halive, hia, p, nk, P, hsource,
        hregion, hP0, hP1, hother, hinter, hfill, hcontrolled, hband, hpoint⟩⟩
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
  obtain ⟨seq, selected, hzero, hmono, hanti, hselected, hsteps, N, hne, hstable, hN, hfair⟩ :=
    spatial_cap_fair_frontier_process g eps ι W₀
      (heps.trans (min_le_left _ _))
      (heps.trans ((min_le_right _ _).trans (min_le_left _ _))) A hanchor hmodels'
  obtain ⟨T, hsub, halive, hspheres, hconnect, Θ, hends, hdisjoint, hfull⟩ :=
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
    Fintype.card_pos, horigin, hfrontsub, hbaseorigin, ?_, ?_, ?_, ?_⟩
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

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
