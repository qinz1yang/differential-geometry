import DifferentialGeometry.Geometry.Neck.FiniteFrontierEnd
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCapFrontierFilling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialNeckLocalTransport
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
  NeckFrontierState.exists_proper_end_of_process from DifferentialGeometry.Geometry.Neck.FiniteFrontierEnd

universe u v
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [PreconnectedSpace M] [SigmaCompactSpace M]
  {D : RealTimeInterval} (S : SolutionOn (I := I3) (M := M) D)
  (eps C1 C2 t : ℝ) (ι : Type v)

open scoped Classical in
private theorem canonical_frontier_step
    (W : NeckFrontierState (S.base.metric t) eps ι)
    (hconn : IsPreconnected (interior (NeckFrontierState.region W)))
    (heps : eps ≤ Classical.choose (exists_spatial_neck_level_graph_tolerance.{u}))
    (hepsstep : eps ≤ Classical.choose (exists_spatial_neck_finite_frontier_step_tolerance.{u, v}))
    (hepscap : eps ≤ 1 / 8646)
    (i : ι) (hi : i ∈ (NeckFrontierState.alive W))
    (witness : CanonicalWitness S eps C1 C2
      ((RecordedNeckSphere.neck (NeckFrontierState.sphere W i)).map ((RecordedNeckSphere.neck (NeckFrontierState.sphere W i)).center, (RecordedNeckSphere.level (NeckFrontierState.sphere W i)))) t)
    (anchor : M) (ha : anchor ∈ (NeckFrontierState.region W))
    (hgap : C2 * S.scalar t anchor <
      S.scalar t ((RecordedNeckSphere.neck (NeckFrontierState.sphere W i)).map ((RecordedNeckSphere.neck (NeckFrontierState.sphere W i)).center, (RecordedNeckSphere.level (NeckFrontierState.sphere W i))))) :
    ∃ V : NeckFrontierState (S.base.metric t) eps ι,
      (NeckFrontierState.region W) ⊆ (NeckFrontierState.region V) ∧ IsConnected (interior (NeckFrontierState.region V)) ∧
      (OrdinaryNeckMoveAt (S.base.metric t) eps ι W V i ∨
        ((NeckFrontierState.alive V) ⊂ (NeckFrontierState.alive W) ∧ (NeckFrontierState.sphere V) = (NeckFrontierState.sphere W))) ∧
      ((∃ localNeck : LocalNeck S eps
          ((RecordedNeckSphere.neck (NeckFrontierState.sphere W i)).map
            ((RecordedNeckSphere.neck (NeckFrontierState.sphere W i)).center,
              RecordedNeckSphere.level (NeckFrontierState.sphere W i))) t witness.domain.carrier,
          witness.alternative = CanonicalAlternative.neck localNeck) ∨
        ∃ (cap : LocalCap S eps
            ((RecordedNeckSphere.neck (NeckFrontierState.sphere W i)).map
              ((RecordedNeckSphere.neck (NeckFrontierState.sphere W i)).center,
                RecordedNeckSphere.level (NeckFrontierState.sphere W i))) t witness.domain.carrier)
          (depth : ∀ z ∈ cap.tube,
            10000 / Real.sqrt (S.scalar t
              ((RecordedNeckSphere.neck (NeckFrontierState.sphere W i)).map
                ((RecordedNeckSphere.neck (NeckFrontierState.sphere W i)).center,
                  RecordedNeckSphere.level (NeckFrontierState.sphere W i)))) ≤
              metricDistance (S.base.metric t)
                ((RecordedNeckSphere.neck (NeckFrontierState.sphere W i)).map
                  ((RecordedNeckSphere.neck (NeckFrontierState.sphere W i)).center,
                    RecordedNeckSphere.level (NeckFrontierState.sphere W i))) z),
          witness.alternative = CanonicalAlternative.cap cap depth ∧
          ∃ K : Set M, IsCompact K ∧ K ⊆ interior cap.core.carrier ∧
            NeckFrontierState.region V = NeckFrontierState.region W ∪ K ∧
            NeckFrontierState.alive V = (NeckFrontierState.alive W).erase i ∧
            K ∩ NeckFrontierState.region W = range (RecordedNeckSphere.map
              (S.base.metric t) eps (NeckFrontierState.sphere W i))) := by
  classical
  have hfront : frontier (NeckFrontierState.region W) = ⋃ j ∈ (NeckFrontierState.alive W),
      range (fun z : Sphere 2 => (RecordedNeckSphere.neck (NeckFrontierState.sphere W j)).map (z, (RecordedNeckSphere.level (NeckFrontierState.sphere W j)))) := by
    simpa only [RecordedNeckSphere.range_map] using (NeckFrontierState.frontier W)
  have hpair : ((NeckFrontierState.alive W) : Set ι).Pairwise (fun i j =>
      Disjoint (range (fun z : Sphere 2 => (RecordedNeckSphere.neck (NeckFrontierState.sphere W i)).map (z, (RecordedNeckSphere.level (NeckFrontierState.sphere W i)))))
        (range (fun z : Sphere 2 => (RecordedNeckSphere.neck (NeckFrontierState.sphere W j)).map (z, (RecordedNeckSphere.level (NeckFrontierState.sphere W j)))))) := by
    simpa only [RecordedNeckSphere.range_map] using (NeckFrontierState.disjoint W)
  rcases witness.exists_neck_or_cap_filling_on_finite_spatial_neck_frontier
    (NeckFrontierState.alive W) (fun j => (RecordedNeckSphere.point (NeckFrontierState.sphere W j))) (fun j => (RecordedNeckSphere.neck (NeckFrontierState.sphere W j)))
    (fun j => (RecordedNeckSphere.level (NeckFrontierState.sphere W j))) (fun j _ => (RecordedNeckSphere.bound (NeckFrontierState.sphere W j)))
    hpair hepscap i hi (RecordedNeckSphere.neck (NeckFrontierState.sphere W i)).center rfl
    (NeckFrontierState.compact W) (NeckFrontierState.regular W) hconn hfront anchor ha hgap with hn | hc
  · obtain ⟨localNeck, htag⟩ := hn
    obtain ⟨V, hWV, _, hVI, _, hm | hr⟩ :=
      NeckFrontierState.exists_step_at_of_neck_central (S.base.metric t) eps ι W i hi
        heps hepsstep ⟨localNeck.strong.toSpatialNeck⟩
    · rcases hm with ⟨halive, hia, p, nk, P, hsource, hregion, hP0, hP1, hother,
        hinter, hfill, hcontrolled, hband, hpoint, hcentral⟩
      exact ⟨V, hWV, hVI hconn, Or.inl ⟨halive, hia, p, nk, P, hsource,
        hregion, hP0, hP1, hother, hinter, hfill, hcontrolled, hband, hpoint, hcentral⟩,
        Or.inl ⟨localNeck, htag⟩⟩
    · exact ⟨V, hWV, hVI hconn, Or.inr hr, Or.inl ⟨localNeck, htag⟩⟩
  · obtain ⟨cap, depth, htag, K, hK, _, hKin, _, hinter, hVK, hVI, hVR, hVF, _, _, _, _, _⟩ := hc
    let V : NeckFrontierState (S.base.metric t) eps ι :=
      NeckFrontierState.mk ((NeckFrontierState.region W) ∪ K) hVK
        ((NeckFrontierState.nonempty W).mono subset_union_left) hVR
        ((NeckFrontierState.alive W).erase i) (NeckFrontierState.sphere W)
        (by simpa only [RecordedNeckSphere.range_map] using hVF)
        (fun j hj k hk hjk => (NeckFrontierState.disjoint W)
          (Finset.mem_of_mem_erase hj) (Finset.mem_of_mem_erase hk) hjk)
    refine ⟨V, subset_union_left, hVI, Or.inr ⟨Finset.erase_ssubset hi, rfl⟩,
      Or.inr ⟨cap, depth, htag, K, hK, hKin, rfl, rfl, ?_⟩⟩
    simpa only [RecordedNeckSphere.range_map] using hinter

private theorem canonical_scheduled_frontier_process [NoncompactSpace M]
    (W₀ : NeckFrontierState (S.base.metric t) eps ι) (schedule : ℕ → ι)
    (hconn : IsPreconnected (interior (NeckFrontierState.region W₀)))
    (heps : eps ≤ Classical.choose (exists_spatial_neck_level_graph_tolerance.{u}))
    (hepsstep : eps ≤ Classical.choose (exists_spatial_neck_finite_frontier_step_tolerance.{u, v}))
    (hepscap : eps ≤ 1 / 8646)
    (anchor : M) (ha : anchor ∈ NeckFrontierState.region W₀)
    (hcanonical : ∀ x : M, x ∉ interior (NeckFrontierState.region W₀) →
      Nonempty (CanonicalWitness S eps C1 C2 x t))
    (hgap : ∀ x : M, x ∉ interior (NeckFrontierState.region W₀) →
      C2 * S.scalar t anchor < S.scalar t x) :
    ∃ (seq : ℕ → NeckFrontierState (S.base.metric t) eps ι) (selected : ℕ → ι),
      seq 0 = W₀ ∧ Monotone (fun n => NeckFrontierState.region (seq n)) ∧
      Antitone (fun n => NeckFrontierState.alive (seq n)) ∧
      (∀ n, IsPreconnected (interior (NeckFrontierState.region (seq n))) ∧
        anchor ∈ NeckFrontierState.region (seq n) ∧
        ∀ x ∉ interior (NeckFrontierState.region (seq n)),
          C2 * S.scalar t anchor < S.scalar t x) ∧
      (∀ n, selected n ∈ NeckFrontierState.alive (seq n)) ∧
      (∀ n, schedule n ∈ NeckFrontierState.alive (seq n) → selected n = schedule n) ∧
      (∀ n, OrdinaryNeckMoveAt (S.base.metric t) eps ι (seq n) (seq (n + 1)) (selected n) ∨
        (NeckFrontierState.alive (seq (n + 1)) ⊂ NeckFrontierState.alive (seq n) ∧
          NeckFrontierState.sphere (seq (n + 1)) = NeckFrontierState.sphere (seq n))) ∧
      ∃ N : ℕ, ∀ n, N ≤ n →
        OrdinaryNeckMoveAt (S.base.metric t) eps ι (seq n) (seq (n + 1)) (selected n) := by
  classical
  let State := {W : NeckFrontierState (S.base.metric t) eps ι //
    NeckFrontierState.region W₀ ⊆ NeckFrontierState.region W ∧
      IsPreconnected (interior (NeckFrontierState.region W))}
  let pick (n : ℕ) (W : State) : ι :=
    if schedule n ∈ NeckFrontierState.alive W.val then schedule n
    else (NeckFrontierState.alive_nonempty (S.base.metric t) eps ι W.val).choose
  have hpick (n : ℕ) (W : State) : pick n W ∈ NeckFrontierState.alive W.val := by
    dsimp only [pick]
    split
    · assumption
    · exact (NeckFrontierState.alive_nonempty (S.base.metric t) eps ι W.val).choose_spec
  have hnext (n : ℕ) (W : State) : ∃ V : State,
      NeckFrontierState.region W.val ⊆ NeckFrontierState.region V.val ∧
      (OrdinaryNeckMoveAt (S.base.metric t) eps ι W.val V.val (pick n W) ∨
        (NeckFrontierState.alive V.val ⊂ NeckFrontierState.alive W.val ∧
          NeckFrontierState.sphere V.val = NeckFrontierState.sphere W.val)) := by
    let f := NeckFrontierState.sphere W.val (pick n W)
    let x := (RecordedNeckSphere.neck f).map
      ((RecordedNeckSphere.neck f).center, RecordedNeckSphere.level f)
    have hx : x ∈ frontier (NeckFrontierState.region W.val) := by
      rw [NeckFrontierState.frontier W.val]
      apply mem_iUnion₂.mpr
      refine ⟨pick n W, hpick n W, ?_⟩
      rw [RecordedNeckSphere.range_map]
      exact mem_range_self _
    have hout : x ∉ interior (NeckFrontierState.region W₀) :=
      fun h => hx.2 (interior_mono W.property.1 h)
    obtain ⟨witness⟩ := hcanonical x hout
    obtain ⟨V, hWV, hVI, hmove, _⟩ :=
      canonical_frontier_step S eps C1 C2 t ι W.val W.property.2
        heps hepsstep hepscap (pick n W) (hpick n W) witness anchor
        (W.property.1 ha) (hgap x hout)
    exact ⟨⟨V, W.property.1.trans hWV, hVI.isPreconnected⟩, hWV, hmove⟩
  choose next hnext using hnext
  let states : ℕ → State := Nat.rec ⟨W₀, Subset.rfl, hconn⟩ (fun n W => next n W)
  let seq (n : ℕ) := (states n).val
  let selected (n : ℕ) := pick n (states n)
  have hmono : Monotone (fun n => NeckFrontierState.region (seq n)) :=
    monotone_nat_of_le_succ (fun n => (hnext n (states n)).1)
  have hsteps (n : ℕ) : OrdinaryNeckMoveAt (S.base.metric t) eps ι (seq n) (seq (n + 1)) (selected n) ∨
      (NeckFrontierState.alive (seq (n + 1)) ⊂ NeckFrontierState.alive (seq n) ∧
        NeckFrontierState.sphere (seq (n + 1)) = NeckFrontierState.sphere (seq n)) :=
    (hnext n (states n)).2
  have hanti : Antitone (fun n => NeckFrontierState.alive (seq n)) := by
    apply antitone_nat_of_succ_le
    intro n
    rcases hsteps n with hn | hd
    · exact hn.1.le
    · exact hd.1.le
  obtain ⟨N, hN⟩ := hanti.exists_forall_ge_of_or_succ_lt
    (fun n => (hsteps n).imp_right And.left)
  refine ⟨seq, selected, rfl, hmono, hanti, ?_, fun n => hpick n (states n), ?_, hsteps, N, hN⟩
  · intro n
    refine ⟨(states n).property.2, (states n).property.1 ha, ?_⟩
    intro x hx
    exact hgap x (fun h => hx (interior_mono (states n).property.1 h))
  · intro n hn
    exact ite_eq_left hn


private theorem canonical_frontier_process [NoncompactSpace M]
    (W₀ : NeckFrontierState (S.base.metric t) eps ι)
    (hconn : IsPreconnected (interior (NeckFrontierState.region W₀)))
    (heps : eps ≤ Classical.choose (exists_spatial_neck_level_graph_tolerance.{u}))
    (hepsstep : eps ≤ Classical.choose (exists_spatial_neck_finite_frontier_step_tolerance.{u, v}))
    (hepscap : eps ≤ 1 / 8646)
    (anchor : M) (ha : anchor ∈ NeckFrontierState.region W₀)
    (hcanonical : ∀ x : M, x ∉ interior (NeckFrontierState.region W₀) →
      Nonempty (CanonicalWitness S eps C1 C2 x t))
    (hgap : ∀ x : M, x ∉ interior (NeckFrontierState.region W₀) →
      C2 * S.scalar t anchor < S.scalar t x) :
    ∃ seq : ℕ → NeckFrontierState (S.base.metric t) eps ι,
      seq 0 = W₀ ∧ Monotone (fun n => NeckFrontierState.region (seq n)) ∧
      Antitone (fun n => NeckFrontierState.alive (seq n)) ∧
      (∀ n, IsPreconnected (interior (NeckFrontierState.region (seq n))) ∧
        anchor ∈ NeckFrontierState.region (seq n) ∧
        ∀ x ∉ interior (NeckFrontierState.region (seq n)),
          C2 * S.scalar t anchor < S.scalar t x) ∧
      (∀ n, OrdinaryNeckMove (S.base.metric t) eps ι (seq n) (seq (n + 1)) ∨
        (NeckFrontierState.alive (seq (n + 1)) ⊂ NeckFrontierState.alive (seq n) ∧
          NeckFrontierState.sphere (seq (n + 1)) = NeckFrontierState.sphere (seq n))) ∧
      ∃ N : ℕ, ∀ n, N ≤ n →
        OrdinaryNeckMove (S.base.metric t) eps ι (seq n) (seq (n + 1)) := by
  classical
  let i := (NeckFrontierState.alive_nonempty (S.base.metric t) eps ι W₀).choose
  obtain ⟨seq, selected, hzero, hmono, hanti, hinv, _, _, hsteps, N, hN⟩ :=
    canonical_scheduled_frontier_process S eps C1 C2 t ι W₀ (fun _ => i)
      hconn heps hepsstep hepscap anchor ha hcanonical hgap
  have hordinary {W V : NeckFrontierState (S.base.metric t) eps ι} {j : ι}
      (h : OrdinaryNeckMoveAt (S.base.metric t) eps ι W V j) :
      OrdinaryNeckMove (S.base.metric t) eps ι W V := ⟨h.1, j, h.2⟩
  exact ⟨seq, hzero, hmono, hanti, hinv,
    fun n => (hsteps n).imp_left hordinary, N, fun n hn => hordinary (hN n hn)⟩

private theorem canonical_fair_frontier_process [NoncompactSpace M]
    (W₀ : NeckFrontierState (S.base.metric t) eps ι)
    (hconn : IsPreconnected (interior (NeckFrontierState.region W₀)))
    (heps : eps ≤ Classical.choose (exists_spatial_neck_level_graph_tolerance.{u}))
    (hepsstep : eps ≤ Classical.choose (exists_spatial_neck_finite_frontier_step_tolerance.{u, v}))
    (hepscap : eps ≤ 1 / 8646)
    (anchor : M) (ha : anchor ∈ NeckFrontierState.region W₀)
    (hcanonical : ∀ x : M, x ∉ interior (NeckFrontierState.region W₀) →
      Nonempty (CanonicalWitness S eps C1 C2 x t))
    (hgap : ∀ x : M, x ∉ interior (NeckFrontierState.region W₀) →
      C2 * S.scalar t anchor < S.scalar t x) :
    ∃ (seq : ℕ → NeckFrontierState (S.base.metric t) eps ι) (selected : ℕ → ι),
      seq 0 = W₀ ∧ Monotone (fun n => NeckFrontierState.region (seq n)) ∧
      Antitone (fun n => NeckFrontierState.alive (seq n)) ∧
      (∀ n, IsPreconnected (interior (NeckFrontierState.region (seq n))) ∧
        anchor ∈ NeckFrontierState.region (seq n) ∧
        ∀ x ∉ interior (NeckFrontierState.region (seq n)),
          C2 * S.scalar t anchor < S.scalar t x) ∧
      (∀ n, selected n ∈ NeckFrontierState.alive (seq n)) ∧
      (∀ n, OrdinaryNeckMoveAt (S.base.metric t) eps ι (seq n) (seq (n + 1)) (selected n) ∨
        (NeckFrontierState.alive (seq (n + 1)) ⊂ NeckFrontierState.alive (seq n) ∧
          NeckFrontierState.sphere (seq (n + 1)) = NeckFrontierState.sphere (seq n))) ∧
      ∃ N : ℕ, (NeckFrontierState.alive (seq N)).Nonempty ∧
        (∀ n, N ≤ n → NeckFrontierState.alive (seq n) = NeckFrontierState.alive (seq N)) ∧
        (∀ n, N ≤ n →
          OrdinaryNeckMoveAt (S.base.metric t) eps ι (seq n) (seq (n + 1)) (selected n)) ∧
        ∀ i ∈ NeckFrontierState.alive (seq N), {n | selected n = i}.Infinite := by
  classical
  obtain ⟨schedule, _, hfair⟩ :=
    (NeckFrontierState.alive W₀).finite_toSet.countable.exists_sequence_cofinal_fibers
      (NeckFrontierState.alive_nonempty (S.base.metric t) eps ι W₀)
  obtain ⟨seq, selected, hzero, hmono, hanti, hinv, hselected, hschedule, hsteps, N, hN⟩ :=
    canonical_scheduled_frontier_process S eps C1 C2 t ι W₀ schedule
      hconn heps hepsstep hepscap anchor ha hcanonical hgap
  have hstable (n : ℕ) (hn : N ≤ n) :
      NeckFrontierState.alive (seq n) = NeckFrontierState.alive (seq N) := by
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih => exact (hN n hn).1.trans ih
  refine ⟨seq, selected, hzero, hmono, hanti, hinv, hselected, hsteps, N,
    NeckFrontierState.alive_nonempty (S.base.metric t) eps ι (seq N), hstable, hN, ?_⟩
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

theorem exists_spatial_neck_proper_end_of_canonical_witnesses_tolerance :
    ∃ eta : ℝ, 0 < eta ∧ ∀ eps : ℝ, eps ≤ eta →
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [PreconnectedSpace M] [NoncompactSpace M]
        [SigmaCompactSpace M] (D : RealTimeInterval)
        (S : SolutionOn (I := I3) (M := M) D) (C1 C2 t : ℝ) (W : Set M),
        IsCompact W → closure (interior W) = W → IsPreconnected (interior W) →
        ∀ (ι : Type v) [Finite ι] (point : ι → M)
          (neck : ∀ i, SpatialNeck (S.base.metric t) eps (point i)) (level : ι → ℝ),
          (∀ i, |level i| ≤ 4) →
          Pairwise (fun i j => Disjoint
            (range (fun q => (neck i).map (q, level i)))
            (range (fun q => (neck j).map (q, level j)))) →
          frontier W = ⋃ i, range (fun q => (neck i).map (q, level i)) →
          ∀ anchor ∈ W,
            (∀ x : M, x ∉ interior W → Nonempty (CanonicalWitness S eps C1 C2 x t)) →
            (∀ x : M, x ∉ interior W → C2 * S.scalar t anchor < S.scalar t x) →
            (∀ B : ℝ, IsCompact {x : M | S.scalar t x ≤ B}) →
            ∃ (i : ι) (Θ : Cylinder → M),
              ContMDiffOn IC I3 ∞ Θ (univ ×ˢ Ici (0 : ℝ)) ∧
              InjOn Θ (univ ×ˢ Ici (0 : ℝ)) ∧
              IsProperMap (fun z : Sphere 2 × ℝ≥0 => Θ (z.1, z.2.val)) ∧
              (let U : TopologicalSpace.Opens Cylinder :=
                ⟨univ ×ˢ Ioi (0 : ℝ), isOpen_univ.prod isOpen_Ioi⟩
               IsSmoothEmbedding IC I3 ∞ (fun z : U => Θ z)) ∧
              Θ '' (univ ×ˢ Ici (0 : ℝ)) ∩ W =
                range (fun z => (neck i).map (z, level i)) ∧
              (∀ z, Θ (z, 0) = (neck i).map (z, level i)) ∧
              (∀ B : ℝ, ∃ T : ℝ≥0, ∀ (z : Sphere 2) (s : ℝ≥0),
                T ≤ s → B < S.scalar t (Θ (z, s.val))) ∧
              ∃ (p : M) (nk : SpatialNeck (S.base.metric t) eps p)
                (P : PartialDiffeomorph IC I3 Cylinder M ∞),
                p ∈ range (fun z => (neck i).map (z, level i)) ∧
                univ ×ˢ Icc (0 : ℝ) 1 ⊆ P.source ∧
                (∀ z s, s ∈ Icc (0 : ℝ) 1 → Θ (z, s) = P (z, s)) ∧
                P '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆
                  nk.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) := by
  classical
  let eta₁ := Classical.choose (exists_spatial_neck_level_graph_tolerance.{u})
  let eta₂ := Classical.choose (exists_spatial_neck_finite_frontier_step_tolerance.{u, v})
  have heta₁ : 0 < eta₁ :=
    (Classical.choose_spec (exists_spatial_neck_level_graph_tolerance.{u})).1
  have heta₂ : 0 < eta₂ :=
    (Classical.choose_spec (exists_spatial_neck_finite_frontier_step_tolerance.{u, v})).1
  refine ⟨min eta₁ (min eta₂ (1 / 156000)),
    lt_min heta₁ (lt_min heta₂ (by norm_num)), ?_⟩
  intro eps heps M _ _ _ _ _ _ _ D S C1 C2 t W hW hreg hconn ι _ point neck level
    hlevel hpair hfront anchor ha hcanonical hgap hcompact
  let _ : Fintype ι := Fintype.ofFinite ι
  let sphere : ι → RecordedNeckSphere (S.base.metric t) eps := fun i =>
    RecordedNeckSphere.mk (point i) (neck i) (level i) (hlevel i)
      (Diffeomorph.refl I2 (Sphere 2) ∞)
  let W₀ : NeckFrontierState (S.base.metric t) eps ι :=
    NeckFrontierState.mk W hW ⟨anchor, ha⟩ hreg Finset.univ sphere
      (by
        change frontier W = ⋃ i ∈ Finset.univ, range (fun q => (neck i).map (q, level i))
        simpa only [Finset.mem_univ, iUnion_true] using hfront)
      (fun i _ j _ hij => hpair hij)
  have hrec : eps ≤ 1 / 156000 :=
    heps.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨seq, hseq0, hmono, hanti, _, hsteps, N, hN⟩ :=
    canonical_frontier_process S eps C1 C2 t ι W₀ hconn
      (heps.trans (min_le_left _ _))
      (heps.trans ((min_le_right _ _).trans (min_le_left _ _)))
      (hrec.trans (by norm_num)) anchor ha hcanonical hgap
  obtain ⟨i, _, Θ, hsm, hinj, hproper, hembed, hinter, hbase, hdiverge, hfirst⟩ :=
    NeckFrontierState.exists_proper_end_of_process (S.base.metric t) eps ι W₀ hrec hcompact
      seq hseq0 hmono hanti hsteps N hN
  exact ⟨i, Θ, hsm, hinj, hproper, hembed, hinter, hbase, hdiverge, hfirst⟩

theorem exists_spatial_neck_saved_end_decomposition_of_canonical_witnesses_tolerance :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ eps : ℝ, eps ≤ eta →
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M] [PreconnectedSpace M] [NoncompactSpace M]
          [SigmaCompactSpace M] (D : RealTimeInterval)
          (S : SolutionOn (I := I3) (M := M) D) (C1 C2 t : ℝ) (W : Set M),
          IsCompact W → closure (interior W) = W → IsPreconnected (interior W) →
          ∀ (ι : Type v) [Finite ι] (point : ι → M) (neck : ∀ i, SpatialNeck (S.base.metric t) eps (point i))
          (level : ι → ℝ), (∀ i, |level i| ≤ 4) →
          Pairwise (fun i j => Disjoint (range (fun q => (neck i).map (q, level i)))
            (range (fun q => (neck j).map (q, level j)))) →
          frontier W = ⋃ i, range (fun q => (neck i).map (q, level i)) →
          ∀ anchor ∈ W,
          (∀ x : M, x ∉ interior W → Nonempty (CanonicalWitness S eps C1 C2 x t)) →
          (∀ x : M, x ∉ interior W → C2 * S.scalar t anchor < S.scalar t x) →
          (∀ B : ℝ, IsCompact {x : M | S.scalar t x ≤ B}) →
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
                T ≤ s → B < S.scalar t (Θ i (z, s.val))) ∧
              ∃ (p : M) (nk : SpatialNeck (S.base.metric t) eps p)
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
  intro eps heps M _ _ _ _ _ _ _ D S C1 C2 t W hW hreg hconn ι _ point neck level
    hlevel hpair hfront anchor ha hcanonical hgap hcompact
  let _ : Fintype ι := Fintype.ofFinite ι
  let sphere : ι → RecordedNeckSphere (S.base.metric t) eps := fun i =>
    RecordedNeckSphere.mk (point i) (neck i) (level i) (hlevel i)
      (Diffeomorph.refl I2 (Sphere 2) ∞)
  let W₀ : NeckFrontierState (S.base.metric t) eps ι :=
    NeckFrontierState.mk W hW ⟨anchor, ha⟩ hreg Finset.univ sphere
      (by
        change frontier W = ⋃ i ∈ Finset.univ, range (fun q => (neck i).map (q, level i))
        simpa only [Finset.mem_univ, iUnion_true] using hfront)
      (fun i _ j _ hij => hpair hij)
  have hrec : eps ≤ 1 / 156000 :=
    heps.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨seq, selected, hzero, hmono, hanti, _, hselected, hsteps, N, hne, hstable, hN, hfair⟩ :=
    canonical_fair_frontier_process S eps C1 C2 t ι W₀ hconn
      (heps.trans (min_le_left _ _))
      (heps.trans ((min_le_right _ _).trans (min_le_left _ _)))
      (hrec.trans (by norm_num)) anchor ha hcanonical hgap
  obtain ⟨T, hsub, halive, hspheres, hconnect, Θ, hends, hdisjoint, hfull, _⟩ :=
    NeckFrontierState.exists_saved_end_family_of_fair_process (S.base.metric t) eps ι W₀
      hrec hcompact seq selected hzero hmono hanti hselected hsteps N hne hstable hN hfair
  let Ind := {i // i ∈ (NeckFrontierState.alive T)}
  let _ : Fintype Ind := (NeckFrontierState.alive T).fintypeCoeSort
  let e : Ind ≃ Fin (Fintype.card Ind) := Fintype.equivFin Ind
  let ends (i : Fin (Fintype.card Ind)) := Θ (e.symm i)
  have hneI : Nonempty Ind := (NeckFrontierState.alive_nonempty (S.base.metric t) eps ι T).to_subtype
  let _ : Nonempty Ind := hneI
  have hbase (i : Ind) : range (fun z => Θ i (z, 0)) = range (RecordedNeckSphere.map (S.base.metric t) eps (NeckFrontierState.sphere T i.val)) := by
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
    have hbaseS : range (fun z => Θ (e.symm i) (z, 0)) = range (RecordedNeckSphere.map (S.base.metric t) eps (NeckFrontierState.sphere W₀ (e.symm i).val)) := by
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
      rw [show range (fun z => ends i (z, 0)) = range (RecordedNeckSphere.map (S.base.metric t) eps (NeckFrontierState.sphere T (e.symm i).val)) from
        hbase (e.symm i)] at hxi
      exact mem_iUnion₂.mpr ⟨(e.symm i).val, (e.symm i).property, hxi⟩
  · rw [hindices]
    exact hfull

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
