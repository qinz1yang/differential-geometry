/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Covering.EmbeddedProjection
import DifferentialGeometry.Topology.PiecewiseLinear.BallComplement
import DifferentialGeometry.Topology.PiecewiseLinear.BranchBoundarySweep
import DifferentialGeometry.Topology.PiecewiseLinear.Pasting
import DifferentialGeometry.Topology.PiecewiseLinear.SingularCrossingLocality
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BranchInjection
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CutAndPaste
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.InnermostCleanDisk

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem eventually_eq_inter_fiber_comp_openPartialHomeomorph {X α : Type*} [TopologicalSpace X]
    {d : ℕ} (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin d))) {f g : α → X} (P : Set α)
    {y : X} (hy : y ∈ e.source) (hfiber : ∀ᶠ z in 𝓝 y, P ∩ f ⁻¹' {z} = P ∩ g ⁻¹' {z}) :
    ∀ᶠ z in 𝓝 (e y), (P ∩ f ⁻¹' e.source) ∩ (e ∘ f) ⁻¹' {z} =
      (P ∩ g ⁻¹' e.source) ∩ (e ∘ g) ⁻¹' {z} := by
  have hback : ∀ᶠ z in 𝓝 (e y), P ∩ f ⁻¹' {e.symm z} = P ∩ g ⁻¹' {e.symm z} :=
    (e.continuousAt_symm (e.map_source hy))
      (show ∀ᶠ z in 𝓝 (e.symm (e y)), P ∩ f ⁻¹' {z} = P ∩ g ⁻¹' {z} from by rwa [e.left_inv hy])
  filter_upwards [e.open_target.mem_nhds (e.map_source hy), hback] with z hz heq
  have hiff : ∀ u : α → X, ∀ x : α,
      x ∈ (P ∩ u ⁻¹' e.source) ∩ (e ∘ u) ⁻¹' {z} ↔ x ∈ P ∩ u ⁻¹' {e.symm z} := by
    intro u x
    constructor
    · rintro ⟨⟨hxP, hxu⟩, hxz⟩
      have hxz' : e (u x) = z := hxz
      exact ⟨hxP, show u x = e.symm z by rw [← hxz', e.left_inv hxu]⟩
    · rintro ⟨hxP, hxu⟩
      have hxu' : u x = e.symm z := hxu
      exact ⟨⟨hxP, show u x ∈ e.source by rw [hxu']; exact e.map_target hz⟩,
        show e (u x) = z by rw [hxu', e.right_inv hz]⟩
  ext x
  rw [hiff f x, hiff g x]
  exact Set.ext_iff.mp heq x

namespace NormalSingularCellData

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B : Set M}

def IsNestedDiskReplacementCell (hD : NormalSingularCellData D BdM B)
    (c : hD.singularSet.Branch) (G : SingularTwoCell M) : Prop :=
  ∃ J T Q E : Set (EuclideanSpace ℝ (Fin 2)),
  ∃ k : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
    ¬hD.singularSet.IsBoundaryBranch c ∧
    IsPLSphere 1 J ∧ IsPLSphere 1 T ∧ Disjoint J T ∧
    hD.branchPreimage c = J ∪ T ∧
    IsPLBall 2 Q ∧ frontier Q = J ∧
    doublePointPreimage D D.domain ∩ Q = J ∧ InjOn (⇑D) Q ∧
    IsPLBall 2 E ∧ E ⊆ interior D.domain ∧ frontier E = T ∧ Q ⊆ interior E ∧
    IsPLHomeomorphOn k E Q ∧ k '' T = J ∧ EqOn (⇑D) (⇑D ∘ k) T ∧
    G.domain = D.domain ∧
    EqOn (⇑G) (⇑D) (D.domain \ E) ∧
    ⇑G '' G.domain ⊆ ⇑D '' D.domain ∧
    Set.range G.boundary = Set.range D.boundary ∧
    ⇑G '' G.domain ∩ BdM = Set.range G.boundary ∧
    Set.range G.boundary ⊆ B ∧
    (∀ x ∈ G.domain, ∃ W ∈ 𝓝[G.domain] x, InjOn (⇑G) W) ∧
    (∀ y, (G.domain ∩ ⇑G ⁻¹' {y}).encard ≤ 2) ∧
    doublePointSet (⇑G) G.domain = doublePointSet (⇑D) ((D.domain \ E) ∪ Q) ∧
    doublePointSet (⇑G) G.domain ⊆ doublePointSet (⇑D) D.domain ∧
    Disjoint (doublePointSet (⇑G) G.domain) (hD.singularSet.branchCarrier c) ∧
    Nonempty (NormalSingularCellData G BdM B)

open Classical in
theorem exists_isNestedDiskReplacementCell [T2Space M] (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} (hc : ¬hD.singularSet.IsBoundaryBranch c)
    {J T Q E : Set (EuclideanSpace ℝ (Fin 2))}
    {k : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hJ : IsPLSphere 1 J) (hT : IsPLSphere 1 T) (hJT : Disjoint J T)
    (hpre : hD.branchPreimage c = J ∪ T)
    (hQ : IsPLBall 2 Q) (hfrontQ : frontier Q = J)
    (hclean : doublePointPreimage (⇑D) D.domain ∩ Q = J) (hinj : InjOn (⇑D) Q)
    (hE : IsPLBall 2 E) (hfrontE : frontier E = T)
    (hk : IsPLHomeomorphOn k E Q) (hkT : k '' T = J) (hkcompat : EqOn (⇑D) (⇑D ∘ k) T)
    (hnested : Q ⊆ interior E) :
    ∃ G : SingularTwoCell M, hD.IsNestedDiskReplacementCell c G := by
  classical
  have hDclosed : IsClosed D.domain := D.isPLBall_domain.isPolyhedron.isCompact.isClosed
  have hQclosed : IsClosed Q := hQ.isPolyhedron.isCompact.isClosed
  have hEclosed : IsClosed E := hE.isPolyhedron.isCompact.isClosed
  have hQE : Q ⊆ E := hnested.trans interior_subset
  have hTE : T ⊆ E := by
    rw [← hfrontE]
    exact hEclosed.frontier_subset
  have hTpre : T ⊆ hD.branchPreimage c := by
    rw [hpre]
    exact subset_union_right
  have hJpre : J ⊆ hD.branchPreimage c := by
    rw [hpre]
    exact subset_union_left
  have hEint : E ⊆ interior D.domain := by
    apply isPLBall_subset_interior_of_frontier_subset_interior hE D.isPLBall_domain
    rw [hfrontE]
    exact hTpre.trans (hD.branchPreimage_subset_interior_of_not_boundaryBranch hc)
  have hED : E ⊆ D.domain := hEint.trans interior_subset
  have hQD : Q ⊆ D.domain := hQE.trans hED
  have hpreDouble : hD.branchPreimage c ⊆ doublePointPreimage (⇑D) D.domain :=
    hD.branchPreimage_subset_doublePointPreimage c
  have hTQ : Disjoint T Q :=
    Set.disjoint_left.mpr fun x hxT hxQ =>
      Set.disjoint_left.mp hJT (hclean.subset ⟨hpreDouble (hTpre hxT), hxQ⟩) hxT
  have hJQ : J ⊆ Q := by
    rw [← hfrontQ]
    exact hQclosed.frontier_subset
  have hkmaps : MapsTo k E Q := hk.bijOn.mapsTo
  have hkinj : InjOn k E := hk.bijOn.injOn
  obtain ⟨r, hrE, hrout⟩ : ∃ r : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
      (∀ x ∈ E, r x = k x) ∧ (∀ x, x ∉ E → r x = x) :=
    ⟨E.piecewise k id, fun x hx => Set.piecewise_eq_of_mem _ _ _ hx,
      fun x hx => Set.piecewise_eq_of_notMem _ _ _ hx⟩
  obtain ⟨G, hGdom, hGr⟩ : ∃ G : SingularTwoCell M, G.domain = D.domain ∧
      ∀ x, ⇑G x = ⇑D (r x) := by
    have hseam : E ∩ (D.domain \ interior E) = T := by
      rw [← hfrontE, hEclosed.frontier_eq]
      exact Subset.antisymm (fun x hx => ⟨hx.1, hx.2.2⟩) fun x hx => ⟨hx.1, hED hx.1, hx.2⟩
    have hcover : E ∪ (D.domain \ interior E) = D.domain := by
      refine Subset.antisymm (union_subset hED Set.sdiff_subset) fun x hx => ?_
      by_cases hxi : x ∈ interior E
      · exact Or.inl (interior_subset hxi)
      · exact Or.inr ⟨hx, hxi⟩
    have h₁ : IsPLOn 2 3 (⇑D ∘ k) E :=
      isPLOn_comp_isPiecewiseAffineOn_of_mapsTo D.isPLOn hk.isPiecewiseAffineOn
        (hkmaps.mono_right hQD)
    have h₂ : IsPLOn 2 3 (⇑D) (D.domain \ interior E) :=
      D.isPLOn.mono_of_isPolyhedron
        (D.isPLBall_domain.isPolyhedron.sdiff_interior_of_isPLBall hE) Set.sdiff_subset
    have h₃ : EqOn (⇑D ∘ k) (⇑D) (E ∩ (D.domain \ interior E)) := by
      rw [hseam]
      exact fun x hx => (hkcompat hx).symm
    have hPL : IsPLOn 2 3 (E.piecewise (⇑D ∘ k) (⇑D)) D.domain := by
      have h := IsPLOn.piecewise_of_isClosed h₁ h₂ hEclosed (hDclosed.sdiff isOpen_interior) h₃
      rwa [hcover] at h
    refine ⟨⟨D.domain, D.isPLBall_domain, E.piecewise (⇑D ∘ k) (⇑D), hPL⟩, rfl, fun x => ?_⟩
    by_cases hx : x ∈ E
    · change E.piecewise (⇑D ∘ k) (⇑D) x = ⇑D (r x)
      rw [Set.piecewise_eq_of_mem _ _ _ hx, hrE x hx]
      rfl
    · change E.piecewise (⇑D ∘ k) (⇑D) x = ⇑D (r x)
      rw [Set.piecewise_eq_of_notMem _ _ _ hx, hrout x hx]
  have hGcont : ContinuousOn (⇑G) D.domain := by
    rw [← hGdom]
    exact G.continuousOn
  have hrmaps : MapsTo r D.domain D.domain := by
    intro x hx
    by_cases hxE : x ∈ E
    · rw [hrE x hxE]
      exact hQD (hkmaps hxE)
    · rw [hrout x hxE]
      exact hx
  have hrinj : InjOn r D.domain := by
    intro x hx y hy hxy
    by_cases hxE : x ∈ E <;> by_cases hyE : y ∈ E
    · rw [hrE x hxE, hrE y hyE] at hxy
      exact hkinj hxE hyE hxy
    · rw [hrE x hxE, hrout y hyE] at hxy
      exact absurd (hQE (hxy ▸ hkmaps hxE)) hyE
    · rw [hrout x hxE, hrE y hyE] at hxy
      exact absurd (hQE (hxy ▸ hkmaps hyE)) hxE
    · rwa [hrout x hxE, hrout y hyE] at hxy
  have hrimage : r '' D.domain = (D.domain \ E) ∪ Q := by
    refine Subset.antisymm ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      by_cases hxE : x ∈ E
      · refine Or.inr ?_
        rw [hrE x hxE]
        exact hkmaps hxE
      · refine Or.inl ?_
        rw [hrout x hxE]
        exact ⟨hx, hxE⟩
    · rintro z (⟨hzD, hzE⟩ | hzQ)
      · exact ⟨z, hzD, hrout z hzE⟩
      · obtain ⟨w, hwE, hwz⟩ := hk.bijOn.surjOn hzQ
        exact ⟨w, hED hwE, (hrE w hwE).trans hwz⟩
  have hPD : (D.domain \ E) ∪ Q ⊆ D.domain := union_subset Set.sdiff_subset hQD
  have hdps : doublePointSet (⇑G) G.domain = doublePointSet (⇑D) ((D.domain \ E) ∪ Q) := by
    rw [doublePointSet_eq_image_of_pullback (D := D) (G := G) (pullback := r)
      (hGdom ▸ hrinj) (fun x _ => (hGr x).symm), hGdom, hrimage]
  have hdsub : doublePointSet (⇑G) G.domain ⊆ doublePointSet (⇑D) D.domain := by
    rw [hdps]
    rintro z ⟨u, hu, v, hv, huv, huz, hvz⟩
    exact ⟨u, hPD hu, v, hPD hv, huv, huz, hvz⟩
  have hfibreOut : ∀ y ∈ doublePointSet (⇑G) G.domain,
      D.domain ∩ ⇑D ⁻¹' {y} ⊆ D.domain \ E := by
    intro y hy
    rw [hdps] at hy
    obtain ⟨u, hu, v, hv, huv, huy, hvy⟩ := hy
    have hnotQ : ∀ w ∈ (D.domain \ E) ∪ Q, ∀ w' ∈ (D.domain \ E) ∪ Q, w ≠ w' →
        ⇑D w = y → ⇑D w' = y → w ∉ Q := by
      intro w hw w' hw' hww' hwy hw'y hwQ
      have hwJ : w ∈ J :=
        hclean.subset
          ⟨⟨hPD hw, ⟨w, hPD hw, w', hPD hw', hww', rfl, hw'y.trans hwy.symm⟩⟩, hwQ⟩
      have hwcar : ⇑D w ∈ hD.singularSet.branchCarrier c := (hJpre hwJ).2
      have hw'car : ⇑D w' ∈ hD.singularSet.branchCarrier c := by
        rw [hw'y, ← hwy]
        exact hwcar
      have hw'pre : w' ∈ hD.branchPreimage c := ⟨hPD hw', hw'car⟩
      rw [hpre] at hw'pre
      rcases hw'pre with hw'J | hw'T
      · exact hww' (hinj hwQ (hJQ hw'J) (hwy.trans hw'y.symm))
      · rcases hw' with ⟨-, hw'E⟩ | hw'Q
        · exact hw'E (hTE hw'T)
        · exact Set.disjoint_left.mp hTQ hw'T hw'Q
    have huD : u ∈ D.domain \ E := hu.resolve_right (hnotQ u hu v hv huv huy hvy)
    have hvD : v ∈ D.domain \ E := hv.resolve_right (hnotQ v hv u hu (Ne.symm huv) hvy huy)
    have hfib : D.domain ∩ ⇑D ⁻¹' {y} = {u, v} :=
      fiber_eq_pair_of_encard_le_two (⇑D) D.domain huD.1 hvD.1 huv huy hvy (hD.fiber_le_two y)
    rw [hfib]
    rintro w (rfl | rfl)
    · exact huD
    · exact hvD
  have hfibreEq : ∀ y ∈ doublePointSet (⇑G) G.domain,
      ∀ᶠ z in 𝓝 y, D.domain ∩ ⇑D ⁻¹' {z} = D.domain ∩ ⇑G ⁻¹' {z} := by
    intro y hy
    obtain ⟨a, b, hab, hfib⟩ := hD.exists_fiber_eq_pair (hdsub hy)
    have hsub := hfibreOut y hy
    rw [hfib] at hsub
    have ha : a ∈ D.domain \ E := hsub (Or.inl rfl)
    have hb : b ∈ D.domain \ E := hsub (Or.inr rfl)
    have hnhdsa : D.domain \ E ∈ 𝓝[D.domain] a :=
      Filter.inter_mem self_mem_nhdsWithin
        (mem_nhdsWithin_of_mem_nhds (hEclosed.isOpen_compl.mem_nhds ha.2))
    have hnhdsb : D.domain \ E ∈ 𝓝[D.domain] b :=
      Filter.inter_mem self_mem_nhdsWithin
        (mem_nhdsWithin_of_mem_nhds (hEclosed.isOpen_compl.mem_nhds hb.2))
    filter_upwards [eventually_preimage_subset_union_of_fiber_eq_pair (⇑D)
      D.isPLBall_domain.isPolyhedron.isCompact D.continuousOn hfib hnhdsa hnhdsb] with z hz
    have hzout : D.domain ∩ ⇑D ⁻¹' {z} ⊆ D.domain \ E := fun w hw => (hz hw).elim id id
    refine Subset.antisymm (fun w hw => ⟨hw.1, ?_⟩) fun w hw => ⟨hw.1, ?_⟩
    · change ⇑G w = z
      rw [hGr w, hrout w (hzout hw).2]
      exact hw.2
    · have hwE : w ∉ E := by
        intro hwE
        have hkw : k w ∈ D.domain ∩ ⇑D ⁻¹' {z} := by
          refine ⟨hQD (hkmaps hwE), ?_⟩
          have hww : ⇑G w = z := hw.2
          rw [hGr w, hrE w hwE] at hww
          exact hww
        exact (hzout hkw).2 (hQE (hkmaps hwE))
      change ⇑D w = z
      have hww : ⇑G w = z := hw.2
      rwa [hGr w, hrout w hwE] at hww
  have hinjtransfer : ∀ U : Set (EuclideanSpace ℝ (Fin 2)), U ⊆ D.domain → InjOn (⇑D) U →
      InjOn (⇑G) U := by
    intro U hUD hU
    have hmixed : ∀ x ∈ U, ∀ y ∈ U, x ∉ E → y ∈ E → ⇑G x ≠ ⇑G y := by
      intro x hx y hy hxE hyE hxy
      rw [hGr x, hrout x hxE, hGr y, hrE y hyE] at hxy
      have hne : x ≠ k y := fun h => hxE (hQE (h ▸ hkmaps hyE))
      have hky : k y ∈ J :=
        hclean.subset ⟨⟨hQD (hkmaps hyE),
          ⟨x, hUD hx, k y, hQD (hkmaps hyE), hne, hxy, rfl⟩⟩, hkmaps hyE⟩
      obtain ⟨t, htT, htk⟩ : ∃ t ∈ T, k t = k y := by
        rw [← hkT] at hky
        exact hky
      have hyT : y ∈ T := (hkinj (hTE htT) hyE htk) ▸ htT
      exact hxE (hTE ((hU hx hy (hxy.trans (hkcompat hyT).symm)) ▸ hyT))
    intro x hx y hy hxy
    by_cases hxE : x ∈ E <;> by_cases hyE : y ∈ E
    · rw [hGr x, hrE x hxE, hGr y, hrE y hyE] at hxy
      exact hkinj hxE hyE (hinj (hkmaps hxE) (hkmaps hyE) hxy)
    · exact absurd hxy.symm (hmixed y hy x hx hyE hxE)
    · exact absurd hxy (hmixed x hx y hy hxE hyE)
    · rw [hGr x, hrout x hxE, hGr y, hrout y hyE] at hxy
      exact hU hx hy hxy
  have hloc : ∀ x ∈ G.domain, ∃ W ∈ 𝓝[G.domain] x, InjOn (⇑G) W := by
    rw [hGdom]
    intro x hx
    obtain ⟨U, hU, hUinj⟩ := hD.locallyInjective x hx
    exact ⟨U ∩ D.domain, Filter.inter_mem hU self_mem_nhdsWithin,
      hinjtransfer _ inter_subset_right (hUinj.mono inter_subset_left)⟩
  have hfibre : ∀ y : M, (G.domain ∩ ⇑G ⁻¹' {y}).encard ≤ 2 := by
    simp only [hGdom]
    intro y
    have himg : r '' (D.domain ∩ ⇑G ⁻¹' {y}) ⊆ D.domain ∩ ⇑D ⁻¹' {y} := by
      rintro _ ⟨x, ⟨hxD, hxy⟩, rfl⟩
      refine ⟨hrmaps hxD, ?_⟩
      change ⇑D (r x) = y
      rw [← hGr x]
      exact hxy
    calc (D.domain ∩ ⇑G ⁻¹' {y}).encard
        = (r '' (D.domain ∩ ⇑G ⁻¹' {y})).encard :=
          (Set.InjOn.encard_image (hrinj.mono inter_subset_left)).symm
      _ ≤ (D.domain ∩ ⇑D ⁻¹' {y}).encard := Set.encard_mono himg
      _ ≤ 2 := hD.fiber_le_two y
  have hfrontsub : frontier D.domain ⊆ D.domain \ E := by
    intro x hx
    have hxD : x ∈ D.domain := D.frontier_subset_domain hx
    exact ⟨hxD, fun hxE => (mem_interior_iff_notMem_frontier hxD).mp (hEint hxE) hx⟩
  have hoff : EqOn (⇑G) (⇑D) (D.domain \ E) := fun x hx => by
    rw [hGr x, hrout x hx.2]
  have hrangeim : ∀ H : SingularTwoCell M, Set.range H.boundary = ⇑H '' frontier H.domain := by
    intro H
    refine Subset.antisymm ?_ ?_
    · rintro _ ⟨x, rfl⟩
      exact ⟨x, x.property, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hrange : Set.range G.boundary = Set.range D.boundary := by
    rw [hrangeim G, hrangeim D, hGdom]
    exact Set.image_congr fun x hx => hoff (hfrontsub hx)
  have himage : ⇑G '' G.domain ⊆ ⇑D '' D.domain := by
    rw [hGdom]
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨r x, hrmaps hx, (hGr x).symm⟩
  have hrangeB : Set.range G.boundary ⊆ B := by
    rw [hrange]
    exact hD.boundary_image_subset
  have hinterBd : ⇑G '' G.domain ∩ BdM = Set.range G.boundary := by
    refine Subset.antisymm (fun y hy => ?_) fun y hy => ?_
    · rw [hrange, ← hD.image_inter_boundary]
      exact ⟨himage hy.1, hy.2⟩
    · have hyD : y ∈ ⇑D '' D.domain ∩ BdM := by
        rw [hD.image_inter_boundary, ← hrange]
        exact hy
      refine ⟨?_, hyD.2⟩
      rw [hrangeim G] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact ⟨x, G.frontier_subset_domain hx, rfl⟩
  have hmiss : Disjoint (doublePointSet (⇑G) G.domain) (hD.singularSet.branchCarrier c) := by
    refine Set.disjoint_left.mpr fun y hy hycar => ?_
    obtain ⟨u, hu, -, -, -, huy, -⟩ := hdsub hy
    have hucar : ⇑D u ∈ hD.singularSet.branchCarrier c := by
      rw [huy]
      exact hycar
    have hupre : u ∈ hD.branchPreimage c := ⟨hu, hucar⟩
    rw [hpre] at hupre
    exact (hfibreOut y hy ⟨hu, huy⟩).2
      (hupre.elim (fun h => hQE (hJQ h)) fun h => hTE h)
  have hcross : ∀ y ∈ doublePointSet (⇑G) G.domain,
      ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e.source ∧
        HasPLNormalDoubleCrossingAt (⇑e ∘ ⇑G) (G.domain ∩ ⇑G ⁻¹' e.source)
          (⇑e '' (e.source ∩ BdM)) (e y) := by
    intro y hy
    obtain ⟨e, he, hye, hcr⟩ := hD.crossing y (hdsub hy)
    refine ⟨e, he, hye, ?_⟩
    rw [hGdom]
    exact HasPLNormalDoubleCrossingAt.of_eventually_eq_fiber
      (e.continuousOn.comp (hGcont.mono inter_subset_left) fun _ hx => hx.2)
      (eventually_eq_inter_fiber_comp_openPartialHomeomorph e D.domain hye (hfibreEq y hy)) hcr
  have hcompact : IsCompact (doublePointSet (⇑G) G.domain) :=
    isCompact_doublePointSet_of_isLocallyInjective
      G.isPLBall_domain.isPolyhedron.isCompact G.continuousOn
      (Covering.isLocallyInjective_domRestrict_iff.mpr hloc)
  have hopenin : ∀ y ∈ doublePointSet (⇑G) G.domain,
      doublePointSet (⇑G) G.domain ∈ 𝓝[doublePointSet (⇑D) D.domain] y := by
    rw [hGdom]
    refine doublePointSet_mem_nhdsWithin_of_pullback (O := (D.domain \ E) ∪ Q)
      (S := hD.singularSet.branchCarrier c) D.isPLBall_domain.isPolyhedron.isCompact
      D.continuousOn hD.fiber_le_two hrmaps (fun x _ => (hGr x).symm) hrinj ?_ ?_ ?_
      (hD.singularSet.isClosed_branchCarrier c) (hGdom ▸ hmiss)
    · intro x hx
      rw [← hrimage]
      exact ⟨x, hx, rfl⟩
    · rintro x (⟨hxD, hxE⟩ | hxQ) hxcar
      · exact Filter.mem_of_superset
          (Filter.inter_mem self_mem_nhdsWithin
            (mem_nhdsWithin_of_mem_nhds (hEclosed.isOpen_compl.mem_nhds hxE)))
          Set.subset_union_left
      · have hxint : x ∈ interior Q := by
          refine (mem_interior_iff_notMem_frontier hxQ).mpr ?_
          rw [hfrontQ]
          exact fun hxJ => hxcar (hJpre hxJ).2
        exact Filter.mem_of_superset
          (mem_nhdsWithin_of_mem_nhds (isOpen_interior.mem_nhds hxint))
          (interior_subset.trans Set.subset_union_right)
    · intro x hx _
      rw [← hrimage] at hx
      exact hx
  have hnormal : Nonempty (NormalSingularCellData G BdM B) :=
    ⟨{ locallyInjective := hloc
       fiber_le_two := hfibre
       boundary_image_subset := hrangeB
       image_inter_boundary := hinterBd
       singularSet := Classical.choice
         (hD.singularSet.restrict_to_clopen_doublePointSet hdsub hcompact hopenin)
       crossing := hcross }⟩
  exact ⟨G, J, T, Q, E, k, hc, hJ, hT, hJT, hpre, hQ, hfrontQ, hclean, hinj, hE, hEint,
    hfrontE, hnested, hk, hkT, hkcompat, hGdom, hoff, himage, hrange, hinterBd, hrangeB,
    hloc, hfibre, hdps, hdsub, hmiss, hnormal⟩

theorem nonempty_normalSingularCellData_of_isNestedDiskReplacementCell
    (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch} {G : SingularTwoCell M}
    (hG : hD.IsNestedDiskReplacementCell c G) :
    Nonempty (NormalSingularCellData G BdM B) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -,
    -, -, hN⟩ := hG
  exact hN

theorem domain_eq_of_isNestedDiskReplacementCell (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} {G : SingularTwoCell M}
    (hG : hD.IsNestedDiskReplacementCell c G) : G.domain = D.domain := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -,
    -, hdom, -⟩ := hG
  exact hdom

theorem image_subset_of_isNestedDiskReplacementCell (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} {G : SingularTwoCell M}
    (hG : hD.IsNestedDiskReplacementCell c G) : ⇑G '' G.domain ⊆ ⇑D '' D.domain := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -,
    -, -, -, him, -⟩ := hG
  exact him

theorem range_boundary_eq_of_isNestedDiskReplacementCell (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} {G : SingularTwoCell M}
    (hG : hD.IsNestedDiskReplacementCell c G) :
    Set.range G.boundary = Set.range D.boundary := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, hrange, -⟩ := hG
  exact hrange

theorem doublePointSet_subset_of_isNestedDiskReplacementCell
    (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch} {G : SingularTwoCell M}
    (hG : hD.IsNestedDiskReplacementCell c G) :
    doublePointSet (⇑G) G.domain ⊆ doublePointSet (⇑D) D.domain := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -,
    hsub, -⟩ := hG
  exact hsub

theorem disjoint_doublePointSet_branchCarrier_of_isNestedDiskReplacementCell
    (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch} {G : SingularTwoCell M}
    (hG : hD.IsNestedDiskReplacementCell c G) :
    Disjoint (doublePointSet (⇑G) G.domain) (hD.singularSet.branchCarrier c) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -,
    -, hmiss, -⟩ := hG
  exact hmiss

theorem exists_isPLBall_eqOn_of_isNestedDiskReplacementCell
    (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch} {G : SingularTwoCell M}
    (hG : hD.IsNestedDiskReplacementCell c G) :
    ∃ E : Set (EuclideanSpace ℝ (Fin 2)), IsPLBall 2 E ∧ E ⊆ interior D.domain ∧
      EqOn (⇑G) (⇑D) (D.domain \ E) := by
  obtain ⟨-, -, -, E, -, -, -, -, -, -,
    -, -, -, -, hE, hEint, -, -, -, -,
    -, -, hoff, -⟩ := hG
  exact ⟨E, hE, hEint, hoff⟩

theorem not_isNestedDiskReplacementCell_self (hD : NormalSingularCellData D BdM B)
    (c : hD.singularSet.Branch) : ¬ hD.IsNestedDiskReplacementCell c D := by
  intro hG
  obtain ⟨z, hz⟩ := (hD.singularSet.branchCarrier_isConnected c).nonempty
  exact Set.disjoint_right.mp
    (hD.disjoint_doublePointSet_branchCarrier_of_isNestedDiskReplacementCell hG) hz
    (hD.singularSet.branchCarrier_subset_doublePointSet c hz)

end NormalSingularCellData

end DifferentialGeometry.Topology.PiecewiseLinear
