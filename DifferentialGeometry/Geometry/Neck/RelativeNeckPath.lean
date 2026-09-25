import DifferentialGeometry.Geometry.Neck.SpatialFiniteFrontier
import DifferentialGeometry.Geometry.Neck.SpatialFrontierOrientation
import DifferentialGeometry.Geometry.Neck.SpatialFreshBand
import DifferentialGeometry.Topology.Manifold.CylinderCollar.SlabGluing

noncomputable section

open Set Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u v

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]
  (g : SmoothRiemannianMetric I3 M) {eps : ℝ}
  {ι : Type v} [Finite ι] (point : ι → M) (savedNeck : ∀ i, SpatialNeck g eps (point i))
  (savedLevel : ι → ℝ) (W : Set M) (lower : Sphere 2 → M)

private structure RelativeNeckPath where
  map : PartialDiffeomorph IC I3 Cylinder M ∞
  source : univ ×ˢ Icc (0 : ℝ) 1 ⊆ map.source
  lower_eq : ∀ q, map (q, 0) = lower q
  point : M
  neck : SpatialNeck g eps point
  level : ℝ
  bound : |level| ≤ 4
  upperParam : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2
  upper_eq : ∀ q, map (q, 1) = neck.map (upperParam q, level)
  inter_base : map '' (univ ×ˢ Icc (0 : ℝ) 1) ∩ W = range lower
  upper_outside : Disjoint (range (fun q : Sphere 2 => neck.map (q, level))) W
  regular : closure (interior (W ∪ map '' (univ ×ˢ Icc (0 : ℝ) 1))) =
    W ∪ map '' (univ ×ˢ Icc (0 : ℝ) 1)
  frontier : frontier (W ∪ map '' (univ ×ˢ Icc (0 : ℝ) 1)) =
    range (fun q : Sphere 2 => neck.map (q, level)) ∪
      ⋃ i, range (fun q : Sphere 2 => (savedNeck i).map (q, savedLevel i))

private def RelativeNeckPath.region
    (T : RelativeNeckPath g point savedNeck savedLevel W lower) : Set M :=
  W ∪ T.map '' (univ ×ˢ Icc (0 : ℝ) 1)

private theorem RelativeNeckPath.outward_graph
    (T : RelativeNeckPath g point savedNeck savedLevel W lower)
    (hlevel : ∀ i, |savedLevel i| ≤ 4)
    (hsaved : ∀ i, range (fun q : Sphere 2 => (savedNeck i).map (q, savedLevel i)) ⊆ W)
    (heps : eps ≤ Classical.choose (exists_spatial_neck_level_graph_tolerance.{u}))
    (hneck : Nonempty (SpatialNeck g eps (T.neck.map (T.neck.center, T.level)))) :
    ∃ (p : M) (nk : SpatialNeck g eps p) (f : Sphere 2 → ℝ)
      (κ : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2),
      ContMDiff I2 𝓘(ℝ) ∞ f ∧ (∀ q, |f q| < 1 / 10) ∧ f nk.center = 0 ∧
      (∀ q, nk.map (q, f q) = T.map (κ q, 1)) ∧
      _root_.frontier T.region = range (fun q => nk.map (q, f q)) ∪
        ⋃ i, range (fun q : Sphere 2 => (savedNeck i).map (q, savedLevel i)) ∧
      (∀ i, Disjoint (range (fun q => nk.map (q, f q)))
        (range (fun q : Sphere 2 => (savedNeck i).map (q, savedLevel i)))) ∧
      (∃ r > 0, ∀ t, 0 < t → t < r → nk.map (nk.center, t) ∉ T.region) := by
  let x := T.neck.map (T.neck.center, T.level)
  obtain ⟨nk₀⟩ := hneck
  obtain ⟨η, h, hh, hsmall, hzero, _, heq⟩ :=
    (Classical.choose_spec (exists_spatial_neck_level_graph_tolerance.{u})).2
      eps heps M g T.point x T.neck nk₀ T.neck.center nk₀.center T.level 0
      T.bound (by norm_num) nk₀.center_eq.symm
  simp only [sub_zero] at hsmall
  have hrange : range (fun q => nk₀.map (q, h q)) =
      range (fun q : Sphere 2 => T.neck.map (q, T.level)) := by
    ext y
    constructor
    · rintro ⟨q, hq⟩
      exact ⟨η q, (heq q).symm.trans hq⟩
    · rintro ⟨q, hq⟩
      refine ⟨η.symm q, (heq _).trans ?_⟩
      rw [η.apply_symm_apply]
      exact hq
  let S := ⋃ i, range (fun q : Sphere 2 => (savedNeck i).map (q, savedLevel i))
  have hfront : _root_.frontier T.region = range (fun q => nk₀.map (q, h q)) ∪ S := by
    rw [hrange]
    exact T.frontier
  have hsub : S ⊆ W := iUnion_subset hsaved
  have hdis : Disjoint (range (fun q => nk₀.map (q, h q))) S := by
    rw [hrange]
    exact T.upper_outside.mono_right hsub
  have hclosed : IsClosed S := by
    apply isClosed_iUnion_of_finite
    intro i
    have hlen : (4 : ℝ) < eps⁻¹ :=
      (lt_inv_comm₀ (by norm_num) (savedNeck i).eps_pos).mpr
        (by linarith [(savedNeck i).eps_small])
    exact (isCompact_range ((savedNeck i).map.contMDiffOn_toFun.continuousOn.comp_continuous
      (continuous_id.prodMk continuous_const) (fun q => (savedNeck i).domain
        ⟨mem_univ _, by constructor <;> linarith [(abs_le.mp (hlevel i)).1,
          (abs_le.mp (hlevel i)).2]⟩))).isClosed
  obtain ⟨nk, f, _, hf, hfsmall, hfzero, hphysical, hout⟩ :=
    nk₀.exists_outward_graph_orientation h hh hsmall hzero T.regular hclosed hfront hdis
  let κ := η.trans T.upperParam.symm
  have hmap (q : Sphere 2) : nk.map (q, f q) = T.map (κ q, 1) := by
    rw [hphysical, heq, T.upper_eq]
    exact congrArg (fun z => T.neck.map (z, T.level))
      (T.upperParam.apply_symm_apply (η q)).symm
  have hequal : (fun q => nk.map (q, f q)) = (fun q => nk₀.map (q, h q)) := funext hphysical
  refine ⟨x, nk, f, κ, hf, hfsmall, hfzero, hmap, ?_, ?_, hout⟩
  · rw [hequal]
    exact hfront
  · intro i
    rw [hequal, hrange]
    exact T.upper_outside.mono_right (hsaved i)


private def RelativeNeckPath.returned
    (T : RelativeNeckPath g point savedNeck savedLevel W lower) : Prop :=
  ∃ (i : ι) (ρ : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2)
    (R : PartialDiffeomorph IC I3 Cylinder M ∞),
    univ ×ˢ Icc (0 : ℝ) 1 ⊆ R.source ∧
    (∀ q, R (q, 0) = lower q) ∧
    (∀ q, R (q, 1) = (savedNeck i).map (ρ q, savedLevel i)) ∧
    T.region ⊆ W ∪ R '' (univ ×ˢ Icc (0 : ℝ) 1) ∧
    R '' (univ ×ˢ Icc (0 : ℝ) 1) ∩ W =
      range lower ∪ range (fun q : Sphere 2 => (savedNeck i).map (q, savedLevel i)) ∧
    closure (interior (W ∪ R '' (univ ×ˢ Icc (0 : ℝ) 1))) =
      W ∪ R '' (univ ×ˢ Icc (0 : ℝ) 1) ∧
    _root_.frontier (W ∪ R '' (univ ×ˢ Icc (0 : ℝ) 1)) =
      ⋃ j : {j // j ≠ i}, range (fun q : Sphere 2 => (savedNeck j.val).map (q, savedLevel j.val))

private theorem RelativeNeckPath.advance_or_return
    (T : RelativeNeckPath g point savedNeck savedLevel W lower)
    (hlevel : ∀ i, |savedLevel i| ≤ 4)
    (hsaved : ∀ i, range (fun q : Sphere 2 => (savedNeck i).map (q, savedLevel i)) ⊆ W)
    (hpair : Pairwise fun i j =>
      Disjoint (range (fun q : Sphere 2 => (savedNeck i).map (q, savedLevel i)))
        (range (fun q : Sphere 2 => (savedNeck j).map (q, savedLevel j))))
    (hlower : ∀ i, Disjoint (range lower)
      (range (fun q : Sphere 2 => (savedNeck i).map (q, savedLevel i))))
    (heps : eps ≤ Classical.choose (exists_spatial_neck_level_graph_tolerance.{u}))
    (hepsstep : eps ≤ Classical.choose (exists_spatial_neck_finite_frontier_step_tolerance.{u, v}))
    (hneck : Nonempty (SpatialNeck g eps (T.neck.map (T.neck.center, T.level)))) :
    T.returned ∨ ∃ U : RelativeNeckPath g point savedNeck savedLevel W lower,
      T.region ⊆ U.region ∧ ∃ (p : M) (nk : SpatialNeck g eps p),
        nk.map '' (univ ×ˢ Icc (1 : ℝ) 2) ⊆ U.region \ T.region := by
  classical
  obtain ⟨p, nk, f, κ, hf, hsmall, hzero, hmap, hfront, hdis, hout⟩ :=
    RelativeNeckPath.outward_graph g point savedNeck savedLevel W lower T hlevel hsaved heps hneck
  have hstep := (Classical.choose_spec (exists_spatial_neck_finite_frontier_step_tolerance.{u, v})).2
  have hupper : range (fun q : Sphere 2 => nk.map (q, f q)) =
      T.map '' (univ ×ˢ ({1} : Set ℝ)) := by
    ext y
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨(κ q, 1), ⟨mem_univ _, rfl⟩, (hmap q).symm⟩
    · rintro ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩
      have ht : t = 1 := ht
      subst t
      refine ⟨κ.symm q, ?_⟩
      change nk.map (κ.symm q, f (κ.symm q)) = T.map (q, 1)
      rw [hmap, κ.apply_symm_apply]
  have hupperT : T.map '' (univ ×ˢ ({1} : Set ℝ)) ⊆
      T.map '' (univ ×ˢ Icc (0 : ℝ) 1) := image_mono (by
    rintro ⟨q,t⟩ ⟨hq,ht⟩
    have ht : t = 1 := ht
    exact ⟨hq, ht ▸ (by norm_num : (1 : ℝ) ∈ Icc 0 1)⟩)
  have hupperW : Disjoint (range (fun q : Sphere 2 => nk.map (q, f q))) W := by
    rw [hupper]
    rw [disjoint_left]
    rintro y ⟨⟨q,t⟩,⟨_,ht⟩,rfl⟩ hy
    have ht : t = 1 := ht
    subst t
    exact disjoint_left.mp T.upper_outside
      ⟨T.upperParam q, (T.upper_eq q).symm⟩ hy
  rcases hstep eps hepsstep M g p nk ι point savedNeck savedLevel hlevel hpair f hf hsmall hzero
      T.region T.regular hfront hdis hout with hadvance | hreturn
  · right
    obtain ⟨A, hA, _, hA0, hA1, _, hinter, hregular, hnewfront, hfresh⟩ := hadvance
    have hmeet : T.map '' (univ ×ˢ Icc (0 : ℝ) 1) ∩
        A '' (univ ×ˢ Icc (0 : ℝ) 1) = T.map '' (univ ×ˢ ({1} : Set ℝ)) := by
      apply Subset.antisymm
      · intro y hy
        have hh := hinter ▸ (show y ∈ A '' (univ ×ˢ Icc (0 : ℝ) 1) ∩ T.region from
          ⟨hy.2, Or.inr hy.1⟩)
        exact hupper ▸ hh
      · intro y hy
        have hh := hinter.symm ▸ (hupper.symm ▸ hy)
        exact ⟨hupperT hy, hh.1⟩
    obtain ⟨R, hR, hRi, hR0, hR1, _, _⟩ :=
      DifferentialGeometry.Topology.Manifold.exists_unit_slab_concatenation T.map A κ
        T.source hA (fun q => (hA0 q).trans (hmap q)) hmeet
    have hregion : W ∪ R '' (univ ×ˢ Icc (0 : ℝ) 1) =
        T.region ∪ A '' (univ ×ˢ Icc (0 : ℝ) 1) := by rw [hRi, ← union_assoc]; rfl
    have hbase : R '' (univ ×ˢ Icc (0 : ℝ) 1) ∩ W = range lower := by
      rw [hRi, union_inter_distrib_right, T.inter_base]
      have hAW : A '' (univ ×ˢ Icc (0 : ℝ) 1) ∩ W = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro y hy
        have hu := hinter ▸ (show y ∈ A '' (univ ×ˢ Icc (0 : ℝ) 1) ∩ T.region from
          ⟨hy.1, Or.inl hy.2⟩)
        exact disjoint_left.mp hupperW hu hy.2
      rw [hAW, union_empty]
    have hnewoutside : Disjoint (range (fun q : Sphere 2 => nk.map (q, (3 : ℝ)))) W := by
      rw [disjoint_left]
      rintro y ⟨q,rfl⟩ hy
      have hu := hinter ▸ (show A (q,1) ∈ A '' (univ ×ˢ Icc (0 : ℝ) 1) ∩ T.region from
        ⟨⟨(q,1), ⟨mem_univ _, by norm_num⟩, rfl⟩, Or.inl ((hA1 q).symm ▸ hy)⟩)
      obtain ⟨z,hz⟩ := hu
      have hh : A (z,0) = A (q,1) := (hA0 z).trans hz
      have hc := congrArg Prod.snd (A.injOn (hA ⟨mem_univ _, by norm_num⟩)
        (hA ⟨mem_univ _, by norm_num⟩) hh)
      norm_num at hc
    let U : RelativeNeckPath g point savedNeck savedLevel W lower :=
      ⟨R,hR,(fun q => (hR0 q).trans (T.lower_eq q)),p,nk,3,by norm_num,κ.symm,
        (fun q => (hR1 q).trans (hA1 (κ.symm q))),hbase,hnewoutside,
        (by rw [hregion]; exact hregular), (by rw [hregion]; simpa only [union_comm] using hnewfront)⟩
    refine ⟨U, ?_, p, nk, ?_⟩
    · change T.region ⊆ W ∪ R '' (univ ×ˢ Icc (0 : ℝ) 1)
      rw [hregion]
      exact subset_union_left
    · intro y hy
      change y ∈ (W ∪ R '' (univ ×ˢ Icc (0 : ℝ) 1)) \ T.region
      rw [hregion]
      exact ⟨Or.inr (hfresh hy).1, (hfresh hy).2⟩
  · left
    obtain ⟨i,η,A,hA,hA0,hA1,_,hinter,hregular,hnewfront⟩ := hreturn
    have hsavedDisjoint : Disjoint
        (T.map '' (univ ×ˢ Icc (0 : ℝ) 1))
        (range (fun q : Sphere 2 => (savedNeck i).map (q, savedLevel i))) := by
      rw [disjoint_left]
      intro y hyR hyS
      have hyL : y ∈ range lower := T.inter_base ▸ ⟨hyR, hsaved i hyS⟩
      exact disjoint_left.mp (hlower i) hyL hyS
    have hmeet : T.map '' (univ ×ˢ Icc (0 : ℝ) 1) ∩
        A '' (univ ×ˢ Icc (0 : ℝ) 1) = T.map '' (univ ×ˢ ({1} : Set ℝ)) := by
      apply Subset.antisymm
      · intro y hy
        have hh := hinter ▸ (show y ∈ A '' (univ ×ˢ Icc (0 : ℝ) 1) ∩ T.region from
          ⟨hy.2, Or.inr hy.1⟩)
        exact hh.elim (fun h => hupper ▸ h)
          (fun h => False.elim (disjoint_left.mp hsavedDisjoint hy.1 h))
      · intro y hy
        have hh : y ∈ A '' (univ ×ˢ Icc (0 : ℝ) 1) ∩ T.region :=
          hinter.symm ▸ (show y ∈ range (fun q => nk.map (q, f q)) ∪
            range (fun q : Sphere 2 => (savedNeck i).map (q, savedLevel i)) from
              Or.inl (hupper.symm ▸ hy))
        exact ⟨hupperT hy, hh.1⟩
    obtain ⟨R,hR,hRi,hR0,hR1,_,_⟩ :=
      DifferentialGeometry.Topology.Manifold.exists_unit_slab_concatenation T.map A κ
        T.source hA (fun q => (hA0 q).trans (hmap q)) hmeet
    have hregion : W ∪ R '' (univ ×ˢ Icc (0 : ℝ) 1) =
        T.region ∪ A '' (univ ×ˢ Icc (0 : ℝ) 1) := by rw [hRi, ← union_assoc]; rfl
    refine ⟨i, κ.symm.trans η, R,hR,fun q => (hR0 q).trans (T.lower_eq q),
      fun q => (hR1 q).trans (hA1 (κ.symm q)), ?_, ?_, ?_, ?_⟩
    · rw [hregion]
      exact subset_union_left
    · rw [hRi, union_inter_distrib_right, T.inter_base]
      congr 1
      apply Subset.antisymm
      · intro y hy
        have hh := hinter ▸ (show y ∈ A '' (univ ×ˢ Icc (0 : ℝ) 1) ∩ T.region from
          ⟨hy.1, Or.inl hy.2⟩)
        exact hh.elim (fun h => False.elim (disjoint_left.mp hupperW h hy.2)) id
      · intro y hy
        have hh : y ∈ A '' (univ ×ˢ Icc (0 : ℝ) 1) ∩ T.region :=
          hinter.symm ▸ (show y ∈ range (fun q => nk.map (q, f q)) ∪
            range (fun q : Sphere 2 => (savedNeck i).map (q, savedLevel i)) from Or.inr hy)
        exact ⟨hh.1, hsaved i hy⟩
    · rw [hregion]
      exact hregular
    · rw [hregion]
      exact hnewfront


private theorem RelativeNeckPath.exists_stopped_or_returned
    (hcompact : IsCompact (closure Wᶜ))
    (T₀ : RelativeNeckPath g point savedNeck savedLevel W lower)
    (hlevel : ∀ i, |savedLevel i| ≤ 4)
    (hsaved : ∀ i, range (fun q : Sphere 2 => (savedNeck i).map (q, savedLevel i)) ⊆ W)
    (hpair : Pairwise fun i j =>
      Disjoint (range (fun q : Sphere 2 => (savedNeck i).map (q, savedLevel i)))
        (range (fun q : Sphere 2 => (savedNeck j).map (q, savedLevel j))))
    (hlower : ∀ i, Disjoint (range lower)
      (range (fun q : Sphere 2 => (savedNeck i).map (q, savedLevel i))))
    (heps : eps ≤ Classical.choose (exists_spatial_neck_level_graph_tolerance.{u}))
    (hepsstep : eps ≤ Classical.choose (exists_spatial_neck_finite_frontier_step_tolerance.{u, v}))
    (hepsrec : eps ≤ 1 / 156000) :
    ∃ T : RelativeNeckPath g point savedNeck savedLevel W lower,
      T₀.region ⊆ T.region ∧
        (¬ Nonempty (SpatialNeck g eps (T.neck.map (T.neck.center, T.level))) ∨ T.returned) := by
  classical
  by_contra hstop
  let State := {T : RelativeNeckPath g point savedNeck savedLevel W lower // T₀.region ⊆ T.region}
  have hnecks (T : State) : Nonempty (SpatialNeck g eps (T.val.neck.map (T.val.neck.center,T.val.level))) := by
    by_contra hn
    exact hstop ⟨T.val,T.property,Or.inl hn⟩
  have hnext (T : State) :
      ∃ U : State, T.val.region ⊆ U.val.region ∧
        ∃ (p : M) (nk : SpatialNeck g eps p),
          nk.map '' (univ ×ˢ Icc (1 : ℝ) 2) ⊆ U.val.region \ T.val.region := by
    rcases RelativeNeckPath.advance_or_return g point savedNeck savedLevel W lower T.val hlevel hsaved hpair hlower heps hepsstep (hnecks T) with hr | ha
    · exact (hstop ⟨T.val,T.property,Or.inr hr⟩).elim
    · obtain ⟨U,hsub,p,nk,hfresh⟩ := ha
      exact ⟨⟨U,T.property.trans hsub⟩,hsub,p,nk,hfresh⟩
  choose next hstep using hnext
  let seq : ℕ → State := fun n => next^[n] ⟨T₀,subset_rfl⟩
  have hseq (n : ℕ) : seq (n+1) = next (seq n) := Function.iterate_succ_apply' _ _ _
  have hmono : Monotone (fun n => (seq n).val.region) := by
    apply monotone_nat_of_le_succ
    intro n
    rw [hseq]
    exact (hstep (seq n)).1
  have hband (n : ℕ) : ∃ (p : M) (nk : SpatialNeck g eps p),
      nk.map '' (univ ×ˢ Icc (1 : ℝ) 2) ⊆ (seq (n+1)).val.region \ (seq n).val.region := by
    rw [hseq]
    exact (hstep (seq n)).2
  choose p nk hband using hband
  have hp (n : ℕ) : (nk n).map ((nk n).center, 3/2) ∈ closure Wᶜ := by
    apply subset_closure
    intro hw
    exact (hband n ⟨((nk n).center,3/2),⟨mem_univ _,by norm_num⟩,rfl⟩).2 (Or.inl hw)
  exact not_forall_spatial_neck_unit_band_subset_sdiff g hcompact hepsrec p nk
    hp (fun n => (seq n).val.region) hmono hband


omit [Finite ι] in
theorem exists_spatial_neck_cylinder_stop_or_return_tolerance :
    ∃ eta : ℝ, 0 < eta ∧ ∀ eps : ℝ, eps ≤ eta →
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M]
        (g : SmoothRiemannianMetric I3 M)
        (ι : Type v) [Finite ι] (point : ι → M)
        (saved : ∀ i, SpatialNeck g eps (point i)) (level : ι → ℝ) (W : Set M),
        IsCompact (closure Wᶜ) →
        (∀ i, |level i| ≤ 4) →
        (∀ i, range (fun q : Sphere 2 => (saved i).map (q, level i)) ⊆ W) →
        Pairwise (fun i j => Disjoint
          (range (fun q : Sphere 2 => (saved i).map (q, level i)))
          (range (fun q : Sphere 2 => (saved j).map (q, level j)))) →
        ∀ (A : PartialDiffeomorph IC I3 Cylinder M ∞),
          univ ×ˢ Icc (0 : ℝ) 1 ⊆ A.source →
          (∀ i, Disjoint (range (fun q : Sphere 2 => A (q,0)))
            (range (fun q : Sphere 2 => (saved i).map (q,level i)))) →
          ∀ (p : M) (nk : SpatialNeck g eps p) (a : ℝ)
            (κ : Sphere 2 ≃ₘ⟮I2,I2⟯ Sphere 2), |a| ≤ 4 →
            (∀ q : Sphere 2, A (q,1) = nk.map (κ q,a)) →
            A '' (univ ×ˢ Icc (0 : ℝ) 1) ∩ W = range (fun q : Sphere 2 => A (q,0)) →
            Disjoint (range (fun q : Sphere 2 => nk.map (q,a))) W →
            closure (interior (W ∪ A '' (univ ×ˢ Icc (0 : ℝ) 1))) =
              W ∪ A '' (univ ×ˢ Icc (0 : ℝ) 1) →
            frontier (W ∪ A '' (univ ×ˢ Icc (0 : ℝ) 1)) =
              range (fun q : Sphere 2 => nk.map (q,a)) ∪
                ⋃ i, range (fun q : Sphere 2 => (saved i).map (q,level i)) →
            (∃ (R : PartialDiffeomorph IC I3 Cylinder M ∞) (p' : M)
              (nk' : SpatialNeck g eps p') (a' : ℝ) (κ' : Sphere 2 ≃ₘ⟮I2,I2⟯ Sphere 2),
              univ ×ˢ Icc (0 : ℝ) 1 ⊆ R.source ∧ |a'| ≤ 4 ∧
              (∀ q : Sphere 2, R (q,0) = A (q,0)) ∧
              (∀ q : Sphere 2, R (q,1) = nk'.map (κ' q,a')) ∧
              W ∪ A '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆ W ∪ R '' (univ ×ˢ Icc (0 : ℝ) 1) ∧
              R '' (univ ×ˢ Icc (0 : ℝ) 1) ∩ W = range (fun q : Sphere 2 => A (q,0)) ∧
              Disjoint (range (fun q : Sphere 2 => nk'.map (q,a'))) W ∧
              closure (interior (W ∪ R '' (univ ×ˢ Icc (0 : ℝ) 1))) =
                W ∪ R '' (univ ×ˢ Icc (0 : ℝ) 1) ∧
              frontier (W ∪ R '' (univ ×ˢ Icc (0 : ℝ) 1)) =
                range (fun q : Sphere 2 => nk'.map (q,a')) ∪
                  ⋃ i, range (fun q : Sphere 2 => (saved i).map (q,level i)) ∧
              ¬ Nonempty (SpatialNeck g eps (nk'.map (nk'.center,a')))) ∨
            (∃ (i : ι) (ρ : Sphere 2 ≃ₘ⟮I2,I2⟯ Sphere 2)
              (R : PartialDiffeomorph IC I3 Cylinder M ∞),
              univ ×ˢ Icc (0 : ℝ) 1 ⊆ R.source ∧
              (∀ q : Sphere 2, R (q,0) = A (q,0)) ∧
              (∀ q : Sphere 2, R (q,1) = (saved i).map (ρ q,level i)) ∧
              W ∪ A '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆ W ∪ R '' (univ ×ˢ Icc (0 : ℝ) 1) ∧
              R '' (univ ×ˢ Icc (0 : ℝ) 1) ∩ W =
                range (fun q : Sphere 2 => A (q,0)) ∪
                  range (fun q : Sphere 2 => (saved i).map (q,level i)) ∧
              closure (interior (W ∪ R '' (univ ×ˢ Icc (0 : ℝ) 1))) =
                W ∪ R '' (univ ×ˢ Icc (0 : ℝ) 1) ∧
              frontier (W ∪ R '' (univ ×ˢ Icc (0 : ℝ) 1)) =
                ⋃ j : {j // j ≠ i}, range (fun q : Sphere 2 => (saved j.val).map (q,level j.val))) := by
  let η₁ := Classical.choose (exists_spatial_neck_level_graph_tolerance.{u})
  have hη₁ : 0 < η₁ := (Classical.choose_spec (exists_spatial_neck_level_graph_tolerance.{u})).1
  let η₂ := Classical.choose (exists_spatial_neck_finite_frontier_step_tolerance.{u,v})
  have hη₂ : 0 < η₂ := (Classical.choose_spec (exists_spatial_neck_finite_frontier_step_tolerance.{u,v})).1
  refine ⟨min η₁ (min η₂ (1/156000)),lt_min hη₁ (lt_min hη₂ (by norm_num)),?_⟩
  intro eps heps M _ _ _ _ g ι _ point saved level W hcompact hlevel hsaved hpair A hA hlower
    p nk a κ ha hupper hinter hout hregular hfront
  let T₀ : RelativeNeckPath g point saved level W (fun q => A (q,0)) :=
    ⟨A,hA,(fun _ => rfl),p,nk,a,ha,κ,hupper,hinter,hout,hregular,hfront⟩
  obtain ⟨T,hsub,hstop | hreturn⟩ := RelativeNeckPath.exists_stopped_or_returned
    g point saved level W (fun q => A (q,0)) hcompact T₀ hlevel hsaved hpair hlower
    (heps.trans (min_le_left _ _))
    (heps.trans ((min_le_right _ _).trans (min_le_left _ _)))
    (heps.trans ((min_le_right _ _).trans (min_le_right _ _)))
  · exact Or.inl ⟨T.map,T.point,T.neck,T.level,T.upperParam,T.source,T.bound,T.lower_eq,
      T.upper_eq,hsub,T.inter_base,T.upper_outside,T.regular,T.frontier,hstop⟩
  · obtain ⟨i,ρ,R,hR,hR0,hR1,hTR,hRW,hregular,hfront⟩ := hreturn
    exact Or.inr ⟨i,ρ,R,hR,hR0,hR1,hsub.trans hTR,hRW,hregular,hfront⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
