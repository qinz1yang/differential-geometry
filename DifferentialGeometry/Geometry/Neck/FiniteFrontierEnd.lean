import DifferentialGeometry.Geometry.Neck.SpatialFiniteFrontier
import DifferentialGeometry.Geometry.Neck.SpatialFrontierOrientation
import DifferentialGeometry.Topology.Compactness.FrontierSurvival
import DifferentialGeometry.Topology.Order.AntitoneSteps
import DifferentialGeometry.Geometry.Neck.SelectedProperEnd
import DifferentialGeometry.Topology.Combinatorics.BranchUpdates
import DifferentialGeometry.Topology.Combinatorics.FairEnumeration
import DifferentialGeometry.Topology.Frontier
import DifferentialGeometry.Topology.OpenPartialHomeomorph.LabelledCylinders
import DifferentialGeometry.Topology.Connected.ClosedAttachments

set_option autoImplicit false
noncomputable section
open Set Manifold
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u v
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]
  (g : SmoothRiemannianMetric I3 M) (eps : ℝ)

private structure RecordedNeckSphere where
  point : M
  neck : SpatialNeck g eps point
  level : ℝ
  bound : |level| ≤ 4
  param : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2

private def RecordedNeckSphere.map (S : RecordedNeckSphere g eps) (q : Sphere 2) : M :=
  S.neck.map (S.param q, S.level)

omit [T2Space M] in
private theorem RecordedNeckSphere.range_map (S : RecordedNeckSphere g eps) :
    range S.map = range (fun q => S.neck.map (q, S.level)) := by
  ext x
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨S.param q, hq⟩
  · rintro ⟨q, hq⟩
    refine ⟨S.param.symm q, ?_⟩
    exact (congrArg (fun z => S.neck.map (z, S.level))
      (show S.param (S.param.symm q) = q from S.param.apply_symm_apply q)).trans hq

private theorem RecordedNeckSphere.closed_range (S : RecordedNeckSphere g eps) :
    IsClosed (range S.map) := by
  rw [S.range_map]
  have hlen : (4 : ℝ) < eps⁻¹ :=
    (lt_inv_comm₀ (by norm_num) S.neck.eps_pos).mpr (by linarith [S.neck.eps_small])
  apply IsCompact.isClosed
  apply isCompact_range
  exact S.neck.map.contMDiffOn_toFun.continuousOn.comp_continuous
    (continuous_id.prodMk continuous_const)
    (fun q => S.neck.domain ⟨mem_univ _, by constructor <;>
      linarith [(abs_le.mp S.bound).1, (abs_le.mp S.bound).2]⟩)

variable (ι : Type v)

private structure NeckFrontierState where
  region : Set M
  compact : IsCompact region
  nonempty : region.Nonempty
  regular : closure (interior region) = region
  alive : Finset ι
  sphere : ι → RecordedNeckSphere g eps
  frontier : frontier region = ⋃ i ∈ alive, range (sphere i).map
  disjoint : (alive : Set ι).Pairwise
    (fun i j => Disjoint (range (sphere i).map) (range (sphere j).map))

omit [T2Space M] in
private theorem RecordedNeckSphere.isPreconnected_range (S : RecordedNeckSphere g eps) :
    IsPreconnected (range S.map) := by
  rw [S.range_map]
  have hlen : (4 : ℝ) < eps⁻¹ :=
    (lt_inv_comm₀ (by norm_num) S.neck.eps_pos).mpr (by linarith [S.neck.eps_small])
  let _ : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) (by norm_num : (0 : ℝ) ≤ 1))
  apply _root_.isPreconnected_range
  exact S.neck.map.contMDiffOn_toFun.continuousOn.comp_continuous
    (continuous_id.prodMk continuous_const)
    (fun q => S.neck.domain ⟨mem_univ _, by constructor <;>
      linarith [(abs_le.mp S.bound).1, (abs_le.mp S.bound).2]⟩)

omit [T2Space M] in
private theorem NeckFrontierState.alive_nonempty [PreconnectedSpace M] [NoncompactSpace M]
    (S : NeckFrontierState g eps ι) : S.alive.Nonempty := by
  obtain ⟨x, hx⟩ := DifferentialGeometry.Topology.frontier_nonempty_of_compact_nonempty
    S.compact S.nonempty
  rw [S.frontier] at hx
  obtain ⟨i, hi, _⟩ := mem_iUnion₂.mp hx
  exact ⟨i, hi⟩

private theorem NeckFrontierState.exists_outward_graph
    (S : NeckFrontierState g eps ι) (i : ι) (hi : i ∈ S.alive)
    (heps : eps ≤ Classical.choose (exists_spatial_neck_level_graph_tolerance.{u}))
    (allNeck : ∀ x ∈ _root_.frontier S.region, Nonempty (SpatialNeck g eps x)) :
    ∃ (p : M) (nk : SpatialNeck g eps p) (f : Sphere 2 → ℝ)
      (η : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2),
      ContMDiff I2 𝓘(ℝ) ∞ f ∧ (∀ q, |f q| < 1 / 10) ∧ f nk.center = 0 ∧
      (∀ q, nk.map (q, f q) = RecordedNeckSphere.map g eps (S.sphere i) (η q)) ∧
      (∃ r > 0, ∀ t, 0 < t → t < r → nk.map (nk.center, t) ∉ S.region) ∧
      p ∈ range (S.sphere i).map := by
  let x := (S.sphere i).neck.map ((S.sphere i).neck.center, (S.sphere i).level)
  have hx : x ∈ _root_.frontier S.region := by
    rw [S.frontier]
    refine mem_iUnion₂.mpr ⟨i, hi, ?_⟩
    rw [(S.sphere i).range_map]
    exact mem_range_self _
  obtain ⟨nk₀⟩ := allNeck x hx
  have hgraph := (Classical.choose_spec (exists_spatial_neck_level_graph_tolerance.{u})).2
  obtain ⟨κ, f, hf, hfsmall, hfzero, _, heq⟩ :=
    hgraph eps heps M g (S.sphere i).point x (S.sphere i).neck nk₀
      (S.sphere i).neck.center nk₀.center (S.sphere i).level 0
      (S.sphere i).bound (by norm_num) nk₀.center_eq.symm
  simp only [sub_zero] at hfsmall
  let η := κ.trans (S.sphere i).param.symm
  have hmap (q) : nk₀.map (q, f q) = RecordedNeckSphere.map g eps (S.sphere i) (η q) := by
    rw [heq]
    exact congrArg (fun z => (S.sphere i).neck.map (z, (S.sphere i).level))
      (show κ q = (S.sphere i).param ((S.sphere i).param.symm (κ q)) from
        ((S.sphere i).param.apply_symm_apply _).symm)
  have hrange : range (fun q => nk₀.map (q, f q)) = range (S.sphere i).map := by
    ext y
    constructor
    · rintro ⟨q, hq⟩; exact ⟨η q, (hmap q).symm.trans hq⟩
    · rintro ⟨q, hq⟩
      exact ⟨η.symm q, (hmap _).trans ((congrArg (RecordedNeckSphere.map g eps (S.sphere i))
        (show η (η.symm q) = q from η.apply_symm_apply q)).trans hq)⟩
  let R : Set M := ⋃ j : {j // j ∈ S.alive ∧ j ≠ i}, range (S.sphere j.val).map
  have hRclosed : IsClosed R := by
    let _ : Finite {j // j ∈ S.alive ∧ j ≠ i} :=
      Set.Finite.to_subtype ((S.alive.finite_toSet).subset (fun _ h => h.1))
    exact isClosed_iUnion_of_finite (fun j => (S.sphere j.val).closed_range)
  have hfront : _root_.frontier S.region = range (fun q => nk₀.map (q, f q)) ∪ R := by
    rw [S.frontier, hrange]
    ext y
    constructor
    · intro hy
      obtain ⟨j, hj, hyj⟩ := mem_iUnion₂.mp hy
      by_cases hji : j = i
      · subst j; exact Or.inl hyj
      · exact Or.inr (mem_iUnion.mpr ⟨⟨j, hj, hji⟩, hyj⟩)
    · rintro (hyi | hyr)
      · exact mem_iUnion₂.mpr ⟨i, hi, hyi⟩
      · obtain ⟨j, hyj⟩ := mem_iUnion.mp hyr
        exact mem_iUnion₂.mpr ⟨j.val, j.property.1, hyj⟩
  have hdis : Disjoint (range (fun q => nk₀.map (q, f q))) R := by
    rw [hrange]
    apply disjoint_iUnion_right.mpr
    intro j
    exact S.disjoint hi j.property.1 (Ne.symm j.property.2)
  obtain ⟨nk, h, _, hh, hhsmall, hhzero, hkeep, hout⟩ :=
    nk₀.exists_outward_graph_orientation f hf hfsmall hfzero S.regular hRclosed hfront hdis
  refine ⟨x, nk, h, η, hh, hhsmall, hhzero, fun q => (hkeep q).trans (hmap q), hout, ?_⟩
  rw [(S.sphere i).range_map]
  exact mem_range_self _

omit [IsManifold I3 ∞ M] in
private theorem filled_lower_face_of_cylinder_attachment
    (A : PartialDiffeomorph IC I3 Cylinder M ∞)
    (hA : univ ×ˢ Icc (0 : ℝ) 1 ⊆ A.source) {W R : Set M}
    (hW : closure (interior W) = W) (hR : IsClosed R)
    (hfront : _root_.frontier W = A '' (univ ×ˢ ({0} : Set ℝ)) ∪ R)
    (havoid : Disjoint R (A '' (univ ×ˢ Icc (0 : ℝ) 1)))
    (hinter : A '' (univ ×ˢ Icc (0 : ℝ) 1) ∩ W = A '' (univ ×ˢ ({0} : Set ℝ))) :
    A '' (univ ×ˢ ({0} : Set ℝ)) ⊆ interior (W ∪ A '' (univ ×ˢ Icc (0 : ℝ) 1)) := by
  let _ : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) (by norm_num : (0 : ℝ) ≤ 1))
  have hlow : A '' (univ ×ˢ ({0} : Set ℝ)) ⊆ W :=
    fun x hx => (hW ▸ isClosed_closure).frontier_subset (hfront.symm ▸ Or.inl hx)
  have hBclosed : IsClosed (A '' (univ ×ˢ Icc (0 : ℝ) 1)) :=
    ((isCompact_univ.prod isCompact_Icc).image_of_continuousOn
      (A.contMDiffOn_toFun.continuousOn.mono hA)).isClosed
  have hBfront := A.toOpenPartialHomeomorph.image_frontier_of_subset_source hA
    (isClosed_univ.prod isClosed_Icc) hBclosed
  change A '' _root_.frontier (univ ×ˢ Icc (0 : ℝ) 1) =
    _root_.frontier (A '' (univ ×ˢ Icc (0 : ℝ) 1)) at hBfront
  rw [frontier_univ_prod_eq, frontier_Icc zero_le_one] at hBfront
  have hdis : Disjoint (interior (A '' (univ ×ˢ Icc (0 : ℝ) 1))) (interior W) := by
    rw [disjoint_left]
    intro x hxB hxW
    have hxlow := hinter ▸ (show x ∈ A '' (univ ×ˢ Icc (0 : ℝ) 1) ∩ W from
      ⟨interior_subset hxB, interior_subset hxW⟩)
    have hxfront : x ∈ _root_.frontier (A '' (univ ×ˢ Icc (0 : ℝ) 1)) := by
      rw [← hBfront]
      exact image_mono (prod_mono_right (by intro t ht; exact Or.inl ht)) hxlow
    exact hxfront.2 hxB
  have hlowB : A '' (univ ×ˢ ({0} : Set ℝ)) ⊆ A '' (univ ×ˢ Icc (0 : ℝ) 1) :=
    image_mono (prod_mono_right (by intro t ht; have h : t = 0 := ht; subst t; norm_num))
  have hh := A.toOpenPartialHomeomorph.image_lower_boundary_subset_interior_union
    (by norm_num : (0 : ℝ) < 1) hA hW hR hdis hlow hfront.le (havoid.mono_right hlowB).symm
  change A '' (univ ×ˢ ({0} : Set ℝ)) ⊆ interior (A '' (univ ×ˢ Icc (0 : ℝ) 1) ∪ W) at hh
  simpa only [union_comm] using hh

private def slabReparametrize (A : PartialDiffeomorph IC I3 Cylinder M ∞)
    (η : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2) : PartialDiffeomorph IC I3 Cylinder M ∞ :=
  (η.prodCongr (Diffeomorph.refl 𝓘(ℝ) ℝ ∞)).toPartialDiffeomorph.trans A

omit [IsManifold I3 ∞ M] [T2Space M] in
private theorem slabReparametrize_apply (A : PartialDiffeomorph IC I3 Cylinder M ∞)
    (η : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2) (q : Sphere 2) (t : ℝ) :
    slabReparametrize A η (q, t) = A (η q, t) := rfl

omit [IsManifold I3 ∞ M] [T2Space M] in
private theorem slabReparametrize_image (A : PartialDiffeomorph IC I3 Cylinder M ∞)
    (η : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2) (L : Set ℝ) :
    slabReparametrize A η '' (univ ×ˢ L) = A '' (univ ×ˢ L) := by
  ext y
  constructor
  · rintro ⟨⟨q, t⟩, ht, hq⟩
    exact ⟨(η q, t), ⟨mem_univ _, ht.2⟩, hq⟩
  · rintro ⟨⟨q, t⟩, ht, hq⟩
    refine ⟨(η.symm q, t), ⟨mem_univ _, ht.2⟩, ?_⟩
    exact (congrArg (fun z => A (z, t))
      (show η (η.symm q) = q from η.apply_symm_apply q)).trans hq

omit [IsManifold I3 ∞ M] [T2Space M] in
private theorem slabReparametrize_source (A : PartialDiffeomorph IC I3 Cylinder M ∞)
    (η : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2)
    (hA : univ ×ˢ Icc (0 : ℝ) 1 ⊆ A.source) :
    univ ×ˢ Icc (0 : ℝ) 1 ⊆ (slabReparametrize A η).source :=
  fun _ hz => ⟨mem_univ _, hA ⟨mem_univ _, hz.2⟩⟩

private def OrdinaryNeckMoveAt (S T : NeckFrontierState g eps ι) (i : ι) : Prop :=
  T.alive = S.alive ∧ i ∈ S.alive ∧ ∃ (p : M) (nk : SpatialNeck g eps p)
    (P : PartialDiffeomorph IC I3 Cylinder M ∞),
    univ ×ˢ Icc (0 : ℝ) 1 ⊆ P.source ∧
    T.region = S.region ∪ P '' (univ ×ˢ Icc (0 : ℝ) 1) ∧
    (∀ q, P (q, 0) = RecordedNeckSphere.map g eps (S.sphere i) q) ∧
    (∀ q, P (q, 1) = RecordedNeckSphere.map g eps (T.sphere i) q) ∧
    (∀ j, j ≠ i → T.sphere j = S.sphere j) ∧
    P '' (univ ×ˢ Icc (0 : ℝ) 1) ∩ S.region = range (S.sphere i).map ∧
    range (S.sphere i).map ⊆ interior T.region ∧
    P '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆ nk.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) ∧
    nk.map '' (univ ×ˢ Icc (1 : ℝ) 2) ⊆ P '' (univ ×ˢ Icc (0 : ℝ) 1) ∧
    p ∈ range (S.sphere i).map

private def OrdinaryNeckMove (S T : NeckFrontierState g eps ι) : Prop :=
  T.alive = S.alive ∧ ∃ i ∈ S.alive, ∃ (p : M) (nk : SpatialNeck g eps p)
    (P : PartialDiffeomorph IC I3 Cylinder M ∞),
    univ ×ˢ Icc (0 : ℝ) 1 ⊆ P.source ∧
    T.region = S.region ∪ P '' (univ ×ˢ Icc (0 : ℝ) 1) ∧
    (∀ q, P (q, 0) = RecordedNeckSphere.map g eps (S.sphere i) q) ∧
    (∀ q, P (q, 1) = RecordedNeckSphere.map g eps (T.sphere i) q) ∧
    (∀ j, j ≠ i → T.sphere j = S.sphere j) ∧
    P '' (univ ×ˢ Icc (0 : ℝ) 1) ∩ S.region = range (S.sphere i).map ∧
    range (S.sphere i).map ⊆ interior T.region ∧
    P '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆ nk.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) ∧
    nk.map '' (univ ×ˢ Icc (1 : ℝ) 2) ⊆ P '' (univ ×ˢ Icc (0 : ℝ) 1) ∧
    p ∈ range (S.sphere i).map

omit [T2Space M] in
private theorem recorded_face_nonempty (S : RecordedNeckSphere g eps) : (range S.map).Nonempty :=
  ⟨RecordedNeckSphere.map g eps S S.neck.center, S.neck.center, rfl⟩

omit [T2Space M] in
private theorem NeckFrontierState.adapt_frontier
    (S : NeckFrontierState g eps ι) (i : ι) (hi : i ∈ S.alive)
    {p : M} (nk : SpatialNeck g eps p) (f : Sphere 2 → ℝ)
    (η : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2)
    (hmap : ∀ q, nk.map (q, f q) = RecordedNeckSphere.map g eps (S.sphere i) (η q)) :
    _root_.frontier S.region = range (fun q => nk.map (q, f q)) ∪
      ⋃ j : {j // j ∈ S.alive ∧ j ≠ i}, range (fun q =>
        (S.sphere j.val).neck.map (q, (S.sphere j.val).level)) := by
  have hactive : range (fun q => nk.map (q, f q)) = range (S.sphere i).map := by
    ext x
    constructor
    · rintro ⟨q, hq⟩; exact ⟨η q, (hmap q).symm.trans hq⟩
    · rintro ⟨q, hq⟩
      exact ⟨η.symm q, (hmap _).trans ((congrArg (RecordedNeckSphere.map g eps (S.sphere i))
        (show η (η.symm q) = q from η.apply_symm_apply q)).trans hq)⟩
  rw [hactive, S.frontier]
  ext x
  constructor
  · intro hx
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hx
    by_cases hji : j = i
    · subst j; exact Or.inl hxj
    · exact Or.inr (mem_iUnion.mpr ⟨⟨j, hj, hji⟩, (S.sphere j).range_map ▸ hxj⟩)
  · rintro (hxi | hxr)
    · exact mem_iUnion₂.mpr ⟨i, hi, hxi⟩
    · obtain ⟨j, hxj⟩ := mem_iUnion.mp hxr
      exact mem_iUnion₂.mpr ⟨j.val, j.property.1, (S.sphere j.val).range_map.symm ▸ hxj⟩

private theorem NeckFrontierState.exists_step_at
    (S : NeckFrontierState g eps ι) (i : ι) (hi : i ∈ S.alive)
    (heps : eps ≤ Classical.choose (exists_spatial_neck_level_graph_tolerance.{u}))
    (hepsstep : eps ≤ Classical.choose (exists_spatial_neck_finite_frontier_step_tolerance.{u, v}))
    (allNeck : ∀ x ∈ _root_.frontier S.region, Nonempty (SpatialNeck g eps x)) :
    ∃ T : NeckFrontierState g eps ι, S.region ⊆ T.region ∧
      (OrdinaryNeckMoveAt g eps ι S T i ∨ (T.alive ⊂ S.alive ∧ T.sphere = S.sphere)) := by
  classical
  obtain ⟨p, nk, f, η, hf, hfsmall, hfzero, hmap, hout, hpoint⟩ :=
    NeckFrontierState.exists_outward_graph g eps ι S i hi heps allNeck
  let Other := {j // j ∈ S.alive ∧ j ≠ i}
  let _ : Finite Other := Set.Finite.to_subtype
    (S.alive.finite_toSet.subset (fun _ h => h.1))
  have hactive : range (fun q => nk.map (q, f q)) = range (S.sphere i).map := by
    ext x
    constructor
    · rintro ⟨q, hq⟩; exact ⟨η q, (hmap q).symm.trans hq⟩
    · rintro ⟨q, hq⟩
      exact ⟨η.symm q, (hmap _).trans ((congrArg (RecordedNeckSphere.map g eps (S.sphere i))
        (show η (η.symm q) = q from η.apply_symm_apply q)).trans hq)⟩
  have hpair : Pairwise (fun j k : Other =>
      Disjoint (range (fun q => (S.sphere j.val).neck.map (q, (S.sphere j.val).level)))
        (range (fun q => (S.sphere k.val).neck.map (q, (S.sphere k.val).level)))) := by
    intro j k hjk
    rw [← (S.sphere j.val).range_map, ← (S.sphere k.val).range_map]
    exact S.disjoint j.property.1 k.property.1 (fun h => hjk (Subtype.ext h))
  have hav (j : Other) : Disjoint (range (fun q => nk.map (q, f q)))
      (range (fun q => (S.sphere j.val).neck.map (q, (S.sphere j.val).level))) := by
    rw [hactive, ← (S.sphere j.val).range_map]
    exact S.disjoint hi j.property.1 (Ne.symm j.property.2)
  have hstep :=
    (Classical.choose_spec (exists_spatial_neck_finite_frontier_step_tolerance.{u, v})).2
  rcases hstep eps hepsstep M g p nk Other (fun j => (S.sphere j.val).point)
    (fun j => (S.sphere j.val).neck) (fun j => (S.sphere j.val).level)
    (fun j => (S.sphere j.val).bound) hpair f hf hfsmall hfzero S.region S.regular
    (NeckFrontierState.adapt_frontier g eps ι S i hi nk f η hmap) hav hout with ho | hr
  · obtain ⟨A, hA, hformula, hzero, hone, hcompact, hinter, hregular, hfront, hfresh⟩ := ho
    let P := slabReparametrize A η.symm
    let B := A '' (univ ×ˢ Icc (0 : ℝ) 1)
    let newSphere : RecordedNeckSphere g eps := ⟨p, nk, 3, by norm_num, η.symm⟩
    let sp := Function.update S.sphere i newSphere
    have hsp_i : sp i = newSphere := Function.update_self _ _ _
    have hsp_ne (j) (hj : j ≠ i) : sp j = S.sphere j := Function.update_of_ne hj _ _
    have hnewfront : _root_.frontier (S.region ∪ B) = ⋃ j ∈ S.alive, range (sp j).map := by
      rw [hfront]
      ext x
      constructor
      · rintro (hx | hx)
        · obtain ⟨j, hj⟩ := mem_iUnion.mp hx
          refine mem_iUnion₂.mpr ⟨j.val, j.property.1, ?_⟩
          rw [hsp_ne j.val j.property.2, (S.sphere j.val).range_map]
          exact hj
        · refine mem_iUnion₂.mpr ⟨i, hi, ?_⟩
          rw [hsp_i, RecordedNeckSphere.range_map]
          exact hx
      · intro hx
        obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hx
        by_cases hji : j = i
        · subst j
          right
          rw [hsp_i, RecordedNeckSphere.range_map] at hxj
          exact hxj
        · left
          refine mem_iUnion.mpr ⟨⟨j, hj, hji⟩, ?_⟩
          rw [hsp_ne j hji, (S.sphere j).range_map] at hxj
          exact hxj
    have hnewdisjoint : (S.alive : Set ι).Pairwise
        (fun j k => Disjoint (range (sp j).map) (range (sp k).map)) := by
      intro j hj k hk hjk
      by_cases hji : j = i
      · subst j
        have hki : k ≠ i := Ne.symm hjk
        rw [hsp_i, hsp_ne k hki, RecordedNeckSphere.range_map]
        rw [disjoint_left]
        rintro x ⟨q, hqx⟩ hxold
        have hxB : x ∈ B := ⟨(q, 1), ⟨mem_univ _, by norm_num⟩, (hone q).trans hqx⟩
        have hxW := S.compact.isClosed.frontier_subset
          (S.frontier.symm ▸ mem_iUnion₂.mpr ⟨k, hk, hxold⟩)
        have hxactive : x ∈ range (S.sphere i).map := hactive ▸ (hinter ▸ ⟨hxB, hxW⟩)
        exact disjoint_left.mp (S.disjoint hi hk hjk) hxactive hxold
      · by_cases hki : k = i
        · subst k
          rw [hsp_ne j hji, hsp_i]
          rw [show range (RecordedNeckSphere.map g eps newSphere) =
            range (fun q => nk.map (q, (3 : ℝ))) from newSphere.range_map]
          rw [disjoint_left]
          rintro x hxold ⟨q, hqx⟩
          have hxB : x ∈ B := ⟨(q, 1), ⟨mem_univ _, by norm_num⟩, (hone q).trans hqx⟩
          have hxW := S.compact.isClosed.frontier_subset
            (S.frontier.symm ▸ mem_iUnion₂.mpr ⟨j, hj, hxold⟩)
          have hxactive : x ∈ range (S.sphere i).map := hactive ▸ (hinter ▸ ⟨hxB, hxW⟩)
          exact disjoint_left.mp (S.disjoint hj hi hjk) hxold hxactive
        · rw [hsp_ne j hji, hsp_ne k hki]
          exact S.disjoint hj hk hjk
    let T : NeckFrontierState g eps ι :=
      ⟨S.region ∪ B, S.compact.union hcompact, S.nonempty.mono subset_union_left,
        hregular, S.alive, sp, hnewfront, hnewdisjoint⟩
    have hPimg : P '' (univ ×ˢ Icc (0 : ℝ) 1) = B := slabReparametrize_image A η.symm _
    have hP0 (q) : P (q, 0) = RecordedNeckSphere.map g eps (S.sphere i) q := by
      change A (η.symm q, 0) = _
      exact (hzero _).trans ((hmap _).trans ((congrArg (RecordedNeckSphere.map g eps (S.sphere i))
        (show η (η.symm q) = q from η.apply_symm_apply q))))
    have hP1 (q) : P (q, 1) = RecordedNeckSphere.map g eps (T.sphere i) q := by
      change A (η.symm q, 1) = RecordedNeckSphere.map g eps (sp i) q
      rw [hsp_i]
      exact hone _
    have hface : A '' (univ ×ˢ ({0} : Set ℝ)) = range (S.sphere i).map := by
      rw [← hactive]
      ext x
      constructor
      · rintro ⟨⟨q, t⟩, ⟨_, ht⟩, hq⟩
        have : t = 0 := ht
        subst t
        exact ⟨q, (hzero q).symm.trans hq⟩
      · rintro ⟨q, hq⟩
        exact ⟨(q, 0), ⟨mem_univ _, rfl⟩, (hzero q).trans hq⟩
    let R := ⋃ j : Other, range (S.sphere j.val).map
    have hRclosed : IsClosed R := isClosed_iUnion_of_finite (fun j => (S.sphere j.val).closed_range)
    have hRavoid : Disjoint R B := by
      rw [disjoint_left]
      intro x hxR hxB
      obtain ⟨j, hxj⟩ := mem_iUnion.mp hxR
      have hxW := S.compact.isClosed.frontier_subset
        (S.frontier.symm ▸ mem_iUnion₂.mpr ⟨j.val, j.property.1, hxj⟩)
      have hxi : x ∈ range (S.sphere i).map := hactive ▸ (hinter ▸ ⟨hxB, hxW⟩)
      exact disjoint_left.mp (S.disjoint hi j.property.1 (Ne.symm j.property.2)) hxi hxj
    have hfr : _root_.frontier S.region = A '' (univ ×ˢ ({0} : Set ℝ)) ∪ R := by
      rw [hface]
      have hc := NeckFrontierState.adapt_frontier g eps ι S i hi nk f η hmap
      rw [hactive] at hc
      change _root_.frontier S.region = range (S.sphere i).map ∪
        ⋃ j : Other, range (S.sphere j.val).map
      simp only [RecordedNeckSphere.range_map]
      simpa only [RecordedNeckSphere.range_map] using hc
    have hfill : range (S.sphere i).map ⊆ interior T.region := by
      rw [← hface]
      exact filled_lower_face_of_cylinder_attachment A hA S.regular hRclosed hfr hRavoid
        (hinter.trans hactive |>.trans hface.symm)
    refine ⟨T, subset_union_left, Or.inl ⟨rfl, hi, p, nk, P,
      slabReparametrize_source A η.symm hA, ?_, hP0, hP1, hsp_ne, ?_, hfill, ?_, ?_, hpoint⟩⟩
    · change S.region ∪ B = S.region ∪ P '' (univ ×ˢ Icc (0 : ℝ) 1)
      rw [hPimg]
    · rw [hPimg]
      exact hinter.trans hactive
    · rw [hPimg]
      rintro x ⟨⟨q, t⟩, ht, htx⟩
      refine ⟨(q, f q + (3 - f q) * t), ?_, (hformula q t).symm.trans htx⟩
      have hlen : (4 : ℝ) < eps⁻¹ :=
        (lt_inv_comm₀ (by norm_num) nk.eps_pos).mpr (by linarith [nk.eps_small])
      have hgap : 0 < 3 - f q := by linarith [(abs_lt.mp (hfsmall q)).2]
      constructor
      · exact mem_univ _
      · constructor <;> nlinarith [ht.2.1, ht.2.2, (abs_lt.mp (hfsmall q)).1,
          (abs_lt.mp (hfsmall q)).2]
    · rw [hPimg]
      exact fun x hx => (hfresh hx).1
  · obtain ⟨j, κ, A, hA, hzero, hone, hcompact, hinter, hregular, hfront⟩ := hr
    let alive := (S.alive.erase i).erase j.val
    let T : NeckFrontierState g eps ι := by
      refine ⟨S.region ∪ A '' (univ ×ˢ Icc (0 : ℝ) 1), S.compact.union hcompact,
        S.nonempty.mono subset_union_left, hregular, alive, S.sphere, ?_, ?_⟩
      · rw [hfront]
        ext x
        constructor
        · intro hx
          obtain ⟨k, hxk⟩ := mem_iUnion.mp hx
          refine mem_iUnion₂.mpr ⟨k.val.val, ?_, ?_⟩
          · simp only [alive, Finset.mem_erase]
            exact ⟨fun h => k.property (Subtype.ext h), k.val.property.2, k.val.property.1⟩
          · exact (S.sphere k.val.val).range_map.symm ▸ hxk
        · intro hx
          obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hx
          have hk' : k ≠ j.val ∧ k ≠ i ∧ k ∈ S.alive := by
            simpa only [alive, Finset.mem_erase] using hk
          refine mem_iUnion.mpr ⟨⟨⟨k, hk'.2.2, hk'.2.1⟩, ?_⟩, ?_⟩
          · exact fun h => hk'.1 (congrArg Subtype.val h)
          · exact (S.sphere k).range_map ▸ hxk
      · intro k hk l hl hkl
        exact S.disjoint (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hk))
          (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hl)) hkl
    refine ⟨T, subset_union_left, Or.inr ⟨?_, rfl⟩⟩
    change alive ⊂ S.alive
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨(Finset.erase_subset _ _).trans (Finset.erase_subset _ _), ?_⟩
    intro hsame
    have hmem : i ∈ alive := hsame.symm ▸ hi
    have hmem' := Finset.mem_of_mem_erase hmem
    exact (Finset.mem_erase.mp hmem').1 rfl

private theorem NeckFrontierState.exists_step
    (S : NeckFrontierState g eps ι) (i : ι) (hi : i ∈ S.alive)
    (heps : eps ≤ Classical.choose (exists_spatial_neck_level_graph_tolerance.{u}))
    (hepsstep : eps ≤ Classical.choose (exists_spatial_neck_finite_frontier_step_tolerance.{u, v}))
    (allNeck : ∀ x ∈ _root_.frontier S.region, Nonempty (SpatialNeck g eps x)) :
    ∃ T : NeckFrontierState g eps ι, S.region ⊆ T.region ∧
      (OrdinaryNeckMove g eps ι S T ∨ (T.alive ⊂ S.alive ∧ T.sphere = S.sphere)) := by
  obtain ⟨T, hsub, ho | hr⟩ :=
    NeckFrontierState.exists_step_at g eps ι S i hi heps hepsstep allNeck
  · exact ⟨T, hsub, Or.inl ⟨ho.1, i, ho.2⟩⟩
  · exact ⟨T, hsub, Or.inr hr⟩

private theorem NeckFrontierState.exists_scheduled_process
    [PreconnectedSpace M] [NoncompactSpace M]
    (S₀ : NeckFrontierState g eps ι) (schedule : ℕ → ι)
    (heps : eps ≤ Classical.choose (exists_spatial_neck_level_graph_tolerance.{u}))
    (hepsstep : eps ≤ Classical.choose (exists_spatial_neck_finite_frontier_step_tolerance.{u, v}))
    (allNeck : ∀ x : M, x ∉ interior S₀.region → Nonempty (SpatialNeck g eps x)) :
    ∃ (S : ℕ → NeckFrontierState g eps ι) (selected : ℕ → ι), S 0 = S₀ ∧
      Monotone (fun n => (S n).region) ∧ Antitone (fun n => (S n).alive) ∧
      (∀ n, selected n ∈ (S n).alive) ∧
      (∀ n, schedule n ∈ (S n).alive → selected n = schedule n) ∧
      (∀ n, OrdinaryNeckMoveAt g eps ι (S n) (S (n + 1)) (selected n) ∨
        ((S (n + 1)).alive ⊂ (S n).alive ∧ (S (n + 1)).sphere = (S n).sphere)) ∧
      ∃ N : ℕ, ∀ n, N ≤ n →
        OrdinaryNeckMoveAt g eps ι (S n) (S (n + 1)) (selected n) := by
  classical
  let State := {S : NeckFrontierState g eps ι // S₀.region ⊆ S.region}
  let pick (n : ℕ) (S : State) : ι :=
    if schedule n ∈ S.val.alive then schedule n
    else (NeckFrontierState.alive_nonempty g eps ι S.val).choose
  have hpick (n : ℕ) (S : State) : pick n S ∈ S.val.alive := by
    dsimp only [pick]
    split
    · assumption
    · exact (NeckFrontierState.alive_nonempty g eps ι S.val).choose_spec
  have hnext (n : ℕ) (S : State) : ∃ T : State, S.val.region ⊆ T.val.region ∧
      (OrdinaryNeckMoveAt g eps ι S.val T.val (pick n S) ∨
        (T.val.alive ⊂ S.val.alive ∧ T.val.sphere = S.val.sphere)) := by
    obtain ⟨T, hsub, hmove⟩ :=
      NeckFrontierState.exists_step_at g eps ι S.val (pick n S) (hpick n S) heps hepsstep
        (fun x hx => allNeck x (fun hxint => hx.2 (interior_mono S.property hxint)))
    exact ⟨⟨T, S.property.trans hsub⟩, hsub, hmove⟩
  choose next hnext using hnext
  let states : ℕ → State := Nat.rec ⟨S₀, Subset.rfl⟩ (fun n S => next n S)
  let S : ℕ → NeckFrontierState g eps ι := fun n => (states n).val
  let selected (n) := pick n (states n)
  have hS (n : ℕ) : S (n + 1) = (next n (states n)).val := rfl
  have hmono : Monotone (fun n => (S n).region) := monotone_nat_of_le_succ (by
    intro n
    rw [hS]
    exact (hnext n (states n)).1)
  have hanti : Antitone (fun n => (S n).alive) := antitone_nat_of_succ_le (by
    intro n
    rw [hS]
    rcases (hnext n (states n)).2 with ho | hr
    · exact ho.1.le
    · exact hr.1.le)
  have hsteps (n) : OrdinaryNeckMoveAt g eps ι (S n) (S (n + 1)) (selected n) ∨
      ((S (n + 1)).alive ⊂ (S n).alive ∧ (S (n + 1)).sphere = (S n).sphere) := by
    rw [hS]
    exact (hnext n (states n)).2
  obtain ⟨N, hN⟩ := hanti.exists_forall_ge_of_or_succ_lt
    (fun n => (hsteps n).imp_right And.left)
  refine ⟨S, selected, rfl, hmono, hanti, fun n => hpick n (states n), ?_, hsteps, N, hN⟩
  intro n hn
  exact if_pos hn

private theorem NeckFrontierState.exists_ordinary_tail
    [PreconnectedSpace M] [NoncompactSpace M]
    (S₀ : NeckFrontierState g eps ι)
    (heps : eps ≤ Classical.choose (exists_spatial_neck_level_graph_tolerance.{u}))
    (hepsstep : eps ≤ Classical.choose (exists_spatial_neck_finite_frontier_step_tolerance.{u, v}))
    (allNeck : ∀ x : M, x ∉ interior S₀.region → Nonempty (SpatialNeck g eps x)) :
    ∃ S : ℕ → NeckFrontierState g eps ι, S 0 = S₀ ∧
      Monotone (fun n => (S n).region) ∧ Antitone (fun n => (S n).alive) ∧
      (∀ n, OrdinaryNeckMove g eps ι (S n) (S (n + 1)) ∨
        ((S (n + 1)).alive ⊂ (S n).alive ∧ (S (n + 1)).sphere = (S n).sphere)) ∧
      ∃ N : ℕ, ∀ n, N ≤ n → OrdinaryNeckMove g eps ι (S n) (S (n + 1)) := by
  classical
  let i := (NeckFrontierState.alive_nonempty g eps ι S₀).choose
  obtain ⟨S, selected, hzero, hmono, hanti, _, _, hsteps, N, hN⟩ :=
    NeckFrontierState.exists_scheduled_process g eps ι S₀ (fun _ => i) heps hepsstep allNeck
  have hordinary {S T : NeckFrontierState g eps ι} {j : ι}
      (h : OrdinaryNeckMoveAt g eps ι S T j) : OrdinaryNeckMove g eps ι S T :=
    ⟨h.1, j, h.2⟩
  exact ⟨S, hzero, hmono, hanti, fun n => (hsteps n).imp_left hordinary,
    N, fun n hn => hordinary (hN n hn)⟩

private theorem NeckFrontierState.exists_fair_process
    [PreconnectedSpace M] [NoncompactSpace M]
    (S₀ : NeckFrontierState g eps ι)
    (heps : eps ≤ Classical.choose (exists_spatial_neck_level_graph_tolerance.{u}))
    (hepsstep : eps ≤ Classical.choose (exists_spatial_neck_finite_frontier_step_tolerance.{u, v}))
    (allNeck : ∀ x : M, x ∉ interior S₀.region → Nonempty (SpatialNeck g eps x)) :
    ∃ (S : ℕ → NeckFrontierState g eps ι) (selected : ℕ → ι), S 0 = S₀ ∧
      Monotone (fun n => (S n).region) ∧ Antitone (fun n => (S n).alive) ∧
      (∀ n, selected n ∈ (S n).alive) ∧
      (∀ n, OrdinaryNeckMoveAt g eps ι (S n) (S (n + 1)) (selected n) ∨
        ((S (n + 1)).alive ⊂ (S n).alive ∧ (S (n + 1)).sphere = (S n).sphere)) ∧
      ∃ N : ℕ, (S N).alive.Nonempty ∧
        (∀ n, N ≤ n → (S n).alive = (S N).alive) ∧
        (∀ n, N ≤ n → OrdinaryNeckMoveAt g eps ι (S n) (S (n + 1)) (selected n)) ∧
        ∀ i ∈ (S N).alive,
          {n | OrdinaryNeckMoveAt g eps ι (S n) (S (n + 1)) i ∧ selected n = i}.Infinite := by
  classical
  obtain ⟨schedule, _, hfair⟩ := S₀.alive.finite_toSet.countable.exists_sequence_cofinal_fibers
    (NeckFrontierState.alive_nonempty g eps ι S₀)
  obtain ⟨S, selected, hzero, hmono, hanti, hselected, hschedule, hsteps, N, hN⟩ :=
    NeckFrontierState.exists_scheduled_process g eps ι S₀ schedule heps hepsstep allNeck
  have hstable (n : ℕ) (hn : N ≤ n) : (S n).alive = (S N).alive := by
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih => exact (hN n hn).1.trans ih
  refine ⟨S, selected, hzero, hmono, hanti, hselected, hsteps, N,
    NeckFrontierState.alive_nonempty g eps ι (S N), hstable, hN, ?_⟩
  intro i hi
  apply Set.infinite_of_forall_exists_gt
  intro a
  have hi0 : i ∈ S₀.alive := by simpa only [hzero] using hanti (Nat.zero_le N) hi
  obtain ⟨n, hn, hsi⟩ := hfair i hi0 (max N (a + 1))
  have hNn : N ≤ n := (le_max_left _ _).trans hn
  have hin : i ∈ (S n).alive := (hstable n hNn).symm ▸ hi
  have hselectedi : selected n = i := (hschedule n (hsi.symm ▸ hin)).trans hsi
  refine ⟨n, ?_, lt_of_lt_of_le (Nat.lt_succ_self a) ((le_max_right _ _).trans hn)⟩
  exact ⟨hselectedi ▸ hN n hNn, hselectedi⟩

private theorem NeckFrontierState.exists_fair_ordinary_tail
    [PreconnectedSpace M] [NoncompactSpace M]
    (S₀ : NeckFrontierState g eps ι)
    (heps : eps ≤ Classical.choose (exists_spatial_neck_level_graph_tolerance.{u}))
    (hepsstep : eps ≤ Classical.choose (exists_spatial_neck_finite_frontier_step_tolerance.{u, v}))
    (allNeck : ∀ x : M, x ∉ interior S₀.region → Nonempty (SpatialNeck g eps x)) :
    ∃ (S : ℕ → NeckFrontierState g eps ι) (selected : ℕ → ι), S₀.region ⊆ (S 0).region ∧
      Monotone (fun n => (S n).region) ∧
      (∀ n, (S n).alive = (S 0).alive) ∧
      (∀ n, OrdinaryNeckMoveAt g eps ι (S n) (S (n + 1)) (selected n)) ∧
      ∀ i ∈ (S 0).alive, {n | selected n = i}.Infinite := by
  obtain ⟨seq, selected, hzero, hmono, _, _, _, N, _, hstable, hN, hfair⟩ :=
    NeckFrontierState.exists_fair_process g eps ι S₀ heps hepsstep allNeck
  let S := fun n => seq (N + n)
  refine ⟨S, fun n => selected (N + n), ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [S, Nat.add_zero, hzero] using hmono (Nat.zero_le N)
  · exact fun a b hab => hmono (Nat.add_le_add_left hab N)
  · intro n
    exact (hstable _ (Nat.le_add_right N n)).trans (congrArg NeckFrontierState.alive
      (show seq N = S 0 from rfl))
  · intro n
    simpa only [S, Nat.add_assoc] using hN (N + n) (Nat.le_add_right N n)
  · intro i hi
    have hinf := hfair i (show i ∈ (seq N).alive from hi)
    apply Set.infinite_of_forall_exists_gt
    intro a
    obtain ⟨n, hn, hgt⟩ := hinf.exists_gt (N + a)
    refine ⟨n - N, ?_, by omega⟩
    change selected (N + (n - N)) = i
    rw [Nat.add_sub_of_le (by omega)]
    exact hn.2

private theorem NeckFrontierState.exists_end_family
    [PreconnectedSpace M] [NoncompactSpace M]
    (S₀ : NeckFrontierState g eps ι)
    (heps : eps ≤ Classical.choose (exists_spatial_neck_level_graph_tolerance.{u}))
    (hepsstep : eps ≤ Classical.choose (exists_spatial_neck_finite_frontier_step_tolerance.{u, v}))
    (hepsrec : eps ≤ 1 / 156000)
    (hcompact : ∀ B : ℝ, IsCompact {x : M | Geometry.Curvature.metricScalarAt g x ≤ B})
    (allNeck : ∀ x : M, x ∉ interior S₀.region → Nonempty (SpatialNeck g eps x)) :
    ∃ S : NeckFrontierState g eps ι, S₀.region ⊆ S.region ∧ IsConnected S.region ∧
      ∃ Θ : {i // i ∈ S.alive} → Cylinder → M,
        (∀ i, ContMDiffOn IC I3 ∞ (Θ i) (univ ×ˢ Ici (0 : ℝ)) ∧
          InjOn (Θ i) (univ ×ˢ Ici (0 : ℝ)) ∧
          IsProperMap (fun z : Sphere 2 × ℝ≥0 => Θ i (z.1, z.2.val)) ∧
          (let U : TopologicalSpace.Opens Cylinder :=
            ⟨univ ×ˢ Ioi (0 : ℝ), isOpen_univ.prod isOpen_Ioi⟩
           IsSmoothEmbedding IC I3 ∞ (fun z : U => Θ i z)) ∧
          Θ i '' (univ ×ˢ Ici (0 : ℝ)) ∩ S.region = range (S.sphere i.val).map ∧
          (∀ z, Θ i (z, 0) = RecordedNeckSphere.map g eps (S.sphere i.val) z) ∧
          (∀ B : ℝ, ∃ T : ℝ≥0, ∀ (z : Sphere 2) (t : ℝ≥0),
            T ≤ t → B < Geometry.Curvature.metricScalarAt g (Θ i (z, t.val))) ∧
          ∃ (p : M) (nk : SpatialNeck g eps p)
            (P : PartialDiffeomorph IC I3 Cylinder M ∞),
            p ∈ range (S.sphere i.val).map ∧
            univ ×ˢ Icc (0 : ℝ) 1 ⊆ P.source ∧
            (∀ z t, t ∈ Icc (0 : ℝ) 1 → Θ i (z, t) = P (z, t)) ∧
            P '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆ nk.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹)) ∧
        Pairwise (fun i j => Disjoint (Θ i '' (univ ×ˢ Ici (0 : ℝ)))
          (Θ j '' (univ ×ˢ Ici (0 : ℝ)))) ∧
        S.region ∪ (⋃ i, Θ i '' (univ ×ˢ Ici (0 : ℝ))) = univ := by
  classical
  obtain ⟨seq, label, hsub, hmono, halive, hmove, hfair⟩ :=
    NeckFrontierState.exists_fair_ordinary_tail g eps ι S₀ heps hepsstep allNeck
  have hchoice (n) := (hmove n).2.2
  choose point neck P hsource hrange hlower hupper hunchanged hinter hfilled hcontrolled hband
    hpoint using hchoice
  let sphere := fun n i => RecordedNeckSphere.map g eps ((seq n).sphere i)
  have hcontained (n) : P n '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆ (seq (n + 1)).region := by
    rw [hrange n]
    exact subset_union_right
  have hsphere (n) : range (sphere n (label n)) ⊆ _root_.frontier (seq n).region := by
    intro x hx
    rw [(seq n).frontier]
    exact mem_iUnion₂.mpr ⟨label n, (hmove n).2.1, hx⟩
  have hend (i : {i // i ∈ (seq 0).alive}) :=
    exists_proper_neck_end_of_infinite_updates g hepsrec hcompact label i.val
      (hfair i.val i.property)
      sphere (fun n hn => congrArg (RecordedNeckSphere.map g eps)
        (hunchanged n i.val (Ne.symm hn)))
      P hsource (fun _ => Diffeomorph.refl I2 (Sphere 2) ∞) hlower hupper
      (fun n => (seq n).region) hmono hcontained hinter hsphere hfilled
      point neck hcontrolled hband
  choose select hselect hlabel hcover Θ hsm hinj hproper hembed hwhole hinitial hfirst hbase hscalar
    using hend
  let Ind := {i // i ∈ (seq 0).alive}
  let _ : Finite Ind := (seq 0).alive.finite_toSet.to_subtype
  let labels (n) : Ind := ⟨label n, halive n ▸ (hmove n).2.1⟩
  have hopen : IsOpen (⋃ n, (seq n).region) := by
    apply DifferentialGeometry.Topology.isOpen_iUnion_of_recurrent_frontier_updates
      (fun n => (seq n).region) (fun n (i : Ind) => range (sphere n i.val)) labels
    · intro n x hx
      rw [(seq n).frontier] at hx
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
      exact mem_iUnion.mpr ⟨⟨i, halive n ▸ hi⟩, hxi⟩
    · intro n i hne
      have hne' : i.val ≠ label n := fun h => hne (Subtype.ext h.symm)
      dsimp only [sphere]
      rw [hunchanged n i.val hne']
    · exact hfilled
    · intro i N
      obtain ⟨n, hn, hgt⟩ := (hfair i.val i.property).exists_gt N
      exact ⟨n, hgt.le, Subtype.ext hn⟩
  have hregions : (⋃ n, (seq n).region) =
      (seq 0).region ∪ ⋃ n, P n '' (univ ×ˢ Icc (0 : ℝ) 1) := by
    apply Subset.antisymm
    · apply iUnion_subset
      intro n
      induction n with
      | zero => exact subset_union_left
      | succ n ih =>
        rw [hrange n]
        exact union_subset ih ((subset_iUnion (fun n => P n '' (univ ×ˢ Icc (0 : ℝ) 1)) n).trans
          subset_union_right)
    · apply union_subset (subset_iUnion (fun n => (seq n).region) 0)
      exact iUnion_subset (fun n => (hcontained n).trans
        (subset_iUnion (fun k => (seq k).region) (n + 1)))
  have hends : (⋃ n, P n '' (univ ×ˢ Icc (0 : ℝ) 1)) =
      ⋃ i : Ind, Θ i '' (univ ×ˢ Ici (0 : ℝ)) := by
    ext x
    constructor
    · intro hx
      obtain ⟨n, hxn⟩ := mem_iUnion.mp hx
      obtain ⟨k, hk⟩ := (hcover (labels n) n).mp rfl
      refine mem_iUnion.mpr ⟨labels n, ?_⟩
      rw [hwhole]
      exact mem_iUnion.mpr ⟨k, hk.symm ▸ hxn⟩
    · intro hx
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
      rw [hwhole] at hxi
      obtain ⟨n, hxn⟩ := mem_iUnion.mp hxi
      exact mem_iUnion.mpr ⟨select i n, hxn⟩
  have hendclosed (i : Ind) : IsClosed (Θ i '' (univ ×ˢ Ici (0 : ℝ))) := by
    have hrange : Θ i '' (univ ×ˢ Ici (0 : ℝ)) =
        range (fun z : Sphere 2 × ℝ≥0 => Θ i (z.1, z.2.val)) := by
      ext x
      constructor
      · rintro ⟨⟨z, t⟩, ⟨_, ht⟩, hx⟩
        exact ⟨(z, ⟨t, ht⟩), hx⟩
      · rintro ⟨⟨z, t⟩, hx⟩
        exact ⟨(z, t.val), ⟨mem_univ _, t.property⟩, hx⟩
    rw [hrange]
    exact (hproper i).isClosed_range
  have hclosed : IsClosed (⋃ n, (seq n).region) := by
    rw [hregions, hends]
    exact (seq 0).compact.isClosed.union (isClosed_iUnion_of_finite hendclosed)
  have hfull : (⋃ n, (seq n).region) = univ :=
    (show IsClopen (⋃ n, (seq n).region) from ⟨hclosed, hopen⟩).eq_univ
      ((seq 0).nonempty.mono (subset_iUnion _ 0))
  have hlowers (n) : P n '' (univ ×ˢ ({0} : Set ℝ)) ⊆ range (sphere n (label n)) := by
    rintro x ⟨⟨z, t⟩, ⟨_, ht⟩, hx⟩
    have : t = 0 := ht
    subst t
    exact ⟨z, (hlower n z).symm.trans hx⟩
  have huppers (n) : P n '' (univ ×ˢ ({1} : Set ℝ)) ⊆ range (sphere (n + 1) (label n)) := by
    rintro x ⟨⟨z, t⟩, ⟨_, ht⟩, hx⟩
    have : t = 1 := ht
    subst t
    exact ⟨z, (hupper n z).symm.trans hx⟩
  have hpair (n) : (range labels).Pairwise
      (fun i j => Disjoint (range (sphere n i.val)) (range (sphere n j.val))) := by
    intro i _ j _ hij
    exact (seq n).disjoint ((halive n).symm ▸ i.property) ((halive n).symm ▸ j.property)
      (fun h => hij (Subtype.ext h))
  have hcross (a b) (hne : labels a ≠ labels b) :
      Disjoint (P a '' (univ ×ˢ Icc (0 : ℝ) 1)) (P b '' (univ ×ˢ Icc (0 : ℝ) 1)) := by
    apply OpenPartialHomeomorph.disjoint_cylinder_images_of_distinct_labels
      labels (fun n (i : Ind) => range (sphere n i.val)) (fun n => (P n).toOpenPartialHomeomorph)
      hsource hlowers huppers ?_ (fun n => (seq n).region) hmono
      hcontained hinter hsphere hfilled hpair a b hne
    intro n i hne
    dsimp only [sphere]
    rw [hunchanged n i.val (fun h => hne (Subtype.ext h.symm))]
  have hdisjoint : Pairwise (fun i j : Ind => Disjoint
      (Θ i '' (univ ×ˢ Ici (0 : ℝ))) (Θ j '' (univ ×ˢ Ici (0 : ℝ)))) := by
    intro i j hij
    rw [hwhole i, hwhole j]
    apply disjoint_iUnion_left.mpr
    intro a
    apply disjoint_iUnion_right.mpr
    intro b
    apply hcross (select i a) (select j b)
    intro h
    have heq := congrArg Subtype.val h
    change label (select i a) = label (select j b) at heq
    rw [hlabel i a, hlabel j b] at heq
    exact hij (Subtype.ext heq)
  have hconnect : IsConnected (seq 0).region := by
    refine ⟨(seq 0).nonempty, ?_⟩
    apply DifferentialGeometry.Topology.isPreconnected_of_finite_closed_attachments
      (fun i : Ind => Θ i '' (univ ×ˢ Ici (0 : ℝ))) (seq 0).compact.isClosed
      hendclosed
    · intro i j hij
      rw [(hdisjoint hij).inter_eq]
      exact empty_subset _
    · intro i
      have hface : range (sphere 0 i.val) ⊆ (seq 0).region := fun x hx =>
        (seq 0).compact.isClosed.frontier_subset
          ((seq 0).frontier.symm ▸ mem_iUnion₂.mpr ⟨i.val, i.property, hx⟩)
      rw [inter_comm, hinitial i, inter_eq_left.mpr hface]
      exact RecordedNeckSphere.isPreconnected_range g eps ((seq 0).sphere i.val)
    · rw [← hends, ← hregions, hfull]
      exact isPreconnected_univ
  refine ⟨seq 0, hsub, hconnect, Θ, ?_, hdisjoint, ?_⟩
  · intro i
    have hface : range (sphere 0 i.val) ⊆ (seq 0).region := fun x hx =>
      (seq 0).compact.isClosed.frontier_subset
        ((seq 0).frontier.symm ▸ mem_iUnion₂.mpr ⟨i.val, i.property, hx⟩)
    refine ⟨hsm i, hinj i, hproper i, hembed i,
      (hinitial i).trans (inter_eq_left.mpr hface), hbase i, hscalar i,
      point (select i 0), neck (select i 0), P (select i 0), ?_,
      hsource (select i 0), hfirst i, hcontrolled (select i 0)⟩
    obtain ⟨z, hz⟩ := hpoint (select i 0)
    refine ⟨z, ?_⟩
    exact (hbase i z).symm.trans ((hfirst i z 0 (by norm_num)).trans
      ((hlower (select i 0) z).trans hz))
  · exact (hregions.trans (congrArg (fun E => (seq 0).region ∪ E) hends)).symm.trans hfull

private theorem NeckFrontierState.exists_proper_end
    [PreconnectedSpace M] [NoncompactSpace M]
    (S₀ : NeckFrontierState g eps ι)
    (heps : eps ≤ Classical.choose (exists_spatial_neck_level_graph_tolerance.{u}))
    (hepsstep : eps ≤ Classical.choose (exists_spatial_neck_finite_frontier_step_tolerance.{u, v}))
    (hepsrec : eps ≤ 1 / 156000)
    (hcompact : ∀ B : ℝ, IsCompact {x : M | Geometry.Curvature.metricScalarAt g x ≤ B})
    (allNeck : ∀ x : M, x ∉ interior S₀.region → Nonempty (SpatialNeck g eps x)) :
    ∃ i ∈ S₀.alive, ∃ Θ : Cylinder → M,
      ContMDiffOn IC I3 ∞ Θ (univ ×ˢ Ici (0 : ℝ)) ∧
      InjOn Θ (univ ×ˢ Ici (0 : ℝ)) ∧
      IsProperMap (fun z : Sphere 2 × ℝ≥0 => Θ (z.1, z.2.val)) ∧
      (let U : TopologicalSpace.Opens Cylinder :=
        ⟨univ ×ˢ Ioi (0 : ℝ), isOpen_univ.prod isOpen_Ioi⟩
       IsSmoothEmbedding IC I3 ∞ (fun z : U => Θ z)) ∧
      Θ '' (univ ×ˢ Ici (0 : ℝ)) ∩ S₀.region = range (S₀.sphere i).map ∧
      (∀ z, Θ (z, 0) = RecordedNeckSphere.map g eps (S₀.sphere i) z) ∧
      (∀ B : ℝ, ∃ T : ℝ≥0, ∀ (z : Sphere 2) (t : ℝ≥0),
        T ≤ t → B < Geometry.Curvature.metricScalarAt g (Θ (z, t.val))) ∧
      ∃ (p : M) (nk : SpatialNeck g eps p) (P : PartialDiffeomorph IC I3 Cylinder M ∞),
        p ∈ range (S₀.sphere i).map ∧
        univ ×ˢ Icc (0 : ℝ) 1 ⊆ P.source ∧
        (∀ z t, t ∈ Icc (0 : ℝ) 1 → Θ (z, t) = P (z, t)) ∧
        P '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆ nk.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) := by
  classical
  obtain ⟨seq, hseq0, hmono, hanti, hsteps, N, hN⟩ :=
    NeckFrontierState.exists_ordinary_tail g eps ι S₀ heps hepsstep allNeck
  let event := fun n => OrdinaryNeckMove g eps ι (seq n) (seq (n + 1))
  have hinfinite : {n | event n}.Infinite :=
    (Ici_infinite N).mono (fun n hn => hN n hn)
  have hreturn (n) (hn : ¬ event n) : (seq (n + 1)).sphere = (seq n).sphere :=
    ((hsteps n).resolve_left hn).2
  obtain ⟨s, hsm, hsevent, _, _, _, hs0, hsucc⟩ :=
    DifferentialGeometry.Topology.exists_strictMono_event_subsequence hinfinite
      (fun n => (seq n).sphere) hreturn
  have hchoice (n) := (hsevent n).2
  choose label hlabel point neck P hsource hrange hlower hupper hunchanged hinter hfilled
    hcontrolled hband hpoint using hchoice
  have hlabels : (range label).Finite := S₀.alive.finite_toSet.subset (by
    rintro i ⟨n, rfl⟩
    rw [← hseq0]
    exact hanti (Nat.zero_le (s n)) (hlabel n))
  let sphere := fun n i => RecordedNeckSphere.map g eps ((seq (s n)).sphere i)
  have hsunchanged (n i) (hni : label n ≠ i) : sphere (n + 1) i = sphere n i := by
    dsimp only [sphere]
    rw [hsucc n, hunchanged n i (Ne.symm hni)]
  have hupper' (n z) : P n (z, 1) = sphere (n + 1) (label n) z := by
    dsimp only [sphere]
    rw [hsucc n]
    exact hupper n z
  have hsmono : Monotone (fun n => (seq (s n)).region) :=
    fun a b hab => hmono (hsm.monotone hab)
  have hcontained (n) : P n '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆ (seq (s (n + 1))).region := by
    apply Subset.trans _ (hmono (Nat.succ_le_of_lt (hsm (Nat.lt_succ_self n))))
    change P n '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆ (seq (s n + 1)).region
    rw [hrange n]
    exact subset_union_right
  have hsphere (n) : range (sphere n (label n)) ⊆ _root_.frontier (seq (s n)).region := by
    intro x hx
    rw [(seq (s n)).frontier]
    exact mem_iUnion₂.mpr ⟨label n, hlabel n, hx⟩
  have hfilled' (n) : range (sphere n (label n)) ⊆ interior (seq (s (n + 1))).region :=
    (hfilled n).trans
      (interior_mono (hmono (Nat.succ_le_of_lt (hsm (Nat.lt_succ_self n)))))
  obtain ⟨i, occurrence, hoccmono, hocclabel, _⟩ :=
    hlabels.exists_strictMono_enumeration_fiber
  have hifiber : {n | label n = i}.Infinite :=
    (Set.infinite_range_of_injective hoccmono.injective).mono (by
      rintro n ⟨m, rfl⟩
      exact hocclabel m)
  obtain ⟨select, _, hsame, _, Θ, hcont, hinj, hproper, hembed, _, hinitial,
    hfirst, hbase, hscalar⟩ :=
    exists_proper_neck_end_of_infinite_updates g hepsrec hcompact label i hifiber sphere
      (fun n => hsunchanged n i) P hsource (fun _ => Diffeomorph.refl I2 (Sphere 2) ∞)
      hlower hupper'
      (fun n => (seq (s n)).region) hsmono hcontained hinter hsphere hfilled'
      point neck hcontrolled hband
  have hilabel : i ∈ S₀.alive := by
    rw [← hseq0]
    have hi := hanti (Nat.zero_le (s (select 0))) (hlabel (select 0))
    simpa only [hsame] using hi
  have hlow : range (S₀.sphere i).map ⊆ S₀.region := fun x hx =>
    S₀.compact.isClosed.frontier_subset (S₀.frontier.symm ▸ mem_iUnion₂.mpr ⟨i, hilabel, hx⟩)
  have hsphere0 : sphere 0 i = (S₀.sphere i).map := by
    dsimp only [sphere]
    rw [hs0, hseq0]
  have hinitial' : Θ '' (univ ×ˢ Ici (0 : ℝ)) ∩ S₀.region = range (S₀.sphere i).map := by
    ext x
    constructor
    · intro hx
      have hx' : x ∈ Θ '' (univ ×ˢ Ici (0 : ℝ)) ∩ (seq (s 0)).region :=
        ⟨hx.1, hmono (Nat.zero_le (s 0)) (by simpa only [hseq0] using hx.2)⟩
      have hxbase := (hinitial ▸ hx').1
      simpa only [hsphere0] using hxbase
    · intro hx
      obtain ⟨z, hz⟩ := hx
      have heq : Θ (z, 0) = RecordedNeckSphere.map g eps (S₀.sphere i) z :=
        (hbase z).trans (congrFun hsphere0 z)
      exact ⟨⟨(z, 0), ⟨mem_univ _, by norm_num⟩, heq.trans hz⟩, hlow ⟨z, hz⟩⟩
  have hbase' (z) : Θ (z, 0) = RecordedNeckSphere.map g eps (S₀.sphere i) z :=
    (hbase z).trans (congrFun hsphere0 z)
  refine ⟨i, hilabel, Θ, hcont, hinj, hproper, hembed, hinitial', hbase', hscalar,
    point (select 0), neck (select 0), P (select 0), ?_, hsource (select 0), hfirst,
    hcontrolled (select 0)⟩
  obtain ⟨z, hz⟩ := hpoint (select 0)
  refine ⟨z, ?_⟩
  exact (hbase' z).symm.trans ((hfirst z 0 (by norm_num)).trans
    ((hlower (select 0) z).trans hz))

theorem exists_spatial_neck_proper_end_with_first_slab_tolerance :
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
          (∀ x : M, x ∉ interior W → Nonempty (SpatialNeck g eps x)) →
          (∀ B : ℝ, IsCompact {x : M | Geometry.Curvature.metricScalarAt g x ≤ B}) →
          ∃ (i : ι) (Θ : Cylinder → M),
            ContMDiffOn IC I3 ∞ Θ (univ ×ˢ Ici (0 : ℝ)) ∧
            InjOn Θ (univ ×ˢ Ici (0 : ℝ)) ∧
            IsProperMap (fun z : Sphere 2 × ℝ≥0 => Θ (z.1, z.2.val)) ∧
            (let U : TopologicalSpace.Opens Cylinder :=
              ⟨univ ×ˢ Ioi (0 : ℝ), isOpen_univ.prod isOpen_Ioi⟩
             IsSmoothEmbedding IC I3 ∞ (fun z : U => Θ z)) ∧
            Θ '' (univ ×ˢ Ici (0 : ℝ)) ∩ W = range (fun z => (neck i).map (z, level i)) ∧
            (∀ z, Θ (z, 0) = (neck i).map (z, level i)) ∧
            (∀ B : ℝ, ∃ T : ℝ≥0, ∀ (z : Sphere 2) (t : ℝ≥0),
              T ≤ t → B < Geometry.Curvature.metricScalarAt g (Θ (z, t.val))) ∧
            ∃ (p : M) (nk : SpatialNeck g eps p)
              (P : PartialDiffeomorph IC I3 Cylinder M ∞),
              p ∈ range (fun z => (neck i).map (z, level i)) ∧
              univ ×ˢ Icc (0 : ℝ) 1 ⊆ P.source ∧
              (∀ z t, t ∈ Icc (0 : ℝ) 1 → Θ (z, t) = P (z, t)) ∧
              P '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆
                nk.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) := by
  classical
  let eta₁ := Classical.choose (exists_spatial_neck_level_graph_tolerance.{u})
  let eta₂ := Classical.choose (exists_spatial_neck_finite_frontier_step_tolerance.{u, v})
  have heta₁ : 0 < eta₁ :=
    (Classical.choose_spec (exists_spatial_neck_level_graph_tolerance.{u})).1
  have heta₂ : 0 < eta₂ :=
    (Classical.choose_spec (exists_spatial_neck_finite_frontier_step_tolerance.{u, v})).1
  refine ⟨min eta₁ (min eta₂ (1 / 156000)), lt_min heta₁ (lt_min heta₂ (by norm_num)), ?_⟩
  intro eps heps M _ _ _ _ _ _ g W hW hne hreg ι _ point neck level hlevel hpair
    hfront hneck hscalar
  let _ : Fintype ι := Fintype.ofFinite ι
  let sphere : ι → RecordedNeckSphere g eps := fun i =>
    ⟨point i, neck i, level i, hlevel i, Diffeomorph.refl I2 (Sphere 2) ∞⟩
  let S : NeckFrontierState g eps ι :=
    { region := W
      compact := hW
      nonempty := hne
      regular := hreg
      alive := Finset.univ
      sphere := sphere
      frontier := by
        change frontier W = ⋃ i ∈ Finset.univ, range (fun q => (neck i).map (q, level i))
        simpa only [Finset.mem_univ, iUnion_true] using hfront
      disjoint := fun i _ j _ hij => hpair hij }
  obtain ⟨i, _, Θ, hsm, hinj, hproper, hembed, hinitial, hbase, hdiverge, hfirst⟩ :=
    NeckFrontierState.exists_proper_end g eps ι S
      (heps.trans (min_le_left _ _))
      (heps.trans ((min_le_right _ _).trans (min_le_left _ _)))
      (heps.trans ((min_le_right _ _).trans (min_le_right _ _))) hscalar hneck
  exact ⟨i, Θ, hsm, hinj, hproper, hembed, hinitial, hbase, hdiverge, hfirst⟩

theorem exists_spatial_neck_proper_end_tolerance :
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
          (∀ x : M, x ∉ interior W → Nonempty (SpatialNeck g eps x)) →
          (∀ B : ℝ, IsCompact {x : M | Geometry.Curvature.metricScalarAt g x ≤ B}) →
          ∃ (i : ι) (Θ : Cylinder → M),
            ContMDiffOn IC I3 ∞ Θ (univ ×ˢ Ici (0 : ℝ)) ∧
            InjOn Θ (univ ×ˢ Ici (0 : ℝ)) ∧
            IsProperMap (fun z : Sphere 2 × ℝ≥0 => Θ (z.1, z.2.val)) ∧
            (let U : TopologicalSpace.Opens Cylinder :=
              ⟨univ ×ˢ Ioi (0 : ℝ), isOpen_univ.prod isOpen_Ioi⟩
             IsSmoothEmbedding IC I3 ∞ (fun z : U => Θ z)) ∧
            Θ '' (univ ×ˢ Ici (0 : ℝ)) ∩ W = range (fun z => (neck i).map (z, level i)) ∧
            (∀ z, Θ (z, 0) = (neck i).map (z, level i)) ∧
            ∀ B : ℝ, ∃ T : ℝ≥0, ∀ (z : Sphere 2) (t : ℝ≥0),
              T ≤ t → B < Geometry.Curvature.metricScalarAt g (Θ (z, t.val)) := by
  obtain ⟨eta, heta, h⟩ := exists_spatial_neck_proper_end_with_first_slab_tolerance.{u, v}
  refine ⟨eta, heta, ?_⟩
  intro eps heps M _ _ _ _ _ _ g W hW hne hreg ι _ point neck level hlevel hpair
    hfront hneck hscalar
  obtain ⟨i, Θ, hsm, hinj, hproper, hembed, hinitial, hbase, hdiverge, _⟩ :=
    h eps heps M g W hW hne hreg ι point neck level hlevel hpair hfront hneck hscalar
  exact ⟨i, Θ, hsm, hinj, hproper, hembed, hinitial, hbase, hdiverge⟩

theorem exists_spatial_neck_finite_end_decomposition_tolerance :
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
          (∀ x : M, x ∉ interior W → Nonempty (SpatialNeck g eps x)) →
          (∀ B : ℝ, IsCompact {x : M | Geometry.Curvature.metricScalarAt g x ≤ B}) →
          ∃ (K : Set M) (m : ℕ) (Θ : Fin m → Cylinder → M),
            W ⊆ K ∧ IsCompact K ∧ IsConnected K ∧ closure (interior K) = K ∧ 0 < m ∧
            (∀ i, ContMDiffOn IC I3 ∞ (Θ i) (univ ×ˢ Ici (0 : ℝ)) ∧
              InjOn (Θ i) (univ ×ˢ Ici (0 : ℝ)) ∧
              IsProperMap (fun z : Sphere 2 × ℝ≥0 => Θ i (z.1, z.2.val)) ∧
              (let U : TopologicalSpace.Opens Cylinder :=
                ⟨univ ×ˢ Ioi (0 : ℝ), isOpen_univ.prod isOpen_Ioi⟩
               IsSmoothEmbedding IC I3 ∞ (fun z : U => Θ i z)) ∧
              Θ i '' (univ ×ˢ Ici (0 : ℝ)) ∩ K = range (fun z => Θ i (z, 0)) ∧
              (∀ B : ℝ, ∃ T : ℝ≥0, ∀ (z : Sphere 2) (t : ℝ≥0),
                T ≤ t → B < Geometry.Curvature.metricScalarAt g (Θ i (z, t.val))) ∧
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
  refine ⟨min eta₁ (min eta₂ (1 / 156000)), lt_min heta₁ (lt_min heta₂ (by norm_num)), ?_⟩
  intro eps heps M _ _ _ _ _ _ g W hW hne hreg ι _ point neck level hlevel hpair
    hfront hneck hscalar
  let _ : Fintype ι := Fintype.ofFinite ι
  let sphere : ι → RecordedNeckSphere g eps := fun i =>
    ⟨point i, neck i, level i, hlevel i, Diffeomorph.refl I2 (Sphere 2) ∞⟩
  let S : NeckFrontierState g eps ι :=
    { region := W
      compact := hW
      nonempty := hne
      regular := hreg
      alive := Finset.univ
      sphere := sphere
      frontier := by
        change frontier W = ⋃ i ∈ Finset.univ, range (fun q => (neck i).map (q, level i))
        simpa only [Finset.mem_univ, iUnion_true] using hfront
      disjoint := fun i _ j _ hij => hpair hij }
  obtain ⟨T, hsub, hconnect, Θ, hends, hdisjoint, hfull⟩ :=
    NeckFrontierState.exists_end_family g eps ι S
      (heps.trans (min_le_left _ _))
      (heps.trans ((min_le_right _ _).trans (min_le_left _ _)))
      (heps.trans ((min_le_right _ _).trans (min_le_right _ _))) hscalar hneck
  let Ind := {i // i ∈ T.alive}
  let _ : Fintype Ind := T.alive.fintypeCoeSort
  let e : Ind ≃ Fin (Fintype.card Ind) := Fintype.equivFin Ind
  let ends (i : Fin (Fintype.card Ind)) := Θ (e.symm i)
  have hneI : Nonempty Ind := (NeckFrontierState.alive_nonempty g eps ι T).to_subtype
  let _ : Nonempty Ind := hneI
  have hbase (i : Ind) : range (fun z => Θ i (z, 0)) = range (T.sphere i.val).map :=
    congrArg range (funext (hends i).2.2.2.2.2.1)
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
  refine ⟨T.region, Fintype.card Ind, ends, hsub, T.compact, hconnect, T.regular,
    Fintype.card_pos, ?_, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨hsm, hinj, hp, he, hi, hb, hd, p, nk, P, hpoint, hsource, hfirst, hcontrolled⟩ :=
      hends (e.symm i)
    refine ⟨hsm, hinj, hp, he, hi.trans (hbase _).symm, hd, p, nk, P, ?_,
      hsource, hfirst, hcontrolled⟩
    exact (hbase _).symm ▸ hpoint
  · intro i j hij
    exact hdisjoint (fun h => hij (e.symm.injective h))
  · rw [T.frontier]
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
      rw [show range (fun z => ends i (z, 0)) = range (T.sphere (e.symm i).val).map from
        hbase (e.symm i)] at hxi
      exact mem_iUnion₂.mpr ⟨(e.symm i).val, (e.symm i).property, hxi⟩
  · rw [hindices]
    exact hfull

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
