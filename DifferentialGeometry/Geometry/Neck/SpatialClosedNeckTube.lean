import DifferentialGeometry.Geometry.Neck.SpatialFrontierStep
import DifferentialGeometry.Geometry.Neck.SpatialFrontierOrientation
import DifferentialGeometry.Geometry.Neck.SpatialFreshBand
import DifferentialGeometry.Topology.Manifold.CylinderCollar.SlabGluing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckRegionBoundary

set_option autoImplicit false
noncomputable section
open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]
  (g : SmoothRiemannianMetric I3 M) {eps : ℝ} {p₀ : M}
  (initial : SpatialNeck g eps p₀)

private structure NeckTube where
  map : PartialDiffeomorph IC I3 Cylinder M ∞
  source : univ ×ˢ Icc (0 : ℝ) 1 ⊆ map.source
  lower : ∀ q, map (q, 0) = initial.map (q, -1)
  point : M
  neck : SpatialNeck g eps point
  level : ℝ
  level_bound : |level| ≤ 4
  upperParam : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2
  upper : ∀ q, map (q, 1) = neck.map (upperParam q, level)

private def NeckTube.region (T : NeckTube g initial) : Set M :=
  T.map '' (univ ×ˢ Icc (0 : ℝ) 1)

omit [T2Space M] in
private theorem NeckTube.compact (T : NeckTube g initial) : IsCompact T.region :=
  (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
    (T.map.contMDiffOn_toFun.continuousOn.mono T.source)

private theorem NeckTube.regular (T : NeckTube g initial) :
    closure (interior T.region) = T.region := by
  apply T.map.toOpenPartialHomeomorph.closure_interior_image_of_subset_source
    T.source _ T.compact.isClosed
  rw [interior_prod_eq, interior_univ, interior_Icc, closure_prod_eq,
    closure_univ, closure_Ioo zero_ne_one]

private theorem NeckTube.frontier (T : NeckTube g initial) :
    _root_.frontier T.region = range (fun q => initial.map (q, -1)) ∪
      range (fun q => T.neck.map (q, T.level)) := by
  have h := T.map.toOpenPartialHomeomorph.image_frontier_of_subset_source
    T.source (isClosed_univ.prod isClosed_Icc) T.compact.isClosed
  change T.map '' _root_.frontier (univ ×ˢ Icc (0 : ℝ) 1) = _root_.frontier T.region at h
  rw [frontier_univ_prod_eq, frontier_Icc zero_le_one] at h
  rw [← h]
  ext x
  constructor
  · rintro ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩
    rcases ht with ht | ht
    · have ht : t = 0 := ht
      subst t
      exact Or.inl ⟨q, (T.lower q).symm⟩
    · have ht : t = 1 := ht
      subst t
      exact Or.inr ⟨T.upperParam q, (T.upper q).symm⟩
  · rintro (⟨q, hq⟩ | ⟨q, hq⟩)
    · exact ⟨(q, 0), ⟨mem_univ _, Or.inl rfl⟩, (T.lower q).trans hq⟩
    · refine ⟨(T.upperParam.symm q, 1), ⟨mem_univ _, Or.inr rfl⟩, ?_⟩
      have hh := T.upper (T.upperParam.symm q)
      exact hh.trans ((congrArg (fun z => T.neck.map (z, T.level))
        (show T.upperParam (T.upperParam.symm q) = q from
          T.upperParam.apply_symm_apply q)).trans hq)

omit [T2Space M] in
private theorem NeckTube.disjoint_ends (T : NeckTube g initial) :
    Disjoint (range (fun q => initial.map (q, -1)))
      (range (fun q => T.neck.map (q, T.level))) := by
  rw [disjoint_left]
  rintro x ⟨q, hq⟩ ⟨r, hr⟩
  have heq : T.map (q, 0) = T.map (T.upperParam.symm r, 1) :=
    (T.lower q).trans (hq.trans (hr.symm.trans ((congrArg
      (fun z => T.neck.map (z, T.level))
        (show r = T.upperParam (T.upperParam.symm r) from
          (T.upperParam.apply_symm_apply r).symm)).trans (T.upper _).symm)))
  have he := T.map.injOn (T.source ⟨mem_univ _, by norm_num⟩)
    (T.source ⟨mem_univ _, by norm_num⟩) heq
  have hh := congrArg Prod.snd he
  norm_num at hh

private def initialNeckTube : NeckTube g initial := by
  let D := DifferentialGeometry.Geometry.Metric.cylinderAxialDiffeomorph
    (I := I2) (M := Sphere 2) (-1) 1 (by norm_num)
  let P := partialDiffeomorphTransMixed D.toPartialDiffeomorph initial.map
  have hp (q : Sphere 2) (t : ℝ) : P (q, t) = initial.map (q, -1 + t) := by
    change initial.map (q, -1 + 1 * t) = _
    rw [one_mul]
  have hlen : (1 : ℝ) < eps⁻¹ :=
    (one_lt_inv₀ initial.eps_pos).mpr (initial.eps_small.trans (by norm_num))
  refine ⟨P, ?_, ?_, p₀, initial, 0, by norm_num, Diffeomorph.refl I2 (Sphere 2) ∞, ?_⟩
  · intro z hz
    refine ⟨mem_univ _, ?_⟩
    exact initial.domain ⟨mem_univ _, by
      change -eps⁻¹ < -1 + 1 * z.2 ∧ -1 + 1 * z.2 < eps⁻¹
      constructor <;> linarith [hz.2.1, hz.2.2]⟩
  · intro q
    rw [hp, add_zero]
  · intro q
    rw [hp]
    norm_num

private theorem NeckTube.exists_outward_neck
    (eta : ℝ)
    (hgraph : ∀ eps : ℝ, eps ≤ eta →
      ∀ (g : SmoothRiemannianMetric I3 M) (p₀ p₁ : M)
        (nk₀ : SpatialNeck g eps p₀) (nk₁ : SpatialNeck g eps p₁)
        (u₀ u₁ : Sphere 2) (a b : ℝ), |a| ≤ 4 → |b| ≤ 4 →
        nk₀.map (u₀, a) = nk₁.map (u₁, b) →
        ∃ (η : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2) (h : Sphere 2 → ℝ),
          ContMDiff I2 𝓘(ℝ) ∞ h ∧ (∀ q, |h q - b| < 1 / 10) ∧ h u₁ = b ∧
          (∀ q, (q, h q) ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) ∧
          ∀ q, nk₁.map (q, h q) = nk₀.map (η q, a))
    (heps : eps ≤ eta) (allNeck : ∀ x : M, Nonempty (SpatialNeck g eps x))
    (T : NeckTube g initial) :
    ∃ (p : M) (nk : SpatialNeck g eps p) (f : Sphere 2 → ℝ)
      (κ : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2),
      ContMDiff I2 𝓘(ℝ) ∞ f ∧ (∀ q, |f q| < 1 / 10) ∧ f nk.center = 0 ∧
      (∀ q, nk.map (q, f q) = T.map (κ q, 1)) ∧
      _root_.frontier T.region = range (fun q => nk.map (q, f q)) ∪
        range (fun q => initial.map (q, -1)) ∧
      Disjoint (range (fun q => nk.map (q, f q)))
        (range (fun q => initial.map (q, -1))) ∧
      ∃ r > 0, ∀ t, 0 < t → t < r → nk.map (nk.center, t) ∉ T.region := by
  let x := T.neck.map (T.neck.center, T.level)
  obtain ⟨nk₀⟩ := allNeck x
  obtain ⟨η, h, hh, hsmall, hzero, _, heq⟩ :=
    hgraph eps heps g T.point x T.neck nk₀ T.neck.center nk₀.center T.level 0
      T.level_bound (by norm_num) nk₀.center_eq.symm
  simp only [sub_zero] at hsmall
  have hrange : range (fun q => nk₀.map (q, h q)) =
      range (fun q => T.neck.map (q, T.level)) := by
    ext y
    constructor
    · rintro ⟨q, hq⟩
      exact ⟨η q, (heq q).symm.trans hq⟩
    · rintro ⟨q, hq⟩
      refine ⟨η.symm q, (heq _).trans ?_⟩
      exact (congrArg (fun z => T.neck.map (z, T.level))
        (show η (η.symm q) = q from η.apply_symm_apply q)).trans hq
  have hfront : _root_.frontier T.region = range (fun q => nk₀.map (q, h q)) ∪
      range (fun q => initial.map (q, -1)) := by
    rw [hrange, union_comm]
    exact T.frontier
  have hdis : Disjoint (range (fun q => nk₀.map (q, h q)))
      (range (fun q => initial.map (q, -1))) := hrange.symm ▸ T.disjoint_ends.symm
  have hS : IsClosed (range (fun q => initial.map (q, -1))) := by
    apply IsCompact.isClosed
    apply isCompact_range
    have hlen : (1 : ℝ) < eps⁻¹ :=
      (one_lt_inv₀ initial.eps_pos).mpr (initial.eps_small.trans (by norm_num))
    exact initial.map.contMDiffOn_toFun.continuousOn.comp_continuous
      (continuous_id.prodMk continuous_const)
      (fun q => initial.domain ⟨mem_univ _, by constructor <;> linarith⟩)
  obtain ⟨nk, f, _, hf, hfsmall, hfzero, hphysical, hout⟩ :=
    nk₀.exists_outward_graph_orientation h hh hsmall hzero T.regular hS hfront hdis
  let κ := η.trans T.upperParam.symm
  have hmap (q : Sphere 2) : nk.map (q, f q) = T.map (κ q, 1) := by
    rw [hphysical, heq, T.upper]
    exact congrArg (fun z => T.neck.map (z, T.level))
      (show η q = T.upperParam (T.upperParam.symm (η q)) from
        (T.upperParam.apply_symm_apply _).symm)
  have hequal : (fun q => nk.map (q, f q)) = (fun q => nk₀.map (q, h q)) := funext hphysical
  refine ⟨x, nk, f, κ, hf, hfsmall, hfzero, hmap, ?_, ?_, hout⟩
  · rw [hequal]
    exact hfront
  · rw [hequal]
    exact hdis

private def NeckTube.ClosedBy (T : NeckTube g initial) : Prop :=
  ∃ (η κ : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2)
    (A : PartialDiffeomorph IC I3 Cylinder M ∞),
    univ ×ˢ Icc (0 : ℝ) 1 ⊆ A.source ∧
    (∀ q, A (q, 0) = T.map (κ q, 1)) ∧
    (∀ q, A (q, 1) = initial.map (η q, -1)) ∧
    A '' (univ ×ˢ Icc (0 : ℝ) 1) ∩ T.region = _root_.frontier T.region ∧
    T.region ∪ A '' (univ ×ˢ Icc (0 : ℝ) 1) = univ

private def NeckTube.Advances (T U : NeckTube g initial) : Prop :=
  T.region ⊆ U.region ∧ ∃ (p : M) (nk : SpatialNeck g eps p),
    nk.map '' (univ ×ˢ Icc (1 : ℝ) 2) ⊆ U.region \ T.region

private theorem NeckTube.advance_or_close
    [PreconnectedSpace M]
    (heps : eps ≤ (Classical.choose (exists_spatial_neck_level_graph_tolerance.{u})))
    (hepsstep : eps ≤ (Classical.choose (exists_spatial_neck_advance_or_return_tolerance.{u})))
    (allNeck : ∀ x : M, Nonempty (SpatialNeck g eps x)) (T : NeckTube g initial) :
    NeckTube.ClosedBy g initial T ∨
      ∃ U : NeckTube g initial, NeckTube.Advances g initial T U := by
  have hgraph := (Classical.choose_spec (exists_spatial_neck_level_graph_tolerance.{u})).2
  obtain ⟨p, nk, f, κ, hf, hsmall, hzero, hmap, hfront, hdis, hout⟩ :=
    NeckTube.exists_outward_neck g initial _ (fun e he => hgraph e he M) heps allNeck T
  have hstep := (Classical.choose_spec (exists_spatial_neck_advance_or_return_tolerance.{u})).2
  rcases hstep eps hepsstep M g p p₀ nk initial f hf hsmall hzero T.region (-1)
    (by norm_num) T.regular hfront hdis hout with hadvance | hclose
  · right
    obtain ⟨A, hA, _, hA0, hA1, _, hinter, _, _, hfresh⟩ := hadvance
    have hmatch (q : Sphere 2) : A (q, 0) = T.map (κ q, 1) := (hA0 q).trans (hmap q)
    have hupper_range : range (fun q => nk.map (q, f q)) =
        T.map '' (univ ×ˢ ({1} : Set ℝ)) := by
      ext x
      constructor
      · rintro ⟨q, hq⟩
        exact ⟨(κ q, 1), ⟨mem_univ _, rfl⟩, (hmap q).symm.trans hq⟩
      · rintro ⟨⟨q, t⟩, ⟨_, ht⟩, hq⟩
        have : t = 1 := ht
        subst t
        refine ⟨κ.symm q, (hmap _).trans ?_⟩
        exact (congrArg (fun z => T.map (z, 1))
          (show κ (κ.symm q) = q from κ.apply_symm_apply q)).trans hq
    have hmeet : T.map '' (univ ×ˢ Icc (0 : ℝ) 1) ∩
        A '' (univ ×ˢ Icc (0 : ℝ) 1) = T.map '' (univ ×ˢ ({1} : Set ℝ)) := by
      rw [inter_comm]
      exact hinter.trans hupper_range
    obtain ⟨R, hR, hrange, hlower, hupper, _, _⟩ :=
      DifferentialGeometry.Topology.Manifold.exists_unit_slab_concatenation T.map A κ
        T.source hA hmatch hmeet
    let U : NeckTube g initial :=
      ⟨R, hR, fun q => (hlower q).trans (T.lower q), p, nk, 3,
        by norm_num, κ.symm, fun q => (hupper q).trans (hA1 (κ.symm q))⟩
    have hU : U.region = T.region ∪ A '' (univ ×ˢ Icc (0 : ℝ) 1) := hrange
    refine ⟨U, ?_, p, nk, ?_⟩
    · rw [hU]
      exact subset_union_left
    · exact fun x hx => ⟨hU.symm ▸ Or.inr (hfresh hx).1, (hfresh hx).2⟩
  · left
    obtain ⟨η, A, hA, hA0, hA1, _, hinter, hcover⟩ := hclose
    exact ⟨η, κ, A, hA, fun q => (hA0 q).trans (hmap q), hA1, hinter, hcover⟩

private theorem exists_closed_neck_tube
    [PreconnectedSpace M] [CompactSpace M]
    (heps : eps ≤ Classical.choose (exists_spatial_neck_level_graph_tolerance.{u}))
    (hepsstep : eps ≤ Classical.choose (exists_spatial_neck_advance_or_return_tolerance.{u}))
    (hepsrec : eps ≤ 1 / 156000)
    (allNeck : ∀ x : M, Nonempty (SpatialNeck g eps x)) :
    ∃ T : NeckTube g initial, NeckTube.ClosedBy g initial T := by
  classical
  by_contra hclosed
  have hnext (T : NeckTube g initial) : ∃ U, NeckTube.Advances g initial T U := by
    rcases NeckTube.advance_or_close g initial heps hepsstep allNeck T with h | h
    · exact (hclosed ⟨T, h⟩).elim
    · exact h
  choose next hstep using hnext
  let seq : ℕ → NeckTube g initial := fun n => next^[n] (initialNeckTube g initial)
  have hseq (n : ℕ) : seq (n + 1) = next (seq n) := Function.iterate_succ_apply' _ _ _
  have hinc (n : ℕ) : (seq n).region ⊆ (seq (n + 1)).region := by
    rw [hseq]
    exact (hstep (seq n)).1
  have hmono : Monotone (fun n => (seq n).region) := monotone_nat_of_le_succ hinc
  have hfresh (n : ℕ) : ∃ (p : M) (nk : SpatialNeck g eps p),
      nk.map '' (univ ×ˢ Icc (1 : ℝ) 2) ⊆ (seq (n + 1)).region \ (seq n).region := by
    rw [hseq]
    exact (hstep (seq n)).2
  choose p neck hband using hfresh
  exact not_forall_spatial_neck_unit_band_subset_sdiff g isCompact_univ hepsrec p neck
    (fun _ => mem_univ _) (fun n => (seq n).region) hmono hband

theorem exists_spatial_neck_two_cylinders_tolerance :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ eps : ℝ, eps ≤ eta →
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M] [PreconnectedSpace M] [CompactSpace M]
          (g : SmoothRiemannianMetric I3 M) (p : M) (initial : SpatialNeck g eps p),
          (∀ x : M, Nonempty (SpatialNeck g eps x)) →
          ∃ (P A : PartialDiffeomorph IC I3 Cylinder M ∞)
            (η κ : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2),
            univ ×ˢ Icc (0 : ℝ) 1 ⊆ P.source ∧
            univ ×ˢ Icc (0 : ℝ) 1 ⊆ A.source ∧
            (∀ q, P (q, 0) = initial.map (q, -1)) ∧
            (∀ q, A (q, 0) = P (κ q, 1)) ∧
            (∀ q, A (q, 1) = P (η q, 0)) ∧
            A '' (univ ×ˢ Icc (0 : ℝ) 1) ∩ P '' (univ ×ˢ Icc (0 : ℝ) 1) =
              P '' (univ ×ˢ ({0, 1} : Set ℝ)) ∧
            P '' (univ ×ˢ Icc (0 : ℝ) 1) ∪ A '' (univ ×ˢ Icc (0 : ℝ) 1) = univ := by
  let eta₀ := Classical.choose (exists_spatial_neck_level_graph_tolerance.{u})
  let eta₁ := Classical.choose (exists_spatial_neck_advance_or_return_tolerance.{u})
  have h₀ : 0 < eta₀ := (Classical.choose_spec (exists_spatial_neck_level_graph_tolerance.{u})).1
  have h₁ : 0 < eta₁ :=
    (Classical.choose_spec (exists_spatial_neck_advance_or_return_tolerance.{u})).1
  refine ⟨min eta₀ (min eta₁ (1 / 156000)), lt_min h₀ (lt_min h₁ (by norm_num)), ?_⟩
  intro eps heps M _ _ _ _ _ _ g p initial hneck
  obtain ⟨T, η, κ, A, hA, hA0, hA1, hinter, hcover⟩ :=
    exists_closed_neck_tube g initial (heps.trans (min_le_left _ _))
      (heps.trans ((min_le_right _ _).trans (min_le_left _ _)))
      (heps.trans ((min_le_right _ _).trans (min_le_right _ _))) hneck
  refine ⟨T.map, A, η, κ, T.source, hA, T.lower, hA0, ?_, ?_, hcover⟩
  · intro q
    exact (hA1 q).trans (T.lower (η q)).symm
  · have hf := T.map.toOpenPartialHomeomorph.image_frontier_of_subset_source
      T.source (isClosed_univ.prod isClosed_Icc) T.compact.isClosed
    change T.map '' _root_.frontier (univ ×ˢ Icc (0 : ℝ) 1) =
      _root_.frontier T.region at hf
    rw [frontier_univ_prod_eq, frontier_Icc zero_le_one] at hf
    exact hinter.trans hf.symm

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
