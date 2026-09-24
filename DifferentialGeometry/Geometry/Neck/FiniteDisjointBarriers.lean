import DifferentialGeometry.Geometry.Neck.SpatialHalfCollarSeparation
import DifferentialGeometry.Geometry.Neck.DisjointSphereAnnulus
import DifferentialGeometry.Topology.OpenPartialHomeomorph.HalfCollarRetraction
import DifferentialGeometry.Geometry.Neck.SpatialBarrierCollar

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {p : M}

private def SpatialNeck.signedLevelChart (nk : SpatialNeck g eps p)
    (a ν : ℝ) (hν : ν = 1 ∨ ν = -1) : OpenPartialHomeomorph Cylinder M :=
  let H : Cylinder ≃ₜ Cylinder :=
    { toFun := fun z => (z.1, a + ν * z.2)
      invFun := fun z => (z.1, ν * (z.2 - a))
      left_inv := by
        intro z
        apply Prod.ext
        · rfl
        · rcases hν with rfl | rfl <;> ring
      right_inv := by
        intro z
        apply Prod.ext
        · rfl
        · rcases hν with rfl | rfl <;> ring
      continuous_toFun := continuous_fst.prodMk
        (continuous_const.add (continuous_const.mul continuous_snd))
      continuous_invFun := continuous_fst.prodMk
        (continuous_const.mul (continuous_snd.sub continuous_const)) }
  H.transOpenPartialHomeomorph nk.map.toOpenPartialHomeomorph

private theorem SpatialNeck.signedLevelChart_apply (nk : SpatialNeck g eps p)
    (a ν : ℝ) (hν : ν = 1 ∨ ν = -1) (z : Cylinder) :
    nk.signedLevelChart a ν hν z = nk.map (z.1, a + ν * z.2) := rfl

private theorem SpatialNeck.signedLevelChart_source (nk : SpatialNeck g eps p)
    (a ν : ℝ) (hν : ν = 1 ∨ ν = -1) (ha : |a| ≤ 3) :
    univ ×ˢ Icc (0 : ℝ) (1 / 2) ⊆ (nk.signedLevelChart a ν hν).source := by
  have hlen : (4 : ℝ) < eps⁻¹ :=
    (lt_inv_comm₀ (by norm_num) nk.eps_pos).mpr (by linarith [nk.eps_small])
  rintro ⟨q, t⟩ ⟨_, ht⟩
  change (q, a + ν * t) ∈ nk.map.source
  apply nk.domain
  refine ⟨mem_univ _, ?_, ?_⟩ <;> rcases hν with rfl | rfl <;>
    nlinarith [(abs_le.mp ha).1, (abs_le.mp ha).2, ht.1, ht.2]

private theorem SpatialNeck.signedLevelChart_image (nk : SpatialNeck g eps p)
    (a ν : ℝ) (hν : ν = 1 ∨ ν = -1) (D : Set ℝ) :
    nk.signedLevelChart a ν hν '' (univ ×ˢ D) =
      nk.map '' {z : Cylinder | ν * (z.2 - a) ∈ D} := by
  ext x
  constructor
  · rintro ⟨⟨q, t⟩, ht, rfl⟩
    refine ⟨(q, a + ν * t), ?_, rfl⟩
    change ν * (a + ν * t - a) ∈ D
    have heq : ν * (a + ν * t - a) = t := by rcases hν with rfl | rfl <;> ring
    exact heq.symm ▸ ht.2
  · rintro ⟨⟨q, t⟩, ht, rfl⟩
    refine ⟨(q, ν * (t - a)), ⟨mem_univ _, ht⟩, ?_⟩
    rw [nk.signedLevelChart_apply]
    have heq : a + ν * (ν * (t - a)) = t := by rcases hν with rfl | rfl <;> ring
    rw [heq]


universe u v

private theorem exists_spatial_neck_complement_retraction_tolerance :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ eps : ℝ, eps ≤ eta →
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M]
          (g : SmoothRiemannianMetric I3 M) (ι : Type v) [Finite ι] (p : ι → M)
          (nk : ∀ i, SpatialNeck g eps (p i)) (a : ι → ℝ),
          (∀ i, |a i| ≤ 3) →
          Pairwise (fun i j => Disjoint (range (fun q : Sphere 2 => (nk i).map (q, a i)))
            (range (fun q : Sphere 2 => (nk j).map (q, a j)))) →
          ∀ (A : ℝ) (x : M), (∀ i, A < (1 - 4323 * eps) * metricScalarAt g (p i)) →
            metricScalarAt g x ≤ A →
            let V := connectedComponentIn (⋃ i, range (fun q : Sphere 2 => (nk i).map (q, a i)))ᶜ x
            let K := ⋃ i, (nk i).map '' (univ ×ˢ Icc (-4 : ℝ) 4)
            ∃ f : M → M, ContinuousOn f V ∧ f x = x ∧
              f '' V ⊆ V \ ⋃ i, (nk i).map '' (univ ×ˢ Ioo (a i - 1 / 100) (a i + 1 / 100)) ∧
              EqOn f id Kᶜ ∧ IsCompact K := by
  obtain ⟨eta₀, heta₀, hcomponent⟩ := exists_spatial_neck_complement_half_collar_tolerance.{u, v}
  obtain ⟨eta₁, heta₁, hseparate⟩ := exists_spatial_neck_disjoint_half_collars_tolerance.{u}
  obtain ⟨eta₂, heta₂, hcover⟩ := exists_spatial_neck_half_collar_cover_tolerance.{u, v}
  refine ⟨min eta₀ (min eta₁ eta₂), lt_min heta₀ (lt_min heta₁ heta₂), ?_⟩
  intro eps heps M _ _ _ _ g ι _ p nk a ha hdis A x hA hx V K
  classical
  let _ := Fintype.ofFinite ι
  let ν : Bool → ℝ := fun b => if b then 1 else - 1
  have hν (b : Bool) : ν b = 1 ∨ ν b = -1 := by cases b <;> simp [ν]
  let T : ι × Bool → OpenPartialHomeomorph Cylinder M :=
    fun j => (nk j.1).signedLevelChart (a j.1) (ν j.2) (hν j.2)
  let J : Finset (ι × Bool) := Finset.univ.filter (fun j =>
    ∀ r : ℝ, 0 < r → ∃ q : Sphere 2, ∃ t ∈ Ioo (0 : ℝ) r,
      (nk j.1).map (q, a j.1 + ν j.2 * t) ∈ V)
  by_cases hn : Nonempty ι
  swap
  · let _ : IsEmpty ι := not_nonempty_iff.mp hn
    refine ⟨id, continuous_id.continuousOn, rfl, ?_, ?_, ?_⟩
    · simpa only [image_id, iUnion_of_empty, sdiff_empty] using (subset_rfl : V ⊆ V)
    · exact fun _ _ => rfl
    · simp [K]
  let _ := hn
  have hlen : (4 : ℝ) < eps⁻¹ :=
    (lt_inv_comm₀ (by norm_num) (nk (Classical.choice hn)).eps_pos).mpr
      (by linarith [(nk (Classical.choice hn)).eps_small])
  have hsource4 (i : ι) : univ ×ˢ Icc (-4 : ℝ) 4 ⊆ (nk i).map.source := by
    intro z hz
    exact (nk i).domain ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  have hhigh (i : ι) (z : M) (hz : z ∈ (nk i).map '' (univ ×ˢ Icc (-4 : ℝ) 4)) :
      A < metricScalarAt g z := by
    obtain ⟨w, hw, rfl⟩ := hz
    exact (hA i).trans_le ((nk i).scalar_bounds_on_image_window
      ⟨w, ⟨hw.1, by linarith [hw.2.1], by linarith [hw.2.2]⟩, rfl⟩).1
  have hxoutside : x ∉ ⋃ i, range (fun q : Sphere 2 => (nk i).map (q, a i)) := by
    intro hh
    obtain ⟨i, hi⟩ := mem_iUnion.mp hh
    obtain ⟨q, hq⟩ := hi
    exact (not_lt_of_ge hx) (hhigh i x
      ⟨(q, a i), ⟨mem_univ _, by linarith [(abs_le.mp (ha i)).1],
        by linarith [(abs_le.mp (ha i)).2]⟩, hq⟩)
  have hxV : x ∈ V := mem_connectedComponentIn hxoutside
  have hVlow : (V ∩ {z | metricScalarAt g z ≤ A}).Nonempty := ⟨x, hxV, hx⟩
  have hVavoid (i : ι) : Disjoint V (range fun q : Sphere 2 => (nk i).map (q, a i)) :=
    disjoint_left.mpr (fun z hz hi => connectedComponentIn_subset _ x hz (mem_iUnion.mpr ⟨i, hi⟩))
  have hTsource (j : ι × Bool) : univ ×ˢ Icc (0 : ℝ) (1 / 2) ⊆ (T j).source :=
    (nk j.1).signedLevelChart_source (a j.1) (ν j.2) (hν j.2) (ha j.1)
  have hTzero (j : ι × Bool) : Disjoint (range fun q : Sphere 2 => T j (q, 0)) V := by
    simpa only [T, SpatialNeck.signedLevelChart_apply, mul_zero, add_zero] using (hVavoid j.1).symm
  have hTpos (j : ι × Bool) (hj : j ∈ J) : T j '' (univ ×ˢ Ioo (0 : ℝ) (1 / 2)) ⊆ V := by
    rw [show T j = (nk j.1).signedLevelChart (a j.1) (ν j.2) (hν j.2) from rfl,
      SpatialNeck.signedLevelChart_image]
    exact hcomponent eps (heps.trans (min_le_left _ _)) M g ι p nk a ha hdis
      j.1 (ν j.2) A x (hν j.2) (hA j.1) hVlow (Finset.mem_filter.mp hj).2
  have hTK (j : ι × Bool) : T j '' (univ ×ˢ Icc (0 : ℝ) (1 / 8)) ⊆ K := by
    rw [show T j = (nk j.1).signedLevelChart (a j.1) (ν j.2) (hν j.2) from rfl,
      SpatialNeck.signedLevelChart_image]
    rintro z ⟨w, hw, rfl⟩
    apply mem_iUnion.mpr
    refine ⟨j.1, w, ⟨mem_univ _, ?_, ?_⟩, rfl⟩ <;>
      rcases hν j.2 with h | h <;> rw [h] at hw <;>
        nlinarith [hw.1, hw.2, (abs_le.mp (ha j.1)).1, (abs_le.mp (ha j.1)).2]
  have hTdis : (J : Set (ι × Bool)).Pairwise fun i j =>
      Disjoint (V ∩ T i '' (univ ×ˢ Icc (0 : ℝ) (1 / 8)))
        (V ∩ T j '' (univ ×ˢ Icc (0 : ℝ) (1 / 8))) := by
    intro i hi j hj hij
    by_cases hindex : i.1 = j.1
    · rw [disjoint_left]
      rintro z ⟨hzV, ⟨wi, hwi, hiz⟩⟩ ⟨_, ⟨wj, hwj, hjz⟩⟩
      have hmap : (nk i.1).map (wi.1, a i.1 + ν i.2 * wi.2) =
          (nk i.1).map (wj.1, a i.1 + ν j.2 * wj.2) := by
        have hh := hiz.trans hjz.symm
        change (nk i.1).map (wi.1, a i.1 + ν i.2 * wi.2) =
          (nk j.1).map (wj.1, a j.1 + ν j.2 * wj.2) at hh
        rw [← hindex] at hh
        exact hh
      have hisrc := hTsource i ⟨hwi.1, hwi.2.1, hwi.2.2.trans (by norm_num)⟩
      have hjsrc := hTsource j ⟨hwj.1, hwj.2.1, hwj.2.2.trans (by norm_num)⟩
      change (wi.1, a i.1 + ν i.2 * wi.2) ∈ (nk i.1).map.source at hisrc
      change (wj.1, a j.1 + ν j.2 * wj.2) ∈ (nk j.1).map.source at hjsrc
      rw [← hindex] at hjsrc
      have heq := congrArg Prod.snd ((nk i.1).map.injOn hisrc hjsrc hmap)
      have hsignne : i.2 ≠ j.2 := fun h => hij (Prod.ext hindex h)
      have hzero : wi.2 = 0 := by
        cases hi' : i.2 <;> cases hj' : j.2 <;> simp [hi', hj', ν] at hsignne heq <;>
          nlinarith [hwi.2.1, hwj.2.1]
      apply disjoint_left.mp (hTzero i) ?_ hzV
      refine ⟨wi.1, ?_⟩
      have hwi0 : wi = (wi.1, 0) := Prod.ext rfl hzero
      change T i (wi.1, 0) = z
      rw [← hwi0]
      exact hiz
    · have hVboth : Disjoint V (range (fun q : Sphere 2 => (nk i.1).map (q, a i.1)) ∪
          range (fun q : Sphere 2 => (nk j.1).map (q, a j.1))) := disjoint_union_right.mpr
            ⟨hVavoid i.1, hVavoid j.1⟩
      have hsmall := hseparate eps (heps.trans ((min_le_right _ _).trans (min_le_left _ _)))
        M g (p i.1) (p j.1) (nk i.1) (nk j.1) (a i.1) (a j.1) (ν i.2) (ν j.2) A
        (ha i.1) (ha j.1) (hν i.2) (hν j.2) (hA i.1) (hA j.1) (hdis hindex)
        V isPreconnected_connectedComponentIn hVlow hVboth
        (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
      have heq (k : ι × Bool) := (nk k.1).signedLevelChart_image (a k.1) (ν k.2) (hν k.2)
        (Icc (0 : ℝ) (1 / 8))
      have hTsmall : Disjoint (T i '' (univ ×ˢ Icc (0 : ℝ) (1 / 8)))
          (T j '' (univ ×ˢ Icc (0 : ℝ) (1 / 8))) := by
        change Disjoint ((nk i.1).signedLevelChart _ _ _ '' _)
          ((nk j.1).signedLevelChart _ _ _ '' _)
        rw [heq i, heq j]
        exact hsmall
      exact hTsmall.mono inter_subset_right inter_subset_right
  obtain ⟨f, hf, hmap, hfix, himage⟩ := OpenPartialHomeomorph.exists_finite_half_collar_retraction
    J T (fun _ => (1 / 2 : ℝ)) (fun _ => (1 / 8 : ℝ)) (by intros; norm_num)
    (by intros; norm_num) (fun j _ => hTsource j) (fun j _ => hTzero j) hTpos hTdis
  have hremove : (⋃ j ∈ J, T j '' (univ ×ˢ Ioo (0 : ℝ) (1 / 8))) ⊆ K := by
    intro z hz
    obtain ⟨j, _, hj⟩ := mem_iUnion₂.mp hz
    exact hTK j (image_mono (prod_mono subset_rfl Ioo_subset_Icc_self) hj)
  have hxK : x ∉ K := by
    intro hh
    obtain ⟨i, hi⟩ := mem_iUnion.mp hh
    exact (not_lt_of_ge hx) (hhigh i x hi)
  refine ⟨f, hf, hfix (fun hxrem => hxK (hremove hxrem)), ?_,
    (fun z hz => hfix (fun hrem => hz (hremove hrem))), ?_⟩
  · rintro z ⟨w, hw, rfl⟩
    obtain ⟨hfwV, hfwavoid⟩ := hmap hw
    refine ⟨hfwV, ?_⟩
    intro hthinpoint
    obtain ⟨i, q, hq, heq⟩ := mem_iUnion.mp hthinpoint
    have hyoutside : (nk i).map q ∉ ⋃ j ∈ (Finset.univ : Finset ι),
        range (fun w : Sphere 2 => (nk j).map (w, a j)) := by
      simp only [Finset.mem_univ, iUnion_true]
      exact connectedComponentIn_subset _ x (heq.symm ▸ hfwV)
    obtain ⟨j, hj, ν', hν', hpoint, hgerm⟩ := hcover eps
      (heps.trans ((min_le_right _ _).trans (min_le_right _ _))) M g ι p nk a Finset.univ
      (fun i _ => ha i) i (Finset.mem_univ _) q.1 (q.2 - a i)
      (by rw [abs_lt]; exact ⟨by linarith [hq.2.1], by linarith [hq.2.2]⟩)
      (by simpa only [add_sub_cancel] using hyoutside)
    have hcomp : connectedComponentIn
        (⋃ j ∈ (Finset.univ : Finset ι), range (fun w : Sphere 2 => (nk j).map (w, a j)))ᶜ
        ((nk i).map (q.1, a i + (q.2 - a i))) = V := by
      simp only [Finset.mem_univ, iUnion_true, add_sub_cancel]
      exact (connectedComponentIn_eq (heq.symm ▸ hfwV)).symm
    rw [hcomp] at hgerm
    obtain ⟨b, hb⟩ : ∃ b : Bool, ν b = ν' := by
      rcases hν' with h | h
      · exact ⟨true, by simpa [ν] using h.symm⟩
      · exact ⟨false, by simpa [ν] using h.symm⟩
    have hjJ : (j, b) ∈ J :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa only [hb] using hgerm⟩
    apply hfwavoid
    refine mem_iUnion₂.mpr ⟨(j, b), hjJ, ?_⟩
    rw [show T (j, b) = (nk j).signedLevelChart (a j) (ν b) (hν b) from rfl,
      SpatialNeck.signedLevelChart_image]
    simpa only [hb, add_sub_cancel, heq, mem_Ioo] using hpoint
  · exact isCompact_iUnion (fun i => (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
      ((nk i).map.contMDiffOn_toFun.continuousOn.mono (hsource4 i)))


theorem exists_finite_disjoint_spatial_neck_barriers_tolerance :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ eps : ℝ, eps ≤ eta →
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M]
          (g : SmoothRiemannianMetric I3 M) (ι : Type v) (p : ι → M)
          (nk : ∀ i, SpatialNeck g eps (p i)) (a : ι → ℝ) (s : Finset ι),
          (∀ i ∈ s, |a i| ≤ 3) →
          ∀ (A : ℝ) (P : Set M), (∀ i ∈ s, A < (1 - 4323 * eps) * metricScalarAt g (p i)) →
            (∀ x ∈ P, metricScalarAt g x ≤ A →
              IsCompact (closure (connectedComponentIn
                (⋃ i ∈ s, range (fun q : Sphere 2 => (nk i).map (q, a i)))ᶜ x))) →
            ∃ t : Finset ι, t ⊆ s ∧
              (t : Set ι).PairwiseDisjoint
                (fun i => range (fun q : Sphere 2 => (nk i).map (q, a i))) ∧
              (∀ u : Finset ι, u ⊆ s →
                (u : Set ι).PairwiseDisjoint
                  (fun i => range (fun q : Sphere 2 => (nk i).map (q, a i))) →
                u.card ≤ t.card) ∧
              (s.Nonempty → t.Nonempty) ∧
              ∀ x ∈ P, metricScalarAt g x ≤ A →
                let V := connectedComponentIn
                  (⋃ i ∈ t, range (fun q : Sphere 2 => (nk i).map (q, a i)))ᶜ x
                let W := connectedComponentIn
                  (⋃ i ∈ s, range (fun q : Sphere 2 => (nk i).map (q, a i)))ᶜ x
                IsCompact (closure V) ∧
                closure V ⊆ closure W ∪ ⋃ i ∈ t, (nk i).map '' (univ ×ˢ Icc (-4 : ℝ) 4) := by
  obtain ⟨eta₀, heta₀, hselect⟩ :=
    exists_finite_disjoint_spatial_neck_spheres_tolerance_of_error.{u, v} (1 / 100) (by norm_num)
  obtain ⟨eta₁, heta₁, hretract⟩ := exists_spatial_neck_complement_retraction_tolerance.{u, v}
  refine ⟨min eta₀ eta₁, lt_min heta₀ heta₁, ?_⟩
  intro eps heps M _ _ _ _ g ι p nk a s ha A P hA hcompact
  obtain ⟨t, hts, htdis, htmax, htne, hgraphs⟩ := hselect eps (heps.trans (min_le_left _ _))
    M g ι p nk a s ha
  refine ⟨t, hts, htdis, htmax, htne, ?_⟩
  intro x hxP hx V W
  let J := {i // i ∈ t}
  have hfinite : Finite J := inferInstance
  let K := ⋃ i ∈ t, (nk i).map '' (univ ×ˢ Icc (-4 : ℝ) 4)
  have hdisJ : Pairwise (fun i j : J =>
      Disjoint (range (fun q : Sphere 2 => (nk i.val).map (q, a i.val)))
        (range (fun q : Sphere 2 => (nk j.val).map (q, a j.val)))) := by
    intro i j hij
    exact htdis i.property j.property (fun h => hij (Subtype.ext h))
  have hcompJ : connectedComponentIn
      (⋃ i : J, range (fun q : Sphere 2 => (nk i.val).map (q, a i.val)))ᶜ x = V := by
    congr 2
    ext z
    simp only [mem_iUnion, exists_prop]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i.val, i.property, hi⟩
    · rintro ⟨i, hi, hiz⟩
      exact ⟨⟨i, hi⟩, hiz⟩
  have hKJ : (⋃ i : J, (nk i.val).map '' (univ ×ˢ Icc (-4 : ℝ) 4)) = K := by
    ext z
    simp only [mem_iUnion, exists_prop, K]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i.val, i.property, hi⟩
    · rintro ⟨i, hi, hiz⟩
      exact ⟨⟨i, hi⟩, hiz⟩
  obtain ⟨f, hf, hfx, himage, hfix, hKcompact⟩ := hretract eps (heps.trans (min_le_right _ _))
    M g J (fun i => p i.val) (fun i => nk i.val) (fun i => a i.val)
    (fun i => ha i.val (hts i.property)) hdisJ A x
    (fun i => hA i.val (hts i.property)) hx
  rw [hcompJ] at hf himage
  rw [hKJ] at hfix hKcompact
  have hcleared : f '' V ⊆ (⋃ i ∈ s, range (fun q : Sphere 2 => (nk i).map (q, a i)))ᶜ := by
    intro z hz
    obtain ⟨hzV, hzthin⟩ := himage hz
    intro hzold
    obtain ⟨i, hi, q, hq⟩ := mem_iUnion₂.mp hzold
    by_cases hit : i ∈ t
    · exact connectedComponentIn_subset _ x hzV (mem_iUnion₂.mpr ⟨i, hit, q, hq⟩)
    · obtain ⟨j, hj, η, h, hh, hsmall, hmem, heq, hrange⟩ := hgraphs i hi hit
      apply hzthin
      refine mem_iUnion.mpr ⟨⟨j, hj⟩, ?_⟩
      have hsource : (η.symm q, h (η.symm q)) ∈
          univ ×ˢ Ioo (a j - 1 / 100) (a j + 1 / 100) := by
        refine ⟨mem_univ _, ?_, ?_⟩ <;>
          linarith [(abs_lt.mp (hsmall (η.symm q))).1, (abs_lt.mp (hsmall (η.symm q))).2]
      refine ⟨(η.symm q, h (η.symm q)), hsource, ?_⟩
      rw [heq, η.apply_symm_apply]
      exact hq
  have hxV : x ∈ V := by
    apply mem_connectedComponentIn
    intro hxbar
    obtain ⟨i, hi, q, hq⟩ := mem_iUnion₂.mp hxbar
    have hlen : (4 : ℝ) < eps⁻¹ :=
      (lt_inv_comm₀ (by norm_num) (nk i).eps_pos).mpr (by linarith [(nk i).eps_small])
    have hscalar := (nk i).scalar_bounds_on_image_window
      ⟨(q, a i), ⟨mem_univ _, by linarith [(abs_le.mp (ha i (hts hi))).1],
        by linarith [(abs_le.mp (ha i (hts hi))).2]⟩, hq⟩
    exact (not_lt_of_ge hx) ((hA i (hts hi)).trans_le hscalar.1)
  have hsubimage : f '' V ⊆ W :=
    (isPreconnected_connectedComponentIn.image f hf).subset_connectedComponentIn
      ⟨x, hxV, hfx⟩ hcleared
  have hsub : V ⊆ closure W ∪ K := by
    intro z hz
    by_cases hzK : z ∈ K
    · exact Or.inr hzK
    · exact Or.inl (subset_closure (hsubimage ⟨z, hz, hfix hzK⟩))
  have hclsub : closure V ⊆ closure W ∪ K :=
    closure_minimal hsub (isClosed_closure.union hKcompact.isClosed)
  exact ⟨((hcompact x hxP hx).union hKcompact).of_isClosed_subset isClosed_closure hclsub, hclsub⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
