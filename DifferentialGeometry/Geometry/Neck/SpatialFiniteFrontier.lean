import DifferentialGeometry.Topology.GraphBandComplement
import DifferentialGeometry.Topology.OpenPartialHomeomorph.CollarReturn
import DifferentialGeometry.Topology.Manifold.FiniteGraphBand
import DifferentialGeometry.Geometry.Neck.SpatialLevelGraph

set_option autoImplicit false
noncomputable section
open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem exists_spatial_neck_first_frontier_annulus_tolerance :
    ∃ eta : ℝ, 0 < eta ∧ ∀ eps : ℝ, eps ≤ eta →
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M]
        (g : SmoothRiemannianMetric I3 M) (p : M) (nk : SpatialNeck g eps p)
        (ι : Type*) [Finite ι] (point : ι → M) (neck : ∀ i, SpatialNeck g eps (point i))
        (level : ι → ℝ), (∀ i, |level i| ≤ 4) →
        Pairwise (fun i j => Disjoint (range (fun q => (neck i).map (q, level i)))
          (range (fun q => (neck j).map (q, level j)))) →
        ∀ f : Sphere 2 → ℝ, ContMDiff I2 𝓘(ℝ) ∞ f → (∀ q, |f q| < 1 / 10) →
        (∀ i, Disjoint (range (fun q => nk.map (q, f q)))
          (range (fun q => (neck i).map (q, level i)))) →
        (∃ i, (nk.map '' {z : Cylinder | f z.1 ≤ z.2 ∧ z.2 ≤ 3} ∩
          range (fun q => (neck i).map (q, level i))).Nonempty) →
        ∃ i, ∃ (η : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2) (h : Sphere 2 → ℝ)
          (A : PartialDiffeomorph IC I3 Cylinder M ∞),
          ContMDiff I2 𝓘(ℝ) ∞ h ∧ (∀ q, f q < h q) ∧
          (∃ q, h q ≤ 3) ∧ (∀ q, h q < 31 / 10) ∧
          univ ×ˢ Icc (0 : ℝ) 1 ⊆ A.source ∧
          (∀ q t, A (q, t) = nk.map (q, f q + (h q - f q) * t)) ∧
          (∀ q, A (q, 0) = nk.map (q, f q)) ∧
          (∀ q, A (q, 1) = (neck i).map (η q, level i)) ∧
          IsCompact (A '' (univ ×ˢ Icc (0 : ℝ) 1)) ∧
          frontier (A '' (univ ×ˢ Icc (0 : ℝ) 1)) =
            range (fun q => nk.map (q, f q)) ∪ range (fun q => (neck i).map (q, level i)) ∧
          ∀ j, j ≠ i → Disjoint (range (fun q => (neck j).map (q, level j)))
            (A '' (univ ×ˢ Icc (0 : ℝ) 1)) := by
  obtain ⟨eta, heta, hgraph⟩ := exists_spatial_neck_level_graph_tolerance.{u}
  refine ⟨eta, heta, ?_⟩
  intro eps heps M _ _ _ _ g p nk ι _ point neck level hlevel hdis f hf hfsmall havoid hmeet
  classical
  let S (i : ι) := range (fun q : Sphere 2 => (neck i).map (q, level i))
  let B := nk.map '' {z : Cylinder | f z.1 ≤ z.2 ∧ z.2 ≤ 3}
  let s : Set ι := {i | (B ∩ S i).Nonempty}
  have hsmall (i : ι) (hi : i ∈ s) :
      ∃ (η : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2) (h : Sphere 2 → ℝ),
        ContMDiff I2 𝓘(ℝ) ∞ h ∧
        (∀ q, -1 / 5 < h q ∧ h q < 31 / 10) ∧
        (∃ q, f q < h q ∧ h q ≤ 3) ∧
        (∀ q, (q, h q) ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) ∧
        (∀ q, nk.map (q, h q) = (neck i).map (η q, level i)) := by
    obtain ⟨y, ⟨⟨v, b⟩, hb, rfl⟩, u, hu⟩ := hi
    have hfb : f v < b := by
      rcases eq_or_lt_of_le hb.1 with h | h
      · have hp : nk.map (v, f v) = nk.map (v, b) := congrArg nk.map (Prod.ext rfl h)
        exact (Set.disjoint_left.mp (havoid i) (mem_range_self v) ⟨u, hu.trans hp.symm⟩).elim
      · exact h
    have hbabs : |b| ≤ 4 := by
      rw [abs_le]
      constructor <;> linarith [(abs_lt.mp (hfsmall v)).1, hb.2]
    obtain ⟨η, h, hh, hhb, hhv, hmem, heq⟩ :=
      hgraph eps heps M g (point i) p (neck i) nk u v (level i) b
        (hlevel i) hbabs hu
    refine ⟨η, h, hh, ?_, ⟨v, by rw [hhv]; exact hfb, by rw [hhv]; exact hb.2⟩, hmem, heq⟩
    intro q
    constructor <;> linarith [(abs_lt.mp (hhb q)).1, (abs_lt.mp (hhb q)).2,
      (abs_lt.mp (hfsmall v)).1, hb.2]
  choose η h hh hbounds htouch hmem heq using hsmall
  let hfun (i : ι) (q : Sphere 2) : ℝ := if hi : i ∈ s then h i hi q else 0
  have hgood (i : ι) (hi : i ∈ s) : hfun i = h i hi := by funext q; exact dif_pos hi
  have hSgraph (i : ι) (hi : i ∈ s) : range (fun q => nk.map (q, hfun i q)) = S i := by
    rw [hgood i hi]
    ext y
    constructor
    · rintro ⟨q, hq⟩
      exact ⟨η i hi q, (heq i hi q).symm.trans hq⟩
    · rintro ⟨q, hq⟩
      refine ⟨(η i hi).symm q, (heq i hi _).trans ?_⟩
      exact (congrArg (fun z => (neck i).map (z, level i))
        (show η i hi ((η i hi).symm q) = q from (η i hi).apply_symm_apply q)).trans hq
  have hlen : (4 : ℝ) < eps⁻¹ :=
    (lt_inv_comm₀ (by norm_num) nk.eps_pos).mpr (by linarith [nk.eps_small])
  have hsource (i : ι) (hi : i ∈ s) :
      {z : Cylinder | z.2 ∈ uIcc (f z.1) (hfun i z.1)} ⊆ nk.map.source := by
    intro z hz
    change z.2 ∈ uIcc (f z.1) (hfun i z.1) at hz
    rw [hgood i hi, mem_uIcc] at hz
    apply nk.domain
    rcases hz with hz | hz
    · exact ⟨mem_univ _, by linarith [(abs_lt.mp (hfsmall z.1)).1, hz.1],
        by linarith [(hbounds i hi z.1).2, hz.2]⟩
    · exact ⟨mem_univ _, by linarith [(hbounds i hi z.1).1, hz.1],
        by linarith [(abs_lt.mp (hfsmall z.1)).2, hz.2]⟩
  have hsmeet : ∃ i ∈ s, ∃ q, f q < hfun i q := by
    obtain ⟨i, hi⟩ := hmeet
    obtain ⟨q, hq, _⟩ := htouch i hi
    exact ⟨i, hi, q, hgood i hi ▸ hq⟩
  let _ : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) (by norm_num : (0 : ℝ) ≤ 1))
  obtain ⟨i, hi, A, hfi, hA, hformula, hzero, hone, hcompact, hfront, hother⟩ :=
    DifferentialGeometry.Topology.exists_first_graph_band_of_finite_boundary_family
      nk.map f hf S (Set.toFinite s) hfun (fun i hi => hgood i hi ▸ hh i hi)
      hsource hSgraph (fun i hi j hj hij => hdis hij) (fun i _ => havoid i) hsmeet
  refine ⟨i, η i hi, hfun i, A, hgood i hi ▸ hh i hi, hfi, ?_, ?_, hA,
    hformula, hzero, ?_, hcompact, hfront, ?_⟩
  · obtain ⟨q, _, hq⟩ := htouch i hi
    exact ⟨q, hgood i hi ▸ hq⟩
  · intro q
    rw [hgood i hi]
    exact (hbounds i hi q).2
  · intro q
    exact (hone q).trans (by rw [hgood i hi]; exact heq i hi q)
  · intro j hji
    by_cases hj : j ∈ s
    · exact hother j hj hji
    · rw [Set.disjoint_left]
      intro y hyS hyA
      obtain ⟨⟨q, t⟩, ht, hty⟩ := hyA
      have hheight : f q ≤ f q + (hfun i q - f q) * t ∧
          f q + (hfun i q - f q) * t ≤ hfun i q := by
        have hgap := sub_pos.mpr (hfi q)
        constructor <;> nlinarith [ht.2.1, ht.2.2]
      have hcoord := (hformula q t).symm.trans hty
      let c := f q + (hfun i q - f q) * t
      have hcabs : |c| ≤ 4 := by
        rw [abs_le]
        have hiupper := (hbounds i hi q).2
        rw [← hgood i hi] at hiupper
        constructor <;> linarith [(abs_lt.mp (hfsmall q)).1]
      obtain ⟨z, hz⟩ := hyS
      obtain ⟨ξ, k, hk, _, hkq, hkmem, hkeq⟩ :=
        hgraph eps heps M g (point j) p (neck j) nk z q (level j) c
          (hlevel j) hcabs (hz.trans hcoord.symm)
      have hkgraph : range (fun x => nk.map (x, k x)) = S j := by
        ext w
        constructor
        · rintro ⟨x, hx⟩
          exact ⟨ξ x, (hkeq x).symm.trans hx⟩
        · rintro ⟨x, hx⟩
          refine ⟨ξ.symm x, (hkeq _).trans ?_⟩
          exact (congrArg (fun z => (neck j).map (z, level j))
            (show ξ (ξ.symm x) = x from ξ.apply_symm_apply x)).trans hx
      have hfkne (x : Sphere 2) : f x ≠ k x := by
        intro h
        have hx : nk.map (x, f x) ∈ S j :=
          hkgraph ▸ ⟨x, congrArg nk.map (Prod.ext rfl h.symm)⟩
        exact Set.disjoint_left.mp (havoid j) (mem_range_self x) hx
      have hki_ne (x : Sphere 2) : k x ≠ hfun i x := by
        intro h
        have hxj : nk.map (x, k x) ∈ S j := hkgraph ▸ mem_range_self x
        have hxi : nk.map (x, k x) ∈ S i :=
          hSgraph i hi ▸ ⟨x, congrArg nk.map (Prod.ext rfl h.symm)⟩
        exact Set.disjoint_left.mp (hdis hji) hxj hxi
      have hfkq : f q < k q := lt_of_le_of_ne (hkq.symm ▸ hheight.1) (hfkne q)
      have hkiq : k q < hfun i q := lt_of_le_of_ne (hkq.symm ▸ hheight.2) (hki_ne q)
      obtain ⟨_, _, hfk, _⟩ := DifferentialGeometry.Topology.exists_least_graph_above
        (Set.finite_singleton ()) f (fun _ : Unit => k) hf.continuous
        (fun _ _ => hk.continuous)
        (by intro a ha b hb hab; exact (hab (Subsingleton.elim _ _)).elim)
        (fun _ _ => hfkne) ⟨(), rfl, q, hfkq⟩
      obtain ⟨_, _, hki, _⟩ := DifferentialGeometry.Topology.exists_least_graph_above
        (Set.finite_singleton ()) k (fun _ : Unit => hfun i) hk.continuous
        (fun _ _ => (hgood i hi ▸ hh i hi).continuous)
        (by intro a ha b hb hab; exact (hab (Subsingleton.elim _ _)).elim)
        (fun _ _ => hki_ne) ⟨(), rfl, q, hkiq⟩
      obtain ⟨w, _, hw⟩ := htouch i hi
      have hw' : k w ≤ 3 := (hki w).le.trans (hgood i hi ▸ hw)
      apply hj
      exact ⟨nk.map (w, k w), ⟨(w, k w), ⟨(hfk w).le, hw'⟩, rfl⟩,
        hkgraph ▸ mem_range_self w⟩

theorem exists_spatial_neck_return_deleting_frontier_tolerance :
    ∃ eta : ℝ, 0 < eta ∧ ∀ eps : ℝ, eps ≤ eta →
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M]
        (g : SmoothRiemannianMetric I3 M) (p : M) (nk : SpatialNeck g eps p)
        (ι : Type*) [Finite ι] (point : ι → M) (neck : ∀ i, SpatialNeck g eps (point i))
        (level : ι → ℝ), (∀ i, |level i| ≤ 4) →
        Pairwise (fun i j => Disjoint (range (fun q => (neck i).map (q, level i)))
          (range (fun q => (neck j).map (q, level j)))) →
        ∀ f : Sphere 2 → ℝ, ContMDiff I2 𝓘(ℝ) ∞ f → (∀ q, |f q| < 1 / 10) →
        f nk.center = 0 →
        (∀ i, Disjoint (range (fun q => nk.map (q, f q)))
          (range (fun q => (neck i).map (q, level i)))) →
        ∀ W : Set M, closure (interior W) = W →
        frontier W = range (fun q => nk.map (q, f q)) ∪
          ⋃ i, range (fun q => (neck i).map (q, level i)) →
        (∃ δ > 0, ∀ t, 0 < t → t < δ → nk.map (nk.center, t) ∉ W) →
        (∃ i, (nk.map '' {z : Cylinder | f z.1 ≤ z.2 ∧ z.2 ≤ 3} ∩
          range (fun q => (neck i).map (q, level i))).Nonempty) →
        ∃ i, ∃ (η : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2)
          (A : PartialDiffeomorph IC I3 Cylinder M ∞),
          univ ×ˢ Icc (0 : ℝ) 1 ⊆ A.source ∧
          (∀ q, A (q, 0) = nk.map (q, f q)) ∧
          (∀ q, A (q, 1) = (neck i).map (η q, level i)) ∧
          IsCompact (A '' (univ ×ˢ Icc (0 : ℝ) 1)) ∧
          (A '' (univ ×ˢ Icc (0 : ℝ) 1)) ∩ W =
            range (fun q => nk.map (q, f q)) ∪ range (fun q => (neck i).map (q, level i)) ∧
          closure (interior (W ∪ A '' (univ ×ˢ Icc (0 : ℝ) 1))) =
            W ∪ A '' (univ ×ˢ Icc (0 : ℝ) 1) ∧
          frontier (W ∪ A '' (univ ×ˢ Icc (0 : ℝ) 1)) =
            ⋃ j : {j // j ≠ i}, range (fun q => (neck j.val).map (q, level j.val)) := by
  obtain ⟨eta, heta, hselect⟩ := exists_spatial_neck_first_frontier_annulus_tolerance.{u}
  refine ⟨eta, heta, ?_⟩
  intro eps heps M _ _ _ _ g p nk ι _ point neck level hlevel hdis
    f hf hfsmall hfzero havoid W hregular hfront hout hmeet
  classical
  let _ : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) (by norm_num : (0 : ℝ) ≤ 1))
  obtain ⟨i, η, h, A, hh, hfh, _, hupperbound, hA, hformula,
    hzero, hone, hcompact, hAfront, hother⟩ :=
    hselect eps heps M g p nk ι point neck level hlevel hdis f hf hfsmall havoid hmeet
  let S (j : ι) := range (fun q : Sphere 2 => (neck j).map (q, level j))
  let U := ⋃ j : {j // j ≠ i}, S j.val
  have hSclosed (j) : IsClosed (S j) := by
    have hlen : (4 : ℝ) < eps⁻¹ :=
      (lt_inv_comm₀ (by norm_num) (neck j).eps_pos).mpr (by linarith [(neck j).eps_small])
    apply IsCompact.isClosed
    apply isCompact_range
    exact (neck j).map.contMDiffOn_toFun.continuousOn.comp_continuous
      (continuous_id.prodMk continuous_const)
      (fun q => (neck j).domain ⟨mem_univ _, by constructor <;>
        linarith [(abs_le.mp (hlevel j)).1, (abs_le.mp (hlevel j)).2]⟩)
  have hUclosed : IsClosed U := isClosed_iUnion_of_finite (fun j => hSclosed j.val)
  have hUavoid : Disjoint U (A '' (univ ×ˢ Icc (0 : ℝ) 1)) := by
    apply disjoint_iUnion_left.mpr
    intro j
    exact hother j.val j.property
  have hupper : range (fun q => nk.map (q, h q)) = S i := by
    ext x
    constructor
    · rintro ⟨q, hq⟩
      have he : nk.map (q, h q) = (neck i).map (η q, level i) :=
        (show A (q, 1) = nk.map (q, h q) by
          simpa only [mul_one, add_sub_cancel] using hformula q 1).symm.trans (hone q)
      exact ⟨η q, he.symm.trans hq⟩
    · rintro ⟨q, hq⟩
      refine ⟨η.symm q, ?_⟩
      have he : nk.map (η.symm q, h (η.symm q)) = (neck i).map (η (η.symm q), level i) :=
        (show A (η.symm q, 1) = nk.map (η.symm q, h (η.symm q)) by
          simpa only [mul_one, add_sub_cancel] using hformula (η.symm q) 1).symm.trans (hone _)
      exact he.trans ((congrArg (fun z => (neck i).map (z, level i))
        (show η (η.symm q) = q from η.apply_symm_apply q)).trans hq)
  have hfront' : frontier W =
      (range (fun q => nk.map (q, f q)) ∪ range (fun q => nk.map (q, h q))) ∪ U := by
    rw [hupper, hfront, union_assoc]
    congr 1
    ext x
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      by_cases hji : j = i
      · subst j; exact Or.inl hj
      · exact Or.inr (mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩)
    · rintro (hi | hu)
      · exact mem_iUnion.mpr ⟨i, hi⟩
      · obtain ⟨j, hj⟩ := mem_iUnion.mp hu
        exact mem_iUnion.mpr ⟨j.val, hj⟩
  have hband : A '' (univ ×ˢ Icc (0 : ℝ) 1) =
      nk.map '' {z : Cylinder | f z.1 ≤ z.2 ∧ z.2 ≤ h z.1} := by
    ext x
    constructor
    · rintro ⟨⟨q, t⟩, ht, htx⟩
      refine ⟨(q, f q + (h q - f q) * t), ?_, (hformula q t).symm.trans htx⟩
      have hgap := sub_pos.mpr (hfh q)
      constructor <;> nlinarith [ht.2.1, ht.2.2]
    · rintro ⟨⟨q, t⟩, ht, htx⟩
      let r := (t - f q) / (h q - f q)
      have hr : r ∈ Icc (0 : ℝ) 1 := by
        constructor
        · exact div_nonneg (sub_nonneg.mpr ht.1) (sub_pos.mpr (hfh q)).le
        · exact (div_le_one (sub_pos.mpr (hfh q))).mpr (by linarith [ht.2])
      refine ⟨(q, r), ⟨mem_univ _, hr⟩, (hformula q r).trans ?_⟩
      have he : f q + (h q - f q) * r = t := by
        dsimp [r]
        field_simp [(sub_pos.mpr (hfh q)).ne']
        ring
      exact (congrArg nk.map (show (q, f q + (h q - f q) * r) = (q, t) from
        Prod.ext rfl he)).trans htx
  have hsource : {z : Cylinder | f z.1 ≤ z.2 ∧ z.2 ≤ h z.1} ⊆ nk.map.source := by
    intro z hz
    have hlen : (4 : ℝ) < eps⁻¹ :=
      (lt_inv_comm₀ (by norm_num) nk.eps_pos).mpr (by linarith [nk.eps_small])
    exact nk.domain ⟨mem_univ _, by linarith [(abs_lt.mp (hfsmall z.1)).1, hz.1],
      by linarith [hupperbound z.1, hz.2]⟩
  have houtband : (nk.map '' {z : Cylinder | f z.1 < z.2 ∧ z.2 < h z.1} \ W).Nonempty := by
    obtain ⟨δ, hδ, hout⟩ := hout
    have hhpos : 0 < h nk.center := hfzero ▸ hfh nk.center
    let t := min δ (h nk.center) / 2
    have ht : 0 < t := by dsimp [t]; positivity
    have htδ : t < δ := by dsimp [t]; linarith [min_le_left δ (h nk.center)]
    have hth : t < h nk.center := by dsimp [t]; linarith [min_le_right δ (h nk.center)]
    exact ⟨nk.map (nk.center, t), ⟨(nk.center, t), ⟨hfzero ▸ ht, hth⟩, rfl⟩, hout t ht htδ⟩
  have hinter := (DifferentialGeometry.Topology.graphBand_image_inter_closed_of_frontier_eq_union
    nk.map.toOpenPartialHomeomorph f h hf.continuous hh.continuous hfh hsource
    (hregular ▸ isClosed_closure) hfront' (hband ▸ hUavoid) houtband).2
  change (nk.map '' {z : Cylinder | f z.1 ≤ z.2 ∧ z.2 ≤ h z.1}) ∩ W =
    range (fun q => nk.map (q, f q)) ∪ range (fun q => nk.map (q, h q)) at hinter
  rw [← hband] at hinter
  have hface (t : ℝ) : A '' (univ ×ˢ ({t} : Set ℝ)) = range (fun q => A (q, t)) := by
    ext x
    constructor
    · rintro ⟨⟨q, s⟩, ⟨_, hs⟩, hqx⟩
      have : s = t := hs
      subst s
      exact ⟨q, hqx⟩
    · rintro ⟨q, hqx⟩
      exact ⟨(q, t), ⟨mem_univ _, rfl⟩, hqx⟩
  have hlowface : A '' (univ ×ˢ ({0} : Set ℝ)) = range (fun q => nk.map (q, f q)) := by
    rw [hface]
    congr 1
    exact funext hzero
  have hhighface : A '' (univ ×ˢ ({1} : Set ℝ)) = range (fun q => nk.map (q, h q)) := by
    rw [hface]
    congr 1
    funext q
    simpa only [mul_one, add_sub_cancel] using hformula q 1
  have hfnew : frontier W = A '' (univ ×ˢ ({0} : Set ℝ)) ∪
      A '' (univ ×ˢ ({1} : Set ℝ)) ∪ U := by rw [hlowface, hhighface]; exact hfront'
  have hi : A '' (univ ×ˢ Icc (0 : ℝ) 1) ∩ W =
      A '' (univ ×ˢ ({0} : Set ℝ)) ∪ A '' (univ ×ˢ ({1} : Set ℝ)) := by
    rw [hlowface, hhighface]
    exact hinter
  have hdelete := A.toOpenPartialHomeomorph.frontier_union_closed_cylinder_of_inter_eq_boundary
    (by norm_num : (0 : ℝ) < 1) hA hregular hUclosed hfnew hUavoid hi
  refine ⟨i, η, A, hA, hzero, hone, hcompact, ?_, hdelete.1, hdelete.2⟩
  rw [hupper] at hinter
  exact hinter

theorem exists_spatial_neck_finite_frontier_step_tolerance :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ eps : ℝ, eps ≤ eta →
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M]
          (g : SmoothRiemannianMetric I3 M) (p : M) (nk : SpatialNeck g eps p)
          (ι : Type*) [Finite ι] (point : ι → M) (neck : ∀ i, SpatialNeck g eps (point i))
          (level : ι → ℝ), (∀ i, |level i| ≤ 4) →
          Pairwise (fun i j => Disjoint (range (fun q => (neck i).map (q, level i)))
            (range (fun q => (neck j).map (q, level j)))) → ∀
          (f : Sphere 2 → ℝ), ContMDiff I2 𝓘(ℝ) ∞ f →
          (∀ q, |f q| < 1 / 10) → f nk.center = 0 →
          ∀ W : Set M, closure (interior W) = W →
          frontier W = range (fun q => nk.map (q, f q)) ∪
            (⋃ i, range (fun q => (neck i).map (q, level i))) →
          (∀ i, Disjoint (range (fun q => nk.map (q, f q)))
            (range (fun q => (neck i).map (q, level i)))) →
          (∃ δ : ℝ, 0 < δ ∧ ∀ t, 0 < t → t < δ → nk.map (nk.center, t) ∉ W) →
          (∃ A : PartialDiffeomorph IC I3 Cylinder M ∞,
            (univ ×ˢ Icc (0 : ℝ) 1 ⊆ A.source) ∧
            (∀ q t, A (q, t) = nk.map (q, f q + (3 - f q) * t)) ∧
            (∀ q, A (q, 0) = nk.map (q, f q)) ∧
            (∀ q, A (q, 1) = nk.map (q, 3)) ∧
            IsCompact (A '' (univ ×ˢ Icc (0 : ℝ) 1)) ∧
            (A '' (univ ×ˢ Icc (0 : ℝ) 1)) ∩ W = range (fun q => nk.map (q, f q)) ∧
            closure (interior (W ∪ A '' (univ ×ˢ Icc (0 : ℝ) 1))) =
              W ∪ A '' (univ ×ˢ Icc (0 : ℝ) 1) ∧
            frontier (W ∪ A '' (univ ×ˢ Icc (0 : ℝ) 1)) =
              (⋃ i, range (fun q => (neck i).map (q, level i))) ∪ range (fun q => nk.map (q, 3)) ∧
            nk.map '' (univ ×ˢ Icc (1 : ℝ) 2) ⊆
              (A '' (univ ×ˢ Icc (0 : ℝ) 1)) \ W) ∨
          (∃ i, ∃ (η : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2)
            (A : PartialDiffeomorph IC I3 Cylinder M ∞),
            (univ ×ˢ Icc (0 : ℝ) 1 ⊆ A.source) ∧
            (∀ q, A (q, 0) = nk.map (q, f q)) ∧
            (∀ q, A (q, 1) = (neck i).map (η q, level i)) ∧
            IsCompact (A '' (univ ×ˢ Icc (0 : ℝ) 1)) ∧
            (A '' (univ ×ˢ Icc (0 : ℝ) 1)) ∩ W =
              range (fun q => nk.map (q, f q)) ∪ range (fun q => (neck i).map (q, level i)) ∧
            closure (interior (W ∪ A '' (univ ×ˢ Icc (0 : ℝ) 1))) =
              W ∪ A '' (univ ×ˢ Icc (0 : ℝ) 1) ∧
            frontier (W ∪ A '' (univ ×ˢ Icc (0 : ℝ) 1)) =
              ⋃ j : {j // j ≠ i}, range (fun q => (neck j.val).map (q, level j.val))) := by
  obtain ⟨eta, heta, hreturn⟩ := exists_spatial_neck_return_deleting_frontier_tolerance.{u}
  refine ⟨eta, heta, ?_⟩
  intro eps heps M _ _ _ _ g p nk ι _ point neck level hlevel hpair
    f hf hfsmall hfzero W hregular hfront hdis hout
  let _ : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) (by norm_num : (0 : ℝ) ≤ 1))
  let S : Set M := ⋃ i, range (fun q : Sphere 2 => (neck i).map (q, level i))
  let B := nk.map '' {z : Cylinder | f z.1 ≤ z.2 ∧ z.2 ≤ 3}
  by_cases hmeet : (B ∩ S).Nonempty
  · right
    have hmeet' : ∃ i, (B ∩ range (fun q => (neck i).map (q, level i))).Nonempty := by
      obtain ⟨x, hxB, hxS⟩ := hmeet
      obtain ⟨i, hi⟩ := mem_iUnion.mp hxS
      exact ⟨i, x, hxB, hi⟩
    exact hreturn eps heps M g p nk ι point neck level hlevel hpair
      f hf hfsmall hfzero hdis W hregular hfront hout hmeet'
  · left
    have hlen : (3 : ℝ) < eps⁻¹ :=
      (lt_inv_comm₀ (by norm_num) nk.eps_pos).mpr (by linarith [nk.eps_small])
    have hsource : {z : Cylinder | z.2 ∈ uIcc (f z.1) 3} ⊆ nk.map.source := by
      intro z hz
      change z.2 ∈ uIcc (f z.1) 3 at hz
      rw [uIcc_of_le (by linarith [(abs_lt.mp (hfsmall z.1)).2])] at hz
      exact nk.domain ⟨mem_univ _, by linarith [hz.1, (abs_lt.mp (hfsmall z.1)).1],
        hz.2.trans_lt hlen⟩
    obtain ⟨A, hA, hformula, hrange, hcompact, _⟩ :=
      DifferentialGeometry.Topology.exists_graphBand_partialDiffeomorph nk.map f
        (fun _ => 3) hf contMDiff_const (fun q => by linarith [(abs_lt.mp (hfsmall q)).2])
        hsource
    have hzero (q) : A (q, 0) = nk.map (q, f q) := by rw [hformula]; simp
    have hone (q) : A (q, 1) = nk.map (q, 3) := by rw [hformula]; simp
    have hB : A '' (univ ×ˢ Icc (0 : ℝ) 1) = B := by
      rw [hrange]
      congr 1
      ext z
      change (z.2 ∈ uIcc (f z.1) 3) ↔ f z.1 ≤ z.2 ∧ z.2 ≤ 3
      rw [uIcc_of_le (by linarith [(abs_lt.mp (hfsmall z.1)).2]), mem_Icc]
    have hlen4 : (4 : ℝ) < eps⁻¹ :=
      (lt_inv_comm₀ (by norm_num) nk.eps_pos).mpr (by linarith [nk.eps_small])
    have hSclosed : IsClosed S := by
      apply isClosed_iUnion_of_finite
      intro i
      apply IsCompact.isClosed
      apply isCompact_range
      exact (neck i).map.contMDiffOn_toFun.continuousOn.comp_continuous
        (continuous_id.prodMk continuous_const)
        (fun q => (neck i).domain ⟨mem_univ _, by constructor <;>
          linarith [(abs_le.mp (hlevel i)).1, (abs_le.mp (hlevel i)).2]⟩)
    have hface (t : ℝ) : A '' (univ ×ˢ ({t} : Set ℝ)) = range (fun q => A (q, t)) := by
      ext y
      constructor
      · rintro ⟨⟨q, s⟩, ⟨_, hs⟩, rfl⟩
        have : s = t := hs
        subst s
        exact ⟨q, rfl⟩
      · rintro ⟨q, rfl⟩
        exact ⟨(q, t), ⟨mem_univ _, rfl⟩, rfl⟩
    have hfrontA : frontier W = A '' (univ ×ˢ ({0} : Set ℝ)) ∪ S := by
      rw [hface, show (fun q => A (q, 0)) = (fun q => nk.map (q, f q)) from funext hzero]
      exact hfront
    have havoid : Disjoint S (A '' (univ ×ˢ Icc (0 : ℝ) 1)) := by
      rw [hB, disjoint_left]
      intro x hxS hxB
      exact hmeet ⟨x, hxB, hxS⟩
    have hseed : (A '' (univ ×ˢ Ioo (0 : ℝ) 1) ∩ Wᶜ).Nonempty := by
      obtain ⟨δ, hδ, houtside⟩ := hout
      let t := min δ 1 / 2
      have ht : 0 < t := by dsimp only [t]; positivity
      have htδ : t < δ := by dsimp only [t]; linarith [min_le_left δ 1]
      have ht3 : t < 3 := by dsimp only [t]; linarith [min_le_right δ 1]
      refine ⟨nk.map (nk.center, t), ⟨(nk.center, t / 3),
        ⟨mem_univ _, by constructor <;> linarith⟩, ?_⟩, houtside t ht htδ⟩
      rw [hformula, hfzero]
      congr 1
      exact Prod.ext rfl (show 0 + (3 - 0) * (t / 3) = t by ring)
    obtain ⟨hinter, hreg, hnewfront⟩ := A.toOpenPartialHomeomorph.closed_cylinder_advance
      (by norm_num : (0 : ℝ) < 1) hA hregular hSclosed hfrontA havoid hseed
    change A '' (univ ×ˢ Icc (0 : ℝ) 1) ∩ W =
      A '' (univ ×ˢ ({0} : Set ℝ)) at hinter
    change closure (interior (A '' (univ ×ˢ Icc (0 : ℝ) 1) ∪ W)) =
      A '' (univ ×ˢ Icc (0 : ℝ) 1) ∪ W at hreg
    change frontier (A '' (univ ×ˢ Icc (0 : ℝ) 1) ∪ W) =
      S ∪ A '' (univ ×ˢ ({1} : Set ℝ)) at hnewfront
    refine ⟨A, hA, fun q t => hformula (q, t), hzero, hone, hcompact, ?_, ?_, ?_, ?_⟩
    · rw [hinter, hface]
      congr 1
      exact funext hzero
    · simpa only [union_comm] using hreg
    · rw [hface] at hnewfront
      have he : (fun q => A (q, 1)) = (fun q => nk.map (q, 3)) := funext hone
      rw [he, union_comm (A '' (univ ×ˢ Icc (0 : ℝ) 1)) W] at hnewfront
      exact hnewfront
    · rintro x ⟨⟨q, t⟩, ht, rfl⟩
      have htB : nk.map (q, t) ∈ B :=
        ⟨(q, t), ⟨by linarith [(abs_lt.mp (hfsmall q)).2, ht.2.1], by linarith [ht.2.2]⟩, rfl⟩
      refine ⟨hB.symm ▸ htB, ?_⟩
      intro hxW
      have hl := hinter ▸ (show nk.map (q, t) ∈ A '' (univ ×ˢ Icc (0 : ℝ) 1) ∩ W from
        ⟨hB.symm ▸ htB, hxW⟩)
      rw [hface] at hl
      obtain ⟨z, hz⟩ := hl
      have hz' : nk.map (z, f z) = nk.map (q, t) := (hzero z).symm.trans hz
      have he := nk.map.injOn
        (nk.domain ⟨mem_univ _, by constructor <;> linarith [(abs_lt.mp (hfsmall z)).1,
          (abs_lt.mp (hfsmall z)).2]⟩)
        (nk.domain ⟨mem_univ _, by constructor <;> linarith [ht.2.1, ht.2.2]⟩) hz'
      have hh := congrArg Prod.snd he
      linarith [(abs_lt.mp (hfsmall z)).2, ht.2.1]

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
