import DifferentialGeometry.Geometry.Neck.SpatialLevelGraph
import DifferentialGeometry.Topology.Manifold.GraphBand
import DifferentialGeometry.Topology.Connected.CoverBySides
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckCapCompactDomains
import Batteries.Tactic.OpenPrivate
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset

open private exists_compactDomain_of_cylinder_slab from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckCapCompactDomains

set_option autoImplicit false
noncomputable section
open Set Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Topology

universe u v

private theorem exists_maximal_disjoint_subfamily
    {X ι : Type*} (S : ι → Set X) (s : Finset ι) :
    ∃ t : Finset ι, t ⊆ s ∧ (t : Set ι).PairwiseDisjoint S ∧
      (∀ u : Finset ι, u ⊆ s → (u : Set ι).PairwiseDisjoint S → u.card ≤ t.card) ∧
      ∀ i ∈ s, i ∉ t → ∃ j ∈ t, (S i ∩ S j).Nonempty := by
  classical
  let candidates : Finset (Finset ι) :=
    s.powerset.filter (fun (t : Finset ι) => (t : Set ι).PairwiseDisjoint S)
  have hne : candidates.Nonempty := ⟨∅, by simp [candidates]⟩
  obtain ⟨t, ht, hmax⟩ := candidates.exists_max_image Finset.card hne
  have hts : t ⊆ s := Finset.mem_powerset.mp (Finset.mem_filter.mp ht).1
  have htd : (t : Set ι).PairwiseDisjoint S := (Finset.mem_filter.mp ht).2
  refine ⟨t, hts, htd, ?_, ?_⟩
  · intro u hus hud
    exact hmax u (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hus, hud⟩)
  · intro i his hit
    by_contra h
    have hdis (j : ι) (hj : j ∈ t) : Disjoint (S i) (S j) := by
      rw [disjoint_iff_inter_eq_empty]
      exact not_nonempty_iff_eq_empty.mp (fun hij => h ⟨j, hj, hij⟩)
    have hnew : ((insert i t : Finset ι) : Set ι).PairwiseDisjoint S := by
      rw [Finset.coe_insert]
      exact htd.insert_of_notMem hit hdis
    have hbound := hmax (insert i t)
      (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.insert_subset his hts), hnew⟩)
    rw [Finset.card_insert_of_notMem hit] at hbound
    exact Nat.not_succ_le_self _ hbound


theorem exists_spatial_neck_disjoint_sphere_annulus_tolerance :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ eps : ℝ, eps ≤ eta →
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M]
          (g : SmoothRiemannianMetric I3 M) (p₀ p₁ : M)
          (nk₀ : SpatialNeck g eps p₀) (nk₁ : SpatialNeck g eps p₁)
          (a b c : ℝ), |a| ≤ 3 → |b| ≤ 3 → |c - a| < 1 / 2 →
          Disjoint (range (fun q : Sphere 2 => nk₀.map (q, a)))
            (range (fun q : Sphere 2 => nk₁.map (q, b))) →
          ∀ (u₀ u₁ : Sphere 2), nk₀.map (u₀, c) = nk₁.map (u₁, b) →
          ∃ (η : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2) (h : Sphere 2 → ℝ)
            (K : CompactDomain M) (F : PartialDiffeomorph IC I3 Cylinder M ∞),
            ContMDiff I2 𝓘(ℝ) ∞ h ∧ (∀ q, |h q - a| < 3 / 5) ∧
            ((∀ q, a < h q) ∨ (∀ q, h q < a)) ∧ h u₀ = c ∧
            (∀ q, nk₀.map (q, h q) = nk₁.map (η q, b)) ∧
            K.carrier = nk₀.map '' {z : Cylinder | z.2 ∈ uIcc a (h z.1)} ∧
            interior K.carrier = nk₀.map '' {z : Cylinder | z.2 ∈ uIoo a (h z.1)} ∧
            frontier K.carrier = range (fun q : Sphere 2 => nk₀.map (q, a)) ∪
              range (fun q : Sphere 2 => nk₁.map (q, b)) ∧
            (univ ×ˢ Icc (0 : ℝ) 1 ⊆ F.source) ∧
            (∀ q t, F (q, t) = nk₀.map (q, a + (h q - a) * t)) ∧
            K.carrier = F '' (univ ×ˢ Icc (0 : ℝ) 1) ∧
            K.carrier ⊆ nk₀.map '' (univ ×ˢ Icc (-4 : ℝ) 4) ∧
            (∀ x ∈ K.carrier,
              (1 - 4323 * eps) * metricScalarAt g p₀ ≤ metricScalarAt g x ∧
              metricScalarAt g x ≤ (1 + 4323 * eps) * metricScalarAt g p₀) ∧
            ∀ A : ℝ, A < (1 - 4323 * eps) * metricScalarAt g p₀ →
              ∀ V : Set M, IsPreconnected V →
                (V ∩ {x | metricScalarAt g x ≤ A}).Nonempty →
                Disjoint V (range (fun q : Sphere 2 => nk₀.map (q, a)) ∪
                  range (fun q : Sphere 2 => nk₁.map (q, b))) →
                Disjoint V K.carrier ∧ Disjoint (closure V) (interior K.carrier) := by
  obtain ⟨eta, heta, hgraph⟩ := exists_spatial_neck_level_graph_tolerance.{u}
  refine ⟨eta, heta, ?_⟩
  intro eps heps M _ _ _ _ g p₀ p₁ nk₀ nk₁ a b c ha hb hc hdisj u₀ u₁ hmeet
  have hc4 : |c| ≤ 4 := by
    rw [abs_le] at ha ⊢
    have h := abs_lt.mp hc
    constructor <;> linarith
  obtain ⟨η, h, hh, hbound, hcpoint, hmem, heq⟩ :=
    hgraph eps heps M g p₁ p₀ nk₁ nk₀ u₁ u₀ b c
      (hb.trans (by norm_num)) hc4 hmeet.symm
  have hsmall : ∀ q, |h q - a| < 3 / 5 := by
    intro q
    have h := abs_lt.mp (hbound q)
    have hc' := abs_lt.mp hc
    rw [abs_lt]
    constructor <;> linarith
  have hlen : (4 : ℝ) < eps⁻¹ :=
    (lt_inv_comm₀ (by norm_num) nk₀.eps_pos).mpr (by linarith [nk₀.eps_small])
  have hne : ∀ q, a ≠ h q := by
    intro q hqa
    apply disjoint_left.mp hdisj ⟨q, rfl⟩
    refine ⟨η q, ?_⟩
    change nk₁.map (η q, b) = nk₀.map (q, a)
    rw [← heq, hqa]
  let _ : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) (by norm_num : (0 : ℝ) ≤ 1))
  have horder : (∀ q, a < h q) ∨ (∀ q, h q < a) := by
    by_cases hhigher : ∀ q, a < h q
    · exact Or.inl hhigher
    · right
      obtain ⟨q, hq⟩ := not_forall.mp hhigher
      intro r
      by_contra hr
      obtain ⟨w, hw⟩ := intermediate_value_univ₂ hh.continuous continuous_const
        (le_of_not_gt hq) (le_of_not_gt hr)
      exact hne w hw.symm
  have hband4 : {z : Cylinder | z.2 ∈ uIcc a (h z.1)} ⊆
      univ ×ˢ Icc (-4 : ℝ) 4 := by
    intro z hz
    have hz' := mem_uIcc.mp hz
    have h := abs_lt.mp (hsmall z.1)
    have ha' := abs_le.mp ha
    refine ⟨mem_univ _, ?_, ?_⟩
    · rcases hz' with hz' | hz' <;> linarith [hz'.1, hz'.2]
    · rcases hz' with hz' | hz' <;> linarith [hz'.1, hz'.2]
  have hsource : {z : Cylinder | z.2 ∈ uIcc a (h z.1)} ⊆ nk₀.map.source := by
    intro z hz
    have hz' := hband4 hz
    exact nk₀.domain ⟨hz'.1, by linarith [hz'.2.1], by linarith [hz'.2.2]⟩
  obtain ⟨F, hF, hformula, hFimage, hcompact, hfront⟩ := exists_graphBand_partialDiffeomorph
    nk₀.map (fun _ => a) h contMDiff_const hh hne hsource
  obtain ⟨K, hK⟩ := exists_compactDomain_of_cylinder_slab F zero_lt_one hF
  have hkrange : K.carrier = nk₀.map '' {z : Cylinder | z.2 ∈ uIcc a (h z.1)} :=
    hK.trans hFimage
  have hKinterior : interior K.carrier = nk₀.map '' {z : Cylinder | z.2 ∈ uIoo a (h z.1)} := by
    rw [hkrange]
    have himage := nk₀.map.toOpenPartialHomeomorph.image_interior_of_subset_source hsource
    change nk₀.map '' interior {z : Cylinder | z.2 ∈ uIcc a (h z.1)} =
      interior (nk₀.map '' {z : Cylinder | z.2 ∈ uIcc a (h z.1)}) at himage
    rw [← himage]
    congr 1
    rcases horder with horder | horder
    · simp_rw [uIcc_of_le (horder _).le, uIoo_of_le (horder _).le, mem_Icc, mem_Ioo]
      exact interior_graphBand (fun _ => a) h continuous_const hh.continuous horder
    · simp_rw [uIcc_of_ge (horder _).le, uIoo_of_ge (horder _).le, mem_Icc, mem_Ioo]
      exact interior_graphBand h (fun _ => a) hh.continuous continuous_const horder
  have hgrange : range (fun q : Sphere 2 => nk₀.map (q, h q)) =
      range (fun q : Sphere 2 => nk₁.map (q, b)) := by
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨η q, (heq q).symm⟩
    · rintro ⟨q, rfl⟩
      refine ⟨η.symm q, ?_⟩
      change nk₀.map (η.symm q, h (η.symm q)) = nk₁.map (q, b)
      rw [heq, η.apply_symm_apply]
  have hKfront : frontier K.carrier = range (fun q : Sphere 2 => nk₀.map (q, a)) ∪
      range (fun q : Sphere 2 => nk₁.map (q, b)) := by
    rw [hK, hfront, hgrange]
  have hscalar : ∀ x ∈ K.carrier,
      (1 - 4323 * eps) * metricScalarAt g p₀ ≤ metricScalarAt g x ∧
      metricScalarAt g x ≤ (1 + 4323 * eps) * metricScalarAt g p₀ := by
    rw [hkrange]
    rintro x ⟨z, hz, rfl⟩
    have hz' := hband4 hz
    exact nk₀.scalar_bounds_on_image_window
      ⟨z, ⟨hz'.1, by linarith [hz'.2.1], by linarith [hz'.2.2]⟩, rfl⟩
  refine ⟨η, h, K, F, hh, hsmall, horder, hcpoint, heq, hkrange, hKinterior, hKfront, hF,
    fun q t => hformula (q, t), hK, ?_, hscalar, ?_⟩
  · rw [hkrange]
    exact image_mono hband4
  · intro A hA V hV hlow havoid
    have hdisjoint : Disjoint V K.carrier := by
      rw [disjoint_left]
      intro z hzV hzK
      have hsub := isPreconnected_subset_interior_of_meets_of_disjoint_frontier hV
        ⟨z, hzV, hzK⟩ (hKfront.symm ▸ havoid)
      obtain ⟨x, hxV, hxA⟩ := hlow
      have hxlow : metricScalarAt g x ≤ A := hxA
      exact (not_lt_of_ge hxlow) (hA.trans_le (hscalar x (interior_subset (hsub hxV))).1)
    exact ⟨hdisjoint, (hdisjoint.mono_right interior_subset).closure_left isOpen_interior⟩


theorem exists_spatial_neck_half_collar_avoids_sphere_tolerance :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ eps : ℝ, eps ≤ eta →
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M]
          (g : SmoothRiemannianMetric I3 M) (p₀ p₁ : M)
          (nk₀ : SpatialNeck g eps p₀) (nk₁ : SpatialNeck g eps p₁)
          (a b ν A : ℝ), |a| ≤ 3 → |b| ≤ 3 → (ν = 1 ∨ ν = -1) →
          A < (1 - 4323 * eps) * metricScalarAt g p₀ →
          Disjoint (range (fun q : Sphere 2 => nk₀.map (q, a)))
            (range (fun q : Sphere 2 => nk₁.map (q, b))) →
          ∀ V : Set M, IsPreconnected V →
            (V ∩ {x | metricScalarAt g x ≤ A}).Nonempty →
            Disjoint V (range (fun q : Sphere 2 => nk₀.map (q, a)) ∪
              range (fun q : Sphere 2 => nk₁.map (q, b))) →
            (∀ r : ℝ, 0 < r → ∃ q : Sphere 2, ∃ t ∈ Ioo (0 : ℝ) r,
              nk₀.map (q, a + ν * t) ∈ V) →
            Disjoint (nk₀.map '' {z : Cylinder | 0 < ν * (z.2 - a) ∧ ν * (z.2 - a) < 1 / 2})
              (range (fun q : Sphere 2 => nk₁.map (q, b))) := by
  obtain ⟨eta, heta, hannulus⟩ := exists_spatial_neck_disjoint_sphere_annulus_tolerance.{u}
  refine ⟨eta, heta, ?_⟩
  intro eps heps M _ _ _ _ g p₀ p₁ nk₀ nk₁ a b ν A ha hb hν hA hdisj V hV hlow havoid hgerm
  rw [disjoint_left]
  rintro x ⟨⟨q, c⟩, hc, rfl⟩ ⟨q', hqq'⟩
  have hcabs : |c - a| < 1 / 2 := by
    rcases hν with rfl | rfl <;> rw [abs_lt] <;>
      constructor <;> nlinarith [hc.1, hc.2]
  obtain ⟨η, h, hhK, F, hh, hsmall, horder, hpoint, heq, hK, hInt, hfront,
    hF, hformula, himage, hfour, hscalar, haway⟩ :=
    hannulus eps heps M g p₀ p₁ nk₀ nk₁ a b c ha hb hcabs hdisj q q' hqq'.symm
  have hav : Disjoint V hhK.carrier := (haway A hA V hV hlow havoid).1
  have hgap : ∀ w : Sphere 2, 0 < ν * (h w - a) := by
    rcases hν with rfl | rfl
    · simp only [one_mul] at hc ⊢
      rcases horder with horder | horder
      · exact fun w => sub_pos.mpr (horder w)
      · have hq := horder q
        rw [hpoint] at hq
        linarith [hc.1]
    · simp only [neg_one_mul] at hc ⊢
      rcases horder with horder | horder
      · have hq := horder q
        rw [hpoint] at hq
        linarith [hc.1]
      · exact fun w => by linarith [horder w]
  obtain ⟨w, _, hwmin⟩ := (isCompact_univ : IsCompact (univ : Set (Sphere 2))).exists_isMinOn
    ⟨nk₀.center, mem_univ _⟩
    ((continuous_const.mul (hh.continuous.sub continuous_const)).continuousOn)
  let r := ν * (h w - a)
  have hr : 0 < r := hgap w
  obtain ⟨v, t, ht, hv⟩ := hgerm r hr
  have htgap : t < ν * (h v - a) := ht.2.trans_le (hwmin (mem_univ v))
  have hmem : a + ν * t ∈ uIcc a (h v) := by
    rcases hν with rfl | rfl
    · have hvh : a < h v := by have := hgap v; linarith
      rw [uIcc_of_le hvh.le]
      constructor <;> nlinarith [ht.1, htgap]
    · have hvh : h v < a := by have := hgap v; linarith
      rw [uIcc_of_ge hvh.le]
      constructor <;> nlinarith [ht.1, htgap]
  exact disjoint_left.mp hav hv (hK.symm ▸ ⟨(v, a + ν * t), hmem, rfl⟩)


theorem exists_spatial_neck_complement_half_collar_tolerance :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ eps : ℝ, eps ≤ eta →
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M]
          (g : SmoothRiemannianMetric I3 M) (ι : Type v) (p : ι → M)
          (nk : ∀ i, SpatialNeck g eps (p i)) (a : ι → ℝ),
          (∀ i, |a i| ≤ 3) →
          Pairwise (fun i j => Disjoint (range (fun q : Sphere 2 => (nk i).map (q, a i)))
            (range (fun q : Sphere 2 => (nk j).map (q, a j)))) →
          ∀ (i : ι) (ν A : ℝ) (x : M), (ν = 1 ∨ ν = -1) →
            A < (1 - 4323 * eps) * metricScalarAt g (p i) →
            let V := connectedComponentIn (⋃ j, range (fun q : Sphere 2 => (nk j).map (q, a j)))ᶜ x
            (V ∩ {z | metricScalarAt g z ≤ A}).Nonempty →
            (∀ r : ℝ, 0 < r → ∃ q : Sphere 2, ∃ t ∈ Ioo (0 : ℝ) r,
              (nk i).map (q, a i + ν * t) ∈ V) →
            (nk i).map '' {z : Cylinder | 0 < ν * (z.2 - a i) ∧ ν * (z.2 - a i) < 1 / 2} ⊆ V := by
  obtain ⟨eta, heta, hpair⟩ := exists_spatial_neck_half_collar_avoids_sphere_tolerance.{u}
  refine ⟨eta, heta, ?_⟩
  intro eps heps M _ _ _ _ g ι p nk a ha hdisjoint i ν A x hν hA V hlow hgerm
  let H : Set Cylinder := {z | 0 < ν * (z.2 - a i) ∧ ν * (z.2 - a i) < 1 / 2}
  have hlen : (4 : ℝ) < eps⁻¹ :=
    (lt_inv_comm₀ (by norm_num) (nk i).eps_pos).mpr (by linarith [(nk i).eps_small])
  have hHsource : H ⊆ (nk i).map.source := by
    intro z hz
    have hzabs : |z.2 - a i| < 1 / 2 := by
      change 0 < ν * (z.2 - a i) ∧ ν * (z.2 - a i) < 1 / 2 at hz
      rcases hν with rfl | rfl <;> rw [abs_lt] <;>
        constructor <;> nlinarith [hz.1, hz.2]
    exact (nk i).domain ⟨mem_univ _, by linarith [(abs_le.mp (ha i)).1, (abs_lt.mp hzabs).1],
      by linarith [(abs_le.mp (ha i)).2, (abs_lt.mp hzabs).2]⟩
  have havoid : ∀ j, Disjoint ((nk i).map '' H)
      (range (fun q : Sphere 2 => (nk j).map (q, a j))) := by
    intro j
    by_cases hij : i = j
    · subst j
      rw [disjoint_left]
      rintro z ⟨w, hw, rfl⟩ ⟨q, hq⟩
      have hsrc : (q, a i) ∈ (nk i).map.source := (nk i).domain
        ⟨mem_univ _, by linarith [(abs_le.mp (ha i)).1], by linarith [(abs_le.mp (ha i)).2]⟩
      have heq := congrArg Prod.snd ((nk i).map.injOn hsrc (hHsource hw) hq)
      change a i = w.2 at heq
      change 0 < ν * (w.2 - a i) ∧ ν * (w.2 - a i) < 1 / 2 at hw
      rw [← heq, sub_self, mul_zero] at hw
      exact (lt_irrefl _ hw.1)
    · exact hpair eps heps M g (p i) (p j) (nk i) (nk j) (a i) (a j) ν A
        (ha i) (ha j) hν hA (hdisjoint hij) V isPreconnected_connectedComponentIn hlow
        (disjoint_left.mpr (fun z hz hs => by
          have hzavoid := connectedComponentIn_subset _ x hz
          apply hzavoid
          rcases hs with hs | hs
          · exact mem_iUnion.mpr ⟨i, hs⟩
          · exact mem_iUnion.mpr ⟨j, hs⟩)) hgerm
  let _ : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) (by norm_num : (0 : ℝ) ≤ 1))
  have hHpre : IsPreconnected H := by
    rcases hν with rfl | rfl
    · have heq : H = univ ×ˢ Ioo (a i) (a i + 1 / 2) := by
        ext z
        change (0 < 1 * (z.2 - a i) ∧ 1 * (z.2 - a i) < 1 / 2) ↔
          (True ∧ a i < z.2 ∧ z.2 < a i + 1 / 2)
        simp only [true_and]
        constructor <;> rintro ⟨hz₁, hz₂⟩ <;> constructor <;> nlinarith
      rw [heq]
      exact isPreconnected_univ.prod isPreconnected_Ioo
    · have heq : H = univ ×ˢ Ioo (a i - 1 / 2) (a i) := by
        ext z
        change (0 < -1 * (z.2 - a i) ∧ -1 * (z.2 - a i) < 1 / 2) ↔
          (True ∧ a i - 1 / 2 < z.2 ∧ z.2 < a i)
        simp only [true_and]
        constructor <;> rintro ⟨hz₁, hz₂⟩ <;> constructor <;> nlinarith
      rw [heq]
      exact isPreconnected_univ.prod isPreconnected_Ioo
  have hpre : IsPreconnected ((nk i).map '' H) := hHpre.image (nk i).map
    ((nk i).map.contMDiffOn_toFun.continuousOn.mono hHsource)
  obtain ⟨q, t, ht, hseed⟩ := hgerm (1 / 2) (by norm_num)
  have htH : (q, a i + ν * t) ∈ H := by
    change 0 < ν * (a i + ν * t - a i) ∧ ν * (a i + ν * t - a i) < 1 / 2
    rcases hν with rfl | rfl <;> constructor <;> nlinarith [ht.1, ht.2]
  have hsub := hpre.subset_connectedComponentIn
    (F := (⋃ j, range (fun q : Sphere 2 => (nk j).map (q, a j)))ᶜ)
    ⟨(q, a i + ν * t), htH, rfl⟩
    (fun z hz => by
      intro hbarrier
      obtain ⟨j, hj⟩ := mem_iUnion.mp hbarrier
      exact disjoint_left.mp (havoid j) hz hj)
  rw [← connectedComponentIn_eq hseed] at hsub
  exact hsub


theorem exists_finite_disjoint_spatial_neck_spheres_tolerance_of_error
    (d : ℝ) (hd : 0 < d) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ eps : ℝ, eps ≤ eta →
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M]
          (g : SmoothRiemannianMetric I3 M) (ι : Type v) (p : ι → M)
          (nk : ∀ i, SpatialNeck g eps (p i)) (a : ι → ℝ) (s : Finset ι),
          (∀ i ∈ s, |a i| ≤ 3) →
          ∃ t : Finset ι, t ⊆ s ∧
            (t : Set ι).PairwiseDisjoint
              (fun i => range (fun q : Sphere 2 => (nk i).map (q, a i))) ∧
            (∀ u : Finset ι, u ⊆ s →
              (u : Set ι).PairwiseDisjoint
                (fun i => range (fun q : Sphere 2 => (nk i).map (q, a i))) →
              u.card ≤ t.card) ∧
            (s.Nonempty → t.Nonempty) ∧
            ∀ i ∈ s, i ∉ t → ∃ j ∈ t,
              ∃ (η : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2) (h : Sphere 2 → ℝ),
                ContMDiff I2 𝓘(ℝ) ∞ h ∧ (∀ q, |h q - a j| < d) ∧
                (∀ q, (q, h q) ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) ∧
                (∀ q, (nk j).map (q, h q) = (nk i).map (η q, a i)) ∧
                range (fun q : Sphere 2 => (nk i).map (q, a i)) =
                  range (fun q : Sphere 2 => (nk j).map (q, h q)) := by
  obtain ⟨eta, heta, hgraph⟩ := exists_spatial_neck_level_graph_tolerance_of_error.{u} d hd
  refine ⟨eta, heta, ?_⟩
  intro eps heps M _ _ _ _ g ι p nk a s ha
  obtain ⟨t, hts, htd, hmax, hmeet⟩ := exists_maximal_disjoint_subfamily
    (fun i => range (fun q : Sphere 2 => (nk i).map (q, a i))) s
  refine ⟨t, hts, htd, hmax, ?_, ?_⟩
  · intro hs
    obtain ⟨i, hi⟩ := hs
    by_cases hit : i ∈ t
    · exact ⟨i, hit⟩
    · obtain ⟨j, hj, _⟩ := hmeet i hi hit
      exact ⟨j, hj⟩
  · intro i hi hit
    obtain ⟨j, hj, x, ⟨qi, hqi⟩, ⟨qj, hqj⟩⟩ := hmeet i hi hit
    obtain ⟨η, h, hh, hbound, _, hmem, heq⟩ := hgraph eps heps M g (p i) (p j)
      (nk i) (nk j) qi qj (a i) (a j)
      ((ha i hi).trans (by norm_num)) ((ha j (hts hj)).trans (by norm_num))
      (hqi.trans hqj.symm)
    refine ⟨j, hj, η, h, hh, hbound, hmem, heq, ?_⟩
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      refine ⟨η.symm q, ?_⟩
      change (nk j).map (η.symm q, h (η.symm q)) = (nk i).map (q, a i)
      rw [heq, η.apply_symm_apply]
    · rintro ⟨q, rfl⟩
      exact ⟨η q, (heq q).symm⟩


theorem exists_finite_disjoint_spatial_neck_spheres_tolerance :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ eps : ℝ, eps ≤ eta →
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M]
          (g : SmoothRiemannianMetric I3 M) (ι : Type v) (p : ι → M)
          (nk : ∀ i, SpatialNeck g eps (p i)) (a : ι → ℝ) (s : Finset ι),
          (∀ i ∈ s, |a i| ≤ 3) →
          ∃ t : Finset ι, t ⊆ s ∧
            (t : Set ι).PairwiseDisjoint
              (fun i => range (fun q : Sphere 2 => (nk i).map (q, a i))) ∧
            (∀ u : Finset ι, u ⊆ s →
              (u : Set ι).PairwiseDisjoint
                (fun i => range (fun q : Sphere 2 => (nk i).map (q, a i))) →
              u.card ≤ t.card) ∧
            (s.Nonempty → t.Nonempty) ∧
            ∀ i ∈ s, i ∉ t → ∃ j ∈ t,
              ∃ (η : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2) (h : Sphere 2 → ℝ),
                ContMDiff I2 𝓘(ℝ) ∞ h ∧ (∀ q, |h q - a j| < 1 / 10) ∧
                (∀ q, (q, h q) ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) ∧
                (∀ q, (nk j).map (q, h q) = (nk i).map (η q, a i)) ∧
                range (fun q : Sphere 2 => (nk i).map (q, a i)) =
                  range (fun q : Sphere 2 => (nk j).map (q, h q)) := by
  exact exists_finite_disjoint_spatial_neck_spheres_tolerance_of_error (1 / 10) (by norm_num)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
