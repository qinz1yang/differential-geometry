import DifferentialGeometry.Geometry.Neck.SpatialLevelOverlap
import DifferentialGeometry.Topology.Connected.LastIntersection
import DifferentialGeometry.Topology.OpenPartialHomeomorph.SegmentSide
import Mathlib.Topology.OpenPartialHomeomorph.Composition

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u v

private theorem SpatialNeck.exists_signed_germ_of_segment
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {p : M} (nk : SpatialNeck g eps p)
    (b : ℝ) {a c : ℝ} (hac : a < c) (γ : ℝ → M) (hγ : ContinuousOn γ (Icc a c))
    (htarget : ∀ t ∈ Icc a c, γ t ∈ nk.map.target)
    (hbase : (nk.map.symm (γ a)).2 = b) {V : Set M}
    (htail : ∀ t ∈ Ioc a c, γ t ∈ V)
    (havoid : Disjoint V (range fun q : Sphere 2 => nk.map (q, b))) :
    ∃ ν : ℝ, (ν = 1 ∨ ν = -1) ∧
      (∀ t ∈ Ioc a c, 0 < ν * ((nk.map.symm (γ t)).2 - b)) ∧
      ∀ r : ℝ, 0 < r → ∃ q : Sphere 2, ∃ t ∈ Ioo (0 : ℝ) r,
        nk.map (q, b + ν * t) ∈ V := by
  let H : Cylinder ≃ₜ Cylinder :=
    { toFun := fun z => (z.1, b + z.2)
      invFun := fun z => (z.1, z.2 - b)
      left_inv := by intro z; ext <;> simp
      right_inv := by intro z; ext <;> simp
      continuous_toFun := continuous_fst.prodMk (continuous_const.add continuous_snd)
      continuous_invFun := continuous_fst.prodMk (continuous_snd.sub continuous_const) }
  let T := H.transOpenPartialHomeomorph nk.map.toOpenPartialHomeomorph
  have hTtarget : T.target = nk.map.target := by ext x; simp [T]
  have hTsymm (x : M) : (T.symm x).2 = (nk.map.symm x).2 - b := rfl
  have hTvalue (q : Sphere 2) (t : ℝ) : T (q, t) = nk.map (q, b + t) := rfl
  obtain ⟨ν, hν, hsign, hgerm⟩ := T.exists_signed_germ_of_segment hac γ hγ
    (fun t ht => hTtarget.symm ▸ htarget t ht)
    (by rw [hTsymm, hbase, sub_self]) htail
    (by simpa only [hTvalue, add_zero] using havoid)
  refine ⟨ν, hν, ?_, ?_⟩
  · simpa only [hTsymm] using hsign
  · simpa only [hTvalue] using hgerm


theorem exists_spatial_neck_half_collar_cover_tolerance :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ eps : ℝ, eps ≤ eta →
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M]
          (g : SmoothRiemannianMetric I3 M) (ι : Type v) (p : ι → M)
          (nk : ∀ i, SpatialNeck g eps (p i)) (a : ι → ℝ) (s : Finset ι),
          (∀ i ∈ s, |a i| ≤ 3) →
          ∀ i ∈ s, ∀ q : Sphere 2, ∀ d : ℝ, |d| < 1 / 100 →
            (nk i).map (q, a i + d) ∉ ⋃ j ∈ s, range (fun w : Sphere 2 => (nk j).map (w, a j)) →
            let V := connectedComponentIn
              (⋃ j ∈ s, range (fun w : Sphere 2 => (nk j).map (w, a j)))ᶜ
              ((nk i).map (q, a i + d))
            ∃ j ∈ s, ∃ ν : ℝ, (ν = 1 ∨ ν = -1) ∧
              (nk i).map (q, a i + d) ∈ (nk j).map ''
                {z : Cylinder | 0 < ν * (z.2 - a j) ∧ ν * (z.2 - a j) < 1 / 8} ∧
              ∀ r : ℝ, 0 < r → ∃ w : Sphere 2, ∃ t ∈ Ioo (0 : ℝ) r,
                (nk j).map (w, a j + ν * t) ∈ V := by
  obtain ⟨eta, heta, hthin⟩ := exists_spatial_neck_thin_level_slab_tolerance.{u}
  refine ⟨eta, heta, ?_⟩
  intro eps heps M _ _ _ _ g ι p nk a s ha i hi q d hd hx V
  let B : Set M := ⋃ j ∈ s, range (fun w : Sphere 2 => (nk j).map (w, a j))
  have hlen : (4 : ℝ) < eps⁻¹ :=
    (lt_inv_comm₀ (by norm_num) (nk i).eps_pos).mpr (by linarith [(nk i).eps_small])
  have hsource (j : ι) (hj : j ∈ s) (w : Sphere 2) : (w, a j) ∈ (nk j).map.source :=
    (nk j).domain ⟨mem_univ _, by linarith [(abs_le.mp (ha j hj)).1],
      by linarith [(abs_le.mp (ha j hj)).2]⟩
  have hclosed : IsClosed B := by
    apply s.finite_toSet.isClosed_biUnion
    intro j hj
    apply (isCompact_range ?_).isClosed
    exact (nk j).map.contMDiffOn_toFun.continuousOn.comp_continuous
      (continuous_id.prodMk continuous_const) (fun w => hsource j hj w)
  let γ : ℝ → M := fun t => (nk i).map (q, a i + d * t)
  have hγsource (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (q, a i + d * t) ∈ (nk i).map.source := by
    have hdabs : |d * t| < 1 / 100 := by
      rw [abs_mul, abs_of_nonneg ht.1]
      exact (mul_le_mul_of_nonneg_left ht.2 (abs_nonneg d)).trans_lt (by simpa using hd)
    apply (nk i).domain
    refine ⟨mem_univ _, ?_, ?_⟩ <;>
      linarith [(abs_le.mp (ha i hi)).1, (abs_le.mp (ha i hi)).2,
        (abs_lt.mp hdabs).1, (abs_lt.mp hdabs).2]
  have hγ : ContinuousOn γ (Icc (0 : ℝ) 1) :=
    (nk i).map.contMDiffOn_toFun.continuousOn.comp
      (continuous_const.prodMk
        (continuous_const.add (continuous_const.mul continuous_id))).continuousOn
      hγsource
  have hstart : γ 0 ∈ B := by
    exact mem_iUnion₂.mpr ⟨i, hi, q, by simp [γ]⟩
  have hend : γ 1 ∉ B := by simpa only [γ, mul_one] using hx
  obtain ⟨c, hc, hcB, htail, hVtail⟩ :=
    DifferentialGeometry.Topology.exists_last_intersection_segment
    hclosed zero_lt_one γ hγ hstart hend
  obtain ⟨j, hj, w, hw⟩ := mem_iUnion₂.mp hcB
  have hdc : |d * c| ≤ 1 / 100 := by
    rw [abs_mul, abs_of_nonneg hc.1]
    exact (mul_le_mul_of_nonneg_left hc.2.le (abs_nonneg d)).trans (by simpa using hd.le)
  have hmeet : (nk i).map (q, a i + d * c) = (nk j).map (w, a j) := hw.symm
  have hfull := hthin eps heps M g (p i) (p j) (nk i) (nk j) q w (a i) (a j) (d * c)
    (ha i hi) (ha j hj) hdc hmeet
  have hγthin (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      γ t ∈ (nk j).map '' (univ ×ˢ Ioo (a j - 1 / 8) (a j + 1 / 8)) := by
    have hdt : |d * t| ≤ 1 / 100 := by
      rw [abs_mul, abs_of_nonneg ht.1]
      exact (mul_le_mul_of_nonneg_left ht.2 (abs_nonneg d)).trans (by simpa using hd.le)
    apply hfull
    refine ⟨(q, a i + d * t), ⟨mem_univ _, ?_, ?_⟩, rfl⟩ <;>
      linarith [(abs_le.mp hdt).1, (abs_le.mp hdt).2]
  have hγtarget (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : γ t ∈ (nk j).map.target := by
    obtain ⟨z, hz, hzγ⟩ := hγthin t ht
    apply hzγ ▸ (nk j).map.map_source ((nk j).domain ?_)
    exact ⟨mem_univ _, by linarith [(abs_le.mp (ha j hj)).1, hz.2.1],
      by linarith [(abs_le.mp (ha j hj)).2, hz.2.2]⟩
  have hbase : ((nk j).map.symm (γ c)).2 = a j := by
    rw [← hw]
    have hinv := (nk j).map.left_inv (hsource j hj w)
    change (nk j).map.symm ((nk j).map (w, a j)) = (w, a j) at hinv
    rw [hinv]
  have htailV (t : ℝ) (ht : t ∈ Ioc c 1) : γ t ∈ V := by
    simpa only [γ, mul_one] using hVtail ⟨t, ht, rfl⟩
  have havoidV : Disjoint V (range fun w : Sphere 2 => (nk j).map (w, a j)) := by
    rw [disjoint_left]
    intro z hz hzs
    exact connectedComponentIn_subset _ _ hz (mem_iUnion₂.mpr ⟨j, hj, hzs⟩)
  obtain ⟨ν, hν, hsign, hgerm⟩ := (nk j).exists_signed_germ_of_segment (a j) hc.2 γ
    (hγ.mono (Icc_subset_Icc hc.1 le_rfl))
    (fun t ht => hγtarget t ⟨hc.1.trans ht.1, ht.2⟩) hbase htailV havoidV
  refine ⟨j, hj, ν, hν, ?_, hgerm⟩
  have hpos := hsign 1 ⟨hc.2, le_rfl⟩
  obtain ⟨z, hz, hzγ⟩ := hγthin 1 ⟨zero_le_one, le_rfl⟩
  have hzsource : z ∈ (nk j).map.source := (nk j).domain
    ⟨mem_univ _, by linarith [(abs_le.mp (ha j hj)).1, hz.2.1],
      by linarith [(abs_le.mp (ha j hj)).2, hz.2.2]⟩
  have hinv := (nk j).map.left_inv hzsource
  change (nk j).map.symm ((nk j).map z) = z at hinv
  rw [← hzγ, hinv] at hpos
  refine ⟨z, ⟨hpos, ?_⟩, by simpa only [γ, mul_one] using hzγ⟩
  rcases hν with rfl | rfl <;> linarith [hz.2.1, hz.2.2]


end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
