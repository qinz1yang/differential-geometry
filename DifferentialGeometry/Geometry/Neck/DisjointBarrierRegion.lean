import DifferentialGeometry.Geometry.Neck.FiniteDisjointBarriers
import DifferentialGeometry.Topology.Connected.CompactComponentUnion
import DifferentialGeometry.Topology.OpenPartialHomeomorph.FiniteCollarFrontier
import Batteries.Tactic.OpenPrivate

open private SpatialNeck.signedLevelChart SpatialNeck.signedLevelChart_apply
  SpatialNeck.signedLevelChart_source from DifferentialGeometry.Geometry.Neck.FiniteDisjointBarriers

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u v

theorem exists_compact_region_of_finite_spatial_neck_barriers_tolerance :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ eps : ℝ, eps ≤ eta →
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M]
          (g : SmoothRiemannianMetric I3 M) (ι : Type v) (p : ι → M)
          (nk : ∀ i, SpatialNeck g eps (p i)) (a : ι → ℝ) (s : Finset ι),
          (∀ i ∈ s, |a i| ≤ 3) →
          ∀ (A : ℝ) (P : Set M), IsCompact P →
            (∀ x ∈ P, metricScalarAt g x ≤ A) →
            (∀ i ∈ s, A < (1 - 4323 * eps) * metricScalarAt g (p i)) →
            (∀ x ∈ P, IsCompact (closure (connectedComponentIn
              (⋃ i ∈ s, range (fun q : Sphere 2 => (nk i).map (q, a i)))ᶜ x))) →
            ∃ (t b : Finset ι) (C : Finset (Set M)),
              t ⊆ s ∧ b ⊆ t ∧
              (t : Set ι).PairwiseDisjoint
                (fun i => range (fun q : Sphere 2 => (nk i).map (q, a i))) ∧
              (∀ V, V ∈ C ↔ ∃ x ∈ P, V = connectedComponentIn
                (⋃ i ∈ t, range (fun q : Sphere 2 => (nk i).map (q, a i)))ᶜ x) ∧
              (∀ V ∈ C, IsOpen V ∧ IsConnected V ∧ IsCompact (closure V)) ∧
              let K := ⋃ V ∈ C, closure V
              IsCompact K ∧ P ⊆ interior K ∧ closure (interior K) = K ∧
              K ⊆ (⋃ x ∈ P, closure (connectedComponentIn
                (⋃ i ∈ s, range (fun q : Sphere 2 => (nk i).map (q, a i)))ᶜ x)) ∪
                ⋃ i ∈ t, (nk i).map '' (univ ×ˢ Icc (-4 : ℝ) 4) ∧
              frontier K = ⋃ i ∈ b, range (fun q : Sphere 2 => (nk i).map (q, a i)) ∧
              ∀ i ∈ b, ∃ r σ : ℝ, 0 < r ∧ (σ = 1 ∨ σ = -1) ∧
                (∀ q, ∀ z ∈ Ioo (-r) r, (q, a i + z) ∈ (nk i).map.source) ∧
                (∀ q, ∀ z ∈ Ioo (-r) r, (nk i).map (q, a i + z) ∈ K ↔ σ * z ≤ 0) ∧
                (∀ q, ∀ z ∈ Ioo (-r) r, (nk i).map (q, a i + z) ∈ interior K ↔ σ * z < 0) := by
  obtain ⟨eta, heta, hselect⟩ := exists_finite_disjoint_spatial_neck_barriers_tolerance.{u, v}
  refine ⟨eta, heta, ?_⟩
  intro eps heps M _ _ _ _ g ι p nk a s ha A P hP hPlow hA hold
  classical
  let _ : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace ThreeSpace M
  obtain ⟨t, hts, htdis, _, _, htcompact⟩ := hselect eps heps M g ι p nk a s ha A P hA
    (fun x hx _ => hold x hx)
  let B : Set M := ⋃ i ∈ t, range (fun q : Sphere 2 => (nk i).map (q, a i))
  have hlen (i : ι) : (4 : ℝ) < eps⁻¹ :=
    (lt_inv_comm₀ (by norm_num) (nk i).eps_pos).mpr (by linarith [(nk i).eps_small])
  have hsource (i : ι) (hi : i ∈ t) (q : Sphere 2) : (q, a i) ∈ (nk i).map.source :=
    (nk i).domain ⟨mem_univ _, by linarith [(abs_le.mp (ha i (hts hi))).1, hlen i],
      by linarith [(abs_le.mp (ha i (hts hi))).2, hlen i]⟩
  have hBclosed : IsClosed B := by
    apply t.finite_toSet.isClosed_biUnion
    intro i hi
    exact (isCompact_range ((nk i).map.contMDiffOn_toFun.continuousOn.comp_continuous
      (continuous_id.prodMk continuous_const) (hsource i hi))).isClosed
  have hPout : P ⊆ Bᶜ := by
    intro x hx hxB
    obtain ⟨i, hi, q, hq⟩ := mem_iUnion₂.mp hxB
    have hscalar := (nk i).scalar_bounds_on_image_window
      ⟨(q, a i), ⟨mem_univ _, by linarith [(abs_le.mp (ha i (hts hi))).1, hlen i],
        by linarith [(abs_le.mp (ha i (hts hi))).2, hlen i]⟩, hq⟩
    exact (not_lt_of_ge (hPlow x hx)) ((hA i (hts hi)).trans_le hscalar.1)
  obtain ⟨C, hC, hCprops, hKcompact, hPK, hKreg, hKfront⟩ :=
    DifferentialGeometry.Topology.exists_finite_compact_component_union
      hBclosed.isOpen_compl hP hPout
      (fun x hx => (htcompact x hx (hPlow x hx)).1)
  let K := ⋃ V ∈ C, closure V
  let J := {i // i ∈ t}
  let e : J → OpenPartialHomeomorph Cylinder M :=
    fun i => SpatialNeck.signedLevelChart (nk i.val) (a i.val) 1 (Or.inl rfl)
  have heq (i : J) (q : Sphere 2) (z : ℝ) : e i (q, z) = (nk i.val).map (q, a i.val + z) := by
    rw [show e i = SpatialNeck.signedLevelChart (nk i.val) (a i.val) 1 (Or.inl rfl) from rfl,
      SpatialNeck.signedLevelChart_apply, one_mul]
  have hBunion : B = ⋃ i : J, range (fun q : Sphere 2 => e i (q, 0)) := by
    simp only [heq, add_zero]
    ext z
    simp only [B, mem_iUnion, exists_prop]
    constructor
    · rintro ⟨i, hi, hiz⟩
      exact ⟨⟨i, hi⟩, hiz⟩
    · rintro ⟨i, hi⟩
      exact ⟨i.val, i.property, hi⟩
  let _ : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) (by norm_num : (0 : ℝ) ≤ 1))
  have hfinite : Finite J := inferInstance
  have hfrontB : frontier K ⊆ B :=
    hKfront.trans (by rw [frontier_compl]; exact hBclosed.frontier_subset)
  obtain ⟨hfront, hcollar⟩ :=
    DifferentialGeometry.Topology.frontier_eq_iUnion_of_finite_disjoint_collars
    e (fun i q => by
      change (q, a i.val + 1 * 0) ∈ (nk i.val).map.source
      simpa using hsource i.val i.property q)
    (fun i j hij => by
      simpa only [heq, add_zero] using htdis i.property j.property (fun h => hij (Subtype.ext h)))
    hKreg (hBunion ▸ hfrontB)
  let b := t.filter
    (fun i => (range (fun q : Sphere 2 => (nk i).map (q, a i)) ∩ frontier K).Nonempty)
  have hfrontb : frontier K = ⋃ i ∈ b, range (fun q : Sphere 2 => (nk i).map (q, a i)) := by
    rw [hfront]
    ext z
    simp only [heq, add_zero, mem_iUnion, mem_ofPred_eq, b, Finset.mem_filter, exists_prop]
    constructor
    · rintro ⟨i, hi, hiz⟩
      exact ⟨i.val, ⟨i.property, hi⟩, hiz⟩
    · rintro ⟨i, ⟨hi, hif⟩, hiz⟩
      exact ⟨⟨i, hi⟩, hif, hiz⟩
  refine ⟨t, b, C, hts, Finset.filter_subset _ _, htdis, hC,
    (fun V hV => ⟨(hCprops V hV).1, (hCprops V hV).2.1, (hCprops V hV).2.2.1⟩),
    hKcompact, hPK, hKreg, ?_, hfrontb, ?_⟩
  · intro z hz
    obtain ⟨V, hV, hzV⟩ := mem_iUnion₂.mp hz
    obtain ⟨x, hx, rfl⟩ := (hC V).mp hV
    rcases (htcompact x hx (hPlow x hx)).2 hzV with hzold | hzchart
    · exact Or.inl (mem_iUnion₂.mpr ⟨x, hx, hzold⟩)
    · exact Or.inr hzchart
  · intro i hi
    obtain ⟨hit, hif⟩ := Finset.mem_filter.mp hi
    obtain ⟨r, σ, hr, hσ, hsrc, hside, hinside⟩ := hcollar ⟨i, hit⟩
      (by simpa only [heq, add_zero] using hif)
    refine ⟨r, σ, hr, hσ, ?_, ?_, ?_⟩
    · intro q z hz
      have h := hsrc (show (q, z) ∈ univ ×ˢ Ioo (-r) r from ⟨mem_univ q, hz⟩)
      change (q, a i + 1 * z) ∈ (nk i).map.source at h
      simpa only [one_mul] using h
    · simpa only [heq] using hside
    · simpa only [heq] using hinside

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
