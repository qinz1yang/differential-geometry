import DifferentialGeometry.Topology.MetricSpace.SeparatedCover
import DifferentialGeometry.Topology.Combinatorics.IntersectionChain
import DifferentialGeometry.Geometry.Neck.SpatialOverlap
import DifferentialGeometry.Geometry.Neck.SpatialCollar
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling

set_option autoImplicit false

noncomputable section

open Set Manifold
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private theorem mem_unit_slab_of_edist_le
    {M : Type*} [EMetricSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    (g : SmoothRiemannianMetric I3 M)
    (hmetric : ∀ x y : M, edist x y = riemannianEDistOf g x y)
    {eps : ℝ} {p x : M} (nk : SpatialNeck g eps p) {r : ℝ≥0}
    (hdist : edist p x ≤ r)
    (hsmall : Real.sqrt (metricScalarAt g p) * (r : ℝ) < 1 / 2) :
    x ∈ nk.map '' (univ ×ˢ Icc (-1 : ℝ) 1) := by
  apply nk.ball_subset_closed_slab (by norm_num : (0 : ℝ) < 1)
    ((one_lt_inv₀ nk.eps_pos).mpr (nk.eps_small.trans (by norm_num)))
  change riemannianEDistOf (scaleMetric (metricScalarAt g p) nk.Q_pos g) p x <
    ENNReal.ofReal (1 / 2 : ℝ)
  rw [DifferentialGeometry.edistOf_scale, ← hmetric p x]
  calc
    ENNReal.ofReal (Real.sqrt (metricScalarAt g p)) * edist p x ≤
        ENNReal.ofReal (Real.sqrt (metricScalarAt g p)) * (r : ℝ≥0∞) :=
      mul_le_mul' le_rfl hdist
    _ = ENNReal.ofReal (Real.sqrt (metricScalarAt g p) * (r : ℝ)) := by
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    _ < ENNReal.ofReal (1 / 2 : ℝ) :=
      (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr hsmall

private theorem exists_finite_connected_spatial_neck_cover_containing_of_scale_bound
    {M : Type*} [EMetricSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    (g : SmoothRiemannianMetric I3 M)
    (hmetric : ∀ x y : M, edist x y = riemannianEDistOf g x y)
    {C A : Set M} (hC : IsCompact C) (hconn : IsPreconnected C)
    (hA : A.Finite) (hAC : A ⊆ C)
    {eps : ℝ} (neck : ∀ p ∈ C, SpatialNeck g eps p)
    {r : ℝ≥0} (hr : 0 < r) (hsep : Metric.IsSeparated r A)
    (hscale : ∀ p ∈ C, Real.sqrt (metricScalarAt g p) * (4 * (r : ℝ)) < 1 / 2) :
    ∃ S : Set M, ∃ hSC : S ⊆ C, A ⊆ S ∧ S.Finite ∧
      Metric.IsSeparated r S ∧
      (∀ x ∈ C, ∃ p : M, ∃ hp : p ∈ S,
        x ∈ (neck p (hSC hp)).map '' (univ ×ˢ Icc (-1 : ℝ) 1)) ∧
      ∀ a b : S, Relation.ReflTransGen
        (fun p q : S =>
          (p : M) ∈ (neck q (hSC q.property)).map '' (univ ×ˢ Icc (-1 : ℝ) 1) ∧
          (q : M) ∈ (neck p (hSC p.property)).map '' (univ ×ˢ Icc (-1 : ℝ) 1)) a b := by
  obtain ⟨S, hAS, hSC, hfinite, hseparated, hcover⟩ :=
    DifferentialGeometry.Topology.exists_finite_separated_cover_containing
      hC.totallyBounded hA hAC hr hsep
  have hsmall (p : M) (hp : p ∈ C) :
      Real.sqrt (metricScalarAt g p) * (r : ℝ) < 1 / 2 :=
    (mul_le_mul_of_nonneg_left (by nlinarith [NNReal.coe_nonneg r] : (r : ℝ) ≤ 4 * (r : ℝ))
      (Real.sqrt_nonneg _)).trans_lt (hscale p hp)
  refine ⟨S, hSC, hAS, hfinite, hseparated, ?_, ?_⟩
  · intro x hx
    obtain ⟨p, hp, hdist⟩ := hcover hx
    change edist x p ≤ (r : ℝ≥0∞) at hdist
    refine ⟨p, hp, mem_unit_slab_of_edist_le g hmetric (neck p (hSC hp))
      (by simpa only [edist_comm] using hdist) (hsmall p (hSC hp))⟩
  · intro a b
    apply Relation.ReflTransGen.mono
      (r := fun p q : S => edist (p : M) q < (4 * r : ℝ≥0))
      (fun p q hpq => ?_) a b
      (DifferentialGeometry.Topology.reflTransGen_edist_lt_of_isPreconnected_isCover
        hconn hSC hr hcover a b)
    have hp (q : S) : Real.sqrt (metricScalarAt g q) * ((4 * r : ℝ≥0) : ℝ) < 1 / 2 :=
      by simpa only [NNReal.coe_mul, NNReal.coe_ofNat] using hscale q (hSC q.property)
    exact ⟨mem_unit_slab_of_edist_le g hmetric (neck q (hSC q.property))
        (by simpa only [edist_comm] using hpq.le) (hp q),
      mem_unit_slab_of_edist_le g hmetric (neck p (hSC p.property)) hpq.le (hp p)⟩

private theorem exists_finite_connected_spatial_neck_cover_containing_of_edist_eq
    {M : Type*} [EMetricSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    (g : SmoothRiemannianMetric I3 M)
    (hmetric : ∀ x y : M, edist x y = riemannianEDistOf g x y)
    {C A : Set M} (hC : IsCompact C) (hconn : IsPreconnected C)
    (hA : A.Finite) (hAC : A ⊆ C)
    {eps : ℝ} (neck : ∀ p ∈ C, SpatialNeck g eps p) :
    ∃ r : ℝ≥0, 0 < r ∧ ∃ S : Set M, ∃ hSC : S ⊆ C,
      A ⊆ S ∧ S.Finite ∧ Metric.IsSeparated r S ∧
      (∀ x ∈ C, ∃ p : M, ∃ hp : p ∈ S,
        x ∈ (neck p (hSC hp)).map '' (univ ×ˢ Icc (-1 : ℝ) 1)) ∧
      ∀ a b : S, Relation.ReflTransGen
        (fun p q : S =>
          (p : M) ∈ (neck q (hSC q.property)).map '' (univ ×ˢ Icc (-1 : ℝ) 1) ∧
          (q : M) ∈ (neck p (hSC p.property)).map '' (univ ×ˢ Icc (-1 : ℝ) 1)) a b := by
  obtain ⟨s, hs, hsep⟩ := DifferentialGeometry.Topology.exists_pos_isSeparated_of_finite hA
  have hc : Continuous (fun p : M => Real.sqrt (metricScalarAt g p)) :=
    Real.continuous_sqrt.comp (metricScalar_smooth g).continuous
  obtain ⟨B, hB⟩ := hC.bddAbove_image hc.continuousOn
  let b : ℝ := max 1 B
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let t : ℝ≥0 := ⟨1 / (16 * b), by positivity⟩
  let r : ℝ≥0 := min s t
  have ht : 0 < t := by change (0 : ℝ) < 1 / (16 * b); positivity
  have hr : 0 < r := lt_min hs ht
  have hrs : r ≤ s := min_le_left _ _
  have hrt : (r : ℝ) ≤ 1 / (16 * b) := by
    exact_mod_cast (min_le_right s t)
  have hscale (p : M) (hp : p ∈ C) :
      Real.sqrt (metricScalarAt g p) * (4 * (r : ℝ)) < 1 / 2 := by
    have hpB : Real.sqrt (metricScalarAt g p) ≤ b :=
      (hB ⟨p, hp, rfl⟩).trans (le_max_right _ _)
    have hprod : (r : ℝ) * (16 * b) ≤ 1 :=
      (le_div_iff₀ (by positivity : 0 < 16 * b)).mp hrt
    have hmul := mul_le_mul_of_nonneg_right hpB (NNReal.coe_nonneg r)
    nlinarith
  exact ⟨r, hr, exists_finite_connected_spatial_neck_cover_containing_of_scale_bound
    g hmetric hC hconn hA hAC neck hr (hsep.anti (by exact_mod_cast hrs)) hscale⟩

open scoped Bundle in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_finite_connected_spatial_neck_cover_containing
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold I3 ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric I3 M)
    {C A : Set M} (hC : IsCompact C) (hconn : IsPreconnected C)
    (hA : A.Finite) (hAC : A ⊆ C)
    {eps : ℝ} (neck : ∀ p ∈ C, SpatialNeck g eps p) :
    ∃ r : ℝ≥0, 0 < r ∧ ∃ S : Set M, ∃ hSC : S ⊆ C,
      A ⊆ S ∧ S.Finite ∧
      S.Pairwise (fun p q => (r : ℝ≥0∞) < riemannianEDistOf g p q) ∧
      (∀ x ∈ C, ∃ p : M, ∃ hp : p ∈ S,
        x ∈ (neck p (hSC hp)).map '' (univ ×ˢ Icc (-1 : ℝ) 1)) ∧
      ∀ a b : S, Relation.ReflTransGen
        (fun p q : S =>
          (p : M) ∈ (neck q (hSC q.property)).map '' (univ ×ˢ Icc (-1 : ℝ) 1) ∧
          (q : M) ∈ (neck p (hSC p.property)).map '' (univ ×ˢ Icc (-1 : ℝ) 1)) a b := by
  let : IsManifold I3 1 M := IsManifold.of_le (n := ∞) (by decide)
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace ThreeSpace M
  let : T3Space M := inferInstance
  let : Bundle.RiemannianBundle (fun x : M => TangentSpace I3 x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle ThreeSpace (fun x : M => TangentSpace I3 x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I3 M
  exact exists_finite_connected_spatial_neck_cover_containing_of_edist_eq g (fun _ _ => rfl)
    hC hconn hA hAC neck

theorem exists_spatial_neck_chain_with_disjoint_nonadjacent_slabs
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold I3 ∞ M]
    (g : SmoothRiemannianMetric I3 M)
    {C : Set M} (hC : IsPreconnected C)
    {eps : ℝ} (neck : ∀ p ∈ C, SpatialNeck g eps p) (a b : C) :
    ∃ n : ℕ, ∃ p : Fin (n + 1) → C,
      p 0 = a ∧ p (Fin.last n) = b ∧ Function.Injective p ∧
      (∀ i : Fin n,
        ((neck (p i.castSucc) (p i.castSucc).property).map '' (univ ×ˢ Icc (-1 : ℝ) 1) ∩
          (neck (p i.succ) (p i.succ).property).map '' (univ ×ˢ Icc (-1 : ℝ) 1)).Nonempty) ∧
      ∀ i j : Fin (n + 1), i.val + 1 < j.val →
        Disjoint ((neck (p i) (p i).property).map '' (univ ×ˢ Icc (-1 : ℝ) 1))
          ((neck (p j) (p j).property).map '' (univ ×ˢ Icc (-1 : ℝ) 1)) := by
  let U : C → Set M := fun p => (neck p p.property).map '' (univ ×ˢ Ioo (-1 : ℝ) 1)
  let T : C → Set M := fun p => (neck p p.property).map '' (univ ×ˢ Icc (-1 : ℝ) 1)
  have hUT (p : C) : U p ⊆ T p := image_mono (prod_mono_right Ioo_subset_Icc_self)
  have hopen (p : C) : IsOpen (U p) := by
    have hlen : (1 : ℝ) < eps⁻¹ :=
      (one_lt_inv₀ (neck p p.property).eps_pos).mpr
        ((neck p p.property).eps_small.trans (by norm_num))
    apply (neck p p.property).map.toOpenPartialHomeomorph.isOpen_image_of_subset_source
      (isOpen_univ.prod isOpen_Ioo)
    intro y hy
    exact (neck p p.property).domain ⟨hy.1,
      (neg_lt_neg hlen).trans hy.2.1, hy.2.2.trans hlen⟩
  have hcenter (p : C) : (p : M) ∈ U p :=
    ⟨((neck p p.property).center, 0), ⟨mem_univ _, by norm_num⟩,
      (neck p p.property).center_eq⟩
  let V : C → Set C := fun p => Subtype.val ⁻¹' U p
  have hV : ⋃ p, V p = univ := by
    apply eq_univ_of_forall
    intro p
    exact mem_iUnion.mpr ⟨p, hcenter p⟩
  let : PreconnectedSpace C := isPreconnected_iff_preconnectedSpace.mp hC
  have hconn : IsPreconnected (⋃ p, V p) := hV.symm ▸ isPreconnected_univ
  have hpath := (hconn.transGen_of_iUnion
    (fun p => (hopen p).preimage continuous_subtype_val) a b
    ⟨a, hcenter a⟩ ⟨b, hcenter b⟩).to_reflTransGen
  have hclosedPath : Relation.ReflTransGen (fun p q : C => (T p ∩ T q).Nonempty) a b := by
    apply Relation.ReflTransGen.mono (fun p q hpq => ?_) a b hpath
    obtain ⟨x, hx, hy⟩ := hpq
    exact ⟨x, hUT p hx, hUT q hy⟩
  exact
    DifferentialGeometry.Topology.exists_chain_with_disjoint_nonadjacent_of_intersection_reachable
      T hclosedPath

universe u

theorem exists_spatial_neck_chain_with_controlled_overlaps :
    ∃ eta : ℝ, 0 < eta ∧ eta < 1 / 200000 ∧
      ∀ eps : ℝ, eps ≤ eta →
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M]
          (g : SmoothRiemannianMetric I3 M) (C : Set M), IsPreconnected C →
          ∀ (neck : ∀ p ∈ C, SpatialNeck g eps p) (a b : C),
          ∃ n : ℕ, ∃ p : Fin (n + 1) → C,
            p 0 = a ∧ p (Fin.last n) = b ∧ Function.Injective p ∧
            (∀ i j : Fin (n + 1), i.val + 1 < j.val →
              Disjoint ((neck (p i) (p i).property).map '' (univ ×ˢ Icc (-1 : ℝ) 1))
                ((neck (p j) (p j).property).map '' (univ ×ˢ Icc (-1 : ℝ) 1))) ∧
            ∀ j : Fin n,
              let nk₀ := neck (p j.castSucc) (p j.castSucc).property
              let nk₁ := neck (p j.succ) (p j.succ).property
              let S := nk₀.map '' (univ ×ˢ Icc (-1 : ℝ) 1) ∪
                nk₁.map '' (univ ×ˢ Icc (-1 : ℝ) 1)
              (nk₀.map '' (univ ×ˢ Icc (-1 : ℝ) 1) ∩
                nk₁.map '' (univ ×ˢ Icc (-1 : ℝ) 1)).Nonempty ∧
              IsCompact S ∧ IsConnected S ∧
              S ⊆ nk₀.map '' (univ ×ˢ Ioo (-eps⁻¹ + 1) (eps⁻¹ - 1)) ∧
              S ⊆ nk₁.map '' (univ ×ˢ Ioo (-eps⁻¹ + 1) (eps⁻¹ - 1)) ∧
              ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ x ∈ S,
                Real.sqrt (g.inner x
                  (Geometry.Operator.gradFun g nk₀.cylindricalChart.axial x -
                    σ • Geometry.Operator.gradFun g nk₁.cylindricalChart.axial x)
                  (Geometry.Operator.gradFun g nk₀.cylindricalChart.axial x -
                    σ • Geometry.Operator.gradFun g nk₁.cylindricalChart.axial x)) ≤
                369424 * eps := by
  obtain ⟨eta, heta, hsmall, hoverlap⟩ := exists_spatial_neck_intersection_tolerance.{u}
  refine ⟨eta, heta, hsmall, ?_⟩
  intro eps heps M _ _ _ _ g C hC neck a b
  obtain ⟨n, p, hfirst, hlast, hinj, hmeet, hdisj⟩ :=
    exists_spatial_neck_chain_with_disjoint_nonadjacent_slabs g hC neck a b
  refine ⟨n, p, hfirst, hlast, hinj, hdisj, ?_⟩
  intro j
  exact ⟨hmeet j, hoverlap eps heps M g (p j.castSucc) (p j.succ)
    (neck (p j.castSucc) (p j.castSucc).property)
    (neck (p j.succ) (p j.succ).property) (hmeet j)⟩

theorem exists_spatial_neck_chain_with_ordered_overlap_bands :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ eps : ℝ, eps ≤ eta →
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M]
          (g : SmoothRiemannianMetric I3 M) (C : Set M), IsPreconnected C →
          ∀ (neck : ∀ p ∈ C, SpatialNeck g eps p) (a b : C),
          ∃ n : ℕ, ∃ p : Fin (n + 1) → C,
            p 0 = a ∧ p (Fin.last n) = b ∧ Function.Injective p ∧
            (∀ i j : Fin (n + 1), i.val + 1 < j.val →
              Disjoint ((neck (p i) (p i).property).map '' (univ ×ˢ Icc (-1 : ℝ) 1))
                ((neck (p j) (p j).property).map '' (univ ×ˢ Icc (-1 : ℝ) 1))) ∧
            ∀ j : Fin n,
              let nk₀ := neck (p j.castSucc) (p j.castSucc).property
              let nk₁ := neck (p j.succ) (p j.succ).property
              let S := nk₀.map '' (univ ×ˢ Icc (-1 : ℝ) 1) ∪
                nk₁.map '' (univ ×ˢ Icc (-1 : ℝ) 1)
              S ⊆ nk₀.map '' (univ ×ˢ Ioo (-eps⁻¹ + 1) (eps⁻¹ - 1)) ∧
              S ⊆ nk₁.map '' (univ ×ˢ Ioo (-eps⁻¹ + 1) (eps⁻¹ - 1)) ∧
              ∃ z : M, z ∈ nk₀.map '' (univ ×ˢ Icc (-1 : ℝ) 1) ∧
                z ∈ nk₁.map '' (univ ×ˢ Icc (-1 : ℝ) 1) ∧
                ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
                  let c := nk₀.cylindricalChart.axial z - σ * nk₁.cylindricalChart.axial z
                  let ψ := fun x : Sphere 2 × Icc (-1 : ℝ) 1 =>
                    nk₁.map.symm (nk₀.map (x.1, (x.2 : ℝ)))
                  let e := fun x => ((ψ x).1,
                    σ * ((Real.sqrt (metricScalarAt g (p j.succ)))⁻¹ * (ψ x).2) + c)
                  ∃ h : C(Sphere 2 × Icc (-1 : ℝ) 1, ℝ),
                    (∀ x, e x = ((e x).1, h ((e x).1, x.2))) ∧
                    (∀ q, StrictMono (fun t => h (q, t))) ∧
                    range e = {y | h (y.1, ⟨-1, le_rfl, by norm_num⟩) ≤ y.2 ∧
                      y.2 ≤ h (y.1, ⟨1, by norm_num, le_rfl⟩)} ∧
                    ∀ s t : Icc (-1 : ℝ) 1,
                      e '' ((univ : Set (Sphere 2)) ×ˢ Icc s t) =
                        {y | h (y.1, s) ≤ y.2 ∧ y.2 ≤ h (y.1, t)} := by
  obtain ⟨eta, heta, hband⟩ := exists_spatial_neck_ordered_overlap_tolerance.{u}
  refine ⟨eta, heta, ?_⟩
  intro eps heps M _ _ _ _ g C hC neck a b
  obtain ⟨n, p, hfirst, hlast, hinj, hmeet, hdisj⟩ :=
    exists_spatial_neck_chain_with_disjoint_nonadjacent_slabs g hC neck a b
  refine ⟨n, p, hfirst, hlast, hinj, hdisj, ?_⟩
  intro j
  obtain ⟨z, hz₀, hz₁⟩ := hmeet j
  obtain ⟨hsub₀, hsub₁, hordered⟩ := hband eps heps M g (p j.castSucc) (p j.succ)
    (neck (p j.castSucc) (p j.castSucc).property)
    (neck (p j.succ) (p j.succ).property) z hz₀ hz₁
  exact ⟨hsub₀, hsub₁, z, hz₀, hz₁, hordered⟩

theorem exists_spatial_neck_chain_with_ordered_neighbor_slabs :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ eps : ℝ, eps ≤ eta →
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M]
          (g : SmoothRiemannianMetric I3 M) (C : Set M), IsPreconnected C →
          ∀ (neck : ∀ p ∈ C, SpatialNeck g eps p) (a b : C),
          ∃ n : ℕ, ∃ p : Fin (n + 1) → C,
            p 0 = a ∧ p (Fin.last n) = b ∧ Function.Injective p ∧
            (∀ j : Fin n,
              ((neck (p j.castSucc) (p j.castSucc).property).map '' (univ ×ˢ Icc (-1 : ℝ) 1) ∩
                (neck (p j.succ) (p j.succ).property).map '' (univ ×ˢ Icc (-1 : ℝ) 1)).Nonempty) ∧
            (∀ i j : Fin (n + 1), i.val + 1 < j.val →
              Disjoint ((neck (p i) (p i).property).map '' (univ ×ˢ Icc (-1 : ℝ) 1))
                ((neck (p j) (p j).property).map '' (univ ×ˢ Icc (-1 : ℝ) 1))) ∧
            ∀ i j k : Fin (n + 1), i.val + 1 = j.val → j.val + 1 = k.val →
              let ni := neck (p i) (p i).property
              let nj := neck (p j) (p j).property
              let nk := neck (p k) (p k).property
              ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
                ∀ x ∈ ni.map '' (univ ×ˢ Icc (-1 : ℝ) 1),
                  ∀ y ∈ nk.map '' (univ ×ˢ Icc (-1 : ℝ) 1),
                    (nj.map.symm x).1 = (nj.map.symm y).1 →
                    σ * (nj.map.symm x).2 < σ * (nj.map.symm y).2 := by
  obtain ⟨eta, heta, horder⟩ := exists_spatial_neck_triple_order_tolerance.{u}
  refine ⟨eta, heta, ?_⟩
  intro eps heps M _ _ _ _ g C hC neck a b
  obtain ⟨n, p, hfirst, hlast, hinj, hmeet, hdisj⟩ :=
    exists_spatial_neck_chain_with_disjoint_nonadjacent_slabs g hC neck a b
  refine ⟨n, p, hfirst, hlast, hinj, hmeet, hdisj, ?_⟩
  intro i j k hij hjk
  have hi : i.val < n := by omega
  have hj : j.val < n := by omega
  let i' : Fin n := ⟨i.val, hi⟩
  let j' : Fin n := ⟨j.val, hj⟩
  have hi₀ : i'.castSucc = i := Fin.ext rfl
  have hi₁ : i'.succ = j := Fin.ext hij
  have hj₀ : j'.castSucc = j := Fin.ext rfl
  have hj₁ : j'.succ = k := Fin.ext hjk
  have hleft := hmeet i'
  rw [hi₀, hi₁] at hleft
  have hright := hmeet j'
  rw [hj₀, hj₁, inter_comm] at hright
  exact horder eps heps M g (p i) (p j) (p k)
    (neck (p i) (p i).property) (neck (p j) (p j).property) (neck (p k) (p k).property)
    hleft hright (hdisj i k (by omega))

theorem exists_spatial_neck_chain_with_shared_collars :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ eps : ℝ, eps ≤ eta →
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M]
          (g : SmoothRiemannianMetric I3 M) (C : Set M), IsPreconnected C →
          ∀ (neck : ∀ p ∈ C, SpatialNeck g eps p) (a b : C),
          ∃ n : ℕ, ∃ p : Fin (n + 1) → C,
            p 0 = a ∧ p (Fin.last n) = b ∧ Function.Injective p ∧
            (∀ i j : Fin (n + 1), i.val + 1 < j.val →
              Disjoint ((neck (p i) (p i).property).map '' (univ ×ˢ Icc (-1 : ℝ) 1))
                ((neck (p j) (p j).property).map '' (univ ×ˢ Icc (-1 : ℝ) 1))) ∧
            ∀ j : Fin n,
              let nk₀ := neck (p j.castSucc) (p j.castSucc).property
              let nk₁ := neck (p j.succ) (p j.succ).property
              ∃ c : DifferentialGeometry.Topology.SmoothTwoSidedCollar I2 I3
                  (fun q : Sphere 2 => nk₀.map (q, 0)),
                c.radius < 1 ∧
                (∀ x : Sphere 2 × DifferentialGeometry.Topology.symmetricOpenInterval c.radius,
                  c.toFun x = nk₀.map (x.1, (x.2 : ℝ))) ∧
                range c.toFun ⊆ nk₀.map '' (univ ×ˢ Ioo (-1 : ℝ) 1) ∧
                range c.toFun ⊆ nk₁.map '' (univ ×ˢ Ioo (-eps⁻¹ + 1) (eps⁻¹ - 1)) ∧
                ∀ k : Fin (n + 1), (j.val + 1 < k.val ∨ k.val + 1 < j.val) →
                  Disjoint (range c.toFun)
                    ((neck (p k) (p k).property).map '' (univ ×ˢ Icc (-1 : ℝ) 1)) := by
  obtain ⟨eta, heta, hcollar⟩ := exists_spatial_neck_shared_collar_tolerance.{u}
  refine ⟨eta, heta, ?_⟩
  intro eps heps M _ _ _ _ g C hC neck a b
  obtain ⟨n, p, hfirst, hlast, hinj, hmeet, hdisj⟩ :=
    exists_spatial_neck_chain_with_disjoint_nonadjacent_slabs g hC neck a b
  refine ⟨n, p, hfirst, hlast, hinj, hdisj, ?_⟩
  intro j
  obtain ⟨c, hcr, heq, hsource, htarget⟩ := hcollar eps heps M g
    (p j.castSucc) (p j.succ) (neck (p j.castSucc) (p j.castSucc).property)
    (neck (p j.succ) (p j.succ).property) (hmeet j) 0 (by norm_num)
  refine ⟨c, by simpa only [zero_add, sub_zero, min_self] using hcr,
    (fun x => by simpa only [zero_add] using heq x), hsource, htarget, ?_⟩
  intro k hk
  have hsub := hsource.trans (image_mono (prod_mono_right Ioo_subset_Icc_self))
  rcases hk with hk | hk
  · exact (hdisj j.castSucc k hk).mono_left hsub
  · exact (hdisj k j.castSucc hk).symm.mono_left hsub


section

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
  {g : SmoothRiemannianMetric I3 M} {eps : ℝ}

private theorem SpatialNeck.scalar_le_twice_of_intersect_unit_slabs
    {x y : M} (nx : SpatialNeck g eps x) (ny : SpatialNeck g eps y) (heps : eps ≤ 1 / 20000)
    (hmeet : (nx.map '' (univ ×ˢ Icc (-1 : ℝ) 1) ∩ ny.map '' (univ ×ˢ Icc (-1 : ℝ) 1)).Nonempty) :
    metricScalarAt g y ≤ 2 * metricScalarAt g x := by
  obtain ⟨z, hzx, hzy⟩ := hmeet
  have hwindow : (univ : Set (Sphere 2)) ×ˢ Icc (-1 : ℝ) 1 ⊆ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹ := by
    have hinv : (1 : ℝ) < eps⁻¹ := (one_lt_inv₀ nx.eps_pos).mpr (by linarith)
    intro p hp
    exact ⟨hp.1, by constructor <;> linarith [hp.2.1, hp.2.2]⟩
  have hx := (nx.scalar_bounds_on_image_window ((image_mono hwindow) hzx)).2
  have hy := (ny.scalar_bounds_on_image_window ((image_mono hwindow) hzy)).1
  have hposx := nx.Q_pos
  have hposy := ny.Q_pos
  nlinarith

private theorem scalar_le_pow_two_of_neck_chain
    {n : ℕ} (p : Fin (n + 1) → M) (neck : ∀ j, SpatialNeck g eps (p j))
    (heps : eps ≤ 1 / 20000)
    (hmeet : ∀ j : Fin n,
      ((neck j.castSucc).map '' (univ ×ˢ Icc (-1 : ℝ) 1) ∩
        (neck j.succ).map '' (univ ×ˢ Icc (-1 : ℝ) 1)).Nonempty) :
    metricScalarAt g (p (Fin.last n)) ≤ (2 : ℝ) ^ n * metricScalarAt g (p 0) := by
  have hb (j : Fin (n + 1)) : metricScalarAt g (p j) ≤ (2 : ℝ) ^ j.val * metricScalarAt g (p 0) := by
    induction j using Fin.induction with
    | zero => simp
    | succ j ih =>
      have hs := (neck j.castSucc).scalar_le_twice_of_intersect_unit_slabs (neck j.succ) heps (hmeet j)
      calc
        metricScalarAt g (p j.succ) ≤ 2 * metricScalarAt g (p j.castSucc) := hs
        _ ≤ 2 * ((2 : ℝ) ^ j.val * metricScalarAt g (p 0)) := by
          exact mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (2 : ℝ) ^ j.succ.val * metricScalarAt g (p 0) := by
          rw [Fin.val_succ, pow_succ]
          ring
  exact hb (Fin.last n)


theorem exists_long_spatial_neck_chain_of_scalar_ratio
    {C : Set M} (hC : IsPreconnected C)
    (neck : ∀ p ∈ C, SpatialNeck g eps p) (heps : eps ≤ 1 / 20000)
    (a b : C) (N : ℕ)
    (hratio : (2 : ℝ) ^ N * metricScalarAt g a ≤ metricScalarAt g b) :
    ∃ n : ℕ, N ≤ n ∧ ∃ p : Fin (n + 1) → C,
      p 0 = a ∧ p (Fin.last n) = b ∧ Function.Injective p ∧
      (∀ i : Fin n,
        ((neck (p i.castSucc) (p i.castSucc).property).map '' (univ ×ˢ Icc (-1 : ℝ) 1) ∩
          (neck (p i.succ) (p i.succ).property).map '' (univ ×ˢ Icc (-1 : ℝ) 1)).Nonempty) ∧
      ∀ i j : Fin (n + 1), i.val + 1 < j.val →
        Disjoint ((neck (p i) (p i).property).map '' (univ ×ˢ Icc (-1 : ℝ) 1))
          ((neck (p j) (p j).property).map '' (univ ×ˢ Icc (-1 : ℝ) 1)) := by
  obtain ⟨n, p, hp0, hpn, hinj, hmeet, hdisj⟩ :=
    exists_spatial_neck_chain_with_disjoint_nonadjacent_slabs g hC neck a b
  have hscale := scalar_le_pow_two_of_neck_chain
    (fun j => (p j).val) (fun j => neck (p j) (p j).property) heps hmeet
  rw [hp0, hpn] at hscale
  have hN : N ≤ n := by
    by_contra hn
    have hpow : (2 : ℝ) ^ n < (2 : ℝ) ^ N := pow_lt_pow_right₀ (by norm_num) (lt_of_not_ge hn)
    have hQ := (neck a a.property).Q_pos
    have hmul := mul_lt_mul_of_pos_right hpow hQ
    exact (not_lt_of_ge (hratio.trans hscale)) hmul
  exact ⟨n, hN, p, hp0, hpn, hinj, hmeet, hdisj⟩


end

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
