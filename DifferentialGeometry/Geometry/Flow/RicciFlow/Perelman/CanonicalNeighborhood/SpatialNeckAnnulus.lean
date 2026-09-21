import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialNeckOverlap
import DifferentialGeometry.Topology.Manifold.GraphBand

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M]

theorem SpatialNeck.image_graphBand_subset_closedBalls
    {g : SmoothRiemannianMetric I3 M} {eps₀ eps₁ r : ℝ} {x y : M}
    (nk₀ : SpatialNeck g eps₀ x) (nk₁ : SpatialNeck g eps₁ y)
    (eta : Sphere 2 → Sphere 2) (height : Sphere 2 → ℝ)
    (hfit : r < eps₀⁻¹) (hheight : ∀ p, |height p| ≤ r)
    (hgraph : ∀ p, nk₀.map (p, height p) = nk₁.map (eta p, 0)) :
    nk₀.map '' {z : Cylinder | z.2 ∈ uIcc 0 (height z.1)} ⊆
      riemannianClosedBallOf g x
        ((r + 6) * Real.sqrt (1 + eps₀) / Real.sqrt (metricScalarAt g x)) ∩
      riemannianClosedBallOf g y
        (r * Real.sqrt (1 + eps₀) / Real.sqrt (metricScalarAt g x) +
          7 / Real.sqrt (metricScalarAt g y)) := by
  have hr : 0 ≤ r := (abs_nonneg (height nk₀.center)).trans (hheight nk₀.center)
  have hmem (z : ℝ) (hz : z ∈ Icc (-r) r) : z ∈ Ioo (-eps₀⁻¹) eps₀⁻¹ :=
    ⟨by linarith [hz.1], by linarith [hz.2]⟩
  rintro z ⟨⟨p, u⟩, hu, rfl⟩
  change u ∈ uIcc 0 (height p) at hu
  have hp : height p ∈ Icc (-r) r := abs_le.mp (hheight p)
  have hur : u ∈ Icc (-r) r := uIcc_subset_Icc ⟨by linarith, hr⟩ hp hu
  refine ⟨nk₀.image_slab_subset_closedBall hr hfit ⟨(p, u), ⟨mem_univ _, hur⟩, rfl⟩, ?_⟩
  have hgap : |height p - u| ≤ r := by
    rcases le_total 0 (height p) with hh | hh
    · rw [uIcc_of_le hh] at hu
      rw [abs_of_nonneg (sub_nonneg.mpr hu.2)]
      linarith [hp.2, hu.1]
    · rw [uIcc_of_ge hh] at hu
      rw [abs_of_nonpos (sub_nonpos.mpr hu.1)]
      linarith [hp.1, hu.2]
  have haxis := (nk₀.edist_same_fiber_le p (hmem _ hp) (hmem _ hur)).trans
    (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hgap (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)))
  have hcentral : riemannianEDistOf g y (nk₀.map (p, height p)) ≤
      ENNReal.ofReal (7 / Real.sqrt (metricScalarAt g y)) := by
    rw [hgraph]
    exact nk₁.central_sphere_subset_closedBall ⟨(eta p, 0), ⟨mem_univ _, rfl⟩, rfl⟩
  have hh := (riemannianEDistOf_triangle g y (nk₀.map (p, height p)) (nk₀.map (p, u))).trans
    (add_le_add hcentral haxis)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)] at hh
  change riemannianEDistOf g y (nk₀.map (p, u)) ≤ _
  simpa only [mul_comm, add_comm] using hh

variable [T2Space M] {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {x y : M}

theorem SpatialNeck.exists_annulus_in_nearby_neck
    (nk₀ : SpatialNeck g eps x) (nk₁ : SpatialNeck g eps y)
    (hsmall : eps < 1 / 1000000)
    (hy : y ∈ nk₀.map '' (univ ×ˢ Icc (-(eps⁻¹ / 10)) (eps⁻¹ / 10)))
    (hdisjoint : Disjoint (nk₀.map '' (univ ×ˢ ({0} : Set ℝ)))
      (nk₁.map '' (univ ×ˢ ({0} : Set ℝ)))) :
    ∃ eta : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2,
      ∃ Ψ : PartialDiffeomorph IC I3 Cylinder M ∞,
        (univ ×ˢ Icc (0 : ℝ) 1 ⊆ Ψ.source) ∧
        (∀ p, Ψ (p, 0) = nk₀.map (p, 0)) ∧
        (∀ p, Ψ (p, 1) = nk₁.map (eta p, 0)) ∧
        IsCompact (Ψ '' (univ ×ˢ Icc (0 : ℝ) 1)) ∧
        (frontier (Ψ '' (univ ×ˢ Icc (0 : ℝ) 1)) =
          nk₀.map '' (univ ×ˢ ({0} : Set ℝ)) ∪
            nk₁.map '' (univ ×ˢ ({0} : Set ℝ))) ∧
        Ψ '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆
          nk₀.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) ∧
        ∃ height : Sphere 2 → ℝ, ContMDiff I2 𝓘(ℝ, ℝ) ∞ height ∧
          (∀ p, height p ∈ Ioo (-eps⁻¹) eps⁻¹) ∧
          ∀ z, Ψ z = nk₀.map (z.1, height z.1 * z.2) := by
  have hi : 0 < eps⁻¹ := inv_pos.mpr nk₀.eps_pos
  obtain ⟨eta, height, hheight, hmem, hgraph⟩ :=
    nk₀.exists_graph_in_nearby_neck nk₁ hsmall hy
      (by constructor <;> linarith : (0 : ℝ) ∈ Icc (-(eps⁻¹ / 10)) (eps⁻¹ / 10))
  have hne (p : Sphere 2) : (0 : ℝ) ≠ height p := by
    intro hp
    apply Set.disjoint_left.mp hdisjoint
      (show nk₀.map (p, 0) ∈ nk₀.map '' (univ ×ˢ ({0} : Set ℝ)) from
        ⟨(p, 0), ⟨mem_univ _, rfl⟩, rfl⟩)
    refine ⟨(eta p, 0), ⟨mem_univ _, rfl⟩, ?_⟩
    have hh := hgraph p
    rw [← hp] at hh
    exact hh.symm
  have hband : {z : Cylinder | z.2 ∈ uIcc 0 (height z.1)} ⊆
      univ ×ˢ Ioo (-eps⁻¹) eps⁻¹ := by
    intro z hz
    exact ⟨mem_univ _, (lt_min (neg_lt_zero.mpr hi) (hmem z.1).1).trans_le hz.1,
      hz.2.trans_lt (max_lt hi (hmem z.1).2)⟩
  obtain ⟨Ψ, hsource, hval, himage, hcompact, hfront⟩ :=
    DifferentialGeometry.Topology.exists_graphBand_partialDiffeomorph nk₀.map
      (fun _ ↦ 0) height contMDiff_const hheight hne (hband.trans nk₀.domain)
  have hrange (f : Cylinder → M) :
      range (fun p : Sphere 2 ↦ f (p, 0)) = f '' (univ ×ˢ ({0} : Set ℝ)) := by
    ext z
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨(p, 0), ⟨mem_univ _, rfl⟩, rfl⟩
    · rintro ⟨⟨p, t⟩, ⟨_, ht⟩, rfl⟩
      have ht0 : t = 0 := ht
      subst t
      exact ⟨p, rfl⟩
  have hupper : range (fun p ↦ nk₀.map (p, height p)) =
      range (fun p : Sphere 2 ↦ nk₁.map (p, 0)) := by
    ext z
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨eta p, (hgraph p).symm⟩
    · rintro ⟨p, rfl⟩
      refine ⟨eta.symm p, ?_⟩
      simpa only [eta.apply_symm_apply] using hgraph (eta.symm p)
  refine ⟨eta, Ψ, hsource, ?_, ?_, hcompact, ?_, ?_, height, hheight, hmem, ?_⟩
  · intro p
    simp [hval]
  · intro p
    simpa only [hval, zero_add, sub_zero, mul_one] using hgraph p
  · rw [hfront, hupper, hrange, hrange]
  · rw [himage]
    exact image_mono hband
  · intro z
    simpa only [zero_add, sub_zero] using hval z

theorem SpatialNeck.exists_annulus_in_intersection_closedBalls
    {g : SmoothRiemannianMetric I3 M} {eps r : ℝ} {x y : M}
    (nk₀ : SpatialNeck g eps x) (nk₁ : SpatialNeck g eps y)
    (hsmall : eps < 1 / 1000000) (hfit : r ≤ eps⁻¹ / 10)
    (hnear : riemannianEDistOf g x y + ENNReal.ofReal (7 / Real.sqrt (metricScalarAt g y)) <
      ENNReal.ofReal (r * Real.sqrt (1 - eps) / Real.sqrt (metricScalarAt g x)))
    (hdisjoint : Disjoint (nk₀.map '' (univ ×ˢ ({0} : Set ℝ)))
      (nk₁.map '' (univ ×ˢ ({0} : Set ℝ)))) :
    ∃ eta : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2,
      ∃ Ψ : PartialDiffeomorph IC I3 Cylinder M ∞,
        (univ ×ˢ Icc (0 : ℝ) 1 ⊆ Ψ.source) ∧
        (∀ p, Ψ (p, 0) = nk₀.map (p, 0)) ∧
        (∀ p, Ψ (p, 1) = nk₁.map (eta p, 0)) ∧
        IsCompact (Ψ '' (univ ×ˢ Icc (0 : ℝ) 1)) ∧
        (frontier (Ψ '' (univ ×ˢ Icc (0 : ℝ) 1)) =
          nk₀.map '' (univ ×ˢ ({0} : Set ℝ)) ∪
            nk₁.map '' (univ ×ˢ ({0} : Set ℝ))) ∧
        (Ψ '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆
          nk₀.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹)) ∧
        Ψ '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆
          riemannianClosedBallOf g x
            ((r + 6) * Real.sqrt (1 + eps) / Real.sqrt (metricScalarAt g x)) ∩
          riemannianClosedBallOf g y
            (r * Real.sqrt (1 + eps) / Real.sqrt (metricScalarAt g x) +
              7 / Real.sqrt (metricScalarAt g y)) := by
  have hr : 0 < r := by
    have hh := ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le hnear)
    have hp : 0 < r * Real.sqrt (1 - eps) :=
      (div_pos_iff_of_pos_right (Real.sqrt_pos.mpr nk₀.Q_pos)).mp hh
    exact pos_of_mul_pos_left hp (Real.sqrt_nonneg _)
  have hi : 0 < eps⁻¹ := inv_pos.mpr nk₀.eps_pos
  have hfit' : r < eps⁻¹ := by linarith
  have hcenter : y ∈ nk₀.map '' (univ ×ˢ Icc (-r) r) := by
    apply nk₀.ball_subset_image_slab hr hfit'
    exact (le_add_right le_rfl).trans_lt hnear
  have hy : y ∈ nk₀.map '' (univ ×ˢ Icc (-(eps⁻¹ / 10)) (eps⁻¹ / 10)) := by
    apply image_mono (s := univ ×ˢ Icc (-r) r) _ hcenter
    intro z hz
    exact ⟨hz.1, by linarith [hz.2.1], hz.2.2.trans hfit⟩
  obtain ⟨eta, Ψ, hsource, hleft, hright, hc, hf, hwindow, height, _hheight, hheightmem, hval⟩ :=
    nk₀.exists_annulus_in_nearby_neck nk₁ hsmall hy hdisjoint
  have hgraph (p : Sphere 2) : nk₀.map (p, height p) = nk₁.map (eta p, 0) := by
    have hh := (hval (p, 1)).symm.trans (hright p)
    simpa only [mul_one] using hh
  have hheight (p : Sphere 2) : |height p| ≤ r := by
    have hc : riemannianEDistOf g y (nk₁.map (eta p, 0)) ≤
        ENNReal.ofReal (7 / Real.sqrt (metricScalarAt g y)) :=
      nk₁.central_sphere_subset_closedBall ⟨(eta p, 0), ⟨mem_univ _, rfl⟩, rfl⟩
    have hd := ((riemannianEDistOf_triangle g x y (nk₁.map (eta p, 0))).trans
      (add_le_add le_rfl hc)).trans_lt hnear
    have hcap := nk₀.ball_subset_image_slab hr hfit' hd
    rw [← hgraph p] at hcap
    obtain ⟨z, hz, heq⟩ := hcap
    have hzsrc : z ∈ nk₀.map.source :=
      nk₀.domain ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
    have hpsrc : (p, height p) ∈ nk₀.map.source := nk₀.domain ⟨mem_univ _, hheightmem p⟩
    have heq' := nk₀.map.toPartialEquiv.injOn hzsrc hpsrc heq
    have hs : height p ∈ Icc (-r) r := by simpa only [heq'] using hz.2
    exact abs_le.mpr hs
  refine ⟨eta, Ψ, hsource, hleft, hright, hc, hf, hwindow, ?_⟩
  apply Subset.trans _ (nk₀.image_graphBand_subset_closedBalls nk₁ eta height hfit' hheight hgraph)
  rintro y ⟨⟨p, t⟩, ht, rfl⟩
  refine ⟨(p, height p * t), ?_, (hval (p, t)).symm⟩
  change height p * t ∈ uIcc 0 (height p)
  rcases le_total 0 (height p) with hh | hh
  · rw [uIcc_of_le hh]
    constructor <;> nlinarith [mul_nonneg hh ht.2.1,
      mul_nonneg hh (sub_nonneg.mpr ht.2.2)]
  · rw [uIcc_of_ge hh]
    constructor <;> nlinarith [mul_nonneg (neg_nonneg.mpr hh) ht.2.1,
      mul_nonneg (neg_nonneg.mpr hh) (sub_nonneg.mpr ht.2.2)]


end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
