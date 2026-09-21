import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckRegionBall
import DifferentialGeometry.Geometry.Metric.Distance.Topology

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology ENNReal Bundle

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private instance neckPackingSphereDimension : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) :=
  ⟨by simp [ThreeSpace]⟩

private theorem central_sphere_edist_lt_of_round_edist_lt
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {x : M}
    (nk : SpatialNeck g eps x) {p q : Sphere 2} {r : ℝ}
    (hpq : riemannianEDistOf (roundMetric (E := ThreeSpace) (n := 2)) p q < ENNReal.ofReal r) :
    riemannianEDistOf (scaleMetric (metricScalarAt g x) nk.Q_pos g)
      (nk.map (p, 0)) (nk.map (q, 0)) < ENNReal.ofReal (4 * r) := by
  obtain ⟨gamma, hstart, hend, hgamma, hlength⟩ :=
    exists_lt_of_edistOf_lt (roundMetric (E := ThreeSpace) (n := 2)) hpq
  have hcyl : ContMDiffOn 𝓘(ℝ, ℝ) IC 1 (fun s => (gamma s, (0 : ℝ))) (Icc (0 : ℝ) 1) :=
    hgamma.prodMk contMDiffOn_const
  have hinside : ∀ s ∈ Icc (0 : ℝ) 1,
      (gamma s, (0 : ℝ)) ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹ := by
    intro s _
    exact ⟨mem_univ _, neg_lt_zero.mpr (inv_pos.mpr nk.eps_pos), inv_pos.mpr nk.eps_pos⟩
  have hcomp : ContMDiffOn 𝓘(ℝ, ℝ) I3 1
      ((nk.map : Cylinder → M) ∘ (fun s => (gamma s, (0 : ℝ)))) (Icc (0 : ℝ) 1) :=
    (nk.map.contMDiffOn_toFun.of_le (by simp)).comp hcyl (fun s hs => nk.domain (hinside s hs))
  have hdist := edistOf_le_metricPathELength
    (scaleMetric (metricScalarAt g x) nk.Q_pos g) (by norm_num : (0 : ℝ) ≤ 1) hcomp
  simp only [Function.comp_apply, hstart, hend] at hdist
  have hupper := (collar_pathELength_bounds nk.cylinder _ nk.map nk.comparison rfl
    nk.eps_pos.le (by linarith [nk.eps_small]) (by norm_num) nk.domain hcyl hinside).2
  have htrans := nk.cylinder.transverse_length_le 0 hgamma
  have hsqrt : Real.sqrt (2 : ℝ) ≤ 2 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsqrt' : Real.sqrt (1 + eps) ≤ 2 :=
    (Real.sqrt_le_iff).mpr ⟨by norm_num, by linarith [nk.eps_small]⟩
  calc
    _ ≤ ENNReal.ofReal (Real.sqrt (1 + eps)) *
        (ENNReal.ofReal (Real.sqrt 2) *
          metricPathELength (roundMetric (E := ThreeSpace) (n := 2)) gamma 0 1) :=
      hdist.trans (hupper.trans (mul_le_mul' le_rfl htrans))
    _ ≤ ENNReal.ofReal (4 : ℝ) *
        metricPathELength (roundMetric (E := ThreeSpace) (n := 2)) gamma 0 1 := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal (by nlinarith [Real.sqrt_nonneg (1 + eps)])) le_rfl
    _ < ENNReal.ofReal (4 : ℝ) * ENNReal.ofReal r :=
      (ENNReal.mul_lt_mul_iff_right (by norm_num) ENNReal.ofReal_ne_top).mpr hlength
    _ = _ := (ENNReal.ofReal_mul (by norm_num)).symm

private theorem exists_round_sphere_net {r : ℝ} (hr : 0 < r) :
    ∃ A : Finset (Sphere 2), ∀ p : Sphere 2, ∃ q ∈ A,
      riemannianEDistOf (roundMetric (E := ThreeSpace) (n := 2)) p q < ENNReal.ofReal r := by
  let _ : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank
      (by simp [ThreeSpace] : 1 < Module.finrank ℝ ThreeSpace)) (0 : ThreeSpace)
      (by norm_num : (0 : ℝ) ≤ 1))
  let g := roundMetric (E := ThreeSpace) (n := 2)
  let m : MetricSpace (Sphere 2) :=
    let _ : PseudoMetricSpace (Sphere 2) := g.toPseudoMetricSpace
    MetricSpace.ofT0PseudoMetricSpace (Sphere 2)
  let _ : MetricSpace (Sphere 2) := m
  let e : PseudoEMetricSpace (Sphere 2) :=
    @PseudoMetricSpace.toPseudoEMetricSpace (Sphere 2) m.toPseudoMetricSpace
  let _ : WeakPseudoEMetricSpace (Sphere 2) :=
    @PseudoEMetricSpace.toWeakPseudoEMetricSpace (Sphere 2) e
  obtain ⟨A, hA⟩ := (isCompact_univ : IsCompact (univ : Set (Sphere 2))).elim_finite_subcover
    (fun q => Metric.eball q (ENNReal.ofReal r)) (fun _ => Metric.isOpen_eball) (by
      intro p _
      exact mem_iUnion.mpr ⟨p, by simpa only [Metric.mem_eball, edist_self] using ENNReal.ofReal_pos.mpr hr⟩)
  refine ⟨A, fun p => ?_⟩
  obtain ⟨q, hq⟩ := mem_iUnion.mp (hA (mem_univ p))
  obtain ⟨hqA, hpq⟩ := mem_iUnion.mp hq
  exact ⟨q, hqA, hpq⟩

theorem exists_uniform_central_sphere_cover {eta : ℝ} (heta : 0 < eta) :
    ∃ A : Finset (Sphere 2), ∀ {M : Type*} [TopologicalSpace M]
      [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
      {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {x : M}
      (nk : SpatialNeck g eps x) (p : Sphere 2), ∃ q ∈ A,
        riemannianEDistOf (scaleMetric (metricScalarAt g x) nk.Q_pos g)
          (nk.map (p, 0)) (nk.map (q, 0)) < ENNReal.ofReal eta := by
  obtain ⟨A, hA⟩ := exists_round_sphere_net (show 0 < eta / 4 by positivity)
  refine ⟨A, fun {_} _ _ _ {_} {_} {_} nk p => ?_⟩
  obtain ⟨q, hqA, hpq⟩ := hA p
  refine ⟨q, hqA, ?_⟩
  simpa only [mul_div_cancel₀ _ (by norm_num : (4 : ℝ) ≠ 0)] using
    central_sphere_edist_lt_of_round_edist_lt nk hpq

theorem exists_uniform_central_sphere_packing_bound {eta : ℝ} (heta : 0 < eta) :
    ∃ N : ℕ, ∀ {M : Type*} [MetricSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
      {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {x : M}
      (nk : SpatialNeck g eps x),
      (∀ y z : M, edist y z = riemannianEDistOf g y z) →
      ∀ S : Finset M, (S : Set M) ⊆ nk.map '' (univ ×ˢ {(0 : ℝ)}) →
        (S : Set M).Pairwise (fun y z => eta ≤ Real.sqrt (metricScalarAt g x) * dist y z) →
        S.card ≤ N := by
  classical
  obtain ⟨A, hA⟩ := exists_uniform_central_sphere_cover (show 0 < eta / 3 by positivity)
  refine ⟨A.card, fun {M} _ _ _ {g} {eps} {x} nk hmetric S hS hsep => ?_⟩
  have hcover (y : S) : ∃ q ∈ A,
      Real.sqrt (metricScalarAt g x) * dist (y : M) (nk.map (q, 0)) < eta / 3 := by
    obtain ⟨⟨p, z⟩, ⟨_, hz⟩, hpy⟩ := hS y.property
    have hz0 : z = 0 := hz
    subst z
    obtain ⟨q, hqA, hpq⟩ := hA nk p
    rw [edistOf_scale, ← hmetric, edist_dist,
      ← ENNReal.ofReal_mul (Real.sqrt_nonneg _), hpy] at hpq
    exact ⟨q, hqA, (ENNReal.ofReal_lt_ofReal_iff_of_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) dist_nonneg)).mp hpq⟩
  choose color hcolor hclose using hcover
  let f : S → A := fun y => ⟨color y, hcolor y⟩
  have hinj : Function.Injective f := by
    intro y z heq
    apply Subtype.ext
    by_contra hyz
    have hcol : color y = color z := congrArg Subtype.val heq
    have hy := hclose y
    have hz := hclose z
    rw [← hcol] at hz
    have ht := mul_le_mul_of_nonneg_left
      (dist_triangle (y : M) (nk.map (color y, 0)) (z : M))
      (Real.sqrt_nonneg (metricScalarAt g x))
    rw [dist_comm (nk.map (color y, 0)) (z : M), mul_add] at ht
    have hl := hsep y.property z.property hyz
    linarith only [hy, hz, ht, hl, heta]
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hinj

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
