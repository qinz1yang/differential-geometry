import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckSpatialBridge
import DifferentialGeometry.Geometry.Neck.SpatialChart
import DifferentialGeometry.Topology.Manifold.ImmersionRange
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckRegionBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoffRemainingFields

set_option autoImplicit false
noncomputable section
open Set Manifold
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u

theorem NormalizedNeck.exists_compact_long_neck_footprint
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric ThreeModel M} {δ₀ δ eps : ℝ} {k : ℕ}
    (N : NormalizedNeck g δ₀ k) (hδ : δ₀ ≤ δ) (hδ1 : δ < 1)
    (hprecision : δ₀ ≤ eps) (hsmall : eps ≤ 1 / 8646) (hk : ⌈eps⁻¹⌉₊ ≤ k)
    (a : ℝ) (ha : 24 < a) (hpublic : δ⁻¹ + 1 ≤ a) (hfit : 4 * a < eps⁻¹) :
    ∃ K : Set M,
      K = N.chart '' {z : neckBuffer δ₀ | -(3*a) ≤ z.val.2 ∧ z.val.2 ≤ 3*a} ∧
      IsCompact K ∧ IsConnected K ∧ N.center ∈ K ∧
      range (N.monoDelta hδ hδ1).chart ⊆ interior K ∧
      IsCompact (riemannianClosedBallOf g N.center (2 * a / Real.sqrt N.scale)) ∧
      riemannianClosedBallOf g N.center (2 * a / Real.sqrt N.scale) ⊆ interior K ∧
      K ⊆ riemannianBallOf g N.center (4 * a / Real.sqrt N.scale) ∧
      ∀ x ∈ K, N.scale / 2 ≤ metricScalarAt g x ∧ metricScalarAt g x ≤ 2 * N.scale := by
  have hepspos : 0 < eps := N.delta_pos.trans_le hprecision
  have hinv : eps⁻¹ ≤ δ₀⁻¹ := inv_anti₀ N.delta_pos hprecision
  have ha0 : 0 < a := by linarith
  have hsmall' : eps < 1 / 11 := hsmall.trans_lt (by norm_num)
  obtain ⟨nk,hmark,hmap⟩ := N.exists_spatialNeck hprecision hsmall' hk
  have hQ : 0 < metricScalarAt g N.center := N.scale_scalar ▸ N.scale_pos
  have h3 : 3 * a < eps⁻¹ := by linarith
  have hslab : (univ ×ˢ Icc (-(3*a)) (3*a) : Set NeckCylinder) ⊆
      univ ×ˢ Ioo (-eps⁻¹) eps⁻¹ := by
    intro z hz
    exact ⟨hz.1,(neg_lt_neg h3).trans_le hz.2.1,hz.2.2.trans_lt h3⟩
  let K := nk.map '' (univ ×ˢ Icc (-(3*a)) (3*a))
  have hK : IsCompact K := (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
    (nk.map.contMDiffOn_toFun.continuousOn.mono (hslab.trans nk.domain))
  let : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) (by norm_num : (0 : ℝ) ≤ 1))
  have hconn : IsConnected K := (isConnected_univ.prod (isConnected_Icc (by linarith : -(3*a) ≤ 3*a))).image nk.map
    (nk.map.contMDiffOn_toFun.continuousOn.mono (hslab.trans nk.domain))
  have hp : N.center ∈ K := ⟨(nk.center,0),⟨mem_univ _,by constructor <;> linarith⟩,nk.center_eq⟩
  have hopen : IsOpen (nk.map '' (univ ×ˢ Ioo (-(3*a)) (3*a))) :=
    nk.map.toOpenPartialHomeomorph.isOpen_image_of_subset_source (isOpen_univ.prod isOpen_Ioo)
      (fun z hz => nk.domain (hslab ⟨hz.1,hz.2.1.le,hz.2.2.le⟩))
  have hinter : nk.map '' (univ ×ˢ Ioo (-(3*a)) (3*a)) ⊆ interior K :=
    hopen.subset_interior_iff.mpr (image_mono (prod_mono subset_rfl Ioo_subset_Icc_self))
  have hchart : range (N.monoDelta hδ hδ1).chart ⊆ interior K := by
    rintro x ⟨q,rfl⟩
    apply hinter
    refine ⟨q.val,⟨mem_univ _,?_,?_⟩,?_⟩
    · linarith [q.property.1]
    · linarith [q.property.2]
    · exact hmap (TopologicalSpace.Opens.inclusion (neckBuffer_le_of_le N.delta_pos hδ) q)
  have hball : riemannianClosedBallOf g N.center (2*a/Real.sqrt N.scale) ⊆ interior K := by
    have hcap := nk.ball_subset_image_slab (by linarith : 0 < 5*a/2)
      (by linarith : 5*a/2 < eps⁻¹)
    have hsqrt : 4/5 < Real.sqrt (1-eps) := by
      have hs := Real.sq_sqrt (by linarith : 0 ≤ 1-eps)
      nlinarith [Real.sqrt_nonneg (1-eps)]
    have hr : 2*a/Real.sqrt N.scale <
        (5*a/2)*Real.sqrt (1-eps)/Real.sqrt (metricScalarAt g N.center) := by
      rw [← N.scale_scalar]
      apply div_lt_div_of_pos_right _ (Real.sqrt_pos.mpr N.scale_pos)
      nlinarith
    intro x hx
    have hxopen : x ∈ riemannianBallOf g N.center
        ((5*a/2)*Real.sqrt (1-eps)/Real.sqrt (metricScalarAt g N.center)) := by
      exact hx.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hr)
    obtain ⟨z,hz,rfl⟩ := hcap hxopen
    apply hinter
    exact ⟨z,⟨hz.1,by linarith [hz.2.1],by linarith [hz.2.2]⟩,rfl⟩
  have hcball : IsCompact (riemannianClosedBallOf g N.center (2*a/Real.sqrt N.scale)) :=
    hK.of_isClosed_subset
      (isClosed_le (continuous_riemannianEDist g N.center) continuous_const)
      (hball.trans interior_subset)
  have houter : K ⊆ riemannianBallOf g N.center (4*a/Real.sqrt N.scale) := by
    have hdist := nk.image_slab_subset_closedBall (by linarith : 0 ≤ 3*a) h3
    have hsqrt : Real.sqrt (1+eps) < 11/10 := by
      have hs := Real.sq_sqrt (by linarith [hepspos] : 0 ≤ 1+eps)
      nlinarith [Real.sqrt_nonneg (1+eps)]
    have hr : (3*a+6)*Real.sqrt (1+eps)/Real.sqrt (metricScalarAt g N.center) <
        4*a/Real.sqrt N.scale := by
      rw [← N.scale_scalar]
      apply div_lt_div_of_pos_right _ (Real.sqrt_pos.mpr N.scale_pos)
      nlinarith
    intro x hx
    exact (hdist hx).trans_lt ((ENNReal.ofReal_lt_ofReal_iff
      (div_pos (by positivity) (Real.sqrt_pos.mpr N.scale_pos))).mpr hr)
  have hKexact : K = N.chart '' {z : neckBuffer δ₀ | -(3*a) ≤ z.val.2 ∧ z.val.2 ≤ 3*a} := by
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩
      have hzbuf : z ∈ neckBuffer δ₀ := by
        constructor <;> linarith [hz.2.1,hz.2.2]
      exact ⟨⟨z,hzbuf⟩,hz.2,(hmap ⟨z,hzbuf⟩).symm⟩
    · rintro ⟨z,hz,rfl⟩
      exact ⟨z.val,⟨mem_univ _,hz⟩,hmap z⟩
  refine ⟨K,hKexact,hK,hconn,hp,hchart,hcball,hball,houter,?_⟩
  intro x hx
  have hs := nk.scalar_bounds_on_image_window (image_mono hslab hx)
  rw [← N.scale_scalar] at hs
  constructor <;> nlinarith [N.scale_pos]


theorem NormalizedNeck.exists_buffered_long_neck_region
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric ThreeModel M} {δ₀ δ eps : ℝ} {k : ℕ}
    (N : NormalizedNeck g δ₀ k) (hδ : δ₀ ≤ δ) (hδ1 : δ < 1)
    (hprecision : δ₀ ≤ eps) (hsmall : eps ≤ 1 / 8646) (hk : ⌈eps⁻¹⌉₊ ≤ k)
    (a : ℝ) (ha : 24 < a) (hpublic : δ⁻¹ + 1 ≤ a) (hfit : 4 * a < eps⁻¹) :
    ∃ U K : Set M,
      U = N.chart '' {z : neckBuffer δ₀ | -a ≤ z.val.2 ∧ z.val.2 ≤ a} ∧
      K = N.chart '' {z : neckBuffer δ₀ | -(3*a) ≤ z.val.2 ∧ z.val.2 ≤ 3*a} ∧
      IsCompact U ∧ IsConnected U ∧ IsCompact K ∧ IsConnected K ∧ U ⊆ interior K ∧
      N.center ∈ U ∧ range (N.monoDelta hδ hδ1).chart ⊆ interior U ∧
      riemannianClosedBallOf g N.center ((4*a/5) / Real.sqrt N.scale) ⊆ interior U ∧
      U ⊆ riemannianBallOf g N.center ((7*a/5) / Real.sqrt N.scale) ∧
      IsCompact (riemannianClosedBallOf g N.center (2*a/Real.sqrt N.scale)) ∧
      riemannianClosedBallOf g N.center (2*a/Real.sqrt N.scale) ⊆ interior K ∧
      K ⊆ riemannianBallOf g N.center (4*a/Real.sqrt N.scale) ∧
      ∀ x ∈ K, N.scale/2 ≤ metricScalarAt g x ∧ metricScalarAt g x ≤ 2*N.scale := by
  obtain ⟨K,hKexact,hK,hKconn,_,hchart,hcball,hball,houter,hscalar⟩ :=
    N.exists_compact_long_neck_footprint hδ hδ1 hprecision hsmall hk a ha hpublic hfit
  obtain ⟨nk,_,hmap⟩ := N.exists_spatialNeck hprecision (hsmall.trans_lt (by norm_num)) hk
  have hepspos : 0 < eps := N.delta_pos.trans_le hprecision
  have hinv : eps⁻¹ ≤ δ₀⁻¹ := inv_anti₀ N.delta_pos hprecision
  have ha0 : 0 < a := by linarith
  have haδ : a < eps⁻¹ := by linarith
  have hslab : (univ ×ˢ Icc (-a) a : Set NeckCylinder) ⊆ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹ := by
    intro z hz
    exact ⟨hz.1,(neg_lt_neg haδ).trans_le hz.2.1,hz.2.2.trans_lt haδ⟩
  let U := nk.map '' (univ ×ˢ Icc (-a) a)
  have hU : IsCompact U := (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
    (nk.map.contMDiffOn_toFun.continuousOn.mono (hslab.trans nk.domain))
  let : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) (by norm_num : (0 : ℝ) ≤ 1))
  have hUconn : IsConnected U := (isConnected_univ.prod (isConnected_Icc (by linarith : -a ≤ a))).image nk.map
    (nk.map.contMDiffOn_toFun.continuousOn.mono (hslab.trans nk.domain))
  have hUexact : U = N.chart '' {z : neckBuffer δ₀ | -a ≤ z.val.2 ∧ z.val.2 ≤ a} := by
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩
      have hzbuf : z ∈ neckBuffer δ₀ := by constructor <;> linarith [hz.2.1,hz.2.2]
      exact ⟨⟨z,hzbuf⟩,hz.2,(hmap ⟨z,hzbuf⟩).symm⟩
    · rintro ⟨z,hz,rfl⟩
      exact ⟨z.val,⟨mem_univ _,hz⟩,hmap z⟩
  have hinter : nk.map '' (univ ×ˢ Ioo (-a) a) ⊆ interior U := by
    have hopen := nk.map.toOpenPartialHomeomorph.isOpen_image_of_subset_source (isOpen_univ.prod isOpen_Ioo)
      (fun z hz => nk.domain (hslab ⟨hz.1,hz.2.1.le,hz.2.2.le⟩))
    exact hopen.subset_interior_iff.mpr (image_mono (prod_mono subset_rfl Ioo_subset_Icc_self))
  have hchartU : range (N.monoDelta hδ hδ1).chart ⊆ interior U := by
    rintro x ⟨q,rfl⟩
    apply hinter
    refine ⟨q.val,⟨mem_univ _,?_,?_⟩,?_⟩
    · linarith [q.property.1]
    · linarith [q.property.2]
    · exact hmap (TopologicalSpace.Opens.inclusion (neckBuffer_le_of_le N.delta_pos hδ) q)
  have hUK : U ⊆ interior K := by
    let V := nk.map '' (univ ×ˢ Ioo (-(3*a)) (3*a))
    have hVopen : IsOpen V := nk.map.toOpenPartialHomeomorph.isOpen_image_of_subset_source
      (isOpen_univ.prod isOpen_Ioo) (fun z hz => nk.domain ⟨hz.1,
        by linarith [hz.2.1],by linarith [hz.2.2]⟩)
    have hVK : V ⊆ K := by
      rw [hKexact]
      rintro x ⟨z,hz,rfl⟩
      have hzbuf : z ∈ neckBuffer δ₀ := by constructor <;> linarith [hz.2.1,hz.2.2]
      exact ⟨⟨z,hzbuf⟩,⟨hz.2.1.le,hz.2.2.le⟩,(hmap ⟨z,hzbuf⟩).symm⟩
    apply (image_mono ?_).trans (hVopen.subset_interior_iff.mpr hVK)
    intro z hz
    exact ⟨hz.1,by linarith [hz.2.1],by linarith [hz.2.2]⟩
  have hinner : riemannianClosedBallOf g N.center ((4*a/5)/Real.sqrt N.scale) ⊆ interior U := by
    have hcap := nk.ball_subset_image_slab (by linarith : 0 < 9*a/10) (by linarith : 9*a/10 < eps⁻¹)
    have hsqrt : 9/10 < Real.sqrt (1-eps) := by
      have hs := Real.sq_sqrt (by linarith : 0 ≤ 1-eps)
      nlinarith [Real.sqrt_nonneg (1-eps)]
    have hr : (4*a/5)/Real.sqrt N.scale < (9*a/10)*Real.sqrt (1-eps)/Real.sqrt (metricScalarAt g N.center) := by
      rw [← N.scale_scalar]
      apply div_lt_div_of_pos_right _ (Real.sqrt_pos.mpr N.scale_pos)
      nlinarith
    intro x hx
    obtain ⟨z,hz,rfl⟩ := hcap (hx.trans_lt ((ENNReal.ofReal_lt_ofReal_iff
      (div_pos (mul_pos (by linarith) (Real.sqrt_pos.mpr (by linarith)))
        (Real.sqrt_pos.mpr nk.Q_pos))).mpr hr))
    exact hinter ⟨z,⟨hz.1,by linarith [hz.2.1],by linarith [hz.2.2]⟩,rfl⟩
  have hUouter : U ⊆ riemannianBallOf g N.center ((7*a/5)/Real.sqrt N.scale) := by
    have hsqrt : Real.sqrt (1+eps) < 11/10 := by
      have hs := Real.sq_sqrt (by linarith [hepspos] : 0 ≤ 1+eps)
      nlinarith [Real.sqrt_nonneg (1+eps)]
    have hr : (a+6)*Real.sqrt (1+eps)/Real.sqrt (metricScalarAt g N.center) < (7*a/5)/Real.sqrt N.scale := by
      rw [← N.scale_scalar]
      apply div_lt_div_of_pos_right _ (Real.sqrt_pos.mpr N.scale_pos)
      nlinarith
    intro x hx
    exact (nk.image_slab_subset_closedBall ha0.le haδ hx).trans_lt
      ((ENNReal.ofReal_lt_ofReal_iff (div_pos (by positivity) (Real.sqrt_pos.mpr N.scale_pos))).mpr hr)
  refine ⟨U,K,hUexact,hKexact,hU,hUconn,hK,hKconn,hUK,?_,hchartU,hinner,hUouter,hcball,hball,houter,hscalar⟩
  exact ⟨(nk.center,0),⟨mem_univ _,by constructor <;> linarith⟩,nk.center_eq⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric ThreeModel M} {δ : ℝ} {k : ℕ}

private theorem interior_neckClosedSlab (δ R : ℝ) :
    interior {z : neckBuffer δ | -R ≤ z.val.2 ∧ z.val.2 ≤ R} =
      {z : neckBuffer δ | -R < z.val.2 ∧ z.val.2 < R} := by
  have hh := (neckBuffer δ).isOpen.isOpenEmbedding_subtypeVal.isOpenMap.preimage_interior_eq_interior_preimage (continuous_subtype_val : Continuous
      (Subtype.val : neckBuffer δ → NeckCylinder)) (univ ×ˢ Icc (-R) R)
  rw [interior_prod_eq, interior_univ, interior_Icc] at hh
  have hleft : (Subtype.val : neckBuffer δ → NeckCylinder) ⁻¹' (univ ×ˢ Icc (-R) R) =
      {z : neckBuffer δ | -R ≤ z.val.2 ∧ z.val.2 ≤ R} := by
    ext z
    simp only [mem_preimage, mem_prod, mem_univ, true_and, mem_Icc, mem_ofPred_eq]
  have hright : (Subtype.val : neckBuffer δ → NeckCylinder) ⁻¹' (univ ×ˢ Ioo (-R) R) =
      {z : neckBuffer δ | -R < z.val.2 ∧ z.val.2 < R} := by
    ext z
    simp only [mem_preimage, mem_prod, mem_univ, true_and, mem_Ioo, mem_ofPred_eq]
  exact hleft ▸ hright ▸ hh.symm

omit [T2Space M] in
theorem NormalizedNeck.interior_image_closedSlab (N : NormalizedNeck g δ k) (R : ℝ) :
    interior (N.chart '' {z : neckBuffer δ | -R ≤ z.val.2 ∧ z.val.2 ≤ R}) =
      N.chart '' {z : neckBuffer δ | -R < z.val.2 ∧ z.val.2 < R} := by
  have hopen : IsOpen (range N.chart) :=
    Manifold.isOpen_range_of_isSmoothEmbedding (by simp [ThreeSpace, Module.finrank_prod])
      N.chart_smooth
  have he : _root_.Topology.IsOpenEmbedding N.chart := ⟨N.chart_smooth.isEmbedding, hopen⟩
  have hh := he.isOpenMap.preimage_interior_eq_interior_preimage N.chart.continuous
    (N.chart '' {z : neckBuffer δ | -R ≤ z.val.2 ∧ z.val.2 ≤ R})
  rw [Set.preimage_image_eq _ N.chart_smooth.isEmbedding.injective,
    interior_neckClosedSlab δ R] at hh
  rw [← hh, image_preimage_eq_of_subset]
  exact (interior_subset.trans (image_subset_range _ _))

omit [T2Space M] in
theorem NormalizedNeck.isConnected_interior_image_closedSlab
    (N : NormalizedNeck g δ k) {R : ℝ} (hR : 0 < R) (hfit : R < δ⁻¹ + 1) :
    IsConnected (interior (N.chart '' {z : neckBuffer δ | -R ≤ z.val.2 ∧ z.val.2 ≤ R})) := by
  let _ : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) (by norm_num : (0 : ℝ) ≤ 1))
  have hslab : IsConnected (univ ×ˢ Ioo (-R) R : Set NeckCylinder) :=
    isConnected_univ.prod (isConnected_Ioo (by linarith))
  have hsub : (univ ×ˢ Ioo (-R) R : Set NeckCylinder) ⊆
      range (Subtype.val : neckBuffer δ → NeckCylinder) := by
    intro z hz
    refine ⟨⟨z, ?_⟩, rfl⟩
    constructor <;> linarith [hz.2.1, hz.2.2]
  have hc := hslab.preimage_of_isOpenMap Subtype.val_injective
    (neckBuffer δ).isOpen.isOpenMap_subtype_val hsub
  rw [N.interior_image_closedSlab R]
  have hset : (Subtype.val : neckBuffer δ → NeckCylinder) ⁻¹' (univ ×ˢ Ioo (-R) R) =
      {z : neckBuffer δ | -R < z.val.2 ∧ z.val.2 < R} := by
    ext z
    simp only [mem_preimage, mem_prod, mem_univ, true_and, mem_Ioo, mem_ofPred_eq]
  exact hset ▸ hc.image N.chart N.chart.continuous.continuousOn

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
