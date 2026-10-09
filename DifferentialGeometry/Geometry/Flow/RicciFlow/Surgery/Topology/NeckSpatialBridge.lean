import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckCylindricalChartBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.StaticComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CylinderReferenceModel
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonComposition
import DifferentialGeometry.Topology.Manifold.OpenSubtypeDiffeomorph
import DifferentialGeometry.Geometry.Neck.CompactSide

set_option autoImplicit false
noncomputable section
open Set Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

private theorem NormalizedNeck.exists_partialDiffeomorph
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] {g : SmoothRiemannianMetric ThreeModel M}
    {δ : ℝ} {k : ℕ} (N : NormalizedNeck g δ k) :
    ∃ F : PartialDiffeomorph NeckCylinderModel ThreeModel NeckCylinder M ∞,
      F.source = neckBuffer δ ∧ F.target = range N.chart ∧
        ∀ z : neckBuffer δ, F z.val = N.chart z := by
  let U := neckBuffer δ
  have hUne : Nonempty U := ⟨⟨(N.sphereMark,0),by
    have hp := inv_pos.mpr N.delta_pos
    constructor <;> linarith⟩⟩
  obtain ⟨V,C,hV,hC,_⟩ := N.exists_cylindricalChart
  let hVne : Nonempty V := ⟨C (Classical.choice hUne)⟩
  let iU := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph NeckCylinderModel U hUne
  let iV := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph ThreeModel V hVne
  let F := (iU.symm.trans C.toPartialDiffeomorph).trans iV
  refine ⟨F,?_,?_,?_⟩
  · ext x
    change ((x ∈ iU.target ∧ iU.symm x ∈ (univ : Set U)) ∧
      C (iU.symm x) ∈ (univ : Set V)) ↔ x ∈ U
    simp only [mem_univ,and_true,iU,DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target]
    rfl
  · rw [← hV]
    ext y
    change (y ∈ iV.target ∧ (iV.symm y ∈ (univ : Set V) ∧
      C.symm (iV.symm y) ∈ (univ : Set U))) ↔ y ∈ V
    simp only [mem_univ,and_self,and_true,iV,
      DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target]
    rfl
  · intro z
    change (C (iU.symm z.val) : M) = N.chart z
    rw [show iU.symm z.val = z from
      DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_symm_apply
        NeckCylinderModel U hUne z.property]
    exact hC z

set_option backward.isDefEq.respectTransparency false in
theorem NormalizedNeck.exists_spatialNeck
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M]
    {g : SmoothRiemannianMetric ThreeModel M} {δ eps : ℝ} {k : ℕ}
    (N : NormalizedNeck g δ k) (heps : δ ≤ eps) (hsmall : eps < 1 / 11)
    (hk : ⌈eps⁻¹⌉₊ ≤ k) :
    ∃ nk : SpatialNeck g eps N.center, nk.center = N.sphereMark ∧
      ∀ z : neckBuffer δ, nk.map z.val = N.chart z := by
  obtain ⟨F,hsource,htarget,hF⟩ := N.exists_partialDiffeomorph
  have hepspos : 0 < eps := N.delta_pos.trans_le heps
  let K : Set NeckCylinder := univ ×ˢ Icc (-eps⁻¹) eps⁻¹
  have hK : IsCompact K := isCompact_univ.prod isCompact_Icc
  have hKU : K ⊆ neckBuffer δ := by
    intro z hz
    have hrad := inv_anti₀ N.delta_pos heps
    change -δ⁻¹-1 < z.2 ∧ z.2 < δ⁻¹+1
    constructor <;> linarith [hz.2.1,hz.2.2]
  have hKd (z : neckBuffer δ) (hz : z.val ∈ K) : z ∈ neckClosedTest δ := by
    have hrad := inv_anti₀ N.delta_pos heps
    change -δ⁻¹ ≤ z.val.2 ∧ z.val.2 ≤ δ⁻¹
    constructor <;> linarith [hz.2.1,hz.2.2]
  have hder (z : neckBuffer δ) (v : TangentSpace NeckCylinderModel z) :
      mfderiv NeckCylinderModel ThreeModel F z.val v =
        mfderiv NeckCylinderModel ThreeModel N.chart z v := by
    have hmap : (fun z : neckBuffer δ => F z.val) = N.chart := funext hF
    have hchain := mfderiv_comp_apply z (F.mdifferentiableAt (by simp) (hsource.symm ▸ z.property))
      (hasMFDerivAt_subtype_val (I := NeckCylinderModel) (neckBuffer δ) z).mdifferentiableAt v
    rw [mfderiv_subtype_val_apply] at hchain
    change mfderiv NeckCylinderModel ThreeModel (fun z : neckBuffer δ => F z.val) z v = _ at hchain
    rw [hmap] at hchain
    exact hchain.symm
  have hlocal (z : neckBuffer δ) (v w : TangentSpace NeckCylinderModel z) :
      N.normalizedMetric.inner z v w =
        (scaleMetric (metricScalarAt g N.center) (N.scale_scalar ▸ N.scale_pos) g).inner (F z.val)
          (mfderiv NeckCylinderModel ThreeModel F z.val v)
          (mfderiv NeckCylinderModel ThreeModel F z.val w) := by
    rw [scaleMetric_inner]
    change N.normalizedMetric.inner z v w = metricScalarAt g N.center *
      (g.inner (F z.val)) (show ThreeSpace from mfderiv NeckCylinderModel ThreeModel F z.val v)
        (show ThreeSpace from mfderiv NeckCylinderModel ThreeModel F z.val w)
    rw [hder z v,hder z w,hF z,← N.scale_scalar]
    exact N.normalized_inner z v w
  have hreference : (cylinderReferenceMetric 0).restrictOpen (neckBuffer δ) =
      roundCylinderMetric.restrictOpen (neckBuffer δ) := by
    apply SmoothRiemannianMetric.ext_inner
    intro z v w
    change (cylinderReferenceMetric 0).inner z.val v w = roundCylinderMetric.inner z.val v w
    rw [roundCylinderMetric_eq_geometry,
      DifferentialGeometry.Geometry.Metric.roundCylinderMetric_inner]
    have hh := cylinderReferenceMetric_inner 0 le_rfl z.val v w
    apply hh.trans
    simp only [sub_zero,mul_one]
    rfl
  have hb (z : neckBuffer δ) (hz : z.val ∈ K) (a : ℕ) (ha : a ≤ ⌈eps⁻¹⌉₊) :
      metricDerivNorm a N.normalizedMetric
        ((cylinderReferenceMetric 0).restrictOpen (neckBuffer δ))
        ((cylinderReferenceMetric 0).restrictOpen (neckBuffer δ)) z ≤ eps := by
    rw [hreference]
    exact (metricDerivNorm_lt_of_sup_lt (isCompact_neckClosedTest δ) (ha.trans hk)
      N.normalizedMetric _ _ N.closeness (hKd z hz)).le.trans heps
  obtain ⟨cmp⟩ := exists_static_metricComparisonOn_of_local_metric
    (cylinderReferenceMetric 0)
    (scaleMetric (metricScalarAt g N.center) (N.scale_scalar ▸ N.scale_pos) g)
    F (neckBuffer δ) N.normalizedMetric hlocal K hK hKU ⌈eps⁻¹⌉₊ hepspos.le hb {0}
  have hUK : (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹ : Set NeckCylinder) ⊆ K :=
    fun _ hz => ⟨hz.1,hz.2.1.le,hz.2.2.le⟩
  refine ⟨{ eps_pos := hepspos
            eps_small := hsmall
            Q_pos := N.scale_scalar ▸ N.scale_pos
            cylinder := cylinderReference
            map := F
            center := N.sphereMark
            center_eq := ?_
            domain := fun z hz => hsource.symm ▸ hKU (hUK hz)
            comparison := cmp.mono hUK le_rfl le_rfl },rfl,hF⟩
  have hm : (N.sphereMark,(0:ℝ)) ∈ neckBuffer δ := by
    have hp := inv_pos.mpr N.delta_pos
    constructor <;> linarith
  exact (hF ⟨(N.sphereMark,0),hm⟩).trans N.marked

private theorem compactSide_cast
    {X : Type*} [TopologicalSpace X] {S T : Set X} (h : S = T)
    (d : DifferentialGeometry.Topology.SphereSeparation.SphereSides S) :
    (h ▸ d).compactSide = d.compactSide := by
  cases h
  rfl

theorem exists_normalized_neck_compact_side_exclusion_tolerance :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ eps : ℝ, eps ≤ eta →
        ∀ (M : Type*) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold ThreeModel ∞ M] [T2Space M]
          (g : SmoothRiemannianMetric ThreeModel M) (δ : ℝ) (k : ℕ)
          (N : NormalizedNeck g δ k), δ ≤ eps → ⌈eps⁻¹⌉₊ ≤ k →
          ∀ d : DifferentialGeometry.Topology.SphereSeparation.SphereSides
            (range (fun q : Sphere 2 => N.chart ⟨(q, 0), by
              have hp := inv_pos.mpr N.delta_pos
              constructor <;> linarith⟩)),
            ¬ ∀ x ∈ d.compactSide,
              ∃ (δ' : ℝ) (k' : ℕ) (N' : NormalizedNeck g δ' k'),
                N'.center = x ∧ δ' ≤ eps ∧ ⌈eps⁻¹⌉₊ ≤ k' := by
  obtain ⟨eta, heta, hexclude⟩ := exists_spatial_neck_compact_side_exclusion_tolerance
  refine ⟨min eta (1 / 12), lt_min heta (by norm_num), ?_⟩
  intro eps heps M _ _ _ _ g δ k N hδ hk d hall
  have hsmall : eps < 1 / 11 := lt_of_le_of_lt (heps.trans (min_le_right _ _)) (by norm_num)
  obtain ⟨nk, _, hmap⟩ := N.exists_spatialNeck hδ hsmall hk
  have hsphere : range (fun q : Sphere 2 => nk.map (q, 0)) =
      range (fun q : Sphere 2 => N.chart ⟨(q, 0), by
        have hp := inv_pos.mpr N.delta_pos
        constructor <;> linarith⟩) := by
    congr 1
    funext q
    exact hmap ⟨(q, 0), by
      have hp := inv_pos.mpr N.delta_pos
      constructor <;> linarith⟩
  let d' : DifferentialGeometry.Topology.SphereSeparation.SphereSides
      (range (fun q : Sphere 2 => nk.map (q, 0))) := hsphere.symm ▸ d
  have hd : d'.compactSide = d.compactSide := by
    exact compactSide_cast hsphere.symm d
  apply hexclude eps (heps.trans (min_le_left _ _)) M g N.center nk d'
  intro x hx
  obtain ⟨δ', k', N', hc, hδ', hk'⟩ := hall x (hd ▸ hx)
  obtain ⟨nk', _, _⟩ := N'.exists_spatialNeck hδ' hsmall hk'
  exact hc ▸ ⟨nk'⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
