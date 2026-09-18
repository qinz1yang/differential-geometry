import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CylinderReferenceModel
import DifferentialGeometry.Geometry.Metric.DistancePullback
import DifferentialGeometry.Geometry.Metric.Distance.Topology
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens
import Mathlib.Topology.MetricSpace.Bounded

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem exists_uniform_neck_image_radius {beta alpha : ℝ}
    (hbeta : 0 < beta) (hba : beta < alpha) :
    ∃ R : ℝ, 0 < R ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
        (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D)
        (x : M) (t : ℝ) (nk : StrongNeck S beta x t),
        ∀ y ∈ univ ×ˢ Ioo (-alpha⁻¹) alpha⁻¹,
          riemannianEDistOf (I := I3)
            (rescaledMetric S t (S.scalar t x) nk.Q_pos 0) x (nk.map y) ≤ ENNReal.ofReal R := by
  let U : TopologicalSpace.Opens Cylinder :=
    ⟨univ ×ˢ Ioo (-beta⁻¹) beta⁻¹, isOpen_univ.prod isOpen_Ioo⟩
  let K : Set Cylinder := univ ×ˢ Icc (-alpha⁻¹) alpha⁻¹
  have halpha : 0 < alpha := hbeta.trans hba
  have hrad : alpha⁻¹ < beta⁻¹ := inv_strictAnti₀ hbeta hba
  have hKU : K ⊆ (U : Set Cylinder) := by
    intro y hy
    exact ⟨hy.1, (neg_lt_neg hrad).trans_le hy.2.1, hy.2.2.trans_lt hrad⟩
  let : PreconnectedSpace (Sphere 2) := Subtype.preconnectedSpace
    (isPreconnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace])) (0 : ThreeSpace) 1)
  have hpre : IsPreconnected (U : Set Cylinder) := isPreconnected_univ.prod isPreconnected_Ioo
  let : PreconnectedSpace U := Subtype.preconnectedSpace hpre
  let g := (cylinderReferenceMetric 0).restrictOpen U
  let : PseudoMetricSpace U := g.toPseudoMetricSpace
  have hK : IsCompact (Subtype.val ⁻¹' K : Set U) := by
    apply Topology.IsInducing.subtypeVal.isCompact_preimage' (isCompact_univ.prod isCompact_Icc)
    intro y hy
    exact ⟨⟨y, hKU hy⟩, rfl⟩
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp hK.isBounded
  let B : ℝ := max C 0 + 1
  have hB : 0 < B := by dsimp only [B]; linarith [le_max_right C 0]
  have hCB : C ≤ B := by dsimp only [B]; linarith [le_max_left C 0]
  have hc : 0 < 1 + beta := by linarith
  refine ⟨Real.sqrt (1 + beta) * B, mul_pos (Real.sqrt_pos.mpr hc) hB, ?_⟩
  intro M _ _ _ D S x t nk y hy
  have hU : (U : Set Cylinder) ⊆ nk.map.source := nk.domain
  let f : U → M := fun z => nk.map (z : Cylinder)
  have hf : IsLocalDiffeomorph IC I3 ∞ f :=
    DifferentialGeometry.isLocalDiffeomorph_restrict_open U
      (fun z => ⟨nk.map, hU z.property, fun _ _ => rfl⟩)
  have hdf (z : U) (v : TangentSpace IC z) :
      mfderiv IC I3 f z v = mfderiv IC I3 nk.map (z : Cylinder) v := by
    have hmap : MDifferentiableAt IC I3 nk.map (z : Cylinder) :=
      (nk.map.contMDiffOn_toFun.contMDiffAt (nk.map.open_source.mem_nhds (hU z.property))).mdifferentiableAt
        (by simp)
    have hh := mfderiv_comp_apply z hmap (hasMFDerivAt_subtype_val (I := IC) U z).mdifferentiableAt v
    rw [mfderiv_subtype_val_apply] at hh
    exact hh
  have hquad (z : U) (v : TangentSpace IC z) :
      (rescaledMetric S t (S.scalar t x) nk.Q_pos 0).inner (f z)
        (mfderiv IC I3 f z v) (mfderiv IC I3 f z v) ≤ (1 + beta) * g.inner z v v := by
    have hh := (nk.comparison.equivalence 0 (by norm_num) (z : Cylinder) z.property v).2
    rw [nk.comparison.pullback_eq 0 (z : Cylinder) z.property (fun _ => v)] at hh
    rw [hdf z v]
    change _ ≤ (1 + beta) * (cylinderReferenceMetric 0).inner (z : Cylinder) v v
    have heq : (nk.cylinder.metric 0).inner (z : Cylinder) v v =
        (cylinderReferenceMetric 0).inner (z : Cylinder) v v :=
      (nk.cylinder.inner_eq 0 le_rfl _ v v).trans
        (cylinderReferenceMetric_inner 0 le_rfl _ v v).symm
    exact hh.trans_eq (congrArg (fun a => (1 + beta) * a) heq)
  have hpK : (nk.center, (0 : ℝ)) ∈ K :=
    ⟨mem_univ _, neg_nonpos.mpr (inv_nonneg.mpr halpha.le), inv_nonneg.mpr halpha.le⟩
  have hyK : y ∈ K := ⟨hy.1, hy.2.1.le, hy.2.2.le⟩
  let p : U := ⟨(nk.center, 0), hKU hpK⟩
  let q : U := ⟨y, hKU hyK⟩
  have href : riemannianEDistOf (I := IC) g p q ≤ ENNReal.ofReal B := by
    rw [← SmoothRiemannianMetric.toPseudoMetricSpace_edist g]
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal ((hC (show p ∈ Subtype.val ⁻¹' K from hpK) (show q ∈ Subtype.val ⁻¹' K from hyK)).trans hCB)
  have hh := edistOf_le_of_quad_of_localDiffeomorph g
    (rescaledMetric S t (S.scalar t x) nk.Q_pos 0) f hf hc hquad p q
  change riemannianEDistOf (rescaledMetric S t (S.scalar t x) nk.Q_pos 0)
    (nk.map (nk.center, 0)) (nk.map y) ≤ _ at hh
  rw [nk.center_eq] at hh
  apply hh.trans
  rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_left href bot_le

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
