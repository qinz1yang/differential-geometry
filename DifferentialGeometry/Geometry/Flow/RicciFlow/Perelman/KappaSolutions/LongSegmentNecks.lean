import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedLineNeck
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.StrongNeckDetection
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.StrongNeckModel
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.KLimThreeDimensionalBounded
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.StandardHarnackLimit
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Line

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open CanonicalNeighborhood CanonicalNeighborhood.FiniteHorn
open scoped _root_.Manifold ContDiff _root_.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem exists_strongNeck_radius_near_almost_isometric_segment (kappa B : ℝ)
    (hB : 0 ≤ B)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hsmall : epsilon < 1 / 11) :
    ∃ A delta : ℝ, 0 < A ∧ 0 < delta ∧ delta < 1 ∧
      ∀ F : PointedFlowData.{u, 0, 0} (I := ThreeModel) ancientTimeInterval,
        IsAncientKappaSolution kappa F → PointedFlowScalarAtBase F 1 →
        Nonempty (TangentOrientationSection F.M) →
        ∀ γ : ℝ → F.M,
          riemannianEDistOf (F.S.family.metric 0) F.basepoint (γ 0) ≤ ENNReal.ofReal B →
          (∀ s ∈ Icc (-A) A, ∀ t ∈ Icc (-A) A,
            ENNReal.ofReal ((1 - delta) * |s - t|) ≤
              riemannianEDistOf (F.S.family.metric 0) (γ s) (γ t) ∧
            riemannianEDistOf (F.S.family.metric 0) (γ s) (γ t) ≤
              ENNReal.ofReal ((1 + delta) * |s - t|)) →
          Nonempty (StrongNeck F.S epsilon F.basepoint 0) := by
  classical
  by_contra hnot
  push Not at hnot
  have hcounter (i : ℕ) := hnot ((i : ℝ) + 1) (1 / ((i : ℝ) + 2))
    (by positivity) (by positivity) (by
      apply (div_lt_one (by positivity : (0 : ℝ) < (i : ℝ) + 2)).mpr
      linarith [Nat.cast_nonneg (α := ℝ) i])
  choose F hF hbase horient γ hcenter hsegment hnone using hcounter
  let X : PointedFlowSeq.{u, 0, 0} (I := ThreeModel) :=
    { D := ancientTimeInterval, term := F }
  obtain ⟨L, phi, hphi, Phi, hKL, hbaseL, hconv, hcmp, hL⟩ :=
    exists_fixed_kappa_compactness X rfl
      (fun i => ancientKappaThree_toKLim (F i) (hF i) (by simp [ThreeSpace])) hbase
  obtain ⟨C, hcanonical⟩ := hconv 0 le_rfl
  have hreference (k : ℕ) : (C.domain k).referenceMetric = (C.domain k).limitMetric := by
    rw [hcanonical]
    rfl
  have hr : Tendsto (fun k => (phi k : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1
      (tendsto_natCast_atTop_atTop.comp hphi.tendsto_atTop)
  have hdelta : Tendsto (fun k => 1 / ((phi k : ℝ) + 2)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop (2 : ℝ)
        ((tendsto_natCast_atTop_atTop (R := ℝ)).comp hphi.tendsto_atTop))
  obtain ⟨gamma, _, hline⟩ :=
    exists_pointed_line_of_growing_almost_isometric_segments_with_bounded_centers C hreference
    (hL.complete 0 (by change (0 : ℝ) ≤ 0; exact le_rfl)) hL.connected (fun k => γ (phi k)) hB (fun k => hcenter (phi k))
    (fun k => (phi k : ℝ) + 1) hr (fun k => 1 / ((phi k : ℝ) + 2)) hdelta
    (fun k => hsegment (phi k))
  obtain ⟨yStar, e, hmarked, hmetric⟩ :=
    pointedAncientKappaLimit_normalized_cylinder_of_intrinsic_line
      (Phi.atTime (L := L) 0) C hcanonical
      (fun k => Classical.choice (horient k)) hbase hL le_rfl gamma hline
  have hnecks := pointedCylinderFlowLimit_eventually_strongNeckWitness Phi rfl hbase
    (hcmp (-1) 0 (by norm_num) le_rfl) yStar e hmarked hmetric epsilon hepsilon
    (by linarith)
  obtain ⟨k, W, _⟩ := hnecks.exists
  exact (hnone (phi k)).false (W.exists_strongNeck hsmall).choose

theorem exists_strongNeck_radius_of_almost_isometric_segment (kappa : ℝ)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hsmall : epsilon < 1 / 11) :
    ∃ A delta : ℝ, 0 < A ∧ 0 < delta ∧ delta < 1 ∧
      ∀ F : PointedFlowData.{u, 0, 0} (I := ThreeModel) ancientTimeInterval,
        IsAncientKappaSolution kappa F → PointedFlowScalarAtBase F 1 →
        Nonempty (TangentOrientationSection F.M) →
        ∀ γ : ℝ → F.M, γ 0 = F.basepoint →
          (∀ s ∈ Icc (-A) A, ∀ t ∈ Icc (-A) A,
            ENNReal.ofReal ((1 - delta) * |s - t|) ≤
              riemannianEDistOf (F.S.family.metric 0) (γ s) (γ t) ∧
            riemannianEDistOf (F.S.family.metric 0) (γ s) (γ t) ≤
              ENNReal.ofReal ((1 + delta) * |s - t|)) →
          Nonempty (StrongNeck F.S epsilon F.basepoint 0) := by
  obtain ⟨A, delta, hA, hdelta, hdelta_one, hneck⟩ :=
    exists_strongNeck_radius_near_almost_isometric_segment.{u}
      kappa 0 le_rfl hepsilon hsmall
  refine ⟨A, delta, hA, hdelta, hdelta_one, ?_⟩
  intro F hF hbase horient γ hcenter hsegment
  apply hneck F hF hbase horient γ _ hsegment
  rw [hcenter, riemannianEDistOf_self]
  exact bot_le


theorem exists_strongNeck_radius_of_minimizing_segment (kappa : ℝ)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hsmall : epsilon < 1 / 11) :
    ∃ A : ℝ, 0 < A ∧
      ∀ F : PointedFlowData.{u, 0, 0} (I := ThreeModel) ancientTimeInterval,
        IsAncientKappaSolution kappa F → PointedFlowScalarAtBase F 1 →
        Nonempty (TangentOrientationSection F.M) →
        ∀ γ : ℝ → F.M, γ 0 = F.basepoint →
          (∀ s ∈ Icc (-A) A, ∀ t ∈ Icc (-A) A,
            riemannianEDistOf (F.S.family.metric 0) (γ s) (γ t) = ENNReal.ofReal |s - t|) →
          Nonempty (StrongNeck F.S epsilon F.basepoint 0) := by
  obtain ⟨A, delta, hA, hdelta, _, hneck⟩ :=
    exists_strongNeck_radius_of_almost_isometric_segment.{u} kappa hepsilon hsmall
  refine ⟨A, hA, ?_⟩
  intro F hF hbase horient γ hcenter hsegment
  apply hneck F hF hbase horient γ hcenter
  intro s hs t ht
  rw [hsegment s hs t ht]
  constructor
  · apply ENNReal.ofReal_le_ofReal
    nlinarith [abs_nonneg (s - t)]
  · apply ENNReal.ofReal_le_ofReal
    nlinarith [abs_nonneg (s - t)]

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
end
