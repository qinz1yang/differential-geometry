import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.GoodPointNeckArmFrontier
import DifferentialGeometry.Topology.SphereSeparation.PathCrossing
import DifferentialGeometry.Topology.SphereSeparation.ProductLevels

noncomputable section
open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Topology.SphereSeparation

universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}

theorem WindowedModelWitness.minimizingArm_lift_on_prefix
    {delta kappa : ℝ} {x : M} {t : ℝ} (W : WindowedModelWitness delta kappa S x t)
    (a : MinimizingArm (S.base.metric t) x) {s : ℝ} (hs : s ∈ Icc 0 a.length)
    (hbuffer : Real.sqrt (S.scalar t x) * s < modelRadius delta - 1) :
    ContinuousOn (fun v => W.embedding.symm (a.point v)) (Icc 0 s) ∧
      W.embedding.symm (a.point 0) = W.model.basepoint ∧
      (∀ v ∈ Icc 0 s, a.point v ∈ W.embedding.target ∧
        W.embedding.symm (a.point v) ∈ W.embedding.source ∧
        W.embedding (W.embedding.symm (a.point v)) = a.point v) := by
  have htarget : ∀ v ∈ Icc 0 s, a.point v ∈ W.embedding.target := by
    intro v hv
    have hvlen : v ∈ Icc 0 a.length := ⟨hv.1, hv.2.trans hs.2⟩
    have hball : a.point v ∈ riemannianBallOf
        (rescaledMetric S t (S.scalar t x) W.scalar_pos 0) x (modelRadius delta - 1) := by
      change riemannianEDistOf _ x (a.point v) < ENNReal.ofReal (modelRadius delta - 1)
      rw [edistOf_rescaledMetric_zero, a.edistOf_start hvlen,
        ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg
        (mul_nonneg (Real.sqrt_nonneg _) hv.1)).mpr
          ((mul_le_mul_of_nonneg_left hv.2 (Real.sqrt_nonneg _)).trans_lt hbuffer)
    obtain ⟨y, hy, hya⟩ := W.source_capture hball
    exact hya ▸ W.embedding.map_source' hy
  have hcont : ContinuousOn (fun v => W.embedding.symm (a.point v)) (Icc 0 s) :=
    W.embedding.symm.contMDiffOn_toFun.continuousOn.comp
      (a.continuousOn_point.mono (Icc_subset_Icc le_rfl hs.2)) htarget
  have hp : W.model.basepoint ∈ W.embedding.source := by
    apply W.buffered_ball
    change riemannianEDistOf (W.model.S.base.metric 0) W.model.basepoint W.model.basepoint ≤ _
    rw [riemannianEDistOf_self]
    exact bot_le
  have hstart : W.embedding.symm (a.point 0) = W.model.basepoint :=
    (congrArg W.embedding.symm (a.start.trans W.base_map.symm)).trans
      (W.embedding.left_inv' hp)
  exact ⟨hcont, hstart, fun v hv =>
    ⟨htarget v hv, W.embedding.map_target' (htarget v hv),
      W.embedding.right_inv' (htarget v hv)⟩⟩

theorem WindowedModelWitness.exists_arm_crossing_of_separated_model_endpoints
    {delta kappa : ℝ} {x : M} {t : ℝ} (W : WindowedModelWitness delta kappa S x t)
    (a : MinimizingArm (S.base.metric t) x) {s : ℝ} (hs : s ∈ Ioc 0 a.length)
    (hbuffer : Real.sqrt (S.scalar t x) * s < modelRadius delta - 1)
    {T : Set W.model.M} (d : TwoSidedSeparation T)
    (hbase : W.model.basepoint ∈ d.negativeSide)
    (hend : W.embedding.symm (a.point s) ∈ d.positiveSide) :
    ∃ s' ∈ Ioo 0 s,
      W.embedding.symm (a.point s') ∈ T ∧
      W.embedding (W.embedding.symm (a.point s')) = a.point s' := by
  obtain ⟨hcont, hzero, hround⟩ := W.minimizingArm_lift_on_prefix a ⟨hs.1.le, hs.2⟩ hbuffer
  let gamma : ℝ → W.model.M := fun v => W.embedding.symm (a.point v)
  have hstart : gamma 0 ∈ d.negativeSide := by
    change W.embedding.symm (a.point 0) ∈ d.negativeSide
    rw [hzero]
    exact hbase
  obtain ⟨v, hv, hvT⟩ := d.exists_mem_Ioo_of_continuousOn hs.1.le hcont hstart hend
  exact ⟨v, hv, hvT, (hround v ⟨hv.1.le, hv.2.le⟩).2.2⟩

theorem WindowedModelWitness.exists_arm_slice_crossing_of_model_separation
    {delta kappa eps : ℝ} {x : M} {t : ℝ} (W : WindowedModelWitness delta kappa S x t)
    (F : PartialDiffeomorph IC I3 Cylinder W.model.M ∞)
    (neck : StrongNeck S eps x t) (hmap : neck.map = F.trans W.embedding)
    (a : MinimizingArm (S.base.metric t) x) {s h : ℝ} (hs : s ∈ Ioc 0 a.length)
    (hbuffer : Real.sqrt (S.scalar t x) * s < modelRadius delta - 1)
    (d : TwoSidedSeparation (F '' (univ ×ˢ ({h} : Set ℝ))))
    (hbase : W.model.basepoint ∈ d.negativeSide)
    (hend : W.embedding.symm (a.point s) ∈ d.positiveSide) :
    ∃ s' ∈ Ioo 0 s, ∃ p : Sphere 2, a.point s' = neck.map (p, h) := by
  obtain ⟨s', hs', hmem, hround⟩ :=
    W.exists_arm_crossing_of_separated_model_endpoints a hs hbuffer d hbase hend
  obtain ⟨q, hq, hqarm⟩ := hmem
  have hqh : q.2 = h := hq.2
  refine ⟨s', hs', q.1, ?_⟩
  rw [hmap]
  change a.point s' = W.embedding (F (q.1, h))
  have hqeq : (q.1, h) = q := Prod.ext rfl hqh.symm
  rw [hqeq, hqarm]
  exact hround.symm

theorem WindowedModelWitness.exists_armNeckHeights_of_model_slice_separations
    {delta kappa alpha : ℝ} {x : M} {t : ℝ} (W : WindowedModelWitness delta kappa S x t)
    (F : PartialDiffeomorph IC I3 Cylinder W.model.M ∞)
    (neck : StrongNeck S (2 * alpha) x t) (hmap : neck.map = F.trans W.embedding)
    (a b : MinimizingArm (S.base.metric t) x) {s v H : ℝ}
    (hs : s ∈ Ioc 0 a.length) (hv : v ∈ Ioc 0 b.length)
    (hsa : Real.sqrt (S.scalar t x) * s < modelRadius delta - 1)
    (hvb : Real.sqrt (S.scalar t x) * v < modelRadius delta - 1)
    (hdepth : twoArmNoReturnDepth (M := M) ≤ H) (hH : H < (2 * alpha)⁻¹)
    (dneg : TwoSidedSeparation (F '' (univ ×ˢ ({-H} : Set ℝ))))
    (dpos : TwoSidedSeparation (F '' (univ ×ˢ ({H} : Set ℝ))))
    (hbaseNeg : W.model.basepoint ∈ dneg.negativeSide)
    (hbasePos : W.model.basepoint ∈ dpos.negativeSide)
    (hendNeg : W.embedding.symm (a.point s) ∈ dneg.positiveSide)
    (hendPos : W.embedding.symm (b.point v) ∈ dpos.positiveSide) :
    ∃ s' ∈ Ioo 0 s, ∃ v' ∈ Ioo 0 v,
      ArmNeckHeights neck a b s' v' := by
  have hHpos : 0 < H := (twoArmNoReturnDepth_pos (M := M)).trans_le hdepth
  obtain ⟨s', hs', p, hp⟩ := W.exists_arm_slice_crossing_of_model_separation F neck hmap
    a hs hsa dneg hbaseNeg hendNeg
  obtain ⟨v', hv', q, hq⟩ := W.exists_arm_slice_crossing_of_model_separation F neck hmap
    b hv hvb dpos hbasePos hendPos
  refine ⟨s', hs', v', hv', p, q, -H, H, hp, hq, ?_, ?_, ?_, ?_, ?_⟩
  · exact mul_neg_of_neg_of_pos (neg_neg_of_pos hHpos) hHpos
  · simpa only [abs_neg, abs_of_pos hHpos] using hdepth
  · simpa only [abs_neg, abs_of_pos hHpos] using hH
  · simpa only [abs_of_pos hHpos] using hdepth
  · simpa only [abs_of_pos hHpos] using hH

theorem WindowedModelWitness.exists_transversePath_of_model_slice_separations
    {delta kappa alpha : ℝ} {x : M} {t : ℝ} (W : WindowedModelWitness delta kappa S x t)
    (F : PartialDiffeomorph IC I3 Cylinder W.model.M ∞)
    (neck : StrongNeck S (2 * alpha) x t) (hmap : neck.map = F.trans W.embedding)
    (a b : MinimizingArm (S.base.metric t) x) {s v H : ℝ}
    (hs : s ∈ Ioc 0 a.length) (hv : v ∈ Ioc 0 b.length)
    (hsa : Real.sqrt (S.scalar t x) * s < modelRadius delta - 1)
    (hvb : Real.sqrt (S.scalar t x) * v < modelRadius delta - 1)
    (hdepth : twoArmNoReturnDepth (M := M) ≤ H) (hH : H < (2 * alpha)⁻¹)
    (dneg : TwoSidedSeparation (F '' (univ ×ˢ ({-H} : Set ℝ))))
    (dpos : TwoSidedSeparation (F '' (univ ×ˢ ({H} : Set ℝ))))
    (hbaseNeg : W.model.basepoint ∈ dneg.negativeSide)
    (hbasePos : W.model.basepoint ∈ dpos.negativeSide)
    (hendNeg : W.embedding.symm (a.point s) ∈ dneg.positiveSide)
    (hendPos : W.embedding.symm (b.point v) ∈ dpos.positiveSide) :
    ∃ path : TransversePath (a.point a.length) (b.point b.length)
        (neck.map '' (univ ×ˢ ({0} : Set ℝ))),
      (path.intersection = 1 ∨ path.intersection = -1) ∧
      (∀ w ∈ Icc s a.length, a.point w ∉ neck.map '' (univ ×ˢ ({0} : Set ℝ))) ∧
      (∀ w ∈ Icc v b.length, b.point w ∉ neck.map '' (univ ×ˢ ({0} : Set ℝ))) := by
  obtain ⟨s', hs', v', hv', hheight⟩ :=
    W.exists_armNeckHeights_of_model_slice_separations F neck hmap a b hs hv hsa hvb
      hdepth hH dneg dpos hbaseNeg hbasePos hendNeg hendPos
  obtain ⟨path, hinter, hano, hbno⟩ := exists_transversePath_of_armNeckHeights neck a b
    ⟨hs'.1, hs'.2.le.trans hs.2⟩ ⟨hv'.1, hv'.2.le.trans hv.2⟩ hheight
  exact ⟨path, hinter, fun w hw => hano w ⟨hs'.2.le.trans hw.1, hw.2⟩,
    fun w hw => hbno w ⟨hv'.2.le.trans hw.1, hw.2⟩⟩

theorem WindowedModelWitness.exists_transversePath_of_opposite_model_slice_sides
    {delta kappa alpha : ℝ} {x : M} {t : ℝ} (W : WindowedModelWitness delta kappa S x t)
    (F : PartialDiffeomorph IC I3 Cylinder W.model.M ∞)
    (neck : StrongNeck S (2 * alpha) x t) (hmap : neck.map = F.trans W.embedding)
    (a b : MinimizingArm (S.base.metric t) x) {s v H : ℝ}
    (hs : s ∈ Ioc 0 a.length) (hv : v ∈ Ioc 0 b.length)
    (hsa : Real.sqrt (S.scalar t x) * s < modelRadius delta - 1)
    (hvb : Real.sqrt (S.scalar t x) * v < modelRadius delta - 1)
    (hdepth : twoArmNoReturnDepth (M := M) ≤ H) (hH : H < (2 * alpha)⁻¹)
    (dneg : TwoSidedSeparation (F '' (univ ×ˢ ({-H} : Set ℝ))))
    (dpos : TwoSidedSeparation (F '' (univ ×ˢ ({H} : Set ℝ))))
    (hbaseNeg : W.model.basepoint ∈ dneg.negativeSide)
    (hbasePos : W.model.basepoint ∈ dpos.negativeSide)
    (hends : (W.embedding.symm (a.point s) ∈ dneg.positiveSide ∧
        W.embedding.symm (b.point v) ∈ dpos.positiveSide) ∨
      (W.embedding.symm (a.point s) ∈ dpos.positiveSide ∧
        W.embedding.symm (b.point v) ∈ dneg.positiveSide)) :
    ∃ path : TransversePath (a.point a.length) (b.point b.length)
        (neck.map '' (univ ×ˢ ({0} : Set ℝ))),
      (path.intersection = 1 ∨ path.intersection = -1) ∧
      (∀ w ∈ Icc s a.length, a.point w ∉ neck.map '' (univ ×ˢ ({0} : Set ℝ))) ∧
      (∀ w ∈ Icc v b.length, b.point w ∉ neck.map '' (univ ×ˢ ({0} : Set ℝ))) := by
  rcases hends with hends | hends
  · exact W.exists_transversePath_of_model_slice_separations F neck hmap a b hs hv hsa hvb
      hdepth hH dneg dpos hbaseNeg hbasePos hends.1 hends.2
  · obtain ⟨v', hv', s', hs', hheights⟩ :=
      W.exists_armNeckHeights_of_model_slice_separations F neck hmap b a hv hs hvb hsa
        hdepth hH dneg dpos hbaseNeg hbasePos hends.2 hends.1
    obtain ⟨p, q, k, l, hp, hq, hkl, hk, hk', hl, hl'⟩ := hheights
    have hswap : ArmNeckHeights neck a b s' v' :=
      ⟨q, p, l, k, hq, hp, by simpa only [mul_comm] using hkl, hl, hl', hk, hk'⟩
    obtain ⟨path, hinter, hano, hbno⟩ := exists_transversePath_of_armNeckHeights neck a b
      ⟨hs'.1, hs'.2.le.trans hs.2⟩ ⟨hv'.1, hv'.2.le.trans hv.2⟩ hswap
    exact ⟨path, hinter, fun w hw => hano w ⟨hs'.2.le.trans hw.1, hw.2⟩,
      fun w hw => hbno w ⟨hv'.2.le.trans hw.1, hw.2⟩⟩

theorem WindowedModelWitness.exists_transversePath_of_global_cylinder_axial_bounds
    {delta kappa alpha : ℝ} {x : M} {t : ℝ} (W : WindowedModelWitness delta kappa S x t)
    (e : Diffeomorph IC I3 Cylinder W.model.M ∞) (p : Sphere 2)
    (hmark : e (p, 0) = W.model.basepoint)
    (neck : StrongNeck S (2 * alpha) x t)
    (hmap : neck.map = e.toPartialDiffeomorph.trans W.embedding)
    (a b : MinimizingArm (S.base.metric t) x) {s v H : ℝ}
    (hs : s ∈ Ioc 0 a.length) (hv : v ∈ Ioc 0 b.length)
    (hsa : Real.sqrt (S.scalar t x) * s < modelRadius delta - 1)
    (hvb : Real.sqrt (S.scalar t x) * v < modelRadius delta - 1)
    (hdepth : twoArmNoReturnDepth (M := M) ≤ H) (hH : H < (2 * alpha)⁻¹)
    (hneg : (e.symm (W.embedding.symm (a.point s))).2 < -H)
    (hpos : H < (e.symm (W.embedding.symm (b.point v))).2) :
    ∃ path : TransversePath (a.point a.length) (b.point b.length)
        (neck.map '' (univ ×ˢ ({0} : Set ℝ))),
      (path.intersection = 1 ∨ path.intersection = -1) ∧
      (∀ w ∈ Icc s a.length, a.point w ∉ neck.map '' (univ ×ˢ ({0} : Set ℝ))) ∧
      (∀ w ∈ Icc v b.length, b.point w ∉ neck.map '' (univ ×ˢ ({0} : Set ℝ))) := by
  let _ : Nonempty (Sphere 2) := ⟨p⟩
  let dneg := (TwoSidedSeparation.prodLevel e.toHomeomorph (-H)).symm
  let dpos := TwoSidedSeparation.prodLevel e.toHomeomorph H
  have hHpos : 0 < H := (twoArmNoReturnDepth_pos (M := M)).trans_le hdepth
  have hinv : e.symm W.model.basepoint = (p, (0 : ℝ)) := by
    rw [← hmark, e.symm_apply_apply]
  apply W.exists_transversePath_of_model_slice_separations e.toPartialDiffeomorph neck hmap
    a b hs hv hsa hvb hdepth hH dneg dpos
  · change -H < (e.symm W.model.basepoint).2
    rw [hinv]
    exact neg_neg_of_pos hHpos
  · change (e.symm W.model.basepoint).2 < H
    rw [hinv]
    exact hHpos
  · exact hneg
  · exact hpos

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
