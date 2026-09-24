import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.BallChartTransportConnected
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Commutative
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.UnitFillingSmooth
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OrientedFactorBallChart

set_option autoImplicit false
noncomputable section
open Set Metric Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

universe u v

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

namespace OppositeModel

def negDiffeomorph : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞ where
  toEquiv :=
    { toFun := fun x => -x
      invFun := fun x => -x
      left_inv := fun x => neg_neg x
      right_inv := fun x => neg_neg x }
  contMDiff_toFun := contMDiff_neg 𝓘(ℝ, E3) ∞
  contMDiff_invFun := contMDiff_neg 𝓘(ℝ, E3) ∞

theorem negDiffeomorph_apply (x : E3) : negDiffeomorph x = -x := rfl

theorem neg_openPartialHomeomorph_apply (x : E3) :
    (negDiffeomorph.toPartialDiffeomorph.toOpenPartialHomeomorph : E3 → E3) x = -x := rfl

theorem mfderiv_affine_neg (x v : E3) :
    mfderiv (𝓡 3) (𝓡 3) (fun y : E3 => (0 : E3) + (-1 : ℝ) • y) x v = -v := by
  rw [AffineModel.mfderiv_affineDiffeomorph]
  exact neg_one_smul ℝ v

end OppositeModel

namespace BallChart

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]

def reflect (c : BallChart 3 (𝓡 3) M) : BallChart 3 (𝓡 3) M where
  chart := (OppositeModel.negDiffeomorph.toPartialDiffeomorph).trans c.chart
  closedBall_subset_source := by
    intro x hx
    change x ∈ ((OppositeModel.negDiffeomorph.toPartialDiffeomorph
      ).toOpenPartialHomeomorph.trans c.chart.toOpenPartialHomeomorph).source
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨Set.mem_univ _, ?_⟩
    refine c.closedBall_subset_source ?_
    change dist (-x) 0 ≤ 2
    rw [dist_eq_norm, sub_zero, norm_neg]
    simpa [Metric.mem_closedBall, dist_eq_norm] using hx

omit [IsManifold (𝓡 3) ∞ M] in
theorem reflect_apply (c : BallChart 3 (𝓡 3) M) (x : E3) :
    (c.reflect).chart x = c.chart (-x) := rfl

omit [IsManifold (𝓡 3) ∞ M] in
theorem reflect_source_subset (c : BallChart 3 (𝓡 3) M) {x : E3}
    (hx : x ∈ (c.reflect).chart.source) : -x ∈ c.chart.source := by
  have hx' := hx
  change x ∈ ((OppositeModel.negDiffeomorph.toPartialDiffeomorph
    ).toOpenPartialHomeomorph.trans c.chart.toOpenPartialHomeomorph).source at hx'
  rw [OpenPartialHomeomorph.trans_source] at hx'
  simpa [OppositeModel.neg_openPartialHomeomorph_apply] using hx'.2

omit [IsManifold (𝓡 3) ∞ M] in
theorem reflect_image_ball (c : BallChart 3 (𝓡 3) M) :
    (c.reflect).chart '' Metric.ball (0 : E3) 1 = c.chart '' Metric.ball (0 : E3) 1 := by
  have hfun : (⇑(c.reflect).chart : E3 → M) = ⇑c.chart ∘ (fun x : E3 => -x) := by
    funext x; exact c.reflect_apply x
  rw [hfun]
  have himg : (fun x : E3 => -x) '' Metric.ball (0 : E3) 1 = Metric.ball (0 : E3) 1 := by
    ext y; constructor
    · rintro ⟨x, hx, rfl⟩; simpa [Metric.mem_ball, dist_eq_norm] using hx
    · intro hy; exact ⟨-y, by simpa [Metric.mem_ball, dist_eq_norm] using hy, by simp⟩
  rw [Set.image_comp, himg]

omit [IsManifold (𝓡 3) ∞ M] in
theorem reflect_image_closedBall (c : BallChart 3 (𝓡 3) M) :
    (c.reflect).chart '' Metric.closedBall (0 : E3) 1
      = c.chart '' Metric.closedBall (0 : E3) 1 := by
  have hfun : (⇑(c.reflect).chart : E3 → M) = ⇑c.chart ∘ (fun x : E3 => -x) := by
    funext x; exact c.reflect_apply x
  rw [hfun]
  have himg : (fun x : E3 => -x) '' Metric.closedBall (0 : E3) 1
      = Metric.closedBall (0 : E3) 1 := by
    ext y; constructor
    · rintro ⟨x, hx, rfl⟩; simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    · intro hy; exact ⟨-y, by simpa [Metric.mem_closedBall, dist_eq_norm] using hy, by simp⟩
  rw [Set.image_comp, himg]

omit [IsManifold (𝓡 3) ∞ M] in
theorem reflect_boundaryMap_val (c : BallChart 3 (𝓡 3) M) (z : Metric.sphere (0 : E3) 1) :
    ((c.reflect).boundaryMap z : M) = (c.boundaryMap (-z) : M) := rfl

end BallChart

namespace OrientationAssembly

theorem orientation_map_neg_tangent {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] (y : M)
    (o : Orientation ℝ (TangentSpace (𝓡 3) y) (Fin 3)) :
    Orientation.map (Fin 3)
      (LinearEquiv.smulOfNeZero ℝ (TangentSpace (𝓡 3) y) (-1) (by norm_num)) o = -o := by
  rw [Orientation.map_eq_neg_iff_det_neg o _
    (by
      change Fintype.card (Fin 3) = Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))
      rw [finrank_euclideanSpace])]
  have hlm : ((LinearEquiv.smulOfNeZero ℝ (TangentSpace (𝓡 3) y) (-1)
      (by norm_num) : TangentSpace (𝓡 3) y ≃ₗ[ℝ] TangentSpace (𝓡 3) y) : _ →ₗ[ℝ] _)
      = (-1 : ℝ) • (LinearMap.id : TangentSpace (𝓡 3) y →ₗ[ℝ] TangentSpace (𝓡 3) y) := by
    ext v
    simp [LinearEquiv.smulOfNeZero_apply]
  rw [hlm, LinearMap.det_smul, LinearMap.det_id, mul_one]
  have hfr : Module.finrank ℝ (TangentSpace (𝓡 3) y) = 3 := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3
    rw [finrank_euclideanSpace]
    norm_num
  rw [hfr]
  norm_num

end OrientationAssembly

namespace BallChart

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M]

set_option backward.isDefEq.respectTransparency false in
theorem reflect_chart_mfderiv_apply (c : BallChart 3 (𝓡 3) M) {x : E3}
    (hx : -x ∈ c.chart.source) (v : E3) :
    mfderiv (𝓡 3) (𝓡 3) (fun y : E3 => c.chart (-y)) x v
      = (-1 : ℝ) • mfderiv (𝓡 3) (𝓡 3) (fun y : E3 => c.chart y) (-x) v := by
  have hfun : (fun y : E3 => c.chart (-y))
      = fun y : E3 => c.chart ((0 : E3) + (-1 : ℝ) • y) := by
    funext y; simp
  rw [hfun]
  have hcomp : mfderiv (𝓡 3) (𝓡 3) (fun y : E3 => c.chart ((0 : E3) + (-1 : ℝ) • y)) x
      = mfderiv (𝓡 3) (𝓡 3) (fun y : E3 => c.chart y) ((0 : E3) + (-1 : ℝ) • x)
        ∘L mfderiv (𝓡 3) (𝓡 3) (fun y : E3 => (0 : E3) + (-1 : ℝ) • y) x :=
    mfderiv_comp (x := x) (f := fun y : E3 => (0 : E3) + (-1 : ℝ) • y)
      (g := fun y : E3 => c.chart y)
      (PartialDiffeomorph.mdifferentiableAt c.chart (by simp) (by simpa using hx))
      ((AffineModel.affineDiffeomorph (0 : E3) (-1) (by norm_num)).mdifferentiable (by simp) x)
  have hv := DFunLike.congr_fun hcomp v
  erw [ContinuousLinearMap.comp_apply, OppositeModel.mfderiv_affine_neg] at hv
  rw [map_neg] at hv
  rw [show (0 : E3) + (-1 : ℝ) • x = -x from by simp] at hv
  simpa [neg_one_smul] using hv

end BallChart

namespace OrientedBallChart

variable {M : ClosedOrientedManifold.{u} 3}

def reflect (c : OrientedBallChart M) : OrientedBallChart M.opposite where
  toBallChart := c.toBallChart.reflect
  preserves_orientation := by
    intro x hx
    have hx' : -x ∈ c.toBallChart.chart.source := c.toBallChart.reflect_source_subset hx
    have hchain :
        (OrientationAssembly.ballChartTangentEquiv (c.toBallChart.reflect) hx).toLinearEquiv
          = (OrientationAssembly.ballChartTangentEquiv c.toBallChart hx').toLinearEquiv.trans
            (LinearEquiv.smulOfNeZero ℝ
              (TangentSpace (𝓡 3) (c.toBallChart.chart (-x))) (-1) (by norm_num)) := by
      refine LinearEquiv.ext fun v => ?_
      erw [LinearEquiv.trans_apply, LinearEquiv.smulOfNeZero_apply]
      exact BallChart.reflect_chart_mfderiv_apply c.toBallChart hx' (v := v)
    change Orientation.map (Fin 3) (OrientationAssembly.ballChartTangentEquiv
        (c.toBallChart.reflect) hx).toLinearEquiv
        (OrientationAssembly.stdOrientation x)
      = M.opposite.orientation.orientation ((c.toBallChart.reflect).chart x)
    rw [hchain]
    erw [← OrientationAssembly.orientation_map_map_trans
      (OrientationAssembly.ballChartTangentEquiv c.toBallChart hx').toLinearEquiv
      (LinearEquiv.smulOfNeZero ℝ
        (TangentSpace (𝓡 3) (c.toBallChart.chart (-x))) (-1) (by norm_num))
      (OrientationAssembly.stdOrientation x)]
    rw [show OrientationAssembly.stdOrientation x = OrientationAssembly.stdOrientation (-x)
      from OrientationAssembly.stdOrientation_eq x (-x)]
    erw [c.preserves_orientation (-x) hx']
    rw [show M.opposite.orientation = M.orientation.opposite from rfl]
    rw [show (M.orientation.opposite).orientation
        = fun y => -(M.orientation.orientation y) from rfl]
    exact OrientationAssembly.orientation_map_neg_tangent _ _

theorem reflect_apply (c : OrientedBallChart M) (x : E3) :
    (c.reflect).toBallChart.chart x = c.toBallChart.chart (-x) := rfl

end OrientedBallChart


section Identity

variable (X Y : ConnectedClosedOrientedManifold.{u} 3)

theorem boundaryAttachment_val (z : ConnectedSumQuotient.csSphere) :
    (((boundaryAttachment.1.toHomeomorph z : ConnectedSumQuotient.csSphere)) : E3)
      = -(z : E3) := rfl

def reflectChart (M : ConnectedClosedOrientedManifold.{u} 3) : BallChart 3 (𝓡 3) M.Carrier :=
  (orientedBallChart M).toBallChart.reflect

theorem reflectChart_apply (M : ConnectedClosedOrientedManifold.{u} 3) (x : E3) :
    (reflectChart M).chart x = (orientedBallChart M).toBallChart.chart (-x) := rfl

theorem reflectChart_boundaryMap_val (M : ConnectedClosedOrientedManifold.{u} 3)
    (z : ConnectedSumQuotient.csSphere) :
    ((reflectChart M).boundaryMap z : M.Carrier)
      = ((orientedBallChart M).toBallChart.boundaryMap (-z) : M.Carrier) := rfl

theorem reflectHomeomorph_boundary_left (z : ConnectedSumQuotient.csSphere) :
    (Homeomorph.refl X.Carrier) ((orientedBallChart X).toBallChart.chart z)
      = (reflectChart X).chart (boundaryAttachment.1.toHomeomorph z) := by
  rw [reflectChart_apply]
  simp only [Homeomorph.refl_apply]
  congr 1
  rw [boundaryAttachment_val]
  simp

theorem reflectHomeomorph_boundary_right (z : ConnectedSumQuotient.csSphere) :
    (Homeomorph.refl Y.Carrier)
        ((orientedBallChart Y).toBallChart.chart (boundaryAttachment.1.toHomeomorph z))
      = (reflectChart Y).chart (boundaryAttachment.1.toHomeomorph
          (boundaryAttachment.1.toHomeomorph z)) := by
  rw [reflectChart_apply]
  simp only [Homeomorph.refl_apply]
  congr 1
  rw [boundaryAttachment_involutive, boundaryAttachment_val]

def reflectHomeomorph :
    ConnectedSumQuotient (orientedBallChart X).toBallChart (orientedBallChart Y).toBallChart
        boundaryAttachment.1.toHomeomorph
      ≃ₜ ConnectedSumQuotient (reflectChart X) (reflectChart Y)
        boundaryAttachment.1.toHomeomorph :=
  ConnectedSumQuotient.homeomorphOfBallImage
    (orientedBallChart X).toBallChart (reflectChart X)
    (orientedBallChart Y).toBallChart (reflectChart Y)
    boundaryAttachment.1.toHomeomorph boundaryAttachment.1.toHomeomorph
    (Homeomorph.refl X.Carrier) (Homeomorph.refl Y.Carrier)
    (by
      rw [show (⇑(Homeomorph.refl X.Carrier) : X.Carrier → X.Carrier) = id from rfl,
        Set.image_id]
      exact ((orientedBallChart X).toBallChart.reflect_image_ball).symm)
    (by
      rw [show (⇑(Homeomorph.refl Y.Carrier) : Y.Carrier → Y.Carrier) = id from rfl,
        Set.image_id]
      exact ((orientedBallChart Y).toBallChart.reflect_image_ball).symm)
    boundaryAttachment.1.toHomeomorph
    (fun z => reflectHomeomorph_boundary_left X z)
    (fun z => reflectHomeomorph_boundary_right Y z)

end Identity


section Smoothness

variable (X Y : ConnectedClosedOrientedManifold.{u} 3)

theorem mem_interior_reflect {c : BallChart 3 (𝓡 3) X.Carrier} {y : X.Carrier}
    (hy : y ∈ c.interior) : y ∈ c.reflect.interior := by
  rw [BallChart.mem_interior] at hy ⊢
  rwa [BallChart.reflect_image_closedBall]

theorem notMem_chart_ball_of_mem_interior {c : BallChart 3 (𝓡 3) X.Carrier} {y : X.Carrier}
    (hy : y ∈ c.interior) : y ∉ c.chart '' Metric.ball (0 : E3) 1 := by
  rw [BallChart.mem_interior] at hy
  exact fun h => hy (Set.image_mono Metric.ball_subset_closedBall h)

theorem mem_punctured_reflect {c : BallChart 3 (𝓡 3) X.Carrier} {y : X.Carrier}
    (hy : y ∉ c.chart '' Metric.ball (0 : E3) 1) :
    y ∉ c.reflect.chart '' Metric.ball (0 : E3) 1 := by
  rwa [BallChart.reflect_image_ball]

theorem reflectHomeomorph_inl (p : (orientedBallChart X).toBallChart.Punctured) :
    reflectHomeomorph X Y (ConnectedSumQuotient.inl (orientedBallChart X).toBallChart
        (orientedBallChart Y).toBallChart boundaryAttachment.1.toHomeomorph p)
      = ConnectedSumQuotient.inl (reflectChart X) (reflectChart Y)
        boundaryAttachment.1.toHomeomorph
        ⟨(p : X.Carrier), mem_punctured_reflect X p.2⟩ := rfl

theorem reflectHomeomorph_inr (q : (orientedBallChart Y).toBallChart.Punctured) :
    reflectHomeomorph X Y (ConnectedSumQuotient.inr (orientedBallChart X).toBallChart
        (orientedBallChart Y).toBallChart boundaryAttachment.1.toHomeomorph q)
      = ConnectedSumQuotient.inr (reflectChart X) (reflectChart Y)
        boundaryAttachment.1.toHomeomorph
        ⟨(q : Y.Carrier),
          (mem_punctured_reflect Y (c := (orientedBallChart Y).toBallChart) q.2)⟩ := rfl

theorem reflectHomeomorph_interiorLeft
    (u : ↥(orientedBallChart X).toBallChart.interior) :
    reflectHomeomorph X Y (ConnectedSumQuotient.interiorLeft (orientedBallChart X).toBallChart
        (orientedBallChart Y).toBallChart boundaryAttachment.1 u)
      = ConnectedSumQuotient.interiorLeft (reflectChart X) (reflectChart Y) boundaryAttachment.1
        ⟨(u : X.Carrier), mem_interior_reflect X u.2⟩ := by
  rw [ConnectedSumQuotient.interiorLeft, Function.comp_apply, reflectHomeomorph_inl]
  refine congrArg (ConnectedSumQuotient.inl (reflectChart X) (reflectChart Y)
    boundaryAttachment.1.toHomeomorph) (Subtype.ext ?_)
  rfl

theorem reflectHomeomorph_interiorRight
    (v : ↥(orientedBallChart Y).toBallChart.interior) :
    reflectHomeomorph X Y (ConnectedSumQuotient.interiorRight (orientedBallChart X).toBallChart
        (orientedBallChart Y).toBallChart boundaryAttachment.1 v)
      = ConnectedSumQuotient.interiorRight (reflectChart X) (reflectChart Y) boundaryAttachment.1
        ⟨(v : Y.Carrier), mem_interior_reflect Y v.2⟩ := by
  rw [ConnectedSumQuotient.interiorRight, Function.comp_apply, reflectHomeomorph_inr]
  refine congrArg (ConnectedSumQuotient.inr (reflectChart X) (reflectChart Y)
    boundaryAttachment.1.toHomeomorph) (Subtype.ext ?_)
  rfl

end Smoothness

section Collar

def collarReflect : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
    ConnectedSumQuotient.CollarDomain ConnectedSumQuotient.CollarDomain ∞ :=
  boundaryAttachment.1.prodCongr (Diffeomorph.refl 𝓘(ℝ, ℝ)
    ConnectedSumQuotient.collarInterval ∞)

theorem collarReflect_pair (p : ConnectedSumQuotient.CollarDomain) :
    collarReflect p = (boundaryAttachment.1.toHomeomorph p.1, p.2) := by
  rw [collarReflect, Diffeomorph.coe_prodCongr]
  rfl

end Collar

section CollarFormula

variable (X Y : ConnectedClosedOrientedManifold.{u} 3)

theorem reflectHomeomorph_collarMap (p : ConnectedSumQuotient.CollarDomain) :
    reflectHomeomorph X Y (ConnectedSumQuotient.collarMap (orientedBallChart X).toBallChart
        (orientedBallChart Y).toBallChart boundaryAttachment.1 p)
      = ConnectedSumQuotient.collarMap (reflectChart X) (reflectChart Y)
        boundaryAttachment.1 (collarReflect p) := by
  obtain ⟨z, t⟩ := p
  rw [collarReflect_pair]
  by_cases ht : 0 ≤ (t : ℝ)
  · rw [ConnectedSumQuotient.collarMap_of_nonneg _ _ _ (z, t) ht,
      ConnectedSumQuotient.collarMap_of_nonneg _ _ _
        (boundaryAttachment.1.toHomeomorph z, t) ht,
      reflectHomeomorph_inl]
    refine congrArg (ConnectedSumQuotient.inl (reflectChart X) (reflectChart Y)
      boundaryAttachment.1.toHomeomorph) (Subtype.ext ?_)
    change (orientedBallChart X).toBallChart.chart ((1 + (t : ℝ)) • (z : E3))
      = (reflectChart X).chart ((1 + (t : ℝ)) • (boundaryAttachment.1.toHomeomorph z : E3))
    rw [reflectChart_apply]
    congr 1
    rw [boundaryAttachment_val]
    simp
  · rw [ConnectedSumQuotient.collarMap_of_neg _ _ _ (z, t) (lt_of_not_ge ht),
      ConnectedSumQuotient.collarMap_of_neg _ _ _
        (boundaryAttachment.1.toHomeomorph z, t) (lt_of_not_ge ht),
      reflectHomeomorph_inr]
    refine congrArg (ConnectedSumQuotient.inr (reflectChart X) (reflectChart Y)
      boundaryAttachment.1.toHomeomorph) (Subtype.ext ?_)
    change (orientedBallChart Y).toBallChart.chart ((1 - (t : ℝ))
        • (boundaryAttachment.1.toHomeomorph z : E3))
      = (reflectChart Y).chart ((1 - (t : ℝ))
        • (boundaryAttachment.1.toHomeomorph (boundaryAttachment.1.toHomeomorph z) : E3))
    rw [reflectChart_apply]
    congr 1
    rw [boundaryAttachment_involutive, boundaryAttachment_val]
    simp

end CollarFormula



section Smooth

variable (X Y : ConnectedClosedOrientedManifold.{u} 3)

theorem mem_interior_of_reflect {c : BallChart 3 (𝓡 3) X.Carrier} {y : X.Carrier}
    (hy : y ∈ c.reflect.interior) : y ∈ c.interior := by
  rw [BallChart.mem_interior] at hy ⊢
  rwa [BallChart.reflect_image_closedBall] at hy

theorem isLocalDiffeomorph_reflectHomeomorph :
    letI := ConnectedSumQuotient.csChartedSpace (orientedBallChart X).toBallChart
      (orientedBallChart Y).toBallChart boundaryAttachment.1.toHomeomorph
    letI := ConnectedSumQuotient.csIsManifold (orientedBallChart X).toBallChart
      (orientedBallChart Y).toBallChart boundaryAttachment.1.toHomeomorph
      (ConnectedSumQuotient.contDiffOn_reflectMap boundaryAttachment.1)
      (ConnectedSumQuotient.contDiffOn_reflectMapInv boundaryAttachment.1)
    letI := ConnectedSumQuotient.csChartedSpace (reflectChart X) (reflectChart Y)
      boundaryAttachment.1.toHomeomorph
    letI := ConnectedSumQuotient.csIsManifold (reflectChart X) (reflectChart Y)
      boundaryAttachment.1.toHomeomorph
      (ConnectedSumQuotient.contDiffOn_reflectMap boundaryAttachment.1)
      (ConnectedSumQuotient.contDiffOn_reflectMapInv boundaryAttachment.1)
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (reflectHomeomorph X Y) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 3))
      (ConnectedSumQuotient (reflectChart X) (reflectChart Y)
        boundaryAttachment.1.toHomeomorph) :=
    ConnectedSumQuotient.csChartedSpace (reflectChart X) (reflectChart Y)
      boundaryAttachment.1.toHomeomorph
  let _ : IsManifold (𝓡 3) ∞
      (ConnectedSumQuotient (reflectChart X) (reflectChart Y)
        boundaryAttachment.1.toHomeomorph) :=
    ConnectedSumQuotient.csIsManifold (reflectChart X) (reflectChart Y)
      boundaryAttachment.1.toHomeomorph
      (ConnectedSumQuotient.contDiffOn_reflectMap boundaryAttachment.1)
      (ConnectedSumQuotient.contDiffOn_reflectMapInv boundaryAttachment.1)
  let S := smoothConnectedSum X Y (orientedBallChart X) (orientedBallChart Y) boundaryAttachment
  let S' := smoothConnectedSum X.opposite Y.opposite (orientedBallChart X).reflect
    (orientedBallChart Y).reflect boundaryAttachment
  let _ := S.charts
  let _ := S.smooth
  let _ := S'.charts
  let _ := S'.smooth
  intro z
  rcases ConnectedSumQuotient.interior_collar_cover (orientedBallChart X).toBallChart
    (orientedBallChart Y).toBallChart boundaryAttachment.1 z with ⟨u, rfl⟩ | ⟨v, rfl⟩ | ⟨p, rfl⟩
  · have hg : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (ConnectedSumQuotient.interiorLeft (orientedBallChart X).toBallChart
          (orientedBallChart Y).toBallChart boundaryAttachment.1) u :=
      S.interiorLeft_localDiffeomorph u
    have hΦint : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (fun y : ↥(orientedBallChart X).toBallChart.interior =>
          (⟨(Diffeomorph.refl (𝓡 3) X.Carrier ∞) (y : X.Carrier),
            mem_interior_reflect X y.2⟩ : ↥(reflectChart X).interior)) u :=
      isLocalDiffeomorph_subtypeMap (Diffeomorph.refl (𝓡 3) X.Carrier ∞)
        (orientedBallChart X).toBallChart.interior (reflectChart X).interior
        (fun y => mem_interior_reflect X y.2)
        (fun y => mem_interior_of_reflect X y.2) u
    have hcomposite : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (fun y : ↥(orientedBallChart X).toBallChart.interior =>
          ConnectedSumQuotient.interiorLeft (reflectChart X) (reflectChart Y)
            boundaryAttachment.1
            (⟨(Diffeomorph.refl (𝓡 3) X.Carrier ∞) (y : X.Carrier),
              mem_interior_reflect X y.2⟩ : ↥(reflectChart X).interior)) u :=
      hΦint.comp (K := 𝓡 3)
        (P := ConnectedSumQuotient (reflectChart X) (reflectChart Y)
          boundaryAttachment.1.toHomeomorph)
        (S'.interiorLeft_localDiffeomorph
          (⟨(Diffeomorph.refl (𝓡 3) X.Carrier ∞) (u : X.Carrier),
            mem_interior_reflect X u.2⟩ : ↥(reflectChart X).interior))
    have hEq : (fun x : ↥(orientedBallChart X).toBallChart.interior =>
        reflectHomeomorph X Y (ConnectedSumQuotient.interiorLeft
          (orientedBallChart X).toBallChart (orientedBallChart Y).toBallChart
          boundaryAttachment.1 x))
        = fun x : ↥(orientedBallChart X).toBallChart.interior =>
          ConnectedSumQuotient.interiorLeft (reflectChart X) (reflectChart Y)
            boundaryAttachment.1
            (⟨(Diffeomorph.refl (𝓡 3) X.Carrier ∞) (x : X.Carrier),
              mem_interior_reflect X x.2⟩ : ↥(reflectChart X).interior) := by
      funext x
      exact reflectHomeomorph_interiorLeft X Y x
    have hFcomp : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (fun x : ↥(orientedBallChart X).toBallChart.interior =>
          reflectHomeomorph X Y (ConnectedSumQuotient.interiorLeft
            (orientedBallChart X).toBallChart (orientedBallChart Y).toBallChart
            boundaryAttachment.1 x)) u := hEq ▸ hcomposite
    have hpt : hg.localInverse (ConnectedSumQuotient.interiorLeft
        (orientedBallChart X).toBallChart (orientedBallChart Y).toBallChart
        boundaryAttachment.1 u) = u := hg.localInverse_left_inv hg.localInverse_mem_target
    have hFcomp' : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (fun x : ↥(orientedBallChart X).toBallChart.interior =>
          reflectHomeomorph X Y (ConnectedSumQuotient.interiorLeft
            (orientedBallChart X).toBallChart (orientedBallChart Y).toBallChart
            boundaryAttachment.1 x))
        (hg.localInverse (ConnectedSumQuotient.interiorLeft
          (orientedBallChart X).toBallChart (orientedBallChart Y).toBallChart
          boundaryAttachment.1 u)) := by
      rw [hpt]; exact hFcomp
    have h2 : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (fun y => reflectHomeomorph X Y (ConnectedSumQuotient.interiorLeft
          (orientedBallChart X).toBallChart (orientedBallChart Y).toBallChart
          boundaryAttachment.1 (hg.localInverse y)))
        (ConnectedSumQuotient.interiorLeft (orientedBallChart X).toBallChart
          (orientedBallChart Y).toBallChart boundaryAttachment.1 u) :=
      (hg.localInverse_isLocalDiffeomorphAt).comp (K := 𝓡 3)
        (P := ConnectedSumQuotient (reflectChart X) (reflectChart Y)
          boundaryAttachment.1.toHomeomorph) hFcomp'
    refine isLocalDiffeomorphAt_of_eventuallyEq ?_ h2
    filter_upwards [hg.localInverse_eventuallyEq_right] with y hy
    simpa only [Function.comp_apply, id_eq] using
      (congrArg (fun z => reflectHomeomorph X Y z) hy).symm
  · have hg : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (ConnectedSumQuotient.interiorRight (orientedBallChart X).toBallChart
          (orientedBallChart Y).toBallChart boundaryAttachment.1) v :=
      S.interiorRight_localDiffeomorph v
    have hΦint : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (fun y : ↥(orientedBallChart Y).toBallChart.interior =>
          (⟨(Diffeomorph.refl (𝓡 3) Y.Carrier ∞) (y : Y.Carrier),
            mem_interior_reflect Y y.2⟩ : ↥(reflectChart Y).interior)) v :=
      isLocalDiffeomorph_subtypeMap (Diffeomorph.refl (𝓡 3) Y.Carrier ∞)
        (orientedBallChart Y).toBallChart.interior (reflectChart Y).interior
        (fun y => mem_interior_reflect Y y.2)
        (fun y => mem_interior_of_reflect Y y.2) v
    have hcomposite : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (fun y : ↥(orientedBallChart Y).toBallChart.interior =>
          ConnectedSumQuotient.interiorRight (reflectChart X) (reflectChart Y)
            boundaryAttachment.1
            (⟨(Diffeomorph.refl (𝓡 3) Y.Carrier ∞) (y : Y.Carrier),
              mem_interior_reflect Y y.2⟩ : ↥(reflectChart Y).interior)) v :=
      hΦint.comp (K := 𝓡 3)
        (P := ConnectedSumQuotient (reflectChart X) (reflectChart Y)
          boundaryAttachment.1.toHomeomorph)
        (S'.interiorRight_localDiffeomorph
          (⟨(Diffeomorph.refl (𝓡 3) Y.Carrier ∞) (v : Y.Carrier),
            mem_interior_reflect Y v.2⟩ : ↥(reflectChart Y).interior))
    have hEq : (fun x : ↥(orientedBallChart Y).toBallChart.interior =>
        reflectHomeomorph X Y (ConnectedSumQuotient.interiorRight
          (orientedBallChart X).toBallChart (orientedBallChart Y).toBallChart
          boundaryAttachment.1 x))
        = fun x : ↥(orientedBallChart Y).toBallChart.interior =>
          ConnectedSumQuotient.interiorRight (reflectChart X) (reflectChart Y)
            boundaryAttachment.1
            (⟨(Diffeomorph.refl (𝓡 3) Y.Carrier ∞) (x : Y.Carrier),
              mem_interior_reflect Y x.2⟩ : ↥(reflectChart Y).interior) := by
      funext x
      exact reflectHomeomorph_interiorRight X Y x
    have hFcomp : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (fun x : ↥(orientedBallChart Y).toBallChart.interior =>
          reflectHomeomorph X Y (ConnectedSumQuotient.interiorRight
            (orientedBallChart X).toBallChart (orientedBallChart Y).toBallChart
            boundaryAttachment.1 x)) v := hEq ▸ hcomposite
    have hpt : hg.localInverse (ConnectedSumQuotient.interiorRight
        (orientedBallChart X).toBallChart (orientedBallChart Y).toBallChart
        boundaryAttachment.1 v) = v := hg.localInverse_left_inv hg.localInverse_mem_target
    have hFcomp' : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (fun x : ↥(orientedBallChart Y).toBallChart.interior =>
          reflectHomeomorph X Y (ConnectedSumQuotient.interiorRight
            (orientedBallChart X).toBallChart (orientedBallChart Y).toBallChart
            boundaryAttachment.1 x))
        (hg.localInverse (ConnectedSumQuotient.interiorRight
          (orientedBallChart X).toBallChart (orientedBallChart Y).toBallChart
          boundaryAttachment.1 v)) := by
      rw [hpt]; exact hFcomp
    have h2 : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (fun y => reflectHomeomorph X Y (ConnectedSumQuotient.interiorRight
          (orientedBallChart X).toBallChart (orientedBallChart Y).toBallChart
          boundaryAttachment.1 (hg.localInverse y)))
        (ConnectedSumQuotient.interiorRight (orientedBallChart X).toBallChart
          (orientedBallChart Y).toBallChart boundaryAttachment.1 v) :=
      (hg.localInverse_isLocalDiffeomorphAt).comp (K := 𝓡 3)
        (P := ConnectedSumQuotient (reflectChart X) (reflectChart Y)
          boundaryAttachment.1.toHomeomorph) hFcomp'
    refine isLocalDiffeomorphAt_of_eventuallyEq ?_ h2
    filter_upwards [hg.localInverse_eventuallyEq_right] with y hy
    simpa only [Function.comp_apply, id_eq] using
      (congrArg (fun z => reflectHomeomorph X Y z) hy).symm
  · have hg : IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
        (ConnectedSumQuotient.collarMap (orientedBallChart X).toBallChart
          (orientedBallChart Y).toBallChart boundaryAttachment.1) p :=
      S.collar_localDiffeomorph p
    have hreflect : IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ))
        ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ (⇑collarReflect) p :=
      collarReflect.isLocalDiffeomorph p
    have htarget : IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
        (ConnectedSumQuotient.collarMap (reflectChart X) (reflectChart Y)
          boundaryAttachment.1) (collarReflect p) :=
      S'.collar_localDiffeomorph (collarReflect p)
    have hcomp : IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
        (fun x => ConnectedSumQuotient.collarMap (reflectChart X) (reflectChart Y)
          boundaryAttachment.1 (collarReflect x)) p :=
      hreflect.comp (K := 𝓡 3)
        (P := ConnectedSumQuotient (reflectChart X) (reflectChart Y)
          boundaryAttachment.1.toHomeomorph) htarget
    have hEq : (fun x => reflectHomeomorph X Y (ConnectedSumQuotient.collarMap
          (orientedBallChart X).toBallChart (orientedBallChart Y).toBallChart
          boundaryAttachment.1 x))
        = fun x => ConnectedSumQuotient.collarMap (reflectChart X) (reflectChart Y)
          boundaryAttachment.1 (collarReflect x) :=
      funext fun x => reflectHomeomorph_collarMap X Y x
    have hFcomp : IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
        (fun x => reflectHomeomorph X Y (ConnectedSumQuotient.collarMap
          (orientedBallChart X).toBallChart (orientedBallChart Y).toBallChart
          boundaryAttachment.1 x)) p := by
      rw [hEq]; exact hcomp
    have hpt : hg.localInverse (ConnectedSumQuotient.collarMap
        (orientedBallChart X).toBallChart (orientedBallChart Y).toBallChart
        boundaryAttachment.1 p) = p := hg.localInverse_left_inv hg.localInverse_mem_target
    have hFcomp' : IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
        (fun x => reflectHomeomorph X Y (ConnectedSumQuotient.collarMap
          (orientedBallChart X).toBallChart (orientedBallChart Y).toBallChart
          boundaryAttachment.1 x))
        (hg.localInverse (ConnectedSumQuotient.collarMap
          (orientedBallChart X).toBallChart (orientedBallChart Y).toBallChart
          boundaryAttachment.1 p)) := by
      rw [hpt]; exact hFcomp
    have h2 : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (fun y => reflectHomeomorph X Y (ConnectedSumQuotient.collarMap
          (orientedBallChart X).toBallChart (orientedBallChart Y).toBallChart
          boundaryAttachment.1 (hg.localInverse y)))
        (ConnectedSumQuotient.collarMap (orientedBallChart X).toBallChart
          (orientedBallChart Y).toBallChart boundaryAttachment.1 p) :=
      (hg.localInverse_isLocalDiffeomorphAt).comp (K := 𝓡 3)
        (P := ConnectedSumQuotient (reflectChart X) (reflectChart Y)
          boundaryAttachment.1.toHomeomorph) hFcomp'
    refine isLocalDiffeomorphAt_of_eventuallyEq ?_ h2
    filter_upwards [hg.localInverse_eventuallyEq_right] with y hy
    simpa only [Function.comp_apply, id_eq] using
      (congrArg (fun z => reflectHomeomorph X Y z) hy).symm

end Smooth


section Diffeomorphism

variable (X Y : ConnectedClosedOrientedManifold.{u} 3)

theorem nonempty_diffeomorph_reflect :
    Nonempty ((smoothConnectedSum X Y (orientedBallChart X) (orientedBallChart Y)
        boundaryAttachment).toConnectedClosedOrientedManifold.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
      (smoothConnectedSum X.opposite Y.opposite (orientedBallChart X).reflect
        (orientedBallChart Y).reflect
          boundaryAttachment).toConnectedClosedOrientedManifold.Carrier) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 3))
      (ConnectedSumQuotient (orientedBallChart X).toBallChart (orientedBallChart Y).toBallChart
        boundaryAttachment.1.toHomeomorph) :=
    ConnectedSumQuotient.csChartedSpace (orientedBallChart X).toBallChart
      (orientedBallChart Y).toBallChart boundaryAttachment.1.toHomeomorph
  let _ : IsManifold (𝓡 3) ∞
      (ConnectedSumQuotient (orientedBallChart X).toBallChart (orientedBallChart Y).toBallChart
        boundaryAttachment.1.toHomeomorph) :=
    ConnectedSumQuotient.csIsManifold (orientedBallChart X).toBallChart
      (orientedBallChart Y).toBallChart boundaryAttachment.1.toHomeomorph
      (ConnectedSumQuotient.contDiffOn_reflectMap boundaryAttachment.1)
      (ConnectedSumQuotient.contDiffOn_reflectMapInv boundaryAttachment.1)
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 3))
      (ConnectedSumQuotient (reflectChart X) (reflectChart Y)
        boundaryAttachment.1.toHomeomorph) :=
    ConnectedSumQuotient.csChartedSpace (reflectChart X) (reflectChart Y)
      boundaryAttachment.1.toHomeomorph
  let _ : IsManifold (𝓡 3) ∞
      (ConnectedSumQuotient (reflectChart X) (reflectChart Y)
        boundaryAttachment.1.toHomeomorph) :=
    ConnectedSumQuotient.csIsManifold (reflectChart X) (reflectChart Y)
      boundaryAttachment.1.toHomeomorph
      (ConnectedSumQuotient.contDiffOn_reflectMap boundaryAttachment.1)
      (ConnectedSumQuotient.contDiffOn_reflectMapInv boundaryAttachment.1)
  exact ⟨IsLocalDiffeomorph.diffeomorphOfBijective (isLocalDiffeomorph_reflectHomeomorph X Y)
    (reflectHomeomorph X Y).bijective⟩

end Diffeomorphism

end DifferentialGeometry.Topology
