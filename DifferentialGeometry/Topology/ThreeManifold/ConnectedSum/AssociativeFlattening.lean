import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Associative
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OrientedFactorBallChart
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict

set_option autoImplicit false
noncomputable section
open Set Function Manifold Topology Metric
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Topology.ConnectedSumQuotient

namespace DifferentialGeometry.Topology

universe u

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

private abbrev ModelSphere : Type := Metric.sphere (0 : E3) 1

private def modelSpherePoint : ModelSphere :=
  Classical.choice (nonempty_sphere_of_neZero (n := 3))

private theorem ball_one_subset_closedBall_two {x : E3} (hx : x ∈ ball (0 : E3) 1) :
    x ∈ closedBall (0 : E3) 2 :=
  closedBall_two_subset_iff' (Metric.ball_subset_closedBall hx)

private theorem sphere_one_subset_closedBall_two {x : E3} (hx : x ∈ sphere (0 : E3) 1) :
    x ∈ closedBall (0 : E3) 2 :=
  closedBall_two_subset_iff' (Metric.sphere_subset_closedBall hx)

private theorem chart_sphere_not_mem_chart_ball {M : Type*} [TopologicalSpace M]
    [ChartedSpace E3 M] (c : BallChart 3 (𝓡 3) M) {z : E3} (hz : z ∈ sphere (0 : E3) 1) :
    c.chart z ∉ c.chart '' ball (0 : E3) 1 := by
  rintro ⟨w, hw, hweq⟩
  have hzw : w = z :=
    c.chart.toPartialEquiv.injOn (c.ball_subset_source hw) (c.sphere_subset_source hz) hweq
  have hz1 : ‖z‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hz
  have hw1 : ‖w‖ < 1 := by simpa [mem_ball, dist_zero_right] using hw
  rw [hzw] at hw1
  linarith

private abbrev sumCarrier (M N : ConnectedClosedOrientedManifold.{u} 3)
    (c : OrientedBallChart M.toClosedOrientedManifold)
    (d : OrientedBallChart N.toClosedOrientedManifold) : ConnectedClosedOrientedManifold.{u} 3 :=
  (smoothConnectedSum M N c d boundaryAttachment).toConnectedClosedOrientedManifold

private abbrev leftSum (X Y : ConnectedClosedOrientedManifold.{u} 3)
    (δ : OrientedBallChart Y.toClosedOrientedManifold) : ConnectedClosedOrientedManifold.{u} 3 :=
  sumCarrier X Y (orientedBallChart X) δ

private abbrev rightSum (Y Z : ConnectedClosedOrientedManifold.{u} 3)
    (dY' : OrientedBallChart Y.toClosedOrientedManifold) : ConnectedClosedOrientedManifold.{u} 3 :=
  sumCarrier Y Z dY' (orientedBallChart Z)

private abbrev disjointInr (Y : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold) : Prop :=
  ∀ x ∈ closedBall (0 : E3) 2, dY'.chart x ∉ δ.chart '' closedBall (0 : E3) 1

private abbrev disjointInl (Y : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold) : Prop :=
  ∀ x ∈ closedBall (0 : E3) 2, δ.chart x ∉ dY'.chart '' closedBall (0 : E3) 1

private def factorChartInr (X Y : ConnectedClosedOrientedManifold.{u} 3)
    (δ : OrientedBallChart Y.toClosedOrientedManifold)
    (dY' : OrientedBallChart Y.toClosedOrientedManifold) (h1 : disjointInr Y δ dY') :
    OrientedBallChart (leftSum X Y δ).toClosedOrientedManifold :=
  Classical.choose (exists_orientedBallChart_inr (orientedBallChart X) δ boundaryAttachment dY' h1)

private theorem factorChartInr_spec (X Y : ConnectedClosedOrientedManifold.{u} 3)
    (δ : OrientedBallChart Y.toClosedOrientedManifold)
    (dY' : OrientedBallChart Y.toClosedOrientedManifold) (h1 : disjointInr Y δ dY')
    {x : E3} (hx : x ∈ closedBall (0 : E3) 2) :
    ∃ hx' : dY'.chart x ∉ δ.chart '' ball (0 : E3) 1,
      (factorChartInr X Y δ dY' h1).toBallChart.chart x =
        inr (orientedBallChart X).toBallChart δ.toBallChart
          boundaryAttachment.1.toHomeomorph ⟨dY'.chart x, hx'⟩ :=
  Classical.choose_spec
    (exists_orientedBallChart_inr (orientedBallChart X) δ boundaryAttachment dY' h1) x hx

private def factorChartInl (Y Z : ConnectedClosedOrientedManifold.{u} 3)
    (dY' : OrientedBallChart Y.toClosedOrientedManifold)
    (δ : OrientedBallChart Y.toClosedOrientedManifold) (h2 : disjointInl Y δ dY') :
    OrientedBallChart (rightSum Y Z dY').toClosedOrientedManifold :=
  Classical.choose
    (exists_orientedBallChart_inl dY' (orientedBallChart Z) boundaryAttachment δ h2)

private theorem factorChartInl_spec (Y Z : ConnectedClosedOrientedManifold.{u} 3)
    (dY' : OrientedBallChart Y.toClosedOrientedManifold)
    (δ : OrientedBallChart Y.toClosedOrientedManifold) (h2 : disjointInl Y δ dY')
    {x : E3} (hx : x ∈ closedBall (0 : E3) 2) :
    ∃ hx' : δ.chart x ∉ dY'.chart '' ball (0 : E3) 1,
      (factorChartInl Y Z dY' δ h2).toBallChart.chart x =
        inl dY'.toBallChart (orientedBallChart Z).toBallChart
          boundaryAttachment.1.toHomeomorph ⟨δ.chart x, hx'⟩ :=
  Classical.choose_spec
    (exists_orientedBallChart_inl dY' (orientedBallChart Z) boundaryAttachment δ h2) x hx

private abbrev leftQuot (X Y Z : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold) (h1 : disjointInr Y δ dY') :=
  ConnectedSumQuotient (factorChartInr X Y δ dY' h1).toBallChart
    (orientedBallChart Z).toBallChart boundaryAttachment.1.toHomeomorph

private abbrev rightQuot (X Y Z : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold) (h2 : disjointInl Y δ dY') :=
  ConnectedSumQuotient (orientedBallChart X).toBallChart
    (factorChartInl Y Z dY' δ h2).toBallChart boundaryAttachment.1.toHomeomorph

private theorem inr_mem_factorChartInr_punctured (X Y : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold) (h1 : disjointInr Y δ dY')
    {y : δ.Punctured} (hy : (y : Y.Carrier) ∉ dY'.chart '' ball (0 : E3) 1) :
    inr (orientedBallChart X).toBallChart δ.toBallChart boundaryAttachment.1.toHomeomorph y
      ∉ (factorChartInr X Y δ dY' h1).toBallChart.chart '' ball (0 : E3) 1 := by
  intro hmem
  obtain ⟨w, hw, hweq⟩ := hmem
  obtain ⟨hw', hfw⟩ := factorChartInr_spec X Y δ dY' h1 (ball_one_subset_closedBall_two hw)
  rw [hfw] at hweq
  have hinj : (⟨dY'.chart w, hw'⟩ : δ.Punctured) = y :=
    inr_injective (orientedBallChart X).toBallChart δ.toBallChart
      boundaryAttachment.1.toHomeomorph hweq
  exact hy ⟨w, hw, congrArg Subtype.val hinj⟩

private theorem inl_mem_factorChartInr_punctured (X Y : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold) (h1 : disjointInr Y δ dY')
    (h2 : disjointInl Y δ dY') {x : (orientedBallChart X).toBallChart.Punctured} :
    inl (orientedBallChart X).toBallChart δ.toBallChart boundaryAttachment.1.toHomeomorph x
      ∉ (factorChartInr X Y δ dY' h1).toBallChart.chart '' ball (0 : E3) 1 := by
  intro hmem
  obtain ⟨w, hw, hweq⟩ := hmem
  obtain ⟨hw', hfw⟩ := factorChartInr_spec X Y δ dY' h1 (ball_one_subset_closedBall_two hw)
  rw [hfw] at hweq
  obtain ⟨ζ, -, hζ'⟩ :=
    (inl_eq_inr_iff (orientedBallChart X).toBallChart δ.toBallChart
      boundaryAttachment.1.toHomeomorph x ⟨dY'.chart w, hw'⟩).mp hweq.symm
  exact h2 (boundaryAttachment.1.toHomeomorph ζ)
    (sphere_one_subset_closedBall_two (boundaryAttachment.1.toHomeomorph ζ).2)
    ⟨w, ball_subset_closedBall hw, (congrArg Subtype.val hζ').symm⟩

private theorem inr_mem_factorChartInl_punctured (Y Z : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold) (h1 : disjointInr Y δ dY')
    (h2 : disjointInl Y δ dY') {z : (orientedBallChart Z).toBallChart.Punctured} :
    inr dY'.toBallChart (orientedBallChart Z).toBallChart boundaryAttachment.1.toHomeomorph z
      ∉ (factorChartInl Y Z dY' δ h2).toBallChart.chart '' ball (0 : E3) 1 := by
  intro hmem
  obtain ⟨w, hw, hweq⟩ := hmem
  obtain ⟨hw', hgw⟩ := factorChartInl_spec Y Z dY' δ h2 (ball_one_subset_closedBall_two hw)
  rw [hgw] at hweq
  obtain ⟨ζ, hζ, -⟩ :=
    (inl_eq_inr_iff dY'.toBallChart (orientedBallChart Z).toBallChart
      boundaryAttachment.1.toHomeomorph ⟨δ.chart w, hw'⟩ z).mp hweq
  exact h1 ζ (sphere_one_subset_closedBall_two ζ.2)
    ⟨w, ball_subset_closedBall hw, (congrArg Subtype.val hζ).symm⟩

private theorem inl_mem_factorChartInl_punctured (Y Z : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold) (h2 : disjointInl Y δ dY')
    {y : dY'.Punctured} (hy : (y : Y.Carrier) ∉ δ.chart '' ball (0 : E3) 1) :
    inl dY'.toBallChart (orientedBallChart Z).toBallChart boundaryAttachment.1.toHomeomorph y
      ∉ (factorChartInl Y Z dY' δ h2).toBallChart.chart '' ball (0 : E3) 1 := by
  intro hmem
  obtain ⟨w, hw, hweq⟩ := hmem
  obtain ⟨hw', hgw⟩ := factorChartInl_spec Y Z dY' δ h2 (ball_one_subset_closedBall_two hw)
  rw [hgw] at hweq
  have hinj : (⟨δ.chart w, hw'⟩ : dY'.Punctured) = y :=
    inl_injective dY'.toBallChart (orientedBallChart Z).toBallChart
      boundaryAttachment.1.toHomeomorph hweq
  exact hy ⟨w, hw, congrArg Subtype.val hinj⟩

private def yPartRight (X Y Z : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold) (h2 : disjointInl Y δ dY')
    (y : δ.Punctured) (hy : (y : Y.Carrier) ∉ dY'.chart '' ball (0 : E3) 1) :
    rightQuot X Y Z δ dY' h2 :=
  inr (orientedBallChart X).toBallChart (factorChartInl Y Z dY' δ h2).toBallChart
    boundaryAttachment.1.toHomeomorph
    ⟨inl dY'.toBallChart (orientedBallChart Z).toBallChart boundaryAttachment.1.toHomeomorph
      ⟨y, hy⟩,
      inl_mem_factorChartInl_punctured Y Z δ dY' h2 (y := ⟨y, hy⟩) y.2⟩

private def yPartMap (X Y Z : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold) (h2 : disjointInl Y δ dY')
    (y : δ.Punctured) : rightQuot X Y Z δ dY' h2 := by
  classical
  exact if hy : (y : Y.Carrier) ∉ dY'.chart '' ball (0 : E3) 1
    then yPartRight X Y Z δ dY' h2 y hy
    else inl (orientedBallChart X).toBallChart (factorChartInl Y Z dY' δ h2).toBallChart
      boundaryAttachment.1.toHomeomorph
      ((orientedBallChart X).toBallChart.boundaryMap modelSpherePoint)

private theorem yPartMap_of_mem (X Y Z : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold) (h2 : disjointInl Y δ dY')
    {y : δ.Punctured} (hy : (y : Y.Carrier) ∉ dY'.chart '' ball (0 : E3) 1) :
    yPartMap X Y Z δ dY' h2 y = yPartRight X Y Z δ dY' h2 y hy := dif_pos hy

private theorem yPartMap_boundary (X Y Z : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold) (h2 : disjointInl Y δ dY')
    (ζ : ModelSphere) :
    yPartMap X Y Z δ dY' h2 (δ.boundaryMap (boundaryAttachment.1.toHomeomorph ζ)) =
      inl (orientedBallChart X).toBallChart (factorChartInl Y Z dY' δ h2).toBallChart
        boundaryAttachment.1.toHomeomorph
        ((orientedBallChart X).toBallChart.boundaryMap ζ) := by
  have hmem :
      ((δ.boundaryMap (boundaryAttachment.1.toHomeomorph ζ)) : Y.Carrier)
        ∉ dY'.chart '' ball (0 : E3) 1 := fun h =>
    h2 (boundaryAttachment.1.toHomeomorph ζ)
      (sphere_one_subset_closedBall_two (boundaryAttachment.1.toHomeomorph ζ).2)
      (image_mono ball_subset_closedBall h)
  rw [yPartMap_of_mem X Y Z δ dY' h2 hmem, yPartRight]
  obtain ⟨hx', hgx⟩ := factorChartInl_spec Y Z dY' δ h2
    (sphere_one_subset_closedBall_two (boundaryAttachment.1.toHomeomorph ζ).2)
  have hgx' : (factorChartInl Y Z dY' δ h2).toBallChart.chart
        (boundaryAttachment.1.toHomeomorph ζ) =
      inl dY'.toBallChart (orientedBallChart Z).toBallChart boundaryAttachment.1.toHomeomorph
        ⟨δ.chart (boundaryAttachment.1.toHomeomorph ζ), hx'⟩ := hgx
  refine ((congrArg (inr (orientedBallChart X).toBallChart
    (factorChartInl Y Z dY' δ h2).toBallChart boundaryAttachment.1.toHomeomorph)
    (Subtype.ext ?_))).trans (boundary_eq (orientedBallChart X).toBallChart
      (factorChartInl Y Z dY' δ h2).toBallChart boundaryAttachment.1.toHomeomorph ζ).symm
  change inl dY'.toBallChart (orientedBallChart Z).toBallChart boundaryAttachment.1.toHomeomorph
      ⟨(δ.boundaryMap (boundaryAttachment.1.toHomeomorph ζ) : Y.Carrier), hmem⟩ =
    (factorChartInl Y Z dY' δ h2).toBallChart.chart (boundaryAttachment.1.toHomeomorph ζ)
  rw [hgx']
  exact congrArg (inl dY'.toBallChart (orientedBallChart Z).toBallChart
    boundaryAttachment.1.toHomeomorph) (Subtype.ext rfl)

private def leftMapFun (X Y Z : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold) (h2 : disjointInl Y δ dY') :
    (orientedBallChart X).toBallChart.Punctured ⊕ δ.Punctured →
      rightQuot X Y Z δ dY' h2 :=
  Sum.elim (fun x => inl (orientedBallChart X).toBallChart
      (factorChartInl Y Z dY' δ h2).toBallChart boundaryAttachment.1.toHomeomorph x)
    (fun y => yPartMap X Y Z δ dY' h2 y)

private theorem leftMapFun_rel (X Y Z : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold) (h2 : disjointInl Y δ dY')
    (u v : (orientedBallChart X).toBallChart.Punctured ⊕ δ.Punctured)
    (h : adjunctionRel (orientedBallChart X).toBallChart.boundaryMap
      (δ.boundaryMap ∘ boundaryAttachment.1.toHomeomorph) u v) :
    leftMapFun X Y Z δ dY' h2 u = leftMapFun X Y Z δ dY' h2 v := by
  obtain ⟨ζ, ⟨hu, hv⟩ | ⟨hv, hu⟩⟩ := h
  · rw [hu, hv]
    simp only [leftMapFun, Sum.elim_inl, Sum.elim_inr, Function.comp_apply]
    exact (yPartMap_boundary X Y Z δ dY' h2 ζ).symm
  · rw [hv, hu]
    simp only [leftMapFun, Sum.elim_inl, Sum.elim_inr, Function.comp_apply]
    exact yPartMap_boundary X Y Z δ dY' h2 ζ

private def leftMap (X Y Z : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold) (h2 : disjointInl Y δ dY') :
    (leftSum X Y δ).Carrier → rightQuot X Y Z δ dY' h2 :=
  Quot.lift (leftMapFun X Y Z δ dY' h2) (leftMapFun_rel X Y Z δ dY' h2)

private theorem leftMap_inl (X Y Z : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold) (h2 : disjointInl Y δ dY')
    (x : (orientedBallChart X).toBallChart.Punctured) :
    leftMap X Y Z δ dY' h2 (inl (orientedBallChart X).toBallChart δ.toBallChart
      boundaryAttachment.1.toHomeomorph x) =
      inl (orientedBallChart X).toBallChart (factorChartInl Y Z dY' δ h2).toBallChart
        boundaryAttachment.1.toHomeomorph x := rfl

private theorem leftMap_inr (X Y Z : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold) (h2 : disjointInl Y δ dY')
    {y : δ.Punctured} (hy : (y : Y.Carrier) ∉ dY'.chart '' ball (0 : E3) 1) :
    leftMap X Y Z δ dY' h2 (inr (orientedBallChart X).toBallChart δ.toBallChart
      boundaryAttachment.1.toHomeomorph y) = yPartRight X Y Z δ dY' h2 y hy :=
  yPartMap_of_mem X Y Z δ dY' h2 hy

private def zPartRight (X Y Z : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold) (h1 : disjointInr Y δ dY')
    (h2 : disjointInl Y δ dY') (z : (orientedBallChart Z).toBallChart.Punctured) :
    rightQuot X Y Z δ dY' h2 :=
  inr (orientedBallChart X).toBallChart (factorChartInl Y Z dY' δ h2).toBallChart
    boundaryAttachment.1.toHomeomorph
    ⟨inr dY'.toBallChart (orientedBallChart Z).toBallChart boundaryAttachment.1.toHomeomorph z,
      inr_mem_factorChartInl_punctured Y Z δ dY' h1 h2 (z := z)⟩

private def flattenFun (X Y Z : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold) (h1 : disjointInr Y δ dY')
    (h2 : disjointInl Y δ dY') :
    (factorChartInr X Y δ dY' h1).toBallChart.Punctured ⊕
        (orientedBallChart Z).toBallChart.Punctured →
      rightQuot X Y Z δ dY' h2 :=
  Sum.elim (fun p => leftMap X Y Z δ dY' h2 (p : (leftSum X Y δ).Carrier))
    (fun z => zPartRight X Y Z δ dY' h1 h2 z)

private theorem flattenFun_rel (X Y Z : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold) (h1 : disjointInr Y δ dY')
    (h2 : disjointInl Y δ dY')
    (u v : (factorChartInr X Y δ dY' h1).toBallChart.Punctured ⊕
        (orientedBallChart Z).toBallChart.Punctured)
    (h : adjunctionRel (factorChartInr X Y δ dY' h1).toBallChart.boundaryMap
      ((orientedBallChart Z).toBallChart.boundaryMap ∘ boundaryAttachment.1.toHomeomorph) u v) :
    flattenFun X Y Z δ dY' h1 h2 u = flattenFun X Y Z δ dY' h1 h2 v := by
  obtain ⟨ζ, ⟨hu, hv⟩ | ⟨hv, hu⟩⟩ := h
  · rw [hu, hv]
    simp only [flattenFun, Sum.elim_inl, Sum.elim_inr, Function.comp_apply]
    obtain ⟨hx, hfζ⟩ := factorChartInr_spec X Y δ dY' h1
      (sphere_one_subset_closedBall_two ζ.2)
    have hmem : dY'.chart (ζ : E3) ∉ dY'.chart '' ball (0 : E3) 1 :=
      chart_sphere_not_mem_chart_ball dY'.toBallChart ζ.2
    have hleft : leftMap X Y Z δ dY' h2
        ((factorChartInr X Y δ dY' h1).toBallChart.boundaryMap ζ :
          (leftSum X Y δ).Carrier) =
        yPartRight X Y Z δ dY' h2 ⟨dY'.chart (ζ : E3), hx⟩ hmem := by
      rw [show ((factorChartInr X Y δ dY' h1).toBallChart.boundaryMap ζ :
          (leftSum X Y δ).Carrier) =
          inr (orientedBallChart X).toBallChart δ.toBallChart
            boundaryAttachment.1.toHomeomorph ⟨dY'.chart (ζ : E3), hx⟩ from hfζ]
      exact leftMap_inr X Y Z δ dY' h2 hmem
    refine hleft.trans ?_
    refine congrArg (inr (orientedBallChart X).toBallChart
      (factorChartInl Y Z dY' δ h2).toBallChart boundaryAttachment.1.toHomeomorph)
      (Subtype.ext ?_)
    refine (congrArg (inl dY'.toBallChart (orientedBallChart Z).toBallChart
      boundaryAttachment.1.toHomeomorph) (Subtype.ext rfl)).trans ?_
    exact boundary_eq dY'.toBallChart (orientedBallChart Z).toBallChart
      boundaryAttachment.1.toHomeomorph ζ
  · rw [hv, hu]
    simp only [flattenFun, Sum.elim_inl, Sum.elim_inr, Function.comp_apply]
    obtain ⟨hx, hfζ⟩ := factorChartInr_spec X Y δ dY' h1
      (sphere_one_subset_closedBall_two ζ.2)
    have hmem : dY'.chart (ζ : E3) ∉ dY'.chart '' ball (0 : E3) 1 :=
      chart_sphere_not_mem_chart_ball dY'.toBallChart ζ.2
    have hleft : leftMap X Y Z δ dY' h2
        ((factorChartInr X Y δ dY' h1).toBallChart.boundaryMap ζ :
          (leftSum X Y δ).Carrier) =
        yPartRight X Y Z δ dY' h2 ⟨dY'.chart (ζ : E3), hx⟩ hmem := by
      rw [show ((factorChartInr X Y δ dY' h1).toBallChart.boundaryMap ζ :
          (leftSum X Y δ).Carrier) =
          inr (orientedBallChart X).toBallChart δ.toBallChart
            boundaryAttachment.1.toHomeomorph ⟨dY'.chart (ζ : E3), hx⟩ from hfζ]
      exact leftMap_inr X Y Z δ dY' h2 hmem
    refine ((congrArg (inr (orientedBallChart X).toBallChart
      (factorChartInl Y Z dY' δ h2).toBallChart boundaryAttachment.1.toHomeomorph)
      (Subtype.ext ?_)).trans hleft.symm)
    refine (congrArg (inr dY'.toBallChart (orientedBallChart Z).toBallChart
      boundaryAttachment.1.toHomeomorph) (Subtype.ext rfl)).trans ?_
    exact (boundary_eq dY'.toBallChart (orientedBallChart Z).toBallChart
      boundaryAttachment.1.toHomeomorph ζ).symm

private def flattenMap (X Y Z : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold) (h1 : disjointInr Y δ dY')
    (h2 : disjointInl Y δ dY') :
    leftQuot X Y Z δ dY' h1 → rightQuot X Y Z δ dY' h2 :=
  Quot.lift (flattenFun X Y Z δ dY' h1 h2) (flattenFun_rel X Y Z δ dY' h1 h2)

private theorem flattenMap_inl_inl (X Y Z : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold) (h1 : disjointInr Y δ dY')
    (h2 : disjointInl Y δ dY') (x : (orientedBallChart X).toBallChart.Punctured) :
    flattenMap X Y Z δ dY' h1 h2
        (inl (factorChartInr X Y δ dY' h1).toBallChart (orientedBallChart Z).toBallChart
          boundaryAttachment.1.toHomeomorph
          ⟨inl (orientedBallChart X).toBallChart δ.toBallChart
            boundaryAttachment.1.toHomeomorph x,
            inl_mem_factorChartInr_punctured X Y δ dY' h1 h2⟩) =
      inl (orientedBallChart X).toBallChart (factorChartInl Y Z dY' δ h2).toBallChart
        boundaryAttachment.1.toHomeomorph x := by
  change leftMap X Y Z δ dY' h2
    (inl (orientedBallChart X).toBallChart δ.toBallChart boundaryAttachment.1.toHomeomorph x) =
    inl (orientedBallChart X).toBallChart (factorChartInl Y Z dY' δ h2).toBallChart
      boundaryAttachment.1.toHomeomorph x
  exact leftMap_inl X Y Z δ dY' h2 x

private theorem flattenMap_inl_inr (X Y Z : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold) (h1 : disjointInr Y δ dY')
    (h2 : disjointInl Y δ dY') (y : δ.Punctured)
    (hy : (y : Y.Carrier) ∉ dY'.chart '' ball (0 : E3) 1) :
    flattenMap X Y Z δ dY' h1 h2
        (inl (factorChartInr X Y δ dY' h1).toBallChart (orientedBallChart Z).toBallChart
          boundaryAttachment.1.toHomeomorph
          ⟨inr (orientedBallChart X).toBallChart δ.toBallChart
            boundaryAttachment.1.toHomeomorph y,
            inr_mem_factorChartInr_punctured X Y δ dY' h1 hy⟩) =
      inr (orientedBallChart X).toBallChart (factorChartInl Y Z dY' δ h2).toBallChart
        boundaryAttachment.1.toHomeomorph
        ⟨inl dY'.toBallChart (orientedBallChart Z).toBallChart
          boundaryAttachment.1.toHomeomorph ⟨y, hy⟩,
          inl_mem_factorChartInl_punctured Y Z δ dY' h2 (y := ⟨y, hy⟩) y.2⟩ := by
  change leftMap X Y Z δ dY' h2
    (inr (orientedBallChart X).toBallChart δ.toBallChart boundaryAttachment.1.toHomeomorph y) =
    inr (orientedBallChart X).toBallChart (factorChartInl Y Z dY' δ h2).toBallChart
      boundaryAttachment.1.toHomeomorph
      ⟨inl dY'.toBallChart (orientedBallChart Z).toBallChart
        boundaryAttachment.1.toHomeomorph ⟨y, hy⟩,
        inl_mem_factorChartInl_punctured Y Z δ dY' h2 (y := ⟨y, hy⟩) y.2⟩
  exact leftMap_inr X Y Z δ dY' h2 hy

private theorem flattenMap_inr (X Y Z : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold) (h1 : disjointInr Y δ dY')
    (h2 : disjointInl Y δ dY') (z : (orientedBallChart Z).toBallChart.Punctured) :
    flattenMap X Y Z δ dY' h1 h2
        (inr (factorChartInr X Y δ dY' h1).toBallChart (orientedBallChart Z).toBallChart
          boundaryAttachment.1.toHomeomorph z) =
      inr (orientedBallChart X).toBallChart (factorChartInl Y Z dY' δ h2).toBallChart
        boundaryAttachment.1.toHomeomorph
        ⟨inr dY'.toBallChart (orientedBallChart Z).toBallChart
          boundaryAttachment.1.toHomeomorph z,
          inr_mem_factorChartInl_punctured Y Z δ dY' h1 h2 (z := z)⟩ := by
  change zPartRight X Y Z δ dY' h1 h2 z =
    inr (orientedBallChart X).toBallChart (factorChartInl Y Z dY' δ h2).toBallChart
      boundaryAttachment.1.toHomeomorph
      ⟨inr dY'.toBallChart (orientedBallChart Z).toBallChart
        boundaryAttachment.1.toHomeomorph z,
        inr_mem_factorChartInl_punctured Y Z δ dY' h1 h2 (z := z)⟩
  rfl

private def xPartLeft (X Y Z : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold) (h1 : disjointInr Y δ dY')
    (y : dY'.Punctured)
    (hy : (y : Y.Carrier) ∉ δ.chart '' ball (0 : E3) 1) :
    leftQuot X Y Z δ dY' h1 :=
  inl (factorChartInr X Y δ dY' h1).toBallChart (orientedBallChart Z).toBallChart
    boundaryAttachment.1.toHomeomorph
    ⟨inr (orientedBallChart X).toBallChart δ.toBallChart boundaryAttachment.1.toHomeomorph
      ⟨y, hy⟩,
      inr_mem_factorChartInr_punctured X Y δ dY' h1 (y := ⟨y, hy⟩) y.2⟩

private def xPartMap (X Y Z : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold) (h1 : disjointInr Y δ dY')
    (y : dY'.Punctured) : leftQuot X Y Z δ dY' h1 := by
  classical
  exact if hy : (y : Y.Carrier) ∉ δ.chart '' ball (0 : E3) 1 then xPartLeft X Y Z δ dY' h1 y hy
    else inl (factorChartInr X Y δ dY' h1).toBallChart (orientedBallChart Z).toBallChart
      boundaryAttachment.1.toHomeomorph
      ((factorChartInr X Y δ dY' h1).toBallChart.boundaryMap modelSpherePoint)

private theorem xPartMap_of_mem (X Y Z : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold) (h1 : disjointInr Y δ dY')
    {y : dY'.Punctured}
    (hy : (y : Y.Carrier) ∉ δ.chart '' ball (0 : E3) 1) :
    xPartMap X Y Z δ dY' h1 y = xPartLeft X Y Z δ dY' h1 y hy := dif_pos hy

private theorem xPartMap_boundary (X Y Z : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold) (h1 : disjointInr Y δ dY')
    (ζ : ModelSphere) :
    xPartMap X Y Z δ dY' h1 (dY'.boundaryMap ζ) =
      inr (factorChartInr X Y δ dY' h1).toBallChart (orientedBallChart Z).toBallChart
        boundaryAttachment.1.toHomeomorph
        ((orientedBallChart Z).toBallChart.boundaryMap (boundaryAttachment.1.toHomeomorph ζ)) := by
  have hmem : ((dY'.boundaryMap ζ) : Y.Carrier) ∉ δ.chart '' ball (0 : E3) 1 := fun h =>
    h1 ζ (sphere_one_subset_closedBall_two ζ.2) (image_mono ball_subset_closedBall h)
  rw [xPartMap_of_mem X Y Z δ dY' h1 hmem, xPartLeft]
  obtain ⟨hx, hfζ⟩ := factorChartInr_spec X Y δ dY' h1 (sphere_one_subset_closedBall_two ζ.2)
  refine (congrArg (inl (factorChartInr X Y δ dY' h1).toBallChart
    (orientedBallChart Z).toBallChart boundaryAttachment.1.toHomeomorph)
    (Subtype.ext ?_)).trans
    (boundary_eq (factorChartInr X Y δ dY' h1).toBallChart (orientedBallChart Z).toBallChart
      boundaryAttachment.1.toHomeomorph ζ)
  change inr (orientedBallChart X).toBallChart δ.toBallChart boundaryAttachment.1.toHomeomorph
      ⟨(dY'.boundaryMap ζ : Y.Carrier), hmem⟩ =
    (factorChartInr X Y δ dY' h1).toBallChart.chart ζ
  rw [show (factorChartInr X Y δ dY' h1).toBallChart.chart ζ =
      inr (orientedBallChart X).toBallChart δ.toBallChart boundaryAttachment.1.toHomeomorph
        ⟨dY'.chart (ζ : E3), hx⟩ from hfζ]
  exact congrArg (inr (orientedBallChart X).toBallChart δ.toBallChart
    boundaryAttachment.1.toHomeomorph) (Subtype.ext rfl)

private def invMapFun (X Y Z : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold) (h1 : disjointInr Y δ dY') :
    dY'.Punctured ⊕ (orientedBallChart Z).toBallChart.Punctured →
      leftQuot X Y Z δ dY' h1 :=
  Sum.elim (fun y => xPartMap X Y Z δ dY' h1 y)
    (fun z => inr (factorChartInr X Y δ dY' h1).toBallChart (orientedBallChart Z).toBallChart
      boundaryAttachment.1.toHomeomorph z)

private theorem invMapFun_rel (X Y Z : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold) (h1 : disjointInr Y δ dY')
    (u v : dY'.Punctured ⊕ (orientedBallChart Z).toBallChart.Punctured)
    (h : adjunctionRel dY'.toBallChart.boundaryMap
      ((orientedBallChart Z).toBallChart.boundaryMap ∘ boundaryAttachment.1.toHomeomorph) u v) :
    invMapFun X Y Z δ dY' h1 u = invMapFun X Y Z δ dY' h1 v := by
  obtain ⟨ζ, ⟨hu, hv⟩ | ⟨hv, hu⟩⟩ := h
  · rw [hu, hv]
    simp only [invMapFun, Sum.elim_inl, Sum.elim_inr, Function.comp_apply]
    exact xPartMap_boundary X Y Z δ dY' h1 ζ
  · rw [hv, hu]
    simp only [invMapFun, Sum.elim_inl, Sum.elim_inr, Function.comp_apply]
    exact (xPartMap_boundary X Y Z δ dY' h1 ζ).symm

private def invMap (X Y Z : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold) (h1 : disjointInr Y δ dY') :
    (rightSum Y Z dY').Carrier → leftQuot X Y Z δ dY' h1 :=
  Quot.lift (invMapFun X Y Z δ dY' h1) (invMapFun_rel X Y Z δ dY' h1)

private theorem invMap_inl (X Y Z : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold) (h1 : disjointInr Y δ dY')
    (y : dY'.Punctured) :
    invMap X Y Z δ dY' h1 (inl dY'.toBallChart (orientedBallChart Z).toBallChart
      boundaryAttachment.1.toHomeomorph y) = xPartMap X Y Z δ dY' h1 y := rfl

private def flattenInvFun (X Y Z : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold) (h1 : disjointInr Y δ dY')
    (h2 : disjointInl Y δ dY') :
    (orientedBallChart X).toBallChart.Punctured ⊕
        (factorChartInl Y Z dY' δ h2).toBallChart.Punctured →
      leftQuot X Y Z δ dY' h1 :=
  Sum.elim (fun x => inl (factorChartInr X Y δ dY' h1).toBallChart
      (orientedBallChart Z).toBallChart boundaryAttachment.1.toHomeomorph
      ⟨inl (orientedBallChart X).toBallChart δ.toBallChart
        boundaryAttachment.1.toHomeomorph x,
        inl_mem_factorChartInr_punctured X Y δ dY' h1 h2⟩)
    (fun q => invMap X Y Z δ dY' h1 (q : (rightSum Y Z dY').Carrier))

private theorem flattenInvFun_rel (X Y Z : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold) (h1 : disjointInr Y δ dY')
    (h2 : disjointInl Y δ dY')
    (u v : (orientedBallChart X).toBallChart.Punctured ⊕
        (factorChartInl Y Z dY' δ h2).toBallChart.Punctured)
    (h : adjunctionRel (orientedBallChart X).toBallChart.boundaryMap
      ((factorChartInl Y Z dY' δ h2).toBallChart.boundaryMap ∘
        boundaryAttachment.1.toHomeomorph) u v) :
    flattenInvFun X Y Z δ dY' h1 h2 u = flattenInvFun X Y Z δ dY' h1 h2 v := by
  obtain ⟨ζ, ⟨hu, hv⟩ | ⟨hv, hu⟩⟩ := h
  · rw [hu, hv]
    simp only [flattenInvFun, Sum.elim_inl, Sum.elim_inr, Function.comp_apply]
    obtain ⟨hx, hgx⟩ := factorChartInl_spec Y Z dY' δ h2
      (sphere_one_subset_closedBall_two (boundaryAttachment.1.toHomeomorph ζ).2)
    have hmem : δ.chart (boundaryAttachment.1.toHomeomorph ζ) ∉ δ.chart '' ball (0 : E3) 1 :=
      chart_sphere_not_mem_chart_ball δ.toBallChart (boundaryAttachment.1.toHomeomorph ζ).2
    have hq : ((factorChartInl Y Z dY' δ h2).toBallChart.boundaryMap
        (boundaryAttachment.1.toHomeomorph ζ) : (rightSum Y Z dY').Carrier) =
        inl dY'.toBallChart (orientedBallChart Z).toBallChart
          boundaryAttachment.1.toHomeomorph
          ⟨δ.chart (boundaryAttachment.1.toHomeomorph ζ), hx⟩ := hgx
    rw [hq, invMap_inl X Y Z δ dY' h1
      ⟨δ.chart (boundaryAttachment.1.toHomeomorph ζ), hx⟩,
      xPartMap_of_mem X Y Z δ dY' h1 hmem, xPartLeft]
    refine congrArg (inl (factorChartInr X Y δ dY' h1).toBallChart
      (orientedBallChart Z).toBallChart boundaryAttachment.1.toHomeomorph)
      (Subtype.ext ?_)
    exact boundary_eq (orientedBallChart X).toBallChart δ.toBallChart
      boundaryAttachment.1.toHomeomorph ζ
  · rw [hv, hu]
    simp only [flattenInvFun, Sum.elim_inl, Sum.elim_inr, Function.comp_apply]
    obtain ⟨hx, hgx⟩ := factorChartInl_spec Y Z dY' δ h2
      (sphere_one_subset_closedBall_two (boundaryAttachment.1.toHomeomorph ζ).2)
    have hmem : δ.chart (boundaryAttachment.1.toHomeomorph ζ) ∉ δ.chart '' ball (0 : E3) 1 :=
      chart_sphere_not_mem_chart_ball δ.toBallChart (boundaryAttachment.1.toHomeomorph ζ).2
    have hq : ((factorChartInl Y Z dY' δ h2).toBallChart.boundaryMap
        (boundaryAttachment.1.toHomeomorph ζ) : (rightSum Y Z dY').Carrier) =
        inl dY'.toBallChart (orientedBallChart Z).toBallChart
          boundaryAttachment.1.toHomeomorph
          ⟨δ.chart (boundaryAttachment.1.toHomeomorph ζ), hx⟩ := hgx
    rw [hq, invMap_inl X Y Z δ dY' h1
      ⟨δ.chart (boundaryAttachment.1.toHomeomorph ζ), hx⟩,
      xPartMap_of_mem X Y Z δ dY' h1 hmem, xPartLeft]
    refine (congrArg (inl (factorChartInr X Y δ dY' h1).toBallChart
      (orientedBallChart Z).toBallChart boundaryAttachment.1.toHomeomorph)
      (Subtype.ext ?_)).symm
    exact boundary_eq (orientedBallChart X).toBallChart δ.toBallChart
      boundaryAttachment.1.toHomeomorph ζ

private def flattenInv (X Y Z : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold) (h1 : disjointInr Y δ dY')
    (h2 : disjointInl Y δ dY') :
    rightQuot X Y Z δ dY' h2 → leftQuot X Y Z δ dY' h1 :=
  Quot.lift (flattenInvFun X Y Z δ dY' h1 h2) (flattenInvFun_rel X Y Z δ dY' h1 h2)

private theorem flattenInv_inl (X Y Z : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold) (h1 : disjointInr Y δ dY')
    (h2 : disjointInl Y δ dY') (x : (orientedBallChart X).toBallChart.Punctured) :
    flattenInv X Y Z δ dY' h1 h2
      (inl (orientedBallChart X).toBallChart (factorChartInl Y Z dY' δ h2).toBallChart
        boundaryAttachment.1.toHomeomorph x) =
      inl (factorChartInr X Y δ dY' h1).toBallChart (orientedBallChart Z).toBallChart
        boundaryAttachment.1.toHomeomorph
        ⟨inl (orientedBallChart X).toBallChart δ.toBallChart
          boundaryAttachment.1.toHomeomorph x,
          inl_mem_factorChartInr_punctured X Y δ dY' h1 h2⟩ := rfl

private theorem flattenInv_inr (X Y Z : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold) (h1 : disjointInr Y δ dY')
    (h2 : disjointInl Y δ dY')
    (q : (factorChartInl Y Z dY' δ h2).toBallChart.Punctured) :
    flattenInv X Y Z δ dY' h1 h2
      (inr (orientedBallChart X).toBallChart (factorChartInl Y Z dY' δ h2).toBallChart
        boundaryAttachment.1.toHomeomorph q) =
      invMap X Y Z δ dY' h1 (q : (rightSum Y Z dY').Carrier) := rfl

private theorem invMap_inr (X Y Z : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold) (h1 : disjointInr Y δ dY')
    (z : (orientedBallChart Z).toBallChart.Punctured) :
    invMap X Y Z δ dY' h1 (inr dY'.toBallChart (orientedBallChart Z).toBallChart
      boundaryAttachment.1.toHomeomorph z) =
      inr (factorChartInr X Y δ dY' h1).toBallChart (orientedBallChart Z).toBallChart
        boundaryAttachment.1.toHomeomorph z := rfl

private theorem flattenInv_flattenMap (X Y Z : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold) (h1 : disjointInr Y δ dY')
    (h2 : disjointInl Y δ dY') (z : leftQuot X Y Z δ dY' h1) :
    flattenInv X Y Z δ dY' h1 h2 (flattenMap X Y Z δ dY' h1 h2 z) = z := by
  induction z using Quot.induction_on with
  | _ s =>
    rcases s with p | z
    · obtain ⟨x, hx⟩ | ⟨y, hy⟩ :=
        jointly_surjective (orientedBallChart X).toBallChart δ.toBallChart
          boundaryAttachment.1.toHomeomorph (p : (leftSum X Y δ).Carrier)
      · obtain rfl : p = ⟨inl (orientedBallChart X).toBallChart δ.toBallChart
            boundaryAttachment.1.toHomeomorph x,
            inl_mem_factorChartInr_punctured X Y δ dY' h1 h2⟩ := (Subtype.ext hx).symm
        change flattenInv X Y Z δ dY' h1 h2
          (flattenMap X Y Z δ dY' h1 h2
            (inl (factorChartInr X Y δ dY' h1).toBallChart
              (orientedBallChart Z).toBallChart boundaryAttachment.1.toHomeomorph
              ⟨inl (orientedBallChart X).toBallChart δ.toBallChart
                boundaryAttachment.1.toHomeomorph x,
                inl_mem_factorChartInr_punctured X Y δ dY' h1 h2⟩)) =
          inl (factorChartInr X Y δ dY' h1).toBallChart (orientedBallChart Z).toBallChart
            boundaryAttachment.1.toHomeomorph
            ⟨inl (orientedBallChart X).toBallChart δ.toBallChart
              boundaryAttachment.1.toHomeomorph x,
              inl_mem_factorChartInr_punctured X Y δ dY' h1 h2⟩
        rw [flattenMap_inl_inl, flattenInv_inl]
      · have hy' : (y : Y.Carrier) ∉ dY'.chart '' ball (0 : E3) 1 := by
          intro hmem
          obtain ⟨w, hw, hwe⟩ := hmem
          obtain ⟨hw', hfw⟩ := factorChartInr_spec X Y δ dY' h1
            (ball_one_subset_closedBall_two hw)
          refine p.2 ⟨w, hw, ?_⟩
          exact hfw.trans ((congrArg (inr (orientedBallChart X).toBallChart δ.toBallChart
            boundaryAttachment.1.toHomeomorph) (Subtype.ext hwe)).trans hy)
        have hy_mem : inr (orientedBallChart X).toBallChart δ.toBallChart
            boundaryAttachment.1.toHomeomorph y
            ∉ (factorChartInr X Y δ dY' h1).toBallChart.chart '' ball (0 : E3) 1 :=
          inr_mem_factorChartInr_punctured X Y δ dY' h1 hy'
        have hpt : p = ⟨inr (orientedBallChart X).toBallChart δ.toBallChart
            boundaryAttachment.1.toHomeomorph y, hy_mem⟩ := (Subtype.ext hy).symm
        rw [show Quot.mk (adjunctionRel (factorChartInr X Y δ dY' h1).toBallChart.boundaryMap
              ((orientedBallChart Z).toBallChart.boundaryMap ∘ boundaryAttachment.1.toHomeomorph))
              (Sum.inl p) =
            Quot.mk (adjunctionRel (factorChartInr X Y δ dY' h1).toBallChart.boundaryMap
              ((orientedBallChart Z).toBallChart.boundaryMap ∘ boundaryAttachment.1.toHomeomorph))
              (Sum.inl ⟨inr (orientedBallChart X).toBallChart δ.toBallChart
                boundaryAttachment.1.toHomeomorph y, hy_mem⟩) from
          congrArg (Quot.mk _) (congrArg Sum.inl hpt)]
        change flattenInv X Y Z δ dY' h1 h2
          (flattenMap X Y Z δ dY' h1 h2
            (inl (factorChartInr X Y δ dY' h1).toBallChart
              (orientedBallChart Z).toBallChart boundaryAttachment.1.toHomeomorph
              ⟨inr (orientedBallChart X).toBallChart δ.toBallChart
                boundaryAttachment.1.toHomeomorph y, hy_mem⟩)) =
          inl (factorChartInr X Y δ dY' h1).toBallChart (orientedBallChart Z).toBallChart
            boundaryAttachment.1.toHomeomorph
            ⟨inr (orientedBallChart X).toBallChart δ.toBallChart
              boundaryAttachment.1.toHomeomorph y, hy_mem⟩
        rw [flattenMap_inl_inr X Y Z δ dY' h1 h2 y hy', flattenInv_inr, invMap_inl,
          xPartMap_of_mem X Y Z δ dY' h1 y.2, xPartLeft]
    · change flattenInv X Y Z δ dY' h1 h2
        (flattenMap X Y Z δ dY' h1 h2
          (inr (factorChartInr X Y δ dY' h1).toBallChart
            (orientedBallChart Z).toBallChart boundaryAttachment.1.toHomeomorph z)) =
        inr (factorChartInr X Y δ dY' h1).toBallChart (orientedBallChart Z).toBallChart
          boundaryAttachment.1.toHomeomorph z
      rw [flattenMap_inr, flattenInv_inr, invMap_inr]

private theorem flattenMap_flattenInv (X Y Z : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold) (h1 : disjointInr Y δ dY')
    (h2 : disjointInl Y δ dY') (w : rightQuot X Y Z δ dY' h2) :
    flattenMap X Y Z δ dY' h1 h2 (flattenInv X Y Z δ dY' h1 h2 w) = w := by
  induction w using Quot.induction_on with
  | _ s =>
    rcases s with x | q
    · change flattenMap X Y Z δ dY' h1 h2
        (flattenInv X Y Z δ dY' h1 h2
          (inl (orientedBallChart X).toBallChart (factorChartInl Y Z dY' δ h2).toBallChart
            boundaryAttachment.1.toHomeomorph x)) =
        inl (orientedBallChart X).toBallChart (factorChartInl Y Z dY' δ h2).toBallChart
          boundaryAttachment.1.toHomeomorph x
      rw [flattenInv_inl, flattenMap_inl_inl]
    · change flattenMap X Y Z δ dY' h1 h2
        (flattenInv X Y Z δ dY' h1 h2
          (inr (orientedBallChart X).toBallChart (factorChartInl Y Z dY' δ h2).toBallChart
            boundaryAttachment.1.toHomeomorph q)) =
        inr (orientedBallChart X).toBallChart (factorChartInl Y Z dY' δ h2).toBallChart
          boundaryAttachment.1.toHomeomorph q
      rw [flattenInv_inr]
      obtain ⟨y, hy⟩ | ⟨z, hz⟩ :=
        jointly_surjective dY'.toBallChart (orientedBallChart Z).toBallChart
          boundaryAttachment.1.toHomeomorph (q : (rightSum Y Z dY').Carrier)
      · have hyδ : (y : Y.Carrier) ∉ δ.chart '' ball (0 : E3) 1 := by
          intro hmem
          obtain ⟨w, hw, hwe⟩ := hmem
          obtain ⟨hw', hgw⟩ := factorChartInl_spec Y Z dY' δ h2
            (ball_one_subset_closedBall_two hw)
          refine q.2 ⟨w, hw, ?_⟩
          exact hgw.trans ((congrArg (inl dY'.toBallChart (orientedBallChart Z).toBallChart
            boundaryAttachment.1.toHomeomorph) (Subtype.ext hwe)).trans hy)
        have hy_mem : inl dY'.toBallChart (orientedBallChart Z).toBallChart
            boundaryAttachment.1.toHomeomorph y
            ∉ (factorChartInl Y Z dY' δ h2).toBallChart.chart '' ball (0 : E3) 1 :=
          inl_mem_factorChartInl_punctured Y Z δ dY' h2 hyδ
        have hq : q = ⟨inl dY'.toBallChart (orientedBallChart Z).toBallChart
            boundaryAttachment.1.toHomeomorph y, hy_mem⟩ := Subtype.ext hy.symm
        rw [show (q : (rightSum Y Z dY').Carrier) = inl dY'.toBallChart
            (orientedBallChart Z).toBallChart boundaryAttachment.1.toHomeomorph y from hy.symm]
        rw [invMap_inl X Y Z δ dY' h1 y, xPartMap_of_mem X Y Z δ dY' h1 hyδ, xPartLeft]
        rw [flattenMap_inl_inr X Y Z δ dY' h1 h2 ⟨y, hyδ⟩ y.2]
        refine (congrArg (inr (orientedBallChart X).toBallChart
          (factorChartInl Y Z dY' δ h2).toBallChart boundaryAttachment.1.toHomeomorph)
          (Subtype.ext ?_)).trans (congrArg (inr (orientedBallChart X).toBallChart
            (factorChartInl Y Z dY' δ h2).toBallChart boundaryAttachment.1.toHomeomorph)
            hq.symm)
        exact congrArg (inl dY'.toBallChart (orientedBallChart Z).toBallChart
          boundaryAttachment.1.toHomeomorph) (Subtype.ext rfl)
      · have hq : q = ⟨inr dY'.toBallChart (orientedBallChart Z).toBallChart
            boundaryAttachment.1.toHomeomorph z,
            inr_mem_factorChartInl_punctured Y Z δ dY' h1 h2 (z := z)⟩ :=
          Subtype.ext hz.symm
        rw [show (q : (rightSum Y Z dY').Carrier) = inr dY'.toBallChart
            (orientedBallChart Z).toBallChart boundaryAttachment.1.toHomeomorph z from hz.symm]
        rw [invMap_inr, flattenMap_inr]
        exact congrArg (inr (orientedBallChart X).toBallChart
          (factorChartInl Y Z dY' δ h2).toBallChart boundaryAttachment.1.toHomeomorph) hq.symm

def ConnectedSumFlatteningIsoCanonical : Prop :=
  ∀ (X Y Z : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold)
    (h1 : ∀ x ∈ closedBall (0 : E3) 2, dY'.chart x ∉ δ.chart '' closedBall (0 : E3) 1)
    (h2 : ∀ x ∈ closedBall (0 : E3) 2, δ.chart x ∉ dY'.chart '' closedBall (0 : E3) 1),
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (smoothConnectedSum (leftSum X Y δ) Z (factorChartInr X Y δ dY' h1)
        (orientedBallChart Z) boundaryAttachment
        ).toConnectedClosedOrientedManifold.toClosedOrientedManifold
      (smoothConnectedSum X (rightSum Y Z dY') (orientedBallChart X)
        (factorChartInl Y Z dY' δ h2) boundaryAttachment
        ).toConnectedClosedOrientedManifold.toClosedOrientedManifold)

theorem connectedSumAssociative_of_flatteningIsoCanonical
    (h : ConnectedSumFlatteningIsoCanonical.{u}) : connectedSumAssociative.{u} := by
  intro X Y Z
  obtain ⟨dY', δ, h1, h2⟩ := exists_disjointOrientedBallChart_closedBall (orientedBallChart Y)
  let A := (smoothConnectedSum X Y (orientedBallChart X) δ boundaryAttachment
    ).toConnectedClosedOrientedManifold
  let B := (smoothConnectedSum Y Z dY' (orientedBallChart Z) boundaryAttachment
    ).toConnectedClosedOrientedManifold
  let f : OrientedBallChart A.toClosedOrientedManifold := factorChartInr X Y δ dY' h1
  let g : OrientedBallChart B.toClosedOrientedManifold := factorChartInl Y Z dY' δ h2
  obtain ⟨Ψd, hΨdo, hΨd⟩ := selfTransport_holds (orientedBallChart Y) δ
  obtain ⟨hAB⟩ := csTransport_diffeomorph_preservesOrientation (orientedBallChart X)
    (orientedBallChart X) (orientedBallChart Y) δ boundaryAttachment
    (Diffeomorph.refl (𝓡 3) X.Carrier ∞) Ψd (fun _ _ => rfl)
    (fun x hx => by simpa only [Diffeomorph.coe_toHomeomorph] using hΨd x hx)
    (Diffeomorph.preservesOrientation_refl X.orientation)
  obtain ⟨Ψd', hΨd'o, hΨd'⟩ := selfTransport_holds (orientedBallChart Y) dY'
  obtain ⟨hBQ⟩ := csTransport_diffeomorph_preservesOrientation (orientedBallChart Y) dY'
    (orientedBallChart Z) (orientedBallChart Z) boundaryAttachment Ψd'
    (Diffeomorph.refl (𝓡 3) Z.Carrier ∞)
    (fun x hx => by simpa only [Diffeomorph.coe_toHomeomorph] using hΨd' x hx)
    (fun _ _ => rfl) hΨd'o
  obtain ⟨Φ₁, hΦ₁o⟩ := hAB
  obtain ⟨Φ₂, hΦ₂o⟩ := hBQ
  obtain ⟨step1⟩ := nonempty_orientedDiffeomorph_smoothConnectedSum_of_orientedDiffeomorph
    Φ₁ hΦ₁o (orientedBallChart Z) boundaryAttachment
  obtain ⟨step2⟩ := nonempty_orientedDiffeomorph_smoothConnectedSum_of_leftChart
    (orientedBallChart A) f (orientedBallChart Z) boundaryAttachment
  obtain ⟨step3⟩ := h X Y Z δ dY' h1 h2
  obtain ⟨step4⟩ := nonempty_orientedDiffeomorph_smoothConnectedSum_of_rightChart
    (orientedBallChart X) g (orientedBallChart B) boundaryAttachment
  obtain ⟨step5⟩ := nonempty_orientedDiffeomorph_smoothConnectedSum_of_orientedDiffeomorph_right
    Φ₂.symm (Diffeomorph.preservesOrientation_symm hΦ₂o) (orientedBallChart X)
    boundaryAttachment
  exact ⟨step1.trans (step2.trans (step3.trans (step4.trans step5)))⟩

theorem connectedSumFlatteningIsoCanonical_of_flatteningIso
    (h : ConnectedSumFlatteningIso.{u}) : ConnectedSumFlatteningIsoCanonical.{u} :=
  fun X Y Z δ dY' h1 h2 =>
    h X Y Z δ dY' (factorChartInr X Y δ dY' h1) (factorChartInl Y Z dY' δ h2)

def connectedSumFlatteningMap (X Y Z : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold)
    (h1 : ∀ x ∈ closedBall (0 : E3) 2, dY'.chart x ∉ δ.chart '' closedBall (0 : E3) 1)
    (h2 : ∀ x ∈ closedBall (0 : E3) 2, δ.chart x ∉ dY'.chart '' closedBall (0 : E3) 1) :
    (smoothConnectedSum (leftSum X Y δ) Z (factorChartInr X Y δ dY' h1)
        (orientedBallChart Z) boundaryAttachment
        ).toConnectedClosedOrientedManifold.Carrier →
      (smoothConnectedSum X (rightSum Y Z dY') (orientedBallChart X)
        (factorChartInl Y Z dY' δ h2) boundaryAttachment
        ).toConnectedClosedOrientedManifold.Carrier :=
  flattenMap X Y Z δ dY' h1 h2

theorem connectedSumFlatteningMap_bijective (X Y Z : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold)
    (h1 : ∀ x ∈ closedBall (0 : E3) 2, dY'.chart x ∉ δ.chart '' closedBall (0 : E3) 1)
    (h2 : ∀ x ∈ closedBall (0 : E3) 2, δ.chart x ∉ dY'.chart '' closedBall (0 : E3) 1) :
    Function.Bijective (connectedSumFlatteningMap X Y Z δ dY' h1 h2) := by
  refine ⟨fun a b hab => ?_, fun b => ⟨flattenInv X Y Z δ dY' h1 h2 b, ?_⟩⟩
  · have hab' : flattenMap X Y Z δ dY' h1 h2 a = flattenMap X Y Z δ dY' h1 h2 b := hab
    rw [← flattenInv_flattenMap X Y Z δ dY' h1 h2 a, hab',
      flattenInv_flattenMap X Y Z δ dY' h1 h2 b]
  · exact flattenMap_flattenInv X Y Z δ dY' h1 h2 b
private abbrev fChart (X Y : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold) (h1 : disjointInr Y δ dY') :
    BallChart 3 (𝓡 3) (leftSum X Y δ).Carrier :=
  (factorChartInr X Y δ dY' h1).toBallChart

private abbrev gChart (Y Z : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold) (h2 : disjointInl Y δ dY') :
    BallChart 3 (𝓡 3) (rightSum Y Z dY').Carrier :=
  (factorChartInl Y Z dY' δ h2).toBallChart

private theorem inl_notMem_fChart_closedBall (X Y : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold) (h1 : disjointInr Y δ dY')
    (h2 : disjointInl Y δ dY') {p : (orientedBallChart X).toBallChart.Punctured} :
    inl (orientedBallChart X).toBallChart δ.toBallChart boundaryAttachment.1.toHomeomorph p
      ∉ (fChart X Y δ dY' h1).chart '' closedBall (0 : E3) 1 := by
  intro hmem
  obtain ⟨w, hw, hweq⟩ := hmem
  obtain ⟨hw', hfw⟩ := factorChartInr_spec X Y δ dY' h1
    (Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2) hw)
  rw [hfw] at hweq
  obtain ⟨ζ, -, hζ⟩ := (inl_eq_inr_iff (orientedBallChart X).toBallChart δ.toBallChart
    boundaryAttachment.1.toHomeomorph p ⟨dY'.chart w, hw'⟩).mp hweq.symm
  refine h2 (boundaryAttachment.1.toHomeomorph ζ)
    (sphere_one_subset_closedBall_two (boundaryAttachment.1.toHomeomorph ζ).2) ?_
  exact ⟨w, hw, (congrArg Subtype.val hζ).symm⟩

private theorem inr_interiorToPunctured_notMem_fChart_closedBall
    (X Y : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold) (h1 : disjointInr Y δ dY')
    {y : δ.interior} (hy : (y : Y.Carrier) ∉ dY'.chart '' closedBall (0 : E3) 1) :
    inr (orientedBallChart X).toBallChart δ.toBallChart boundaryAttachment.1.toHomeomorph
      (δ.interiorToPunctured y) ∉ (fChart X Y δ dY' h1).chart '' closedBall (0 : E3) 1 := by
  intro hmem
  obtain ⟨w, hw, hweq⟩ := hmem
  obtain ⟨hw', hfw⟩ := factorChartInr_spec X Y δ dY' h1
    (Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2) hw)
  rw [hfw] at hweq
  have hinj : (⟨dY'.chart w, hw'⟩ : δ.Punctured) = δ.interiorToPunctured y :=
    inr_injective (orientedBallChart X).toBallChart δ.toBallChart
      boundaryAttachment.1.toHomeomorph hweq
  exact hy ⟨w, hw, congrArg Subtype.val hinj⟩

private theorem inr_interiorToPunctured_notMem_gChart_closedBall
    (Y Z : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold) (h1 : disjointInr Y δ dY')
    (h2 : disjointInl Y δ dY')
    {z : (orientedBallChart Z).toBallChart.Punctured} :
    inr dY'.toBallChart (orientedBallChart Z).toBallChart boundaryAttachment.1.toHomeomorph z
      ∉ (gChart Y Z δ dY' h2).chart '' closedBall (0 : E3) 1 := by
  intro hmem
  obtain ⟨w, hw, hweq⟩ := hmem
  obtain ⟨hw', hgw⟩ := factorChartInl_spec Y Z dY' δ h2
    (Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2) hw)
  rw [hgw] at hweq
  obtain ⟨ζ, hζ, -⟩ := (inl_eq_inr_iff dY'.toBallChart (orientedBallChart Z).toBallChart
    boundaryAttachment.1.toHomeomorph ⟨δ.chart w, hw'⟩ z).mp hweq
  exact h1 ζ (sphere_one_subset_closedBall_two ζ.2) ⟨w, hw, (congrArg Subtype.val hζ).symm⟩

private theorem inr_notMem_fChart_closedBall_of_notMem_chart
    (X Y : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold) (h1 : disjointInr Y δ dY')
    {y : δ.Punctured} (hy : (y : Y.Carrier) ∉ dY'.chart '' closedBall (0 : E3) 1) :
    inr (orientedBallChart X).toBallChart δ.toBallChart boundaryAttachment.1.toHomeomorph y
      ∉ (fChart X Y δ dY' h1).chart '' closedBall (0 : E3) 1 := by
  intro hmem
  obtain ⟨w, hw, hweq⟩ := hmem
  obtain ⟨hw', hfw⟩ := factorChartInr_spec X Y δ dY' h1
    (Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2) hw)
  rw [hfw] at hweq
  have hinj : (⟨dY'.chart w, hw'⟩ : δ.Punctured) = y :=
    inr_injective (orientedBallChart X).toBallChart δ.toBallChart
      boundaryAttachment.1.toHomeomorph hweq
  exact hy ⟨w, hw, congrArg Subtype.val hinj⟩

private theorem inl_notMem_gChart_closedBall_of_notMem_chart
    (Y Z : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold) (h2 : disjointInl Y δ dY')
    {q : dY'.Punctured} (hq : (q : Y.Carrier) ∉ δ.chart '' closedBall (0 : E3) 1) :
    inl dY'.toBallChart (orientedBallChart Z).toBallChart boundaryAttachment.1.toHomeomorph q
      ∉ (gChart Y Z δ dY' h2).chart '' closedBall (0 : E3) 1 := by
  intro hmem
  obtain ⟨w, hw, hweq⟩ := hmem
  obtain ⟨hw', hgw⟩ := factorChartInl_spec Y Z dY' δ h2
    (Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2) hw)
  rw [hgw] at hweq
  have hinj : (⟨δ.chart w, hw'⟩ : dY'.Punctured) = q :=
    inl_injective dY'.toBallChart (orientedBallChart Z).toBallChart
      boundaryAttachment.1.toHomeomorph hweq
  exact hq ⟨w, hw, congrArg Subtype.val hinj⟩

private theorem ball_sphere_norm {z : E3} (hz : z ∈ sphere (0 : E3) 1) : ‖z‖ = 1 := by
  simpa [mem_sphere, dist_zero_right] using hz

private theorem chart_smul_sphere_notMem_chart_ball {M : Type*} [TopologicalSpace M]
    [ChartedSpace E3 M] (c : BallChart 3 (𝓡 3) M) {z : E3} (hz : z ∈ sphere (0 : E3) 1)
    {r : ℝ} (hr1 : 1 ≤ r) (hr2 : r ≤ 2) : c.chart (r • z) ∉ c.chart '' ball (0 : E3) 1 := by
  rintro ⟨w, hw, hweq⟩
  have hsrc : r • z ∈ c.chart.source := by
    refine mem_chart_source_of_norm_le_two c ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_trans zero_le_one hr1),
      ball_sphere_norm hz, mul_one]
    exact hr2
  have hzw : w = r • z :=
    c.chart.toPartialEquiv.injOn (c.ball_subset_source hw) hsrc hweq
  have hw1 : ‖w‖ < 1 := by simpa [mem_ball, dist_zero_right] using hw
  rw [hzw, norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_trans zero_le_one hr1),
    ball_sphere_norm hz, mul_one] at hw1
  linarith

private theorem norm_radial_of_mem_sphere {z : E3} (hz : z ∈ sphere (0 : E3) 1) {r : ℝ}
    (hr0 : 0 ≤ r) : ‖r • z‖ = r := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr0, ball_sphere_norm hz, mul_one]

private def chartClosedBallCompl (Y : ConnectedClosedOrientedManifold.{u} 3)
    (dY' : OrientedBallChart Y.toClosedOrientedManifold) : TopologicalSpace.Opens Y.Carrier :=
  ⟨(dY'.chart '' closedBall (0 : E3) 1)ᶜ, dY'.isCompact_closedBall_image.isClosed.isOpen_compl⟩

private def goodInterior (Y : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold) : TopologicalSpace.Opens δ.interior :=
  ⟨{u : δ.interior | (u : Y.Carrier) ∈ (chartClosedBallCompl Y dY' : Set Y.Carrier)},
    (chartClosedBallCompl Y dY').2.preimage continuous_subtype_val⟩

private def yPartInterior (Y Z : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold) (h2 : disjointInl Y δ dY')
    (y : δ.interior) (hy : (y : Y.Carrier) ∉ dY'.chart '' closedBall (0 : E3) 1) :
    (gChart Y Z δ dY' h2).interior :=
  let qI : dY'.interior :=
    ⟨δ.interiorToPunctured y, show ((δ.interiorToPunctured y : δ.Punctured) : Y.Carrier)
      ∉ dY'.chart '' closedBall (0 : E3) 1 from hy⟩
  let qP : dY'.Punctured :=
    ⟨δ.interiorToPunctured y, fun h => hy (show ((δ.interiorToPunctured y : δ.Punctured)
        : Y.Carrier) ∈ dY'.chart '' closedBall (0 : E3) 1
        from image_mono Metric.ball_subset_closedBall h)⟩
  ⟨interiorLeft dY'.toBallChart (orientedBallChart Z).toBallChart boundaryAttachment.1 qI,
    inl_notMem_gChart_closedBall_of_notMem_chart Y Z δ dY' h2 (q := qP) y.2⟩

private theorem leftMap_interiorLeft (X Y Z : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold) (h2 : disjointInl Y δ dY')
    (x : (orientedBallChart X).toBallChart.interior) :
    leftMap X Y Z δ dY' h2
        (interiorLeft (orientedBallChart X).toBallChart δ.toBallChart
          boundaryAttachment.1 x) =
      interiorLeft (orientedBallChart X).toBallChart (gChart Y Z δ dY' h2) boundaryAttachment.1 x :=
  rfl

private theorem leftMap_interiorRight (X Y Z : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold) (h2 : disjointInl Y δ dY')
    (y : δ.interior) (hy : (y : Y.Carrier) ∉ dY'.chart '' closedBall (0 : E3) 1) :
    leftMap X Y Z δ dY' h2
        (interiorRight (orientedBallChart X).toBallChart δ.toBallChart
          boundaryAttachment.1 y) =
      interiorRight (orientedBallChart X).toBallChart (gChart Y Z δ dY' h2) boundaryAttachment.1
        (yPartInterior Y Z δ dY' h2 y hy) := by
  have hmem : ((δ.interiorToPunctured y : δ.Punctured) : Y.Carrier)
      ∉ dY'.chart '' ball (0 : E3) 1 := fun h =>
    hy (image_mono Metric.ball_subset_closedBall h)
  rw [show leftMap X Y Z δ dY' h2
      (interiorRight (orientedBallChart X).toBallChart δ.toBallChart boundaryAttachment.1 y)
      = yPartMap X Y Z δ dY' h2 (δ.interiorToPunctured y) from rfl]
  rw [yPartMap_of_mem X Y Z δ dY' h2 hmem]
  rw [yPartRight]
  refine congrArg (inr (orientedBallChart X).toBallChart (gChart Y Z δ dY' h2)
    boundaryAttachment.1.toHomeomorph) (Subtype.ext ?_)
  rw [yPartInterior]
  exact congrArg (inl dY'.toBallChart (orientedBallChart Z).toBallChart
    boundaryAttachment.1.toHomeomorph) (Subtype.ext rfl)

private theorem leftMap_collarMap (X Y Z : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold) (h2 : disjointInl Y δ dY')
    (q : ConnectedSumQuotient.CollarDomain) :
    leftMap X Y Z δ dY' h2
        (collarMap (orientedBallChart X).toBallChart δ.toBallChart boundaryAttachment.1 q) =
      collarMap (orientedBallChart X).toBallChart (gChart Y Z δ dY' h2) boundaryAttachment.1 q := by
  rcases lt_trichotomy (q.2 : ℝ) 0 with ht | ht | ht
  · have hrad : 1 - (q.2 : ℝ) ∈ Set.Icc 1 2 := by
      have h := collar_right_radius q.2 ht.le
      exact ⟨h.1, le_trans (le_of_lt h.2) (by norm_num)⟩
    rw [collarMap_of_neg (orientedBallChart X).toBallChart δ.toBallChart
        boundaryAttachment.1 q ht,
      collarMap_of_neg (orientedBallChart X).toBallChart (gChart Y Z δ dY' h2)
        boundaryAttachment.1 q ht]
    have hmem : ((δ.radialMap (boundaryAttachment.1.toHomeomorph q.1) (1 - (q.2 : ℝ)) hrad
        : δ.Punctured) : Y.Carrier) ∉ dY'.chart '' ball (0 : E3) 1 := by
      intro h
      obtain ⟨w, hw, hwe⟩ := h
      have hx2 : (1 - (q.2 : ℝ)) ≤ 2 := hrad.2
      have hpos : (0 : ℝ) ≤ 1 - (q.2 : ℝ) := by linarith [q.2.2]
      refine h2 ((1 - (q.2 : ℝ)) • (boundaryAttachment.1.toHomeomorph q.1 : E3))
        (by
          rw [Metric.mem_closedBall, dist_zero_right,
            norm_radial_of_mem_sphere (boundaryAttachment.1.toHomeomorph q.1).2 hpos]
          exact hx2) ?_
      exact ⟨w, Metric.ball_subset_closedBall hw, hwe⟩
    change yPartMap X Y Z δ dY' h2
        (δ.radialMap (boundaryAttachment.1.toHomeomorph q.1) (1 - (q.2 : ℝ)) hrad) =
      inr (orientedBallChart X).toBallChart (gChart Y Z δ dY' h2)
        boundaryAttachment.1.toHomeomorph
        ((gChart Y Z δ dY' h2).radialMap (boundaryAttachment.1.toHomeomorph q.1)
          (1 - (q.2 : ℝ)) _)
    rw [yPartMap_of_mem X Y Z δ dY' h2 hmem, yPartRight]
    refine congrArg (inr (orientedBallChart X).toBallChart (gChart Y Z δ dY' h2)
      boundaryAttachment.1.toHomeomorph) (Subtype.ext ?_)
    have hbound : (1 - (q.2 : ℝ)) • (boundaryAttachment.1.toHomeomorph q.1 : E3)
        ∈ closedBall (0 : E3) 2 := by
      have hpos : (0 : ℝ) ≤ 1 - (q.2 : ℝ) := by linarith [q.2.2]
      rw [Metric.mem_closedBall, dist_zero_right,
        norm_radial_of_mem_sphere (boundaryAttachment.1.toHomeomorph q.1).2 hpos]
      exact hrad.2
    obtain ⟨hx', hgx⟩ := factorChartInl_spec Y Z dY' δ h2 hbound
    simp only [BallChart.radialMap]
    refine (congrArg (inl dY'.toBallChart (orientedBallChart Z).toBallChart
      boundaryAttachment.1.toHomeomorph) (Subtype.ext rfl)).trans ?_
    exact hgx.symm
  · rw [collarMap_of_nonneg (orientedBallChart X).toBallChart δ.toBallChart
        boundaryAttachment.1 q (le_of_eq ht.symm),
      collarMap_of_nonneg (orientedBallChart X).toBallChart (gChart Y Z δ dY' h2)
        boundaryAttachment.1 q (le_of_eq ht.symm)]
    exact leftMap_inl X Y Z δ dY' h2 _
  · rw [collarMap_of_nonneg (orientedBallChart X).toBallChart δ.toBallChart
        boundaryAttachment.1 q ht.le,
      collarMap_of_nonneg (orientedBallChart X).toBallChart (gChart Y Z δ dY' h2)
        boundaryAttachment.1 q ht.le]
    exact leftMap_inl X Y Z δ dY' h2 _

private theorem flattenMap_interiorLeft (X Y Z : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold) (h1 : disjointInr Y δ dY')
    (h2 : disjointInl Y δ dY') (u : (fChart X Y δ dY' h1).interior) :
    flattenMap X Y Z δ dY' h1 h2
        (interiorLeft (fChart X Y δ dY' h1) (orientedBallChart Z).toBallChart
          boundaryAttachment.1 u) =
      leftMap X Y Z δ dY' h2 (u : (leftSum X Y δ).Carrier) := rfl

private theorem flattenMap_interiorRight (X Y Z : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold) (h1 : disjointInr Y δ dY')
    (h2 : disjointInl Y δ dY') (v : (orientedBallChart Z).toBallChart.interior) :
    flattenMap X Y Z δ dY' h1 h2
        (interiorRight (fChart X Y δ dY' h1) (orientedBallChart Z).toBallChart
          boundaryAttachment.1 v) =
      interiorRight (orientedBallChart X).toBallChart (gChart Y Z δ dY' h2) boundaryAttachment.1
        ⟨inr dY'.toBallChart (orientedBallChart Z).toBallChart boundaryAttachment.1.toHomeomorph
          ((orientedBallChart Z).toBallChart.interiorToPunctured v),
          inr_interiorToPunctured_notMem_gChart_closedBall Y Z δ dY' h1 h2⟩ := rfl

private theorem collarMap_mem_gChart_interior {Y Z : ConnectedClosedOrientedManifold.{u} 3}
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold) (h1 : disjointInr Y δ dY')
    (h2 : disjointInl Y δ dY') (p : ConnectedSumQuotient.CollarDomain) :
    collarMap dY'.toBallChart (orientedBallChart Z).toBallChart boundaryAttachment.1 p
      ∈ (gChart Y Z δ dY' h2).interior := by
  by_cases ht : 0 ≤ (p.2 : ℝ)
  · rw [collarMap_of_nonneg dY'.toBallChart (orientedBallChart Z).toBallChart
      boundaryAttachment.1 p ht]
    have hr2 : 1 + (p.2 : ℝ) ≤ 2 := by
      have h := p.2.2.2
      linarith
    have hmem : (1 + (p.2 : ℝ)) • (p.1 : E3) ∈ closedBall (0 : E3) 2 := by
      rw [Metric.mem_closedBall, dist_zero_right,
        norm_radial_of_mem_sphere p.1.2 (by linarith)]
      exact hr2
    exact inl_notMem_gChart_closedBall_of_notMem_chart Y Z δ dY' h2
      (q := dY'.radialMap p.1 (1 + (p.2 : ℝ)) _) (h1 _ hmem)
  · rw [collarMap_of_neg dY'.toBallChart (orientedBallChart Z).toBallChart
      boundaryAttachment.1 p (lt_of_not_ge ht)]
    exact inr_interiorToPunctured_notMem_gChart_closedBall Y Z δ dY' h1 h2

private theorem flattenMap_collarMap (X Y Z : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold) (h1 : disjointInr Y δ dY')
    (h2 : disjointInl Y δ dY') (p : ConnectedSumQuotient.CollarDomain) :
    flattenMap X Y Z δ dY' h1 h2
        (collarMap (fChart X Y δ dY' h1) (orientedBallChart Z).toBallChart boundaryAttachment.1 p) =
      interiorRight (orientedBallChart X).toBallChart (gChart Y Z δ dY' h2) boundaryAttachment.1
        ⟨collarMap dY'.toBallChart (orientedBallChart Z).toBallChart boundaryAttachment.1 p,
          collarMap_mem_gChart_interior δ dY' h1 h2 p⟩ := by
  by_cases ht : 0 ≤ (p.2 : ℝ)
  · have hr2 : 1 + (p.2 : ℝ) ≤ 2 := by
      have h := p.2.2.2
      linarith
    have hmem : (1 + (p.2 : ℝ)) • (p.1 : E3) ∈ closedBall (0 : E3) 2 := by
      rw [Metric.mem_closedBall, dist_zero_right,
        norm_radial_of_mem_sphere p.1.2 (by linarith)]
      exact hr2
    have hR : interiorRight (orientedBallChart X).toBallChart (gChart Y Z δ dY' h2)
          boundaryAttachment.1
          ⟨collarMap dY'.toBallChart (orientedBallChart Z).toBallChart boundaryAttachment.1 p,
            collarMap_mem_gChart_interior δ dY' h1 h2 p⟩ =
        interiorRight (orientedBallChart X).toBallChart (gChart Y Z δ dY' h2)
          boundaryAttachment.1
          ⟨inl dY'.toBallChart (orientedBallChart Z).toBallChart
              boundaryAttachment.1.toHomeomorph (dY'.radialMap p.1 (1 + (p.2 : ℝ)) _),
            inl_notMem_gChart_closedBall_of_notMem_chart Y Z δ dY' h2
              (q := dY'.radialMap p.1 (1 + (p.2 : ℝ)) _) (h1 _ hmem)⟩ :=
      congrArg (interiorRight (orientedBallChart X).toBallChart (gChart Y Z δ dY' h2)
          boundaryAttachment.1)
        (Subtype.ext (collarMap_of_nonneg dY'.toBallChart (orientedBallChart Z).toBallChart
          boundaryAttachment.1 p ht))
    rw [hR, collarMap_of_nonneg (fChart X Y δ dY' h1) (orientedBallChart Z).toBallChart
      boundaryAttachment.1 p ht]
    have hr1 : 1 ≤ 1 + (p.2 : ℝ) := by linarith
    obtain ⟨hx', hfx⟩ := factorChartInr_spec X Y δ dY' h1 hmem
    have hy : dY'.chart ((1 + (p.2 : ℝ)) • (p.1 : E3)) ∉ dY'.chart '' ball (0 : E3) 1 :=
      chart_smul_sphere_notMem_chart_ball dY'.toBallChart p.1.2 hr1 hr2
    rw [show (fChart X Y δ dY' h1).radialMap p.1 (1 + (p.2 : ℝ))
          (by
            have hr := collar_left_radius p.2 ht
            exact ⟨hr.1, le_trans (le_of_lt hr.2) (by norm_num)⟩) =
        ⟨inr (orientedBallChart X).toBallChart δ.toBallChart boundaryAttachment.1.toHomeomorph
          ⟨dY'.chart ((1 + (p.2 : ℝ)) • (p.1 : E3)), hx'⟩,
          inr_mem_factorChartInr_punctured X Y δ dY' h1 hy⟩ from Subtype.ext hfx]
    change leftMap X Y Z δ dY' h2
        (inr (orientedBallChart X).toBallChart δ.toBallChart boundaryAttachment.1.toHomeomorph
          ⟨dY'.chart ((1 + (p.2 : ℝ)) • (p.1 : E3)), hx'⟩) = _
    rw [leftMap_inr X Y Z δ dY' h2
        (y := ⟨dY'.chart ((1 + (p.2 : ℝ)) • (p.1 : E3)), hx'⟩) hy,
      yPartRight]
    refine congrArg (inr (orientedBallChart X).toBallChart (gChart Y Z δ dY' h2)
      boundaryAttachment.1.toHomeomorph) (Subtype.ext ?_)
    exact congrArg (inl dY'.toBallChart (orientedBallChart Z).toBallChart
      boundaryAttachment.1.toHomeomorph) (Subtype.ext rfl)
  · have hR : interiorRight (orientedBallChart X).toBallChart (gChart Y Z δ dY' h2)
          boundaryAttachment.1
          ⟨collarMap dY'.toBallChart (orientedBallChart Z).toBallChart boundaryAttachment.1 p,
            collarMap_mem_gChart_interior δ dY' h1 h2 p⟩ =
        interiorRight (orientedBallChart X).toBallChart (gChart Y Z δ dY' h2)
          boundaryAttachment.1
          ⟨inr dY'.toBallChart (orientedBallChart Z).toBallChart
              boundaryAttachment.1.toHomeomorph
              ((orientedBallChart Z).toBallChart.radialMap
                (boundaryAttachment.1 p.1) (1 - (p.2 : ℝ)) _),
            inr_interiorToPunctured_notMem_gChart_closedBall Y Z δ dY' h1 h2⟩ :=
      congrArg (interiorRight (orientedBallChart X).toBallChart (gChart Y Z δ dY' h2)
          boundaryAttachment.1)
        (Subtype.ext (collarMap_of_neg dY'.toBallChart (orientedBallChart Z).toBallChart
          boundaryAttachment.1 p (lt_of_not_ge ht)))
    rw [hR, collarMap_of_neg (fChart X Y δ dY' h1) (orientedBallChart Z).toBallChart
      boundaryAttachment.1 p (lt_of_not_ge ht)]
    change zPartRight X Y Z δ dY' h1 h2
        ((orientedBallChart Z).toBallChart.radialMap
          (boundaryAttachment.1 p.1) (1 - (p.2 : ℝ)) _) = _
    refine congrArg (inr (orientedBallChart X).toBallChart (gChart Y Z δ dY' h2)
      boundaryAttachment.1.toHomeomorph) (Subtype.ext rfl)

section

variable (X Y Z : ConnectedClosedOrientedManifold.{u} 3)
  (δ dY' : OrientedBallChart Y.toClosedOrientedManifold)
  (h1 : disjointInr Y δ dY') (h2 : disjointInl Y δ dY')

local instance : ChartedSpace E3
    (ConnectedSumQuotient (orientedBallChart X).toBallChart δ.toBallChart
      boundaryAttachment.1.toHomeomorph) :=
  (smoothConnectedSum X Y (orientedBallChart X) δ boundaryAttachment).charts

local instance : IsManifold (𝓡 3) ∞
    (ConnectedSumQuotient (orientedBallChart X).toBallChart δ.toBallChart
      boundaryAttachment.1.toHomeomorph) :=
  (smoothConnectedSum X Y (orientedBallChart X) δ boundaryAttachment).smooth

local instance : ChartedSpace E3 (rightQuot X Y Z δ dY' h2) :=
  (smoothConnectedSum X (rightSum Y Z dY') (orientedBallChart X)
    (factorChartInl Y Z dY' δ h2) boundaryAttachment).charts

local instance : IsManifold (𝓡 3) ∞ (rightQuot X Y Z δ dY' h2) :=
  (smoothConnectedSum X (rightSum Y Z dY') (orientedBallChart X)
    (factorChartInl Y Z dY' δ h2) boundaryAttachment).smooth

local instance : ChartedSpace E3
    (ConnectedSumQuotient dY'.toBallChart (orientedBallChart Z).toBallChart
      boundaryAttachment.1.toHomeomorph) :=
  (smoothConnectedSum Y Z dY' (orientedBallChart Z) boundaryAttachment).charts

local instance : IsManifold (𝓡 3) ∞
    (ConnectedSumQuotient dY'.toBallChart (orientedBallChart Z).toBallChart
      boundaryAttachment.1.toHomeomorph) :=
  (smoothConnectedSum Y Z dY' (orientedBallChart Z) boundaryAttachment).smooth

local instance : ChartedSpace E3
    (ConnectedSumQuotient (factorChartInr X Y δ dY' h1).toBallChart
      (orientedBallChart Z).toBallChart boundaryAttachment.1.toHomeomorph) :=
  (smoothConnectedSum (leftSum X Y δ) Z (factorChartInr X Y δ dY' h1)
    (orientedBallChart Z) boundaryAttachment).charts

local instance : IsManifold (𝓡 3) ∞
    (ConnectedSumQuotient (factorChartInr X Y δ dY' h1).toBallChart
      (orientedBallChart Z).toBallChart boundaryAttachment.1.toHomeomorph) :=
  (smoothConnectedSum (leftSum X Y δ) Z (factorChartInr X Y δ dY' h1)
    (orientedBallChart Z) boundaryAttachment).smooth

private theorem interiorRight_notMem_dY'_closedBall_of_mem_fInterior
    {y : δ.interior}
    (hy : interiorRight (orientedBallChart X).toBallChart δ.toBallChart boundaryAttachment.1 y
      ∈ (fChart X Y δ dY' h1).interior) :
    (y : Y.Carrier) ∉ dY'.chart '' closedBall (0 : E3) 1 := by
  intro hmem
  obtain ⟨w, hw, hwe⟩ := hmem
  obtain ⟨hw', hfw⟩ := factorChartInr_spec X Y δ dY' h1
    (Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2) hw)
  refine hy ⟨w, hw, ?_⟩
  rw [hfw]
  exact congrArg (inr (orientedBallChart X).toBallChart δ.toBallChart
    boundaryAttachment.1.toHomeomorph) (Subtype.ext hwe)

private theorem leftMap_interiorRight_good (v : goodInterior Y δ dY') :
    leftMap X Y Z δ dY' h2
        (interiorRight (orientedBallChart X).toBallChart δ.toBallChart boundaryAttachment.1
          (v : δ.interior)) =
      interiorRight (orientedBallChart X).toBallChart (gChart Y Z δ dY' h2) boundaryAttachment.1
        (yPartInterior Y Z δ dY' h2 (v : δ.interior) v.2) := by
  rw [show leftMap X Y Z δ dY' h2
        (interiorRight (orientedBallChart X).toBallChart δ.toBallChart boundaryAttachment.1
          (v : δ.interior)) =
        yPartMap X Y Z δ dY' h2 (δ.interiorToPunctured (v : δ.interior)) from rfl]
  rw [yPartMap_of_mem X Y Z δ dY' h2
      (fun h => v.2 (image_mono Metric.ball_subset_closedBall h)), yPartRight]
  refine congrArg (inr (orientedBallChart X).toBallChart (gChart Y Z δ dY' h2)
    boundaryAttachment.1.toHomeomorph) (Subtype.ext ?_)
  exact congrArg (inl dY'.toBallChart (orientedBallChart Z).toBallChart
    boundaryAttachment.1.toHomeomorph) (Subtype.ext rfl)

private def yPartInteriorMap :
    goodInterior Y δ dY' → (gChart Y Z δ dY' h2).interior :=
  fun v => yPartInterior Y Z δ dY' h2 (v : δ.interior) v.2

private theorem isLocalDiffeomorph_yPartInteriorMap :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
      (interiorRight (orientedBallChart X).toBallChart (gChart Y Z δ dY' h2)
        boundaryAttachment.1 ∘ yPartInteriorMap Y Z δ dY' h2) := by
  have hψ : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
      (fun v : goodInterior Y δ dY' => (⟨↑(v : δ.interior), v.2⟩ : dY'.interior)) := by
    intro v
    exact isLocalDiffeomorphAt_subtypeCodRestrict (V := dY'.interior) (fun w => w.2)
      ((isLocalDiffeomorph_comp (I := 𝓡 3) (J := 𝓡 3) (K := 𝓡 3)
        (isLocalDiffeomorph_subtype_val δ.interior)
        (isLocalDiffeomorph_subtype_val (goodInterior Y δ dY'))) v)
  have hinner : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (yPartInteriorMap Y Z δ dY' h2) := by
    intro v
    exact isLocalDiffeomorphAt_subtypeCodRestrict (V := (gChart Y Z δ dY' h2).interior)
      (fun w : goodInterior Y δ dY' => inl_notMem_gChart_closedBall_of_notMem_chart Y Z δ dY' h2
        (q := (⟨δ.interiorToPunctured (w : δ.interior),
          fun h => w.2 (image_mono Metric.ball_subset_closedBall h)⟩ : dY'.Punctured))
        (w : δ.interior).2)
      ((isLocalDiffeomorph_comp (I := 𝓡 3) (J := 𝓡 3) (K := 𝓡 3)
        ((smoothConnectedSum Y Z dY' (orientedBallChart Z)
          boundaryAttachment).interiorLeft_localDiffeomorph)
        hψ) v)
  exact isLocalDiffeomorph_comp (I := 𝓡 3) (J := 𝓡 3) (K := 𝓡 3)
    ((smoothConnectedSum X (rightSum Y Z dY') (orientedBallChart X)
      (factorChartInl Y Z dY' δ h2) boundaryAttachment).interiorRight_localDiffeomorph)
    hinner

private theorem isLocalDiffeomorphAt_leftMap_of_interiorLeft
    (x : (orientedBallChart X).toBallChart.interior) :
    IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (leftMap X Y Z δ dY' h2)
      (interiorLeft (orientedBallChart X).toBallChart δ.toBallChart boundaryAttachment.1 x) := by
  have hcomp : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
      (fun z => leftMap X Y Z δ dY' h2
        (interiorLeft (orientedBallChart X).toBallChart δ.toBallChart boundaryAttachment.1 z))
      x :=
    IsLocalDiffeomorphAt.of_eventuallyEq
      (Filter.Eventually.of_forall fun z => leftMap_interiorLeft X Y Z δ dY' h2 z)
      ((smoothConnectedSum X (rightSum Y Z dY') (orientedBallChart X)
        (factorChartInl Y Z dY' δ h2) boundaryAttachment).interiorLeft_localDiffeomorph x)
  have hf : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
      (interiorLeft (orientedBallChart X).toBallChart δ.toBallChart boundaryAttachment.1) x :=
    ((smoothConnectedSum X Y (orientedBallChart X) δ
      boundaryAttachment).interiorLeft_localDiffeomorph x)
  exact isLocalDiffeomorphAt_of_comp (I := 𝓡 3) (J := 𝓡 3) (K := 𝓡 3)
    (f := interiorLeft (orientedBallChart X).toBallChart δ.toBallChart boundaryAttachment.1)
    (g := leftMap X Y Z δ dY' h2) hcomp hf

private theorem isLocalDiffeomorphAt_leftMap_of_collarMap
    (p : ConnectedSumQuotient.CollarDomain) :
    IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (leftMap X Y Z δ dY' h2)
      (collarMap (orientedBallChart X).toBallChart δ.toBallChart boundaryAttachment.1 p) := by
  have hcomp : IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      (fun q => leftMap X Y Z δ dY' h2
        (collarMap (orientedBallChart X).toBallChart δ.toBallChart boundaryAttachment.1 q))
      p :=
    IsLocalDiffeomorphAt.of_eventuallyEq
      (Filter.Eventually.of_forall fun q => leftMap_collarMap X Y Z δ dY' h2 q)
      ((smoothConnectedSum X (rightSum Y Z dY') (orientedBallChart X)
        (factorChartInl Y Z dY' δ h2) boundaryAttachment).collar_localDiffeomorph p)
  have hf : IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      (collarMap (orientedBallChart X).toBallChart δ.toBallChart boundaryAttachment.1) p :=
    ((smoothConnectedSum X Y (orientedBallChart X) δ
      boundaryAttachment).collar_localDiffeomorph p)
  exact isLocalDiffeomorphAt_of_comp (I := (𝓡 2).prod 𝓘(ℝ, ℝ)) (J := 𝓡 3) (K := 𝓡 3)
    (f := collarMap (orientedBallChart X).toBallChart δ.toBallChart boundaryAttachment.1)
    (g := leftMap X Y Z δ dY' h2) hcomp hf

private theorem isLocalDiffeomorphAt_leftMap_of_interiorRight
    {y : δ.interior} (hy : (y : Y.Carrier) ∉ dY'.chart '' closedBall (0 : E3) 1) :
    IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (leftMap X Y Z δ dY' h2)
      (interiorRight (orientedBallChart X).toBallChart δ.toBallChart boundaryAttachment.1 y) := by
  have hcomp : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
      (fun v : goodInterior Y δ dY' => leftMap X Y Z δ dY' h2
        (interiorRight (orientedBallChart X).toBallChart δ.toBallChart boundaryAttachment.1
          (v : δ.interior))) (⟨y, hy⟩ : goodInterior Y δ dY') :=
    IsLocalDiffeomorphAt.of_eventuallyEq
      (Filter.Eventually.of_forall fun v => leftMap_interiorRight_good X Y Z δ dY' h2 v)
      (isLocalDiffeomorph_yPartInteriorMap X Y Z δ dY' h2 (⟨y, hy⟩ : goodInterior Y δ dY'))
  have hf : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
      (fun v : goodInterior Y δ dY' => interiorRight (orientedBallChart X).toBallChart
        δ.toBallChart boundaryAttachment.1 (v : δ.interior))
      (⟨y, hy⟩ : goodInterior Y δ dY') :=
    IsLocalDiffeomorphAt.comp (K := 𝓡 3) (P := (leftSum X Y δ).Carrier)
      ((isLocalDiffeomorph_subtype_val (goodInterior Y δ dY'))
        (⟨y, hy⟩ : goodInterior Y δ dY'))
      ((smoothConnectedSum X Y (orientedBallChart X) δ
        boundaryAttachment).interiorRight_localDiffeomorph (⟨y, hy⟩ : goodInterior Y δ dY'))
  exact isLocalDiffeomorphAt_of_comp (I := 𝓡 3) (J := 𝓡 3) (K := 𝓡 3)
    (f := fun v : goodInterior Y δ dY' => interiorRight (orientedBallChart X).toBallChart
      δ.toBallChart boundaryAttachment.1 (v : δ.interior))
    (g := leftMap X Y Z δ dY' h2) hcomp hf

private theorem isLocalDiffeomorph_leftMap_of_mem_fInterior :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
      (fun u : (fChart X Y δ dY' h1).interior =>
        leftMap X Y Z δ dY' h2 (u : (leftSum X Y δ).Carrier)) := by
  refine isLocalDiffeomorph_restrict_open (I := 𝓡 3) (J := 𝓡 3)
    (f := leftMap X Y Z δ dY' h2) (fChart X Y δ dY' h1).interior ?_
  intro u
  rcases interior_collar_cover (orientedBallChart X).toBallChart δ.toBallChart
    boundaryAttachment.1 (u : (leftSum X Y δ).Carrier) with ⟨x, hx⟩ | ⟨y, hy⟩ | ⟨p, hp⟩
  · rw [← hx]
    exact isLocalDiffeomorphAt_leftMap_of_interiorLeft X Y Z δ dY' h2 x
  · rw [← hy]
    exact isLocalDiffeomorphAt_leftMap_of_interiorRight X Y Z δ dY' h2
      (interiorRight_notMem_dY'_closedBall_of_mem_fInterior X Y δ dY' h1 (hy ▸ u.2))
  · rw [← hp]
    exact isLocalDiffeomorphAt_leftMap_of_collarMap X Y Z δ dY' h2 p

private theorem isLocalDiffeomorph_flattenMap :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (flattenMap X Y Z δ dY' h1 h2) := by
  have hL : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
      (interiorLeft (factorChartInr X Y δ dY' h1).toBallChart (orientedBallChart Z).toBallChart
        boundaryAttachment.1) :=
    ((smoothConnectedSum (leftSum X Y δ) Z (factorChartInr X Y δ dY' h1)
      (orientedBallChart Z) boundaryAttachment).interiorLeft_localDiffeomorph)
  have hLr : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
      (interiorRight (factorChartInr X Y δ dY' h1).toBallChart (orientedBallChart Z).toBallChart
        boundaryAttachment.1) :=
    ((smoothConnectedSum (leftSum X Y δ) Z (factorChartInr X Y δ dY' h1)
      (orientedBallChart Z) boundaryAttachment).interiorRight_localDiffeomorph)
  have hLc : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      (collarMap (factorChartInr X Y δ dY' h1).toBallChart (orientedBallChart Z).toBallChart
        boundaryAttachment.1) :=
    ((smoothConnectedSum (leftSum X Y δ) Z (factorChartInr X Y δ dY' h1)
      (orientedBallChart Z) boundaryAttachment).collar_localDiffeomorph)
  have hRr : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
      (interiorRight (orientedBallChart X).toBallChart (gChart Y Z δ dY' h2)
        boundaryAttachment.1) :=
    ((smoothConnectedSum X (rightSum Y Z dY') (orientedBallChart X)
      (factorChartInl Y Z dY' δ h2) boundaryAttachment).interiorRight_localDiffeomorph)
  have hRc : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      (collarMap (orientedBallChart X).toBallChart (gChart Y Z δ dY' h2)
        boundaryAttachment.1) :=
    ((smoothConnectedSum X (rightSum Y Z dY') (orientedBallChart X)
      (factorChartInl Y Z dY' δ h2) boundaryAttachment).collar_localDiffeomorph)
  have hBr : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
      (interiorRight dY'.toBallChart (orientedBallChart Z).toBallChart boundaryAttachment.1) :=
    ((smoothConnectedSum Y Z dY' (orientedBallChart Z)
      boundaryAttachment).interiorRight_localDiffeomorph)
  have hBc : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      (collarMap dY'.toBallChart (orientedBallChart Z).toBallChart boundaryAttachment.1) :=
    ((smoothConnectedSum Y Z dY' (orientedBallChart Z) boundaryAttachment).collar_localDiffeomorph)
  intro z
  rcases interior_collar_cover (factorChartInr X Y δ dY' h1).toBallChart
    (orientedBallChart Z).toBallChart boundaryAttachment.1 z with ⟨u, hu⟩ | ⟨v, hv⟩ | ⟨p, hp⟩
  · rw [← hu]
    have hgf : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (fun w : (fChart X Y δ dY' h1).interior => flattenMap X Y Z δ dY' h1 h2
          (interiorLeft (fChart X Y δ dY' h1) (orientedBallChart Z).toBallChart
            boundaryAttachment.1 w)) u :=
      IsLocalDiffeomorphAt.of_eventuallyEq
        (Filter.Eventually.of_forall fun w => flattenMap_interiorLeft X Y Z δ dY' h1 h2 w)
        ((isLocalDiffeomorph_leftMap_of_mem_fInterior X Y Z δ dY' h1 h2) u)
    exact isLocalDiffeomorphAt_of_comp (I := 𝓡 3) (J := 𝓡 3) (K := 𝓡 3)
      (f := interiorLeft (fChart X Y δ dY' h1) (orientedBallChart Z).toBallChart
        boundaryAttachment.1)
      (g := flattenMap X Y Z δ dY' h1 h2) hgf (hL u)
  · rw [← hv]
    have hcod : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
        (fun w : (orientedBallChart Z).toBallChart.interior =>
          (⟨inr dY'.toBallChart (orientedBallChart Z).toBallChart
              boundaryAttachment.1.toHomeomorph
              ((orientedBallChart Z).toBallChart.interiorToPunctured w),
            inr_interiorToPunctured_notMem_gChart_closedBall Y Z δ dY' h1 h2⟩ :
            (gChart Y Z δ dY' h2).interior)) := by
      intro w
      exact isLocalDiffeomorphAt_subtypeCodRestrict (V := (gChart Y Z δ dY' h2).interior)
        (fun w' => inr_interiorToPunctured_notMem_gChart_closedBall Y Z δ dY' h1 h2)
        (hBr w)
    have hcomp : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
        (fun w : (orientedBallChart Z).toBallChart.interior =>
          interiorRight (orientedBallChart X).toBallChart (gChart Y Z δ dY' h2)
            boundaryAttachment.1
            (⟨inr dY'.toBallChart (orientedBallChart Z).toBallChart
                boundaryAttachment.1.toHomeomorph
                ((orientedBallChart Z).toBallChart.interiorToPunctured w),
              inr_interiorToPunctured_notMem_gChart_closedBall Y Z δ dY' h1 h2⟩ :
              (gChart Y Z δ dY' h2).interior)) := by
      intro w
      exact IsLocalDiffeomorphAt.comp (K := 𝓡 3) (P := rightQuot X Y Z δ dY' h2)
        (hcod w)
        (hRr (⟨inr dY'.toBallChart (orientedBallChart Z).toBallChart
            boundaryAttachment.1.toHomeomorph
            ((orientedBallChart Z).toBallChart.interiorToPunctured w),
          inr_interiorToPunctured_notMem_gChart_closedBall Y Z δ dY' h1 h2⟩ :
          (gChart Y Z δ dY' h2).interior))
    have hgf : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (fun w : (orientedBallChart Z).toBallChart.interior => flattenMap X Y Z δ dY' h1 h2
          (interiorRight (factorChartInr X Y δ dY' h1).toBallChart (orientedBallChart Z).toBallChart
            boundaryAttachment.1 w)) v :=
      IsLocalDiffeomorphAt.of_eventuallyEq
        (Filter.Eventually.of_forall fun w => flattenMap_interiorRight X Y Z δ dY' h1 h2 w)
        (hcomp v)
    exact isLocalDiffeomorphAt_of_comp (I := 𝓡 3) (J := 𝓡 3) (K := 𝓡 3)
      (f := interiorRight (factorChartInr X Y δ dY' h1).toBallChart
        (orientedBallChart Z).toBallChart boundaryAttachment.1)
      (g := flattenMap X Y Z δ dY' h1 h2) hgf (hLr v)
  · rw [← hp]
    have hcod : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
        (fun q : ConnectedSumQuotient.CollarDomain =>
          (⟨collarMap dY'.toBallChart (orientedBallChart Z).toBallChart boundaryAttachment.1 q,
            collarMap_mem_gChart_interior δ dY' h1 h2 q⟩ :
            (gChart Y Z δ dY' h2).interior)) := by
      intro q
      exact isLocalDiffeomorphAt_subtypeCodRestrict (V := (gChart Y Z δ dY' h2).interior)
        (fun q' => collarMap_mem_gChart_interior δ dY' h1 h2 q') (hBc q)
    have hcomp : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
        (fun q : ConnectedSumQuotient.CollarDomain =>
          interiorRight (orientedBallChart X).toBallChart (gChart Y Z δ dY' h2)
            boundaryAttachment.1
            (⟨collarMap dY'.toBallChart (orientedBallChart Z).toBallChart boundaryAttachment.1 q,
              collarMap_mem_gChart_interior δ dY' h1 h2 q⟩ :
              (gChart Y Z δ dY' h2).interior)) := by
      intro q
      exact IsLocalDiffeomorphAt.comp (K := 𝓡 3) (P := rightQuot X Y Z δ dY' h2)
        (hcod q)
        (hRr (⟨collarMap dY'.toBallChart (orientedBallChart Z).toBallChart boundaryAttachment.1 q,
          collarMap_mem_gChart_interior δ dY' h1 h2 q⟩ :
          (gChart Y Z δ dY' h2).interior))
    have hgf : IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
        (fun q => flattenMap X Y Z δ dY' h1 h2
          (collarMap (factorChartInr X Y δ dY' h1).toBallChart (orientedBallChart Z).toBallChart
            boundaryAttachment.1 q)) p :=
      IsLocalDiffeomorphAt.of_eventuallyEq
        (Filter.Eventually.of_forall fun q => flattenMap_collarMap X Y Z δ dY' h1 h2 q)
        (hcomp p)
    exact isLocalDiffeomorphAt_of_comp (I := (𝓡 2).prod 𝓘(ℝ, ℝ)) (J := 𝓡 3) (K := 𝓡 3)
      (f := collarMap (factorChartInr X Y δ dY' h1).toBallChart (orientedBallChart Z).toBallChart
        boundaryAttachment.1)
      (g := flattenMap X Y Z δ dY' h1 h2) hgf (hLc p)

theorem connectedSumFlatteningIsoCanonical_holds : ConnectedSumFlatteningIsoCanonical.{u} := by
  intro M N P δm dNm h1m h2m
  let S := smoothConnectedSum (leftSum M N δm) P (factorChartInr M N δm dNm h1m)
    (orientedBallChart P) boundaryAttachment
  let S' := smoothConnectedSum M (rightSum N P dNm) (orientedBallChart M)
    (factorChartInl N P dNm δm h2m) boundaryAttachment
  let _ := S.charts
  let _ := S.smooth
  let _ := S'.charts
  let _ := S'.smooth
  let F : ConnectedSumQuotient (factorChartInr M N δm dNm h1m).toBallChart
        (orientedBallChart P).toBallChart boundaryAttachment.1.toHomeomorph ≃ₘ⟮𝓡 3, 𝓡 3⟯
      ConnectedSumQuotient (orientedBallChart M).toBallChart
        (factorChartInl N P dNm δm h2m).toBallChart boundaryAttachment.1.toHomeomorph :=
    IsLocalDiffeomorph.diffeomorphOfBijective
      (isLocalDiffeomorph_flattenMap M N P δm dNm h1m h2m)
      (connectedSumFlatteningMap_bijective M N P δm dNm h1m h2m)
  refine ⟨⟨F, ?_⟩⟩
  change F.preservesOrientation S.orientation S'.orientation
  obtain ⟨v⟩ := ConnectedSumUnit.nonempty_chart_interior (orientedBallChart P)
  let IRL := interiorRight (factorChartInr M N δm dNm h1m).toBallChart
    (orientedBallChart P).toBallChart boundaryAttachment.1
  let ψ : (orientedBallChart P).toBallChart.interior → (gChart N P δm dNm h2m).interior :=
    fun w => ⟨inr dNm.toBallChart (orientedBallChart P).toBallChart
        boundaryAttachment.1.toHomeomorph
        ((orientedBallChart P).toBallChart.interiorToPunctured w),
      inr_interiorToPunctured_notMem_gChart_closedBall N P δm dNm h1m h2m⟩
  let IRR := interiorRight (orientedBallChart M).toBallChart (gChart N P δm dNm h2m)
    boundaryAttachment.1
  have hcomp : (F ∘ IRL) = (IRR ∘ ψ) :=
    funext fun w => flattenMap_interiorRight M N P δm dNm h1m h2m w
  have hψld : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ ψ := by
    intro w
    exact isLocalDiffeomorphAt_subtypeCodRestrict (V := (gChart N P δm dNm h2m).interior)
      (fun w' => inr_interiorToPunctured_notMem_gChart_closedBall N P δm dNm h1m h2m)
      ((smoothConnectedSum N P dNm (orientedBallChart P)
        boundaryAttachment).interiorRight_localDiffeomorph w)
  have hmfψ : mfderiv (𝓡 3) (𝓡 3) ψ v = mfderiv (𝓡 3) (𝓡 3)
      (interiorRight dNm.toBallChart (orientedBallChart P).toBallChart boundaryAttachment.1) v :=
    (DifferentialGeometry.mfderiv_subtypeVal_comp (I := 𝓡 3) (J := 𝓡 3)
      (U := (gChart N P δm dNm h2m).interior) (f := ψ) (x := v)).symm
  let eA := (S.interiorRight_localDiffeomorph.mfderivToContinuousLinearEquiv
    (by simp) v).toLinearEquiv
  let eB := (F.mfderivToContinuousLinearEquiv (by simp) (IRL v)).toLinearEquiv
  let eC := (S'.interiorRight_localDiffeomorph.mfderivToContinuousLinearEquiv
    (by simp) (ψ v)).toLinearEquiv
  let eD := ((smoothConnectedSum N P dNm (orientedBallChart P) boundaryAttachment
    ).interiorRight_localDiffeomorph.mfderivToContinuousLinearEquiv (by simp) v).toLinearEquiv
  have hA : ⇑eA = ⇑(mfderiv (𝓡 3) (𝓡 3) IRL v) := by
    change ⇑((S.interiorRight_localDiffeomorph.mfderivToContinuousLinearEquiv
      (by simp) v).toLinearEquiv) = ⇑(mfderiv (𝓡 3) (𝓡 3) IRL v)
    rw [ContinuousLinearEquiv.coe_toLinearEquiv]
    rfl
  have hB : ⇑eB = ⇑(mfderiv (𝓡 3) (𝓡 3) (F : _ → _) (IRL v)) := by
    change ⇑((F.mfderivToContinuousLinearEquiv (by simp) (IRL v)).toLinearEquiv)
      = ⇑(mfderiv (𝓡 3) (𝓡 3) (F : _ → _) (IRL v))
    rw [ContinuousLinearEquiv.coe_toLinearEquiv]
    rfl
  have hC : ⇑eC = ⇑(mfderiv (𝓡 3) (𝓡 3) IRR (ψ v)) := by
    change ⇑((S'.interiorRight_localDiffeomorph.mfderivToContinuousLinearEquiv
      (by simp) (ψ v)).toLinearEquiv) = ⇑(mfderiv (𝓡 3) (𝓡 3) IRR (ψ v))
    rw [ContinuousLinearEquiv.coe_toLinearEquiv]
    rfl
  have hD : ⇑eD = ⇑(mfderiv (𝓡 3) (𝓡 3)
      (interiorRight dNm.toBallChart (orientedBallChart P).toBallChart
        boundaryAttachment.1) v) := by
    change ⇑(((smoothConnectedSum N P dNm (orientedBallChart P) boundaryAttachment
      ).interiorRight_localDiffeomorph.mfderivToContinuousLinearEquiv
      (by simp) v).toLinearEquiv) = ⇑(mfderiv (𝓡 3) (𝓡 3)
        (interiorRight dNm.toBallChart (orientedBallChart P).toBallChart
          boundaryAttachment.1) v)
    rw [ContinuousLinearEquiv.coe_toLinearEquiv]
    rfl
  have hIRL_md : MDifferentiableAt (𝓡 3) (𝓡 3) IRL v :=
    S.interiorRight_localDiffeomorph.mdifferentiable (by simp) v
  have hIRR_md : MDifferentiableAt (𝓡 3) (𝓡 3) IRR (ψ v) :=
    S'.interiorRight_localDiffeomorph.mdifferentiable (by simp) (ψ v)
  have hF_md : MDifferentiableAt (𝓡 3) (𝓡 3) (F : _ → _) (IRL v) :=
    F.mdifferentiable (by simp) (IRL v)
  have hψ_md : MDifferentiableAt (𝓡 3) (𝓡 3) ψ v :=
    hψld.mdifferentiable (by simp) v
  have hlin : eA.trans eB = eD.trans eC := by
    apply LinearEquiv.ext
    intro w
    change ⇑eB (⇑eA w) = ⇑eC (⇑eD w)
    rw [hA, hB, hC, hD, ← hmfψ]
    rw [← mfderiv_comp_apply (x := v) (f := IRL) (g := (F : _ → _)) hF_md hIRL_md w]
    refine (congrArg (fun G => mfderiv (𝓡 3) (𝓡 3) G v w) hcomp).trans ?_
    exact mfderiv_comp_apply (x := v) (f := ψ) (g := IRR) hIRR_md hψ_md w
  have hO : Orientation.map (Fin 3) eA (P.orientation.orientation v)
      = S.orientation.orientation (IRL v) :=
    S.interiorRight_preserves_orientation v
  have hψo : Orientation.map (Fin 3) eD (P.orientation.orientation v)
      = (rightSum N P dNm).orientation.orientation (ψ v) :=
    (smoothConnectedSum N P dNm (orientedBallChart P) boundaryAttachment
      ).interiorRight_preserves_orientation v
  have hO' : Orientation.map (Fin 3) eC ((rightSum N P dNm).orientation.orientation (ψ v))
      = S'.orientation.orientation (IRR (ψ v)) :=
    S'.interiorRight_preserves_orientation (ψ v)
  have hpoint : Orientation.map (Fin 3) eB (S.orientation.orientation (IRL v))
      = S'.orientation.orientation (F (IRL v)) := by
    have hpt : (S'.orientation.orientation (IRR (ψ v)) : Orientation ℝ E3 (Fin 3))
        = (S'.orientation.orientation (F (IRL v)) : Orientation ℝ E3 (Fin 3)) := rfl
    have hAeq : Orientation.map (Fin 3) eB (S.orientation.orientation (IRL v))
        = Orientation.map (Fin 3) (eA.trans eB) (P.orientation.orientation v) :=
      (congrArg (fun z => Orientation.map (Fin 3) eB z) hO.symm).trans
        (orientation_map_trans eA eB (P.orientation.orientation v)).symm
    have hDeq : Orientation.map (Fin 3) (eD.trans eC) (P.orientation.orientation v)
        = S'.orientation.orientation (F (IRL v)) :=
      (orientation_map_trans eD eC (P.orientation.orientation v)).trans
        ((congrArg (fun z => Orientation.map (Fin 3) eC z) hψo).trans (hO'.trans hpt))
    exact hAeq.trans ((congrArg (fun e => Orientation.map (Fin 3) e
      (P.orientation.orientation v)) hlin).trans hDeq)
  let _ := S'.connected
  exact Diffeomorph.preservesOrientation_of_eq_at F S.orientation S'.orientation (IRL v) hpoint

end

theorem connectedSumAssociative_holds : connectedSumAssociative.{u} :=
  connectedSumAssociative_of_flatteningIsoCanonical connectedSumFlatteningIsoCanonical_holds

end DifferentialGeometry.Topology
