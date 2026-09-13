import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Associative
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OrientedFactorBallChart

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

end DifferentialGeometry.Topology
