import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.SphereCapFilling
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.SphereCapRadialDiffeomorph
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.UnitFillingSmooth
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.BallChartTransportConnected
import DifferentialGeometry.Topology.Manifold.BallChartTransport

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff Topology InnerProductSpace
open Function

namespace DifferentialGeometry.Topology.SphereUnitFilling

lemma chart_image_closedBall (P : S3) :
    (sphereBallChart P).chart '' Metric.closedBall (0 : E3) 1
      = {x : S3 | ⟪(x : E4), (P : E4)⟫_ℝ ≤ 0} := by
  have himg : (sphereBallChart P).chart '' Metric.closedBall (0 : E3) 1
      = (stereographic' 3 P).symm '' Metric.closedBall (0 : E3) 2 := by
    have hfun : (sphereBallChart P).chart '' Metric.closedBall (0 : E3) 1 =
        ((fun v : E3 => (stereographic' 3 P).symm v) ∘
          (fun u : E3 => -((2 : ℝ) • u))) '' Metric.closedBall (0 : E3) 1 := rfl
    rw [hfun, Set.image_comp]
    congr 1
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right] at hu ⊢
      rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
    · intro hv
      refine ⟨-(((2 : ℝ)⁻¹) • v), ?_, ?_⟩
      · rw [Metric.mem_closedBall, dist_zero_right] at hv ⊢
        rw [norm_neg, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr (by norm_num : (0 : ℝ) < 2))]
        linarith
      · simp only [smul_neg, smul_smul, mul_inv_cancel₀ (by norm_num : (2 : ℝ) ≠ 0),
          neg_neg, one_smul]
  rw [himg]
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hv
    rw [Set.mem_ofPred_eq, inner_stereographic_symm_apply]
    have hnum : ‖v‖ ^ 2 - 4 ≤ 0 := by nlinarith [norm_nonneg v, hv]
    exact div_nonpos_of_nonpos_of_nonneg hnum (by positivity)
  · intro hx
    have hxle : ⟪(x : E4), (P : E4)⟫_ℝ ≤ 0 := hx
    have hxP : x ≠ P := by
      intro h
      rw [h, inner_self_eq_norm_sq_to_K, norm_coe_sphere P] at hxle
      norm_num at hxle
    refine ⟨(stereographic' 3 P) x, ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right]
      have hval : ⟪(x : E4), (P : E4)⟫_ℝ =
          (‖(stereographic' 3 P) x‖ ^ 2 - 4) / (‖(stereographic' 3 P) x‖ ^ 2 + 4) := by
        conv_lhs => rw [← (stereographic' 3 P).left_inv (mem_source_stereographic P hxP)]
        exact inner_stereographic_symm_apply P _
      rw [hval] at hxle
      have hpos : (0 : ℝ) < ‖(stereographic' 3 P) x‖ ^ 2 + 4 := by
        nlinarith [sq_nonneg ‖(stereographic' 3 P) x‖]
      have hnum : ‖(stereographic' 3 P) x‖ ^ 2 - 4 ≤ 0 := by
        rcases div_nonpos_iff.mp hxle with ⟨_, h2⟩ | ⟨h1, _⟩
        · exact absurd h2 (not_le_of_gt hpos)
        · exact h1
      nlinarith [hnum, norm_nonneg ((stereographic' 3 P) x)]
    · exact (stereographic' 3 P).left_inv (mem_source_stereographic P hxP)

lemma mem_interior_iff (P : S3) (x : S3) :
    x ∈ (sphereBallChart P).interior ↔ 0 < ⟪(x : E4), (P : E4)⟫_ℝ := by
  rw [BallChart.mem_interior, chart_image_closedBall]
  simp only [Set.mem_ofPred_eq, not_le]

universe u

lemma neg_ne_pole_of_mem_interior {P : S3} {y : S3} (hy : y ∈ (sphereBallChart P).interior) :
    (-(y) : S3) ≠ P := by
  intro h
  have hpos := (mem_interior_iff P y).mp hy
  have hyco : (y : E4) = -(P : E4) := by
    have hc := congrArg (fun z : S3 => (z : E4)) h
    exact neg_eq_iff_eq_neg.mp hc
  rw [hyco, inner_neg_left, inner_self_eq_norm_sq_to_K, norm_coe_sphere P] at hpos
  norm_num at hpos

lemma norm_stereographic_neg_lt_two {P : S3} {y : S3} (hy : y ∈ (sphereBallChart P).interior) :
    ‖stereographic' 3 P (-(y))‖ < 2 := by
  have hpos := (mem_interior_iff P y).mp hy
  have hyP := neg_ne_pole_of_mem_interior hy
  have hleft := (stereographic' 3 P).left_inv (mem_source_stereographic P hyP)
  have hcoord : ⟪((-(y) : S3) : E4), (P : E4)⟫_ℝ =
      (‖stereographic' 3 P (-(y))‖ ^ 2 - 4) / (‖stereographic' 3 P (-(y))‖ ^ 2 + 4) := by
    conv_lhs => rw [← hleft]
    exact inner_stereographic_symm_apply P _
  have hcoe : ((-(y) : S3) : E4) = -(y : E4) := by simp
  have hneg : ⟪((-(y) : S3) : E4), (P : E4)⟫_ℝ < 0 := by
    rw [hcoe, inner_neg_left]
    linarith
  rw [hcoord] at hneg
  have hden : (0 : ℝ) < ‖stereographic' 3 P (-(y))‖ ^ 2 + 4 := by
    nlinarith [sq_nonneg ‖stereographic' 3 P (-(y))‖]
  rcases div_neg_iff.mp hneg with ⟨_, h2⟩ | ⟨h1, _⟩
  · exact absurd h2 (not_lt_of_ge (le_of_lt hden))
  · nlinarith [h1, norm_nonneg (stereographic' 3 P (-(y)))]

lemma norm_capRadialMap_stereographic_neg_lt_one {P : S3} {y : S3}
    (hy : y ∈ (sphereBallChart P).interior) :
    ‖capRadialMap (stereographic' 3 P (-(y)))‖ ≤ 1 := by
  have hlt := norm_stereographic_neg_lt_two hy
  have hle : ‖stereographic' 3 P (-(y))‖ ≤ 2 := le_of_lt hlt
  rcases eq_or_lt_of_le (norm_nonneg (stereographic' 3 P (-(y)))) with h0 | h0
  · have hv0 : stereographic' 3 P (-(y)) = 0 := norm_eq_zero.mp h0.symm
    rw [hv0]
    simp [capRadialMap]
  · exact norm_capRadialMap_le_one h0 hle

lemma isLocalDiffeomorphAt_stereographic (P : S3) {z : S3} (hz : z ∈ ({P}ᶜ : Set S3)) :
    IsLocalDiffeomorphAt (𝓡 3) 𝓘(ℝ, E3) ∞ (fun z : S3 => stereographic' 3 P z) z := by
  refine ⟨{ toFun := fun z : S3 => stereographic' 3 P z
            invFun := fun v : E3 => (stereographic' 3 P).symm v
            source := {P}ᶜ
            target := Set.univ
            map_source' := fun w hw => Set.mem_univ _
            map_target' := fun v _ => by
              have hv : v ∈ (stereographic' 3 P).target := by
                rw [stereographic'_target]
                exact Set.mem_univ v
              simpa only [stereographic'_source] using (stereographic' 3 P).map_target hv
            left_inv' := fun w hw => (stereographic' 3 P).left_inv (by
              simpa only [stereographic'_source] using hw)
            right_inv' := fun v _ => (stereographic' 3 P).right_inv (by
              rw [stereographic'_target]
              exact Set.mem_univ v)
            open_source := isClosed_singleton.isOpen_compl
            open_target := isOpen_univ
            contMDiffOn_toFun := contMDiffOn_stereographic P
            contMDiffOn_invFun := contMDiffOn_stereographic_symm P },
    hz, fun w _ => rfl⟩

variable {M : ConnectedClosedOrientedManifold.{u} 3}

theorem isLocalDiffeomorphAt_sphereFill (P : S3) (c : BallChart 3 (𝓡 3) M.Carrier)
    (y : S3) (hy : y ∈ (sphereBallChart P).interior) :
    IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
      (fun y : S3 => c.chart (capRadialMap (stereographic' 3 P (-(y))))) y := by
  have hz : (-(y) : S3) ∈ ({P}ᶜ : Set S3) := neg_ne_pole_of_mem_interior hy
  have h1 : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (fun y : S3 => -(y)) y :=
    (Manifold.sphereAntipodalDiffeomorph (n := 3) (E := E4)).isLocalDiffeomorph y
  have h2 : IsLocalDiffeomorphAt (𝓡 3) 𝓘(ℝ, E3) ∞ (fun z : S3 => stereographic' 3 P z) (-(y)) :=
    isLocalDiffeomorphAt_stereographic P hz
  have h12 : IsLocalDiffeomorphAt (𝓡 3) 𝓘(ℝ, E3) ∞
      (fun y : S3 => stereographic' 3 P (-(y))) y :=
    h1.comp (K := 𝓘(ℝ, E3)) (P := E3) h2
  have h3 : IsLocalDiffeomorphAt 𝓘(ℝ, E3) 𝓘(ℝ, E3) ∞ capRadialMap
      (stereographic' 3 P (-(y))) :=
    isLocalDiffeomorph_capRadialMap _
  have h123 : IsLocalDiffeomorphAt (𝓡 3) 𝓘(ℝ, E3) ∞
      (fun y : S3 => capRadialMap (stereographic' 3 P (-(y)))) y :=
    h12.comp (K := 𝓘(ℝ, E3)) (P := E3) h3
  have h4 : IsLocalDiffeomorphAt 𝓘(ℝ, E3) (𝓡 3) ∞ (fun v : E3 => c.chart v)
      (capRadialMap (stereographic' 3 P (-(y)))) :=
    PartialDiffeomorph.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ c.chart
      (c.closedBall_one_subset_source (Metric.mem_closedBall.mpr (by
        rw [dist_zero_right]
        exact norm_capRadialMap_stereographic_neg_lt_one hy)))
  exact h123.comp (K := 𝓡 3) (P := M.Carrier) h4

end DifferentialGeometry.Topology.SphereUnitFilling

namespace DifferentialGeometry.Topology

namespace ConnectedSumUnit

open SphereUnitFilling

universe u

variable {M : ConnectedClosedOrientedManifold.{u} 3}

lemma mem_interior_lift {P : SphereUnitFilling.S3}
    (d : OrientedBallChart standardThreeSphereLift.{u}.toClosedOrientedManifold)
    (hd : ∀ u : csE3, ULift.down (d.toBallChart.chart u)
      = (SphereUnitFilling.sphereBallChart P).chart u)
    (x : d.toBallChart.interior) :
    ULift.down x.1 ∈ (SphereUnitFilling.sphereBallChart P).interior := by
  have himg : ∀ y : ULift.{u} SphereUnitFilling.S3,
      (y ∈ d.toBallChart.chart '' Metric.closedBall (0 : csE3) 1)
        ↔ (ULift.down y ∈ (SphereUnitFilling.sphereBallChart P).chart ''
            Metric.closedBall (0 : csE3) 1) := by
    intro y
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, hu, (hd u).symm⟩
    · rintro ⟨u, hu, hu'⟩
      exact ⟨u, hu, ULift.down_injective (by rw [hd u]; exact hu')⟩
  have hnot : x.1 ∉ d.toBallChart.chart '' Metric.closedBall (0 : csE3) 1 := by
    have hx := x.2
    rw [BallChart.mem_interior] at hx
    exact hx
  refine (SphereUnitFilling.mem_interior_iff P _).mpr ?_
  have h1 : ULift.down x.1 ∉ (SphereUnitFilling.sphereBallChart P).chart ''
      Metric.closedBall (0 : csE3) 1 :=
    fun h => hnot ((himg _).mpr h)
  rw [SphereUnitFilling.chart_image_closedBall] at h1
  have h2 : ¬ (⟪(ULift.down (α := SphereUnitFilling.S3) x.1 : E4), (P : E4)⟫_ℝ ≤ 0) :=
    fun h => h1 h
  exact not_le.mp h2

theorem unitFillingOfSphereChart_fill_eq (P : SphereUnitFilling.S3)
    (d : OrientedBallChart standardThreeSphereLift.{u}.toClosedOrientedManifold)
    (hd : ∀ u : csE3, ULift.down (d.toBallChart.chart u)
      = (SphereUnitFilling.sphereBallChart P).chart u)
    (c : OrientedBallChart M.toClosedOrientedManifold) (x : d.toBallChart.interior) :
    ((unitFillingOfSphereChart P d hd c).fill (d.toBallChart.interiorToPunctured x) : M.Carrier)
      = c.toBallChart.chart
        (SphereUnitFilling.capRadialMap
          (stereographic' 3 P (-(ULift.down (α := SphereUnitFilling.S3) x.1)))) := by
  have hΦ : ((BallChart.puncturedHomeomorphOfImage d.toBallChart
        (SphereUnitFilling.sphereBallChart P) uliftSphereHomeomorph
        (puncturedImage_ulift P d hd)) (d.toBallChart.interiorToPunctured x)
      : SphereUnitFilling.S3) = (ULift.down (α := SphereUnitFilling.S3) x.1) := by
    rw [puncturedHomeomorph_apply_val P d hd]
    rfl
  rw [unitFillingOfSphereChart_fill, SphereUnitFilling.capFill_apply,
    SphereUnitFilling.capFillMap_val, SphereUnitFilling.capPoint_apply, hΦ]

theorem ballComplementSmooth_unitFillingOfSphereChart (P : SphereUnitFilling.S3)
    (d : OrientedBallChart standardThreeSphereLift.{u}.toClosedOrientedManifold)
    (hd : ∀ u : csE3, ULift.down (d.toBallChart.chart u)
      = (SphereUnitFilling.sphereBallChart P).chart u)
    (c : OrientedBallChart M.toClosedOrientedManifold) :
    BallComplementSmooth (unitFillingOfSphereChart P d hd c) := by
  intro x
  refine isLocalDiffeomorphAt_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => unitFillingOfSphereChart_fill_eq P d hd c y) ?_
  have hsub : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
      (fun x : d.toBallChart.interior => x.1) x :=
    isLocalDiffeomorphAt_subtype_val d.toBallChart.interior x
  have hulift : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
      (fun y : standardThreeSphereLift.{u}.Carrier => ULift.down y) x.1 := by
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (ULift.{u} SphereUnitFilling.S3) :=
      DifferentialGeometry.Topology.uliftChartedSpace _ _
    let _ : IsManifold (𝓡 3) ∞ (ULift.{u} SphereUnitFilling.S3) :=
      DifferentialGeometry.Topology.isManifold_ulift (𝓡 3) SphereUnitFilling.S3
    have h := (DifferentialGeometry.Topology.uliftDiffeomorph (𝓡 3) SphereUnitFilling.S3).symm
      |>.isLocalDiffeomorph x.1
    refine isLocalDiffeomorphAt_of_eventuallyEq ?_ h
    filter_upwards with y
    exact (DifferentialGeometry.Topology.uliftDiffeomorph_symm_apply (𝓡 3)
      SphereUnitFilling.S3 y).symm
  have hcomp : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
      (fun x : d.toBallChart.interior => ULift.down (α := SphereUnitFilling.S3) x.1) x :=
    hsub.comp (K := 𝓡 3) (P := SphereUnitFilling.S3) hulift
  have hamb : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
      (fun y : SphereUnitFilling.S3 => c.toBallChart.chart
        (SphereUnitFilling.capRadialMap (stereographic' 3 P (-(y))))) (ULift.down x.1) :=
    isLocalDiffeomorphAt_sphereFill P c.toBallChart _ (mem_interior_lift d hd x)
  have hfinal : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
      (fun x : d.toBallChart.interior => c.toBallChart.chart
        (SphereUnitFilling.capRadialMap
          (stereographic' 3 P (-(ULift.down (α := SphereUnitFilling.S3) x.1))))) x :=
    hcomp.comp (K := 𝓡 3) (P := M.Carrier) hamb
  exact hfinal

theorem nonempty_diffeomorph_connectedSum_sphere_right
    (X : ConnectedClosedOrientedManifold.{u} 3) (P : SphereUnitFilling.S3)
    (h : ∃ d : OrientedBallChart standardThreeSphereLift.{u}.toClosedOrientedManifold,
      ∀ u : csE3, ULift.down (d.toBallChart.chart u)
        = (SphereUnitFilling.sphereBallChart P).chart u) :
    Nonempty ((connectedSum X standardThreeSphereLift.{u}).toClosedOrientedManifold.Carrier
      ≃ₘ⟮𝓡 3, 𝓡 3⟯ X.toClosedOrientedManifold.Carrier) := by
  obtain ⟨d, hd⟩ := h
  let c := orientedBallChart X
  let c' := orientedBallChart X
  let d' := orientedBallChart standardThreeSphereLift.{u}
  obtain ⟨e₁⟩ := nonempty_diffeomorph_of_unitFilling
    (unitFillingOfSphereChart P d hd c)
    (ballComplementCollar_unitFillingOfSphereChart P d hd c)
    (ballComplementSmooth_unitFillingOfSphereChart P d hd c)
  have hΦ : Manifold.BallChartTransport c.toBallChart c'.toBallChart :=
    ballChartTransport_of_orientedBallCharts X c c'
  have hΨ : Manifold.BallChartTransport d.toBallChart d'.toBallChart :=
    ballChartTransport_of_orientedBallCharts standardThreeSphereLift.{u} d d'
  obtain ⟨e₂⟩ := nonempty_connectedSumQuotient_diffeomorph_of_ballChartTransport
    c c' d d' boundaryAttachment hΦ hΨ
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 3))
      (ConnectedSumQuotient c.toBallChart d.toBallChart boundaryAttachment.1.toHomeomorph) :=
    ConnectedSumQuotient.csChartedSpace c.toBallChart d.toBallChart
      boundaryAttachment.1.toHomeomorph
  let _ : IsManifold (𝓡 3) ∞
      (ConnectedSumQuotient c.toBallChart d.toBallChart boundaryAttachment.1.toHomeomorph) :=
    ConnectedSumQuotient.csIsManifold c.toBallChart d.toBallChart
      boundaryAttachment.1.toHomeomorph
      (ConnectedSumQuotient.contDiffOn_reflectMap boundaryAttachment.1)
      (ConnectedSumQuotient.contDiffOn_reflectMapInv boundaryAttachment.1)
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 3))
      (ConnectedSumQuotient c'.toBallChart d'.toBallChart boundaryAttachment.1.toHomeomorph) :=
    ConnectedSumQuotient.csChartedSpace c'.toBallChart d'.toBallChart
      boundaryAttachment.1.toHomeomorph
  let _ : IsManifold (𝓡 3) ∞
      (ConnectedSumQuotient c'.toBallChart d'.toBallChart boundaryAttachment.1.toHomeomorph) :=
    ConnectedSumQuotient.csIsManifold c'.toBallChart d'.toBallChart
      boundaryAttachment.1.toHomeomorph
      (ConnectedSumQuotient.contDiffOn_reflectMap boundaryAttachment.1)
      (ConnectedSumQuotient.contDiffOn_reflectMapInv boundaryAttachment.1)
  exact ⟨e₂.symm.trans e₁⟩

end ConnectedSumUnit

end DifferentialGeometry.Topology
