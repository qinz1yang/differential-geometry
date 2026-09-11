import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CollapseMap
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.InsertionDomination
import DifferentialGeometry.Geometry.Measure.ProductLevel
import DifferentialGeometry.Geometry.Metric.WeakLength
import DifferentialGeometry.Geometry.Metric.RoundCylinder

set_option autoImplicit false
noncomputable section
open Bundle Set Manifold TopologicalSpace MeasureTheory Filter DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Geometry.Measure
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian
open scoped Manifold ContDiff InnerProductSpace Topology ENNReal NNReal
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private abbrev EC := EuclideanSpace ℝ (Fin 2) × ℝ
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

private local instance (O : Opens (S2 × ℝ)) : SigmaCompactSpace O :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen IC O.isOpen)
private local instance (O : Opens (S2 × ℝ)) : MeasurableSpace O := borel O
private local instance (O : Opens (S2 × ℝ)) : BorelSpace O := ⟨rfl⟩

private theorem radial_metric_bound (y : S2) (r s z : ℝ) (hr : 0 < r)
    (hs : s ∈ Icc (0 : ℝ) 1) (v : TangentSpace IC (y, z)) :
    metric.inner (r • (y : E3))
      ((s * v.2) • (y : E3) + r • dIncl (n := 2) y v.1)
      ((s * v.2) • (y : E3) + r • dIncl (n := 2) y v.1) ≤
      (roundCylinderMetric (E := E3) (n := 2)).inner (y, z) v v := by
  rw [metric_inner_polar (norm_eq_of_mem_sphere y)
    (dIncl_orth y v.1) (dIncl_orth y v.1) hr, roundCylinderMetric_inner]
  have hi : 0 ≤ ⟪dIncl (n := 2) y v.1, dIncl (n := 2) y v.1⟫_ℝ := real_inner_self_nonneg
  have ha := warpingFunction_le_sqrt_two r
  have hp := (warpingFunction_pos hr).le
  have htwo : warpingFunction r ^ 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hsquare : s ^ 2 ≤ 1 := by nlinarith [hs.1, hs.2]
  nlinarith [mul_nonneg (sub_nonneg.mpr htwo) hi,
    mul_nonneg (sub_nonneg.mpr hsquare) (sq_nonneg v.2)]

private theorem collapseMap_deep_radius {A B : ℝ} (hA : 0 < A) (hAB : 2 * A < B)
    (q : DifferentialGeometry.Geometry.Neck.openCylinder B) (hq : q.val.2 ≤ -2 * A) :
    ‖(collapseMap hA hAB q : E3)‖ < conformalRadius (-7 * A / 4) := by
  change ‖collapseMapAmbient A q.val‖ < _
  rw [collapseMapAmbient_norm]
  apply max_lt
  · exact conformalRadius_pos _
  · calc
      collapseRadius A q.val.2 ≤ collapseRadius A (-2 * A) := monotone_collapseRadius A hq
      _ = conformalRadius (-2 * A) := collapseRadius_eq_conformalRadius le_rfl
      _ < conformalRadius (-7 * A / 4) := strictMono_conformalRadius (by linarith)

private theorem collapseMap_deep_inner_le {A B η : ℝ}
    (hA : 0 < A) (hAB : 2 * A < B) (hη : 0 < η)
    (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B))
    (q : DifferentialGeometry.Geometry.Neck.openCylinder B)
    (htip : collapseTip A < q.val.2) (hq : q.val.2 ≤ -2 * A)
    (v : TangentSpace IC q) :
    (insertedMetric hA hAB hη h).inner (collapseMap hA hAB q)
      (mfderiv IC (𝓡 3) (collapseMap hA hAB) q v)
      (mfderiv IC (𝓡 3) (collapseMap hA hAB) q v) ≤
      η * (roundCylinderMetric (E := E3) (n := 2)).inner q.val v v := by
  rw [insertedMetric_inner_of_inner hA hAB hη h _ (collapseMap_deep_radius hA hAB q hq)]
  rw [collapseMap_mfderiv_of_tip_lt hA hAB q htip,
    collapseMap_radial hA hAB q htip.le]
  exact mul_le_mul_of_nonneg_left
    (radial_metric_bound q.val.1 (collapseRadius A q.val.2)
      (deriv (collapseRadius A) q.val.2) q.val.2 (collapseRadius_pos_iff.mpr htip)
      (deriv_collapseRadius_mem_Icc A q.val.2) v) hη.le

private theorem collapseMap_collar_mfderiv {A B : ℝ}
    (hA : 0 < A) (hAB : 2 * A < B) (q : insertionCylinder A B)
    (v : TangentSpace IC q) :
    mfderiv IC (𝓡 3) (collapseMap hA hAB)
      (Opens.inclusion (insertionCylinder_le_openCylinder hAB) q) v =
      mfderiv IC (𝓡 3) (insertionMap hA hAB) q v := by
  have htip := collapseTip_lt A
  have hL := transitionEnd_pos
  have hne : (Opens.inclusion (insertionCylinder_le_openCylinder hAB) q).val.2 ≠
      collapseTip A := by
    have hq := q.property.1
    change q.val.2 ≠ collapseTip A
    linarith
  have hcomp := congrArg (fun D => D v) (mfderiv_comp q
    ((contMDiffAt_collapseMap_of_height_ne hA hAB _ hne).mdifferentiableAt (by decide))
    ((contMDiff_inclusion (insertionCylinder_le_openCylinder hAB) (n := ∞)).mdifferentiable
      (by decide) q))
  have heq : collapseMap hA hAB ∘ Opens.inclusion (insertionCylinder_le_openCylinder hAB) =
      insertionMap hA hAB := funext (collapseMap_insertionMap hA hAB)
  rw [heq, mfderiv_opens_incl] at hcomp
  exact hcomp.symm

theorem collapseMap_inner_le_of_cylinder_lower {A B η : ℝ}
    (hA : 0 < A) (hAB : 2 * A < B) (hη : 0 < η)
    (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B))
    (q : DifferentialGeometry.Geometry.Neck.openCylinder B) (hq : q.val.2 ≠ collapseTip A)
    (v : TangentSpace IC q)
    (hlower : η * (roundCylinderMetric (E := E3) (n := 2)).inner q.val v v ≤ h.inner q v v) :
    (insertedMetric hA hAB hη h).inner (collapseMap hA hAB q)
      (mfderiv IC (𝓡 3) (collapseMap hA hAB) q v)
      (mfderiv IC (𝓡 3) (collapseMap hA hAB) q v) ≤ h.inner q v v := by
  rcases lt_or_gt_of_ne hq with hlt | hgt
  · rw [collapseMap_mfderiv_of_height_lt hA hAB q hlt]
    simpa using metric_inner_self_nonneg h q v
  · by_cases hdeep : q.val.2 ≤ -2 * A
    · exact (collapseMap_deep_inner_le hA hAB hη h q hgt hdeep v).trans hlower
    · let q' : insertionCylinder A B := ⟨q.val, not_le.mp hdeep, q.property.2⟩
      have hq' : Opens.inclusion (insertionCylinder_le_openCylinder hAB) q' = q := Subtype.ext rfl
      have heq := collapseMap_insertionMap hA hAB q'
      rw [hq'] at heq
      have hd : mfderiv IC (𝓡 3) (collapseMap hA hAB) q v =
          mfderiv IC (𝓡 3) (insertionMap hA hAB) q' v := by
        simpa only [hq'] using! collapseMap_collar_mfderiv hA hAB q' v
      erw [heq, hd]
      exact insertedMetric_inner_le_of_cylinder_lower hA hAB hη h q' v hlower

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem collapseMap_eVariationOn_le_of_cylinder_lower {A B η : ℝ}
    (hA : 0 < A) (hAB : 2 * A < B) (hη : 0 < η)
    (g : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B))
    (hlower : ∀ q : DifferentialGeometry.Geometry.Neck.openCylinder B, ∀ v : TangentSpace IC q,
      η * (roundCylinderMetric (E := E3) (n := 2)).inner q.val v v ≤ g.inner q v v)
    (γ : ℝ → DifferentialGeometry.Geometry.Neck.openCylinder B) (a b : ℝ)
    (hγ : ContinuousOn γ (Icc a b)) :
    (let cg := g.toContinuousRiemannianMetric
     letI : RiemannianBundle (TangentSpace IC : DifferentialGeometry.Geometry.Neck.openCylinder B → Type _) :=
       ⟨cg.toRiemannianMetric⟩
     letI : IsContinuousRiemannianBundle EC
       (TangentSpace IC : DifferentialGeometry.Geometry.Neck.openCylinder B → Type _) :=
       inferInstance
     letI : PseudoEMetricSpace (DifferentialGeometry.Geometry.Neck.openCylinder B) :=
       .ofRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B)
     let k := insertedMetric hA hAB hη g
     let ck := k.toContinuousRiemannianMetric
     letI : RiemannianBundle (TangentSpace (𝓡 3) : insertionBall B → Type _) :=
       ⟨ck.toRiemannianMetric⟩
     letI : IsContinuousRiemannianBundle E3 (TangentSpace (𝓡 3) : insertionBall B → Type _) :=
       inferInstance
     letI : PseudoEMetricSpace (insertionBall B) := .ofRiemannianMetric (𝓡 3) (insertionBall B)
     eVariationOn (collapseMap hA hAB ∘ γ) (Icc a b) ≤ eVariationOn γ (Icc a b)) := by
  apply eVariationOn_comp_le_of_ae_mfderiv g (insertedMetric hA hAB hη g)
    (collapseMap hA hAB) (collapseMap_local_intrinsic_bound hA hAB g _) _ γ a b hγ
  have hnull := riemannianVolumeMeasure_snd_fiber_eq_zero
    (DifferentialGeometry.Geometry.Neck.openCylinder B) g (collapseTip A)
  have hae : ∀ᵐ q ∂riemannianVolumeMeasure IC (DifferentialGeometry.Geometry.Neck.openCylinder B) g,
      q.val.2 ≠ collapseTip A := measure_eq_zero_iff_ae_notMem.mp hnull
  filter_upwards [hae] with q hq
  intro _hdiff v
  exact Real.sqrt_le_sqrt (collapseMap_inner_le_of_cylinder_lower hA hAB hη g q hq v (hlower q v))

end DifferentialGeometry.PDE.RicciFlow.StandardCap
