import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongWindowSpliceC12X
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.Parameter
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.ReferenceChange
import DifferentialGeometry.Geometry.Metric.Family.ChartCurvature.MetricFamilySmoothOn

/-!
# Cylinder family: continuity, shift and reference change (C12X, O-C12X-S16H G4c)

`cylFam_C12X σ = 2 (1 - σ) round + dz²` (the shrinking cylinder of `SS/ShrinkingCylinder`) and
its axial rescaling `cyl2_C12X σ c = 2 (1 - σ) round + c dz²`.  Frame changes in the far-early
branch of `hwin` send the cylinder comparison of an input to a time-shifted, axially rescaled
cylinder used as its own reference (the axial factor absorbs the pre/post normalization
mismatch `c = (q r²)^{±1}`).  This file provides the uniform estimates for that family:

* `cyl2_inner_C12X`, `cyl2_one_C12X`, `cyl2_chartGram_eq_C12X`.
* `cyl2_metricDerivNorm_continuousOn_C12X`: joint continuity in all parameters.
* `exists_cyl2_shift_small_C12X`, `exists_cyl2_reference_bound_C12X`: uniform smallness of a
  parameter change and uniform reference change on the parameter box `[-2, 1/2] × [1/2, 2]`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Operator

private local instance s16h_sphereDim2 :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

private local instance s16h_bufferSigma2 (ε : ℝ) : SigmaCompactSpace (spatialNeckBuffer ε) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen SpatialNeckCylinderModel
      (spatialNeckBuffer ε).isOpen)

/-- The shrinking cylinder `2 (1 - σ) round + dz²` on the spatial neck cylinder. -/
def cylFam_C12X (σ : ℝ) : SmoothRiemannianMetric SpatialNeckCylinderModel SpatialNeckCylinder :=
  _root_.DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric
    (E := EuclideanSpace ℝ (Fin 3)) σ

/-- Inner product of the cylinder family. -/
theorem cylFam_inner_C12X {σ : ℝ} (hσ : σ < 1) (x : SpatialNeckCylinder)
    (v w : TangentSpace SpatialNeckCylinderModel x) :
    (cylFam_C12X σ).inner x v w =
      2 * (1 - σ) * (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner x.1 v.1 w.1 +
        v.2 * w.2 :=
  _root_.DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_inner hσ x v w

/-- On the neck buffer the background is the restricted cylinder. -/
theorem strongNeckBackgroundMetric_eq_cylFam_C12X (ε s : ℝ) (hs : s ≤ 0) :
    strongNeckBackgroundMetric ε s = (cylFam_C12X s).restrictOpen (spatialNeckBuffer ε) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  have hs1 : s < 1 := by linarith
  rw [strongNeckBackgroundMetric_of_nonpos ε s hs, SmoothRiemannianMetric.restrictOpen_inner,
    SmoothRiemannianMetric.restrictOpen_inner]
  exact (scalarOneShrinkingCylinderMetric_inner s hs1 x.val.1 x.val.2 v.1 w.1 v.2 w.2).trans
    (cylFam_inner_C12X hs1 x.val v w).symm

/-- Joint chart smoothness of the cylinder family. -/
theorem cylFam_chartGram_contDiffOn_C12X (x : SpatialNeckCylinder)
    (i j : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ))) :
    ContDiffOn ℝ ∞
      (fun q : ℝ × (EuclideanSpace ℝ (Fin 2) × ℝ) => chartGramOnE (cylFam_C12X q.1) x i j q.2)
      (Ioo (-3 : ℝ) 1 ×ˢ interior (extChartAt SpatialNeckCylinderModel x).target) := by
  have hS := _root_.DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_isSolutionOn_interval
    (E := EuclideanSpace ℝ (Fin 3)) (show (-3 : ℝ) < 1 by norm_num) le_rfl
  exact hS.smoothMetric.chartGramOnE_contDiffOn (J := Ioo (-3) 1) (fun _ ht => ht) x i j

private def s16h_posPart (a : ℝ) : ℝ := if 0 < a then a else 1

private theorem s16h_posPart_pos (a : ℝ) : 0 < s16h_posPart a := by
  unfold s16h_posPart
  split_ifs with h
  · exact h
  · exact one_pos

private theorem s16h_posPart_of_pos {a : ℝ} (h : 0 < a) : s16h_posPart a = a := by
  simp [s16h_posPart, h]

/-- The axially rescaled shrinking cylinder `2 (1 - σ) round + c dz²`. -/
def cyl2_C12X (σ c : ℝ) : SmoothRiemannianMetric SpatialNeckCylinderModel SpatialNeckCylinder :=
  (scaleMetric (s16h_posPart (2 * (1 - σ))) (s16h_posPart_pos _)
    (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2))).prod
    (scaleMetric (s16h_posPart c) (s16h_posPart_pos _) (euclideanMetric (E := ℝ)))

/-- Inner product of the two-parameter family. -/
theorem cyl2_inner_C12X {σ c : ℝ} (hσ : σ < 1) (hc : 0 < c) (x : SpatialNeckCylinder)
    (v w : TangentSpace SpatialNeckCylinderModel x) :
    (cyl2_C12X σ c).inner x v w =
      2 * (1 - σ) * (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner x.1 v.1 w.1 +
        c * (v.2 * w.2) := by
  rw [cyl2_C12X, SmoothRiemannianMetric.prod_inner]
  erw [scaleMetric_inner, scaleMetric_inner]
  rw [s16h_posPart_of_pos (by linarith : (0 : ℝ) < 2 * (1 - σ)), s16h_posPart_of_pos hc]
  change _ + c * inner ℝ (v.2 : ℝ) (w.2 : ℝ) = _
  rw [RCLike.inner_apply, conj_trivial]
  ring

/-- `c = 1` is the cylinder family. -/
theorem cyl2_one_C12X {σ : ℝ} (hσ : σ < 1) : cyl2_C12X σ 1 = cylFam_C12X σ := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [cyl2_inner_C12X hσ one_pos, cylFam_inner_C12X hσ]
  ring

/-- Chart Gram entries of the two-parameter family are a linear combination of two members of
the cylinder family. -/
theorem cyl2_chartGram_eq_C12X {σ c : ℝ} (hσ : σ < 1) (hc : 0 < c) (x : SpatialNeckCylinder)
    (i j : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ)))
    (z : EuclideanSpace ℝ (Fin 2) × ℝ) :
    chartGramOnE (cyl2_C12X σ c) x i j z =
      (2 * (2 * (1 - σ)) - c) * chartGramOnE (cylFam_C12X (1 / 2)) x i j z +
        2 * (c - 2 * (1 - σ)) * chartGramOnE (cylFam_C12X (3 / 4)) x i j z := by
  simp only [chartGramOnE_def, DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply]
  rw [cyl2_inner_C12X hσ hc, cylFam_inner_C12X (by norm_num), cylFam_inner_C12X (by norm_num)]
  ring

/-- Joint chart smoothness of the two-parameter family. -/
theorem cyl2_chartGram_contDiffOn_C12X (x : SpatialNeckCylinder)
    (i j : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ))) :
    ContDiffOn ℝ ∞ (fun q : (ℝ × ℝ) × (EuclideanSpace ℝ (Fin 2) × ℝ) =>
        chartGramOnE (cyl2_C12X q.1.1 q.1.2) x i j q.2)
      ((Ioo (-3 : ℝ) 1 ×ˢ Ioi (0 : ℝ)) ×ˢ
        interior (extChartAt SpatialNeckCylinderModel x).target) := by
  let V := interior (extChartAt SpatialNeckCylinderModel x).target
  have hG (σ₀ : ℝ) (h0 : σ₀ ∈ Ioo (-3 : ℝ) 1) :
      ContDiffOn ℝ ∞ (fun q : (ℝ × ℝ) × (EuclideanSpace ℝ (Fin 2) × ℝ) =>
        chartGramOnE (cylFam_C12X σ₀) x i j q.2) ((Ioo (-3 : ℝ) 1 ×ˢ Ioi (0 : ℝ)) ×ˢ V) :=
    ((cylFam_chartGram_contDiffOn_C12X x i j).comp
      ((contDiff_const.prodMk contDiff_snd).contDiffOn) (fun q hq => ⟨h0, hq.2⟩)).congr
      fun _ _ => rfl
  have hA : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × (EuclideanSpace ℝ (Fin 2) × ℝ) =>
      2 * (2 * (1 - q.1.1)) - q.1.2) := by fun_prop
  have hB : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × (EuclideanSpace ℝ (Fin 2) × ℝ) =>
      2 * (q.1.2 - 2 * (1 - q.1.1))) := by fun_prop
  refine ((hA.contDiffOn.mul (hG (1 / 2) ⟨by norm_num, by norm_num⟩)).add
    (hB.contDiffOn.mul (hG (3 / 4) ⟨by norm_num, by norm_num⟩))).congr ?_
  rintro ⟨⟨σ, c⟩, z⟩ ⟨⟨hσ, hc⟩, -⟩
  exact cyl2_chartGram_eq_C12X hσ.2 hc x i j z

/-- Joint continuity of the two-parameter family's derivative norms. -/
theorem cyl2_metricDerivNorm_continuousOn_C12X (r : ℕ) :
    ContinuousOn (fun q : ((ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ)) × SpatialNeckCylinder =>
      metricDerivNorm r (cyl2_C12X q.1.1.1 q.1.1.2) (cyl2_C12X q.1.2.1.1 q.1.2.1.2)
        (cyl2_C12X q.1.2.2.1 q.1.2.2.2) q.2)
      (((Ioo (-3 : ℝ) 1 ×ˢ Ioi (0 : ℝ)) ×ˢ (Ioo (-3 : ℝ) 1 ×ˢ Ioi (0 : ℝ)) ×ˢ
        (Ioo (-3 : ℝ) 1 ×ˢ Ioi (0 : ℝ))) ×ˢ univ) := by
  let B : Set (ℝ × ℝ) := Ioo (-3 : ℝ) 1 ×ˢ Ioi (0 : ℝ)
  let A : Set ((ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ)) := B ×ˢ B ×ˢ B
  have hsm (x : SpatialNeckCylinder) (i j : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ)))
      (f : (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ) → ℝ × ℝ) (hf : ContDiff ℝ ∞ f)
      (hfA : ∀ q ∈ A, f q ∈ B) :
      ContDiffOn ℝ ∞ (fun q : ((ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ)) × (EuclideanSpace ℝ (Fin 2) × ℝ) =>
        chartGramOnE (cyl2_C12X (f q.1).1 (f q.1).2) x i j q.2)
        (A ×ˢ interior (extChartAt SpatialNeckCylinderModel x).target) := by
    have hc := cyl2_chartGram_contDiffOn_C12X x i j
    have hg : ContDiff ℝ ∞ (fun q : ((ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ)) ×
        (EuclideanSpace ℝ (Fin 2) × ℝ) => (f q.1, q.2)) :=
      (hf.comp contDiff_fst).prodMk contDiff_snd
    exact (hc.comp hg.contDiffOn (fun q hq => ⟨hfA q.1 hq.1, hq.2⟩)).congr fun _ _ => rfl
  have hlocal : ∀ x ∈ (univ : Set SpatialNeckCylinder),
      ∃ V : Set (EuclideanSpace ℝ (Fin 2) × ℝ), IsOpen V ∧
        extChartAt SpatialNeckCylinderModel x x ∈ V ∧
        V ⊆ (extChartAt SpatialNeckCylinderModel x).target ∧
        ∀ i j : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ)),
          ContDiffOn ℝ ∞ (fun q : ((ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ)) ×
            (EuclideanSpace ℝ (Fin 2) × ℝ) =>
              chartGramOnE (cyl2_C12X q.1.1.1 q.1.1.2) x i j q.2) (A ×ˢ V) ∧
          ContDiffOn ℝ ∞ (fun q : ((ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ)) ×
            (EuclideanSpace ℝ (Fin 2) × ℝ) =>
              chartGramOnE (cyl2_C12X q.1.2.1.1 q.1.2.1.2) x i j q.2) (A ×ˢ V) ∧
          ContDiffOn ℝ ∞ (fun q : ((ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ)) ×
            (EuclideanSpace ℝ (Fin 2) × ℝ) =>
              chartGramOnE (cyl2_C12X q.1.2.2.1 q.1.2.2.2) x i j q.2) (A ×ˢ V) := by
    intro x _
    have hopen : IsOpen (extChartAt SpatialNeckCylinderModel x).target :=
      isOpen_extChartAt_target x
    refine ⟨interior (extChartAt SpatialNeckCylinderModel x).target, isOpen_interior, ?_,
      interior_subset, fun i j => ⟨?_, ?_, ?_⟩⟩
    · rw [hopen.interior_eq]
      exact mem_extChartAt_target x
    · exact hsm x i j (fun q => q.1) contDiff_fst fun q hq => hq.1
    · exact hsm x i j (fun q => q.2.1) contDiff_snd.fst fun q hq => hq.2.1
    · exact hsm x i j (fun q => q.2.2) contDiff_snd.snd fun q hq => hq.2.2
  exact metricDerivNorm_joint_continuousOn
    (fun q : (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ) => cyl2_C12X q.1.1 q.1.2)
    (fun q => cyl2_C12X q.2.1.1 q.2.1.2) (fun q => cyl2_C12X q.2.2.1 q.2.2.2) hlocal r

/-- The compact parameter box `[-2, 1/2] × [1/2, 2]`. -/
def cylBox_C12X : Set (ℝ × ℝ) := Icc (-2 : ℝ) (1 / 2) ×ˢ Icc (1 / 2 : ℝ) 2

private theorem s16h_box_sub {a : ℝ × ℝ} (ha : a ∈ cylBox_C12X) :
    a ∈ Ioo (-3 : ℝ) 1 ×ˢ Ioi (0 : ℝ) :=
  ⟨⟨by linarith [ha.1.1], by linarith [ha.1.2]⟩, by
    change (0 : ℝ) < a.2
    linarith [ha.2.1]⟩

/-- Uniform smallness of a parameter change of the two-parameter family on compact sets. -/
theorem exists_cyl2_shift_small_C12X (r : ℕ) {K : Set SpatialNeckCylinder} (hK : IsCompact K)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ ∀ a b c : ℝ × ℝ, a ∈ cylBox_C12X → b ∈ cylBox_C12X → c ∈ cylBox_C12X →
      |a.1 - b.1| < η → |a.2 - b.2| < η → ∀ x ∈ K,
        metricDerivNorm r (cyl2_C12X a.1 a.2) (cyl2_C12X b.1 b.2) (cyl2_C12X c.1 c.2) x < δ := by
  have hbox : IsCompact cylBox_C12X := isCompact_Icc.prod isCompact_Icc
  have hA : IsCompact ((cylBox_C12X ×ˢ cylBox_C12X ×ˢ cylBox_C12X) ×ˢ K) :=
    (hbox.prod (hbox.prod hbox)).prod hK
  have hsub : (cylBox_C12X ×ˢ cylBox_C12X ×ˢ cylBox_C12X) ×ˢ K ⊆
      (((Ioo (-3 : ℝ) 1 ×ˢ Ioi (0 : ℝ)) ×ˢ (Ioo (-3 : ℝ) 1 ×ˢ Ioi (0 : ℝ)) ×ˢ
        (Ioo (-3 : ℝ) 1 ×ˢ Ioi (0 : ℝ))) ×ˢ univ) := by
    rintro ⟨⟨a, b, c⟩, x⟩ ⟨⟨ha, hb, hc⟩, -⟩
    exact ⟨⟨s16h_box_sub ha, s16h_box_sub hb, s16h_box_sub hc⟩, mem_univ _⟩
  have hunif := hA.uniformContinuousOn_of_continuous
    ((cyl2_metricDerivNorm_continuousOn_C12X r).mono hsub)
  rw [Metric.uniformContinuousOn_iff] at hunif
  obtain ⟨η, hη, h⟩ := hunif δ hδ
  refine ⟨η, hη, fun a b c ha hb hc h1 h2 x hx => ?_⟩
  have hdist : dist ((a, b, c), x) ((b, b, c), x) < η := by
    have hab : dist a b < η := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      exact max_lt h1 h2
    refine lt_of_le_of_lt ?_ hab
    simp [Prod.dist_eq]
  have hh := h _ ⟨⟨ha, hb, hc⟩, hx⟩ _ ⟨⟨hb, hb, hc⟩, hx⟩ hdist
  rw [metricDerivNorm_self, Real.dist_eq, sub_zero] at hh
  exact (le_abs_self _).trans_lt hh

private theorem s16h_norm_iterCov_eq (ε : ℝ)
    (h g : SmoothRiemannianMetric SpatialNeckCylinderModel (spatialNeckBuffer ε)) (j : ℕ)
    (hj : 1 ≤ j) (x : spatialNeckBuffer ε) :
    Real.sqrt (normSq0S g x (2 + j) (iterCov g 2 (metricTensorField h) j x)) =
      metricDerivNorm j h g g x := by
  classical
  obtain ⟨b, hb⟩ := exists_orthonormal_basis g x
  rw [metricDerivNorm_eq_iterCov h g g j b (metricInverseInBasis_identity_of_orthonormal g b hb)]
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  rw [iterCov_sub, iterCov_metric_zero, sub_zero]

/-- **Uniform reference change** within the two-parameter family on the neck buffer: for
parameters `a, b` in the box, the reference `cyl2 a` can be replaced by `cyl2 b` with a uniform
constant. -/
theorem exists_cyl2_reference_bound_C12X (ε : ℝ) (p : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ a ∈ cylBox_C12X, ∀ b ∈ cylBox_C12X,
      ∀ A B : SmoothRiemannianMetric SpatialNeckCylinderModel (spatialNeckBuffer ε),
      ∀ r ≤ p, ∀ x : spatialNeckBuffer ε,
        metricDerivNorm r A B ((cyl2_C12X b.1 b.2).restrictOpen (spatialNeckBuffer ε)) x ≤
          D * ∑ k ∈ Finset.range (p + 1),
            metricDerivNorm k A B ((cyl2_C12X a.1 a.2).restrictOpen (spatialNeckBuffer ε)) x := by
  let U := spatialNeckBuffer ε
  let K₀ : Set SpatialNeckCylinder := univ ×ˢ Icc (-(ε⁻¹ + 1)) (ε⁻¹ + 1)
  have hK₀ : IsCompact K₀ := isCompact_univ.prod isCompact_Icc
  have hUK (x : U) : x.val ∈ K₀ := by
    have hx := x.2
    change -ε⁻¹ - 1 < x.val.2 ∧ x.val.2 < ε⁻¹ + 1 at hx
    exact ⟨mem_univ _, by linarith [hx.1], by linarith [hx.2]⟩
  have hbox : IsCompact cylBox_C12X := isCompact_Icc.prod isCompact_Icc
  have hbd (j : ℕ) : ∃ M₀ : ℝ, ∀ q ∈ cylBox_C12X ×ˢ cylBox_C12X, ∀ y ∈ K₀,
      metricDerivNorm j (cyl2_C12X q.1.1 q.1.2) (cyl2_C12X q.2.1 q.2.2)
        (cyl2_C12X q.2.1 q.2.2) y ≤ M₀ := by
    have hcont : ContinuousOn (fun q : ((ℝ × ℝ) × (ℝ × ℝ)) × SpatialNeckCylinder =>
        metricDerivNorm j (cyl2_C12X q.1.1.1 q.1.1.2) (cyl2_C12X q.1.2.1 q.1.2.2)
          (cyl2_C12X q.1.2.1 q.1.2.2) q.2)
        ((cylBox_C12X ×ˢ cylBox_C12X) ×ˢ K₀) := by
      refine (cyl2_metricDerivNorm_continuousOn_C12X j).comp
        (f := fun q : ((ℝ × ℝ) × (ℝ × ℝ)) × SpatialNeckCylinder =>
          ((q.1.1, q.1.2, q.1.2), q.2))
        ((continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_fst.snd)).prodMk
          continuous_snd).continuousOn ?_
      rintro ⟨⟨a, b⟩, y⟩ ⟨⟨ha, hb⟩, -⟩
      exact ⟨⟨s16h_box_sub ha, s16h_box_sub hb, s16h_box_sub hb⟩, mem_univ _⟩
    obtain ⟨M₀, hM₀⟩ := ((hbox.prod hbox).prod hK₀).exists_bound_of_continuousOn hcont
    refine ⟨M₀, fun q hq y hy => ?_⟩
    have h1 := hM₀ (q, y) ⟨hq, hy⟩
    rw [Real.norm_eq_abs] at h1
    exact (le_abs_self _).trans h1
  choose M₀ hM₀ using hbd
  let Mt : ℝ := ∑ j ∈ Finset.range (p + 1), |M₀ j|
  let Bc : ℝ := Real.sqrt (6 ^ (2 + p)) * Mt
  have hBc : 0 ≤ Bc :=
    mul_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  obtain ⟨D, hD, hbound⟩ := exists_uniform_metric_deriv_norm_reference_bound
    (I := SpatialNeckCylinderModel) (M := U) p (show (1 : ℝ) ≤ 6 by norm_num) hBc
  refine ⟨D, hD, fun a ha b hb A B r hr x => ?_⟩
  have ha1 : a.1 < 1 := by linarith [ha.1.2]
  have hb1 : b.1 < 1 := by linarith [hb.1.2]
  have ha2 : 0 < a.2 := by linarith [ha.2.1]
  have hb2 : 0 < b.2 := by linarith [hb.2.1]
  have heq : ∀ y ∈ (univ : Set U), ∀ v : TangentSpace SpatialNeckCylinderModel y,
      (6 : ℝ)⁻¹ * ((cyl2_C12X a.1 a.2).restrictOpen U).inner y v v ≤
          ((cyl2_C12X b.1 b.2).restrictOpen U).inner y v v ∧
        ((cyl2_C12X b.1 b.2).restrictOpen U).inner y v v ≤
          6 * ((cyl2_C12X a.1 a.2).restrictOpen U).inner y v v := by
    intro y _ v
    have e1 : ((cyl2_C12X a.1 a.2).restrictOpen U).inner y v v =
        2 * (1 - a.1) * (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner y.val.1 v.1
          v.1 + a.2 * (v.2 * v.2) := by
      rw [SmoothRiemannianMetric.restrictOpen_inner]
      exact cyl2_inner_C12X ha1 ha2 y.val v v
    have e2 : ((cyl2_C12X b.1 b.2).restrictOpen U).inner y v v =
        2 * (1 - b.1) * (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner y.val.1 v.1
          v.1 + b.2 * (v.2 * v.2) := by
      rw [SmoothRiemannianMetric.restrictOpen_inner]
      exact cyl2_inner_C12X hb1 hb2 y.val v v
    rw [e1, e2]
    have hR := metric_inner_self_nonneg (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2))
      y.val.1 v.1
    have hv := mul_self_nonneg v.2
    have h1 := mul_nonneg (show (0 : ℝ) ≤ 10 - 12 * b.1 + 2 * a.1 by
      linarith [hb.1.2, ha.1.1]) hR
    have h2 := mul_nonneg (show (0 : ℝ) ≤ 10 - 12 * a.1 + 2 * b.1 by
      linarith [ha.1.2, hb.1.1]) hR
    have h3 := mul_nonneg (show (0 : ℝ) ≤ 6 * b.2 - a.2 by linarith [hb.2.1, ha.2.2]) hv
    have h4 := mul_nonneg (show (0 : ℝ) ≤ 6 * a.2 - b.2 by linarith [ha.2.1, hb.2.2]) hv
    constructor
    · rw [inv_mul_le_iff₀ (by norm_num : (0 : ℝ) < 6)]
      nlinarith
    · nlinarith
  have hEq : MetricUniformEquivalentOn (univ : Set U) ((cyl2_C12X a.1 a.2).restrictOpen U)
      ((cyl2_C12X b.1 b.2).restrictOpen U) 6 := ⟨by norm_num, heq⟩
  have hbB : ∀ y ∈ (univ : Set U), ∀ j : ℕ, 1 ≤ j → j ≤ p →
      Real.sqrt (normSq0S ((cyl2_C12X b.1 b.2).restrictOpen U) y (2 + j)
        (iterCov ((cyl2_C12X a.1 a.2).restrictOpen U) 2
          (metricTensorField ((cyl2_C12X b.1 b.2).restrictOpen U)) j y)) ≤ Bc := by
    intro y _ j hj1 hjp
    calc _ ≤ Real.sqrt (6 ^ (2 + j)) * Real.sqrt (normSq0S ((cyl2_C12X a.1 a.2).restrictOpen U)
            y (2 + j) (iterCov ((cyl2_C12X a.1 a.2).restrictOpen U) 2
              (metricTensorField ((cyl2_C12X b.1 b.2).restrictOpen U)) j y)) :=
          hEq.sqrt_normSq0S_le (mem_univ y) _
      _ = Real.sqrt (6 ^ (2 + j)) * metricDerivNorm j (cyl2_C12X b.1 b.2) (cyl2_C12X a.1 a.2)
            (cyl2_C12X a.1 a.2) y.val := by
          rw [s16h_norm_iterCov_eq ε _ _ j hj1 y, metricDerivNorm_restrictOpen]
      _ ≤ Real.sqrt (6 ^ (2 + p)) * Mt := by
          apply mul_le_mul (Real.sqrt_le_sqrt (pow_le_pow_right₀ (by norm_num) (by omega)))
            _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
          exact ((hM₀ j (b, a) ⟨hb, ha⟩ y.val (hUK y)).trans (le_abs_self _)).trans
            (Finset.single_le_sum (f := fun k => |M₀ k|) (fun k _ => abs_nonneg (M₀ k))
              (Finset.mem_range.mpr (by omega)))
  exact hbound univ isOpen_univ _ _ heq hbB A B r hr x (mem_univ x)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
