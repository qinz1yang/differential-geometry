import DifferentialGeometry.Analysis.Integration.Measure.Parametric.Defs
import DifferentialGeometry.Analysis.Integration.Measure.Chart.Density
import DifferentialGeometry.Analysis.Integration.Measure.Chart.HaarBasis
import DifferentialGeometry.Geometry.Exponential.Variation.Radial
import DifferentialGeometry.Geometry.Comparison.Variation.Jacobi.Gram
import DifferentialGeometry.Geometry.Exponential.NormalCoordinates.Frame
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

noncomputable section

open Set Manifold MeasureTheory
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open Exponential NormalCoordinates Variation
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Coordinates

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space (TangentBundle I M)]

theorem paramDensity_expMap_eq_curveDensity
    (g : SmoothRiemannianMetric I M) (p : M) (v : E)
    (hv : (show TangentSpace I p from v) ∈ expDomain (I := I) g p) :
    paramDensity (I := I) g
        (fun b : E => expMap (I := I) g p (show TangentSpace I p from b)) v =
      curveDensity (I := I) g (radialCurve (I := I) g p v)
        (fun i => radialJacobiField (I := I) g p v (chartModelBasis E i)) 1 := by
  unfold paramDensity curveDensity
  apply congrArg Real.sqrt
  apply congrArg Matrix.det
  ext i j
  simp only [paramGramMatrix_apply, curveGram, Matrix.of_apply]
  rw [radialJacobiField_one (I := I) g p v _ hv,
    radialJacobiField_one (I := I) g p v _ hv]
  exact congrArg (fun y : M => g.inner y
    (show TangentSpace I y from
      (mfderiv 𝓘(ℝ, E) I
        (fun b : E => expMap (I := I) g p (show TangentSpace I p from b)) v
        (chartModelBasis E i) : E))
    (show TangentSpace I y from
      (mfderiv 𝓘(ℝ, E) I
        (fun b : E => expMap (I := I) g p (show TangentSpace I p from b)) v
        (chartModelBasis E j) : E))) (radialCurve_one (I := I) g p v).symm

theorem curveDensity_radialJacobiField_basis
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SmoothRiemannianMetric I M) (p : M) (v : E)
    (hv : (show TangentSpace I p from v) ∈ expDomain (I := I) g p)
    (B B' : Module.Basis ι ℝ E) :
    curveDensity (I := I) g (radialCurve (I := I) g p v)
        (fun i => radialJacobiField (I := I) g p v (B' i)) 1 =
      |B.det B'| *
        curveDensity (I := I) g (radialCurve (I := I) g p v)
          (fun i => radialJacobiField (I := I) g p v (B i)) 1 := by
  classical
  let F : E → M := fun w =>
    expMap (I := I) g p (show TangentSpace I p from w)
  let L : E →L[ℝ] TangentSpace I (radialCurve (I := I) g p v 1) :=
    mfderiv 𝓘(ℝ, E) I F v
  let C : Matrix ι ι ℝ := B.toMatrix B'
  have hcoord (i : ι) : B' i = ∑ k, C k i • B k := by
    simpa only [C, Module.Basis.toMatrix_apply] using (B.sum_repr (B' i)).symm
  have hcol (w : E) : radialJacobiField (I := I) g p v w 1 = L w := by
    exact radialJacobiField_one (I := I) g p v w hv
  have hjac : ∀ i, radialJacobiField (I := I) g p v (B' i) 1 =
      ∑ k, C k i • radialJacobiField (I := I) g p v (B k) 1 := by
    intro i
    rw [hcol, hcoord i, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hcol]
    exact L.map_smul (C k i) (B k)
  simpa only [C, Module.Basis.det_apply] using
    curveDensity_recomb (I := I) g (radialCurve (I := I) g p v)
      (fun i => radialJacobiField (I := I) g p v (B i))
      (fun i => radialJacobiField (I := I) g p v (B' i)) 1 C hjac

end Normed

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space (TangentBundle I M)]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

theorem lintegral_paramDensity_expMap_eq_lintegral_curveDensity
    (g : SmoothRiemannianMetric I M) (p : M) {K : Set E}
    (hK : MeasurableSet K)
    (hKdom : K ⊆ expDomain (I := I) g p) :
    (∫⁻ v in K,
        ENNReal.ofReal
          (paramDensity (I := I) g
            (fun b : E => expMap (I := I) g p
              (show TangentSpace I p from b)) v)
        ∂(modelHaar (E := E))) =
      ∫⁻ w in (normalFrame (I := I) (E := E) g p) ⁻¹' K,
        ENNReal.ofReal
          (curveDensity (I := I) g
            (radialCurve (I := I) g p
              (normalFrame (I := I) (E := E) g p w))
            (fun i => radialJacobiField (I := I) g p
              (normalFrame (I := I) (E := E) g p w)
              (normalBasis (I := I) g p i)) 1)
        ∂(volume : Measure E) := by
  classical
  let b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E :=
    chartModelBasis E
  let b' : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E :=
    normalBasis (I := I) g p
  let L : E ≃L[ℝ] E := normalFrame (I := I) (E := E) g p
  let F : E → M := fun v =>
    expMap (I := I) g p (show TangentSpace I p from v)
  let Dn : E → ℝ := fun v =>
    curveDensity (I := I) g (radialCurve (I := I) g p v)
      (fun i => radialJacobiField (I := I) g p v (b' i)) 1
  have hD (v : E) (hv : v ∈ K) :
      ENNReal.ofReal |b.det b'| *
          ENNReal.ofReal (paramDensity (I := I) g F v) =
        ENNReal.ofReal (Dn v) := by
    have hdensity : paramDensity (I := I) g F v =
        curveDensity (I := I) g (radialCurve (I := I) g p v)
          (fun i => radialJacobiField (I := I) g p v (b i)) 1 := by
      exact paramDensity_expMap_eq_curveDensity (I := I) g p v (hKdom hv)
    rw [← ENNReal.ofReal_mul (abs_nonneg (b.det b'))]
    congr 1
    rw [hdensity]
    exact (curveDensity_radialJacobiField_basis (I := I) g p v (hKdom hv) b b').symm
  have hbasis :
      (∫⁻ v in K,
          ENNReal.ofReal (paramDensity (I := I) g F v)
          ∂(modelHaar (E := E))) =
        ∫⁻ v in K, ENNReal.ofReal (Dn v) ∂b'.addHaar := by
    calc
      _ = ∫⁻ v in K,
          ENNReal.ofReal (paramDensity (I := I) g F v) ∂b.addHaar := by
            rfl
      _ = ∫⁻ v in K,
          ENNReal.ofReal |b.det b'| *
            ENNReal.ofReal (paramDensity (I := I) g F v)
          ∂b'.addHaar := by
            rw [← Module.Basis.det_smul_addHaar b b',
              setLIntegral_smul_measure]
            exact
              (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ = ∫⁻ v in K, ENNReal.ofReal (Dn v) ∂b'.addHaar := by
            exact setLIntegral_congr_fun hK hD
  have hbmap :
      (stdOrthonormalBasis ℝ E).toBasis.map L.toLinearEquiv = b' := by
    ext i
    change normalFrame (I := I) (E := E) g p
        ((stdOrthonormalBasis ℝ E) i) = normalBasis (I := I) g p i
    exact normalFrame_basis (I := I) g p i
  have hmap : Measure.map L (volume : Measure E) = b'.addHaar := by
    calc
      _ = Measure.map L (stdOrthonormalBasis ℝ E).toBasis.addHaar := by
            rw [(stdOrthonormalBasis ℝ E).addHaar_eq_volume]
      _ = ((stdOrthonormalBasis ℝ E).toBasis.map
          L.toLinearEquiv).addHaar := Module.Basis.map_addHaar _ _
      _ = b'.addHaar := congrArg Module.Basis.addHaar hbmap
  have hmp : MeasurePreserving L (volume : Measure E) b'.addHaar :=
    ⟨L.continuous.measurable, hmap⟩
  rw [hbasis]
  exact
    (hmp.setLIntegral_comp_preimage_emb
      L.toHomeomorph.toMeasurableEquiv.measurableEmbedding
      (fun v => ENNReal.ofReal (Dn v)) K).symm

end InnerProduct

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
