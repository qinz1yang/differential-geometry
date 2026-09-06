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

private theorem inner_radialJacobiField_self
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) {t : ℝ}
    (ht : (show TangentSpace I p from t • x) ∈ expDomain (I := I) g p) :
    g.inner (radialCurve (I := I) g p x t)
      (radialJacobiField (I := I) g p x x t)
      (radialJacobiField (I := I) g p x w t) = t ^ 2 * g.inner p x w := by
  let G : E →L[ℝ] E →L[ℝ] ℝ := g.inner (radialCurve (I := I) g p x t)
  have hJ := radialJacobiField_self (I := I) g p x ht
  have hpair : G
      (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
      (radialJacobiField (I := I) g p x w t) = t * g.inner p x w :=
    inner_curveVelocity_radialJacobiField (I := I) g p x w ht
  let v : E := curveVelocity (I := I) (radialCurve (I := I) g p x) t
  let z : E := radialJacobiField (I := I) g p x w t
  have hJ' : (radialJacobiField (I := I) g p x x t : E) = t • v := hJ
  change G (radialJacobiField (I := I) g p x x t) z = _
  rw [hJ', G.map_smul, _root_.smul_apply, smul_eq_mul]
  rw [show G v z = t * g.inner p x w from hpair]
  ring

theorem curveGram_det_radialJacobiField_option
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SmoothRiemannianMetric I M) (p : M) (x : E) (w : ι → E) {t : ℝ}
    (ht : (show TangentSpace I p from t • x) ∈ expDomain (I := I) g p)
    (hperp : ∀ i, g.inner p x (w i) = 0) :
    (curveGram (I := I) g (radialCurve (I := I) g p x)
      (fun o => radialJacobiField (I := I) g p x (Option.elim o x w)) t).det =
      t ^ 2 * g.inner p x x *
        (curveGram (I := I) g (radialCurve (I := I) g p x)
          (fun i => radialJacobiField (I := I) g p x (w i)) t).det := by
  have h := curveGram_det_option (I := I) g (radialCurve (I := I) g p x)
    (fun o => radialJacobiField (I := I) g p x (Option.elim o x w)) t (fun i => by
      simpa only [Option.elim_none, Option.elim_some, hperp i, mul_zero] using!
        inner_radialJacobiField_self (I := I) g p x (w i) ht)
  simpa only [Option.elim_none, Option.elim_some,
    inner_radialJacobiField_self (I := I) g p x x ht] using! h

theorem curveDensity_radialJacobiField_option
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SmoothRiemannianMetric I M) (p : M) (x : E) (w : ι → E) {t : ℝ}
    (ht : (show TangentSpace I p from t • x) ∈ expDomain (I := I) g p)
    (hperp : ∀ i, g.inner p x (w i) = 0) :
    curveDensity (I := I) g (radialCurve (I := I) g p x)
      (fun o => radialJacobiField (I := I) g p x (Option.elim o x w)) t =
      |t| * Real.sqrt (g.inner p x x) *
        curveDensity (I := I) g (radialCurve (I := I) g p x)
          (fun i => radialJacobiField (I := I) g p x (w i)) t := by
  unfold curveDensity
  rw [curveGram_det_radialJacobiField_option (I := I) g p x w ht hperp,
    Real.sqrt_mul (mul_nonneg (sq_nonneg t) (metric_inner_self_nonneg (I := I) g p x)),
    Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq_eq_abs]

theorem curveDensity_radialJacobiField_smul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SmoothRiemannianMetric I M) (p : M) (x : E) (w : ι → E) (t : ℝ)
    (ht : (show TangentSpace I p from t • x) ∈ expDomain (I := I) g p) :
    curveDensity (I := I) g (radialCurve (I := I) g p x)
      (fun i => radialJacobiField (I := I) g p x (w i)) t =
      |t| ^ Fintype.card ι *
        curveDensity (I := I) g (radialCurve (I := I) g p (t • x))
          (fun i => radialJacobiField (I := I) g p (t • x) (w i)) 1 := by
  let γ := radialCurve (I := I) g p (t • x)
  let V : ι → ∀ s, TangentSpace I (γ s) :=
    fun i => radialJacobiField (I := I) g p (t • x) (w i)
  let A : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) I
    (fun v : E => expMap (I := I) g p (show TangentSpace I p from v)) (t • x)
  have hcol (i : ι) : (radialJacobiField (I := I) g p x (w i) t : E) =
      t • (V i 1 : E) := by
    have hJ : (radialJacobiField (I := I) g p x (w i) t : E) = A (t • w i) :=
      radialJacobiField_eq_mfderiv_expMap (I := I) g p x (w i) t ht
    have hV : (V i 1 : E) = A (w i) :=
      radialJacobiField_one (I := I) g p (t • x) (w i) ht
    exact hJ.trans ((A.map_smul t (w i)).trans
      (congrArg (fun v : E => t • v) hV.symm))
  have hbridge :
      curveDensity (I := I) g (radialCurve (I := I) g p x)
        (fun i => radialJacobiField (I := I) g p x (w i)) t =
      curveDensity (I := I) g γ (fun i => t • V i) 1 := by
    unfold curveDensity curveGram
    apply congrArg Real.sqrt
    apply congrArg Matrix.det
    ext i j
    simp only [Matrix.of_apply, Pi.smul_apply]
    have hbase : γ 1 = radialCurve (I := I) g p x t := by
      simp only [γ, radialCurve, one_smul]
    rw [hbase]
    change g.inner (radialCurve (I := I) g p x t)
      (radialJacobiField (I := I) g p x (w i) t)
      (radialJacobiField (I := I) g p x (w j) t) =
      g.inner (radialCurve (I := I) g p x t) (t • (V i 1 : E)) (t • (V j 1 : E))
    rw [hcol, hcol]
  rw [hbridge, curveDensity_smul]

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
