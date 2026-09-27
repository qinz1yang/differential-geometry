import DifferentialGeometry.Analysis.Integration.Measure.Chart.HaarBasis
import DifferentialGeometry.Geometry.Comparison.Volume.Bishop.Polar
import DifferentialGeometry.Geometry.Exponential.NormalCoordinates.Framed
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

noncomputable section

open Filter Metric Set
open scoped ENNReal Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace VolumeComparison

open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Integral.Measure
open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] [Nontrivial E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [T2Space M]
  [SigmaCompactSpace M] [T2Space (TangentBundle I M)]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private noncomputable def basisGram
    {V κ : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    (β : V →L[Real] V →L[Real] Real) (f : κ → V) : Matrix κ κ Real :=
  Matrix.of fun i j => β (f i) (f j)

private lemma gram_det_change
    {U V κ : Type*} [NormedAddCommGroup U] [NormedSpace Real U]
    [NormedAddCommGroup V] [NormedSpace Real V]
    [Fintype κ] [DecidableEq κ]
    (β : V →L[Real] V →L[Real] Real) (L : U →L[Real] V)
    (e B : Module.Basis κ Real U)
    (hgram : basisGram β (fun i => L (B i)) =
      (e.toMatrix B).transpose * basisGram β (fun i => L (e i)) * e.toMatrix B) :
    (basisGram β (fun i => L (B i))).det =
      (e.det B) ^ 2 * (basisGram β (fun i => L (e i))).det := by
  rw [hgram, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    Module.Basis.det_apply]
  ring

private noncomputable def frameBasis
    (g : SmoothRiemannianMetric I M) (p : M) :
    Module.Basis (Fin (Module.finrank Real E)) Real (TangentSpace I p) :=
  (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).map (normalFrame (I := I) g p).toLinearEquiv

private noncomputable def modelBasisAt (p : M) :
    Module.Basis (Fin (Module.finrank Real E)) Real (TangentSpace I p) :=
  DifferentialGeometry.Tensor.Coordinates.chartModelBasis E

omit [Nontrivial E] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma frame_gram_change
    (g : SmoothRiemannianMetric I M) (p : M) {z : E}
    (hz : z ∈ (framedExpDiffeo (I := I) g p).source) :
    (paramGramMatrix (I := I) g (framedExpDiffeo (I := I) g p) z).det =
      ((modelBasisAt (I := I) (E := E) p).det (frameBasis (I := I) g p)) ^ 2 *
        (normalGramMatrix (I := I) g p
          (tangentSpaceModelContinuousLinearEquiv (I := I) p
            (normalFrame (I := I) g p z))).det := by
  let q : M := framedExpDiffeo (I := I) g p z
  let D : TangentSpace I p →L[Real] TangentSpace I q :=
    mfderiv 𝓘(Real, E) I (expMapDiffeo (I := I) g p)
      (tangentSpaceModelContinuousLinearEquiv (I := I) p
        (normalFrame (I := I) g p z))
  have hframed :
      paramGramMatrix (I := I) g (framedExpDiffeo (I := I) g p) z =
        basisGram (g.inner q) (fun i => D (frameBasis (I := I) g p i)) := by
    ext i j
    simp only [paramGramMatrix_apply, basisGram, Matrix.of_apply, frameBasis,
      Module.Basis.map_apply, q, D]
    rw [mfderiv_framedExp (I := I) g p hz]
    rfl
  have hraw :
      basisGram (g.inner q) (fun i => D (modelBasisAt (I := I) (E := E) p i)) =
        normalGramMatrix (I := I) g p
          (tangentSpaceModelContinuousLinearEquiv (I := I) p
            (normalFrame (I := I) g p z)) := by
    ext i j
    simp only [basisGram, Matrix.of_apply, modelBasisAt, q, D]
    rw [framedExp_apply]
    rfl
  have hchange : basisGram (g.inner q)
        (fun i => D (frameBasis (I := I) g p i)) =
      ((modelBasisAt (I := I) (E := E) p).toMatrix
          (frameBasis (I := I) g p)).transpose *
        basisGram (g.inner q)
          (fun i => D (modelBasisAt (I := I) (E := E) p i)) *
          (modelBasisAt (I := I) (E := E) p).toMatrix
            (frameBasis (I := I) g p) := by
    classical
    ext i j
    change g.inner q (D (frameBasis (I := I) g p i))
      (D (frameBasis (I := I) g p j)) = _
    rw [show frameBasis (I := I) g p i =
        ∑ k, ((modelBasisAt (I := I) (E := E) p).repr
          (frameBasis (I := I) g p i)) k •
            modelBasisAt (I := I) (E := E) p k from
      ((modelBasisAt (I := I) (E := E) p).sum_repr
        (frameBasis (I := I) g p i)).symm]
    rw [show frameBasis (I := I) g p j =
        ∑ l, ((modelBasisAt (I := I) (E := E) p).repr
          (frameBasis (I := I) g p j)) l •
            modelBasisAt (I := I) (E := E) p l from
      ((modelBasisAt (I := I) (E := E) p).sum_repr
        (frameBasis (I := I) g p j)).symm]
    simp only [basisGram, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Module.Basis.toMatrix_apply, map_sum, map_smul,
      sum_apply, smul_apply, smul_eq_mul]
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l _
    ring_nf
  rw [hframed]
  rw [gram_det_change (g.inner q) D (modelBasisAt (I := I) (E := E) p)
    (frameBasis (I := I) g p) hchange]
  rw [hraw]

omit [NeZero (Module.finrank Real E)] [Nontrivial E] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
private lemma frame_det_ne
    (g : SmoothRiemannianMetric I M) (p : M) :
    (modelBasisAt (I := I) (E := E) p).det (frameBasis (I := I) g p) ≠ 0 :=
  ((modelBasisAt (I := I) (E := E) p).isUnit_det
    (frameBasis (I := I) g p)).ne_zero

omit [Nontrivial E] [T2Space M] [SigmaCompactSpace M]
  [NeZero (Module.finrank ℝ E)] in
theorem framedDens_zero
    (g : SmoothRiemannianMetric I M) (p : M) :
    paramDensity (I := I) g (framedExpDiffeo (I := I) g p) 0 =
      Real.sqrt (Matrix.of fun i j =>
        inner Real (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i) (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E j)).det := by
  rw [paramDensity_apply]
  apply congrArg Real.sqrt
  apply congrArg Matrix.det
  ext i j
  rw [paramGramMatrix_apply]
  change framedMetric (I := I) g p 0 (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i)
      (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E j) = _
  rw [framedMetric_zero]
  rfl

omit [Nontrivial E] [T2Space M] [SigmaCompactSpace M]
  [NeZero (Module.finrank ℝ E)] in
theorem framedDens_haar
    (g : SmoothRiemannianMetric I M) (p : M) :
    ENNReal.ofReal
          (paramDensity (I := I) g (framedExpDiffeo (I := I) g p) 0) •
        (modelHaar (E := E)) =
      (volume : Measure E) := by
  classical
  let e : Module.Basis (Fin (Module.finrank Real E)) Real E :=
    (stdOrthonormalBasis Real E).toBasis
  let b : Module.Basis (Fin (Module.finrank Real E)) Real E :=
    DifferentialGeometry.Tensor.Coordinates.chartModelBasis E
  let L : E →L[Real] E := ContinuousLinearMap.id Real E
  have hchange :
      basisGram (innerSL Real) (fun i => L (b i)) =
        (e.toMatrix b).transpose *
          basisGram (innerSL Real) (fun i => L (e i)) * e.toMatrix b := by
    ext i j
    change (innerSL Real) (L (b i)) (L (b j)) = _
    rw [show b i = ∑ k, (e.repr (b i)) k • e k from (e.sum_repr (b i)).symm]
    rw [show b j = ∑ l, (e.repr (b j)) l • e l from (e.sum_repr (b j)).symm]
    simp only [basisGram, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Module.Basis.toMatrix_apply, map_sum, map_smul,
      sum_apply, smul_apply, smul_eq_mul]
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l _
    ring_nf
  have heGram : basisGram (innerSL Real) (fun i => L (e i)) = 1 := by
    ext i j
    simp only [basisGram, Matrix.of_apply, L, ContinuousLinearMap.id_apply, e,
      OrthonormalBasis.coe_toBasis, Matrix.one_apply]
    exact (stdOrthonormalBasis Real E).inner_eq_ite i j
  have hdet :
      (Matrix.of fun i j => inner Real (b i) (b j)).det = (e.det b) ^ 2 := by
    have h := gram_det_change (innerSL Real) L e b hchange
    rw [heGram, Matrix.det_one, mul_one] at h
    change (Matrix.of fun i j => inner Real (b i) (b j)).det = (e.det b) ^ 2 at h
    exact h
  have hdensity :
      Real.sqrt (Matrix.of fun i j => inner Real (b i) (b j)).det =
        |e.det b| := by
    rw [hdet, Real.sqrt_sq_eq_abs]
  rw [framedDens_zero]
  change ENNReal.ofReal
      (Real.sqrt (Matrix.of fun i j => inner Real (b i) (b j)).det) •
        b.addHaar = (volume : Measure E)
  rw [hdensity]
  calc
    ENNReal.ofReal |e.det b| • b.addHaar = e.addHaar :=
      Module.Basis.det_smul_addHaar e b
    _ = (volume : Measure E) :=
      (stdOrthonormalBasis Real E).addHaar_eq_volume

omit [Nontrivial E] [T2Space M] [SigmaCompactSpace M]
  [NeZero (Module.finrank ℝ E)] in
theorem normalHaar_eq
    (g : SmoothRiemannianMetric I M) (p : M) :
    ENNReal.ofReal (normalChartDensity (I := I) g p 0) •
        (modelHaar (E := E)) =
      Measure.map (normalFrame (I := I) g p) (volume : Measure E) := by
  classical
  let b : Module.Basis (Fin (Module.finrank Real E)) Real E :=
    DifferentialGeometry.Tensor.Coordinates.chartModelBasis E
  let L : E ≃L[Real] E := normalFrame (I := I) g p
  let b' : Module.Basis (Fin (Module.finrank Real E)) Real E :=
    b.map L.toLinearEquiv
  let d : Real := b.det b'
  have hdensity :
      paramDensity (I := I) g (framedExpDiffeo (I := I) g p) 0 =
        |d| * normalChartDensity (I := I) g p 0 := by
    rw [paramDensity, normalDensity_det]
    rw [frame_gram_change (I := I) g p
      (zero_mem_framedExp_source (I := I) g p)]
    change Real.sqrt (d ^ 2 *
        (normalGramMatrix (I := I) g p (L 0)).det) =
      |d| * Real.sqrt (normalGramMatrix (I := I) g p 0).det
    rw [map_zero, Real.sqrt_mul (sq_nonneg d), Real.sqrt_sq_eq_abs]
  have hmap : Measure.map L (modelHaar (E := E)) = b'.addHaar := by
    simpa only [b, b', L, modelHaar] using
      Module.Basis.map_addHaar b L
  change ENNReal.ofReal (normalChartDensity (I := I) g p 0) •
      b.addHaar = Measure.map L (volume : Measure E)
  calc
    ENNReal.ofReal (normalChartDensity (I := I) g p 0) • b.addHaar =
        ENNReal.ofReal (normalChartDensity (I := I) g p 0) •
          (ENNReal.ofReal |d| • b'.addHaar) := by
      rw [Module.Basis.det_smul_addHaar b b']
    _ = (ENNReal.ofReal |d| *
          ENNReal.ofReal (normalChartDensity (I := I) g p 0)) •
        b'.addHaar := by
      rw [smul_smul, mul_comm]
    _ = ENNReal.ofReal
          (|d| * normalChartDensity (I := I) g p 0) • b'.addHaar := by
      rw [ENNReal.ofReal_mul (abs_nonneg d)]
    _ = ENNReal.ofReal
          (paramDensity (I := I) g (framedExpDiffeo (I := I) g p) 0) •
        b'.addHaar := by
      rw [hdensity]
    _ = Measure.map L
          (ENNReal.ofReal
              (paramDensity (I := I) g (framedExpDiffeo (I := I) g p) 0) •
            modelHaar (E := E)) := by
      rw [Measure.map_smul, hmap]
    _ = Measure.map L (volume : Measure E) := by
      rw [framedDens_haar (I := I) g p]

omit [Nontrivial E] in
omit [T2Space M]
  [SigmaCompactSpace M]
  [NeZero (Module.finrank ℝ E)] in
theorem exists_framed_den
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ c : Real, 0 < c ∧ ∀ z ∈ (framedExpDiffeo (I := I) g p).source,
      paramDensity (I := I) g (framedExpDiffeo (I := I) g p) z =
        c * normalChartDensity (I := I) g p
          (tangentSpaceModelContinuousLinearEquiv (I := I) p
            (normalFrame (I := I) g p z)) := by
  let d : Real := (modelBasisAt (I := I) (E := E) p).det
    (frameBasis (I := I) g p)
  refine ⟨|d|, abs_pos.mpr (by
    simpa only [d] using frame_det_ne (I := I) g p), ?_⟩
  intro z hz
  rw [paramDensity, normalDensity_det]
  rw [frame_gram_change (I := I) g p hz]
  rw [Real.sqrt_mul (sq_nonneg d)]
  rw [Real.sqrt_sq_eq_abs]

omit [Nontrivial E]
  [T2Space M]
  [SigmaCompactSpace M]
  [NeZero (Module.finrank ℝ E)] in
theorem framedRatio_anti
    (g : SmoothRiemannianMetric I M) (p : M) (u : E)
    (q : Real) (d : Nat) {b : Real}
    (hsrc : MapsTo (fun r : Real => r • u) (Ioo (0 : Real) b)
      (framedExpDiffeo (I := I) g p).source)
    (hnormal : AntitoneOn
      (fun r =>
        r ^ d * normalChartDensity (I := I) g p
            (r • tangentSpaceModelContinuousLinearEquiv (I := I) p
              (normalFrame (I := I) g p u)) /
          hyperbolicDensity q d r)
      (Ioo (0 : Real) b)) :
    AntitoneOn
      (fun r =>
        r ^ d * paramDensity (I := I) g (framedExpDiffeo (I := I) g p)
            (r • u) /
          hyperbolicDensity q d r)
      (Ioo (0 : Real) b) := by
  obtain ⟨c, hc, hdensity⟩ := exists_framed_den (I := I) g p
  intro r hr s hs hrs
  calc
    s ^ d * paramDensity (I := I) g (framedExpDiffeo (I := I) g p) (s • u) /
          hyperbolicDensity q d s =
        c * (s ^ d * normalChartDensity (I := I) g p
            (s • tangentSpaceModelContinuousLinearEquiv (I := I) p
              (normalFrame (I := I) g p u)) / hyperbolicDensity q d s) := by
      rw [hdensity (s • u) (hsrc hs), map_smul,
        (tangentSpaceModelContinuousLinearEquiv (I := I) p).map_smul]
      ring
    _ ≤ c * (r ^ d * normalChartDensity (I := I) g p
            (r • tangentSpaceModelContinuousLinearEquiv (I := I) p
              (normalFrame (I := I) g p u)) / hyperbolicDensity q d r) :=
      mul_le_mul_of_nonneg_left (hnormal hr hs hrs) hc.le
    _ = r ^ d * paramDensity (I := I) g
          (framedExpDiffeo (I := I) g p) (r • u) / hyperbolicDensity q d r := by
      rw [hdensity (r • u) (hsrc hr), map_smul,
        (tangentSpaceModelContinuousLinearEquiv (I := I) p).map_smul]
      ring

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
  [Nontrivial E] in
private lemma smul_mem_ball
    {R : Real} (hR : 0 < R) (u : sphere (0 : E) 1) (r : Ioi (0 : Real)) :
    r.1 • u.1 ∈ ball (0 : E) R ↔ r ∈ Iio (⟨R, hR⟩ : Ioi (0 : Real)) := by
  have hu : ‖u.1‖ = 1 := by
    simpa only [mem_sphere_zero_iff_norm] using u.2
  rw [mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg r.2.le, hu,
    mul_one]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem framedImage_polar
    (g : SmoothRiemannianMetric I M) (p : M)
    {B : Set E} (hB_meas : MeasurableSet B)
    (hB_source : B ⊆ (framedExpDiffeo (I := I) g p).source) :
    riemannianVolumeMeasure (I := I) (M := M) g
        (framedExpDiffeo (I := I) g p '' B) =
      ∫⁻ u : sphere (0 : E) 1,
        ∫⁻ r : Ioi (0 : Real),
          B.indicator
            (fun w => ENNReal.ofReal
              (paramDensity (I := I) g (framedExpDiffeo (I := I) g p) w))
            (r.1 • u.1)
          ∂(Measure.volumeIoiPow (Module.finrank Real E - 1))
        ∂(modelHaar (E := E)).toSphere := by
  let Ψ := framedExpDiffeo (I := I) g p
  let F : E → ENNReal :=
    B.indicator (fun w => ENNReal.ofReal (paramDensity (I := I) g Ψ w))
  have hcont : ContinuousOn (paramDensity (I := I) g Ψ) Ψ.source :=
    paramDensity_contOn (I := I) g Ψ
  have hF : AEMeasurable F (modelHaar (E := E)) := by
    apply (aemeasurable_indicator_iff hB_meas).mpr
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      ((hcont.mono hB_source).aemeasurable hB_meas)
  calc
    riemannianVolumeMeasure (I := I) (M := M) g (Ψ '' B) =
        ∫⁻ w in B, ENNReal.ofReal (paramDensity (I := I) g Ψ w)
          ∂(modelHaar (E := E)) := by
      exact riemannianVolumeMeasure_image_param_eq (I := I) (M := M) g Ψ
        hB_meas hB_source
    _ = ∫⁻ w, F w ∂(modelHaar (E := E)) := by
      rw [lintegral_indicator hB_meas]
    _ = ∫⁻ u : sphere (0 : E) 1,
          ∫⁻ r : Ioi (0 : Real), F (r.1 • u.1)
            ∂(Measure.volumeIoiPow (Module.finrank Real E - 1))
          ∂(modelHaar (E := E)).toSphere :=
      lintegral_polar (modelHaar (E := E)) F hF
    _ = ∫⁻ u : sphere (0 : E) 1,
          ∫⁻ r : Ioi (0 : Real),
            B.indicator
              (fun w => ENNReal.ofReal
                (paramDensity (I := I) g (framedExpDiffeo (I := I) g p) w))
              (r.1 • u.1)
            ∂(Measure.volumeIoiPow (Module.finrank Real E - 1))
          ∂(modelHaar (E := E)).toSphere := by
      rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem framedBall_polar
    (g : SmoothRiemannianMetric I M) (p : M) {R : Real} (hR : 0 < R)
    (hsource : ball (0 : E) R ⊆ (framedExpDiffeo (I := I) g p).source) :
    riemannianVolumeMeasure (I := I) (M := M) g
        (framedExpDiffeo (I := I) g p '' ball (0 : E) R) =
      ∫⁻ u : sphere (0 : E) 1,
        ∫⁻ r : Ioi (0 : Real) in Iio (⟨R, hR⟩ : Ioi (0 : Real)),
          ENNReal.ofReal
            (paramDensity (I := I) g (framedExpDiffeo (I := I) g p)
              (r.1 • u.1))
          ∂(Measure.volumeIoiPow (Module.finrank Real E - 1))
        ∂(modelHaar (E := E)).toSphere := by
  rw [framedImage_polar (I := I) g p measurableSet_ball hsource]
  apply lintegral_congr
  intro u
  rw [← lintegral_indicator measurableSet_Iio]
  apply lintegral_congr
  intro r
  by_cases hr : r ∈ Iio (⟨R, hR⟩ : Ioi (0 : Real))
  · have hb : r.1 • u.1 ∈ ball (0 : E) R :=
      (smul_mem_ball (E := E) hR u r).2 hr
    simp only [Set.indicator_of_mem hr, Set.indicator_of_mem hb]
  · have hb : r.1 • u.1 ∉ ball (0 : E) R := fun h =>
      hr ((smul_mem_ball (E := E) hR u r).1 h)
    simp only [Set.indicator_of_notMem hr, Set.indicator_of_notMem hb]

end VolumeComparison
end Riemannian
end Geometry
end DifferentialGeometry

end
