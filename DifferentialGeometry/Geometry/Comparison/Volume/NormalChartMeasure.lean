import DifferentialGeometry.Analysis.Integration.Measure.ParamEvaluation
import DifferentialGeometry.Geometry.Comparison.NormalCoordinates
import DifferentialGeometry.Geometry.Exponential.JacobiVariation

set_option linter.unusedSectionVars false

/-!
# Normal-chart volume evaluation

This file starts Stage V1 of the volume-comparison lane by specializing the
Integration-layer parametrized volume formula to the exponential partial
diffeomorphism that defines normal coordinates.
-/

noncomputable section

open Set Bundle
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace VolumeComparison

open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

section NormalChart

variable [I.Boundaryless] [CompleteSpace E] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)]

/-- The normal-coordinate density is the parametrized density of the exponential
partial diffeomorphism.

Mathematically this is `sqrt(det g_ij)` in normal coordinates.  The definition is
valid on the whole model space, while the volume formula only consumes it on
sets inside `(expMapDiffeo g p).source`.  V1b will identify this same density
with the Gram determinant of Jacobi fields along radial geodesics. -/
def normalChartDensity (g : SmoothRiemannianMetric I M) (p : M) : E → ℝ :=
  paramDensity (I := I) g (expMapDiffeo (I := I) g p)

@[simp] lemma normalChartDensity_apply
    (g : SmoothRiemannianMetric I M) (p : M) (w : E) :
    normalChartDensity (I := I) g p w =
      paramDensity (I := I) g (expMapDiffeo (I := I) g p) w := rfl

/-- The normal-coordinate Gram matrix is the parametrized Gram matrix of the
exponential-side partial diffeomorphism. -/
def normalGramMatrix (g : SmoothRiemannianMetric I M) (p : M) :
    E → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  paramGramMatrix (I := I) g (expMapDiffeo (I := I) g p)

@[simp] lemma normalGram_apply
    (g : SmoothRiemannianMetric I M) (p : M) (w : E)
    (i j : Fin (Module.finrank ℝ E)) :
    normalGramMatrix (I := I) g p w i j =
      g.inner (expMapDiffeo (I := I) g p w)
        (mfderiv 𝓘(ℝ, E) I (expMapDiffeo (I := I) g p) w ((chartModelBasis E) i))
        (mfderiv 𝓘(ℝ, E) I (expMapDiffeo (I := I) g p) w ((chartModelBasis E) j)) :=
  rfl

/-- The normal-coordinate density is the square root of the determinant of the
normal-coordinate Gram matrix. -/
lemma normalDensity_det
    (g : SmoothRiemannianMetric I M) (p : M) (w : E) :
    normalChartDensity (I := I) g p w =
      Real.sqrt (normalGramMatrix (I := I) g p w).det :=
  rfl

omit [T2Space M] [SigmaCompactSpace M] in
/-- The normal-coordinate Gram matrix is continuous at the chart centre. -/
lemma normalGram_contAt
    (g : SmoothRiemannianMetric I M) (p : M) :
    ContinuousAt (normalGramMatrix (I := I) g p) 0 := by
  let Ψ := expMapDiffeo (I := I) g p
  let U : Set E := Ψ.source ∩
    Ψ ⁻¹' (trivializationAt E (TangentSpace I) p).baseSet
  have hUopen : IsOpen U := by
    dsimp only [U]
    exact Ψ.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage
      Ψ.open_source (trivializationAt E (TangentSpace I) p).open_baseSet
  have hzero_src : (0 : E) ∈ Ψ.source := by
    simpa only [Ψ] using zero_mem_expMapDiffeo_source (I := I) g p
  have hzeroU : (0 : E) ∈ U := by
    refine ⟨hzero_src, ?_⟩
    change Ψ (0 : E) ∈ (trivializationAt E (TangentSpace I) p).baseSet
    rw [show Ψ (0 : E) = p by
      simpa only [Ψ] using expMapDiffeo_zero (I := I) g p]
    exact mem_baseSet_trivializationAt E (TangentSpace I) p
  have hcont : ContinuousOn (normalGramMatrix (I := I) g p) U := by
    simpa only [normalGramMatrix, Ψ] using
      paramGram_contOn (I := I) g p Ψ hUopen
        Set.inter_subset_left (fun w hw => hw.2)
  exact hcont.continuousAt (hUopen.mem_nhds hzeroU)

/-- The radial variation field along the geodesic launched by `x`.

At `t = 1`, this is the vector-slot derivative of the exponential map; see
`radialJacobi_one`. -/
def radialJacobiField (g : SmoothRiemannianMetric I M) (p : M)
    (x w : E) (t : ℝ) :
    TangentSpace I
      ((expMap (I := I) g p (show TangentSpace I p from (t • x)) : M)) :=
  mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ =>
    (expMap (I := I) g p
      (show TangentSpace I p from (t • (x + s • w))) : M)) 0 (1 : ℝ)

/-- The packaged radial Jacobi field vanishes at the centre. -/
lemma radialJacobi_zero
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) :
    radialJacobiField (I := I) g p x w 0 = 0 := by
  simpa [radialJacobiField] using
    DifferentialGeometry.Geometry.Riemannian.radial_jacobi_zero (I := I) g p x w

/-- Radius form of the Jacobi equation for the packaged radial Jacobi field. -/
theorem exists_radialJacobi_radius
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ r : ℝ, 0 < r ∧ ∀ x w : E, ‖x‖ < r → ‖w‖ < r → ∀ t₀ ∈ Set.Ioo (0 : ℝ) 1,
      IsJacobiAt (I := I) g
        (fun v : ℝ => (expMap (I := I) g p (show TangentSpace I p from (v • x)) : M))
        (radialJacobiField (I := I) g p x w) t₀ := by
  simpa [radialJacobiField] using
    DifferentialGeometry.Geometry.Riemannian.exists_radial_jacobi_radius (I := I) g p

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Radius form of the endpoint Jacobi equation for the packaged radial Jacobi
field. -/
theorem exists_radialJacobi_zero_radius
    [PseudoEMetricSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ r : ℝ, 0 < r ∧ ∀ x w : E, ‖x‖ < r → ‖w‖ < r →
      IsJacobiAt (I := I) g
        (fun v : ℝ => (expMap (I := I) g p (show TangentSpace I p from (v • x)) : M))
        (radialJacobiField (I := I) g p x w) 0 := by
  simpa [radialJacobiField] using
    DifferentialGeometry.Geometry.Riemannian.exists_jacobi_zero (I := I) g hEnorm p

/-- Radius form of the second initial condition for the packaged radial Jacobi
field. -/
theorem exists_radialJacobi_deriv_radius
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ r : ℝ, 0 < r ∧ ∀ x w : E, ‖x‖ < r → ‖w‖ < r →
      (covDerivAlong (I := I) g
        (fun v : ℝ => (expMap (I := I) g p (show TangentSpace I p from (v • x)) : M))
        (radialJacobiField (I := I) g p x w) 0 : E) = w := by
  simpa [radialJacobiField] using
    DifferentialGeometry.Geometry.Riemannian.exists_radial_jacobi_deriv_radius (I := I) g p

/-- The Gram matrix of the endpoint radial Jacobi fields generated by the fixed
model basis. -/
def radialJacobiGram (g : SmoothRiemannianMetric I M) (p : M) (x : E) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun i j =>
    g.inner (expMap (I := I) g p (show TangentSpace I p from x))
      (radialJacobiField (I := I) g p x ((chartModelBasis E) i) 1)
      (radialJacobiField (I := I) g p x ((chartModelBasis E) j) 1)

@[simp] lemma radialJacobiGram_apply
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    (i j : Fin (Module.finrank ℝ E)) :
    radialJacobiGram (I := I) g p x i j =
      g.inner (expMap (I := I) g p (show TangentSpace I p from x))
        (radialJacobiField (I := I) g p x ((chartModelBasis E) i) 1)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) j) 1) :=
  rfl

/-- Endpoint identification of the packaged radial Jacobi field. -/
lemma radialJacobi_one
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E)
    (hx : ‖x‖ < expMapC2Radius (I := I) g p) :
    radialJacobiField (I := I) g p x w 1 =
      mfderiv 𝓘(ℝ, E) I
        (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M)) x w := by
  simpa [radialJacobiField] using
    DifferentialGeometry.Geometry.Riemannian.radial_jacobi_one (I := I) g p x w hx

/-- Radial time scaling can be transferred to both launch vectors and then
evaluated at time one.  This is an algebraic identity of the defining
exponential variations, valid at every scale; the radial Gram comparison uses
it inside the source of `expMapDiffeo` to obtain linear independence. -/
lemma radialJacobi_scale
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) (t : ℝ) :
    radialJacobiField (I := I) g p x w t =
      radialJacobiField (I := I) g p (t • x) (t • w) 1 := by
  have hfun :
      (fun s : ℝ => (expMap (I := I) g p
        (show TangentSpace I p from t • (x + s • w)) : M)) =
      fun s : ℝ => (expMap (I := I) g p
        (show TangentSpace I p from (1 : ℝ) • (t • x + s • (t • w))) : M) := by
    funext s
    apply congrArg (fun v : E =>
      (expMap (I := I) g p (show TangentSpace I p from v) : M))
    module
  unfold radialJacobiField
  rw [hfun]
  rfl

/-- At any radial time in the local `C²` range, the radial Jacobi field is the
exponential differential applied to the scaled variation direction. -/
lemma radialJacobi_at
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) (t : ℝ)
    (htx : ‖t • x‖ < expMapC2Radius (I := I) g p) :
    radialJacobiField (I := I) g p x w t =
      mfderiv 𝓘(ℝ, E) I
        (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M))
        (t • x) (t • w) := by
  rw [radialJacobi_scale (I := I) g p x w t,
    radialJacobi_one (I := I) g p (t • x) (t • w) htx]

/-- Radial Jacobi fields preserve finite linear combinations at every time in
the local `C²` range. -/
lemma radialJacobi_sum_at
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    (w : ι → E) (c : ι → ℝ) (t : ℝ)
    (htx : ‖t • x‖ < expMapC2Radius (I := I) g p) :
    radialJacobiField (I := I) g p x (∑ i, c i • w i) t =
      ∑ i, c i • radialJacobiField (I := I) g p x (w i) t := by
  classical
  rw [radialJacobi_at (I := I) g p x (∑ i, c i • w i) t htx]
  set L :=
    mfderiv 𝓘(ℝ, E) I
      (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M))
      (t • x)
  have hinput : t • ∑ i, c i • w i = ∑ i, c i • (t • w i) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    module
  rw [hinput]
  have hmap : L (∑ i, c i • (t • w i)) =
      ∑ i, L (c i • (t • w i)) := by
    simpa only using
      (map_sum L (fun i : ι => c i • (t • w i)) Finset.univ)
  calc
    L (∑ i, c i • (t • w i)) = ∑ i, L (c i • (t • w i)) := hmap
    _ = ∑ i, c i • radialJacobiField (I := I) g p x (w i) t := by
      refine Finset.sum_congr rfl fun i _ => ?_
      calc
        L (c i • (t • w i)) = c i • L (t • w i) :=
          L.map_smul (c i) (t • w i)
        _ = c i • radialJacobiField (I := I) g p x (w i) t := by
          rw [radialJacobi_at (I := I) g p x (w i) t htx]

/-- Endpoint radial Jacobi fields are linear in the variation direction. -/
lemma radialJacobi_one_smul
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) (a : ℝ)
    (hx : ‖x‖ < expMapC2Radius (I := I) g p) :
    radialJacobiField (I := I) g p x (a • w) 1 =
      a • radialJacobiField (I := I) g p x w 1 := by
  rw [radialJacobi_one (I := I) g p x (a • w) hx,
    radialJacobi_one (I := I) g p x w hx]
  exact (mfderiv 𝓘(ℝ, E) I
    (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M)) x).map_smul a w

/-- Endpoint radial Jacobi fields preserve arbitrary finite linear
combinations of variation directions. -/
lemma radialJacobi_sum
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    (w : ι → E) (c : ι → ℝ)
    (hx : ‖x‖ < expMapC2Radius (I := I) g p) :
    radialJacobiField (I := I) g p x (∑ i, c i • w i) 1 =
      ∑ i, c i • radialJacobiField (I := I) g p x (w i) 1 := by
  classical
  rw [radialJacobi_one (I := I) g p x (∑ i, c i • w i) hx]
  set L :=
    mfderiv 𝓘(ℝ, E) I
      (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M)) x
  change L (∑ i, c i • w i) =
    ∑ i, c i • radialJacobiField (I := I) g p x (w i) 1
  rw [map_sum L]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [radialJacobi_one (I := I) g p x (w i) hx]
  exact L.map_smul (c i) (w i)

/-- Endpoint radial Jacobi fields are linear over finite combinations of
variation directions. -/
lemma radialJacobi_one_sum
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    (c : Fin (Module.finrank ℝ E) → ℝ)
    (hx : ‖x‖ < expMapC2Radius (I := I) g p) :
    radialJacobiField (I := I) g p x
        (∑ i, c i • (chartModelBasis E) i) 1 =
      ∑ i, c i • radialJacobiField (I := I) g p x ((chartModelBasis E) i) 1 := by
  exact radialJacobi_sum (I := I) g p x (chartModelBasis E) c hx

/-- On the source of the exponential partial diffeomorphism, its derivative is
the derivative of the actual exponential map. -/
lemma expDiffeo_mfderiv
    (g : SmoothRiemannianMetric I M) (p : M) {x : E}
    (hx : x ∈ (expMapDiffeo (I := I) g p).source) :
    mfderiv 𝓘(ℝ, E) I (expMapDiffeo (I := I) g p) x =
      mfderiv 𝓘(ℝ, E) I
        (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M)) x := by
  have hsrc : ∀ᶠ y in 𝓝 x, y ∈ (expMapDiffeo (I := I) g p).source :=
    (expMapDiffeo (I := I) g p).open_source.mem_nhds hx
  have hagree :
      (fun y : E => expMapDiffeo (I := I) g p y) =ᶠ[𝓝 x]
        (fun y : E => (expMap (I := I) g p (show TangentSpace I p from y) : M)) := by
    filter_upwards [hsrc] with y hy
    exact expMapDiffeo_apply_eq (I := I) g p hy
  exact hagree.mfderiv_eq

/-- The normal-coordinate Gram matrix is the Gram matrix of the radial Jacobi
fields at parameter `1`, for points where both the normal chart and the local
Jacobi construction apply. -/
lemma normalGram_radial
    (g : SmoothRiemannianMetric I M) (p : M) {x : E}
    (hxsrc : x ∈ (expMapDiffeo (I := I) g p).source)
    (hxrad : ‖x‖ < expMapC2Radius (I := I) g p)
    (i j : Fin (Module.finrank ℝ E)) :
    normalGramMatrix (I := I) g p x i j =
      g.inner (expMap (I := I) g p (show TangentSpace I p from x))
        (radialJacobiField (I := I) g p x ((chartModelBasis E) i) 1)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) j) 1) := by
  rw [normalGram_apply]
  have hbase := expMapDiffeo_apply_eq (I := I) g p hxsrc
  have hderiv := expDiffeo_mfderiv (I := I) g p hxsrc
  have hi :
      mfderiv 𝓘(ℝ, E) I (expMapDiffeo (I := I) g p) x ((chartModelBasis E) i) =
        mfderiv 𝓘(ℝ, E) I
          (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M))
          x ((chartModelBasis E) i) :=
    congrArg (fun L => L ((chartModelBasis E) i)) hderiv
  have hj :
      mfderiv 𝓘(ℝ, E) I (expMapDiffeo (I := I) g p) x ((chartModelBasis E) j) =
        mfderiv 𝓘(ℝ, E) I
          (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M))
          x ((chartModelBasis E) j) :=
    congrArg (fun L => L ((chartModelBasis E) j)) hderiv
  rw [hi, hj, hbase]
  rw [← radialJacobi_one (I := I) g p x ((chartModelBasis E) i) hxrad]
  rw [← radialJacobi_one (I := I) g p x ((chartModelBasis E) j) hxrad]

/-- Matrix form of the normal-Gram/radial-Jacobi identification. -/
lemma normalGram_radialMat
    (g : SmoothRiemannianMetric I M) (p : M) {x : E}
    (hxsrc : x ∈ (expMapDiffeo (I := I) g p).source)
    (hxrad : ‖x‖ < expMapC2Radius (I := I) g p) :
    normalGramMatrix (I := I) g p x = radialJacobiGram (I := I) g p x := by
  ext i j
  exact normalGram_radial (I := I) g p hxsrc hxrad i j

/-- Density form of the normal-Gram/radial-Jacobi identification. -/
lemma normalDensity_radial
    (g : SmoothRiemannianMetric I M) (p : M) {x : E}
    (hxsrc : x ∈ (expMapDiffeo (I := I) g p).source)
    (hxrad : ‖x‖ < expMapC2Radius (I := I) g p) :
    normalChartDensity (I := I) g p x =
      Real.sqrt (radialJacobiGram (I := I) g p x).det := by
  rw [normalDensity_det, normalGram_radialMat (I := I) g p hxsrc hxrad]

/-- V1a normal-chart volume evaluation.

If a measurable manifold set `A` lies in the source of the normal chart at `p`,
then its Riemannian volume is the model Haar integral over its normal-coordinate
image, with density `normalChartDensity`.  This is true because
`normalChartAt g p` is the inverse of the exponential-side partial
diffeomorphism `expMapDiffeo g p`, so the Integration-layer V0 theorem applies
directly.  V1b consumes this statement by replacing `normalChartDensity` with
the Jacobi-field Gram determinant. -/
theorem normalChart_volume_eq
    (g : SmoothRiemannianMetric I M) (p : M)
    {A : Set M} (hA_meas : MeasurableSet A)
    (hA_source : A ⊆ (normalChartAt (I := I) g p).source) :
    riemannianVolumeMeasure (I := I) (M := M) g A =
      ∫⁻ w in (normalChartAt (I := I) g p) '' A,
        ENNReal.ofReal (normalChartDensity (I := I) g p w)
          ∂(modelHaar (E := E)) := by
  have hA_target : A ⊆ (expMapDiffeo (I := I) g p).target := by
    simpa [normalChartAt_source_eq (I := I) g p] using hA_source
  simpa [normalChartAt, normalChartDensity] using
    riemannianVolumeMeasure_param_target_eq (I := I) (M := M) g
      (expMapDiffeo (I := I) g p) hA_meas hA_target

/-- V1b normal-chart volume evaluation with the density expressed by endpoint
radial Jacobi fields. -/
theorem normalChart_volume_radial
    (g : SmoothRiemannianMetric I M) (p : M)
    {A : Set M} (hA_meas : MeasurableSet A)
    (hA_source : A ⊆ (normalChartAt (I := I) g p).source)
    (hA_rad : (normalChartAt (I := I) g p) '' A ⊆
      Metric.ball (0 : E) (expMapC2Radius (I := I) g p)) :
    riemannianVolumeMeasure (I := I) (M := M) g A =
      ∫⁻ w in (normalChartAt (I := I) g p) '' A,
        ENNReal.ofReal (Real.sqrt (radialJacobiGram (I := I) g p w).det)
          ∂(modelHaar (E := E)) := by
  have hA_target : A ⊆ (expMapDiffeo (I := I) g p).target := by
    simpa [normalChartAt_source_eq (I := I) g p] using hA_source
  have hB_meas : MeasurableSet ((normalChartAt (I := I) g p) '' A) := by
    simpa [normalChartAt] using
      measurableSet_symm_image_param (I := I) (M := M)
        (Ψ := expMapDiffeo (I := I) g p) hA_meas hA_target
  rw [normalChart_volume_eq (I := I) (M := M) g p hA_meas hA_source]
  refine MeasureTheory.setLIntegral_congr_fun hB_meas ?_
  intro w hw
  have hwsrc : w ∈ (expMapDiffeo (I := I) g p).source := by
    rcases hw with ⟨y, hyA, hyw⟩
    have hy_source : y ∈ (normalChartAt (I := I) g p).source := hA_source hyA
    have hw_target : normalChartAt (I := I) g p y ∈
        (normalChartAt (I := I) g p).target :=
      (normalChartAt (I := I) g p).map_source hy_source
    rw [hyw] at hw_target
    simpa [normalChartAt_target_eq (I := I) g p] using hw_target
  have hwrad : ‖w‖ < expMapC2Radius (I := I) g p := by
    have hwball : w ∈ Metric.ball (0 : E) (expMapC2Radius (I := I) g p) := hA_rad hw
    simpa [Metric.mem_ball, dist_eq_norm] using hwball
  simpa using
    congrArg ENNReal.ofReal (normalDensity_radial (I := I) g p hwsrc hwrad)

end NormalChart

end VolumeComparison
end Riemannian
end Geometry
end DifferentialGeometry
