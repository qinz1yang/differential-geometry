import DifferentialGeometry.Geometry.HarmonicMap.ConformalSource
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskDifferential
import DifferentialGeometry.Analysis.Elliptic.MetricExtension
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Laplacian
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Classical
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Divergence.Local

section

noncomputable section
open Set Filter Bundle Manifold InnerProductSpace
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Operator
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
local notation "H" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private theorem toEuclidean_chartCoord (v : E) (k : Fin (Module.finrank ℝ E)) :
    toEuclidean v k = chartCoord k v := by
  unfold chartCoord chartModelBasis
  rw [Module.Basis.map_repr]
  change toEuclidean v k = (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).repr
    (toEuclidean v) k
  exact (EuclideanSpace.basisFun_repr _ _ _ k).symm


private theorem toEuclidean_christoffelContraction
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (p : M) (v w y : E)
    (k : Fin (Module.finrank ℝ E)) :
    toEuclidean (chartChristoffelContraction g p v w y) k =
      ∑ a, ∑ b, chartChristoffel g p a b k y * toEuclidean v a * toEuclidean w b := by
  rw [toEuclidean_chartCoord]
  simp only [chartChristoffelContraction, chartCoord, Module.Basis.repr_sum_self]
  simp only [toEuclidean_chartCoord, chartCoord]


theorem diskMapTension_eq_zero_of_chart_laplacian
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {z : ℂ}
    (hU : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 2 U z) {p : M}
    (hsrc : U z ∈ (chartAt E p).source)
    (heq : let X : ℂ → H := fun x => toEuclidean (extChartAt 𝓘(ℝ, E) p (U x))
      ∀ k, Laplacian.laplacian (fun x => X x k) z =
        -(∑ j : Fin 2, ∑ a, ∑ b,
          chartChristoffel g p a b k ((toEuclidean (E := E)).symm (X z)) *
            (fderiv ℝ X z (Complex.orthonormalBasisOneI j)) a *
            (fderiv ℝ X z (Complex.orthonormalBasisOneI j)) b)) :
    diskMapTension g U z = 0 := by
  let Y : ℂ → E := extChartAt 𝓘(ℝ, E) p ∘ U
  let X : ℂ → H := fun x => toEuclidean (Y x)
  have hY : ContDiffAt ℝ 2 Y z :=
    ((contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := 2) hsrc).comp z hU).contDiffAt
  have hd (v : ℂ) : fderiv ℝ X z v = toEuclidean (fderiv ℝ Y z v) := by
    rw [show X = (toEuclidean (E := E)) ∘ Y from rfl]
    have hh := (toEuclidean (E := E)).hasFDerivAt.comp z
      (hY.differentiableAt (by norm_num)).hasFDerivAt
    rw [hh.fderiv]
    rfl
  have hΔ (k : Fin (Module.finrank ℝ E)) :
      Laplacian.laplacian (fun x => X x k) z =
        toEuclidean (Laplacian.laplacian Y z) k := by
    let L : E →L[ℝ] ℝ := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (Module.finrank ℝ E) => ℝ) k).comp
      (toEuclidean (E := E)).toContinuousLinearMap
    exact hY.laplacian_CLM_comp_left (l := L)
  have hzero : Laplacian.laplacian Y z +
      chartChristoffelContraction g p (fderiv ℝ Y z 1) (fderiv ℝ Y z 1) (Y z) +
      chartChristoffelContraction g p (fderiv ℝ Y z Complex.I)
        (fderiv ℝ Y z Complex.I) (Y z) = 0 := by
    apply (toEuclidean (E := E)).injective
    ext k
    simp only [map_add, map_zero, PiLp.add_apply, PiLp.zero_apply]
    rw [← hΔ k, toEuclidean_christoffelContraction, toEuclidean_christoffelContraction]
    have hh := heq k
    change Laplacian.laplacian (fun x => X x k) z =
      -(∑ j : Fin 2, ∑ a, ∑ b,
        chartChristoffel g p a b k ((toEuclidean (E := E)).symm (X z)) *
          (fderiv ℝ X z (Complex.orthonormalBasisOneI j)) a *
          (fderiv ℝ X z (Complex.orthonormalBasisOneI j)) b) at hh
    have hXz : (toEuclidean (E := E)).symm (X z) = Y z :=
      ContinuousLinearEquiv.symm_apply_apply _ _
    rw [hXz] at hh
    simp only [Fin.sum_univ_two, Complex.coe_orthonormalBasisOneI,
      Matrix.cons_val_zero, Matrix.cons_val_one, hd] at hh
    change Laplacian.laplacian (fun x => X x k) z + _ + _ = 0
    linarith
  have hchart := chart_planarTension g hU hsrc
  have hb : U z ∈ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hsrc
  let τ := trivializationAt E (TangentSpace 𝓘(ℝ, E)) p
  apply (τ.continuousLinearEquivAt ℝ (U z) hb).injective
  simp only [Trivialization.coe_continuousLinearEquivAt_eq τ hb, map_zero]
  change (trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).continuousLinearMapAt ℝ (U z)
    (planarTension g U z) = 0
  exact hchart.trans hzero

end DifferentialGeometry.Geometry

end

end

section

noncomputable section

open Set Filter MeasureTheory Manifold InnerProductSpace Metric
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open scoped ContDiff Topology Manifold ENNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
local notation "V" => EuclideanSpace ℝ (Fin 2)
local notation "H" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

theorem diskMapTension_eq_zero_of_shifted_chart_weak_divergence
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {b : ℂ}
    (hU : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 2 U b) {p : M} {r : ℝ} (hr : 0 < r)
    (hsrc : MapsTo (fun x : V => U (b + Complex.orthonormalBasisOneI.repr.symm x))
      (ball (0 : V) r) (extChartAt 𝓘(ℝ, E) p).source) :
    let Z : V → H := fun x => toEuclidean
      (extChartAt 𝓘(ℝ, E) p (U (b + Complex.orthonormalBasisOneI.repr.symm x)))
    ContDiffOn ℝ 2 Z (ball (0 : V) r) →
    (hz : ∀ k, DeGiorgi.MemW1pWitness 2 (fun x => Z x k) (ball (0 : V) r)) →
    (∀ k, DeGiorgi.HasWeakDiv (fun x => -(∑ j : Fin 2, ∑ a, ∑ c,
      chartChristoffel g p a c k ((toEuclidean (E := E)).symm (Z x)) *
        (hz a).weakGrad x j * (hz c).weakGrad x j)) (hz k).weakGrad (ball (0 : V) r)) →
    diskMapTension g U b = 0 := by
  intro Z hZ2 hz hdiv0
  let e := Complex.orthonormalBasisOneI.repr.symm
  let X : ℂ → H := fun x => toEuclidean (extChartAt 𝓘(ℝ, E) p (U x))
  let T : ℂ → H := fun x => X (b + x)
  let R := r / 2
  have hR : 0 < R := half_pos hr
  have hball : closedBall (0 : V) R ⊆ ball 0 r := closedBall_subset_ball (half_lt_self hr)
  have hsub : ball (0 : V) R ⊆ ball 0 r := ball_subset_closedBall.trans hball
  let D (k : Fin (Module.finrank ℝ E)) (x : V) :=
    DeGiorgi.smoothGradField (fun y => Z y k) x
  have hDae (k : Fin (Module.finrank ℝ E)) :
      (hz k).weakGrad =ᵐ[volume.restrict (ball (0 : V) R)] D k :=
    (hz k).weakGrad_ae_eq_smoothGradField_on_ball (by norm_num) isOpen_ball
      ((contDiff_piLp_apply (p := 2) (i := k)).comp_contDiffOn
        (hZ2.of_le (by norm_num))) hball
  have hcolumn (k : Fin (Module.finrank ℝ E)) (x : V) (hx : x ∈ ball (0 : V) R) (j : Fin 2) :
      D k x j = (fderiv ℝ Z x (EuclideanSpace.single j 1)) k := by
    let L : H →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin (Module.finrank ℝ E) => ℝ) k
    have hh := L.hasFDerivAt.comp x
      ((hZ2.contDiffAt (isOpen_ball.mem_nhds (hsub hx))).differentiableAt
        (by norm_num)).hasFDerivAt
    change fderiv ℝ (L ∘ Z) x (EuclideanSpace.single j 1) = _
    rw [hh.fderiv]
    rfl
  let Γ (k a c : Fin (Module.finrank ℝ E)) (y : H) :=
    chartChristoffel g p a c k ((toEuclidean (E := E)).symm y)
  let Fk (k : Fin (Module.finrank ℝ E)) (x : V) :=
    -(∑ j : Fin 2, ∑ a, ∑ c, Γ k a c (Z x) * D a x j * D c x j)
  have hFk (k : Fin (Module.finrank ℝ E)) : ContinuousOn (Fk k) (ball (0 : V) R) := by
    have hDcont (a : Fin (Module.finrank ℝ E)) (j : Fin 2) :
        ContinuousOn (fun x => D a x j) (ball (0 : V) R) := by
      have ha : ContDiffOn ℝ 2 (fun x => Z x a) (ball (0 : V) R) :=
        (contDiff_piLp_apply (p := 2) (i := a)).comp_contDiffOn (hZ2.mono hsub)
      exact (ha.continuousOn_fderiv_of_isOpen isOpen_ball (by norm_num)).clm_apply
        continuousOn_const
    have hΓ (a c : Fin (Module.finrank ℝ E)) :
        ContinuousOn (fun x => Γ k a c (Z x)) (ball (0 : V) R) := by
      have hg := (chartChristoffel_contDiffOn_interior g p a c k).continuousOn
      rw [(isOpen_extChartAt_target (I := 𝓘(ℝ, E)) p).interior_eq] at hg
      apply hg.comp ((toEuclidean (E := E)).symm.continuous.comp_continuousOn
        (hZ2.continuousOn.mono hsub))
      intro x hx
      change (toEuclidean (E := E)).symm (toEuclidean
        (extChartAt 𝓘(ℝ, E) p (U (b + e x)))) ∈ (extChartAt 𝓘(ℝ, E) p).target
      rw [ContinuousLinearEquiv.symm_apply_apply]
      exact (extChartAt 𝓘(ℝ, E) p).map_source (hsrc (hsub hx))
    exact (continuousOn_finsetSum _ fun j _ => continuousOn_finsetSum _ fun a _ =>
      continuousOn_finsetSum _ fun c _ => ((hΓ a c).mul (hDcont a j)).mul (hDcont c j)).neg
  have hdiv (k : Fin (Module.finrank ℝ E)) :
      DeGiorgi.HasWeakDiv (Fk k) (hz k).weakGrad (ball (0 : V) R) := by
    apply ((hdiv0 k).restrict hsub).congr_ae _ (EventuallyEq.rfl)
    filter_upwards [ae_all_iff.mpr hDae] with x hx
    simp only [Fk, Γ, hx]
  have hLap (k : Fin (Module.finrank ℝ E)) :
      EqOn (Laplacian.laplacian (fun x => Z x k)) (Fk k) (ball (0 : V) R) :=
    laplacian_eq_of_contDiffOn_of_memW1p_hasWeakDiv isOpen_ball (by norm_num)
      ((hz k).restrict isOpen_ball hsub)
      ((contDiff_piLp_apply (p := 2) (i := k)).comp_contDiffOn (hZ2.mono hsub))
      (hFk k) (hdiv k)
  have hcenter : (0 : V) ∈ ball (0 : V) R := mem_ball_self hR
  have hZ0 : Z 0 = X b := by simp only [Z, X, map_zero, add_zero]
  have hds (j : Fin 2) : fderiv ℝ Z 0 (EuclideanSpace.single j 1) =
      fderiv ℝ X b (Complex.orthonormalBasisOneI j) := by
    rw [show Z = T ∘ e.toContinuousLinearEquiv from rfl,
      e.toContinuousLinearEquiv.comp_right_fderiv]
    change fderiv ℝ T (e 0) (e (EuclideanSpace.single j 1)) = _
    rw [map_zero, show e (EuclideanSpace.single j 1) = Complex.orthonormalBasisOneI j by
      apply e.symm.injective
      rw [e.symm_apply_apply]
      exact (Complex.orthonormalBasisOneI.repr_self j).symm]
    dsimp only [T]
    rw [fderiv_comp_add_left, add_zero]
  have hLapshift (k : Fin (Module.finrank ℝ E)) :
      Laplacian.laplacian (fun x => Z x k) 0 = Laplacian.laplacian (fun x => X x k) b := by
    rw [show (fun x => Z x k) = (fun x => T x k) ∘ e from rfl,
      LinearIsometryEquiv.laplacian_comp, map_zero]
    have ht := iteratedFDeriv_comp_add_left (𝕜 := ℝ) (f := fun x => X x k) 2 b 0
    simp only [T, laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, ht, add_zero]
  apply diskMapTension_eq_zero_of_chart_laplacian g hU (p := p)
    (by simpa only [extChartAt_source, map_zero, add_zero] using hsrc (mem_ball_self hr))
  dsimp only
  intro k
  have hh := hLap k hcenter
  rw [hLapshift] at hh
  simpa only [Fk, Γ, hcolumn _ 0 hcenter, hZ0, hds] using hh

end DifferentialGeometry.Geometry

end

end
