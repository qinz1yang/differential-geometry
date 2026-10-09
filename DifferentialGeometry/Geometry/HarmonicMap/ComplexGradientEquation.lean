import DifferentialGeometry.Geometry.HarmonicMap.ConformalSource
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartBilinear
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

set_option autoImplicit false
noncomputable section

open Set Filter Manifold InnerProductSpace
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open scoped ContDiff Manifold Topology ComplexConjugate

namespace DifferentialGeometry.Geometry

private def complexGradient (f : ℂ → ℝ) (z : ℂ) : ℂ :=
  ⟨fderiv ℝ f z 1 / 2, -fderiv ℝ f z Complex.I / 2⟩

private theorem fderiv_complexGradient_apply {f : ℂ → ℝ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 f z) (v : ℂ) :
    fderiv ℝ (complexGradient f) z v =
      ⟨fderiv ℝ (fun q => fderiv ℝ f q 1) z v / 2,
        -fderiv ℝ (fun q => fderiv ℝ f q Complex.I) z v / 2⟩ := by
  have hd := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have ha := hd.clm_apply (differentiableAt_const (1 : ℂ))
  have hb := hd.clm_apply (differentiableAt_const Complex.I)
  have hp := (ha.hasFDerivAt.mul_const (2 : ℝ)⁻¹).prodMk
    (hb.hasFDerivAt.neg.mul_const (2 : ℝ)⁻¹)
  have hh := Complex.equivRealProdCLM.symm.hasFDerivAt.comp z hp
  change HasFDerivAt (complexGradient f) _ z at hh
  rw [hh.fderiv]
  apply Complex.ext <;>
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      smul_eq_mul, div_eq_mul_inv] <;> ring

private theorem complexGradient_dbar {f : ℂ → ℝ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 f z) :
    (fderiv ℝ (complexGradient f) z 1 +
        Complex.I * fderiv ℝ (complexGradient f) z Complex.I) / 2 =
      (Laplacian.laplacian f z : ℂ) / 4 := by
  have hd := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have hpartial (v w : ℂ) :
      fderiv ℝ (fun q => fderiv ℝ f q w) z v = fderiv ℝ (fderiv ℝ f) z v w := by
    rw [fderiv_clm_apply hd (differentiableAt_const w)]
    simp
  have hsym := hf.isSymmSndFDerivAt (by norm_num) (1 : ℂ) Complex.I
  rw [fderiv_complexGradient_apply hf, fderiv_complexGradient_apply hf,
    hpartial, hpartial, hpartial, hpartial,
    laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply]
  apply Complex.ext <;> simp [hsym] <;> ring

private theorem contDiffOn_complexGradient {f : ℂ → ℝ} {s : Set ℂ}
    (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s) :
    ContDiffOn ℝ ∞ (complexGradient f) s := by
  have hd := hf.fderiv_of_isOpen (m := ∞) hs (by simp)
  have ha := hd.clm_apply (contDiffOn_const (c := (1 : ℂ)))
  have hb := hd.clm_apply (contDiffOn_const (c := Complex.I))
  have hp := (ha.mul (contDiffOn_const (c := (2 : ℝ)⁻¹))).prodMk
    (hb.neg.mul (contDiffOn_const (c := (2 : ℝ)⁻¹)))
  refine (Complex.equivRealProdCLM.symm.contDiff.comp_contDiffOn hp).congr ?_
  intro x _
  apply Complex.ext <;> simp [complexGradient,
    Complex.equivRealProdCLM_symm_apply, div_eq_mul_inv]

private theorem symmetric_complex_sum {n : ℕ} (G : Fin n → Fin n → ℝ)
    (hG : ∀ i j, G i j = G j i) (a b : Fin n → ℝ) :
    (∑ i, ∑ j, (G i j : ℂ) * conj (⟨a i / 2, -b i / 2⟩ : ℂ) *
        (⟨a j / 2, -b j / 2⟩ : ℂ)) =
      (((∑ i, ∑ j, G i j * a i * a j) +
        (∑ i, ∑ j, G i j * b i * b j) : ℝ) : ℂ) / 4 := by
  have hre (i j : Fin n) :
      ((G i j : ℂ) * conj (⟨a i / 2, -b i / 2⟩ : ℂ) *
        (⟨a j / 2, -b j / 2⟩ : ℂ)).re =
        (G i j * a i * a j + G i j * b i * b j) / 4 := by
    simp
    ring
  have him (i j : Fin n) :
      ((G i j : ℂ) * conj (⟨a i / 2, -b i / 2⟩ : ℂ) *
        (⟨a j / 2, -b j / 2⟩ : ℂ)).im =
        (G i j * b i * a j - G i j * a i * b j) / 4 := by
    simp
    ring
  have hcross : (∑ i, ∑ j, G i j * b i * a j) =
      ∑ i, ∑ j, G i j * a i * b j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hG j i]
    ring
  apply Complex.ext
  · change Complex.reCLM _ = _
    simp only [map_sum]
    change (∑ i, ∑ j, ((G i j : ℂ) * conj (⟨a i / 2, -b i / 2⟩ : ℂ) *
      (⟨a j / 2, -b j / 2⟩ : ℂ)).re) = _
    simp_rw [hre]
    simp [← Finset.sum_div, Finset.sum_add_distrib]
  · change Complex.imCLM _ = _
    simp only [map_sum]
    change (∑ i, ∑ j, ((G i j : ℂ) * conj (⟨a i / 2, -b i / 2⟩ : ℂ) *
      (⟨a j / 2, -b j / 2⟩ : ℂ)).im) = _
    simp_rw [him]
    simp [← Finset.sum_div, Finset.sum_sub_distrib, hcross]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The complex derivative of the actual coordinate functions of a planar map,
using the same chart basis as the metric's Christoffel coefficients. -/
def chartComplexGradient (p : M) (U : ℂ → M)
    (k : Fin (Module.finrank ℝ E)) (z : ℂ) : ℂ :=
  complexGradient (fun q => chartCoordCLM E k (extChartAt 𝓘(ℝ, E) p (U q))) z

/-- The canonical coefficient matrix in the first-order complex gradient equation. -/
def chartComplexGradientCoefficient (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (p : M) (U : ℂ → M) (k j : Fin (Module.finrank ℝ E)) (z : ℂ) : ℂ :=
  -(∑ i, (chartChristoffel g p i j k (extChartAt 𝓘(ℝ, E) p (U z)) : ℂ) *
    conj (chartComplexGradient p U i z))

private theorem chartCoordCLM_eq_coord (k : Fin (Module.finrank ℝ E)) (v : E) :
    chartCoordCLM E k v = chartCoord (E := E) k v := by
  simp only [chartCoordCLM_apply, chartCoord, Module.Basis.equivFun_apply]

private theorem fderiv_chartCoord_comp {X : ℂ → E} {z : ℂ}
    (hX : DifferentiableAt ℝ X z) (k : Fin (Module.finrank ℝ E)) (v : ℂ) :
    fderiv ℝ (fun q => chartCoordCLM E k (X q)) z v =
      chartCoordCLM E k (fderiv ℝ X z v) := by
  have hh := congrArg (fun L : ℂ →L[ℝ] ℝ => L v)
    ((chartCoordCLM E k).hasFDerivAt.comp z hX.hasFDerivAt).fderiv
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply] using hh

/-- Harmonicity gives the actual complex first-order system even at a zero of the
disk differential. No branch factorization, conformality or immersion is assumed. -/
theorem chartComplexGradient_dbar_eq
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {z : ℂ}
    (hU : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 2 U z) {p : M}
    (hsrc : U z ∈ (chartAt E p).source) (hτ : planarTension g U z = 0)
    (k : Fin (Module.finrank ℝ E)) :
    (fderiv ℝ (chartComplexGradient p U k) z 1 +
        Complex.I * fderiv ℝ (chartComplexGradient p U k) z Complex.I) / 2 =
      ∑ j, chartComplexGradientCoefficient g p U k j z * chartComplexGradient p U j z := by
  let X : ℂ → E := extChartAt 𝓘(ℝ, E) p ∘ U
  have hX : ContDiffAt ℝ 2 X z :=
    ((contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := 2) hsrc).comp z hU).contDiffAt
  have hk : ContDiffAt ℝ 2 (fun q => chartCoordCLM E k (X q)) z :=
    (chartCoordCLM E k).contDiff.contDiffAt.comp z hX
  have hΔ := hX.laplacian_CLM_comp_left (l := chartCoordCLM E k)
  simp only [Function.comp_def] at hΔ
  have hchart := chart_planarTension g hU hsrc
  rw [hτ, map_zero] at hchart
  have hcoord := congrArg (chartCoordCLM E k) hchart
  simp only [map_zero, map_add] at hcoord
  change 0 = chartCoordCLM E k (Laplacian.laplacian X z) +
    chartCoordCLM E k (chartChristoffelContraction g p (fderiv ℝ X z 1)
      (fderiv ℝ X z 1) (X z)) +
    chartCoordCLM E k (chartChristoffelContraction g p (fderiv ℝ X z Complex.I)
      (fderiv ℝ X z Complex.I) (X z)) at hcoord
  have hcontraction (v w : E) :
      chartCoordCLM E k (chartChristoffelContraction g p v w (X z)) =
        ∑ i, ∑ j, chartChristoffel g p i j k (X z) *
          chartCoord (E := E) i v * chartCoord (E := E) j w := by
    rw [chartCoordCLM_eq_coord, Riemannian.AlongCurve.chartCoord_chartChristoffelContraction]
  rw [← hΔ, hcontraction, hcontraction] at hcoord
  let a (i : Fin (Module.finrank ℝ E)) := chartCoord (E := E) i (fderiv ℝ X z 1)
  let b (i : Fin (Module.finrank ℝ E)) := chartCoord (E := E) i (fderiv ℝ X z Complex.I)
  let G (i j : Fin (Module.finrank ℝ E)) := chartChristoffel g p i j k (X z)
  have hgrad (i : Fin (Module.finrank ℝ E)) :
      chartComplexGradient p U i z = (⟨a i / 2, -b i / 2⟩ : ℂ) := by
    unfold chartComplexGradient complexGradient
    change (⟨fderiv ℝ (fun q => chartCoordCLM E i (X q)) z 1 / 2,
      -fderiv ℝ (fun q => chartCoordCLM E i (X q)) z Complex.I / 2⟩ : ℂ) = _
    rw [fderiv_chartCoord_comp (hX.differentiableAt (by norm_num)),
      fderiv_chartCoord_comp (hX.differentiableAt (by norm_num)),
      chartCoordCLM_eq_coord, chartCoordCLM_eq_coord]
  have hreal : Laplacian.laplacian (fun q => chartCoordCLM E k (X q)) z =
      -((∑ i, ∑ j, G i j * a i * a j) + (∑ i, ∑ j, G i j * b i * b j)) := by
    change 0 = Laplacian.laplacian (fun q => chartCoordCLM E k (X q)) z +
      (∑ i, ∑ j, G i j * a i * a j) + (∑ i, ∑ j, G i j * b i * b j) at hcoord
    linarith
  have hsum := symmetric_complex_sum G (fun i j => chartChristoffel_symm g p i j k (X z)) a b
  change (fderiv ℝ (complexGradient (fun q => chartCoordCLM E k (X q))) z 1 +
    Complex.I * fderiv ℝ (complexGradient (fun q => chartCoordCLM E k (X q))) z Complex.I) / 2 = _
  rw [complexGradient_dbar hk, hreal]
  have hrhs :
      (∑ j, chartComplexGradientCoefficient g p U k j z * chartComplexGradient p U j z) =
        -(∑ i, ∑ j, (G i j : ℂ) * conj (⟨a i / 2, -b i / 2⟩ : ℂ) *
          (⟨a j / 2, -b j / 2⟩ : ℂ)) := by
    simp only [chartComplexGradientCoefficient, hgrad, neg_mul, Finset.sum_mul]
    change (∑ j, -(∑ i, (G i j : ℂ) * conj (⟨a i / 2, -b i / 2⟩ : ℂ) *
      (⟨a j / 2, -b j / 2⟩ : ℂ))) = _
    rw [Finset.sum_neg_distrib]
    congr 1
    exact Finset.sum_comm
  rw [hrhs, hsum]
  simp only [Complex.ofReal_neg, neg_div]

/-- On an actual open chart neighborhood of a smooth map, the canonical matrix
in its complex gradient equation is smooth on that same neighborhood. -/
theorem contDiffOn_chartComplexGradientCoefficient
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s) (p : M)
    (hsrc : ∀ z ∈ s, U z ∈ (chartAt E p).source)
    (k j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (chartComplexGradientCoefficient g p U k j) s := by
  let X : ℂ → E := extChartAt 𝓘(ℝ, E) p ∘ U
  have hX : ContDiffOn ℝ ∞ X s := by
    intro z hz
    exact (((contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := ∞) (hsrc z hz)).comp z
      (hU.contMDiffAt (hs.mem_nhds hz))).contDiffAt).contDiffWithinAt
  have hξ (i : Fin (Module.finrank ℝ E)) :
      ContDiffOn ℝ ∞ (chartComplexGradient p U i) s :=
    contDiffOn_complexGradient hs ((chartCoordCLM E i).contDiff.comp_contDiffOn hX)
  apply ContDiffOn.neg
  apply ContDiffOn.sum
  intro i _
  have hΓ : ContDiffOn ℝ ∞ (chartChristoffel g p i j k)
      (extChartAt 𝓘(ℝ, E) p).target := by
    simpa only [(isOpen_extChartAt_target (I := 𝓘(ℝ, E)) p).interior_eq] using
      chartChristoffel_contDiffOn_interior g p i j k
  have hΓX := hΓ.comp hX (fun z hz => (extChartAt 𝓘(ℝ, E) p).map_source
    (by simpa only [extChartAt_source] using hsrc z hz))
  exact (Complex.ofRealCLM.contDiff.comp_contDiffOn hΓX).mul
    (Complex.conjCLE.contDiff.comp_contDiffOn (hξ i))

end DifferentialGeometry.Geometry
