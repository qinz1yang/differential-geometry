import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.W.Variation.Laplacian
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.ConjugateHeat.Product
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Algebra.MetricShift
import DifferentialGeometry.Geometry.Curvature.Bochner.Scalar.TensorFormula
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.W.Variation.Flow

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Entropy

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem laplacian_smooth_linear_combination
    (G : MetricConnectionFamily (I := I) (M := M) ℝ) (t : ℝ)
    (a b c d : ℝ) (f h k : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hk : ContMDiff I 𝓘(ℝ, ℝ) ∞ k) (x : M) :
    laplacianAt G t (fun y => a * f y + b * h y + c * k y + d) x =
      a * laplacianAt G t f x + b * laplacianAt G t h x + c * laplacianAt G t k x := by
  let fd := hf.mdifferentiable (by simp)
  let hd := hh.mdifferentiable (by simp)
  let kd := hk.mdifferentiable (by simp)
  have hfa : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y => a * f y) := contMDiff_const.mul hf
  have hhb : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y => b * h y) := contMDiff_const.mul hh
  have hkc : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y => c * k y) := contMDiff_const.mul hk
  unfold laplacianAt
  rw [show (fun y => a * f y + b * h y + c * k y + d) =
      (fun y => d + (a * f y + b * h y + c * k y)) by funext y; ring]
  rw [laplacian_add_const (G.connection t) (G.metric t) d
    (f := fun y => a * f y + b * h y + c * k y)
    (Filter.Eventually.of_forall (((hfa.add hhb).add hkc).mdifferentiable (by simp)))
    (gradientFun_mdiffAt (G.metric t) ((hfa.add hhb).add hkc) x)]
  rw [laplacian_add_at (G.connection t) (G.metric t)
    (f := fun y => a * f y + b * h y) (h := fun y => c * k y)
    (Filter.Eventually.of_forall ((hfa.add hhb).mdifferentiable (by simp)))
    (Filter.Eventually.of_forall (hkc.mdifferentiable (by simp)))
    (gradientFun_mdiffAt (G.metric t) (hfa.add hhb) x)
    (gradientFun_mdiffAt (G.metric t) hkc x)]
  rw [laplacian_add_at (G.connection t) (G.metric t)
    (f := fun y => a * f y) (h := fun y => b * h y)
    (Filter.Eventually.of_forall (hfa.mdifferentiable (by simp)))
    (Filter.Eventually.of_forall (hhb.mdifferentiable (by simp)))
    (gradientFun_mdiffAt (G.metric t) hfa x)
    (gradientFun_mdiffAt (G.metric t) hhb x)]
  change laplacian (G.connection t) (G.metric t) (a • f) x +
    laplacian (G.connection t) (G.metric t) (b • h) x +
    laplacian (G.connection t) (G.metric t) (c • k) x = _
  rw [laplacian_const_smul (G.connection t) (G.metric t) a fd
    (gradientFun_mdiffAt (G.metric t) hf x),
    laplacian_const_smul (G.connection t) (G.metric t) b hd
    (gradientFun_mdiffAt (G.metric t) hh x),
    laplacian_const_smul (G.connection t) (G.metric t) c kd
    (gradientFun_mdiffAt (G.metric t) hk x)]

private theorem gradient_smooth_linear_combination
    (g : SmoothRiemannianMetric I M) (a b c d : ℝ) (f h k : M → ℝ) {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hh : MDifferentiableAt I 𝓘(ℝ, ℝ) h x)
    (hk : MDifferentiableAt I 𝓘(ℝ, ℝ) k x) :
    gradientFun g (fun y => a * f y + b * h y + c * k y + d) x =
      a • gradientFun g f x + b • gradientFun g h x + c • gradientFun g k x := by
  have hfa : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => a * f y) x :=
    mdifferentiableAt_const.mul hf
  have hhb : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => b * h y) x :=
    mdifferentiableAt_const.mul hh
  have hkc : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => c * k y) x :=
    mdifferentiableAt_const.mul hk
  rw [gradientFun_add g (f := fun y => a * f y + b * h y + c * k y)
    (h := fun _ => d) (((hfa.add hhb).add hkc)) mdifferentiableAt_const,
    gradientFun_const, add_zero]
  rw [gradientFun_add g (f := fun y => a * f y + b * h y)
    (h := fun y => c * k y) (hfa.add hhb) hkc,
    gradientFun_add g (f := fun y => a * f y) (h := fun y => b * h y) hfa hhb]
  change gradientFun g (a • f) x + gradientFun g (b • h) x + gradientFun g (c • k) x = _
  rw [gradientFun_const_smul g a hf, gradientFun_const_smul g b hh,
    gradientFun_const_smul g c hk]

def perelmanV
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (R u : ℝ → M → ℝ) (t : ℝ) (x : M) : ℝ :=
  let f := perelmanPotential (Module.finrank ℝ E) t (u t)
  (t * (2 * laplacianAt G t f x -
    (G.metric t).inner x (gradientAt G t f x) (gradientAt G t f x) + R t x) +
      f x - (Module.finrank ℝ E : ℝ)) * u t x

theorem perelman_v_evolution
    [I.Boundaryless] [T2Space M]
    {D Dr : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (u : ℝ → M → ℝ)
    (hu : DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn Dr
      (reverseFamily (flowG S) T) (fun r x => -S.scalar (T - r) x) u)
    (hpos : ∀ r, r ∈ Dr.regular ∩ Set.Ioi (0 : ℝ) → ∀ x, 0 < u r x)
    {t : ℝ} (ht : t ∈ Dr.regular) (htpos : 0 < t)
    (hTt : T - t ∈ D.regular) (x : M) :
    let G := reverseFamily (flowG S) T
    let f := perelmanPotential (Module.finrank ℝ E) t (u t)
    let hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f :=
      potential_slice Dr G (fun r x => -S.scalar (T - r) x) u
        (Module.finrank ℝ E) hu ht htpos (hpos t ⟨ht, htpos⟩)
    let v := perelmanV G (fun r => S.scalar (T - r)) u
    HasDerivAt (fun r => v r x)
      (laplacianAt G t (v t) x - S.scalar (T - t) x * v t x -
        2 * t * normSq0S (G.metric t) x 2
          (metricRicciAt (G.metric t) x +
            hessianSec (metricCov (G.metric t)) (metricCov_smooth (G.metric t)) f hf x -
            (1 / (2 * t)) • metricTensor0S (G.metric t) x) * u t x) t := by
  classical
  dsimp only
  let G := reverseFamily (flowG S) T
  let n : ℝ := Module.finrank ℝ E
  let f := fun r => perelmanPotential (Module.finrank ℝ E) r (u r)
  let g := G.metric t
  let R := fun r => S.scalar (T - r)
  let q := fun r y => (G.metric r).inner y
    (gradientFun (G.metric r) (f r) y) (gradientFun (G.metric r) (f r) y)
  let L := fun r y => laplacianAt G r (f r) y
  let B := fun r y => 2 * L r y - q r y + R r y
  let A := fun r y => r * B r y + f r y - n
  let ft := fun y => L t y - q t y + R t y - n / (2 * t)
  have hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ (f t) :=
    potential_slice Dr G (fun r y => -R r y) u (Module.finrank ℝ E)
      hu ht htpos (hpos t ⟨ht, htpos⟩)
  have hconn : G.connection t = LeviCivita g := rfl
  have hLf : L t = ΔG g ⟨f t, hf⟩ := by
    funext y
    exact laplacianAt_eq_delta G t hf hconn y
  have hLs : ContMDiff I 𝓘(ℝ, ℝ) ∞ (L t) := by
    rw [hLf]
    exact Δ_g_contMDiff g ⟨f t, hf⟩
  have hqf : q t = normGradSqFun g (f t) := by
    funext y
    simp only [q, g, normGradSqFun_def, gradient_eq_gradFun]
  have hqs : ContMDiff I 𝓘(ℝ, ℝ) ∞ (q t) := by
    rw [hqf]
    exact normGradSqFun_contMDiff g hf
  have hRs : ContMDiff I 𝓘(ℝ, ℝ) ∞ (R t) := metricScalar_smooth g
  have hBs : ContMDiff I 𝓘(ℝ, ℝ) ∞ (B t) :=
    (contMDiff_const.mul hLs |>.sub hqs).add hRs
  have hAs : ContMDiff I 𝓘(ℝ, ℝ) ∞ (A t) :=
    (contMDiff_const.mul hBs |>.add hf).sub contMDiff_const
  have hfts : ContMDiff I 𝓘(ℝ, ℝ) ∞ ft :=
    (hLs.sub hqs |>.add hRs).sub contMDiff_const
  have hfT : HasDerivAt (fun r => f r x) (ft x) t := by
    convert potential_pde Dr G (fun r y => -R r y) u
      (Module.finrank ℝ E) hu ht htpos (hpos t ⟨ht, htpos⟩) x using 1
    simp only [f, ft, q, L, n, sub_neg_eq_add]
  have hLT := revLaplacianPotential_time S hS T u hu hpos ht htpos hTt x
  change HasDerivAt (fun r => L r x)
    (laplacianAt G t ft x - 2 * inner0S g x 2 (metricRicciAt g x)
      (hessianSec (metricCov g) (metricCov_smooth g) (f t) hf x)) t at hLT
  have hqT := revGradSq_time S hS T (fun r y => -R r y) u
    (Module.finrank ℝ E) hu hpos ht htpos hTt x
  simp only [sub_neg_eq_add] at hqT
  change HasDerivAt (fun r => q r x)
    (-2 * metricRicciAt g x (vec2 (gradientFun g (f t) x) (gradientFun g (f t) x)) +
      2 * g.inner x (gradientFun g ft x) (gradientFun g (f t) x)) t at hqT
  have hRT := revScalar_time S hS T t hTt x
  change HasDerivAt (fun r => R r x)
    (-(laplacianAt G t (R t) x + 2 * normSq0S g x 2 (metricRicciAt g x))) t at hRT
  have hAT := (((hasDerivAt_id t).mul (((hLT.const_mul 2).sub hqT).add hRT)).add hfT).sub_const n
  change HasDerivAt (fun r => A r x) _ t at hAT
  have hLapFt : laplacianAt G t ft x =
      laplacianAt G t (L t) x - laplacianAt G t (q t) x + laplacianAt G t (R t) x := by
    simpa only [ft, one_mul, neg_one_mul, sub_eq_add_neg, neg_div] using
      laplacian_smooth_linear_combination G t 1 (-1) 1 (-n / (2 * t))
        (L t) (q t) (R t) hLs hqs hRs x
  have hGradFt : gradientFun g ft x =
      gradientFun g (L t) x - gradientFun g (q t) x + gradientFun g (R t) x := by
    simpa only [ft, one_mul, neg_one_mul, one_smul, neg_one_smul, sub_eq_add_neg,
      neg_div] using gradient_smooth_linear_combination g 1 (-1) 1 (-n / (2 * t))
        (L t) (q t) (R t) (hLs.mdifferentiable (by simp) x)
          (hqs.mdifferentiable (by simp) x) (hRs.mdifferentiable (by simp) x)
  have hLapB : laplacianAt G t (B t) x =
      2 * laplacianAt G t (L t) x - laplacianAt G t (q t) x + laplacianAt G t (R t) x := by
    simpa only [B, one_mul, neg_one_mul, add_zero, sub_eq_add_neg] using
      laplacian_smooth_linear_combination G t 2 (-1) 1 0
        (L t) (q t) (R t) hLs hqs hRs x
  have hGradB : gradientFun g (B t) x =
      (2 : ℝ) • gradientFun g (L t) x - gradientFun g (q t) x + gradientFun g (R t) x := by
    simpa only [B, one_mul, neg_one_mul, one_smul, neg_one_smul, add_zero, sub_eq_add_neg]
      using gradient_smooth_linear_combination g 2 (-1) 1 0
        (L t) (q t) (R t) (hLs.mdifferentiable (by simp) x)
          (hqs.mdifferentiable (by simp) x) (hRs.mdifferentiable (by simp) x)
  have hLapA : laplacianAt G t (A t) x = t * laplacianAt G t (B t) x + L t x := by
    simpa only [A, L, one_mul, zero_mul, add_zero, sub_eq_add_neg] using
      laplacian_smooth_linear_combination G t t 1 0 (-n)
        (B t) (f t) (R t) hBs hf hRs x
  have hGradA : gradientFun g (A t) x =
      t • gradientFun g (B t) x + gradientFun g (f t) x := by
    simpa only [A, one_mul, zero_mul, add_zero, one_smul, zero_smul, sub_eq_add_neg]
      using gradient_smooth_linear_combination g t 1 0 (-n)
        (B t) (f t) (R t) (hBs.mdifferentiable (by simp) x)
          (hf.mdifferentiable (by simp) x) (hRs.mdifferentiable (by simp) x)
  have hBochner := laplacian_gradient_norm_sq_eq g hf x
  have hqnative : (fun y => g.inner y (gradientFun g (f t) y) (gradientFun g (f t) y)) = q t := rfl
  have hLnative : (fun y => laplacian (metricCov g) g (f t) y) = L t := rfl
  rw [hqnative, hLnative] at hBochner
  change laplacianAt G t (q t) x = _ at hBochner
  have hTraceH : metricTracePair0SAt g
      (hessianSec (metricCov g) (metricCov_smooth g) (f t) hf x) = L t x := by
    exact (scalarLap_smooth (metricCov g) (metricCov_smooth g) g
      (leviCivitaConnectionOfMetric_isMetricCompatible g) (f t) hf).eq_trace.symm
  have hTraceR : metricTracePair0SAt g (metricRicciAt g x) = R t x := rfl
  let Hf := hessianSec (metricCov g) (metricCov_smooth g) (f t) hf x
  let Rc := metricRicciAt g x
  have hSq := normSq0S_sub_smul_metricTensor0S g x (Rc + Hf) (1 / (2 * t))
  rw [_root_.Tensor0SBundle.normSq0S_add, metricTracePair0SAt_add, hTraceR, hTraceH] at hSq
  have hDrift : deriv (fun r => A r x) t - laplacianAt G t (A t) x +
      2 * g.inner x (gradientFun g (f t) x) (gradientFun g (A t) x) =
      -2 * t * normSq0S g x 2 (Rc + Hf - (1 / (2 * t)) • metricTensor0S g x) := by
    rw [hAT.deriv, hLapA, hLapB, hLapFt, hGradA, hGradB, hGradFt, hBochner, hSq]
    simp only [map_add, map_sub, map_smul, add_apply, sub_apply, smul_eq_mul]
    rw [g.symm x (gradientFun g (L t) x) (gradientFun g (f t) x),
      g.symm x (gradientFun g (q t) x) (gradientFun g (f t) x),
      g.symm x (gradientFun g (R t) x) (gradientFun g (f t) x)]
    dsimp only [B, ft, q, Hf, Rc, n, g, id, Pi.add_apply, Pi.sub_apply]
    field_simp [htpos.ne']
    ring
  have hus := hu.sliceSmooth t (Dr.regular_subset ht)
  have huT : HasDerivAt (fun r => u r x) (laplacianAt G t (u t) x - R t x * u t x) t := by
    convert hu.equation t ht x using 1
    change _ = _ + (-R t x) * u t x
    ring
  have hProduct := conjugate_heat_mul_eq_potential_drift G R A u
    (Module.finrank ℝ E) htpos x hAT.differentiableAt huT
    ((hAs x).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) ((hus x).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) (hpos t ⟨ht, htpos⟩ x)
  change deriv (fun r => A r x * u r x) t -
      laplacianAt G t (fun y => A t y * u t y) x + R t x * (A t x * u t x) =
      u t x * (deriv (fun r => A r x) t - laplacianAt G t (A t) x +
        2 * g.inner x (gradientFun g (f t) x) (gradientFun g (A t) x)) at hProduct
  rw [hDrift] at hProduct
  have hVT := hAT.mul huT
  apply hVT.congr_deriv
  rw [← hVT.deriv]
  change deriv (fun r => A r x * u r x) t =
    laplacianAt G t (fun y => A t y * u t y) x - R t x * (A t x * u t x) -
      2 * t * normSq0S g x 2 (Rc + Hf - (1 / (2 * t)) • metricTensor0S g x) * u t x
  linarith

end DifferentialGeometry.PDE.RicciFlow.Entropy
