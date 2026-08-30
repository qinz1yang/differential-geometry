import DifferentialGeometry.Geometry.Metric.RicciSoliton.Normalized
import DifferentialGeometry.Geometry.Operator.LaplacianBridge

set_option autoImplicit false

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

open Curvature Operator
open DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
    [I.Boundaryless] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
private theorem contMDiff_rpow_of_pos
    {f : C^∞⟮I, M; Real⟯} {p : Real} (hpos : ∀ y : M, 0 < f y) :
    ContMDiff I 𝓘(Real, Real) ∞ (fun y : M => f y ^ p) := by
  intro y
  exact (Real.contDiffAt_rpow_const_of_ne (p := p) (hpos y).ne').comp_contMDiffAt
    (f.contMDiff.contMDiffAt)

omit [NeZero (Module.finrank Real E)] in
theorem normalizedGradientRicciSoliton_weightedLaplacian_inv
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hpos : ∀ y : M, 0 < f y) (x : M) :
    let u : C^∞⟮I, M; 𝓘(Real, Real), Real⟯ :=
      ⟨fun y : M => f y ^ (-1 : Real), contMDiff_rpow_of_pos (I := I) hpos⟩
    weightedLaplacian (I := I) g f u x =
      f x ^ (-1 : Real) - (Module.finrank Real E : Real) / 2 * f x ^ (-2 : Real) +
        2 * g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g f x) *
          f x ^ (-3 : Real) := by
  let u : C^∞⟮I, M; 𝓘(Real, Real), Real⟯ :=
    ⟨fun y : M => f y ^ (-1 : Real), contMDiff_rpow_of_pos (I := I) hpos⟩
  change weightedLaplacian (I := I) g f u x = _
  have hf : ∀ y : M, MDifferentiableAt I 𝓘(Real, Real) (f : M → Real) y :=
    fun y => (f.contMDiff y).mdifferentiableAt (by simp)
  have hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x :=
    (gradientFun_contMDiffAt (I := I) g (f.contMDiff x)).mdifferentiableAt (by simp)
  have hpow := laplacian_rpow (I := I) (LeviCivita (I := I) g) g
    (-1 : Real) hf hpos hgrad
  have hpow' :
      ΔG (I := I) g u x =
        (-1 : Real) * f x ^ (-2 : Real) * ΔG (I := I) g f x +
          (-1 : Real) * (-2 : Real) * f x ^ (-3 : Real) *
            g.inner x (gradientFun (I := I) g f x)
              (gradientFun (I := I) g f x) := by
    have hu' :
        ΔG (I := I) g u x =
          laplacian (I := I) (LeviCivita (I := I) g) g
            (u : M → Real) x := by
      exact (laplacian_levi_eq (I := I) g u.contMDiff x).symm
    have hf' :
        ΔG (I := I) g f x =
          laplacian (I := I) (LeviCivita (I := I) g) g
            (f : M → Real) x := by
      exact (laplacian_levi_eq (I := I) g f.contMDiff x).symm
    rw [hu', hf']
    change laplacian (I := I) (LeviCivita (I := I) g) g
      (fun y : M => f y ^ (-1 : Real)) x = _
    convert hpow using 1
    all_goals ring_nf
  have hgradpow :
      gradFun (I := I) g u x =
        ((-1 : Real) * f x ^ (-2 : Real)) •
          gradFun (I := I) g f x := by
    change gradientFun (I := I) g (u : M → Real) x =
      ((-1 : Real) * f x ^ (-2 : Real)) • gradientFun (I := I) g f x
    rw [show (u : M → Real) = (fun y : M => f y ^ (-1 : Real)) by rfl]
    convert gradientFun_rpow (I := I) g (-1 : Real) (hf x) (hpos x) using 1
    all_goals ring_nf
  have htrace := gradientRicciSoliton_trace (I := I) h.2.1 x
  have hham := normalizedGradientRicciSoliton_potential_equation (I := I) h x
  have hfg : gradFun (I := I) g f x = gradientFun (I := I) g f x := by
    exact (Connection.gradient_eq_gradFun (I := I) g f x).symm
  rw [hfg] at hham hgradpow
  have hΔ :
      ΔG (I := I) g f x =
        (Module.finrank Real E : Real) / 2 - f x +
          g.inner x (gradientFun (I := I) g f x) (gradientFun (I := I) g f x) := by
    change metricScalarAt (I := I) g x + ΔG (I := I) g f x =
      (Module.finrank Real E : Real) * 1 / 2 at htrace
    linarith [htrace, hham]
  rw [weightedLaplacian_apply, hfg, hpow', hgradpow]
  rw [show g.inner x (gradientFun (I := I) g f x)
      (((-1 : Real) * f x ^ (-2 : Real)) •
        gradientFun (I := I) g f x) =
      (-1 : Real) * f x ^ (-2 : Real) *
        g.inner x (gradientFun (I := I) g f x)
          (gradientFun (I := I) g f x) by
    simp only [map_smul, smul_eq_mul]]
  rw [hΔ]
  have hpow12 : f x ^ (-2 : Real) * f x = f x ^ (-1 : Real) := by
    calc
      f x ^ (-2 : Real) * f x = f x ^ (-2 : Real) * f x ^ (1 : Real) := by
        rw [Real.rpow_one]
      _ = f x ^ ((-2 : Real) + 1) := (Real.rpow_add (hpos x) _ _).symm
      _ = f x ^ (-1 : Real) := by norm_num
  calc
    _ = -1 * f x ^ (-2 : Real) *
          ((Module.finrank Real E : Real) / 2 +
            g.inner x (gradientFun (I := I) g f x)
              (gradientFun (I := I) g f x)) +
          f x ^ (-2 : Real) * f x +
          (-1 : Real) * (-2 : Real) * f x ^ (-3 : Real) *
            g.inner x (gradientFun (I := I) g f x)
              (gradientFun (I := I) g f x) -
          (-1 : Real) * f x ^ (-2 : Real) *
            g.inner x (gradientFun (I := I) g f x)
              (gradientFun (I := I) g f x) := by ring
    _ = _ := by rw [hpow12]; ring

omit [NeZero (Module.finrank Real E)] in
theorem normalizedGradientRicciSoliton_weightedLaplacian_inv_sq
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hpos : ∀ y : M, 0 < f y) (x : M) :
    let u : C^∞⟮I, M; 𝓘(Real, Real), Real⟯ :=
      ⟨fun y : M => f y ^ (-2 : Real), contMDiff_rpow_of_pos (I := I) hpos⟩
    weightedLaplacian (I := I) g f u x =
      2 * f x ^ (-2 : Real) - (Module.finrank Real E : Real) * f x ^ (-3 : Real) +
        6 * g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g f x) *
          f x ^ (-4 : Real) := by
  let u : C^∞⟮I, M; 𝓘(Real, Real), Real⟯ :=
    ⟨fun y : M => f y ^ (-2 : Real), contMDiff_rpow_of_pos (I := I) hpos⟩
  change weightedLaplacian (I := I) g f u x = _
  have hf : ∀ y : M, MDifferentiableAt I 𝓘(Real, Real) (f : M → Real) y :=
    fun y => (f.contMDiff y).mdifferentiableAt (by simp)
  have hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x :=
    (gradientFun_contMDiffAt (I := I) g (f.contMDiff x)).mdifferentiableAt (by simp)
  have hpow := laplacian_rpow (I := I) (LeviCivita (I := I) g) g
    (-2 : Real) hf hpos hgrad
  have hpow' :
      ΔG (I := I) g u x =
        (-2 : Real) * f x ^ (-3 : Real) * ΔG (I := I) g f x +
          (-2 : Real) * (-3 : Real) * f x ^ (-4 : Real) *
            g.inner x (gradientFun (I := I) g f x)
              (gradientFun (I := I) g f x) := by
    have hu' :
        ΔG (I := I) g u x =
          laplacian (I := I) (LeviCivita (I := I) g) g
            (u : M → Real) x := by
      exact (laplacian_levi_eq (I := I) g u.contMDiff x).symm
    have hf' :
        ΔG (I := I) g f x =
          laplacian (I := I) (LeviCivita (I := I) g) g
            (f : M → Real) x := by
      exact (laplacian_levi_eq (I := I) g f.contMDiff x).symm
    rw [hu', hf']
    change laplacian (I := I) (LeviCivita (I := I) g) g
      (fun y : M => f y ^ (-2 : Real)) x =
        -2 * f x ^ (-3 : Real) *
            laplacian (I := I) (LeviCivita (I := I) g) g (f : M → Real) x + _
    convert hpow using 1
    all_goals ring_nf
  have hgradpow :
      gradFun (I := I) g u x =
        ((-2 : Real) * f x ^ (-3 : Real)) •
          gradFun (I := I) g f x := by
    change gradientFun (I := I) g (u : M → Real) x =
      ((-2 : Real) * f x ^ (-3 : Real)) • gradientFun (I := I) g f x
    rw [show (u : M → Real) = (fun y : M => f y ^ (-2 : Real)) by rfl]
    convert gradientFun_rpow (I := I) g (-2 : Real) (hf x) (hpos x) using 1
    all_goals ring_nf
  have htrace := gradientRicciSoliton_trace (I := I) h.2.1 x
  have hham := normalizedGradientRicciSoliton_potential_equation (I := I) h x
  have hfg : gradFun (I := I) g f x = gradientFun (I := I) g f x := by
    exact (Connection.gradient_eq_gradFun (I := I) g f x).symm
  rw [hfg] at hham hgradpow
  have hΔ :
      ΔG (I := I) g f x =
        (Module.finrank Real E : Real) / 2 - f x +
          g.inner x (gradientFun (I := I) g f x) (gradientFun (I := I) g f x) := by
    change metricScalarAt (I := I) g x + ΔG (I := I) g f x =
      (Module.finrank Real E : Real) * 1 / 2 at htrace
    linarith [htrace, hham]
  rw [weightedLaplacian_apply, hfg, hpow', hgradpow]
  rw [show g.inner x (gradientFun (I := I) g f x)
      (((-2 : Real) * f x ^ (-3 : Real)) •
        gradientFun (I := I) g f x) =
      (-2 : Real) * f x ^ (-3 : Real) *
        g.inner x (gradientFun (I := I) g f x)
          (gradientFun (I := I) g f x) by
    simp only [map_smul, smul_eq_mul]]
  rw [hΔ]
  have hpow23 : f x ^ (-3 : Real) * f x = f x ^ (-2 : Real) := by
    calc
      f x ^ (-3 : Real) * f x = f x ^ (-3 : Real) * f x ^ (1 : Real) := by
        rw [Real.rpow_one]
      _ = f x ^ ((-3 : Real) + 1) := (Real.rpow_add (hpos x) _ _).symm
      _ = f x ^ (-2 : Real) := by norm_num
  calc
    _ = (-2 : Real) * f x ^ (-3 : Real) *
          ((Module.finrank Real E : Real) / 2 +
            g.inner x (gradientFun (I := I) g f x)
              (gradientFun (I := I) g f x)) +
          2 * f x ^ (-3 : Real) * f x +
          (-2 : Real) * (-3 : Real) * f x ^ (-4 : Real) *
            g.inner x (gradientFun (I := I) g f x)
              (gradientFun (I := I) g f x) -
          (-2 : Real) * f x ^ (-3 : Real) *
            g.inner x (gradientFun (I := I) g f x)
              (gradientFun (I := I) g f x) := by ring
    _ = _ := by
      have hmul : 2 * f x ^ (-3 : Real) * f x =
          2 * f x ^ (-2 : Real) := by
        calc
          2 * f x ^ (-3 : Real) * f x =
              2 * (f x ^ (-3 : Real) * f x) := by ring
          _ = 2 * f x ^ (-2 : Real) := by rw [hpow23]
      rw [hmul]
      ring

end DifferentialGeometry.Geometry
