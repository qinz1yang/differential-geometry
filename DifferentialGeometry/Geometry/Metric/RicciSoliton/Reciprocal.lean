import DifferentialGeometry.Geometry.Metric.RicciSoliton.Normalized
import DifferentialGeometry.Geometry.Operator.Laplacian.LeviCivitaIdentification

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

noncomputable def reciprocalPotentialBarrier
    (f : C^∞⟮I, M; Real⟯) (hpos : ∀ y : M, 0 < f y) :
    C^∞⟮I, M; Real⟯ :=
  ⟨fun y : M => f y ^ (-1 : Real) +
      (Module.finrank Real E : Real) * f y ^ (-2 : Real),
    (contMDiff_rpow_of_pos (I := I) (p := (-1 : Real)) hpos).add
      (contMDiff_const.mul
        (contMDiff_rpow_of_pos (I := I) (p := (-2 : Real)) hpos))⟩

omit [NeZero (Module.finrank Real E)] in
theorem normalizedGradientRicciSoliton_weightedLaplacian_rpow_at
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (p : Real) {x : M} (hx : 0 < f x) :
    laplacian (I := I) (LeviCivita (I := I) g) g (fun y => f y ^ p) x -
        g.inner x (gradientFun (I := I) g f x)
          (gradientFun (I := I) g (fun y => f y ^ p) x) =
      (p * f x ^ (p - 1)) * ((Module.finrank Real E : Real) / 2 - f x) +
        (p * (p - 1) * f x ^ (p - 2)) *
          g.inner x (gradientFun (I := I) g f x)
            (gradientFun (I := I) g f x) := by
  have hf : ∀ y : M, MDifferentiableAt I 𝓘(Real, Real) (f : M → Real) y :=
    fun y => (f.contMDiff y).mdifferentiableAt (by simp)
  have hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x :=
    (gradientFun_contMDiffAt (I := I) g (f.contMDiff x)).mdifferentiableAt (by simp)
  have hpotential := normalizedGradientRicciSoliton_weightedLaplacian_potential h x
  have hbridge : laplacian (I := I) (LeviCivita (I := I) g) g f x = ΔG g f x :=
    laplacian_levi_eq (I := I) g f.contMDiff x
  rw [weightedLaplacian_apply, ← hbridge,
    ← Connection.gradient_eq_gradFun] at hpotential
  rw [laplacian_rpow_at (I := I) (LeviCivita (I := I) g) g p
      (Filter.Eventually.of_forall hf) hx hgrad,
    gradientFun_rpow (I := I) g p (hf x) hx]
  simp only [map_smul, smul_eq_mul]
  rw [← hpotential]
  ring

omit [NeZero (Module.finrank Real E)] in
theorem normalizedGradientRicciSoliton_weightedLaplacian_inv_at
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    {x : M} (hx : 0 < f x) :
    laplacian (I := I) (LeviCivita (I := I) g) g
        (fun y => f y ^ (-1 : Real)) x -
        g.inner x (gradientFun (I := I) g f x)
          (gradientFun (I := I) g (fun y => f y ^ (-1 : Real)) x) =
      f x ^ (-1 : Real) - (Module.finrank Real E : Real) / 2 * f x ^ (-2 : Real) +
        2 * g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g f x) *
          f x ^ (-3 : Real) := by
  rw [normalizedGradientRicciSoliton_weightedLaplacian_rpow_at h (-1) hx]
  have hpow : f x ^ (-2 : Real) * f x = f x ^ (-1 : Real) := by
    calc
      f x ^ (-2 : Real) * f x = f x ^ (-2 : Real) * f x ^ (1 : Real) := by
        rw [Real.rpow_one]
      _ = f x ^ ((-2 : Real) + 1) := (Real.rpow_add hx _ _).symm
      _ = f x ^ (-1 : Real) := by norm_num
  rw [Connection.gradient_eq_gradFun]
  norm_num only [show (-1 : Real) - 1 = -2 by norm_num,
    show (-1 : Real) - 2 = -3 by norm_num]
  nlinarith [hpow]

omit [NeZero (Module.finrank Real E)] in
theorem normalizedGradientRicciSoliton_weightedLaplacian_inv_sq_at
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    {x : M} (hx : 0 < f x) :
    laplacian (I := I) (LeviCivita (I := I) g) g
        (fun y => f y ^ (-2 : Real)) x -
        g.inner x (gradientFun (I := I) g f x)
          (gradientFun (I := I) g (fun y => f y ^ (-2 : Real)) x) =
      2 * f x ^ (-2 : Real) - (Module.finrank Real E : Real) * f x ^ (-3 : Real) +
        6 * g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g f x) *
          f x ^ (-4 : Real) := by
  rw [normalizedGradientRicciSoliton_weightedLaplacian_rpow_at h (-2) hx]
  have hpow : f x ^ (-3 : Real) * f x = f x ^ (-2 : Real) := by
    calc
      f x ^ (-3 : Real) * f x = f x ^ (-3 : Real) * f x ^ (1 : Real) := by
        rw [Real.rpow_one]
      _ = f x ^ ((-3 : Real) + 1) := (Real.rpow_add hx _ _).symm
      _ = f x ^ (-2 : Real) := by norm_num
  rw [Connection.gradient_eq_gradFun]
  norm_num only [show (-2 : Real) - 1 = -3 by norm_num,
    show (-2 : Real) - 2 = -4 by norm_num]
  nlinarith [hpow]

omit [NeZero (Module.finrank Real E)] in
theorem normalizedGradientRicciSoliton_weightedLaplacian_reciprocalPotentialBarrier_at
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    {x : M} (hx : 0 < f x) :
    let B : M → Real := fun y =>
      f y ^ (-1 : Real) + (Module.finrank Real E : Real) * f y ^ (-2 : Real)
    laplacian (I := I) (LeviCivita (I := I) g) g B x -
        g.inner x (gradientFun (I := I) g f x) (gradientFun (I := I) g B x) =
      B x + (Module.finrank Real E : Real) * f x ^ (-3 : Real) *
          (f x / 2 - (Module.finrank Real E : Real)) +
        2 * g.inner x (gradFun (I := I) g f x)
            (gradFun (I := I) g f x) * f x ^ (-3 : Real) +
        6 * (Module.finrank Real E : Real) *
          g.inner x (gradFun (I := I) g f x)
            (gradFun (I := I) g f x) * f x ^ (-4 : Real) := by
  let u : M → Real := fun y => f y ^ (-1 : Real)
  let v : M → Real := fun y => f y ^ (-2 : Real)
  let n : Real := Module.finrank Real E
  have hnear : ∀ᶠ y in nhds x, 0 < f y :=
    f.contMDiff.continuous.continuousAt.eventually (lt_mem_nhds hx)
  have hu : ∀ᶠ y in nhds x, MDifferentiableAt I 𝓘(Real, Real) u y := by
    filter_upwards [hnear] with y hy
    exact mdifferentiableAt_rpow (I := I) (-1)
      ((f.contMDiff y).mdifferentiableAt (by simp)) hy
  have hv : ∀ᶠ y in nhds x, MDifferentiableAt I 𝓘(Real, Real) v y := by
    filter_upwards [hnear] with y hy
    exact mdifferentiableAt_rpow (I := I) (-2)
      ((f.contMDiff y).mdifferentiableAt (by simp)) hy
  have hw : ∀ᶠ y in nhds x,
      MDifferentiableAt I 𝓘(Real, Real) (n • v) y := by
    filter_upwards [hv] with y hy
    exact mdifferentiableAt_const.mul hy
  have hus : ContMDiffAt I 𝓘(Real, Real) ∞ u x :=
    (Real.contDiffAt_rpow_const_of_ne (p := (-1 : Real)) hx.ne').comp_contMDiffAt
      f.contMDiff.contMDiffAt
  have hvs : ContMDiffAt I 𝓘(Real, Real) ∞ v x :=
    (Real.contDiffAt_rpow_const_of_ne (p := (-2 : Real)) hx.ne').comp_contMDiffAt
      f.contMDiff.contMDiffAt
  have hgu : MDiffAt (T% fun y => gradientFun (I := I) g u y) x :=
    (gradientFun_contMDiffAt (I := I) g hus).mdifferentiableAt (by simp)
  have hgv : MDiffAt (T% fun y => gradientFun (I := I) g v y) x :=
    (gradientFun_contMDiffAt (I := I) g hvs).mdifferentiableAt (by simp)
  have hgw : MDiffAt (T% fun y => gradientFun (I := I) g (n • v) y) x :=
    (gradientFun_contMDiffAt (I := I) g (contMDiffAt_const.mul hvs)).mdifferentiableAt
      (by simp)
  have hlinear :
      laplacian (I := I) (LeviCivita (I := I) g) g (fun y => u y + (n • v) y) x -
          g.inner x (gradientFun (I := I) g f x)
            (gradientFun (I := I) g (fun y => u y + (n • v) y) x) =
        (laplacian (I := I) (LeviCivita (I := I) g) g u x -
          g.inner x (gradientFun (I := I) g f x) (gradientFun (I := I) g u x)) +
        n * (laplacian (I := I) (LeviCivita (I := I) g) g v x -
          g.inner x (gradientFun (I := I) g f x) (gradientFun (I := I) g v x)) := by
    rw [laplacian_add_at (I := I) (LeviCivita (I := I) g) g hu hw hgu hgw,
      laplacian_smul_at (I := I) (LeviCivita (I := I) g) g n hv hgv,
      gradientFun_add (I := I) g hu.self_of_nhds hw.self_of_nhds,
      gradientFun_const_smul (I := I) g n hv.self_of_nhds]
    simp only [map_add, map_smul, smul_eq_mul]
    ring
  change laplacian (I := I) (LeviCivita (I := I) g) g (fun y => u y + (n • v) y) x -
    g.inner x (gradientFun (I := I) g f x)
      (gradientFun (I := I) g (fun y => u y + (n • v) y) x) = _
  rw [hlinear,
    normalizedGradientRicciSoliton_weightedLaplacian_inv_at h hx,
    normalizedGradientRicciSoliton_weightedLaplacian_inv_sq_at h hx]
  have hpow : f x ^ (-3 : Real) * f x = f x ^ (-2 : Real) := by
    calc
      f x ^ (-3 : Real) * f x = f x ^ (-3 : Real) * f x ^ (1 : Real) := by
        rw [Real.rpow_one]
      _ = f x ^ ((-3 : Real) + 1) := (Real.rpow_add hx _ _).symm
      _ = f x ^ (-2 : Real) := by norm_num
  dsimp only [u, v, n]
  nlinarith [congrArg (fun r : Real => (Module.finrank Real E : Real) * r) hpow]

omit [NeZero (Module.finrank Real E)] in
theorem normalizedGradientRicciSoliton_weightedLaplacian_reciprocalPotentialBarrier_ge_at
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    {x : M} (hx : 0 < f x) (hlarge : 2 * (Module.finrank Real E : Real) ≤ f x) :
    let B : M → Real := fun y =>
      f y ^ (-1 : Real) + (Module.finrank Real E : Real) * f y ^ (-2 : Real)
    B x ≤ laplacian (I := I) (LeviCivita (I := I) g) g B x -
      g.inner x (gradientFun (I := I) g f x) (gradientFun (I := I) g B x) := by
  change _ ≤ _
  rw [normalizedGradientRicciSoliton_weightedLaplacian_reciprocalPotentialBarrier_at h hx]
  have hn : 0 ≤ (Module.finrank Real E : Real) := by positivity
  have hf : 0 ≤ f x / 2 - (Module.finrank Real E : Real) := by linarith
  have hgrad : 0 ≤ g.inner x (gradFun (I := I) g f x)
      (gradFun (I := I) g f x) := by
    simpa only [normGradSqFun_def] using
      normGradSqFun_nonneg (I := I) g (f : M → Real) x
  have hp3 : 0 ≤ f x ^ (-3 : Real) := (Real.rpow_pos_of_pos hx _).le
  have hp4 : 0 ≤ f x ^ (-4 : Real) := (Real.rpow_pos_of_pos hx _).le
  have hterm1 : 0 ≤ (Module.finrank Real E : Real) *
      f x ^ (-3 : Real) * (f x / 2 - (Module.finrank Real E : Real)) := by positivity
  have hterm2 : 0 ≤ 2 * g.inner x (gradFun (I := I) g f x)
      (gradFun (I := I) g f x) * f x ^ (-3 : Real) := by positivity
  have hterm3 : 0 ≤ 6 * (Module.finrank Real E : Real) *
      g.inner x (gradFun (I := I) g f x)
        (gradFun (I := I) g f x) * f x ^ (-4 : Real) := by positivity
  linarith

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
  have hbridge : laplacian (I := I) (LeviCivita (I := I) g) g u x = ΔG g u x :=
    laplacian_levi_eq (I := I) g u.contMDiff x
  rw [weightedLaplacian_apply, ← hbridge]
  simpa only [u, ContMDiffMap.coeFn_mk, Connection.gradient_eq_gradFun] using
    normalizedGradientRicciSoliton_weightedLaplacian_inv_at h (hpos x)

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
  have hbridge : laplacian (I := I) (LeviCivita (I := I) g) g u x = ΔG g u x :=
    laplacian_levi_eq (I := I) g u.contMDiff x
  rw [weightedLaplacian_apply, ← hbridge]
  simpa only [u, ContMDiffMap.coeFn_mk, Connection.gradient_eq_gradFun] using
    normalizedGradientRicciSoliton_weightedLaplacian_inv_sq_at h (hpos x)

omit [NeZero (Module.finrank Real E)] in
theorem normalizedGradientRicciSoliton_weightedLaplacian_reciprocalPotentialBarrier
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hpos : ∀ y : M, 0 < f y) (x : M) :
    weightedLaplacian (I := I) g f
        (reciprocalPotentialBarrier (I := I) f hpos) x =
      reciprocalPotentialBarrier (I := I) f hpos x +
        (Module.finrank Real E : Real) * f x ^ (-3 : Real) *
          (f x / 2 - (Module.finrank Real E : Real)) +
        2 * g.inner x (gradFun (I := I) g f x)
            (gradFun (I := I) g f x) * f x ^ (-3 : Real) +
        6 * (Module.finrank Real E : Real) *
          g.inner x (gradFun (I := I) g f x)
            (gradFun (I := I) g f x) * f x ^ (-4 : Real) := by
  have hbridge :
      laplacian (I := I) (LeviCivita (I := I) g) g
          (reciprocalPotentialBarrier (I := I) f hpos) x =
        ΔG g (reciprocalPotentialBarrier (I := I) f hpos) x :=
    laplacian_levi_eq (I := I) g (reciprocalPotentialBarrier (I := I) f hpos).contMDiff x
  rw [weightedLaplacian_apply, ← hbridge]
  simpa only [reciprocalPotentialBarrier, ContMDiffMap.coeFn_mk,
    Connection.gradient_eq_gradFun] using
    normalizedGradientRicciSoliton_weightedLaplacian_reciprocalPotentialBarrier_at h (hpos x)

omit [NeZero (Module.finrank Real E)] in
theorem normalizedGradientRicciSoliton_weightedLaplacian_reciprocalPotentialBarrier_ge
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hpos : ∀ y : M, 0 < f y) (x : M)
    (hx : 2 * (Module.finrank Real E : Real) ≤ f x) :
    reciprocalPotentialBarrier (I := I) f hpos x ≤
      weightedLaplacian (I := I) g f
        (reciprocalPotentialBarrier (I := I) f hpos) x := by
  have hbridge :
      laplacian (I := I) (LeviCivita (I := I) g) g
          (reciprocalPotentialBarrier (I := I) f hpos) x =
        ΔG g (reciprocalPotentialBarrier (I := I) f hpos) x :=
    laplacian_levi_eq (I := I) g (reciprocalPotentialBarrier (I := I) f hpos).contMDiff x
  rw [weightedLaplacian_apply, ← hbridge]
  simpa only [reciprocalPotentialBarrier, ContMDiffMap.coeFn_mk,
    Connection.gradient_eq_gradFun] using
    normalizedGradientRicciSoliton_weightedLaplacian_reciprocalPotentialBarrier_ge_at
      h (hpos x) hx

end DifferentialGeometry.Geometry
