import DifferentialGeometry.Geometry.Comparison.Variation.FirstVariation.Basic

set_option autoImplicit false

noncomputable section

open Set Function Filter Manifold Bundle
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace CovariantDerivativeAlong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless]

omit [NeZero (Module.finrank ℝ E)] in
theorem inner_self_hasDerivAt_along
    {n : WithTop ℕ∞} (hn : 1 ≤ n)
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ∀ t, TangentSpace I (γ t)) (t : ℝ)
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I n γ t)
    (hV : DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t) :
    HasDerivAt (fun s : ℝ => g.inner (γ s) (V s) (V s))
      (2 * g.inner (γ t) (covDerivAlong (I := I) g γ V t) (V t)) t := by
  have h := Variation.inner_deriv_at (I := I) hn g γ V V t hγ hV hV
  have hsymm :
      g.inner (γ t) (covDerivAlong (I := I) g γ V t) (V t) +
        g.inner (γ t) (V t) (covDerivAlong (I := I) g γ V t) =
        2 * g.inner (γ t) (covDerivAlong (I := I) g γ V t) (V t) := by
    rw [g.symm (γ t) (V t) (covDerivAlong (I := I) g γ V t)]
    ring
  rwa [hsymm] at h

omit [NeZero (Module.finrank ℝ E)] in
theorem inner_covDeriv_hasDerivAt_along
    {n : WithTop ℕ∞} (hn : 1 ≤ n)
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V W : ∀ t, TangentSpace I (γ t)) (t : ℝ)
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I n γ t)
    (hVderiv : DifferentiableAt ℝ
      (chartRepAt (I := I) γ (fun s => covDerivAlong (I := I) g γ V s) t) t)
    (hW : DifferentiableAt ℝ (chartRepAt (I := I) γ W t) t) :
    HasDerivAt (fun s : ℝ => g.inner (γ s) (covDerivAlong (I := I) g γ V s) (W s))
      (g.inner (γ t) (covDerivAlong (I := I) g γ
          (fun s => covDerivAlong (I := I) g γ V s) t) (W t) +
        g.inner (γ t) (covDerivAlong (I := I) g γ V t)
          (covDerivAlong (I := I) g γ W t)) t :=
  Variation.inner_deriv_at (I := I) hn g γ
    (fun s => covDerivAlong (I := I) g γ V s) W t hγ hVderiv hW

omit [NeZero (Module.finrank ℝ E)] in
theorem inner_self_kato_along
    {n : WithTop ℕ∞} (hn : 1 ≤ n)
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ∀ t, TangentSpace I (γ t)) (t : ℝ)
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I n γ t)
    (hVderiv : DifferentiableAt ℝ
      (chartRepAt (I := I) γ (fun s => covDerivAlong (I := I) g γ V s) t) t)
    (hV : DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t) :
    HasDerivAt (fun s : ℝ => 2 * g.inner (γ s)
        (covDerivAlong (I := I) g γ V s) (V s))
      (2 * (g.inner (γ t) (covDerivAlong (I := I) g γ
          (fun s => covDerivAlong (I := I) g γ V s) t) (V t) +
        g.inner (γ t) (covDerivAlong (I := I) g γ V t)
          (covDerivAlong (I := I) g γ V t))) t :=
  (inner_covDeriv_hasDerivAt_along (I := I) hn g γ V V t hγ hVderiv hV).const_mul 2

omit [NeZero (Module.finrank ℝ E)] in
theorem inner_self_hasDerivAt_along_const
    (g : SmoothRiemannianMetric I M) (p : M) (w : TangentSpace I p) (t : ℝ) :
    HasDerivAt (fun _ : ℝ => g.inner p w w) (0 : ℝ) t := by
  have hγ : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ (fun _ : ℝ => p) t := contMDiffAt_const
  have hVrep : DifferentiableAt ℝ
      (chartRepAt (I := I) (fun _ : ℝ => p) (fun _ : ℝ => w) t) t := by
    have hconst : chartRepAt (I := I) (fun _ : ℝ => p) (fun _ : ℝ => w) t =
        fun _ : ℝ => chartRepAt (I := I) (fun _ : ℝ => p) (fun _ : ℝ => w) t t := rfl
    rw [hconst]
    exact differentiableAt_const _
  have h := inner_self_hasDerivAt_along (I := I)
    (by simp : (1 : WithTop ℕ∞) ≤ ∞) g (fun _ : ℝ => p) (fun _ : ℝ => w) t hγ hVrep
  have hzero : covDerivAlong (I := I) g (fun _ : ℝ => p) (fun _ : ℝ => w) t = 0 := by
    have hderiv : deriv (fun _ : ℝ => (w : E)) t = 0 := deriv_const t w
    have hconst := covDerivAlong_const (I := I) g p (fun _ : ℝ => w) t
      (differentiableAt_const w)
    rw [hconst, hderiv]
  rw [hzero] at h
  simpa using h

omit [NeZero (Module.finrank ℝ E)] in
theorem hasDerivAt_deriv_inner_self_along
    {n : WithTop ℕ∞} (hn : 1 ≤ n)
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ∀ t, TangentSpace I (γ t)) (t : ℝ)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I n γ)
    (hV : ∀ s, DifferentiableAt ℝ (chartRepAt (I := I) γ V s) s)
    (hVderiv : ∀ s, DifferentiableAt ℝ
      (chartRepAt (I := I) γ (fun u => covDerivAlong (I := I) g γ V u) s) s) :
    HasDerivAt (fun s : ℝ => deriv (fun u : ℝ => g.inner (γ u) (V u) (V u)) s)
      (2 * (g.inner (γ t) (covDerivAlong (I := I) g γ
          (fun s => covDerivAlong (I := I) g γ V s) t) (V t) +
        g.inner (γ t) (covDerivAlong (I := I) g γ V t)
          (covDerivAlong (I := I) g γ V t))) t := by
  have hfun : (fun s : ℝ => deriv (fun u : ℝ => g.inner (γ u) (V u) (V u)) s) =ᶠ[𝓝 t]
      (fun s : ℝ => 2 * g.inner (γ s) (covDerivAlong (I := I) g γ V s) (V s)) :=
    Filter.Eventually.of_forall fun s =>
      (inner_self_hasDerivAt_along (I := I) hn g γ V s hγ.contMDiffAt (hV s)).deriv
  exact hfun.hasDerivAt_iff.mpr (inner_self_kato_along (I := I) hn g γ V t
    hγ.contMDiffAt (hVderiv t) (hV t))

end CovariantDerivativeAlong
end Riemannian
end Geometry
end DifferentialGeometry
