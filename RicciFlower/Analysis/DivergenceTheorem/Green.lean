import RicciFlower.Analysis.DivergenceTheorem.LocalFormula
import RicciFlower.Analysis.DivergenceTheorem.Gradient
import RicciFlower.Analysis.DivergenceTheorem.Laplacian
import RicciFlower.Analysis.DivergenceTheorem.IntegrationByParts
import RicciFlower.Analysis.DivergenceTheorem.Closed
import RicciFlower.Analysis.DivergenceTheorem.Proper
import RicciFlower.Analysis.Volume.Properties

/-!
# Green's identities on a Riemannian manifold

For a smooth Riemannian metric `g` on a smooth manifold `M` (without boundary),
the integration-by-parts machinery established in `IntegrationByParts.lean`
combines with the gradient and Laplacian to yield Green's identities.

## Main results

* `integral_inner_grad_eq_neg_integral_smul_laplacian` (**Green's first identity**):
  for smooth `f, h : M → ℝ` with `h` having compact support,
  $$\int_M g(\nabla_g f, \nabla_g h)\,d\mu_g = -\int_M f \cdot \Delta_g h\,d\mu_g.$$

* `integral_smul_laplacian_sub_eq_zero` (**Green's second identity**):
  on a closed manifold, for any smooth `f, h : M → ℝ`,
  $$\int_M (f \cdot \Delta_g h - h \cdot \Delta_g f)\,d\mu_g = 0.$$
-/

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix

namespace RicciFlower
namespace Analysis
namespace DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open RicciFlower.Analysis.Volume

/-! ## File-local Borel-space instances

Match the convention in the surrounding files: `E` and `M` carry their canonical
Borel σ-algebras. Declared `local` to avoid leaking into callers. -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-! ## Green's first identity

For smooth `f, h : M → ℝ` with at least one compactly supported, the gradient
of `h` is a compactly-supported smooth tangent section, and we can apply the
basic integration-by-parts identity from `IntegrationByParts.lean` with this
section. The duality `tangentSectionAction X f x = g.inner x (X x) (grad_g f x)`
(provided by `tangentSectionAction_grad_g_eq_inner`) and the symmetry of the
metric yield the integrand `g.inner x (grad_g f x) (grad_g h x)`.

Because the divergence of `grad_g h` equals the Laplacian `Δ_g h`, the right-
hand side of the IBP identity becomes the integral of `f · Δ_g h`. -/

/-- **Green's first identity.** For smooth `f, h : M → ℝ` with `h` having
compact support on a σ-compact Hausdorff smooth Riemannian manifold `(M, g)`
without boundary,
$$\int_M g(\nabla_g f, \nabla_g h)\,d\mu_g = -\int_M f \cdot \Delta_g h\,d\mu_g.$$
-/
theorem integral_inner_grad_eq_neg_integral_smul_laplacian
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hh_supp : HasCompactSupport h) :
    ∫ x, g.inner x ((grad_g (I := I) g hf :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((grad_g (I := I) g hh :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      -∫ x, f x * Δ_g (I := I) g hh x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  -- Set X := grad_g g hh, which is a smooth tangent section with compact support.
  set X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := grad_g (I := I) g hh with hX_def
  have hX_cs : HasCompactSupport X := hasCompactSupport_grad_g (I := I) g hh hh_supp
  -- Apply identity (a) of `IntegrationByParts.lean` with this `X` and `f`.
  have h_ibp := integral_tangentSectionAction_eq_neg_integral_smul_divergence
    (I := I) g hf X hX_cs
  -- LHS of `h_ibp`: ∫ tangentSectionAction X f.
  -- By duality `tangentSectionAction X f x = g.inner x (X x) (grad_g g hf x)`
  -- (where `X = grad_g g hh`), this equals `g.inner x (grad_g g hh x) (grad_g g hf x)`.
  -- By symmetry of the metric, equals `g.inner x (grad_g g hf x) (grad_g g hh x)`.
  -- RHS of `h_ibp`: -∫ f x * divergence_g g X x = -∫ f x * Δ_g g hh x.
  -- Hence the result.
  have hLHS_eq : ∀ x : M,
      tangentSectionAction (I := I) X f x =
        g.inner x ((grad_g (I := I) g hf :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((grad_g (I := I) g hh :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) := by
    intro x
    rw [tangentSectionAction_grad_g_eq_inner (I := I) g hf X x]
    -- `tangentSectionAction_grad_g_eq_inner` gives:
    -- `tangentSectionAction X f x = g.inner x (X x) (grad_g g hf x)`.
    -- Now with `X = grad_g g hh`, this is `g.inner x (grad_g g hh x) (grad_g g hf x)`.
    -- Apply symmetry to swap.
    change g.inner x (X x) ((grad_g (I := I) g hf :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) =
      g.inner x ((grad_g (I := I) g hf :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) (X x)
    exact g.symm x _ _
  have hRHS_eq : ∀ x : M,
      f x * divergence_g (I := I) g X x = f x * Δ_g (I := I) g hh x := by
    intro x
    -- Δ_g g hh x = divergence_g g (grad_g g hh) x = divergence_g g X x by `hX_def`.
    rfl
  have hLHS_int : ∫ x, tangentSectionAction (I := I) X f x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, g.inner x ((grad_g (I := I) g hf :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((grad_g (I := I) g hh :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    integral_congr_ae (Filter.Eventually.of_forall hLHS_eq)
  have hRHS_int : ∫ x, f x * divergence_g (I := I) g X x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, f x * Δ_g (I := I) g hh x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    integral_congr_ae (Filter.Eventually.of_forall hRHS_eq)
  rw [← hLHS_int, h_ibp, hRHS_int]

/-! ## Green's second identity

On a closed manifold, both `f` and `h` automatically have compact support (since
the manifold is compact). Applying Green's first identity twice — once with `h`
compactly supported and once with `f` compactly supported — gives
$\int g(\nabla f, \nabla h) = -\int f \Delta h = -\int h \Delta f$, so the
integrand `f \Delta h - h \Delta f` integrates to zero.

We provide the symmetric variant of Green's first identity (with `f` having
compact support instead of `h`) as a corollary, then combine. -/

/-- A symmetric variant of Green's first identity, with the compact-support
hypothesis on `f` instead of `h`. -/
private theorem integral_inner_grad_eq_neg_integral_smul_laplacian'
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hf_supp : HasCompactSupport f) :
    ∫ x, g.inner x ((grad_g (I := I) g hf :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((grad_g (I := I) g hh :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      -∫ x, h x * Δ_g (I := I) g hf x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  -- Apply the IBP identity with `X = grad_g g hf` (compactly supported) and the scalar `h`.
  set X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := grad_g (I := I) g hf with hX_def
  have hX_cs : HasCompactSupport X := hasCompactSupport_grad_g (I := I) g hf hf_supp
  have h_ibp := integral_tangentSectionAction_eq_neg_integral_smul_divergence
    (I := I) g hh X hX_cs
  -- LHS: ∫ tangentSectionAction X h x = ∫ g.inner x (X x) (grad_g g hh x)
  --      = ∫ g.inner x (grad_g g hf x) (grad_g g hh x).
  -- RHS: -∫ h x * divergence_g g X x = -∫ h x * Δ_g g hf x.
  have hLHS_eq : ∀ x : M,
      tangentSectionAction (I := I) X h x =
        g.inner x ((grad_g (I := I) g hf :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((grad_g (I := I) g hh :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) := by
    intro x
    rw [tangentSectionAction_grad_g_eq_inner (I := I) g hh X x]
  have hRHS_eq : ∀ x : M,
      h x * divergence_g (I := I) g X x = h x * Δ_g (I := I) g hf x := by
    intro x; rfl
  have hLHS_int : ∫ x, tangentSectionAction (I := I) X h x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, g.inner x ((grad_g (I := I) g hf :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((grad_g (I := I) g hh :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    integral_congr_ae (Filter.Eventually.of_forall hLHS_eq)
  have hRHS_int : ∫ x, h x * divergence_g (I := I) g X x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, h x * Δ_g (I := I) g hf x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    integral_congr_ae (Filter.Eventually.of_forall hRHS_eq)
  rw [← hLHS_int, h_ibp, hRHS_int]

/-- **Green's second identity.** For smooth `f, h : M → ℝ` on a closed (compact
and boundaryless) smooth Riemannian manifold `(M, g)`,
$$\int_M (f \cdot \Delta_g h - h \cdot \Delta_g f)\,d\mu_g = 0.$$ -/
theorem integral_smul_laplacian_sub_eq_zero
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h) :
    ∫ x, (f x * Δ_g (I := I) g hh x - h x * Δ_g (I := I) g hf x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 := by
  classical
  -- On compact M, every continuous (or smooth) function has compact support.
  have hf_cs : HasCompactSupport f := HasCompactSupport.of_compactSpace _
  have hh_cs : HasCompactSupport h := HasCompactSupport.of_compactSpace _
  -- Green's first with `h` compactly supported.
  have h1 := integral_inner_grad_eq_neg_integral_smul_laplacian (I := I) g hf hh hh_cs
  -- Symmetric variant with `f` compactly supported.
  have h2 := integral_inner_grad_eq_neg_integral_smul_laplacian' (I := I) g hf hh hf_cs
  -- From `h1` and `h2`: -∫ f * Δh = -∫ h * Δf, so ∫ f * Δh = ∫ h * Δf.
  have h_eq : ∫ x, f x * Δ_g (I := I) g hh x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ∫ x, h x * Δ_g (I := I) g hf x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    -- Use h1.symm and h2 to relate both sides.
    have : -∫ x, f x * Δ_g (I := I) g hh x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
          -∫ x, h x * Δ_g (I := I) g hf x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
      rw [← h1, h2]
    linarith
  -- Now expand the integral of the difference.
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  -- Both `f * Δh` and `h * Δf` are continuous on compact `M`, hence integrable.
  have hΔh_cont : Continuous (Δ_g (I := I) g hh) :=
    (Δ_g_contMDiff (I := I) g hh).continuous
  have hΔf_cont : Continuous (Δ_g (I := I) g hf) :=
    (Δ_g_contMDiff (I := I) g hf).continuous
  have hf_cont : Continuous f := hf.continuous
  have hh_cont : Continuous h := hh.continuous
  have h_int_fΔh : Integrable (fun x : M => f x * Δ_g (I := I) g hh x)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    have hcont : Continuous (fun x : M => f x * Δ_g (I := I) g hh x) :=
      hf_cont.mul hΔh_cont
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h_int_hΔf : Integrable (fun x : M => h x * Δ_g (I := I) g hf x)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    have hcont : Continuous (fun x : M => h x * Δ_g (I := I) g hf x) :=
      hh_cont.mul hΔf_cont
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_sub h_int_fΔh h_int_hΔf]
  rw [h_eq, sub_self]

/-! ## Exponential weight identity -/

/-- General closed weighted Green identity in the form used before expanding
`Delta(exp(-f))`:
`∫ e^{-f} Delta q dmu = ∫ q Delta(e^{-f}) dmu`.

With the current convention in `integral_smul_laplacian_sub_eq_zero`, expanding
the right-hand side later gives
`q * e^{-f} * (-Delta f + |grad f|^2)`. -/
theorem expNegWeightedGreen
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f q : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hq : ContMDiff I 𝓘(ℝ, ℝ) ∞ q) :
    ∫ x, Real.exp (-(f x)) * Δ_g (I := I) g hq x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, q x *
        Δ_g (I := I) g
          (by
            simpa using Real.contDiff_exp.contMDiff.comp hf.neg) x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  let expNeg : M → ℝ := fun x => Real.exp (-(f x))
  have hexp : ContMDiff I 𝓘(ℝ, ℝ) ∞ expNeg := by
    simpa [expNeg] using Real.contDiff_exp.contMDiff.comp hf.neg
  have hgreen := integral_smul_laplacian_sub_eq_zero
    (I := I) g (f := expNeg) (h := q) hexp hq
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  have hΔq_cont : Continuous (Δ_g (I := I) g hq) :=
    (Δ_g_contMDiff (I := I) g hq).continuous
  have hΔexp_cont : Continuous (Δ_g (I := I) g hexp) :=
    (Δ_g_contMDiff (I := I) g hexp).continuous
  have hexp_cont : Continuous expNeg := hexp.continuous
  have hq_cont : Continuous q := hq.continuous
  have h_int_expΔq :
      Integrable (fun x : M => expNeg x * Δ_g (I := I) g hq x)
        (riemannianVolumeMeasure (I := I) (M := M) g) := by
    have hcont : Continuous (fun x : M => expNeg x * Δ_g (I := I) g hq x) :=
      hexp_cont.mul hΔq_cont
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h_int_qΔexp :
      Integrable (fun x : M => q x * Δ_g (I := I) g hexp x)
        (riemannianVolumeMeasure (I := I) (M := M) g) := by
    have hcont : Continuous (fun x : M => q x * Δ_g (I := I) g hexp x) :=
      hq_cont.mul hΔexp_cont
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hzero :
      ∫ x, expNeg x * Δ_g (I := I) g hq x -
          q x * Δ_g (I := I) g hexp x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 := by
    simpa [expNeg] using hgreen
  rw [integral_sub h_int_expΔq h_int_qΔexp] at hzero
  have h_eq :
      ∫ x, expNeg x * Δ_g (I := I) g hq x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, q x * Δ_g (I := I) g hexp x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    linarith
  simpa [expNeg] using h_eq

/-- Pointwise scalar expansion
`Delta(e^{-f}) = e^{-f} * (-Delta f + |grad f|^2)`. -/
theorem expNegLap
    [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    Δ_g (I := I) g
        (by
          simpa using Real.contDiff_exp.contMDiff.comp hf.neg) x =
      Real.exp (-(f x)) *
        (-Δ_g (I := I) g hf x +
          g.inner x ((grad_g (I := I) g hf :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((grad_g (I := I) g hf :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)) := by
  classical
  let expNeg : M → ℝ := fun y => Real.exp (-(f y))
  let phi : M → ℝ := fun y => -expNeg y
  have hexp : ContMDiff I 𝓘(ℝ, ℝ) ∞ expNeg := by
    simpa [expNeg] using Real.contDiff_exp.contMDiff.comp hf.neg
  have hphi : ContMDiff I 𝓘(ℝ, ℝ) ∞ phi := by
    simpa [phi] using hexp.neg
  have hsection :
      (grad_g (I := I) g hexp :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) =
        smoothSmul (I := I) phi hphi (grad_g (I := I) g hf) := by
    ext y
    rw [grad_g_apply, smoothSmul_apply, grad_g_apply]
    change gradFun (I := I) g (fun y : M => Real.exp (-(f y))) y =
      phi y • gradFun (I := I) g f y
    dsimp [phi, expNeg]
    exact gradFun_exp_neg (I := I) g (hf.mdifferentiable (by simp) y)
  have hactExp := tangentSectionAction_grad_g_eq_inner
    (I := I) g hexp (grad_g (I := I) g hf) x
  rw [hsection] at hactExp
  have hactPhi :
      tangentSectionAction (I := I) (grad_g (I := I) g hf) phi x =
        Real.exp (-(f x)) *
          g.inner x ((grad_g (I := I) g hf :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((grad_g (I := I) g hf :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) := by
    have hneg :
        tangentSectionAction (I := I) (grad_g (I := I) g hf) phi x =
          -tangentSectionAction (I := I) (grad_g (I := I) g hf) expNeg x := by
      have hmdiff_exp : MDifferentiableAt I 𝓘(ℝ, ℝ) expNeg x :=
        hexp.mdifferentiable (by simp) x
      have hmf :
          mfderiv I 𝓘(ℝ, ℝ) phi x =
            -mfderiv I 𝓘(ℝ, ℝ) expNeg x := by
        simpa [phi] using hmdiff_exp.hasMFDerivAt.neg.mfderiv
      change mfderiv I 𝓘(ℝ, ℝ) phi x
          ((grad_g (I := I) g hf :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) =
        -(mfderiv I 𝓘(ℝ, ℝ) expNeg x
          ((grad_g (I := I) g hf :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))
      rw [hmf]
      rfl
    rw [hneg, hactExp]
    rw [smoothSmul_apply, grad_g_apply]
    dsimp [phi, expNeg]
    simp [smul_eq_mul]
  change divergence_g (I := I) g
      (grad_g (I := I) g hexp) x = _
  rw [hsection]
  rw [divergence_g_smoothSmul (I := I) g phi hphi (grad_g (I := I) g hf) x]
  rw [hactPhi]
  simp [Δ_g, phi, expNeg]
  ring

/-- Expanded arbitrary-test weighted Green identity:
`∫ e^{-f} Delta q = ∫ q e^{-f}(-Delta f + |grad f|^2)`. -/
theorem expNegGreen
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f q : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hq : ContMDiff I 𝓘(ℝ, ℝ) ∞ q) :
    ∫ x, Real.exp (-(f x)) * Δ_g (I := I) g hq x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, q x *
        (Real.exp (-(f x)) *
          (-Δ_g (I := I) g hf x +
            g.inner x ((grad_g (I := I) g hf :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
              ((grad_g (I := I) g hf :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  rw [expNegWeightedGreen (I := I) g hf hq]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall ?_
  intro x
  change q x *
      Δ_g (I := I) g
        (by
          simpa using Real.contDiff_exp.contMDiff.comp hf.neg) x =
    q x *
      (Real.exp (-(f x)) *
        (-Δ_g (I := I) g hf x +
          g.inner x ((grad_g (I := I) g hf :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((grad_g (I := I) g hf :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)))
  rw [expNegLap (I := I) g hf x]

/-- Closed weighted identity used in Perelman's formula 5.10 route:
`∫ e^{-f} Δ f dμ_g = ∫ e^{-f} |∇ f|² dμ_g`. -/
theorem expNegLap_eq_gradSq
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ∫ x, Real.exp (-(f x)) * Δ_g (I := I) g hf x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, Real.exp (-(f x)) *
        g.inner x ((grad_g (I := I) g hf :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((grad_g (I := I) g hf :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  let expNeg : M → ℝ := fun x => Real.exp (-(f x))
  have hexp : ContMDiff I 𝓘(ℝ, ℝ) ∞ expNeg := by
    simpa [expNeg] using Real.contDiff_exp.contMDiff.comp hf.neg
  have hgreen :=
    integral_inner_grad_eq_neg_integral_smul_laplacian
      (I := I) g (f := expNeg) (h := f) hexp hf
      (HasCompactSupport.of_compactSpace f)
  have hleft :
      ∫ x, g.inner x ((grad_g (I := I) g hexp :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((grad_g (I := I) g hf :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ∫ x, -(Real.exp (-(f x)) *
          g.inner x ((grad_g (I := I) g hf :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((grad_g (I := I) g hf :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    apply integral_congr_ae
    refine Filter.Eventually.of_forall ?_
    intro x
    have hfx : MDifferentiableAt I 𝓘(ℝ, ℝ) f x :=
      hf.mdifferentiable (by simp) x
    change
      g.inner x ((grad_g (I := I) g hexp :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((grad_g (I := I) g hf :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) =
        -(Real.exp (-(f x)) *
          g.inner x ((grad_g (I := I) g hf :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((grad_g (I := I) g hf :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))
    rw [grad_g_apply (I := I) g hexp x, grad_g_apply (I := I) g hf x]
    dsimp [expNeg]
    change
      g.inner x (gradFun (I := I) g (fun y : M => Real.exp (-(f y))) x)
          (gradFun (I := I) g f x) =
        -(Real.exp (-(f x)) *
          g.inner x (gradFun (I := I) g f x)
            (gradFun (I := I) g f x))
    rw [gradFun_exp_neg (I := I) g hfx]
    rw [map_smul]
    rw [ContinuousLinearMap.smul_apply]
    rw [smul_eq_mul]
    ring_nf
  have hneg :
      -∫ x, Real.exp (-(f x)) *
          g.inner x ((grad_g (I := I) g hf :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((grad_g (I := I) g hf :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        -∫ x, Real.exp (-(f x)) * Δ_g (I := I) g hf x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    simpa [integral_neg, expNeg] using hleft.symm.trans hgreen
  exact (neg_injective hneg).symm

/-- Integral form of `∫ e^{-f}(Δf - |∇f|²)dμ_g = 0`.  The explicit
integrability hypotheses are separated because the geometric smoothness bridge
for `|∇f|²` is useful elsewhere and should live in the gradient layer. -/
theorem expNegIBP
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hlap :
      Integrable (fun x : M =>
        Real.exp (-(f x)) * Δ_g (I := I) g hf x)
        (riemannianVolumeMeasure (I := I) (M := M) g))
    (hgrad :
      Integrable (fun x : M =>
        Real.exp (-(f x)) *
          g.inner x ((grad_g (I := I) g hf :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((grad_g (I := I) g hf :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))
        (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ∫ x, Real.exp (-(f x)) *
        (Δ_g (I := I) g hf x -
          g.inner x ((grad_g (I := I) g hf :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((grad_g (I := I) g hf :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))
      ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 := by
  have hbase := expNegLap_eq_gradSq (I := I) g hf
  have hpoint :
      (fun x : M =>
        Real.exp (-(f x)) *
          (Δ_g (I := I) g hf x -
            g.inner x ((grad_g (I := I) g hf :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
              ((grad_g (I := I) g hf :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))) =
      fun x : M =>
        Real.exp (-(f x)) * Δ_g (I := I) g hf x -
          Real.exp (-(f x)) *
            g.inner x ((grad_g (I := I) g hf :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
              ((grad_g (I := I) g hf :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) := by
    funext x
    ring
  rw [hpoint]
  rw [integral_sub hlap hgrad]
  rw [hbase, sub_self]

end DivergenceTheorem
end Analysis
end RicciFlower
