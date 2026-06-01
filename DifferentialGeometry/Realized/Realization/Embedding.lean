import DifferentialGeometry.Realized.Realization.Basic
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.RingTheory.Derivation.Lie

/-!
# SmoothRicciFlow: Embedding of vector fields as derivations

This file defines the pointwise action of a smooth vector field on a smooth function,
proves the result is smooth, and packages the action as a `Derivation ℝ C^∞⟮I,M;ℝ⟯ C^∞⟮I,M;ℝ⟯`.

Given a smooth vector field `X : Cₛ^∞⟮I; E, TangentSpace I⟯` and a smooth function
`f : C^∞⟮I, M; ℝ⟯`, the directional derivative of `f` along `X` at each point `x` is:

  `vectorFieldAction X f x := extDerivFun f x (X x)`

## Main definitions

* `vectorFieldAction` : the pointwise action `X(f)(x) = df_x(X_x)`
* `vectorFieldActionSmooth` : the action packaged as a smooth function `C^∞⟮I, M; ℝ⟯`
* `embedDeriv` : the action packaged as a `Derivation ℝ C^∞⟮I,M;ℝ⟯ C^∞⟮I,M;ℝ⟯`

## Main results

* `vectorFieldActionSmooth_add` : additivity in the function argument
* `vectorFieldActionSmooth_smul` : ℝ-homogeneity in the function argument
* `vectorFieldActionSmooth_leibniz` : Leibniz rule `X(fg) = fX(g) + gX(f)`
* `vectorFieldActionSmooth_map_one_eq_zero` : `X(1) = 0`
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology
open Bundle

section Embedding

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- The pointwise action of a smooth vector field `X` on a smooth function `f`:
`vectorFieldAction X f x = extDerivFun f x (X x) = df_x(X_x)`. -/
noncomputable def vectorFieldAction
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (f : C^∞⟮I, M; ℝ⟯) : M → ℝ :=
  fun x => extDerivFun (I := I) f x (X x)

/-- The action of a smooth vector field on a smooth function is itself smooth.

The proof factors the action through the tangent map of `f` composed with the section `X`,
then extracts the fiber component using the trivialization of the model-space tangent bundle. -/
noncomputable def vectorFieldActionSmooth
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (f : C^∞⟮I, M; ℝ⟯) : C^∞⟮I, M; ℝ⟯ :=
  ⟨vectorFieldAction I M X f, by
    intro x₀
    -- Step 1: The tangent map of f is C^∞
    have hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := f.2
    have htangent : ContMDiff (I.prod 𝓘(ℝ, E)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
        (tangentMap I 𝓘(ℝ, ℝ) f) := by
      apply ContMDiff.contMDiff_tangentMap hf
      simp
    -- Step 2: Compose with the smooth section X to get M → TangentBundle 𝓘(ℝ,ℝ) ℝ
    have hcomp : ContMDiffAt I (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
        (fun x => tangentMap I 𝓘(ℝ, ℝ) f ⟨x, X x⟩) x₀ :=
      (htangent.contMDiffAt).comp x₀ (X.contMDiff.contMDiffAt)
    -- Step 3: Extract the fiber component using contMDiffAt_totalSpace
    rw [contMDiffAt_totalSpace] at hcomp
    obtain ⟨_, hfiber⟩ := hcomp
    -- hfiber gives smoothness of the trivialized fiber component.
    -- For the model space 𝓘(ℝ,ℝ), the trivialization is the identity
    -- (by trivializationAt_model_space_apply), so this is exactly our function.
    convert hfiber using 1
    ext x
    simp only [vectorFieldAction, extDerivFun, tangentMap,
      trivializationAt_model_space_apply]
    rfl⟩

/-! ## Part 2: Derivation properties of vectorFieldActionSmooth

We show that for each smooth vector field `X`, the map
`f ↦ vectorFieldActionSmooth I M X f` is a derivation `ℝ C^∞⟮I,M;ℝ⟯ C^∞⟮I,M;ℝ⟯`.
-/

/-- Helper: a smooth function `f : C^∞⟮I, M; ℝ⟯` is `MDifferentiableAt` at every point. -/
theorem contMDiffMap_mdifferentiableAt (f : C^∞⟮I, M; ℝ⟯) (x : M) :
    MDifferentiableAt I 𝓘(ℝ, ℝ) f x :=
  f.contMDiff.contMDiffAt.mdifferentiableAt (by simp)

/-- Additivity of `vectorFieldActionSmooth` in the function argument. -/
theorem vectorFieldActionSmooth_add
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (f g : C^∞⟮I, M; ℝ⟯) :
    vectorFieldActionSmooth I M X (f + g) =
      vectorFieldActionSmooth I M X f + vectorFieldActionSmooth I M X g := by
  ext x
  change vectorFieldAction I M X (f + g) x =
    vectorFieldAction I M X f x + vectorFieldAction I M X g x
  unfold vectorFieldAction
  rw [show ((f + g : C^∞⟮I, M; ℝ⟯) : M → ℝ) = (f : M → ℝ) + (g : M → ℝ) from rfl]
  rw [extDerivFun_add (contMDiffMap_mdifferentiableAt I M f x)
    (contMDiffMap_mdifferentiableAt I M g x)]
  simp [ContinuousLinearMap.add_apply]

/-- ℝ-homogeneity of `vectorFieldActionSmooth` in the function argument:
    `X(c • f) = c • X(f)` for `c : ℝ`. -/
theorem vectorFieldActionSmooth_smul
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (c : ℝ) (f : C^∞⟮I, M; ℝ⟯) :
    vectorFieldActionSmooth I M X (c • f) =
      c • vectorFieldActionSmooth I M X f := by
  ext x
  change vectorFieldAction I M X (c • f) x = c * vectorFieldAction I M X f x
  unfold vectorFieldAction
  rw [show ((c • f : C^∞⟮I, M; ℝ⟯) : M → ℝ) = c • (f : M → ℝ) from by
    ext y; simp [Pi.smul_apply, smul_eq_mul]]
  have hf := contMDiffMap_mdifferentiableAt I M f x
  have hmfderiv : mfderiv I 𝓘(ℝ, ℝ) (c • (f : M → ℝ)) x = c • mfderiv I 𝓘(ℝ, ℝ) f x :=
    (hf.hasMFDerivAt.const_smul c).mfderiv
  -- Unfold extDerivFun to fromTangentSpace.toCLM ∘L mfderiv, substitute hmfderiv
  simp only [extDerivFun, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    hmfderiv]
  -- fromTangentSpace on ℝ is the identity; reduce and conclude
  change (NormedSpace.fromTangentSpace _) ((c • mfderiv I 𝓘(ℝ, ℝ) (f : M → ℝ) x) (X x)) =
    c * (NormedSpace.fromTangentSpace _) ((mfderiv I 𝓘(ℝ, ℝ) (f : M → ℝ) x) (X x))
  simp only [NormedSpace.fromTangentSpace, ContinuousLinearEquiv.coe_mk, LinearEquiv.coe_mk]
  exact smul_eq_mul c _

/-- Leibniz rule for `vectorFieldActionSmooth`:
    `X(f * g) = f * X(g) + g * X(f)`. -/
theorem vectorFieldActionSmooth_leibniz
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (f g : C^∞⟮I, M; ℝ⟯) :
    vectorFieldActionSmooth I M X (f * g) =
      f * vectorFieldActionSmooth I M X g + g * vectorFieldActionSmooth I M X f := by
  ext x
  change vectorFieldAction I M X (f * g) x =
    (f : M → ℝ) x * vectorFieldAction I M X g x +
    (g : M → ℝ) x * vectorFieldAction I M X f x
  unfold vectorFieldAction
  have hf := contMDiffMap_mdifferentiableAt I M f x
  have hg := contMDiffMap_mdifferentiableAt I M g x
  -- Rewrite pointwise multiplication as scalar multiplication for mfderiv API
  rw [show ((f * g : C^∞⟮I, M; ℝ⟯) : M → ℝ) = (f : M → ℝ) • (g : M → ℝ) from by
    ext y; simp [Pi.mul_apply, smul_eq_mul]]
  -- Apply the product rule for mfderiv of scalar multiplication
  have h := fromTangentSpace_mfderiv_smul_apply (I := I) hf hg (X x)
  -- Align the goal with h using the fact that extDerivFun = fromTangentSpace ∘ mfderiv
  change (extDerivFun (I := I) ((f : M → ℝ) • (g : M → ℝ)) x) (X x) =
    (f : M → ℝ) x * (extDerivFun (I := I) (g : M → ℝ) x) (X x) +
    (g : M → ℝ) x * (extDerivFun (I := I) (f : M → ℝ) x) (X x)
  simp only [smul_eq_mul] at h
  exact h.trans (by
    simp only [extDerivFun, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
    ring)

/-- `vectorFieldActionSmooth X` kills the constant `1 : C^∞⟮I, M; ℝ⟯`. -/
theorem vectorFieldActionSmooth_map_one_eq_zero
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    vectorFieldActionSmooth I M X 1 = 0 := by
  ext x
  change vectorFieldAction I M X 1 x = 0
  unfold vectorFieldAction
  rw [show ((1 : C^∞⟮I, M; ℝ⟯) : M → ℝ) = fun (_ : M) => (1 : ℝ) from by ext; simp]
  rw [show extDerivFun (I := I) (fun (_ : M) => (1 : ℝ)) x (X x) =
    ((NormedSpace.fromTangentSpace (1 : ℝ)).toContinuousLinearMap ∘L
      mfderiv I 𝓘(ℝ, ℝ) (fun (_ : M) => (1 : ℝ)) x) (X x) from rfl]
  simp [mfderiv_const]

/-- The embedding of a smooth vector field as a derivation `ℝ C^∞⟮I,M;ℝ⟯ C^∞⟮I,M;ℝ⟯`.

For each smooth vector field `X`, the map `f ↦ vectorFieldActionSmooth I M X f`
is additive, ℝ-homogeneous, satisfies the Leibniz rule, and kills constants. -/
noncomputable def embedDeriv
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ where
  toLinearMap :=
    { toFun := vectorFieldActionSmooth I M X
      map_add' := vectorFieldActionSmooth_add I M X
      map_smul' := fun c f => by
        simp only [RingHom.id_apply]
        exact vectorFieldActionSmooth_smul I M X c f }
  leibniz' f g := by
    change vectorFieldActionSmooth I M X (f * g) =
      f • vectorFieldActionSmooth I M X g + g • vectorFieldActionSmooth I M X f
    rw [vectorFieldActionSmooth_leibniz I M X f g]
    simp [smul_eq_mul]
  map_one_eq_zero' := by
    change vectorFieldActionSmooth I M X 1 = 0
    exact vectorFieldActionSmooth_map_one_eq_zero I M X

/-! ## Part 3: C^∞(M)-linearity of embedDeriv in the vector field argument

We show that `embedDeriv` is `C^∞(M, ℝ)`-linear in X, i.e., it preserves addition
and scalar multiplication by smooth functions. This packages `embedDeriv` as a
`C^∞(M, ℝ)`-linear map from smooth sections of TM to derivations on `C^∞(M, ℝ)`.
-/

/-- Additivity of `embedDeriv` in the vector field argument:
    `embedDeriv (X + Y) = embedDeriv X + embedDeriv Y`.
    Each `extDerivFun f x` is a continuous linear map, so it preserves addition. -/
theorem embedDeriv_add
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    embedDeriv I M (X + Y) = embedDeriv I M X + embedDeriv I M Y := by
  ext f x
  change vectorFieldAction I M (X + Y) f x =
    vectorFieldAction I M X f x + vectorFieldAction I M Y f x
  simp only [vectorFieldAction, ContMDiffSection.coe_add, Pi.add_apply,
    ContinuousLinearMap.map_add]

/-- `C^∞(M)`-homogeneity of `embedDeriv` in the vector field argument:
    `embedDeriv (φ • X) = φ • embedDeriv X` for `φ : C^∞⟮I, M; ℝ⟯`.
    Each `extDerivFun f x` is a continuous linear map, so it preserves scalar
    multiplication. The `C^∞(M)`-module structure on derivations acts pointwise. -/
theorem embedDeriv_smul
    (φ : C^∞⟮I, M; ℝ⟯)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    embedDeriv I M (φ • X) = φ • embedDeriv I M X := by
  ext f x
  change vectorFieldAction I M (φ • X) f x =
    ((φ • embedDeriv I M X) f : M → ℝ) x
  simp only [vectorFieldAction]
  -- LHS: extDerivFun f x ((φ • X) x) = extDerivFun f x (φ x • X x)
  -- Since extDerivFun f x is a CLM: = φ x • extDerivFun f x (X x)
  rw [show (φ • X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x = φ x • X x from by
    simp [ContMDiffSection.coe_smulContMDiffMap]]
  rw [ContinuousLinearMap.map_smul]
  -- RHS: (φ • D) f = φ • D f, and (φ • g) x = φ x • g x = φ x * g x
  change φ x • extDerivFun (I := I) f x (X x) =
    ((φ • embedDeriv I M X) f : M → ℝ) x
  simp only [Derivation.coe_smul, Pi.smul_apply, smul_eq_mul]
  rfl

/-- The embedding of smooth vector fields as derivations is `C^∞(M)`-linear.

This packages `embedDeriv I M` as a `C^∞(M, ℝ)`-linear map from smooth sections
of the tangent bundle to derivations on the algebra of smooth functions. -/
noncomputable def embedLinearMap :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ →ₗ[C^∞⟮I, M; ℝ⟯]
      Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ where
  toFun := embedDeriv I M
  map_add' := embedDeriv_add I M
  map_smul' := embedDeriv_smul I M

/-! ## Part 4: Injectivity of embedLinearMap

We prove that `embedLinearMap I M` is injective: if `embedDeriv I M X = 0`
(i.e., `X(f) = 0` for all smooth functions `f`), then `X = 0` as a section.

The proof uses the contrapositive: if `X x₀ ≠ 0` for some `x₀ : M`, we construct
a smooth function `f` such that `extDerivFun f x₀ (X x₀) ≠ 0`.

The construction uses:
1. The extended chart `extChartAt I x₀`, whose `mfderiv` at `x₀` is invertible.
2. A coordinate functional that separates the nonzero image vector from zero.
3. A smooth bump function to extend the local coordinate function to a global smooth function.
-/

/-- The `mfderiv` of `extChartAt` at the center is injective (it is in fact a linear equivalence).
    If `v ≠ 0` then `mfderiv (extChartAt I x₀) x₀ v ≠ 0`. -/
private theorem mfderiv_extChartAt_ne_zero
    {x₀ : M} (v : TangentSpace I x₀) (hv : v ≠ 0) :
    mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) x₀ v ≠ 0 := by
  have hmem : x₀ ∈ (extChartAt I x₀).source := mem_extChartAt_source x₀
  have hinv := isInvertible_mfderiv_extChartAt (I := I) hmem
  intro h
  apply hv
  apply hinv.injective
  rw [h, map_zero]

/-- Injectivity of the embedding: if `embedDeriv I M X = 0` for all smooth functions,
    then `X = 0` as a smooth section of the tangent bundle. -/
theorem embedLinearMap_injective :
    Function.Injective (embedLinearMap I M) := by
  intro X Y hXY
  -- Reduce to showing X x = Y x for all x
  apply ContMDiffSection.ext
  intro x₀
  -- Suppose for contradiction that X x₀ ≠ Y x₀
  by_contra hne
  -- The difference D = X - Y satisfies embedDeriv I M D = 0
  have hD : embedLinearMap I M (X - Y) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact hXY
  -- So for all smooth f and all x: extDerivFun f x ((X - Y) x) = 0
  have hD_action : ∀ (f : C^∞⟮I, M; ℝ⟯) (x : M),
      vectorFieldAction I M (X - Y) f x = 0 := by
    intro f x
    have h := DFunLike.congr_fun (Derivation.ext_iff.mp hD f) x
    simpa [embedLinearMap, embedDeriv, vectorFieldActionSmooth] using h
  -- In particular, at x₀:
  set v := (X - Y) x₀ with hv_def
  have hv : v ≠ 0 := by
    intro heq
    apply hne
    have : X x₀ - Y x₀ = 0 := heq
    exact sub_eq_zero.mp this
  -- Step 1: mfderiv of extChartAt at x₀ applied to v is nonzero (chart mfderiv is invertible)
  have hmem : x₀ ∈ (extChartAt I x₀).source := mem_extChartAt_source x₀
  have hinv := isInvertible_mfderiv_extChartAt (I := I) hmem
  set w := mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) x₀ v
  have hw : w ≠ 0 := by
    intro heq
    apply hv
    apply hinv.injective
    rw [map_zero]; exact heq
  -- Step 2: Find a coordinate functional ℓ : E →ₗ[ℝ] ℝ with ℓ(w) ≠ 0
  have : ∃ i, (Module.finBasis ℝ E).coord i w ≠ 0 := by
    by_contra h
    apply hw
    simp only [not_exists, not_not] at h
    exact (Module.finBasis ℝ E).forall_coord_eq_zero_iff.mp h
  obtain ⟨i, hi⟩ := this
  set ℓ := (Module.finBasis ℝ E).coord i
  set ℓ_clm := LinearMap.toContinuousLinearMap ℓ
  -- Step 3: Construct the global smooth test function
  -- Take a smooth bump function at x₀
  obtain ⟨ψ⟩ : Nonempty (SmoothBumpFunction I x₀) := inferInstance
  -- Define local function g(x) = ℓ(extChartAt I x₀ x - extChartAt I x₀ x₀)
  set g : M → ℝ := fun x => ℓ_clm (extChartAt I x₀ x - extChartAt I x₀ x₀)
  -- g is smooth on the chart source
  have hg_smooth : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ g (chartAt H x₀).source := by
    apply ContinuousLinearMap.contMDiff (𝕜 := ℝ) (ℓ_clm) |>.comp_contMDiffOn
    exact (contMDiffOn_extChartAt (I := I)).sub contMDiffOn_const
  -- f := ψ • g is globally smooth
  have hf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => ψ x • g x) :=
    ψ.contMDiff_smul hg_smooth
  set f : C^∞⟮I, M; ℝ⟯ := ⟨fun x => ψ x • g x, fun x => hf_smooth.contMDiffAt⟩
  -- Step 4: Near x₀, ψ = 1, so f = g locally
  have hψ_eq_one : ψ =ᶠ[𝓝 x₀] 1 := ψ.eventuallyEq_one
  have hf_eq_g : (fun x => ψ x • g x) =ᶠ[𝓝 x₀] g := by
    filter_upwards [hψ_eq_one] with x hx
    simp [hx]
  -- mfderiv of f at x₀ equals mfderiv of g at x₀
  have hf_mfderiv : mfderiv I 𝓘(ℝ, ℝ) (fun x => ψ x • g x) x₀ = mfderiv I 𝓘(ℝ, ℝ) g x₀ :=
    hf_eq_g.mfderiv_eq
  -- Step 5: Compute mfderiv of g at x₀
  have h_ext_diff : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I x₀) x₀ :=
    mdifferentiableAt_extChartAt (mem_chart_source H x₀)
  have h_sub_diff : MDifferentiableAt I 𝓘(ℝ, E)
      (fun x => extChartAt I x₀ x - extChartAt I x₀ x₀) x₀ :=
    h_ext_diff.sub mdifferentiableAt_const
  -- g = ℓ_clm ∘ (extChartAt - const), which has same mfderiv as ℓ_clm ∘ extChartAt
  have h_mfderiv_g : mfderiv I 𝓘(ℝ, ℝ) g x₀ =
      ℓ_clm.comp (mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) x₀) := by
    -- Step 1: g =ᶠ ℓ_clm ∘ extChartAt - const (using linearity of ℓ_clm)
    have hg_eq : g =ᶠ[𝓝 x₀]
        ((fun x => ℓ_clm (extChartAt I x₀ x)) - fun _ => ℓ_clm (extChartAt I x₀ x₀)) := by
      filter_upwards with x
      simp [g, sub_eq_add_neg]
    -- Step 2: mfderiv g = mfderiv (ℓ_clm ∘ extChartAt - const)
    rw [hg_eq.mfderiv_eq]
    -- Step 3: mfderiv of (f - const) = mfderiv f
    have h_comp_diff : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun x => ℓ_clm (extChartAt I x₀ x)) x₀ :=
      ℓ_clm.mdifferentiableAt.comp x₀ h_ext_diff
    rw [mfderiv_sub h_comp_diff mdifferentiableAt_const, mfderiv_const, sub_zero]
    -- Step 4: chain rule: mfderiv (ℓ_clm ∘ extChartAt) = ℓ_clm ∘L mfderiv extChartAt
    rw [show (fun x => ℓ_clm (extChartAt I x₀ x)) = ℓ_clm ∘ (extChartAt I x₀) from rfl]
    rw [mfderiv_comp x₀ ℓ_clm.mdifferentiableAt h_ext_diff, ℓ_clm.mfderiv_eq]
  -- Step 6: Derive contradiction
  -- vectorFieldAction (X - Y) f x₀ = 0 (from hD_action)
  have h_zero := hD_action f x₀
  -- The action at x₀ is: extDerivFun (↑f) x₀ v
  -- = (fromTangentSpace (f x₀)) ∘L mfderiv (↑f) x₀) v
  -- = (fromTangentSpace _) (mfderiv g x₀ v)     [since f =ᶠ g near x₀]
  -- = (fromTangentSpace _) (ℓ_clm (mfderiv (extChartAt) x₀ v))  [by chain rule]
  -- = (fromTangentSpace _) (ℓ_clm w)
  -- But ℓ w ≠ 0 and fromTangentSpace is an equiv, so this is ≠ 0. Contradiction.
  -- Compute: mfderiv f x₀ v = ℓ_clm w
  have hf_mfderiv_v : mfderiv I 𝓘(ℝ, ℝ) (f : M → ℝ) x₀ v = ℓ_clm w := by
    have h1 : mfderiv I 𝓘(ℝ, ℝ) (f : M → ℝ) x₀ = mfderiv I 𝓘(ℝ, ℝ) g x₀ := hf_mfderiv
    rw [h1, h_mfderiv_g]
    rfl
  -- The action value is:
  -- vectorFieldAction (X - Y) f x₀
  -- = extDerivFun (↑f) x₀ v
  -- = (fromTangentSpace (f x₀)) (mfderiv (↑f) x₀ v)
  -- = (fromTangentSpace _) (ℓ_clm w)
  -- This must equal 0, but ℓ w ≠ 0.
  -- Expand h_zero to get a contradiction
  change extDerivFun (I := I) (f : M → ℝ) x₀ ((X - Y) x₀) = 0 at h_zero
  -- extDerivFun = fromTangentSpace ∘L mfderiv
  rw [show extDerivFun (I := I) (f : M → ℝ) x₀ ((X - Y) x₀) =
    (NormedSpace.fromTangentSpace ((f : M → ℝ) x₀))
      (mfderiv I 𝓘(ℝ, ℝ) (f : M → ℝ) x₀ v) from rfl] at h_zero
  rw [hf_mfderiv_v] at h_zero
  -- h_zero : (fromTangentSpace _) (ℓ_clm w) = 0
  -- fromTangentSpace is an equiv, so ℓ_clm w = 0
  have h_ℓw : (ℓ_clm : E → ℝ) w = 0 :=
    (NormedSpace.fromTangentSpace ((f : M → ℝ) x₀)).injective
      (by rw [map_zero]; exact h_zero)
  exact hi h_ℓw

/-! ## Part 5: Bracket closure — the Lie bracket of embedded derivations is again embedded

We prove that for smooth vector fields `X, Y`, the derivation Lie bracket
`⁅embedLinearMap X, embedLinearMap Y⁆` is in the image of `embedLinearMap`.
The witness is `mlieBracket I X Y`, Mathlib's Lie bracket of vector fields.

The proof proceeds in two stages:
1. Construct `mlieBracket I X Y` as a smooth section (using `ContDiff.mlieBracket_vectorField`).
2. Prove the key identity: for all smooth `f` and all `x`,
   `extDerivFun f x (mlieBracket I X Y x) = X(Y(f))(x) - Y(X(f))(x)`.

For the key identity, we work in chart coordinates where `mlieBracket` reduces to the
vector space `lieBracket` (via `mlieBracketWithin_eq_lieBracketWithin`), and the identity
follows from the chain rule (`HasFDerivAt.clm_apply`) and symmetry of second derivatives
(`IsSymmSndFDerivAt`).
-/

/-- The Lie bracket of two smooth vector fields, packaged as a smooth section.
Uses `ContDiff.mlieBracket_vectorField` from Mathlib to establish smoothness. -/
noncomputable def mlieBracketSection
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  ⟨VectorField.mlieBracket I X Y, by
    have hX := X.contMDiff
    have hY := Y.contMDiff
    -- The Lie bracket of C^∞ vector fields is C^∞.
    -- We use ContMDiffAt.mlieBracket_vectorField with m = ∞ and n = ∞.
    -- Need: IsManifold I (∞ + 1) M and minSmoothness ℝ (∞ + 1) ≤ ∞.
    -- In ℕ∞, ∞ + 1 = ∞, so both reduce to what we already have.
    -- We need several IsManifold instances that Lean can't find automatically.
    -- For ℝ-manifolds: minSmoothness ℝ n = n, and ∞ + 1 = ∞ in ℕ∞.
    -- Provide IsManifold instances needed by mlieBracket_vectorField
    haveI : IsManifold I (minSmoothness ℝ 2) M := by
      rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
    haveI : IsManifold I (minSmoothness ℝ 3) M := by
      rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
    -- The Lie bracket of C^∞ vector fields is C^∞.
    -- We directly use ContDiff.mlieBracket_vectorField after providing the needed instance.
    -- The function needs [IsManifold I (n + 1) M] where n : ℕ∞.
    -- For n = ⊤ : ℕ∞, (⊤ + 1 : ℕ∞) = ⊤, so IsManifold I ↑⊤ M = IsManifold I ∞ M.
    -- We just need Lean to see through this.
    -- Use ContDiff.mlieBracket_vectorField with n = ⊤ : ℕ∞, m = ⊤ : ℕ∞.
    -- Need: IsManifold I (⊤ + 1) M and minSmoothness ℝ (⊤ + 1) ≤ ⊤.
    -- Both follow from ⊤ + 1 = ⊤ in ℕ∞.
    -- Provide IsManifold I ((⊤ : ℕ∞) + 1) M needed by mlieBracket_vectorField.
    -- In ℕ∞, ⊤ + 1 = ⊤, so this is just IsManifold I ∞ M which we have.
    haveI : IsManifold I ((⊤ : ℕ∞) + 1) M := by
      have : ((⊤ : ℕ∞) + 1 : WithTop ℕ∞) = ∞ := by
        show ((⊤ : ℕ∞) + 1 : WithTop ℕ∞) = ∞
        simp
      exact this ▸ ‹IsManifold I ∞ M›
    exact ContDiff.mlieBracket_vectorField (I := I) (m := (⊤ : ℕ∞)) (n := (⊤ : ℕ∞))
      hX hY (by
        rw [minSmoothness_of_isRCLikeNormedField]
        show ((⊤ : ℕ∞) + 1 : WithTop ℕ∞) ≤ ∞
        simp)⟩

/-- The embedding of the Lie bracket equals the commutator of embeddings.
The proof reduces to the model-space identity `fderivWithin_apply_lieBracket` via chart transfer. -/
theorem embedDeriv_mlieBracket
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (f : C^∞⟮I, M; ℝ⟯) :
    embedDeriv I M (mlieBracketSection I M X Y) f =
      embedDeriv I M X (embedDeriv I M Y f) -
      embedDeriv I M Y (embedDeriv I M X f) := by
  ext x₀
  change vectorFieldAction I M (mlieBracketSection I M X Y) f x₀ =
    vectorFieldAction I M X (vectorFieldActionSmooth I M Y f) x₀ -
    vectorFieldAction I M Y (vectorFieldActionSmooth I M X f) x₀
  simp only [vectorFieldAction, mlieBracketSection, ContMDiffSection.coeFn_mk]
  simp only [extDerivFun, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  simp only [NormedSpace.fromTangentSpace, ContinuousLinearEquiv.coe_mk, LinearEquiv.coe_mk]
  -- Setup chart coordinates
  set φ := extChartAt I x₀ with hφ
  set y₀ := φ x₀ with hy₀
  set s := Set.range I with hs
  have hmem : x₀ ∈ φ.source := mem_extChartAt_source x₀
  have hmem_tgt : y₀ ∈ φ.target := φ.map_source hmem
  have huniq : UniqueDiffOn ℝ s := I.uniqueDiffOn
  have hy₀s : y₀ ∈ s := ⟨_, rfl⟩
  set g := (f : M → ℝ) ∘ φ.symm
  set V' := VectorField.mpullbackWithin 𝓘(ℝ, E) I φ.symm (fun x => X x) s
  set W' := VectorField.mpullbackWithin 𝓘(ℝ, E) I φ.symm (fun x => Y x) s
  -- mfderiv I 𝓘(ℝ,ℝ) h x₀ = fderivWithin ℝ (h ∘ φ⁻¹) s y₀
  have mfderiv_eq : ∀ (h : M → ℝ), MDifferentiableAt I 𝓘(ℝ, ℝ) h x₀ →
      mfderiv I 𝓘(ℝ, ℝ) h x₀ = fderivWithin ℝ (h ∘ φ.symm) s y₀ := by
    intro h hh; simp only [mfderiv, if_pos hh]; congr 1
  have hf_diff : MDifferentiableAt I 𝓘(ℝ, ℝ) (f : M → ℝ) x₀ :=
    f.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  rw [mfderiv_eq _ hf_diff]
  -- mlieBracket = lieBracketWithin via mfderiv_extChartAt_self
  have bracket_eq : VectorField.mlieBracket I (fun x => X x) (fun x => Y x) x₀ =
      VectorField.lieBracketWithin ℝ V' W' s y₀ := by
    have h1 : VectorField.mlieBracket I (fun x => X x) (fun x => Y x) x₀ =
        (mfderiv I 𝓘(ℝ, E) φ x₀).inverse
          (VectorField.lieBracketWithin ℝ V' W' (↑φ.symm ⁻¹' Set.univ ∩ s) y₀) :=
      VectorField.mlieBracketWithin_apply
    rw [h1, mfderiv_extChartAt_self (I := I)]
    erw [ContinuousLinearMap.inverse_id, ContinuousLinearMap.id_apply]
    simp only [Set.preimage_univ, Set.univ_inter]
  rw [bracket_eq]
  -- V' y₀ = X x₀, W' y₀ = Y x₀
  have hV'_y₀ : V' y₀ = X x₀ := by
    simp only [V', VectorField.mpullbackWithin]
    rw [φ.left_inv hmem]
    exact mfderivWithin_extChartAt_symm_inverse_apply (I := I) _
  have hW'_y₀ : W' y₀ = Y x₀ := by
    simp only [W', VectorField.mpullbackWithin]
    rw [φ.left_inv hmem]
    exact mfderivWithin_extChartAt_symm_inverse_apply (I := I) _
  -- Smoothness of g
  have hg_smooth : ContDiffWithinAt ℝ ∞ g s y₀ :=
    (contMDiffAt_iff.mp (f.contMDiff.contMDiffAt (x := x₀))).2
  -- y₀ ∈ closure (interior s)
  have hy₀_closure : y₀ ∈ closure (interior s) := I.range_subset_closure_interior hy₀s
  -- DifferentiableWithinAt for V', W'
  have hV'_diff : DifferentiableWithinAt ℝ V' s y₀ := by
    have hX_mdiff : MDifferentiableWithinAt _ _
        (fun x => (⟨x, X x⟩ : TangentBundle I M)) Set.univ x₀ :=
      X.contMDiff.contMDiffAt.mdifferentiableAt (by simp) |>.mdifferentiableWithinAt
    have h := hX_mdiff.differentiableWithinAt_mpullbackWithin_vectorField (I := I)
    simp only [Set.preimage_univ, Set.univ_inter] at h
    exact h
  have hW'_diff : DifferentiableWithinAt ℝ W' s y₀ := by
    have hY_mdiff : MDifferentiableWithinAt _ _
        (fun x => (⟨x, Y x⟩ : TangentBundle I M)) Set.univ x₀ :=
      Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp) |>.mdifferentiableWithinAt
    have h := hY_mdiff.differentiableWithinAt_mpullbackWithin_vectorField (I := I)
    simp only [Set.preimage_univ, Set.univ_inter] at h
    exact h
  -- RHS differentiability
  have hYf_diff : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (vectorFieldActionSmooth I M Y f : M → ℝ) x₀ :=
    (vectorFieldActionSmooth I M Y f).contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hXf_diff : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (vectorFieldActionSmooth I M X f : M → ℝ) x₀ :=
    (vectorFieldActionSmooth I M X f).contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  -- Reduce to fderivWithin equality
  suffices hsuff : fderivWithin ℝ g s y₀ (VectorField.lieBracketWithin ℝ V' W' s y₀) =
    fderivWithin ℝ (↑(vectorFieldActionSmooth I M Y f) ∘ ↑φ.symm) s y₀ (X x₀) -
    fderivWithin ℝ (↑(vectorFieldActionSmooth I M X f) ∘ ↑φ.symm) s y₀ (Y x₀) by
    simp only [mfderiv_eq _ hYf_diff, mfderiv_eq _ hXf_diff] at hsuff ⊢
    exact hsuff
  -- Yf ∘ φ⁻¹ =ᶠ fun y => fderivWithin g s y (W' y) near y₀ within s
  -- For y ∈ φ.target, Yf(φ.symm y) = mfderiv f (φ.symm y) (Y(φ.symm y))
  -- and fderivWithin g s y (W' y) = fderivWithin g s y ((mfderivWithin φ.symm s y).inverse (Y(φ.symm y)))
  -- The key identity follows from:
  -- mfderiv f z = fderivWithin (writtenInExtChartAt) s (φ z), where writtenInExtChartAt = g ∘ chartchange
  -- At z ∈ φ.source: f =ᶠ g ∘ φ near z, so mfderiv f z = mfderiv (g∘φ) z
  -- By chain rule: mfderiv (g∘φ) z v = mfderiv g (φ z) (mfderiv φ z v)
  -- For model space: mfderiv g y = fderiv g y
  -- And W'(φ z) = mfderiv φ z (Y z) by definition of mpullbackWithin and invertibility
  -- So mfderiv f z (Y z) = fderiv g (φ z) (W'(φ z))
  -- The remaining issue is fderiv vs fderivWithin, handled by DifferentiableAt
  -- Helper: mfderiv f z = fderivWithin g s (φ z) ∘L mfderiv φ z for z ∈ φ.source
  -- This follows from f =ᶠ g ∘ φ near z, the manifold chain rule within φ.source,
  -- and mfderivWithin_eq_fderivWithin for the model space.
  -- Chain rule: mfderiv f z = fderivWithin g s (φ z) ∘L mfderiv φ z for z ∈ φ.source
  -- Proof: f =ᶠ g ∘ φ near z; by manifold chain rule within φ.source (open),
  -- mfderiv (g∘φ) z = mfderivWithin g s (φ z) ∘L mfderiv φ z;
  -- for model space, mfderivWithin = fderivWithin.
  have mfderiv_fderivWithin_chain : ∀ z ∈ φ.source,
      mfderiv I 𝓘(ℝ, ℝ) (f : M → ℝ) z =
        (fderivWithin ℝ g s (φ z)).comp (mfderiv I 𝓘(ℝ, E) φ z) := by
    intro z hz
    -- Step 1: Basic chart facts
    have hφ_open : IsOpen φ.source := isOpen_extChartAt_source x₀
    have hz_chart : z ∈ (chartAt H x₀).source := by
      rwa [extChartAt_source (I := I)] at hz
    have hφz_tgt : φ z ∈ φ.target := φ.map_source hz
    -- Step 2: f =ᶠ g ∘ φ near z (since φ.left_inv on φ.source)
    have hf_eq : (f : M → ℝ) =ᶠ[𝓝 z] g ∘ φ := by
      filter_upwards [hφ_open.mem_nhds hz] with w hw
      simp only [Function.comp_def, g, φ.left_inv hw]
    -- Step 3: mfderiv f z = mfderiv (g ∘ φ) z
    rw [hf_eq.mfderiv_eq]
    -- Step 4: φ is MDifferentiableAt/Within at z
    have hφ_diff : MDifferentiableAt I 𝓘(ℝ, E) φ z :=
      mdifferentiableAt_extChartAt hz_chart
    have hφ_diffWithin : MDifferentiableWithinAt I 𝓘(ℝ, E) φ φ.source z :=
      hφ_diff.mdifferentiableWithinAt
    -- Step 5: g is DifferentiableWithinAt within s at φ z
    -- Use contMDiffAt_iff which gives ContDiffWithinAt for writtenInExtChartAt
    -- For f : M → ℝ smooth at z, with chart φ = extChartAt I x₀:
    -- writtenInExtChartAt I 𝓘(ℝ,ℝ) z f = extChartAt 𝓘(ℝ,ℝ) (f z) ∘ f ∘ (extChartAt I z).symm
    -- We need g = f ∘ φ.symm differentiable within s at φ z.
    -- Use that f ∘ φ.symm = f ∘ (extChartAt I x₀).symm is ContDiffWithinAt ∞ within range I at φ z
    -- via chart compatibility.
    have hg_diffWithin : DifferentiableWithinAt ℝ g s (φ z) := by
      -- f is smooth, hence ContMDiffAt I 𝓘(ℝ,ℝ) at φ.symm (φ z) = z
      have hf_at_z := f.contMDiff.contMDiffAt (x := z)
      -- φ.symm is ContMDiffWithinAt 𝓘(ℝ,E) I within s at φ z
      have hφsymm : ContMDiffWithinAt 𝓘(ℝ, E) I ∞ φ.symm s (φ z) :=
        contMDiffWithinAt_extChartAt_symm_range x₀ hφz_tgt
      -- Compose: g = f ∘ φ.symm is ContMDiffWithinAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ) within s at φ z
      have hg_cmd : ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g s (φ z) := by
        have h_eq : φ.symm (φ z) = z := φ.left_inv hz
        exact hf_at_z.comp_contMDiffWithinAt_of_eq hφsymm h_eq
      -- For maps between model spaces, ContMDiffWithinAt ↔ ContDiffWithinAt
      exact (contMDiffWithinAt_iff_contDiffWithinAt.mp hg_cmd).differentiableWithinAt
        (by simp : (∞ : WithTop ℕ∞) ≠ 0)
    have hg_mdiffWithin : MDifferentiableWithinAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g s (φ z) :=
      mdifferentiableWithinAt_iff_differentiableWithinAt.mpr hg_diffWithin
    -- Step 6: φ maps φ.source into s = range I
    have h_maps : φ.source ⊆ φ ⁻¹' s := fun w hw =>
      extChartAt_target_subset_range x₀ (φ.map_source hw)
    -- Step 7: UniqueMDiffWithinAt on open set φ.source
    have hUniq : UniqueMDiffWithinAt I φ.source z :=
      hφ_open.uniqueMDiffWithinAt hz
    -- Step 8: Within-chain rule
    have hchain := mfderivWithin_comp z hg_mdiffWithin hφ_diffWithin h_maps hUniq
    -- Step 9: Simplify mfderivWithin to mfderiv on open set φ.source
    rw [mfderivWithin_eq_mfderiv hUniq hφ_diff] at hchain
    have hgφ_diff : MDifferentiableAt I 𝓘(ℝ, ℝ) (g ∘ φ) z := by
      have hf_mdiff : MDifferentiableAt I 𝓘(ℝ, ℝ) (f : M → ℝ) z :=
        f.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
      exact hf_eq.mdifferentiableAt_iff.mp hf_mdiff
    rw [mfderivWithin_eq_mfderiv hUniq hgφ_diff] at hchain
    -- Step 10: mfderivWithin on model space = fderivWithin
    rw [mfderivWithin_eq_fderivWithin] at hchain
    exact hchain
  -- W' y = (mfderivWithin φ.symm s y).inverse (Y(φ.symm y))
  -- = mfderiv φ (φ.symm y) (Y(φ.symm y)) when y ∈ φ.target
  -- So fderivWithin g s y (W' y) = fderivWithin g s y (mfderiv φ (φ.symm y) (Y(φ.symm y)))
  -- = mfderiv f (φ.symm y) (Y(φ.symm y)) by mfderiv_fderivWithin_chain
  -- For y ∈ φ.target: mfderiv f (φ.symm y) (V(φ.symm y)) = fderivWithin g s y (V' y)
  -- This follows from mfderiv_fderivWithin_chain and invertibility of chart derivatives:
  -- mfderiv f z (V z) = fderivWithin g s (φ z) (mfderiv φ z (V z))
  --                    = fderivWithin g s (φ z) (V'(φ z))
  -- where the last step uses V'(φ z) = (mfderivWithin φ.symm s (φ z)).inverse (V z) = mfderiv φ z (V z)
  -- EventuallyEq: Yf ∘ φ.symm =ᶠ fun y => fderivWithin g s y (W' y)
  -- For y ∈ φ.target: by mfderiv_fderivWithin_chain and invertibility of chart derivatives,
  -- mfderiv f (φ.symm y) (Y(φ.symm y)) = fderivWithin g s y (mfderiv φ (φ.symm y) (Y(φ.symm y)))
  --   = fderivWithin g s y (W' y)
  -- where W' y = (mfderivWithin φ.symm s y).inverse (Y(φ.symm y)) = mfderiv φ (φ.symm y) (Y(φ.symm y))
  -- Helper: for y ∈ φ.target, W' y = mfderiv φ (φ.symm y) (Y (φ.symm y))
  -- This follows from inverse_eq applied to the chart derivative pair.
  have W'_eq : ∀ y ∈ φ.target,
      W' y = mfderiv I 𝓘(ℝ, E) φ (φ.symm y) (Y (φ.symm y)) := by
    intro y hy
    simp only [W', VectorField.mpullbackWithin_apply]
    congr 1
    exact ContinuousLinearMap.inverse_eq
      (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt (I := I) hy)
      (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := I) hy)
  have V'_eq : ∀ y ∈ φ.target,
      V' y = mfderiv I 𝓘(ℝ, E) φ (φ.symm y) (X (φ.symm y)) := by
    intro y hy
    change (mfderivWithin 𝓘(ℝ, E) I φ.symm s y).inverse (X (φ.symm y)) =
      mfderiv I 𝓘(ℝ, E) φ (φ.symm y) (X (φ.symm y))
    congr 1
    exact ContinuousLinearMap.inverse_eq
      (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt (I := I) hy)
      (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := I) hy)
  -- Helper: extDerivFun f x v = mfderiv f x v (since fromTangentSpace on ℝ is id)
  have extDerivFun_eq_mfderiv : ∀ (x : M) (v : TangentSpace I x),
      extDerivFun (I := I) (f : M → ℝ) x v = mfderiv I 𝓘(ℝ, ℝ) (f : M → ℝ) x v := by
    intro x v
    simp only [extDerivFun, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
    simp only [NormedSpace.fromTangentSpace, ContinuousLinearEquiv.coe_mk, LinearEquiv.coe_mk]
    rfl
  have hYf_eq : (↑(vectorFieldActionSmooth I M Y f) ∘ ↑φ.symm) =ᶠ[𝓝[s] y₀]
      (fun y => fderivWithin ℝ g s y (W' y)) := by
    filter_upwards [extChartAt_target_mem_nhdsWithin_of_mem hmem_tgt] with y hy
    simp only [Function.comp_def, vectorFieldActionSmooth, ContMDiffMap.coeFn_mk,
      vectorFieldAction]
    rw [extDerivFun_eq_mfderiv]
    -- y ∈ φ.target, φ.symm y ∈ φ.source
    have hy_src : φ.symm y ∈ φ.source := φ.map_target hy
    -- By mfderiv_fderivWithin_chain at z = φ.symm y:
    have h1 := mfderiv_fderivWithin_chain (φ.symm y) hy_src
    -- mfderiv f (φ.symm y) (Y (φ.symm y)) = fderivWithin g s (φ (φ.symm y)) (mfderiv φ (φ.symm y) (Y (φ.symm y)))
    have h2 : mfderiv I 𝓘(ℝ, ℝ) (f : M → ℝ) (φ.symm y) (Y (φ.symm y)) =
        fderivWithin ℝ g s (φ (φ.symm y)) (mfderiv I 𝓘(ℝ, E) φ (φ.symm y) (Y (φ.symm y))) := by
      rw [h1]; rfl
    rw [h2, φ.right_inv hy]; congr 1; exact (W'_eq y hy).symm
  have hXf_eq : (↑(vectorFieldActionSmooth I M X f) ∘ ↑φ.symm) =ᶠ[𝓝[s] y₀]
      (fun y => fderivWithin ℝ g s y (V' y)) := by
    filter_upwards [extChartAt_target_mem_nhdsWithin_of_mem hmem_tgt] with y hy
    simp only [Function.comp_def, vectorFieldActionSmooth, ContMDiffMap.coeFn_mk,
      vectorFieldAction]
    rw [extDerivFun_eq_mfderiv]
    have hy_src : φ.symm y ∈ φ.source := φ.map_target hy
    have h1 := mfderiv_fderivWithin_chain (φ.symm y) hy_src
    have h2 : mfderiv I 𝓘(ℝ, ℝ) (f : M → ℝ) (φ.symm y) (X (φ.symm y)) =
        fderivWithin ℝ g s (φ (φ.symm y)) (mfderiv I 𝓘(ℝ, E) φ (φ.symm y) (X (φ.symm y))) := by
      rw [h1]; rfl
    rw [h2, φ.right_inv hy]; congr 1; exact (V'_eq y hy).symm
  rw [hYf_eq.fderivWithin_eq (hYf_eq.self_of_nhdsWithin hy₀s),
      hXf_eq.fderivWithin_eq (hXf_eq.self_of_nhdsWithin hy₀s)]
  rw [← hV'_y₀, ← hW'_y₀]
  exact VectorField.fderivWithin_apply_lieBracket hg_smooth
    (by rw [minSmoothness_of_isRCLikeNormedField]; norm_cast)
    huniq hy₀_closure hy₀s hW'_diff hV'_diff


/-- The Lie bracket of two smooth vector fields, when embedded as derivations,
equals the derivation Lie bracket (commutator) of the individual embeddings. -/
theorem embed_bracket_closed
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ∃ Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯,
      embedLinearMap I M Z = ⁅embedLinearMap I M X, embedLinearMap I M Y⁆ := by
  refine ⟨mlieBracketSection I M X Y, ?_⟩
  apply Derivation.ext; intro f
  rw [Derivation.commutator_apply]
  exact embedDeriv_mlieBracket I M X Y f

end Embedding

end
