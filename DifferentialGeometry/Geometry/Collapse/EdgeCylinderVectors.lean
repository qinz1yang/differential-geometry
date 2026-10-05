import DifferentialGeometry.Geometry.Collapse.EdgeModelFibreDisk
import DifferentialGeometry.Geometry.Collapse.EdgeScaledSmoothing

/-!
# LFR28 B4: the vector conditions on the model cylinder from covector estimates on `N`

Blueprint 207A, LFR28 (A:27223), proof step 4: "The first covector is within `10⁻³` of `dt` and the
second within `10⁻³` of `dH_N`, while `dH_N(∂_t) = 0` and `‖dH_N‖ > 1 - 10⁻⁸`. Evaluating on `∂_t` and
the unit model gradient direction of `H_N` gives a two-by-two determinant greater than `0.99`."

At a point `x` of LFR24's cylinder `U ⊆ ℝ × S`, with the product chart `Θ : ℝ × S → N`, a map
`j : N → X` and source functions `f, H`, write `w = (f ∘ j ∘ Θ, H ∘ j ∘ Θ)` and `u₀ = (t, Δ h)`.
`edgeCylinder_vectors_of_covector_bounds` (**B4**): if
* `V = dΘ_x(1, 0)` is `G`-unit and `G`-orthogonal to `dΘ_x(0, Y)` (the product metric, R5);
* `d(f ∘ j)` is within `10⁻³` of `G(V, ·)` at `Θ x` ((LFR28.3), F7-DOWN);
* `d(H ∘ j)` is within `c ≤ 10⁻³` of `dG_N` at `Θ x` ((LFR28.4), F7-LFR28B G3) where
  `dG_N(dΘ_x(a, Y)) = Δ dh(Y)` (the model height is `G_N = Δ h ∘ (Θ⁻¹)₂`);
* a model direction `Y` with `|dΘ_x(0, Y)|_G ≤ 1` and `Δ dh(Y) ≥ 1/2` (LFR24's gradient clause),
then `X₁ = (1, 0)`, `X₂ = (0, Y)` satisfy all eight clauses of the `hpair` hypothesis of
`edgeModelCylinder_disk_bundle` at `x`, and `X₁` the two clauses of `hrow`
(`edgeCylinder_row_of_covector_bound`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

open Bundle

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {S : Type*} [MetricSpace S] [ChartedSpace E2 S]
  {N : Type*} [TopologicalSpace N] [ChartedSpace E3 N]
  {X : Type*}

/-- The derivative of `x ↦ F (Θ x)` on the cylinder, read through `Θ`. -/
theorem mfderiv_edgeCylinder_comp {z₀ : S} {Δ : ℝ} {r : WithTop ℕ∞} (hr : r ≠ 0)
    (Θ : Diffeomorph (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) (ℝ × S) N r) {F : N → ℝ × ℝ}
    (x : edgeModelCylinder z₀ Δ) (hF : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ × ℝ) F (Θ x))
    (v : ℝ × E2) :
    mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ) (fun z : edgeModelCylinder z₀ Δ => F (Θ z)) x v =
      mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ × ℝ) F (Θ x)
        (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ (x : ℝ × S) v) := by
  have hΘ : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ (x : ℝ × S) :=
    Θ.mdifferentiable hr _
  have hd := (hF.hasMFDerivAt.comp (x : ℝ × S) hΘ.hasMFDerivAt).comp x
    (DifferentialGeometry.hasMFDerivAt_subtype_val (I := 𝓘(ℝ, ℝ).prod (𝓡 2)) _ x)
  have hmf : mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ)
      (fun z : edgeModelCylinder z₀ Δ => F (Θ z)) x =
      ((mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ × ℝ) F (Θ x)).comp
        (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ (x : ℝ × S))).comp
        (ContinuousLinearMap.id ℝ (ℝ × E2)) := hd.mfderiv
  rw [hmf]
  rfl

/-- The derivative of the model map `u₀ = (t, Δ h)` on the cylinder. -/
theorem mfderiv_edgeCylinder_model {z₀ : S} {h : S → ℝ} {Δ : ℝ}
    (x : edgeModelCylinder z₀ Δ) (hhx : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) h (x : ℝ × S).2)
    (v : ℝ × E2) :
    mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ)
      (fun y : edgeModelCylinder z₀ Δ => (((y : ℝ × S).1, Δ * h (y : ℝ × S).2) : ℝ × ℝ)) x v =
      (v.1, Δ * mvfderiv (𝓡 2) h (x : ℝ × S).2 v.2) := by
  have hs : HasMFDerivAt (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2)
      (fun y : edgeModelCylinder z₀ Δ => (y : ℝ × S).2) x
      ((ContinuousLinearMap.snd ℝ ℝ E2).comp (ContinuousLinearMap.id ℝ (ℝ × E2))) :=
    (hasMFDerivAt_snd (x : ℝ × S)).comp x (DifferentialGeometry.hasMFDerivAt_subtype_val _ x)
  have hf : HasMFDerivAt (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ)
      (fun y : edgeModelCylinder z₀ Δ => (y : ℝ × S).1) x
      ((ContinuousLinearMap.fst ℝ ℝ E2).comp (ContinuousLinearMap.id ℝ (ℝ × E2))) :=
    (hasMFDerivAt_fst (x : ℝ × S)).comp x (DifferentialGeometry.hasMFDerivAt_subtype_val _ x)
  have hg := (hhx.hasMFDerivAt.comp x hs).const_smul Δ
  have hv : HasMFDerivAt (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ)
      (fun y : edgeModelCylinder z₀ Δ => (((y : ℝ × S).1, Δ * h (y : ℝ × S).2) : ℝ × ℝ)) x
      (((ContinuousLinearMap.fst ℝ ℝ E2).comp (ContinuousLinearMap.id ℝ (ℝ × E2))).prod
        (Δ • (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) h (x : ℝ × S).2).comp
          ((ContinuousLinearMap.snd ℝ ℝ E2).comp (ContinuousLinearMap.id ℝ (ℝ × E2))))) :=
    ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩
  rw [hv.mfderiv]
  rfl

/-- The derivative of a pair of real functions. -/
theorem mfderiv_pair_apply {y : N} {g k : N → ℝ}
    (hg : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) g y) (hk : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) k y)
    (Z : TangentSpace 𝓘(ℝ, E3) y) :
    mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ × ℝ) (fun z => ((g z, k z) : ℝ × ℝ)) y Z =
      (mvfderiv 𝓘(ℝ, E3) g y Z, mvfderiv 𝓘(ℝ, E3) k y Z) := by
  have hd : HasMFDerivAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ × ℝ) (fun z => ((g z, k z) : ℝ × ℝ)) y
      ((mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) g y).prod (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) k y)) :=
    ⟨hg.hasMFDerivAt.1.prodMk hk.hasMFDerivAt.1, hg.hasMFDerivAt.2.prodMk hk.hasMFDerivAt.2⟩
  rw [hd.mfderiv]
  rfl

/-- **LFR28 B4 (row).** If `V = dΘ_x(1, 0)` is `G`-unit and `d(f ∘ j)` is within `10⁻³` of `G(V, ·)`
at `Θ x`, then `X = (1, 0)` satisfies the `hrow` clauses at `x`. -/
theorem edgeCylinder_row_of_covector_bound [IsManifold 𝓘(ℝ, E3) ∞ N] {z₀ : S} {h : S → ℝ} {Δ : ℝ}
    {r : WithTop ℕ∞}
    (hr : r ≠ 0) (Θ : Diffeomorph (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) (ℝ × S) N r) (j : N → X)
    {f H : X → ℝ} {n : ℕ∞ω}
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E3) n E3 (TangentSpace 𝓘(ℝ, E3) : N → Type _))
    (x : edgeModelCylinder z₀ Δ) (hhx : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) h (x : ℝ × S).2)
    (hfj : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun y => f (j y)) (Θ x))
    (hHj : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun y => H (j y)) (Θ x))
    (hVV : G.inner (Θ x) (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ (x : ℝ × S) ((1 : ℝ), (0 : E2)))
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ (x : ℝ × S) ((1 : ℝ), (0 : E2))) = 1)
    (h3 : ∀ Z : E3, |mvfderiv 𝓘(ℝ, E3) (fun y => f (j y)) (Θ x) Z -
      G.inner (Θ x) (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ (x : ℝ × S) ((1 : ℝ), (0 : E2))) Z| ≤
        1 / 1000 * Real.sqrt (G.inner (Θ x) Z Z)) :
    ∃ X₀ : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 2)) x,
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ)
        (fun y : edgeModelCylinder z₀ Δ => (((y : ℝ × S).1, Δ * h (y : ℝ × S).2) : ℝ × ℝ))
        x X₀).1 = 1 ∧
      |(mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ)
        (fun z : edgeModelCylinder z₀ Δ => ((f (j (Θ z)), H (j (Θ z))) : ℝ × ℝ)) x X₀).1 - 1|
        ≤ 1 / 1000 := by
  refine ⟨((1 : ℝ), (0 : E2)), ?_, ?_⟩
  · rw [mfderiv_edgeCylinder_model x hhx]
  · have hpair : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ × ℝ)
        (fun y => ((f (j y), H (j y)) : ℝ × ℝ)) (Θ x) := hfj.prodMk_space hHj
    rw [mfderiv_edgeCylinder_comp hr Θ (F := fun y => ((f (j y), H (j y)) : ℝ × ℝ)) x hpair,
      mfderiv_pair_apply hfj hHj]
    have h := h3 (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ (x : ℝ × S) ((1 : ℝ), (0 : E2)))
    rw [hVV, Real.sqrt_one, mul_one] at h
    exact h

/-- **LFR28 B4 (pair).** Under the hypotheses of `edgeCylinder_row_of_covector_bound`, the
orthogonality `G(V, dΘ_x(0, ·)) = 0`, the `(LFR28.4)` bound `|d(H ∘ j) - dG_N| ≤ c|·|` (`c ≤ 10⁻³`),
`dG_N ∘ dΘ_x = Δ dh ∘ snd`, and a model direction `Y` with `|dΘ_x(0, Y)| ≤ 1`, `Δ dh(Y) ≥ 1/2`, the
vectors `X₁ = (1, 0)`, `X₂ = (0, Y)` satisfy the eight `hpair` clauses at `x`. -/
theorem edgeCylinder_vectors_of_covector_bounds [IsManifold 𝓘(ℝ, E3) ∞ N] {z₀ : S} {h : S → ℝ}
    {Δ : ℝ} {r : WithTop ℕ∞}
    (hr : r ≠ 0) (Θ : Diffeomorph (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) (ℝ × S) N r) (j : N → X)
    {f H : X → ℝ} {GN : N → ℝ} {n : ℕ∞ω}
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E3) n E3 (TangentSpace 𝓘(ℝ, E3) : N → Type _))
    (x : edgeModelCylinder z₀ Δ) (hhx : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) h (x : ℝ × S).2)
    (hfj : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun y => f (j y)) (Θ x))
    (hHj : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun y => H (j y)) (Θ x))
    (hVV : G.inner (Θ x) (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ (x : ℝ × S) ((1 : ℝ), (0 : E2)))
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ (x : ℝ × S) ((1 : ℝ), (0 : E2))) = 1)
    (hVY : ∀ Y : E2, G.inner (Θ x)
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ (x : ℝ × S) ((1 : ℝ), (0 : E2)))
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ (x : ℝ × S) ((0 : ℝ), Y)) = 0)
    (h3 : ∀ Z : E3, |mvfderiv 𝓘(ℝ, E3) (fun y => f (j y)) (Θ x) Z -
      G.inner (Θ x) (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ (x : ℝ × S) ((1 : ℝ), (0 : E2))) Z| ≤
        1 / 1000 * Real.sqrt (G.inner (Θ x) Z Z))
    {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 1 / 1000)
    (h4 : ∀ Z : E3, |mvfderiv 𝓘(ℝ, E3) (fun y => H (j y)) (Θ x) Z - mvfderiv 𝓘(ℝ, E3) GN (Θ x) Z| ≤
      c * Real.sqrt (G.inner (Θ x) Z Z))
    (hGN : ∀ (a : ℝ) (Y : E2), mvfderiv 𝓘(ℝ, E3) GN (Θ x)
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ (x : ℝ × S) (a, Y)) =
        Δ * mvfderiv (𝓡 2) h (x : ℝ × S).2 Y)
    {Y : E2}
    (hY1 : G.inner (Θ x) (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ (x : ℝ × S) ((0 : ℝ), Y))
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ (x : ℝ × S) ((0 : ℝ), Y)) ≤ 1)
    (hY2 : 1 / 2 ≤ Δ * mvfderiv (𝓡 2) h (x : ℝ × S).2 Y) :
    ∃ X₁ X₂ : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 2)) x,
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ)
        (fun y : edgeModelCylinder z₀ Δ => (((y : ℝ × S).1, Δ * h (y : ℝ × S).2) : ℝ × ℝ))
        x X₁).1 = 1 ∧
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ)
        (fun y : edgeModelCylinder z₀ Δ => (((y : ℝ × S).1, Δ * h (y : ℝ × S).2) : ℝ × ℝ))
        x X₂).1 = 0 ∧
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ)
        (fun y : edgeModelCylinder z₀ Δ => (((y : ℝ × S).1, Δ * h (y : ℝ × S).2) : ℝ × ℝ))
        x X₁).2 = 0 ∧
      1 / 2 ≤ (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ)
        (fun y : edgeModelCylinder z₀ Δ => (((y : ℝ × S).1, Δ * h (y : ℝ × S).2) : ℝ × ℝ))
        x X₂).2 ∧
      |(mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ)
        (fun z : edgeModelCylinder z₀ Δ => ((f (j (Θ z)), H (j (Θ z))) : ℝ × ℝ)) x X₁).1 - 1|
          ≤ 1 / 1000 ∧
      |(mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ)
        (fun z : edgeModelCylinder z₀ Δ => ((f (j (Θ z)), H (j (Θ z))) : ℝ × ℝ)) x X₂).1|
          ≤ 1 / 1000 ∧
      |(mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ)
        (fun z : edgeModelCylinder z₀ Δ => ((f (j (Θ z)), H (j (Θ z))) : ℝ × ℝ)) x X₁).2|
          ≤ 1 / 1000 ∧
      |(mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ)
        (fun z : edgeModelCylinder z₀ Δ => ((f (j (Θ z)), H (j (Θ z))) : ℝ × ℝ)) x X₂).2 -
        (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ)
          (fun y : edgeModelCylinder z₀ Δ => (((y : ℝ × S).1, Δ * h (y : ℝ × S).2) : ℝ × ℝ))
          x X₂).2| ≤ 1 / 1000 := by
  have hpair : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ × ℝ)
      (fun y => ((f (j y), H (j y)) : ℝ × ℝ)) (Θ x) := hfj.prodMk_space hHj
  have hw : ∀ v : ℝ × E2, mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ)
      (fun z : edgeModelCylinder z₀ Δ => ((f (j (Θ z)), H (j (Θ z))) : ℝ × ℝ)) x v =
      (mvfderiv 𝓘(ℝ, E3) (fun y => f (j y)) (Θ x)
          (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ (x : ℝ × S) v),
        mvfderiv 𝓘(ℝ, E3) (fun y => H (j y)) (Θ x)
          (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ (x : ℝ × S) v)) := by
    intro v
    rw [mfderiv_edgeCylinder_comp hr Θ (F := fun y => ((f (j y), H (j y)) : ℝ × ℝ)) x hpair,
      mfderiv_pair_apply hfj hHj]
  have hsY : Real.sqrt (G.inner (Θ x)
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ (x : ℝ × S) ((0 : ℝ), Y))
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ (x : ℝ × S) ((0 : ℝ), Y))) ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_le_sqrt hY1
  have hdh0 : mvfderiv (𝓡 2) h (x : ℝ × S).2 (0 : E2) = 0 :=
    (mvfderiv (𝓡 2) h (x : ℝ × S).2).map_zero
  refine ⟨((1 : ℝ), (0 : E2)), ((0 : ℝ), Y), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mfderiv_edgeCylinder_model x hhx]
  · rw [mfderiv_edgeCylinder_model x hhx]
  · rw [mfderiv_edgeCylinder_model x hhx]
    dsimp only
    rw [hdh0, mul_zero]
  · rw [mfderiv_edgeCylinder_model x hhx]
    exact hY2
  · rw [hw]
    have h := h3 (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ (x : ℝ × S) ((1 : ℝ), (0 : E2)))
    rw [hVV, Real.sqrt_one, mul_one] at h
    exact h
  · rw [hw]
    have h := h3 (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ (x : ℝ × S) ((0 : ℝ), Y))
    rw [hVY Y, sub_zero] at h
    exact h.trans (by nlinarith [Real.sqrt_nonneg (G.inner (Θ x)
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ (x : ℝ × S) ((0 : ℝ), Y))
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ (x : ℝ × S) ((0 : ℝ), Y)))])
  · rw [hw]
    have h := h4 (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ (x : ℝ × S) ((1 : ℝ), (0 : E2)))
    rw [hGN, hdh0, mul_zero, sub_zero, hVV, Real.sqrt_one, mul_one] at h
    exact h.trans hc
  · rw [hw, mfderiv_edgeCylinder_model x hhx]
    dsimp only
    have h := h4 (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ (x : ℝ × S) ((0 : ℝ), Y))
    rw [hGN] at h
    exact h.trans (by nlinarith [Real.sqrt_nonneg (G.inner (Θ x)
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ (x : ℝ × S) ((0 : ℝ), Y))
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ (x : ℝ × S) ((0 : ℝ), Y)))])

end DifferentialGeometry.Geometry.Collapse
