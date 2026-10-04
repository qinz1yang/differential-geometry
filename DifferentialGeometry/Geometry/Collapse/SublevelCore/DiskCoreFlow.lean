import DifferentialGeometry.Analysis.Calculus.Derivative.Curve
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-!
# LC45 (partial): disk cores, exhaustion and the normal-flow coordinate

Blueprint LC45 (master207A:22169). Delivered here:

* `sublevel_subset_interior_sublevel`, `iUnion_interior_sublevel`,
  `exists_subset_interior_sublevel`, `isCompact_sublevel_of_isProperMap`: for a continuous
  proper radius function `u` the cores `D_T = {u ≤ T}` are compact, nested
  (`D_T ⊆ int D_{T'}` for `T < T'`) and exhaust (every compact set lies in `int D_T` for large `T`).
* `mfderiv_ne_zero_of_curve`: a function with nonzero derivative along one curve has nonzero
  differential (applied to `Q = |v|²` along the fibre scaling `s ↦ (1+s) v`, derivative `2Q > 0`:
  every positive level of `Q` is regular).
* `mvfderiv_eq_one_of_translating`, `mvfderiv_eq_one_of_ray_flow`: the flow clause. If the
  retained flow `φ` translates the radius along rays, `e(q, r v) = φ_{r-ℓ}(e(q, ℓ v))` for unit
  `v` and `r > ℓ`, then `du(V) = 1` on `{u > ℓ}` for its generator `V`; hence `V` is strictly
  outward transverse to every `∂D_T`, `T > ℓ`, with defining function `u - T`.

Not delivered (reported in the lane sheet): properness of the fibre norm of a general smooth
vector bundle over a compact base (finite trivializing cover with a uniform eigenvalue bound)
and the explicit diffeomorphism `D_T ≅ D(E)`; the tree has no generic disk-bundle compactness
lemma (PC's `NormalBundleCompactness` covers only radius neighbourhoods of the soul).
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

section Exhaustion

variable {N : Type*} [TopologicalSpace N] {u : N → ℝ}

theorem isCompact_sublevel_of_isProperMap (hu : IsProperMap u) (T : ℝ) (h0 : ∀ x, 0 ≤ u x) :
    IsCompact {x | u x ≤ T} := by
  have : {x | u x ≤ T} = u ⁻¹' Icc 0 T := by
    ext x
    exact ⟨fun h => ⟨h0 x, h⟩, fun h => h.2⟩
  rw [this]
  exact hu.isCompact_preimage isCompact_Icc

theorem sublevel_subset_interior_sublevel (hu : Continuous u) {T T' : ℝ} (hT : T < T') :
    {x | u x ≤ T} ⊆ interior {x | u x ≤ T'} := by
  intro x hx
  have hopen : IsOpen {y | u y < T'} := isOpen_lt hu continuous_const
  have hsub : {y | u y < T'} ⊆ {y | u y ≤ T'} := fun y (hy : u y < T') => (le_of_lt hy : u y ≤ T')
  exact interior_maximal hsub hopen (lt_of_le_of_lt (hx : u x ≤ T) hT)

theorem iUnion_interior_sublevel (hu : Continuous u) :
    ⋃ T : ℝ, interior {x | u x ≤ T} = univ := by
  refine eq_univ_of_forall fun x => mem_iUnion.mpr ⟨u x + 1, ?_⟩
  exact sublevel_subset_interior_sublevel hu (by linarith : u x < u x + 1)
    (show x ∈ {y | u y ≤ u x} from le_refl (u x))

theorem exists_subset_interior_sublevel (hu : Continuous u) {K : Set N} (hK : IsCompact K) :
    ∃ T₀ : ℝ, ∀ T, T₀ ≤ T → K ⊆ interior {x | u x ≤ T} := by
  obtain ⟨B, hB⟩ := (hK.image hu).isBounded.subset_closedBall 0
  refine ⟨B + 1, fun T hT x hx => sublevel_subset_interior_sublevel hu
    (by linarith : B < T) ?_⟩
  have h := hB ⟨x, hx, rfl⟩
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h
  exact (le_abs_self _).trans h

end Exhaustion

section Flow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N]

/-- A function whose derivative along one curve through `x` is nonzero has nonzero
differential at `x`. -/
theorem mfderiv_ne_zero_of_curve {Q : N → ℝ} {x : N} (hQ : MDifferentiableAt I 𝓘(ℝ, ℝ) Q x)
    {γ : ℝ → N} (hγ0 : γ 0 = x) (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ 0) {D : ℝ}
    (hD : HasDerivAt (fun s => Q (γ s)) D 0) (hD0 : D ≠ 0) : mfderiv I 𝓘(ℝ, ℝ) Q x ≠ 0 := by
  intro h
  subst hγ0
  have hcomp := DifferentialGeometry.Analysis.Calculus.hasDerivAt_comp_mfderiv_along I Q γ 0 hQ hγ
  rw [h] at hcomp
  exact hD0 (hD.unique hcomp)

/-- The derivative of `u` along the generator of a flow that translates `u` at unit speed is
one. -/
theorem mvfderiv_eq_one_of_translating {u : N → ℝ} {x : N}
    (hu : MDifferentiableAt I 𝓘(ℝ, ℝ) u x) {γ : ℝ → N} {V : TangentSpace I x}
    (hγ0 : γ 0 = x) (hγ : HasMFDerivAt 𝓘(ℝ, ℝ) I γ 0 ((1 : ℝ →L[ℝ] ℝ).smulRight V))
    (htr : ∀ᶠ t in 𝓝 (0 : ℝ), u (γ t) = u x + t) :
    mvfderiv (I := I) u x V = 1 := by
  subst hγ0
  have hcomp := DifferentialGeometry.Analysis.Calculus.hasDerivAt_comp_mfderiv_along I u γ 0 hu
    hγ.mdifferentiableAt
  have hlin : HasDerivAt (fun t => u (γ t)) 1 0 := by
    have h := (hasDerivAt_id (0 : ℝ)).const_add (u (γ 0))
    exact h.congr_of_eventuallyEq (by filter_upwards [htr] with t ht; rw [ht]; rfl)
  have heq := hcomp.unique hlin
  rw [hγ.mfderiv] at heq
  have hv : ((1 : ℝ →L[ℝ] ℝ).smulRight V)
      (DifferentialGeometry.Analysis.Calculus.realTangentOne 0) = V := one_smul ℝ V
  have hc := congrArg (mvfderiv (I := I) u (γ 0)) hv
  rw [← hc]
  exact heq

/-- LC45, flow clause. `e` maps a fibre model `B` (for instance the normal bundle) to `N`,
`nE` is the fibre norm, `sc r v` the fibre scaling, `u` the radius on `N` (`u ∘ e = nE`), and
the retained flow satisfies the ray identity `e(r v) = φ_{r-ℓ}(e(ℓ v))` for unit `v` and
`r > ℓ`. Then the generator `V` of `φ` has `du(V) = 1` on `{u > ℓ}`. -/
theorem mvfderiv_eq_one_of_ray_flow {B : Type*} {e : B → N} {nE : B → ℝ} {sc : ℝ → B → B}
    {u : N → ℝ} (hue : ∀ w, u (e w) = nE w)
    (hsc : ∀ v, nE v = 1 → ∀ r, 0 ≤ r → nE (sc r v) = r)
    (hpolar : ∀ w, ∃ v, nE v = 1 ∧ sc (nE w) v = w) {ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    {φ : ℝ → N → N} (hφadd : ∀ s t x, φ (s + t) x = φ t (φ s x))
    (hray : ∀ v, nE v = 1 → ∀ r, ℓ < r → e (sc r v) = φ (r - ℓ) (e (sc ℓ v)))
    (V : (x : N) → TangentSpace I x)
    (hV : ∀ x, HasMFDerivAt 𝓘(ℝ, ℝ) I (fun t => φ t x) 0 ((1 : ℝ →L[ℝ] ℝ).smulRight (V x)))
    (hφ0 : ∀ x, φ 0 x = x) {w : B} (hw : ℓ < nE w)
    (hu : MDifferentiableAt I 𝓘(ℝ, ℝ) u (e w)) :
    mvfderiv (I := I) u (e w) (V (e w)) = 1 := by
  obtain ⟨v, hv, hvw⟩ := hpolar w
  set r := nE w with hr
  apply mvfderiv_eq_one_of_translating hu (hφ0 _) (hV (e w))
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), ℓ < r + t := by
    have : Tendsto (fun t : ℝ => r + t) (𝓝 0) (𝓝 r) := by
      simpa using (tendsto_const_nhds (x := r)).add (tendsto_id (x := (𝓝 (0 : ℝ))))
    exact this.eventually (lt_mem_nhds hw)
  filter_upwards [hev] with t ht
  have h1 : φ t (e w) = e (sc (r + t) v) := by
    rw [← hvw, hray v hv r hw, ← hφadd, hray v hv (r + t) ht]
    congr 1
    ring
  rw [h1, hue, hue, hsc v hv (r + t) (by linarith), ← hvw, hsc v hv r (by linarith)]

end Flow

end DifferentialGeometry.Geometry.Collapse
