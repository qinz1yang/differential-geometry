import DifferentialGeometry.Geometry.Comparison.FiniteSoul.ClosedGeodesicNormal
import DifferentialGeometry.Geometry.Comparison.FiniteMetric.FirstVariation
import DifferentialGeometry.Topology.Manifold.InjectiveLocalDiffeomorph
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict
import DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem.Basic

/-!
# The normal tube of a closed geodesic of a surface (S-TUBE, disposition D3)

Package CM-S (finite soul), lane CMS-T. Design `docs/geometrization/chapter13/design-finite-soul-20261004.md`
§4.2 S-TUBE and errata E3; review `build-logs/inbox/review-finite-soul.md` §7.

Let `γ t = π φ_t(p)` be a simple closed unit geodesic of period `ℓ` of a complete `C^(r+1)` metric,
`r ≥ 2`, on a surface, `S = range γ`, and `ν` a continuous unit normal along `γ` with holonomy
`ν (t + ℓ) = σ • ν t`. The tube map `(s, h) ↦ exp_{γ(ℓ s)}(h ν(ℓ s))` descends to the normal line
bundle `NormalLineBundle σ = (ℝ × ℝ) / ((s + 1, h) ∼ (s, σ h))`.

* `isInvertible_mfderiv_transverseShift_rescaled`: its differential along the zero section is
  `(a, b) ↦ ℓ a γ' + b ν`, invertible.
* `inner_minimizingDirection_geodesicFlow_eq_zero`: at a nearest point `γ τ` of `S` to `y`, every
  minimizing direction from `γ τ` to `y` is orthogonal to `γ'(τ)` (first variation, both
  directions).
* `exists_transverseShift_eq_of_infDist`: every point `y` is `exp_{γ τ}(h ν τ)` with
  `|h| = d_S(y)`.
* `exists_closedGeodesic_normalLineBundle_tube` (**main**): for some `ε > 0` the induced map `F` on
  the quotient is injective on the open `ε`-tube, maps it onto `{d_S < ε}`, fixes the zero section,
  satisfies `d_S (F q) = |h|`, and for every finite order `1 ≤ k ≤ r` restricts to a `C^k`
  partial diffeomorphism from the `ε`-tube onto `{d_S < ε}`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- The rescaled transverse shift `(s, h) ↦ α(ℓ s, h)` is `C^r` on the plane (dimension two). -/
theorem contMDiff_transverseShift_rescaled
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 1 ≤ r) (hdim : Module.finrank ℝ E = 2) (hdom : g.geodesicFlowDomain = univ)
    (p : TangentBundle I M) (hunit : g.inner p.proj p.snd p.snd = 1) {ν : ℝ → E}
    (hν : Continuous (fun t => (⟨(g.geodesicFlow p t).proj, ν t⟩ : TangentBundle I M)))
    (hνunit : ∀ t, g.inner (g.geodesicFlow p t).proj (ν t) (ν t) = 1)
    (hνperp : ∀ t, g.inner (g.geodesicFlow p t).proj (ν t) (g.geodesicFlow p t).snd = 0)
    (ℓ : ℝ) :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) I r (fun w : ℝ × ℝ => transverseShift g p ν (ℓ * w.1, w.2)) := by
  intro w
  have hV := contMDiffAt_unitNormal_dim_two g hr hdim p (fun t => by rw [hdom]; exact mem_univ _)
    hunit isOpen_univ hν.continuousOn (fun t _ => hνunit t) (fun t _ => hνperp t)
    (mem_univ (ℓ * w.1))
  have hα := contMDiffAt_transverseShift g hr hdom p (z := (ℓ * w.1, w.2)) hV
  have hL : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) r (fun w : ℝ × ℝ => (ℓ * w.1, w.2)) w :=
    ((contDiff_const.mul contDiff_fst).prodMk contDiff_snd).contMDiff.contMDiffAt
  exact ContMDiffAt.comp (g := transverseShift g p ν) (f := fun w : ℝ × ℝ => (ℓ * w.1, w.2)) w hα hL

/-- **The differential of the tube map along the zero section is invertible**: it is
`(a, b) ↦ ℓ a γ'(ℓ τ) + b ν(ℓ τ)`, an isomorphism `ℝ × ℝ ≃ T_{γ(ℓ τ)} M`. -/
theorem isInvertible_mfderiv_transverseShift_rescaled
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 1 ≤ r) (hdim : Module.finrank ℝ E = 2) (hdom : g.geodesicFlowDomain = univ)
    (p : TangentBundle I M) (hunit : g.inner p.proj p.snd p.snd = 1) {ν : ℝ → E}
    (hν : Continuous (fun t => (⟨(g.geodesicFlow p t).proj, ν t⟩ : TangentBundle I M)))
    (hνunit : ∀ t, g.inner (g.geodesicFlow p t).proj (ν t) (ν t) = 1)
    (hνperp : ∀ t, g.inner (g.geodesicFlow p t).proj (ν t) (g.geodesicFlow p t).snd = 0)
    {ℓ : ℝ} (hℓ : ℓ ≠ 0) (τ : ℝ) :
    (mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun w : ℝ × ℝ => transverseShift g p ν (ℓ * w.1, w.2))
      (τ, 0)).IsInvertible := by
  have hmem : ∀ q : TangentBundle I M × ℝ, q ∈ g.geodesicFlowDomain := fun q => by
    rw [hdom]; exact mem_univ q
  set α := transverseShift g p ν with hαdef
  set L : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
    (ℓ • ContinuousLinearMap.fst ℝ ℝ ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ) with hL
  have hLapp : ∀ w : ℝ × ℝ, L w = (ℓ * w.1, w.2) := fun w => rfl
  set w₀ : ℝ × ℝ := (ℓ * τ, 0) with hw₀
  have hV := contMDiffAt_unitNormal_dim_two g hr hdim p (fun t => hmem _) hunit isOpen_univ
    hν.continuousOn (fun t _ => hνunit t) (fun t _ => hνperp t) (mem_univ (ℓ * τ))
  have hαc : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I r α w₀ :=
    contMDiffAt_transverseShift g hr hdom p (z := w₀) hV
  have hαd : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I α w₀ :=
    hαc.mdifferentiableAt (by exact_mod_cast (zero_lt_one.trans_le hr).ne')
  have hf : HasFDerivAt (fun w : ℝ × ℝ => (ℓ * w.1, w.2)) L (τ, 0) :=
    (hasFDerivAt_fst.const_mul ℓ).prodMk hasFDerivAt_snd
  set T : ℝ × ℝ →L[ℝ] E := mfderiv 𝓘(ℝ, ℝ × ℝ) I α w₀ with hT
  have hcomp : HasMFDerivAt 𝓘(ℝ, ℝ × ℝ) I (α ∘ fun w : ℝ × ℝ => (ℓ * w.1, w.2)) (τ, 0)
      (T.comp L) :=
    hαd.hasMFDerivAt.comp (τ, 0) hf.hasMFDerivAt
  have hfun : (fun w : ℝ × ℝ => transverseShift g p ν (ℓ * w.1, w.2)) =
      α ∘ fun w : ℝ × ℝ => (ℓ * w.1, w.2) := rfl
  rw [hfun, hcomp.mfderiv]
  set x : M := (g.geodesicFlow p (ℓ * τ)).proj with hx
  set U : E := (g.geodesicFlow p (ℓ * τ)).snd with hU
  set N : E := ν (ℓ * τ) with hN
  have hD10 : T ((1 : ℝ), (0 : ℝ)) = U := by
    refine (mfderiv_apply_eq_slice hαd).1.trans ?_
    have hslice : (fun s => α (s, w₀.2)) = fun s => (g.geodesicFlow p s).proj := by
      funext s
      simp only [hαdef, hw₀, transverseShift, g.geodesicFlow_zero hr]
    rw [hslice, (g.hasMFDerivAt_geodesicFlow_proj hr (hmem (p, w₀.1))).mfderiv]
    change (1 : ℝ) • (g.geodesicFlow p (ℓ * τ)).snd = U
    rw [one_smul]
  have hD01 : T ((0 : ℝ), (1 : ℝ)) = N := by
    refine (mfderiv_apply_eq_slice hαd).2.trans ?_
    refine (mfderiv_transverseShift_snd g hr hdom p ν w₀).trans ?_
    change (g.geodesicFlow (⟨(g.geodesicFlow p (ℓ * τ)).proj, ν (ℓ * τ)⟩ : TangentBundle I M)
      0).snd = N
    rw [g.geodesicFlow_zero hr]
  have hDapp : ∀ a b : ℝ, (T.comp L) (a, b) = (ℓ * a) • U + b • N := by
    intro a b
    have hLab : L (a, b) = (ℓ * a) • ((1 : ℝ), (0 : ℝ)) + b • ((0 : ℝ), (1 : ℝ)) := by
      rw [hLapp]; ext <;> simp
    rw [ContinuousLinearMap.comp_apply, hLab, map_add, map_smul, map_smul, hD10, hD01]
  set B : E →L[ℝ] E →L[ℝ] ℝ := g.inner x with hB
  have hUU : B U U = 1 := by
    change g.inner x U U = 1
    rw [hx, hU, g.inner_geodesicFlow_eq hr p _ (hmem _), hunit]
  have hNN : B N N = 1 := hνunit (ℓ * τ)
  have hNU : B N U = 0 := hνperp (ℓ * τ)
  have hUN : B U N = 0 := (g.symm x U N).trans hNU
  have hinj : Function.Injective (T.comp L) := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨a, b⟩ hab
    rw [hDapp] at hab
    have h1 := congrArg (fun v => B v U) hab
    have h2 := congrArg (fun v => B v N) hab
    simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul,
      map_zero, zero_apply, hUU, hNU, hUN, hNN] at h1 h2
    have hb : b = 0 := by linarith
    have ha : a = 0 := by
      have : ℓ * a = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hℓ
      · exact h
    rw [ha, hb]
    rfl
  have hfr : Module.finrank ℝ (ℝ × ℝ) = Module.finrank ℝ E := by
    rw [Module.finrank_prod, Module.finrank_self, hdim]
  have hsurj : Function.Surjective ((T.comp L : ℝ × ℝ →L[ℝ] E) : ℝ × ℝ →ₗ[ℝ] E) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).mp hinj
  exact ⟨(LinearEquiv.ofBijective ((T.comp L : ℝ × ℝ →L[ℝ] E) : ℝ × ℝ →ₗ[ℝ] E)
    ⟨hinj, hsurj⟩).toContinuousLinearEquiv, by ext v; rfl⟩

/-- The closed geodesic is the image of one period. -/
theorem range_geodesicFlow_eq_image_Ico
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 1 ≤ r) (hdom : g.geodesicFlowDomain = univ) {p : TangentBundle I M} {ℓ : ℝ}
    (hℓ : 0 < ℓ) (hper : g.geodesicFlow p ℓ = p) :
    range (fun t => (g.geodesicFlow p t).proj) = (fun t => (g.geodesicFlow p t).proj) '' Ico 0 ℓ := by
  refine Subset.antisymm ?_ (image_subset_range _ _)
  rintro _ ⟨t, rfl⟩
  refine ⟨ℓ * Int.fract (t / ℓ), ⟨by have := Int.fract_nonneg (t / ℓ); positivity,
    by have := Int.fract_lt_one (t / ℓ); nlinarith⟩, ?_⟩
  have e : t = ℓ * Int.fract (t / ℓ) + ((⌊t / ℓ⌋ : ℤ) : ℝ) * ℓ := by
    rw [Int.fract]; field_simp; ring
  change (g.geodesicFlow p (ℓ * Int.fract (t / ℓ))).proj = (g.geodesicFlow p t).proj
  conv_rhs => rw [e]
  rw [geodesicFlow_add_int_mul g hr hdom hper]

/-- The closed geodesic is compact. -/
theorem isCompact_range_geodesicFlow
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 1 ≤ r) (hdom : g.geodesicFlowDomain = univ) {p : TangentBundle I M} {ℓ : ℝ}
    (hℓ : 0 < ℓ) (hper : g.geodesicFlow p ℓ = p) :
    IsCompact (range fun t => (g.geodesicFlow p t).proj) := by
  have hc : Continuous fun t => (g.geodesicFlow p t).proj :=
    continuous_iff_continuousAt.mpr fun t =>
      (g.hasMFDerivAt_geodesicFlow_proj hr (by rw [hdom]; exact mem_univ _)).continuousAt
  have h : range (fun t => (g.geodesicFlow p t).proj) = (fun t => (g.geodesicFlow p t).proj) '' Icc 0 ℓ :=
    Subset.antisymm ((range_geodesicFlow_eq_image_Ico g hr hdom hℓ hper).le.trans
      (image_mono Ico_subset_Icc_self)) (image_subset_range _ _)
  rw [h]
  exact isCompact_Icc.image hc

section Complete

variable [CompleteSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M]

/-- **Orthogonality at a nearest point** (first variation in both time directions): if `γ τ` is
a point of the closed geodesic nearest to `y ≠ γ τ`, every minimizing direction from `γ τ` to `y`
is orthogonal to `γ'(τ)`. -/
theorem inner_minimizingDirection_geodesicFlow_eq_zero
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : TangentBundle I M) {y : M} {τ : ℝ}
    (hnear : ∀ t, dist (g.geodesicFlow p τ).proj y ≤ dist (g.geodesicFlow p t).proj y)
    (hy : (g.geodesicFlow p τ).proj ≠ y) {u : E}
    (hu : u ∈ g.finiteMinimizingDirectionsTo {y} (g.geodesicFlow p τ).proj) :
    g.inner (g.geodesicFlow p τ).proj u (g.geodesicFlow p τ).snd = 0 := by
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  have hdom := g.geodesicFlowDomain_eq_univ hr hnorm
  set x := (g.geodesicFlow p τ).proj with hx
  set X : E := (g.geodesicFlow p τ).snd with hX
  -- one direction: along any curve through `x` staying at distance `≥ d(x, y)` from `y`
  have key : ∀ (c : ℝ → M) (Y : E), c 0 = x →
      HasMFDerivAt 𝓘(ℝ, ℝ) I c 0 ((1 : ℝ →L[ℝ] ℝ).smulRight Y) →
      (∀ s, dist x y ≤ dist (c s) y) → g.inner x u Y ≤ 0 := by
    intro c Y hc0 hc hfar
    by_contra hpos
    rw [not_le] at hpos
    have hev := g.eventually_infDist_sub_le_finite_of_eq hr hnorm isClosed_singleton
      (singleton_nonempty y) hc0 hc (fun h => hy (mem_singleton_iff.mp h)) hu
      (c := -(g.inner x u Y) / 2) (by linarith)
    obtain ⟨s, hs, hspos⟩ := (hev.and self_mem_nhdsWithin).exists
    rw [infDist_singleton, infDist_singleton] at hs
    have hs' : (0 : ℝ) < s := hspos
    have := hfar s
    nlinarith
  have hγ : HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => (g.geodesicFlow p (τ + s)).proj) 0
      ((1 : ℝ →L[ℝ] ℝ).smulRight X) := by
    have htr : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun σ : ℝ => τ + σ) 0 (1 : ℝ →L[ℝ] ℝ) :=
      hasMFDerivAt_iff_hasFDerivAt.mpr ((hasFDerivAt_id (0 : ℝ)).const_add τ)
    have hγt : HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => (g.geodesicFlow p s).proj) (τ + 0)
        ((1 : ℝ →L[ℝ] ℝ).smulRight X) := by
      rw [add_zero]
      exact g.hasMFDerivAt_geodesicFlow_proj hr1 (by rw [hdom]; exact mem_univ _)
    exact (hγt.comp 0 htr).congr_mfderiv (ContinuousLinearMap.ext fun _ => rfl)
  have h1 := key (fun s => (g.geodesicFlow p (τ + s)).proj) X (by simp [hx])
    hγ (fun s => hnear (τ + s))
  have h2 := key (fun s => (g.geodesicFlow p (τ + -s)).proj) (-X) (by simp [hx])
    (Bundle.ContMDiffRiemannianMetric.hasMFDerivAt_comp_neg hγ) (fun s => hnear (τ + -s))
  have h2' : g.inner x u (-X) = -g.inner x u X := by
    set B : E →L[ℝ] E →L[ℝ] ℝ := g.inner x with hB
    change B u (-X) = -(B u X)
    rw [map_neg]
  rw [h2'] at h2
  linarith

/-- The transverse shift moves a point of the geodesic by at most `|h|`. -/
theorem dist_geodesicFlow_transverseShift_le
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 1 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : TangentBundle I M) {ν : ℝ → E}
    (hνunit : ∀ t, g.inner (g.geodesicFlow p t).proj (ν t) (ν t) = 1) (τ h : ℝ) :
    dist (g.geodesicFlow p τ).proj (transverseShift g p ν (τ, h)) ≤ |h| := by
  have hdom := g.geodesicFlowDomain_eq_univ_of_one_le hr hnorm
  set x := (g.geodesicFlow p τ).proj with hx
  have h0 := g.expMap_smul_eq_proj_geodesicFlow hr x (ν τ) 0 (by rw [hdom]; exact mem_univ _)
  rw [g.geodesicFlow_zero hr] at h0
  have hh := g.expMap_smul_eq_proj_geodesicFlow hr x (ν τ) h (by rw [hdom]; exact mem_univ _)
  have hd := g.dist_expMap_smul_le_of_completeSpace hr hnorm (x := x) (ν τ) 0 h
  rw [h0, hh, hνunit τ, Real.sqrt_one, one_mul, sub_zero] at hd
  exact hd

/-- **Every point is a transverse shift of its distance**: `y = exp_{γ τ}(h ν τ)` with
`|h| = d_S(y)`, `γ τ` a nearest point of the closed geodesic `S` (orthogonality at the foot,
dimension two). -/
theorem exists_transverseShift_eq_of_infDist [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hdim : Module.finrank ℝ E = 2) (p : TangentBundle I M) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hunit : g.inner p.proj p.snd p.snd = 1) (hper : g.geodesicFlow p ℓ = p) {ν : ℝ → E}
    (hνunit : ∀ t, g.inner (g.geodesicFlow p t).proj (ν t) (ν t) = 1)
    (hνperp : ∀ t, g.inner (g.geodesicFlow p t).proj (ν t) (g.geodesicFlow p t).snd = 0) (y : M) :
    ∃ τ h : ℝ, |h| = infDist y (range fun t => (g.geodesicFlow p t).proj) ∧
      transverseShift g p ν (τ, h) = y := by
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  have hdom := g.geodesicFlowDomain_eq_univ hr hnorm
  have hmem : ∀ q : TangentBundle I M × ℝ, q ∈ g.geodesicFlowDomain := fun q => by
    rw [hdom]; exact mem_univ q
  set S := range fun t => (g.geodesicFlow p t).proj with hS
  have hSc : IsCompact S := isCompact_range_geodesicFlow g hr1 hdom hℓ hper
  obtain ⟨s, ⟨τ, rfl⟩, hds⟩ := hSc.exists_infDist_eq_dist ⟨_, 0, rfl⟩ y
  set x := (g.geodesicFlow p τ).proj with hx
  have hshift0 : transverseShift g p ν (τ, 0) = x := by
    simp only [transverseShift, g.geodesicFlow_zero hr1, hx]
  by_cases hy : x = y
  · refine ⟨τ, 0, ?_, by rw [hshift0, hy]⟩
    rw [hds]
    change |(0 : ℝ)| = dist y x
    rw [hy, dist_self, abs_zero]
  obtain ⟨u, hu⟩ := (g.finiteMinimizingDirectionsTo_nonempty_isCompact hr hnorm isClosed_singleton
    (singleton_nonempty y) x).1
  have hnear : ∀ t, dist (g.geodesicFlow p τ).proj y ≤ dist (g.geodesicFlow p t).proj y := by
    intro t
    rw [dist_comm, ← hds, dist_comm]
    exact infDist_le_dist_of_mem ⟨t, rfl⟩
  have horth := inner_minimizingDirection_geodesicFlow_eq_zero g hr hnorm p hnear hy hu
  set B : E →L[ℝ] E →L[ℝ] ℝ := g.inner x with hB
  have hUU : B (g.geodesicFlow p τ).snd (g.geodesicFlow p τ).snd = 1 := by
    change g.inner x _ _ = 1
    rw [hx, g.inner_geodesicFlow_eq hr1 p _ (hmem _), hunit]
  have hrep : u = B u (ν τ) • ν τ :=
    eq_smul_of_orthonormal_dim_two hdim (fun a b => g.symm x a b) hUU (hνunit τ) (hνperp τ) horth
  set c := B u (ν τ) with hc
  have hcc : c * c = 1 := by
    have h := hu.1
    change B u u = 1 at h
    have hN : B (ν τ) (ν τ) = 1 := hνunit τ
    rw [hrep] at h
    simpa only [map_smul, smul_apply, smul_eq_mul, hN, mul_one] using h
  have habs : |c| = 1 := by
    rcases mul_self_eq_one_iff.mp hcc with h | h <;> rw [h] <;> norm_num
  have hexp : g.expMap (⟨x, infDist x {y} • u⟩ : TangentBundle I M) = y := hu.2
  have hvec : (infDist x {y} • u : E) = (dist x y * c) • ν τ := by
    rw [infDist_singleton, hrep]
    change (dist x y • (c • ν τ) : E) = _
    rw [smul_smul]
  have hpt : (⟨x, infDist x {y} • u⟩ : TangentBundle I M) = ⟨x, (dist x y * c) • ν τ⟩ :=
    congrArg (fun v : E => (⟨x, v⟩ : TangentBundle I M)) hvec
  rw [hpt] at hexp
  refine ⟨τ, dist x y * c, ?_, ?_⟩
  · rw [abs_mul, habs, mul_one, abs_of_nonneg dist_nonneg, hds, dist_comm]
  · exact (g.expMap_smul_eq_proj_geodesicFlow hr1 x (ν τ) _ (hmem _)).symm.trans hexp

/-- **S-TUBE (disposition D3): the tube around a closed geodesic of a surface.** Let `γ` be a
simple closed unit geodesic of period `ℓ` and `ν` a continuous unit normal with holonomy
`ν (t + ℓ) = σ • ν t`. The tube map descends to `F : NormalLineBundle σ → M`,
`F [s, h] = exp_{γ(ℓ s)}(h ν(ℓ s))`, and for some `ε > 0`: `F` fixes the zero section, is
calibrated (`d_S (F q) = |h|`), is injective on the open `ε`-tube and maps it onto `{d_S < ε}`; for
every finite order `1 ≤ k ≤ r` it is a `C^k` partial diffeomorphism from the `ε`-tube onto
`{d_S < ε}` (so of order `r = m − 1` for finite `r`). -/
theorem exists_closedGeodesic_normalLineBundle_tube
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hdim : Module.finrank ℝ E = 2) (p : TangentBundle I M) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hunit : g.inner p.proj p.snd p.snd = 1) (hper : g.geodesicFlow p ℓ = p)
    (hinj : InjOn (fun t => (g.geodesicFlow p t).proj) (Ico 0 ℓ)) {ν : ℝ → E}
    (hν : Continuous (fun t => (⟨(g.geodesicFlow p t).proj, ν t⟩ : TangentBundle I M)))
    (hνunit : ∀ t, g.inner (g.geodesicFlow p t).proj (ν t) (ν t) = 1)
    (hνperp : ∀ t, g.inner (g.geodesicFlow p t).proj (ν t) (g.geodesicFlow p t).snd = 0)
    {σ : ℤˣ} (hσ : ∀ t, ν (t + ℓ) = ((σ : ℤ) : ℝ) • ν t) :
    ∃ ε > 0, ∃ F : NormalLineBundle σ → M,
      (∀ t h, F (NormalLineBundle.mk σ t h) =
        g.expMap (⟨(g.geodesicFlow p (ℓ * t)).proj, h • ν (ℓ * t)⟩ : TangentBundle I M)) ∧
      (∀ t, F (NormalLineBundle.mk σ t 0) = (g.geodesicFlow p (ℓ * t)).proj) ∧
      (∀ q, NormalLineBundle.fiberAbs σ q < ε →
        infDist (F q) (range fun t => (g.geodesicFlow p t).proj) = NormalLineBundle.fiberAbs σ q) ∧
      F '' {q | NormalLineBundle.fiberAbs σ q < ε} =
        {y | infDist y (range fun t => (g.geodesicFlow p t).proj) < ε} ∧
      InjOn F {q | NormalLineBundle.fiberAbs σ q < ε} ∧
      ∀ k : ℕ, 1 ≤ k → (k : ℕ∞) ≤ r →
        ∃ Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) I (NormalLineBundle σ) M k,
          Φ.source = {q | NormalLineBundle.fiberAbs σ q < ε} ∧
          Φ.target = {y | infDist y (range fun t => (g.geodesicFlow p t).proj) < ε} ∧
          (Φ : NormalLineBundle σ → M) = F := by
  have : NeZero (Module.finrank ℝ E) := ⟨by rw [hdim]; norm_num⟩
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  have hdom := g.geodesicFlowDomain_eq_univ hr hnorm
  have hmem : ∀ q : TangentBundle I M × ℝ, q ∈ g.geodesicFlowDomain := fun q => by
    rw [hdom]; exact mem_univ q
  set S := range fun t => (g.geodesicFlow p t).proj with hS
  set α : ℝ × ℝ → M := fun w => transverseShift g p ν (ℓ * w.1, w.2) with hα
  set F : NormalLineBundle σ → M := Quotient.lift (closedGeodesicTubeMap g p ℓ ν σ) (by
    intro a b hab
    obtain ⟨k, rfl⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hab)
    exact closedGeodesicTubeMap_smul g hr1 hdom hper hσ k b) with hFdef
  have hFmk : ∀ t h, F (NormalLineBundle.mk σ t h) = transverseShift g p ν (ℓ * t, h) :=
    fun _ _ => rfl
  have hαs := contMDiff_transverseShift_rescaled g hr1 hdim hdom p hunit hν hνunit hνperp ℓ
  have hFc : Continuous F :=
    Continuous.quotient_lift (f := closedGeodesicTubeMap g p ℓ ν σ) hαs.continuous _
  -- local diffeomorphism of order one along the zero section (inverse function theorem)
  have : IsManifold I (1 : WithTop ℕ∞) M := IsManifold.of_le (n := ∞) (by exact_mod_cast le_top)
  have hzero : ∀ τ : ℝ, IsLocalDiffeomorphAt 𝓘(ℝ, ℝ × ℝ) I 1 α (τ, 0) := fun τ =>
    DifferentialGeometry.Coordinates.contMDiffAt_isLocalDiffeomorphAt_of_mfderiv le_rfl
      (by exact_mod_cast (WithTop.one_ne_top : (1 : ℕ∞) ≠ ⊤))
      ((hαs (τ, 0)).of_le (by exact_mod_cast hr1))
      (isInvertible_mfderiv_transverseShift_rescaled g hr1 hdim hdom p hunit hν hνunit hνperp
        hℓ.ne' τ)
  set G : Set (NormalCover σ) := {z | IsLocalDiffeomorphAt 𝓘(ℝ, ℝ × ℝ) I 1 α z} with hG
  have hGo : IsOpen G := by
    rw [isOpen_iff_mem_nhds]
    rintro z ⟨Φ, hzΦ, hEq⟩
    exact Filter.mem_of_superset (Φ.open_source.mem_nhds hzΦ) fun z' hz' => ⟨Φ, hz', hEq⟩
  have hGk : ∀ k : ℕ, 1 ≤ k → (k : ℕ∞) ≤ r → ∀ z : ℝ × ℝ,
      IsLocalDiffeomorphAt 𝓘(ℝ, ℝ × ℝ) I 1 α z → IsLocalDiffeomorphAt 𝓘(ℝ, ℝ × ℝ) I k α z := by
    intro k hk1 hkr z hz
    have : IsManifold I (k : WithTop ℕ∞) M := IsManifold.of_le (n := ∞) (by exact_mod_cast le_top)
    exact DifferentialGeometry.Coordinates.contMDiffAt_isLocalDiffeomorphAt_of_mfderiv
      (by exact_mod_cast hk1) (by exact_mod_cast ENat.natCast_ne_top k)
      ((hαs z).of_le (by exact_mod_cast hkr)) (hz.isInvertible_mfderiv one_ne_zero)
  -- the good set in the quotient
  set Gq : Set (NormalLineBundle σ) := NormalLineBundle.proj σ '' G with hGq
  have hGqo : IsOpen Gq := NormalLineBundle.isOpenMap_proj σ G hGo
  have hZG : (range fun t : ℝ => NormalLineBundle.mk σ t 0) ⊆ Gq := by
    rintro _ ⟨t, rfl⟩
    exact ⟨NormalCover.mk σ t 0, hzero t, rfl⟩
  have hFk : ∀ k : ℕ, 1 ≤ k → (k : ℕ∞) ≤ r → ∀ q ∈ Gq,
      IsLocalDiffeomorphAt 𝓘(ℝ, ℝ × ℝ) I k F q := by
    rintro k hk1 hkr _ ⟨z, hz, rfl⟩
    have h1 : IsLocalDiffeomorphAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) k (NormalLineBundle.proj σ) z :=
      NormalLineBundle.isLocalDiffeomorph_proj σ k z
    have h2 : IsLocalDiffeomorphAt 𝓘(ℝ, ℝ × ℝ) I k (F ∘ NormalLineBundle.proj σ) z :=
      hGk k hk1 hkr z hz
    exact DifferentialGeometry.isLocalDiffeomorphAt_of_comp h2 h1
  -- injectivity on the zero section
  have hγper : ∀ t : ℝ, (g.geodesicFlow p (ℓ * t)).proj =
      (g.geodesicFlow p (ℓ * Int.fract t)).proj := by
    intro t
    have e : ℓ * t = ℓ * Int.fract t + ((⌊t⌋ : ℤ) : ℝ) * ℓ := by rw [Int.fract]; ring
    rw [e, geodesicFlow_add_int_mul g hr1 hdom hper]
  have hmkfract : ∀ t : ℝ, NormalLineBundle.mk σ t 0 = NormalLineBundle.mk σ (Int.fract t) 0 := by
    intro t
    rw [NormalLineBundle.mk_eq_mk_iff]
    exact ⟨-⌊t⌋, by rw [Int.fract]; push_cast; ring, by rw [mul_zero]⟩
  have hF0 : ∀ t, F (NormalLineBundle.mk σ t 0) = (g.geodesicFlow p (ℓ * t)).proj := by
    intro t
    rw [hFmk]
    simp only [transverseShift, g.geodesicFlow_zero hr1]
  have hfr : ∀ t : ℝ, ℓ * Int.fract t ∈ Ico 0 ℓ := fun t =>
    ⟨mul_nonneg hℓ.le (Int.fract_nonneg t), by have := Int.fract_lt_one t; nlinarith⟩
  have hinjZ : InjOn F (range fun t : ℝ => NormalLineBundle.mk σ t 0) := by
    rintro _ ⟨t, rfl⟩ _ ⟨t', rfl⟩ heq
    simp only at heq ⊢
    rw [hF0, hF0, hγper t, hγper t'] at heq
    have h := hinj (hfr t) (hfr t') heq
    rw [hmkfract t, hmkfract t', mul_left_cancel₀ hℓ.ne' h]
  obtain ⟨T, hT, hinjT⟩ := hinjZ.exists_mem_nhdsSet (NormalLineBundle.isCompact_zeroSection σ)
    (fun q _ => hFc.continuousAt) (fun q hq => by
      obtain ⟨Φ, hqΦ, hEq⟩ := hFk 1 le_rfl (by exact_mod_cast hr1) q (hZG hq)
      exact ⟨Φ.source, Φ.open_source.mem_nhds hqΦ, fun a ha b hb hab =>
        Φ.toPartialEquiv.injOn ha hb ((hEq ha).symm.trans (hab.trans (hEq hb)))⟩)
  obtain ⟨ε, hε, hεsub⟩ :=
    NormalLineBundle.exists_tube_subset σ (Filter.inter_mem hT (hGqo.mem_nhdsSet.mpr hZG))
  set Tε : Set (NormalLineBundle σ) := {q | NormalLineBundle.fiberAbs σ q < ε} with hTε
  have hTinj : InjOn F Tε := hinjT.mono fun q hq => (hεsub hq).1
  have hTG : Tε ⊆ Gq := fun q hq => (hεsub hq).2
  -- calibration and image
  have hbound : ∀ t h, infDist (F (NormalLineBundle.mk σ t h)) S ≤ |h| := by
    intro t h
    rw [hFmk]
    refine (infDist_le_dist_of_mem
      (mem_range_self (f := fun t => (g.geodesicFlow p t).proj) (ℓ * t))).trans ?_
    rw [dist_comm]
    exact dist_geodesicFlow_transverseShift_le g hr1 hnorm p hνunit (ℓ * t) h
  have hrepr : ∀ y, infDist y S < ε →
      ∃ q ∈ Tε, F q = y ∧ NormalLineBundle.fiberAbs σ q = infDist y S := by
    intro y hy
    obtain ⟨τ, h, hh, hτ⟩ :=
      exists_transverseShift_eq_of_infDist g hr hnorm hdim p hℓ hunit hper hνunit hνperp y
    refine ⟨NormalLineBundle.mk σ (τ / ℓ) h, ?_, ?_, ?_⟩
    · change NormalLineBundle.fiberAbs σ (NormalLineBundle.mk σ (τ / ℓ) h) < ε
      rw [NormalLineBundle.fiberAbs_mk, hh]
      exact hy
    · rw [hFmk, mul_div_cancel₀ τ hℓ.ne']
      exact hτ
    · rw [NormalLineBundle.fiberAbs_mk, hh]
  have hcal : ∀ q ∈ Tε, infDist (F q) S = NormalLineBundle.fiberAbs σ q := by
    intro q hq
    obtain ⟨t, -, h, rfl⟩ := NormalLineBundle.exists_mk_eq σ q
    have hq' : |h| < ε := by
      change NormalLineBundle.fiberAbs σ _ < ε at hq
      rwa [NormalLineBundle.fiberAbs_mk] at hq
    obtain ⟨q', hq'T, hFq', hfq'⟩ := hrepr _ ((hbound t h).trans_lt hq')
    have hqq := hTinj hq'T hq hFq'
    rw [← hqq, hFq', hfq']
  have himage : F '' Tε = {y | infDist y S < ε} := by
    ext y
    constructor
    · rintro ⟨q, hq, rfl⟩
      change infDist (F q) S < ε
      rw [hcal q hq]
      exact hq
    · intro hy
      obtain ⟨q, hq, hFq, -⟩ := hrepr y hy
      exact ⟨q, hq, hFq⟩
  have : Nonempty (NormalLineBundle σ) := ⟨NormalLineBundle.mk σ 0 0⟩
  refine ⟨ε, hε, F, fun t h => ?_, hF0, fun q hq => hcal q hq, himage, hTinj,
    fun k hk1 hkr => ?_⟩
  · rw [hFmk]
    exact (g.expMap_smul_eq_proj_geodesicFlow hr1 _ (ν (ℓ * t)) h (hmem _)).symm
  · obtain ⟨Φ, hs, ht, hΦ⟩ :=
      DifferentialGeometry.Topology.Manifold.exists_partialDiffeomorph_of_injOn
        (I := 𝓘(ℝ, ℝ × ℝ)) (J := I) (n := (k : WithTop ℕ∞)) (NormalLineBundle.isOpen_tube σ ε)
        (fun q => hFk k hk1 hkr q (hTG q.2)) hTinj
    exact ⟨Φ, hs, ht.trans himage, hΦ⟩

end Complete

end DifferentialGeometry.Geometry.FiniteSoul
