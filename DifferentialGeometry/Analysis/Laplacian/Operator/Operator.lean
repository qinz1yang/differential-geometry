import DifferentialGeometry.Analysis.Laplacian.Operator.SmoothBridge
import DifferentialGeometry.Analysis.Laplacian.Operator.SmoothDenseLp

/-!
# The variational Laplacian operator and its domain

For a closed Riemannian manifold `(M, g)`, this file packages the variational
Laplacian as a linear map from its domain to `Lp ℝ 2 μ_g`.

## Construction

Recall the resolvent
`resolvent g : Lp ℝ 2 μ_g →L[ℝ] H1Compl g`
constructed via Lax–Milgram: for every `f ∈ Lp ℝ 2 μ_g` there is a unique
`u = resolvent g f ∈ H1Compl g` satisfying
`⟨u, v⟩_{H¹} = ⟨H1ComplToLp v, f⟩_{L²}` for every test `v ∈ H1Compl g`.

The variational Laplacian's domain is
`laplacianDomain g := LinearMap.range (resolvent g).toLinearMap ⊆ H1Compl g`,
i.e. the image of the resolvent. The Laplacian itself acts as
`Δ_g u := H1ComplToLp u - f` whenever `u = resolvent g f`. Equivalently, `f`
is `(1 - Δ_g) u`, so `Δ_g u = u - (1 - Δ_g) u`.

For this construction to be well-defined, the preimage `f` must be unique, i.e.
`resolvent g` must be injective. This follows from the density of smooth
functions in `Lp ℝ 2 μ_g` (`denseRange_smoothToLp`, Stone–Weierstrass +
continuous-Lp density).

## Main definitions

* `laplacianDomain g : Submodule ℝ (H1Compl g)` — the image of the resolvent.
* `laplacianOp g : laplacianDomain g →ₗ[ℝ] Lp ℝ 2 μ_g` — the variational
  Laplacian on its domain.

## Main results

* `resolvent_injective`: the resolvent is injective.
* `laplacianDomain_mem_iff`: characterisation of the Laplacian domain.
* `laplacianOp_resolvent`: the key identity `Δ_g (resolvent f) = H1ComplToLp (resolvent f) - f`.
* `laplacianOp_smoothToH1Compl`: the smooth bridge — for a smooth scalar `u`,
  `u` lies in the Laplacian domain and `Δ_g u` agrees with the classical
  Laplacian's `Lp` class.

## Sign convention

We follow the geometer convention `Δ_g = div_g ∘ grad_g`, so the Laplacian
is non-positive on a closed manifold. The resolvent is `(1 - Δ_g)⁻¹`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

/-- The resolvent of `(1 - Δ_g)` is an injective continuous linear map. -/
theorem resolvent_injective (g : SmoothRiemannianMetric I M) :
    Function.Injective (resolvent (I := I) (M := M) g) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  have h_orth : ∀ v : H1Compl g,
      ⟪H1ComplToLp (I := I) (M := M) g v, f⟫_ℝ = 0 := by
    intro v
    have h := resolvent_inner_eq_lpFunctional (I := I) (M := M) g f v
    rw [hf] at h
    rw [inner_zero_left] at h
    linarith
  have h_dense : DenseRange (H1ComplToLp (I := I) (M := M) g) :=
    denseRange_H1ComplToLp (I := I) (M := M) g
  have h_inner_zero : ∀ w : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g),
      (innerSL ℝ f) w = 0 := by
    intro w
    have h_eq_on_range :
        (fun y : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) =>
            (innerSL ℝ f) y) ∘ (H1ComplToLp (I := I) (M := M) g) =
        (fun _ : H1Compl g => (0 : ℝ)) := by
      funext v
      change ⟪f, H1ComplToLp (I := I) (M := M) g v⟫_ℝ = 0
      rw [real_inner_comm]
      exact h_orth v
    have h_func_eq :
        (fun y : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) =>
            (innerSL ℝ f) y) =
        (fun _ : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) => (0 : ℝ)) :=
      h_dense.equalizer (innerSL ℝ f).continuous continuous_const h_eq_on_range
    have := congrFun h_func_eq w
    exact this
  have h_self : ⟪f, f⟫_ℝ = 0 := by
    have := h_inner_zero f
    rwa [innerSL_apply_apply] at this
  rw [real_inner_self_eq_norm_sq] at h_self
  have h_norm_zero : ‖f‖ = 0 := by
    have h_pow_zero : ‖f‖ ^ 2 = 0 := h_self
    exact pow_eq_zero_iff (two_ne_zero) |>.mp h_pow_zero
  exact norm_eq_zero.mp h_norm_zero

/-- The domain of the variational Laplacian: the image of the resolvent
`(1 - Δ_g)⁻¹` from `Lp ℝ 2 μ_g` to `H1Compl g`. -/
def laplacianDomain (g : SmoothRiemannianMetric I M) :
    Submodule ℝ (H1Compl g) :=
  LinearMap.range (resolvent (I := I) (M := M) g).toLinearMap

/-- `u ∈ laplacianDomain g` iff `u` is the image of some `f ∈ Lp ℝ 2 μ_g`
under the resolvent. -/
lemma laplacianDomain_mem_iff (g : SmoothRiemannianMetric I M) {u : H1Compl g} :
    u ∈ laplacianDomain (I := I) (M := M) g ↔
      ∃ f : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g),
        u = resolvent (I := I) (M := M) g f := by
  unfold laplacianDomain
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨f, hf⟩; exact ⟨f, hf.symm⟩
  · rintro ⟨f, hf⟩; exact ⟨f, hf.symm⟩

/-- The unique preimage of `u ∈ laplacianDomain g` under the resolvent.
Well-defined because the resolvent is injective. -/
def laplacianDomain.preimage (g : SmoothRiemannianMetric I M)
    (u : laplacianDomain (I := I) (M := M) g) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  Classical.choose ((laplacianDomain_mem_iff (I := I) (M := M) g).mp u.2)

/-- Defining property of `laplacianDomain.preimage`. -/
@[simp] lemma resolvent_laplacianDomain_preimage_eq
    (g : SmoothRiemannianMetric I M)
    (u : laplacianDomain (I := I) (M := M) g) :
    resolvent (I := I) (M := M) g
        (laplacianDomain.preimage (I := I) (M := M) g u) =
      (u : H1Compl g) :=
  (Classical.choose_spec ((laplacianDomain_mem_iff (I := I) (M := M) g).mp u.2)).symm

/-- `laplacianDomain.preimage` of zero is zero. -/
lemma laplacianDomain_preimage_zero (g : SmoothRiemannianMetric I M) :
    laplacianDomain.preimage (I := I) (M := M) g
        (0 : laplacianDomain (I := I) (M := M) g) = 0 := by
  apply resolvent_injective (I := I) (M := M) g
  rw [resolvent_laplacianDomain_preimage_eq]
  rw [(resolvent (I := I) (M := M) g).map_zero]
  rfl

/-- `laplacianDomain.preimage` is additive. -/
lemma laplacianDomain_preimage_add (g : SmoothRiemannianMetric I M)
    (u v : laplacianDomain (I := I) (M := M) g) :
    laplacianDomain.preimage (I := I) (M := M) g (u + v) =
      laplacianDomain.preimage (I := I) (M := M) g u +
      laplacianDomain.preimage (I := I) (M := M) g v := by
  apply resolvent_injective (I := I) (M := M) g
  rw [resolvent_laplacianDomain_preimage_eq]
  rw [(resolvent (I := I) (M := M) g).map_add]
  rw [resolvent_laplacianDomain_preimage_eq, resolvent_laplacianDomain_preimage_eq]
  rfl

/-- `laplacianDomain.preimage` is homogeneous. -/
lemma laplacianDomain_preimage_smul (g : SmoothRiemannianMetric I M)
    (c : ℝ) (u : laplacianDomain (I := I) (M := M) g) :
    laplacianDomain.preimage (I := I) (M := M) g (c • u) =
      c • laplacianDomain.preimage (I := I) (M := M) g u := by
  apply resolvent_injective (I := I) (M := M) g
  rw [resolvent_laplacianDomain_preimage_eq]
  rw [(resolvent (I := I) (M := M) g).map_smul]
  rw [resolvent_laplacianDomain_preimage_eq]
  rfl

/-- `laplacianDomain.preimage` as a linear map. -/
def laplacianDomain.preimageLin (g : SmoothRiemannianMetric I M) :
    laplacianDomain (I := I) (M := M) g →ₗ[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) where
  toFun := laplacianDomain.preimage (I := I) (M := M) g
  map_add' := laplacianDomain_preimage_add (I := I) (M := M) g
  map_smul' c u := laplacianDomain_preimage_smul (I := I) (M := M) g c u

/-- The variational Laplacian as a linear map from its domain to `Lp ℝ 2 μ_g`.

For `u ∈ laplacianDomain g`, with `u = resolvent g f`, the Laplacian acts as
`Δ_g u := H1ComplToLp u - f`, equivalently `(1 - Δ_g) u = f`. -/
def laplacianOp (g : SmoothRiemannianMetric I M) :
    laplacianDomain (I := I) (M := M) g →ₗ[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  ((H1ComplToLp (I := I) (M := M) g).toLinearMap.comp
    (laplacianDomain (I := I) (M := M) g).subtype) -
  laplacianDomain.preimageLin (I := I) (M := M) g

/-- For `u ∈ laplacianDomain g`, `laplacianOp u = H1ComplToLp u - preimage u`. -/
@[simp] lemma laplacianOp_apply (g : SmoothRiemannianMetric I M)
    (u : laplacianDomain (I := I) (M := M) g) :
    laplacianOp (I := I) (M := M) g u =
      H1ComplToLp (I := I) (M := M) g (u : H1Compl g) -
        laplacianDomain.preimage (I := I) (M := M) g u := by
  unfold laplacianOp
  rw [LinearMap.sub_apply]
  rfl

/-- The key identity: `Δ_g (resolvent g f) = H1ComplToLp (resolvent g f) - f`. -/
theorem laplacianOp_resolvent (g : SmoothRiemannianMetric I M)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    laplacianOp (I := I) (M := M) g
        ⟨resolvent (I := I) (M := M) g f,
          (laplacianDomain_mem_iff (I := I) (M := M) g).mpr ⟨f, rfl⟩⟩ =
      H1ComplToLp (I := I) (M := M) g (resolvent (I := I) (M := M) g f) - f := by
  rw [laplacianOp_apply]
  have h_preimage_eq :
      laplacianDomain.preimage (I := I) (M := M) g
          ⟨resolvent (I := I) (M := M) g f,
            (laplacianDomain_mem_iff (I := I) (M := M) g).mpr ⟨f, rfl⟩⟩ = f := by
    apply resolvent_injective (I := I) (M := M) g
    rw [resolvent_laplacianDomain_preimage_eq]
  rw [h_preimage_eq]

/-- For a smooth scalar `u`, the H¹ lift `smoothToH1Compl u` lies in the
Laplacian domain. -/
lemma smoothToH1Compl_mem_laplacianDomain
    {g : SmoothRiemannianMetric I M} (u : SmoothScalar g) :
    smoothToH1Compl (I := I) (M := M) g u ∈
      laplacianDomain (I := I) (M := M) g := by
  rw [laplacianDomain_mem_iff]
  refine ⟨smoothToLp (I := I) (M := M) g u.oneSubLapClassical, ?_⟩
  exact smoothToH1Compl_eq_resolvent_oneSubLap (I := I) (M := M) u

/-- The variational Laplacian on a smooth scalar agrees with the L² class of
the classical Laplacian. -/
theorem laplacianOp_smoothToH1Compl
    {g : SmoothRiemannianMetric I M} (u : SmoothScalar g) :
    laplacianOp (I := I) (M := M) g
        ⟨smoothToH1Compl (I := I) (M := M) g u,
          smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) u⟩ =
      smoothToLp (I := I) (M := M) g u -
        smoothToLp (I := I) (M := M) g u.oneSubLapClassical := by
  rw [show (⟨smoothToH1Compl (I := I) (M := M) g u,
        smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) u⟩ :
        laplacianDomain (I := I) (M := M) g) =
      ⟨resolvent (I := I) (M := M) g
        (smoothToLp (I := I) (M := M) g u.oneSubLapClassical),
        (laplacianDomain_mem_iff (I := I) (M := M) g).mpr
          ⟨smoothToLp (I := I) (M := M) g u.oneSubLapClassical, rfl⟩⟩ from ?_]
  · rw [laplacianOp_resolvent]
    have h_eq : resolvent (I := I) (M := M) g
          (smoothToLp (I := I) (M := M) g u.oneSubLapClassical) =
        smoothToH1Compl (I := I) (M := M) g u :=
      (smoothToH1Compl_eq_resolvent_oneSubLap (I := I) (M := M) u).symm
    rw [h_eq, H1ComplToLp_smoothToH1Compl]
  · apply Subtype.ext
    exact smoothToH1Compl_eq_resolvent_oneSubLap (I := I) (M := M) u

example (g : SmoothRiemannianMetric I M) :
    Submodule ℝ (H1Compl g) := laplacianDomain (I := I) (M := M) g

example (g : SmoothRiemannianMetric I M) :
    laplacianDomain (I := I) (M := M) g →ₗ[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  laplacianOp (I := I) (M := M) g

/-- For `u, v ∈ laplacianDomain g`, the H¹ inner product expands via the
variational identity into an `Lp` inner product against the preimage. -/
private lemma h1Inner_eq_lpInner_with_preimage
    (g : SmoothRiemannianMetric I M)
    (u v : laplacianDomain (I := I) (M := M) g) :
    ⟪(u : H1Compl g), (v : H1Compl g)⟫_ℝ =
      ⟪H1ComplToLp (I := I) (M := M) g (v : H1Compl g),
        laplacianDomain.preimage (I := I) (M := M) g u⟫_ℝ := by
  have h_u_eq : (u : H1Compl g) = resolvent (I := I) (M := M) g
      (laplacianDomain.preimage (I := I) (M := M) g u) :=
    (resolvent_laplacianDomain_preimage_eq (I := I) (M := M) g u).symm
  rw [h_u_eq]
  exact resolvent_inner_eq_lpFunctional (I := I) (M := M) g
    (laplacianDomain.preimage (I := I) (M := M) g u) (v : H1Compl g)

/-- The L² inner product `⟨H1ComplToLp v, preimage u⟩` equals
`⟨H1ComplToLp u, preimage v⟩` (a key consequence of H¹ symmetry). -/
private lemma lpInner_preimage_swap
    (g : SmoothRiemannianMetric I M)
    (u v : laplacianDomain (I := I) (M := M) g) :
    ⟪H1ComplToLp (I := I) (M := M) g (v : H1Compl g),
        laplacianDomain.preimage (I := I) (M := M) g u⟫_ℝ =
      ⟪H1ComplToLp (I := I) (M := M) g (u : H1Compl g),
        laplacianDomain.preimage (I := I) (M := M) g v⟫_ℝ := by
  rw [← h1Inner_eq_lpInner_with_preimage (I := I) (M := M) g u v]
  rw [← h1Inner_eq_lpInner_with_preimage (I := I) (M := M) g v u]
  exact real_inner_comm _ _

/-- **Symmetry of the variational Laplacian.** For `u, v ∈ laplacianDomain g`,

  `⟨H1ComplToLp u, Δ_g v⟩_{L²} = ⟨Δ_g u, H1ComplToLp v⟩_{L²}`. -/
theorem laplacianOp_symmetric (g : SmoothRiemannianMetric I M)
    (u v : laplacianDomain (I := I) (M := M) g) :
    ⟪H1ComplToLp (I := I) (M := M) g (u : H1Compl g),
        laplacianOp (I := I) (M := M) g v⟫_ℝ =
      ⟪laplacianOp (I := I) (M := M) g u,
        H1ComplToLp (I := I) (M := M) g (v : H1Compl g)⟫_ℝ := by
  rw [laplacianOp_apply, laplacianOp_apply]
  rw [inner_sub_right, inner_sub_left]
  have h_swap := lpInner_preimage_swap (I := I) (M := M) g v u
  have h_swap_inner :
      ⟪H1ComplToLp (I := I) (M := M) g (u : H1Compl g),
          laplacianDomain.preimage (I := I) (M := M) g v⟫_ℝ =
        ⟪laplacianDomain.preimage (I := I) (M := M) g u,
          H1ComplToLp (I := I) (M := M) g (v : H1Compl g)⟫_ℝ := by
    rw [h_swap, real_inner_comm]
  linarith [h_swap_inner]

/-- For `u, v ∈ laplacianDomain g`, the H¹ inner product is symmetric.
This follows trivially from the symmetry of `⟨·, ·⟩_{H1Compl}`. -/
theorem h1Inner_symmetric_on_laplacianDomain
    (g : SmoothRiemannianMetric I M)
    (u v : laplacianDomain (I := I) (M := M) g) :
    ⟪(u : H1Compl g), (v : H1Compl g)⟫_ℝ =
      ⟪(v : H1Compl g), (u : H1Compl g)⟫_ℝ :=
  real_inner_comm _ _

example (g : SmoothRiemannianMetric I M)
    (u v : laplacianDomain (I := I) (M := M) g) :
    ⟪H1ComplToLp (I := I) (M := M) g (u : H1Compl g),
        laplacianOp (I := I) (M := M) g v⟫_ℝ =
      ⟪laplacianOp (I := I) (M := M) g u,
        H1ComplToLp (I := I) (M := M) g (v : H1Compl g)⟫_ℝ :=
  laplacianOp_symmetric (I := I) (M := M) g u v

end Laplacian
end Analysis
end DifferentialGeometry

end
