import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThinBoundaryCollar

/-!
# CH12-S34 G3: metric error of a collar lifted through a smooth map

If `c : P → W₀` is smooth, `h` is the pullback metric `c^* g` (`hind`), and `L : cuspDomain → P`
is a smooth lift of `φ : cuspDomain → W₀` through `c` (`c ∘ L = φ`), then `L^* h = φ^* g` exactly,
so the `C^K` error of `L` against the model cusp equals the error of `φ`.  Applied to the cut
(`c = cutPieceMap`, `h = cutMetric`) this shows that the stretch of the cut presentation costs nothing:
the thin collar of the piece is `L = σ_i(·, ψ ·)` but its pulled-back metric is that of `φ = f ∘ cuspMap`.
-/

set_option autoImplicit false

noncomputable section

open Set TopologicalSpace DifferentialGeometry DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Connection
  DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Tensor.RSTensor
  DifferentialGeometry.Geometry.Collapse GC.Endpoint Bundle
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

universe u

/-- Iterated covariant derivative norms on the open set `cuspDomain` only depend on the field there. -/
theorem iterated_norm_congr_S34 (H : HyperbolicCusp) {s : ℕ}
    (A A' : (x : CuspHalfSpace) → Tensor0SSpace s halfCollarModel x)
    (hAA : ∀ z ∈ cuspDomain, A z = A' z) (k : ℕ) {p : CuspHalfSpace} (hp : p ∈ cuspDomain) :
    tensor0SFiberNorm H.metric p (s + k) (iteratedMetricCovariantDerivative H.metric s A k p) =
      tensor0SFiberNorm H.metric p (s + k) (iteratedMetricCovariantDerivative H.metric s A' k p) := by
  have h1 := tensor0SFiberNorm_iteratedMetricCovariantDerivative_restrictOpen H.metric
    cuspDomainOpens_C4 A k ⟨p, hp⟩
  have h2 := tensor0SFiberNorm_iteratedMetricCovariantDerivative_restrictOpen H.metric
    cuspDomainOpens_C4 A' k ⟨p, hp⟩
  have hfun : (fun z : cuspDomainOpens_C4 => Tensor0SSpace.ofModel (I := halfCollarModel)
        (x := z) (Tensor0SSpace.toModel (A (z : CuspHalfSpace)))) =
      (fun z : cuspDomainOpens_C4 => Tensor0SSpace.ofModel (I := halfCollarModel)
        (x := z) (Tensor0SSpace.toModel (A' (z : CuspHalfSpace)))) := by
    funext z
    rw [hAA z z.2]
  rw [← h1, ← h2, hfun]

theorem localPullInner_transfer_S34 {W₀ P : CompactCarrier.{u}}
    (g : SmoothRiemannianMetric W₀.model W₀.Carrier)
    (c : P.Carrier → W₀.Carrier) (hc : ContMDiff P.model W₀.model ∞ c)
    (h : SmoothRiemannianMetric P.model P.Carrier)
    (hind : ∀ (x : P.Carrier) (v w : TangentSpace P.model x), h.inner x v w =
      g.inner (c x) (mfderiv P.model W₀.model c x v) (mfderiv P.model W₀.model c x w))
    (L : CuspHalfSpace → P.Carrier) (φ : CuspHalfSpace → W₀.Carrier)
    (hL : ContMDiffOn halfCollarModel P.model ∞ L cuspDomain)
    (hb : ∀ p ∈ cuspDomain, c (L p) = φ p) {p : CuspHalfSpace} (hp : p ∈ cuspDomain) :
    localPullInner (I := halfCollarModel) (J := P.model) h L p =
      localPullInner (I := halfCollarModel) (J := W₀.model) g φ p := by
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by decide
  have hnhds : cuspDomain ∈ nhds p := isOpen_cuspDomain_C4.mem_nhds hp
  have hLd : MDifferentiableAt halfCollarModel P.model L p :=
    (hL.contMDiffAt hnhds).mdifferentiableAt hn
  have hcd : MDifferentiableAt P.model W₀.model c (L p) := (hc (L p)).mdifferentiableAt hn
  have hev : φ =ᶠ[nhds p] c ∘ L :=
    Filter.eventuallyEq_of_mem hnhds (fun q hq => (hb q hq).symm)
  have hder : mfderiv halfCollarModel W₀.model φ p =
      (mfderiv P.model W₀.model c (L p)).comp (mfderiv halfCollarModel P.model L p) := by
    rw [hev.mfderiv_eq]
    exact mfderiv_comp p hcd hLd
  refine ContinuousLinearMap.ext fun v => ContinuousLinearMap.ext fun w => ?_
  rw [localPullInner_apply, localPullInner_apply, hind, hder, ← hb p hp]
  rfl

/-- **G3.** The `C^K` cusp-metric error of the lift `L` equals that of `φ`. -/
theorem cuspMetricErrorBound_transfer_S34 {W₀ P : CompactCarrier.{u}}
    (g : SmoothRiemannianMetric W₀.model W₀.Carrier)
    (c : P.Carrier → W₀.Carrier) (hc : ContMDiff P.model W₀.model ∞ c)
    (h : SmoothRiemannianMetric P.model P.Carrier)
    (hind : ∀ (x : P.Carrier) (v w : TangentSpace P.model x), h.inner x v w =
      g.inner (c x) (mfderiv P.model W₀.model c x v) (mfderiv P.model W₀.model c x w))
    (K : ℕ) (δ : ℝ) (H : HyperbolicCusp)
    (L : CuspHalfSpace → P.Carrier) (φ : CuspHalfSpace → W₀.Carrier)
    (hL : ContMDiffOn halfCollarModel P.model ∞ L cuspDomain)
    (hb : ∀ p ∈ cuspDomain, c (L p) = φ p)
    (hbd : cuspMetricErrorBound g K δ H φ) : cuspMetricErrorBound h K δ H L := by
  intro k hk p hp
  have heq : ∀ z ∈ cuspDomain, cuspMetricError h H L z = cuspMetricError g H φ z := by
    intro z hz
    unfold cuspMetricError
    rw [localPullInner_transfer_S34 g c hc h hind L φ hL hb hz]
  rw [iterated_norm_congr_S34 H (cuspMetricError h H L) (cuspMetricError g H φ) heq k hp]
  exact hbd k hk p hp

end GC.LongTime.Ch12
