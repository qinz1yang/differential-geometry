import DifferentialGeometry.Geometry.Collapse.LocalExport.SlimProductModel
import DifferentialGeometry.Topology.Manifold.Orientation

/-!
# The compact factor of an LC81 slim product model is a surface (LFR20 item 3)

Blueprint LFR20 (master207A:26358), item 3: "a complete finite product `N = ℝ × Z` with
`diam Z ≤ D`, a compact connected oriented nonnegative `C^{K-1}` surface `Z`"; LC85
(`def:collapse-slim-packet`, A:30962): "`Z` is a compact connected orientable nonnegative surface".
`SlimProductModel` keeps the compact factor only as a compact METRIC space `W` with the exact
splitting `e : N ≃ᵢ ℓ²(ℝ × W)`. Lane LFR20-CMP, packet 2 (review 43, row LFR20 (ii)).

`SlimSurfaceFactor P` records, for ONE product model `P`, the surface structure of ITS factor
`P.W`: a smooth surface `S` (model `𝓡 2`), an isometry `ψ : S ≃ᵢ P.W`, a `C^{K-1}` Riemannian
metric `κ` on `S` whose distance is the distance of `S` (`IsRiemannianManifold`, tangent norm the
`κ`-norm), `sec_κ ≥ 0`, an orientation of `S`, and the identification of `N` with the Riemannian
product `ℝ × S` through the SAME splitting: `Ψ (t, s) = e⁻¹(t, ψ s)` is `C^K` with `C^K` inverse
`x ↦ ((e x)_ℝ, ψ⁻¹ (e x)_W)`, and `Ψ^* G = dt² + κ`.

Compactness and connectedness of `S` are consequences (`SlimSurfaceFactor.compactSpace`,
`SlimSurfaceFactor.connectedSpace`). Producer: `nonempty_slimSurfaceFactor`
(`FiniteSurface/SlimSurfaceFactorProducer.lean`), from an orientation of `P.N`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Metric WithLp Manifold
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry.Collapse

open GC.MetricGeometry

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] SlimProductModel.instMetricN SlimProductModel.instChartedN
  SlimProductModel.instManifoldN SlimProductModel.instProperN SlimProductModel.instConnectedN
  SlimProductModel.instBundleN SlimProductModel.instRiemannianN SlimProductModel.instMetricW
  SlimProductModel.instCompactW

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)

local instance nezero_finrank_euclidean_three_surfaceFactor_LFR20CMP :
    NeZero (Module.finrank ℝ E3) :=
  ⟨by rw [finrank_euclideanSpace_fin]; decide⟩

variable {M : Type*} [MetricSpace M] [ChartedSpace E3 M] [IsManifold 𝓘(ℝ, E3) ∞ M]
  [SigmaCompactSpace M] [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]
  [IsRiemannianManifold 𝓘(ℝ, E3) M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E3 (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]

/-- **The surface structure of the compact factor of an LC81 slim product model** (LFR20 item 3).
See the module docstring. -/
structure SlimSurfaceFactor {g : SmoothRiemannianMetric 𝓘(ℝ, E3) M}
    {hEnorm : DifferentialGeometry.Geometry.Riemannian.IsMetricNorm g} {Δ σ : ℝ}
    {Y : Type*} [MetricSpace Y] {p : M} {y₀ : Y} {β : ℝ}
    {α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) β}
    {c : SlimChart g hEnorm Δ σ α} {K : ℕ} (P : SlimProductModel c K) where
  /-- The smooth surface. -/
  S : Type
  [instMetricS : MetricSpace S]
  [instChartedS : ChartedSpace E2 S]
  [instManifoldS : IsManifold (𝓡 2) ∞ S]
  [instBundleS : RiemannianBundle (fun x : S => TangentSpace (𝓡 2) x)]
  [instRiemannianS : IsRiemannianManifold (𝓡 2) S]
  /-- The surface IS the factor of the splitting `P.e`, isometrically. -/
  ψ : S ≃ᵢ P.W
  /-- Its finite-order metric, inducing the distance of `S`. -/
  κ : ContMDiffRiemannianMetric (𝓡 2) ((K - 1 : ℕ) : ℕ∞ω) E2 (TangentSpace (𝓡 2) : S → Type _)
  enorm : ∀ (x : S) (w : TangentSpace (𝓡 2) x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (κ.inner x w w))
  sectional_nonneg : ∀ (x : S) (v w : TangentSpace (𝓡 2) x), 0 ≤ κ.sectionalCurvature x v w
  /-- An orientation of the surface. -/
  orientation : ManifoldOrientation (𝓡 2) S 2
  /-- `N` is the product `ℝ × S` through the SAME splitting, in class `C^K` … -/
  product_contMDiff : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) K
    (fun q : ℝ × S => P.e.symm (toLp 2 (q.1, ψ q.2)))
  product_symm_contMDiff : ContMDiff 𝓘(ℝ, E3) (𝓘(ℝ, ℝ).prod (𝓡 2)) K
    (fun x : P.N => ((P.e x).fst, ψ.symm (P.e x).snd))
  /-- … and as a Riemannian product: `Ψ^* G = dt² + κ`. -/
  product_metric : ∀ (q : ℝ × S) (v w : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 2)) q),
    P.G.inner (P.e.symm (toLp 2 (q.1, ψ q.2)))
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3)
        (fun q : ℝ × S => P.e.symm (toLp 2 (q.1, ψ q.2))) q v)
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3)
        (fun q : ℝ × S => P.e.symm (toLp 2 (q.1, ψ q.2))) q w) =
    inner ℝ v.1 w.1 + κ.inner q.2 v.2 w.2

attribute [local instance] SlimSurfaceFactor.instMetricS SlimSurfaceFactor.instChartedS
  SlimSurfaceFactor.instManifoldS SlimSurfaceFactor.instBundleS SlimSurfaceFactor.instRiemannianS

namespace SlimSurfaceFactor

variable {g : SmoothRiemannianMetric 𝓘(ℝ, E3) M}
  {hEnorm : DifferentialGeometry.Geometry.Riemannian.IsMetricNorm g} {Δ σ : ℝ}
  {Y : Type*} [MetricSpace Y] {p : M} {y₀ : Y} {β : ℝ}
  {α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) β}
  {c : SlimChart g hEnorm Δ σ α} {K : ℕ} {P : SlimProductModel c K}

/-- The surface is compact (it is isometric to the compact factor). -/
theorem compactSpace (Q : SlimSurfaceFactor P) : CompactSpace Q.S :=
  Q.ψ.symm.toHomeomorph.compactSpace

/-- The surface is connected (it is the image of the connected model under the splitting). -/
theorem connectedSpace (Q : SlimSurfaceFactor P) : ConnectedSpace Q.S := by
  have hsurj : Function.Surjective (fun x : P.N => Q.ψ.symm (P.e x).snd) := by
    intro s
    refine ⟨P.e.symm (toLp 2 (0, Q.ψ s)), ?_⟩
    simp only [IsometryEquiv.apply_symm_apply]
    exact Q.ψ.symm_apply_apply s
  exact hsurj.connectedSpace
    (Q.ψ.symm.continuous.comp (continuous_snd.comp ((WithLp.prod_continuous_ofLp 2 ℝ P.W).comp
      P.e.continuous)))

end SlimSurfaceFactor

end DifferentialGeometry.Geometry.Collapse
