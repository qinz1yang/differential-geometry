import DifferentialGeometry.Geometry.Collapse.SublevelCore.OpenBallBundleType

/-!
# Consumer of LC61 at a fixed normalized scale: the open balls are the soul's normal bundle

`eventually_open_ball_bundle_type` for LC54's actual normal-flow diffeomorphism
`e = normalFlowMap … ϕ ℓ : νS ≃ N` of a soul `S` (fibre radius `u = ‖(e.symm ·).2‖`, `du(V) = 1`
beyond `ℓ`, `normalFlow_radius_core_data`): on one tail every open ball `B(p_i, ρ)`,
`ρ ∈ [1/5, 2]`, is diffeomorphic to the whole normal bundle `νS`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle
open scoped Manifold ContDiff ENNReal Topology NNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Topology
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Topology.VectorBundle

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [SigmaCompactSpace N]
  [ConnectedSpace N]
  [RiemannianBundle (fun x : N => TangentSpace I x)] [IsRiemannianManifold I N]
  [CompleteSpace N] [IsContinuousRiemannianBundle E (fun x : N => TangentSpace I x)]
  [T2Space (TangentBundle I N)]
  {M : ℕ → Type} [∀ i, MetricSpace (M i)] [∀ i, ChartedSpace H (M i)]
  [∀ i, IsManifold I ∞ (M i)] [∀ i, SigmaCompactSpace (M i)]
  [∀ i, RiemannianBundle (fun x : M i => TangentSpace I x)]
  [∀ i, IsRiemannianManifold I (M i)] [∀ i, CompleteSpace (M i)]
  [∀ i, IsContinuousRiemannianBundle E (fun x : M i => TangentSpace I x)]

/-- **Consumer of `eventually_open_ball_bundle_type`: `B(p_i, ρ) ≅ νS`.** For LC54's actual
normal-flow diffeomorphism `e : νS ≃ N` of a soul `S`, a field `V` with flow `ϕ` and the LC55 collar
bounds, and a level `T₀ > ℓ` whose fibre-radius sublevel lies in `B(n, 1/2)`, one tail has every
open ball `B(p_i, ρ)`, `ρ ∈ [1/5, 2]`, diffeomorphic to the whole normal bundle. -/
theorem eventually_open_ball_soul_normal_type {m : ℕ} (hdim : Module.finrank ℝ E = m + 1)
    (g : SmoothRiemannianMetric I N) (hNorm : IsMetricNorm g)
    (U : TopologicalSpace.Opens N) (n : U)
    (hbuffer : Metric.closedBall (n : N) 10 ⊆ U)
    (hSeq : ℕ → SmoothRiemannianMetric I U)
    (gSeq : ∀ i, SmoothRiemannianMetric I (M i))
    (hSeqNorm : ∀ i, IsMetricNorm (gSeq i))
    (j : ∀ i, PartialDiffeomorph I I U (M i) ∞)
    (hj : ∀ i, (j i).source = univ)
    (hmetric : ∀ i, ∀ x : U, ∀ v w : TangentSpace I x,
      (hSeq i).inner x v w = (gSeq i).inner (j i x)
        (mfderiv I I (j i : U → M i) x v) (mfderiv I I (j i : U → M i) x w))
    (hconv : ∀ C : Set U, IsCompact C →
      MetricCPConvergenceOn C 1 hSeq (g.restrictOpen U) (g.restrictOpen U))
    {ζ : N → ℝ} {εN : ℝ≥0} (hεN : (εN : ℝ) ≤ 1 / 64)
    (hclose : ∀ x, |ζ x - dist (n : N) x| < 1 / 80)
    (hlip : LipschitzWith εN (fun x => ζ x - dist (n : N) x))
    {Wζ : Set N} (hWζ : IsOpen Wζ)
    (hcollarW : ∀ x, 3 / 4 < dist (n : N) x → dist (n : N) x < 5 / 4 → x ∈ Wζ)
    (hζW : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ ζ Wζ)
    {S : Set N} (hconvS : IsTotallyConvex g S) (hB : relBoundary I S = ∅) (hScomp : IsCompact S)
    (V : Cₛ^∞⟮I; E, TangentSpace I⟯) (ϕ : Flow ℝ N) {ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (hIntegral : ∀ q, IsMIntegralCurve (fun t => ϕ t q) V)
    (hVB : ∀ x, 3 / 4 < dist (n : N) x → dist (n : N) x < 5 / 4 → g.inner x (V x) (V x) ≤ 4)
    (hVdir : ∀ x, 3 / 4 < dist (n : N) x → dist (n : N) x < 5 / 4 →
      ∀ w ∈ inwardMinimizingDirections (I := I) g hNorm (n : N) x, g.inner x (V x) w ≤ -(1 / 4))
    {T₀ : ℝ} (hℓT₀ : ℓ < T₀)
    {ε : ℝ≥0} (hε : (ε : ℝ) < 1 / 32)
    (η : ∀ i, M i → ℝ) (eη : ℕ → ℝ)
    (hη : ∀ᶠ i in atTop, eη i < 1 / 40 ∧ (∀ x, |η i x - dist (j i n) x| < eη i) ∧
      LipschitzWith ε (fun x => η i x - dist (j i n) x) ∧
      ∃ Wi : Set (M i), IsOpen Wi ∧
        (∀ x, 1 / 10 ≤ dist (j i n) x → dist (j i n) x ≤ 10 → x ∈ Wi) ∧
        ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (η i) Wi ∧
        ∀ x, 1 / 10 ≤ dist (j i n) x → dist (j i n) x ≤ 10 →
          (1 - (ε : ℝ)) ^ 2 ≤ (gSeq i).inner x (gradientFun (I := I) (gSeq i) (η i) x)
            (gradientFun (I := I) (gSeq i) (η i) x)) :
    let hS := isEmbeddedSlice_of_relBoundary_eq_empty hNorm hconvS hB
    let _ := embeddedSliceChartedSpace hS
    let a := normalBundlePrebundle g hNorm hconvS hB
    let _ := a.totalSpaceTopology
    let _ := a.toFiberBundle
    let _ := a.toVectorBundle
    ∀ e : TotalSpace (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ)
        (normalBundleFiber g S) ≃ₘ⟮
          (𝓘(ℝ, Fin (maxSliceDim I S) → ℝ)).prod
            𝓘(ℝ, Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ), I⟯ N,
      (∀ z, e z = normalFlowMap (I := I) g hNorm S ϕ ℓ z) →
      {x | ‖(e.symm x).2‖ ≤ T₀} ⊆ Metric.ball (n : N) (1 / 2) →
      ∀ᶠ i in atTop, ∀ ρ ∈ Icc (1 / 5 : ℝ) 2,
        ∃ Ψ : PartialDiffeomorph I ((𝓘(ℝ, Fin (maxSliceDim I S) → ℝ)).prod
            𝓘(ℝ, Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ)) (M i)
            (TotalSpace (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ)
              (normalBundleFiber g S)) ∞,
          Ψ.source = Metric.ball (j i n) ρ ∧ Ψ.target = univ := by
  intro hS _ a _ _ _ e he hT₀
  let _ := embeddedSlice_isManifold hS
  let _ := normalBundle_isContMDiff g hNorm hconvS hB
  let _ := normalBundle_isContMDiffRiemannianBundle g hNorm hconvS hB
  have : CompactSpace S := isCompact_iff_compactSpace.mp hScomp
  obtain ⟨-, -, -, hdu⟩ :=
    normalFlow_radius_core_data g hNorm hconvS hB hScomp V ϕ hℓ hIntegral e he
  exact eventually_open_ball_bundle_type hdim g hNorm U n hbuffer hSeq gSeq hSeqNorm j hj hmetric
    hconv hεN hclose hlip hWζ hcollarW hζW (fun x => V x) hVB hVdir e one_pos
    (u := fun x => ‖(e.symm x).2‖) (fun x => (one_mul _).symm) (hℓ.trans_lt hℓT₀) hT₀
    isOpen_univ (subset_univ _) V.contMDiff.contMDiffOn
    (fun x hx => by rw [hdu x (lt_of_lt_of_le hℓT₀ hx)]; exact one_pos) hε η eη hη

end DifferentialGeometry.Geometry.Collapse
