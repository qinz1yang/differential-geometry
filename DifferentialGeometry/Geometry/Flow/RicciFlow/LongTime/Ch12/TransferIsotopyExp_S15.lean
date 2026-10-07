import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
import DifferentialGeometry.Geometry.Exponential.Trivialization
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Velocity

/-!
# CH12-S15, H1 group B: joint smoothness of `(λ, p) ↦ exp_p (a(λ,p) · V(p))`

On a complete manifold, `expMapIntrinsic` is smooth on `TM` (`intrinsicExp_smooth`).  Composing
with a smooth scaling of a smooth tangent-bundle map gives the smooth family
`E(λ,p) = exp_p(λ χ(p) v(p))` of HPS03 once `a(λ,p) = λ χ(p)`, `V = v`.
-/

set_option autoImplicit false
open scoped Manifold ContDiff Topology
open Set Function Bundle Filter
noncomputable section
namespace GC.LongTime.Ch12

open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Riemannian.Exponential

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  {HN : Type*} [TopologicalSpace HN] {J : ModelWithCorners ℝ EN HN}
  {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]

/-- smooth scalar multiple of a tangent-bundle map is smooth at a point. -/
theorem contMDiffAt_smul_tangent_S15 (V : N → TangentBundle I M) (a : N → ℝ) {p₀ : N}
    (hV : ContMDiffAt J I.tangent ∞ V p₀) (ha : ContMDiffAt J 𝓘(ℝ, ℝ) ∞ a p₀) :
    ContMDiffAt J I.tangent ∞
      (fun p : N => (⟨(V p).proj, a p • (V p).snd⟩ : TangentBundle I M)) p₀ := by
  have hbase : ContMDiffAt J I ∞ (fun p : N => (V p).proj) p₀ :=
    (contMDiff_proj (TangentSpace I)).contMDiffAt.comp p₀ hV
  rw [contMDiffAt_totalSpace]
  have hV₀ := (contMDiffAt_totalSpace (f := V)).1 hV
  refine ⟨hbase, ?_⟩
  have hsmul := ha.smul hV₀.2
  refine hsmul.congr_of_eventuallyEq ?_
  have hmem : (V p₀).proj ∈
      (trivializationAt E (TangentSpace I) (V p₀).proj).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' (V p₀).proj
  have hb : ∀ᶠ p in 𝓝 p₀, (V p).proj ∈
      (trivializationAt E (TangentSpace I) (V p₀).proj).baseSet :=
    hbase.continuousAt.preimage_mem_nhds
      ((trivializationAt E (TangentSpace I) (V p₀).proj).open_baseSet.mem_nhds hmem)
  filter_upwards [hb] with p hp
  change ((trivializationAt E (TangentSpace I) (V p₀).proj)
      (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (V p).proj (a p • (V p).snd))).2 =
    a p • ((trivializationAt E (TangentSpace I) (V p₀).proj)
      (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (V p).proj (V p).snd)).2
  rw [(trivializationAt E (TangentSpace I) (V p₀).proj).apply_eq_prod_continuousLinearEquivAt
        ℝ (V p).proj hp,
      (trivializationAt E (TangentSpace I) (V p₀).proj).apply_eq_prod_continuousLinearEquivAt
        ℝ (V p).proj hp]
  exact map_smul _ _ _

/-- smooth scalar multiple of a smooth tangent-bundle map is smooth. -/
theorem contMDiff_smul_tangent_S15 (V : N → TangentBundle I M) (a : N → ℝ)
    (hV : ContMDiff J I.tangent ∞ V) (ha : ContMDiff J 𝓘(ℝ, ℝ) ∞ a) :
    ContMDiff J I.tangent ∞ (fun p : N => (⟨(V p).proj, a p • (V p).snd⟩ : TangentBundle I M)) :=
  fun p₀ => contMDiffAt_smul_tangent_S15 V a (hV p₀) (ha p₀)

section Complete
variable [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- **H1-B.** The scaled-exponential family `p ↦ exp_{(V p).proj}(a p • (V p).snd)` is jointly
smooth on a complete manifold.  With `N = ℝ × M`, `a(λ,p) = λ χ(p)`, `V(λ,p) = v(p)` this is
the smoothness of `E_λ(p) = exp_p(λ χ(p) v(p))`. -/
theorem contMDiff_scaledExp_S15 (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (V : N → TangentBundle I M) (a : N → ℝ)
    (hV : ContMDiff J I.tangent ∞ V) (ha : ContMDiff J 𝓘(ℝ, ℝ) ∞ a) :
    ContMDiff J I ∞ (fun p : N =>
      expMapIntrinsic g hEnorm (V p).proj (a p • (V p).snd)) :=
  (intrinsicExp_smooth (I := I) g hEnorm).comp (contMDiff_smul_tangent_S15 V a hV ha)

/-- the isotopy `E_λ(p) = exp_p(λ χ(p) v(p))`, for a smooth section `v` (a tangent-bundle map
over the identity) and smooth cutoff `χ`. -/
def transferIsotopy_S15 (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (v : M → TangentBundle I M) (χ : M → ℝ) : ℝ × M → M := fun q : ℝ × M =>
  expMapIntrinsic g hEnorm (v q.2).proj ((q.1 * χ q.2) • (v q.2).snd)

theorem contMDiff_transferIsotopy_S15 (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (v : M → TangentBundle I M) (χ : M → ℝ)
    (hv : ContMDiff I I.tangent ∞ v) (hχ : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (transferIsotopy_S15 g hEnorm v χ) :=
  contMDiff_scaledExp_S15 (J := 𝓘(ℝ, ℝ).prod I) g hEnorm (fun q : ℝ × M => v q.2) (fun q : ℝ × M => q.1 * χ q.2)
    (hv.comp contMDiff_snd) (contMDiff_fst.mul (hχ.comp contMDiff_snd))

/-- `E_0 = id` when `v` is a section. -/
theorem transferIsotopy_zero_S15 (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (v : M → TangentBundle I M) (χ : M → ℝ) (hsec : ∀ p, (v p).proj = p) (p : M) :
    transferIsotopy_S15 g hEnorm v χ (0, p) = p := by
  unfold transferIsotopy_S15
  simp only [zero_mul, zero_smul]
  have := expMapIntrinsic_zero (I := I) g hEnorm (v p).proj
  rw [hsec] at this ⊢
  exact this

end Complete
end GC.LongTime.Ch12
