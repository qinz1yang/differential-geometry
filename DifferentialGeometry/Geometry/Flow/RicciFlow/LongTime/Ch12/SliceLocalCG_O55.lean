import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.IncompleteLocal
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Scalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Background
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling

/-!
# CH12-O55, group 1: slice-form local Cheeger–Gromov extraction (`[FROZEN] CH12-O55 SliceLocalCG`)

Generic over a sequence of smooth 3-manifolds `(M n, g n, y n)` with scales `Q n > 0`
(for slices: `M n = (s n).stage.Carrier`, `g n = (s n).metric`, `Q n = R(y n)`).
On the rescaled metrics `gs n = Q n • g n`, inputs are: compact closed balls of radius `< Rb`,
curvature-derivative bounds (`hjets`, the slice Shi bounds) and the inner volume test.
Output: an incomplete pointed limit `(LM, gL, x₀)` of radius `Rb` with explicit approximating
maps `φ k`, smooth on an exhausting family `src k` (`[FROZEN v2] CH12-O56 φ-clause`),
capture of the rescaled balls, the `(1 ± ε)` metric comparison and scalar convergence.

Proof: the generic engine
`exists_pointed_convergence_with_uniform_metric_bounds_on_base_components`
(the core behind O3 / O23) + `pointedScalar_uniform_on_compact_of_canonical_domains`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace GC.LongTime.Ch12

universe u

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

/-- **Slice-form local Cheeger–Gromov extraction** (`[FROZEN] CH12-O55 SliceLocalCG`). -/
theorem sliceLocalCG_O55 (M : ℕ → Type u) [∀ n, TopologicalSpace (M n)]
    [∀ n, ChartedSpace ThreeSpace (M n)] [∀ n, IsManifold ThreeModel ∞ (M n)]
    [∀ n, SigmaCompactSpace (M n)] [∀ n, T2Space (M n)]
    [∀ n, T2Space (TangentBundle ThreeModel (M n))]
    (g : ∀ n, SmoothRiemannianMetric ThreeModel (M n)) (y : ∀ n, M n) (Q : ℕ → ℝ)
    (hQ : ∀ n, 0 < Q n) {Rb : ℝ} (hRb : 0 < Rb)
    (hcompact : ∀ R : ℝ, 0 < R → R < Rb → ∀ᶠ n in atTop,
      IsCompact (riemannianClosedBallOf (scaleMetric (Q n) (hQ n) (g n)) (y n) R))
    (hjets : ∀ R : ℝ, 0 < R → R < Rb → ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
      ∀ w : M n, riemannianEDistOf (scaleMetric (Q n) (hQ n) (g n)) (y n) w ≤
          ENNReal.ofReal R →
        curvDerivNorm p (scaleMetric (Q n) (hQ n) (g n)) w ≤ C)
    (hvol : ∀ r R : ℝ, 0 < r → r < R → R < Rb → ∀ C : ℝ, 0 ≤ C →
      ∃ a κ : ℝ, 0 < a ∧ 0 < κ ∧ r + a ≤ R ∧ a ^ 4 * C ^ 2 ≤ 1 ∧
      ∀ᶠ n in atTop, ∀ x ∈ riemannianClosedBallOf (scaleMetric (Q n) (hQ n) (g n)) (y n) r,
        ENNReal.ofReal (κ * a ^ 3) ≤
          riemannianVolumeMeasure ThreeModel (M n) (scaleMetric (Q n) (hQ n) (g n))
            (riemannianBallOf (scaleMetric (Q n) (hQ n) (g n)) x a)) :
    ∃ (LM : Type u) (_ : TopologicalSpace LM) (_ : ChartedSpace ThreeSpace LM)
      (_ : IsManifold ThreeModel ∞ LM) (_ : T2Space LM) (_ : SigmaCompactSpace LM)
      (gL : SmoothRiemannianMetric ThreeModel LM) (x₀ : LM) (f : ℕ → ℕ), StrictMono f ∧
      ∃ (φ : ∀ k, LM → M (f k)) (src : ℕ → Set LM),
        ((∀ k, IsOpen (src k)) ∧
          (∀ K : Set LM, IsCompact K → ∀ᶠ k in atTop, K ⊆ src k) ∧
          (∀ k, x₀ ∈ src k) ∧ (∀ k, ContMDiffOn ThreeModel ThreeModel ∞ (φ k) (src k))) ∧
        (∀ k, φ k x₀ = y (f k)) ∧
        (∀ x : LM, riemannianEDistOf gL x₀ x < ENNReal.ofReal Rb) ∧
        (∀ r : ℝ, r < Rb → IsCompact (riemannianClosedBallOf gL x₀ r)) ∧
        (∀ r : ℝ, r < Rb → ∀ᶠ k in atTop, ∀ w : M (f k),
          riemannianEDistOf (scaleMetric (Q (f k)) (hQ (f k)) (g (f k))) (y (f k)) w ≤
              ENNReal.ofReal r →
            ∃ x ∈ src k, φ k x = w) ∧
        (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ x ∈ src k, ∀ v : TangentSpace ThreeModel x,
          (1 - ε) * gL.inner x v v ≤
              (scaleMetric (Q (f k)) (hQ (f k)) (g (f k))).inner (φ k x)
                (mfderiv ThreeModel ThreeModel (φ k) x v)
                (mfderiv ThreeModel ThreeModel (φ k) x v) ∧
            (scaleMetric (Q (f k)) (hQ (f k)) (g (f k))).inner (φ k x)
                (mfderiv ThreeModel ThreeModel (φ k) x v)
                (mfderiv ThreeModel ThreeModel (φ k) x v) ≤
              (1 + ε) * gL.inner x v v) ∧
        (∀ K : Set LM, IsCompact K → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ x ∈ K,
          |metricScalarAt (g (f k)) (φ k x) / Q (f k) - metricScalarAt gL x| < ε) := by
  have : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
    { obj := fun n =>
        { M := M n
          basepoint := y n
          metric := scaleMetric (Q n) (hQ n) (g n) } }
  have hvolX : ∀ r R : ℝ, 0 < r → r < R → R < Rb → ∀ C : ℝ, 0 ≤ C →
      ∃ a κ : ℝ, 0 < a ∧ 0 < κ ∧ r + a ≤ R ∧ a ^ 4 * C ^ 2 ≤ 1 ∧
      ∀ᶠ n in atTop, ∀ x ∈ riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint r,
        ENNReal.ofReal (κ * a ^ Module.finrank ℝ ThreeSpace) ≤
          riemannianVolumeMeasure ThreeModel (X.obj n).M (X.obj n).metric
            (riemannianBallOf (X.obj n).metric x a) := by
    simpa only [ThreeSpace, finrank_euclideanSpace, Fintype.card_fin] using hvol
  obtain ⟨f, hf, r, hr, hrlim, L, F, C, hdomain, hradial, hcompactL, hcapture, hbounds⟩ :=
    exists_pointed_convergence_with_uniform_metric_bounds_on_base_components X hRb hcompact
      hjets hvolX
  try dsimp only at hcapture hbounds
  let U := fun i => connectedComponentOpen (I := ThreeModel) (X.obj i).basepoint
  let hp := fun i => (mem_connectedComponent : (X.obj i).basepoint ∈ U i)
  let F' := F.liftTargetOpen U hp
  refine ⟨L.M, L.topology, L.charted, L.smooth, L.t2, L.sigmaCompact, L.metric, L.basepoint,
    f, hf, fun k => F'.map k, fun k => F'.source k, ⟨fun k => F'.source_open k, ?_,
      fun k => F'.base_mem k, fun k => (F'.partialDiffeomorph k).contMDiffOn⟩,
    fun k => F'.basepoint_map k, hradial, ?_, ?_, hbounds, ?_⟩
  · intro K hK
    obtain ⟨k0, hk0⟩ := F'.source_subset hK
    exact eventually_atTop.mpr ⟨k0, hk0⟩
  · intro R hR
    by_cases h0 : 0 ≤ R
    · exact hcompactL R h0 hR
    · have hset : riemannianClosedBallOf L.metric L.basepoint R =
          riemannianClosedBallOf L.metric L.basepoint 0 := by
        ext z
        simp only [riemannianClosedBallOf, Set.mem_ofPred_eq,
          ENNReal.ofReal_of_nonpos (le_of_lt (not_le.mp h0)), ENNReal.ofReal_zero]
      rw [hset]
      exact hcompactL 0 le_rfl hRb
  · intro R hR
    have hev : ∀ᶠ k in atTop, R < r k :=
      (tendsto_order.mp hrlim).1 R hR
    filter_upwards [hev] with k hk
    intro w hw
    have hwt : w ∈ F'.target k := by
      apply hcapture k
      exact hw.trans (ENNReal.ofReal_le_ofReal hk.le)
    exact ⟨(F'.partialDiffeomorph k).symm w,
      (F'.partialDiffeomorph k).toPartialEquiv.map_target hwt,
      (F'.partialDiffeomorph k).toPartialEquiv.right_inv hwt⟩
  · intro K hK ε hε
    obtain ⟨k0, hk0⟩ :=
    DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalar_uniform_on_compact_of_canonical_domains C hdomain K hK ε hε
    refine eventually_atTop.mpr ⟨k0, fun k hk x hx => ?_⟩
    have h := (hk0 k hk).2 x hx
    change |metricScalarAt (scaleMetric (Q (f k)) (hQ (f k)) (g (f k))) (F'.map k x) -
      metricScalarAt L.metric x| < ε at h
    rw [metricScalarAt_scaleMetric] at h
    rwa [div_eq_inv_mul]

end GC.LongTime.Ch12

end
