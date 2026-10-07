import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.OuterCurvature_S41
import DifferentialGeometry.Geometry.Curvature.Metric.ConstantSectionalNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.SectionalFromCurvatureBound

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set Filter
open Manifold GC.LongTime DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff ENNReal Topology
universe u
namespace GC.LongTime.Ch12

/-- **(G2, hLow)** Uniform lower sectional bound `-1/c₀²` on `B_ḡ(φ y, c₀)` for `y ∈ B(x_i, n)`,
from the C² buffer error and the universal curvature perturbation bound; `hC0` is the C⁰
comparison (frozen shape, supplied by S40's S2). -/
theorem hLow_S41 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ} (B : BufferedPersistentCores F K)
    (hC0 : ∃ T₀ : ℝ, ∀ t (ht : B.start ≤ t), T₀ ≤ t → ∀ i : Fin B.count,
      ∀ y ∈ riemannianBallOf (B.model i).metric (B.model i).basepoint (B.accuracy t)⁻¹,
      ∀ x ∈ riemannianClosedBallOf (B.model i).metric y 4, ∀ v : TangentSpace (𝓡 3) x,
        (B.model i).metric.inner x v v ≤
          (2 : ℝ) ^ 2 * (scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht))
            (postMetric F.observation t)).inner (B.map i t ht x)
            (mfderiv (𝓡 3) (𝓡 3) (B.map i t ht) x v)
            (mfderiv (𝓡 3) (𝓡 3) (B.map i t ht) x v)) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ T₁ : ℝ, ∀ t (ht : B.start ≤ t), T₁ ≤ t → ∀ i : Fin B.count,
      ∀ y ∈ riemannianBallOf (B.model i).metric (B.model i).basepoint (B.accuracy t)⁻¹,
      ∀ q ∈ riemannianBallOf (scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht))
          (postMetric F.observation t)) (B.map i t ht y) c₀,
        SectionalBoundedBelowAt (scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht))
          (postMetric F.observation t)) q (-(c₀ ^ 2)⁻¹) := by
  obtain ⟨T₀, hT₀C⟩ := hC0
  have hCex := fun i : Fin B.count =>
    DifferentialGeometry.Geometry.Curvature.exists_pos_bound_intrinsic_curvature_derivative_of_metric_error
      (I := 𝓡 3) (M := (B.model i).Carrier) 0 (1 / 2) 1 (by norm_num)
  choose C hCpos hC using hCex
  set Cs : ℝ := 1 + ∑ i, C i with hCs
  have hCs1 : 1 ≤ Cs := by
    have : 0 ≤ ∑ i, C i := Finset.sum_nonneg fun i _ => (hCpos i).le
    linarith
  have hCle : ∀ i, C i ≤ Cs := fun i => by
    have := Finset.single_le_sum (f := C) (fun j _ => (hCpos j).le) (Finset.mem_univ i)
    linarith
  obtain ⟨T₁, -, hT₁⟩ := accuracy_inv_large_S29 B 10000
  refine ⟨min 1 (1 / Cs), lt_min one_pos (by positivity), max T₀ T₁, fun t ht hT i y hy q hq => ?_⟩
  have hn : (10000 : ℝ) ≤ (B.accuracy t)⁻¹ := hT₁ t ((le_max_right _ _).trans hT)
  have hpos : 0 < B.accuracy t := B.accuracy_pos t ht
  have hacc : B.accuracy t ≤ 1 / 2 := by
    rw [le_inv_comm₀ (by norm_num) hpos] at hn
    have : B.accuracy t ≤ (10000 : ℝ)⁻¹ := by simpa using hn
    linarith
  have hceil : 2 ≤ ⌈(B.accuracy t)⁻¹⌉₊ := by
    have h2 : (2 : ℝ) ≤ ⌈(B.accuracy t)⁻¹⌉₊ := (by linarith : (2 : ℝ) ≤ (B.accuracy t)⁻¹).trans
      (Nat.le_ceil _)
    exact_mod_cast h2
  have hk : 2 ≤ max K ⌈(B.accuracy t)⁻¹⌉₊ := hceil.trans (le_max_right _ _)
  have hyd : y ∈ B.domain i t := B.buffer_domain i t ht
    (riemannianBallOf_mono _ _ (by linarith) hy)
  -- first exit
  have hsource : riemannianClosedBallOf (B.model i).metric y 4 ⊆ (B.domain i t : Set _) := by
    intro z hz
    apply B.buffer_domain i t ht
    have hy' : riemannianEDistOf (B.model i).metric (B.model i).basepoint y <
        ENNReal.ofReal (B.accuracy t)⁻¹ := hy
    have hz' : riemannianEDistOf (B.model i).metric y z ≤ ENNReal.ofReal 4 := hz
    change riemannianEDistOf (B.model i).metric (B.model i).basepoint z <
      ENNReal.ofReal (2 * (B.accuracy t)⁻¹)
    calc riemannianEDistOf (B.model i).metric (B.model i).basepoint z
        ≤ riemannianEDistOf (B.model i).metric (B.model i).basepoint y +
          riemannianEDistOf (B.model i).metric y z := riemannianEDistOf_triangle _ _ _ _
      _ < ENNReal.ofReal (B.accuracy t)⁻¹ + ENNReal.ofReal 4 :=
          ENNReal.add_lt_add_of_lt_of_le (ne_of_lt (lt_of_le_of_lt hz' (by simp))) hy' hz'
      _ = ENNReal.ofReal ((B.accuracy t)⁻¹ + 4) :=
          (ENNReal.ofReal_add (by positivity) (by norm_num)).symm
      _ ≤ ENNReal.ofReal (2 * (B.accuracy t)⁻¹) :=
          ENNReal.ofReal_le_ofReal (by linarith)
  have hcap := ambient_ball_subset_image_S35 B i t ht
    (scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht)) (postMetric F.observation t))
    y hyd (R := 4) (L := 2) (by norm_num) (by norm_num) hsource
    (hT₀C t ht ((le_max_left _ _).trans hT) i y hy)
  have hc1 : min 1 (1 / Cs) ≤ 4 / 2 := (min_le_left _ _).trans (by norm_num)
  obtain ⟨z, hz4, rfl⟩ := hcap (riemannianBallOf_mono _ _ hc1 hq)
  have hz2 : z ∈ riemannianBallOf (B.model i).metric (B.model i).basepoint
      (2 * (B.accuracy t)⁻¹) := by
    have hy' : riemannianEDistOf (B.model i).metric (B.model i).basepoint y <
        ENNReal.ofReal (B.accuracy t)⁻¹ := hy
    have hz' : riemannianEDistOf (B.model i).metric y z ≤ ENNReal.ofReal 4 := hz4
    change riemannianEDistOf (B.model i).metric (B.model i).basepoint z <
      ENNReal.ofReal (2 * (B.accuracy t)⁻¹)
    calc riemannianEDistOf (B.model i).metric (B.model i).basepoint z
        ≤ riemannianEDistOf (B.model i).metric (B.model i).basepoint y +
          riemannianEDistOf (B.model i).metric y z := riemannianEDistOf_triangle _ _ _ _
      _ < ENNReal.ofReal (B.accuracy t)⁻¹ + ENNReal.ofReal 4 :=
          ENNReal.add_lt_add_of_lt_of_le (ne_of_lt (lt_of_le_of_lt hz' (by simp))) hy' hz'
      _ = ENNReal.ofReal ((B.accuracy t)⁻¹ + 4) :=
          (ENNReal.ofReal_add (by positivity) (by norm_num)).symm
      _ ≤ ENNReal.ofReal (2 * (B.accuracy t)⁻¹) :=
          ENNReal.ofReal_le_ofReal (by linarith)
  obtain ⟨q', hq', hiff⟩ := bufferedMap_curvature_bridge_S41 B i t ht
    (scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht)) (postMetric F.observation t))
    (fun w => by
      ext a b
      simp only [localPullInner_apply, scaleMetric_inner, smul_apply, smul_eq_mul])
    z hz2 hk
  -- reference norm bound
  have hsec : ∀ a b : TangentSpace (𝓡 3) z,
      metricRm04StandardAt (B.model i).metric z a b b a =
        -(1 / 4 : ℝ) * ((B.model i).metric.inner z a a * (B.model i).metric.inner z b b -
          (B.model i).metric.inner z a b ^ 2) := fun a b => by
    rw [metricRm_eq_neg_quarter_S26 (B.model i) z a b]; ring
  have hnorm := normSq0S_metricRm04At_eq_of_constant_sectional_numerator
    (B.model i).metric z (-(1 / 4 : ℝ)) hsec
  have hrank : (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) : ℝ) = 3 := by simp
  rw [hrank] at hnorm
  have hRef : ∀ s ≤ 0, Real.sqrt (normSq0S (B.model i).metric z (4 + s)
      (iterCov (B.model i).metric 4 (metricRm04 (B.model i).metric) s z)) ≤ 1 := by
    intro s hs
    obtain rfl : s = 0 := Nat.le_zero.mp hs
    refine Real.sqrt_le_one.mpr ?_
    have h0 : normSq0S (B.model i).metric z (4 + 0)
        (iterCov (B.model i).metric 4 (metricRm04 (B.model i).metric) 0 z) =
        normSq0S (B.model i).metric z 4 (metricRm04At (B.model i).metric z) := rfl
    rw [h0, hnorm]; norm_num
  have hbd := hC i (B.model i).metric q' z
    (fun s hs => (hq' s (by omega)).le.trans hacc) hRef
  have hbd' : normSq0S q' z 4 (metricRm04At q' z) ≤ (C i) ^ 2 := by
    have h0 : normSq0S q' z (4 + 0) (iterCov q' 4 (metricRm04 q') 0 z) =
        normSq0S q' z 4 (metricRm04At q' z) := rfl
    rw [h0] at hbd
    have := Real.sqrt_le_left (hCpos i).le |>.mp hbd
    exact this
  have hsecq := DifferentialGeometry.PDE.RicciFlow.sectionalBoundedBelowAt_neg_sqrt_of_normSq0S_le
    (I := 𝓡 3) q' z hbd'
  rw [Real.sqrt_sq (hCpos i).le] at hsecq
  refine ((hiff _).mp hsecq).mono ?_
  -- `Cs ≤ (c₀²)⁻¹`
  have hc0 : 0 < min 1 (1 / Cs) := lt_min one_pos (by positivity)
  have hc1' : min 1 (1 / Cs) ≤ 1 := min_le_left _ _
  have hc2 : min 1 (1 / Cs) ≤ 1 / Cs := min_le_right _ _
  have hsq : (min 1 (1 / Cs)) ^ 2 ≤ 1 / Cs := by nlinarith
  have hinv : Cs ≤ ((min 1 (1 / Cs)) ^ 2)⁻¹ := by
    rw [le_inv_comm₀ (by linarith) (by positivity)]
    simpa [one_div] using hsq
  linarith [hCle i]

end GC.LongTime.Ch12
