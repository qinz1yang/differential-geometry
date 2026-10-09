import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.KL83GeometricLimit_CX7
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.KL83Scaling_CX7
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL83Reduce_O6

/-!
# CH12-CX7: the uniform KL83.1 core at unit scale

The contradiction sequence is blown up at `ρᵢ = 1/(i+2)`, while the excluded radius
is `ρᵢ²`. Noncollapse survives this blow-up. A rank-three packet in the proper
limit lifts to a ball of fixed positive radius, contradicting the excluded scale.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter
open scoped Manifold ContDiff ENNReal NNReal Topology
open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
  (modelVolume euclideanUnitBallVolume euclideanUnitBallVolume_pos)
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.MetricGeometry

namespace GC.LongTime.Ch12

universe u

/-- There is no sequence of noncollapsed unit balls excluding almost-model balls
at all radii at least `(i+2)⁻²`. -/
theorem no_bad_unit_sequence_CX7
    {X : ℕ → Type u} [mX : ∀ i, MetricSpace (X i)] [∀ i, ChartedSpace ThreeSpace (X i)]
    [∀ i, IsManifold ThreeModel ∞ (X i)] [∀ i, CompactSpace (X i)]
    (g : ∀ i, SmoothRiemannianMetric ThreeModel (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    (p : ∀ i, X i) {w ε : ℝ} (hw : 0 < w) (hε : 0 < ε) (hε1 : ε < 1)
    (hsec : ∀ i, ∀ q ∈ riemannianBallOf (g i) (p i) 1, SectionalBoundedBelowAt (g i) q (-1))
    (hvol : ∀ i, ENNReal.ofReal w ≤ ballVolume (g i) (p i) 1)
    (hbad : ∀ i (y : X i) (σ : ℝ), (((i : ℝ) + 2)⁻¹) ^ 2 ≤ σ →
      dist (p i) y + 2 * σ ≤ 1 →
      ballVolume (g i) y σ < ENNReal.ofReal ((1 - ε) * modelVolume (-1) 3 σ)) : False := by
  let L : ℕ → ℝ := fun i => (i : ℝ) + 2
  let ρ : ℕ → ℝ := fun i => (L i)⁻¹
  have hLpos (i : ℕ) : 0 < L i := by dsimp [L]; positivity
  have hρ (i : ℕ) : 0 < ρ i := inv_pos.mpr (hLpos i)
  have hρle (i : ℕ) : 2 * ρ i ≤ 1 := by
    dsimp [ρ]
    have h2 : 2 ≤ L i := by dsimp [L]; linarith [Nat.cast_nonneg (α := ℝ) i]
    have hinv := inv_anti₀ (by norm_num : (0 : ℝ) < 2) h2
    norm_num at hinv
    linarith
  have hL : Tendsto L atTop atTop :=
    tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have hbuffer : ∀ i, ∀ y ∈ riemannianBallOf (g i) (p i) (L i * ρ i),
      SectionalBoundedBelowAt (g i) y (-((L i * ρ i) ^ 2)⁻¹) := by
    intro i
    have heq : L i * ρ i = 1 := mul_inv_cancel₀ (hLpos i).ne'
    simpa only [heq, one_pow, inv_one] using hsec i
  have hlower (i : ℕ) : ENNReal.ofReal (Real.exp (-4) * w) ≤
      ballVolume (scaleMetric ((ρ i)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρ i)) 2) (g i)) (p i) 2 :=
    noncollapse_rescale_CX7 hdim (g i) (hmetric i) (p i) (hρ i) (hρle i) (hsec i) (hvol i)
  obtain ⟨Y, mY, q, φ, hφ, hcomplete, hproper, hconv, hdimY, hcomp, -, -, -⟩ :=
    exists_rescaled_pointed_limit_of_sectional_buffer g hmetric p hρ hL hbuffer
  let := mY
  have : CompleteSpace Y := hcomplete
  have : ProperSpace Y := hproper
  let m' : ∀ i, MetricSpace (X (φ i)) := fun i =>
    (mX (φ i)).rescale (ρ (φ i))⁻¹ (inv_pos.mpr (hρ (φ i)))
  let : ∀ i, MetricSpace (X (φ i)) := m'
  let g' := fun i => scaleMetric ((ρ (φ i))⁻¹ ^ 2)
    (pow_pos (inv_pos.mpr (hρ (φ i))) 2) (g (φ i))
  have hm' (i : ℕ) (a b : X (φ i)) : riemannianEDistOf (g' i) a b = ENNReal.ofReal (dist a b) :=
    riemannianEDistOf_scaleMetric_inv_sq_eq_rescale (m := mX (φ i)) (g (φ i)) (hmetric (φ i)) (hρ (φ i)) a b
  have hL' : Tendsto (fun i => L (φ i)) atTop atTop := hL.comp hφ.tendsto_atTop
  have hs' (i : ℕ) (y : X (φ i)) (hy : y ∈ ball (p (φ i)) (L (φ i))) :
      SectionalBoundedBelowAt (g' i) y (-((L (φ i))⁻¹ ^ 2)) := by
    have h := sectionalBoundedBelowAt_rescaled_ball (m := mX (φ i)) (g (φ i)) (hmetric (φ i))
      (p (φ i)) (hρ (φ i)) (hbuffer (φ i)) y hy
    simpa only [g', inv_pow] using h
  have hdlo : 2 < dimH (univ : Set Y) :=
    dimH_gt_two_of_riemannian_noncollapse_CX7 hdim g' hm' hconv
      (by positivity : 0 < Real.exp (-4) * w)
      (Eventually.of_forall (fun i => hlower (φ i)))
      (eventually_sectional_neg_one_CX7 g' hL' hs' 5)
  have hdhi : dimH (univ : Set Y) ≤ 3 := by simpa only [hdim, Nat.cast_ofNat] using hdimY
  let θ := min (ε / 36) (1 / 20)
  have hθ : 0 < θ := by positivity
  have hθ1 : θ ≤ 1 / 10 := (min_le_right _ _).trans (by norm_num)
  have hθeps : 9 * θ < ε := by have := min_le_left (ε / 36) (1 / 20); dsimp only [θ]; linarith
  obtain ⟨s, hs, hs1, htail⟩ := eventually_almost_euclidean_ball_CX7 hdim g' hm' hL' hs'
    hconv hcomp hdlo hdhi hθ hθ1
  have hrzero : Tendsto (fun i => ρ (φ i)) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hL'
  have hrsmall : ∀ᶠ i in atTop, ρ (φ i) ≤ s := (hrzero.eventually (gt_mem_nhds hs)).mono (fun _ h => h.le)
  have hexplim : Tendsto (fun i => (1 - ε) * Real.exp (2 * (ρ (φ i) * s)))
      atTop (𝓝 (1 - ε)) := by
    have hz2 : Tendsto (fun i => 2 * (ρ (φ i) * s)) atTop (𝓝 0) := by
      simpa using (hrzero.mul_const s).const_mul 2
    have ht := (Real.continuous_exp.tendsto 0).comp hz2
    simpa using ht.const_mul (1 - ε)
  have hexpsmall : ∀ᶠ i in atTop, (1 - ε) * Real.exp (2 * (ρ (φ i) * s)) < 1 - 9 * θ :=
    hexplim.eventually (gt_mem_nhds (by linarith))
  obtain ⟨i, ⟨y, hy, hyv⟩, hri, hei⟩ := (htail.and (hrsmall.and hexpsmall)).exists
  have hσ : 0 < ρ (φ i) * s := mul_pos (hρ _) hs
  have hσlow : (((φ i : ℝ) + 2)⁻¹) ^ 2 ≤ ρ (φ i) * s := by
    change ρ (φ i) ^ 2 ≤ ρ (φ i) * s
    nlinarith only [mul_le_mul_of_nonneg_left hri (hρ (φ i)).le]
  have hdist : @dist (X (φ i)) (mX (φ i)).toDist (p (φ i)) y + 2 * (ρ (φ i) * s) ≤ 1 := by
    change (ρ (φ i))⁻¹ * @dist (X (φ i)) (mX (φ i)).toDist y (p (φ i)) < 1 / 2 at hy
    have hd := (inv_mul_lt_iff₀ (hρ (φ i))).mp hy
    rw [@dist_comm (X (φ i)) (mX (φ i)).toPseudoMetricSpace y (p (φ i))] at hd
    nlinarith only [hd, hs1, hρle (φ i), hρ (φ i)]
  have hsqrt : Real.sqrt ((ρ (φ i))⁻¹ ^ 2) * (ρ (φ i) * s) = s := by
    rw [Real.sqrt_sq (inv_pos.mpr (hρ (φ i))).le, ← mul_assoc,
      inv_mul_cancel₀ (hρ (φ i)).ne', one_mul]
  have hback : ENNReal.ofReal (((1 - 9 * θ) * euclideanUnitBallVolume 3) * (ρ (φ i) * s) ^ 3) ≤
      ballVolume (g (φ i)) y (ρ (φ i) * s) := by
    apply (le_ballVolume_scaleMetric_iff hdim ((ρ (φ i))⁻¹ ^ 2)
      (pow_pos (inv_pos.mpr (hρ (φ i))) 2)).mp
    rw [hsqrt]
    exact hyv
  have hmodel : (1 - ε) * modelVolume (-1) 3 (ρ (φ i) * s) ≤
      ((1 - 9 * θ) * euclideanUnitBallVolume 3) * (ρ (φ i) * s) ^ 3 := by
    have hω := euclideanUnitBallVolume_pos 3
    have hm := modelVolume_neg_sq_three_le (q := 1) zero_le_one hσ.le
    norm_num only [one_pow, one_mul] at hm
    have hmul := mul_le_mul_of_nonneg_left hm (show 0 ≤ 1 - ε by linarith)
    have he := mul_le_mul_of_nonneg_right hei.le
      (show 0 ≤ euclideanUnitBallVolume 3 * (ρ (φ i) * s) ^ 3 by positivity)
    nlinarith only [hmul, he]
  exact (not_lt_of_ge ((ENNReal.ofReal_le_ofReal hmodel).trans hback))
    (hbad (φ i) y (ρ (φ i) * s) hσlow hdist)

/-- The KL83.1 core for aligned compact three-manifolds at unit scale. -/
theorem unit_core_CX7 (w : ℝ) (hw : 0 < w) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ σ₀ : ℝ, 0 < σ₀ ∧
      ∀ (X : Type u) [MetricSpace X] [ChartedSpace ThreeSpace X]
        [IsManifold ThreeModel ∞ X] [CompactSpace X]
        (g : SmoothRiemannianMetric ThreeModel X),
        (∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)) →
        ∀ p : X,
        (∀ q ∈ riemannianBallOf g p 1, SectionalBoundedBelowAt g q (-1)) →
        ENNReal.ofReal w ≤ ballVolume g p 1 →
        ∃ (y : X) (σ : ℝ), σ₀ ≤ σ ∧ dist p y + 2 * σ ≤ 1 ∧
          ENNReal.ofReal ((1 - ε) * modelVolume (-1) 3 σ) ≤ ballVolume g y σ := by
  classical
  by_contra hneg
  push Not at hneg
  have hcounter := fun i : ℕ => hneg ((((i : ℝ) + 2)⁻¹) ^ 2) (by positivity)
  choose X mX cX sX kX g hmetric p hsec hvol hbad using hcounter
  exact no_bad_unit_sequence_CX7 (mX := mX) g hmetric p hw hε hε1 hsec hvol hbad

end GC.LongTime.Ch12
