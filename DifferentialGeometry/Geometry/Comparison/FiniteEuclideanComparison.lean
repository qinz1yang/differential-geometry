import DifferentialGeometry.Geometry.Comparison.NonnegativeSegmentLog
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.Pseudo.Pi

set_option autoImplicit false

open Set Metric Filter Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem exists_finite_euclidean_comparison_of_dense_tangent_isometries
    {X : Type*} [MetricSpace X] [∀ q : X, HasAnglesAt q]
    (hcomp : fourPointComparison 0 (univ : Set X))
    (hsegments : ∀ x y : X, ∃ γ : Icc (0 : ℝ) (dist x y) → X,
      Isometry γ ∧ γ ⟨0, le_rfl, dist_nonneg⟩ = x ∧
        γ ⟨dist x y, dist_nonneg, le_rfl⟩ = y)
    {m : ℕ} {S : Set X} (hS : Dense S)
    (hregular : ∀ q ∈ S, ∃ e : TangentCone q ≃ᵢ EuclideanSpace ℝ (Fin m),
      e EuclideanCone.tip = 0)
    {ι : Type*} [Finite ι] (p : X) (a : ι → X) :
    ∃ v : ι → EuclideanSpace ℝ (Fin m),
      (∀ i, ‖v i‖ = dist p (a i)) ∧ ∀ i j, dist (a i) (a j) ≤ dist (v i) (v j) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let ε : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hεpos (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  have hεone (j : ℕ) : ε j ≤ 1 := by
    dsimp [ε]
    exact (div_le_one (by positivity)).mpr (by have := Nat.cast_nonneg (α := ℝ) j; linarith)
  have hnear (j : ℕ) : ∃ q ∈ S, q ∈ ball p (ε j) :=
    hS.exists_mem_open isOpen_ball ⟨p, mem_ball_self (hεpos j)⟩
  choose q hqS hqball using hnear
  have hqt : Tendsto q atTop (𝓝 p) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero (fun _ => dist_nonneg) (fun j => (hqball j).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hconfiguration (j : ℕ) : ∃ v : ι → EuclideanSpace ℝ (Fin m),
      (∀ i, ‖v i‖ = dist (q j) (a i)) ∧
      ∀ i k, dist (a i) (a k) ≤ dist (v i) (v k) := by
    obtain ⟨e, he⟩ := hregular (q j) (hqS j)
    choose γ hγ hγ0 hγend using fun i => hsegments (q j) (a i)
    refine ⟨fun i => e (segmentLog (a i) (γ i) (hγ i) (hγ0 i)), ?_, ?_⟩
    · intro i
      rw [← dist_zero_right, ← he, e.dist_eq, EuclideanCone.dist_tip, segmentLog_radius]
    · intro i k
      rw [e.dist_eq]
      exact dist_le_dist_segmentLog_of_fourPointComparison_zero hcomp
        (a i) (a k) (γ i) (γ k) (hγ i) (hγ k) (hγ0 i) (hγ0 k) (hγend i) (hγend k)
  choose v hvnorm hvdist using hconfiguration
  have hbounded (j : ℕ) (i : ι) : ‖v j i‖ ≤ dist p (a i) + 1 := by
    rw [hvnorm]
    have htri := dist_triangle (q j) p (a i)
    have hq : dist (q j) p < ε j := hqball j
    linarith [hεone j]
  let A (j : ℕ) : ∀ i : ι, closedBall (0 : EuclideanSpace ℝ (Fin m)) (dist p (a i) + 1) :=
    fun i => ⟨v j i, by simpa only [mem_closedBall, dist_zero_right] using hbounded j i⟩
  obtain ⟨w, φ, hφ, hw⟩ := CompactSpace.tendsto_subseq A
  have hlim (i : ι) : Tendsto (fun j => v (φ j) i) atTop (𝓝 (w i).val) :=
    continuous_subtype_val.continuousAt.tendsto.comp (hw.apply_nhds i)
  refine ⟨fun i => (w i).val, ?_, ?_⟩
  · intro i
    apply tendsto_nhds_unique (hlim i).norm
    have hd := (hqt.comp hφ.tendsto_atTop).dist (tendsto_const_nhds (x := a i))
    exact hd.congr' (Eventually.of_forall fun j => (hvnorm (φ j) i).symm)
  · intro i k
    exact ge_of_tendsto ((hlim i).dist (hlim k))
      (Eventually.of_forall fun j => hvdist (φ j) i k)

end DifferentialGeometry.Geometry.Comparison.Toponogov
