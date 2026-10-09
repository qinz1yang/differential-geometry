import DifferentialGeometry.Geometry.Collapse.CircleFiberLocalModel
import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottApproximation

/-!
# LFR07: a supplied circle packet at a two-stratum point (from supplied rank-two coordinates)

Blueprint 207A, LFR07 (`cor:collapse-rank-two-circle-packet`, A:25322–25357). The row's proof applies
LFR06 (rank-two adapted coordinates, not in the tree) and then the arithmetic proved here.

* `circlePacket_enclosures`: Pythagoras in the `ℓ²` product `ℝ² × Y` turns `|η − Φ| < 1/10`, distortion
  `≤ β ≤ 1/200` and the tested residual bound `d(v, a) < 1` into the two LC83 enclosures.
* `exists_cutoff_of_enclosure`: the cutoff `Φ_{a,b}(|η|)`, extended by zero, is smooth with compact
  support (any radii `0 < a < b ≤ r`).
* `circlePacket_of_rank_two_coordinates` (LFR07 for supplied coordinates): enclosures, the LC83 packet
  (`circleFiber_local_model`) and the cutoff `Φ_{8,9}(|η|)`.

Missing for the full row: LFR06's producer of `η` (needs LC78 with inner radius 3 on a 2-splitting and
a mixed-anchor Gram estimate, `build-logs/resume/request-LFR06-to-X83.md`), and the `S¹`
identification of the fibre (lane W4-FCb).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle
open scoped ContDiff Manifold Topology NNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Topology
open GC.MetricGeometry

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

private theorem dist_withLp_two_prod_eq {α β : Type*} [PseudoMetricSpace α]
    [PseudoMetricSpace β] (f g : WithLp 2 (α × β)) :
    dist f g = Real.sqrt (dist f.fst g.fst ^ 2 + dist f.snd g.snd ^ 2) := by
  rw [WithLp.prod_dist_eq_add (by norm_num), Real.sqrt_eq_rpow]
  norm_num

/-- **LFR07, enclosure arithmetic.** Let `F` be a pointed `β`-approximation of `(M, q)` by
`ℝ² × Y` with `β ≤ 1/200`, whose residual coordinate stays within `1` of `a` on `B(q, 200)`, and let
`η` be within `1/10` of the `ℝ²`-coordinate there. Then `η⁻¹ B(0, 100) ⊆ B(q, 102)` and
`η⁻¹(0) ⊆ B(q, 2)` on `B(q, 200)` (the two LC83 enclosures, by Pythagoras). -/
theorem circlePacket_enclosures {M Y : Type*} [MetricSpace M] [MetricSpace Y] {q : M} {a : Y}
    {β : ℝ} (F : KleinerLottApprox q (WithLp.toLp 2 ((0 : ℝ²), a)) β) (hβ : β ≤ 1 / 200)
    (hres : ∀ x ∈ ball q 200, dist (F.toFun x).snd a < 1) {η : M → ℝ²}
    (hclose : ∀ x ∈ ball q 200, ‖η x - (F.toFun x).fst‖ < 1 / 10) :
    (∀ x ∈ ball q 200, ‖η x‖ < 100 → x ∈ ball q 102) ∧
      (∀ x ∈ ball q 200, η x = 0 → x ∈ ball q 2) := by
  have hβpos := F.error_pos
  have hball : ∀ x ∈ ball q 200, x ∈ ball q β⁻¹ := by
    intro x hx
    have h200 : (200 : ℝ) ≤ β⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) hβpos]
      linarith
    exact ball_subset_ball h200 hx
  have hq : q ∈ ball q β⁻¹ := mem_ball_self (inv_pos.mpr hβpos)
  have key : ∀ x ∈ ball q 200, ∀ s c : ℝ, 0 < c → ‖η x‖ + 1 / 10 ≤ s → s ^ 2 + 1 ≤ c ^ 2 →
      dist x q < c + 1 / 200 := by
    intro x hx s c hc hs hsc
    have hdist := F.distortion x (hball x hx) q hq
    rw [F.basepoint, dist_withLp_two_prod_eq] at hdist
    simp only [WithLp.toLp_fst, WithLp.toLp_snd, dist_zero_right] at hdist
    have hfst : ‖(F.toFun x).fst‖ < s := by
      have h1 := norm_sub_norm_le (F.toFun x).fst (η x)
      rw [norm_sub_rev] at h1
      have h2 := hclose x hx
      linarith
    have hsnd := hres x hx
    have hsq : ‖(F.toFun x).fst‖ ^ 2 + dist (F.toFun x).snd a ^ 2 < c ^ 2 := by
      have h0 : 0 ≤ ‖(F.toFun x).fst‖ := norm_nonneg _
      have h0' : 0 ≤ dist (F.toFun x).snd a := dist_nonneg
      nlinarith
    have hsqrt := (Real.sqrt_lt' hc).mpr hsq
    have habs := (abs_le.mp hdist).1
    linarith
  refine ⟨fun x hx h100 => ?_, fun x hx h0 => ?_⟩
  · have := key x hx (100 + 1 / 10) 101 (by norm_num) (by linarith) (by norm_num)
    exact mem_ball.mpr (by linarith)
  · have := key x hx (1 / 10) (3 / 2) (by norm_num) (by rw [h0, norm_zero]; norm_num)
      (by norm_num)
    exact mem_ball.mpr (by linarith)


/-- **LFR07, the cutoff.** If `η` is smooth on an open `W` and `{x ∈ W | ‖η x‖ < r}` lies in a compact
`K ⊆ W`, then for `0 < a < b ≤ r` the function `ψ(η)` with a smooth radial profile `ψ = 1` on
`B̄(0, a)`, `ψ = 0` off `B(0, b)`, extended by zero off `W`, is smooth with compact support. -/
theorem exists_cutoff_of_enclosure {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [T2Space M]
    [ChartedSpace H M] {W : Set M} (hW : IsOpen W) {η : M → ℝ²}
    (hη : ContMDiffOn I 𝓘(ℝ, ℝ²) ∞ η W) {r : ℝ} {K : Set M} (hK : IsCompact K) (hKW : K ⊆ W)
    (hencl : ∀ x ∈ W, ‖η x‖ < r → x ∈ K) {a b : ℝ} (ha : 0 < a) (hab : a < b) (hbr : b ≤ r) :
    ∃ ζ : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ ζ ∧ HasCompactSupport ζ ∧ (∀ x, ζ x ∈ Icc 0 1) ∧
      (∀ x ∈ W, ‖η x‖ ≤ a → ζ x = 1) ∧ (∀ x, ζ x ≠ 0 → x ∈ W ∧ ‖η x‖ < b) := by
  classical
  let ψ : ContDiffBump (0 : ℝ²) := { rIn := a, rOut := b, rIn_pos := ha, rIn_lt_rOut := hab }
  let ζ : M → ℝ := fun x => if x ∈ W then ψ (η x) else 0
  let T : Set M := K ∩ η ⁻¹' closedBall 0 b
  have hT : IsClosed T :=
    (hη.continuousOn.mono hKW).preimage_isClosed_of_isClosed hK.isClosed isClosed_closedBall
  have hsupp : ∀ x, ζ x ≠ 0 → x ∈ W ∧ ‖η x‖ < b := by
    intro x hx
    by_cases hxW : x ∈ W
    · refine ⟨hxW, ?_⟩
      have hne : ψ (η x) ≠ 0 := by simpa [ζ, hxW] using hx
      have hmem : η x ∈ support ψ := hne
      rw [ψ.support_eq, mem_ball, dist_zero_right] at hmem
      exact hmem
    · exact absurd (by simp [ζ, hxW]) hx
  have hsuppT : support ζ ⊆ T := by
    intro x hx
    obtain ⟨hxW, hxb⟩ := hsupp x hx
    exact ⟨hencl x hxW (hxb.trans_le hbr), by
      rw [mem_preimage, mem_closedBall, dist_zero_right]; exact hxb.le⟩
  have htsupp : tsupport ζ ⊆ T := closure_minimal hsuppT hT
  refine ⟨ζ, ?_, ?_, ?_, ?_, hsupp⟩
  · intro x
    by_cases hxW : x ∈ W
    · have hcomp : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun y => ψ (η y)) x :=
        (ψ.contDiff.contMDiff.contMDiffAt).comp x ((hη x hxW).contMDiffAt (hW.mem_nhds hxW))
      refine hcomp.congr_of_eventuallyEq ?_
      filter_upwards [hW.mem_nhds hxW] with y hy
      simp [ζ, hy]
    · have hxT : x ∉ T := fun h => hxW (hKW h.1)
      refine (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [hT.isOpen_compl.mem_nhds hxT] with y hy
      by_contra hne
      exact hy (hsuppT hne)
  · exact hK.of_isClosed_subset (isClosed_tsupport ζ) (htsupp.trans inter_subset_left)
  · intro x
    by_cases hxW : x ∈ W
    · simp only [ζ, hxW, ite_true]
      exact ⟨ψ.nonneg, ψ.le_one⟩
    · simp [ζ, hxW]
  · intro x hxW hxa
    simp only [ζ, hxW, ite_true]
    exact ψ.one_of_mem_closedBall (by rwa [mem_closedBall, dist_zero_right])


section Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- **LFR07** from supplied rank-two coordinates. On a complete Riemannian manifold let
`F : (M, q) → ℝ² × Y` be a pointed `β`-approximation, `β ≤ 1/200`, whose residual coordinate stays
within `1` of `a` on `B(q, 200)` (the tested residual estimate of LC83, e.g. LPA03's
`exists_simultaneous_circle_residual_threshold`), and let `η : B(q, 200) → ℝ²` be smooth of rank two,
`2`-Lipschitz, `η(q) = 0`, within `1/10` of the `ℝ²`-coordinate of `F` (LFR06's output after the fixed
rescaling). Then both LC83 enclosures hold, `η` gives the LC83 packet over `B(0, 100)`, and the
cutoff `Φ_{8,9}(|η|)` is a smooth compactly supported function on `M`. -/
theorem circlePacket_of_rank_two_coordinates (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {Y : Type*} [MetricSpace Y] {q : M} {a : Y} {β : ℝ}
    (F : KleinerLottApprox q (WithLp.toLp 2 ((0 : ℝ²), a)) β) (hβ : β ≤ 1 / 200)
    (hres : ∀ x ∈ ball q 200, dist (F.toFun x).snd a < 1) {η : M → ℝ²}
    (hη : ContMDiffOn I 𝓘(ℝ, ℝ²) ∞ η (ball q 200))
    (hrank : ∀ x ∈ ball q 200, Surjective (mfderiv I 𝓘(ℝ, ℝ²) η x))
    (hlip : LipschitzOnWith 2 η (ball q 200)) (hq : η q = 0)
    (hclose : ∀ x ∈ ball q 200, ‖η x - (F.toFun x).fst‖ < 1 / 10) :
    (∀ x ∈ ball q 200, ‖η x‖ < 100 → x ∈ ball q 102) ∧
      (∀ x ∈ ball q 200, η x = 0 → x ∈ ball q 2) ∧
      (let f := diskPreimageMap (ball q 200) isOpen_ball η hη.continuousOn 100
      ContMDiff I 𝓘(ℝ, ℝ²) ∞ f ∧ (∀ x, Surjective (mfderiv I 𝓘(ℝ, ℝ²) f x)) ∧ IsProperMap f ∧
        Surjective f ∧ (∀ z, IsCompact (f ⁻¹' {z}) ∧ IsConnected (f ⁻¹' {z})) ∧
        ∀ R (hR : 0 < R) (hRr : R < 100),
          let y₀ : planeBallOpens 100 := ⟨0, zero_mem_planeBallOpens (hR.trans hRr)⟩
          let _ := regularFiberChartedSpace f y₀ (contMDiff_diskPreimageMap isOpen_ball hη 100)
            (fun x _ ↦ surjective_mfderiv_diskPreimageMap isOpen_ball hη hrank 100 x)
          let U : TopologicalSpace.Opens
              (diskPreimageOpens (ball q 200) isOpen_ball η hη.continuousOn 100) :=
            ⟨f ⁻¹' planeBallInner 100 R,
              (planeBallInner 100 R).isOpen.preimage (continuous_diskPreimageMap isOpen_ball _ 100)⟩
          ∃ (hy : y₀ ∈ planeBallInner 100 R) (Θ : Diffeomorph
              (𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ²) → ℝ).prod 𝓘(ℝ, ℝ²)) I
              ({x // f x = y₀} × planeBallInner 100 R) U ∞),
            (∀ q, f (Θ q).1 = q.2.1) ∧ (∀ x, (Θ (x, ⟨y₀, hy⟩)).1 = x.1)) ∧
      ∃ ζ : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ ζ ∧ HasCompactSupport ζ ∧ (∀ x, ζ x ∈ Icc 0 1) ∧
        (∀ x ∈ ball q 200, ‖η x‖ ≤ 8 → ζ x = 1) ∧
        (∀ x, ζ x ≠ 0 → x ∈ ball q 200 ∧ ‖η x‖ < 9) := by
  obtain ⟨h102, h2⟩ := circlePacket_enclosures F hβ hres hclose
  exact ⟨h102, h2, circleFiber_local_model g hEnorm hη hrank hlip hq h102 h2,
    exists_cutoff_of_enclosure isOpen_ball hη (soul_isCompact_closedBall g hEnorm q 102)
      (closedBall_subset_ball (by norm_num))
      (fun x hx hx100 => ball_subset_closedBall (h102 x hx hx100)) (by norm_num) (by norm_num)
      (by norm_num : (9 : ℝ) ≤ 100)⟩

end Riemannian

end DifferentialGeometry.Geometry.Collapse
