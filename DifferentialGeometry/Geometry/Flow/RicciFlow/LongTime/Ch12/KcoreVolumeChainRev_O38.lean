import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.KcanVolumeChain_O14

/-!
# CH12-O38, group 2a: the A1 chain kernel (Bishop–Gromov chain through a fixed centre)

The (a') A1 route of `[FROZEN] CH12-O31` KL70.2 sub-statements runs the Bishop–Gromov chain
`w_n → y_n → p` ONLY through balls of radius `≤ 3h` centred inside `B(y_n, (N+1)h)` (external
review R4 point 1: never a ball centred at `w_n` of radius `~ d(w_n, p)`).  Everything is local:
the Ricci lower bound and compactness are assumed on the single ball `B(x, (N+4)h)`, `x = y_n`.

* `ballVolume_chain_rev_O38`: the reverse chain `c^{k+1} vol B(y,h) ≤ vol B(x,h)` for
  `d(x,y) < (k+1)h` (O14's `ballVolume_chain_O14` is the forward direction).
* `ballVolume_through_centre_O38`: `c^{2(N+1)} vol B(w,h) ≤ vol B(p,h)` for `w, p ∈ B(x,(N+1)h)`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure

namespace GC.LongTime.Ch12

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]

/-- **Reverse Bishop–Gromov chain towards the centre.** -/
theorem ballVolume_chain_rev_O38 (g : SmoothRiemannianMetric I M) (x : M) {q h : ℝ}
    (hq : 0 ≤ q) (hh : 0 < h) (N : ℕ)
    (hcpt : IsCompact (riemannianClosedBallOf g x ((N + 4) * h)))
    (hRic : ∀ z ∈ riemannianBallOf g x ((N + 4) * h), ∀ v : TangentSpace I z,
      -(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2) * g.inner z v v ≤
        ricciTensor (I := I) g z v v) :
    ∀ k : ℕ, k ≤ N → ∀ y : M, riemannianEDistOf g x y < ENNReal.ofReal ((k + 1) * h) →
      ENNReal.ofReal (chainConst_O14 (Module.finrank ℝ E) q h ^ (k + 1)) *
          riemannianVolumeMeasure I M g (riemannianBallOf g y h) ≤
        riemannianVolumeMeasure I M g (riemannianBallOf g x h) := by
  have hc0 := (chainConst_pos_O14 (Module.finrank ℝ E) q h).le
  have hstep : ∀ u y : M, riemannianEDistOf g x y < ENNReal.ofReal ((N + 1) * h) →
      riemannianEDistOf g u y < ENNReal.ofReal (2 * h) →
      ENNReal.ofReal (chainConst_O14 (Module.finrank ℝ E) q h) *
          riemannianVolumeMeasure I M g (riemannianBallOf g u h) ≤
        riemannianVolumeMeasure I M g (riemannianBallOf g y h) := by
    intro u y hxy huy
    have hin : ∀ z, riemannianEDistOf g y z ≤ ENNReal.ofReal (3 * h) →
        riemannianEDistOf g x z < ENNReal.ofReal ((N + 4) * h) := by
      intro z hz
      calc riemannianEDistOf g x z ≤ riemannianEDistOf g x y + riemannianEDistOf g y z :=
            riemannianEDistOf_triangle _ _ _ _
        _ < ENNReal.ofReal ((N + 1) * h) + ENNReal.ofReal (3 * h) :=
            ENNReal.add_lt_add_of_lt_of_le (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hz) hxy hz
        _ = ENNReal.ofReal ((N + 4) * h) := by
            rw [← ENNReal.ofReal_add (by positivity) (by linarith)]; ring_nf
    refine ballVolume_step_O14 g hq hh huy ?_ ?_
    · refine hcpt.of_isClosed_subset (isClosed_riemannianClosedBallOf_O14 g y _) ?_
      intro z hz
      exact (hin z hz).le
    · intro z hz v
      exact hRic z (hin z (le_of_lt hz)) v
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hxx : riemannianEDistOf g x x < ENNReal.ofReal ((N + 1) * h) := by
    rw [riemannianEDistOf_self]; exact ENNReal.ofReal_pos.mpr (by positivity)
  intro k
  induction k with
  | zero =>
    intro _ y hy
    have hyx : riemannianEDistOf g y x < ENNReal.ofReal (2 * h) := by
      rw [riemannianEDistOf_comm]
      exact lt_of_lt_of_le hy (ENNReal.ofReal_le_ofReal (by push_cast; linarith))
    simpa using hstep y x hxx hyx
  | succ k ih =>
    intro hk y hy
    have hkN : k ≤ N := Nat.le_of_succ_le hk
    have hkR : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    obtain ⟨z, hxz, hzy⟩ := exists_intermediate_point_O14 g (c := (k + 1 / 2) * h)
      (D := ((k + 1 : ℕ) + 1) * h) (by positivity) (by push_cast; nlinarith) hy
    have hxz' : riemannianEDistOf g x z < ENNReal.ofReal ((k + 1) * h) :=
      lt_of_le_of_lt hxz ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by nlinarith))
    have hyz : riemannianEDistOf g y z < ENNReal.ofReal (2 * h) := by
      rw [riemannianEDistOf_comm]
      exact lt_of_lt_of_le hzy (ENNReal.ofReal_le_ofReal (by push_cast; nlinarith))
    have hNR : ((k + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hk
    have hz' : riemannianEDistOf g x z < ENNReal.ofReal ((N + 1) * h) :=
      lt_of_lt_of_le hxz' (ENNReal.ofReal_le_ofReal (by push_cast at hNR; nlinarith))
    have h1 := ih hkN z hxz'
    have h2 := hstep y z hz' hyz
    calc ENNReal.ofReal (chainConst_O14 (Module.finrank ℝ E) q h ^ (k + 1 + 1)) *
          riemannianVolumeMeasure I M g (riemannianBallOf g y h)
        = ENNReal.ofReal (chainConst_O14 (Module.finrank ℝ E) q h ^ (k + 1)) *
          (ENNReal.ofReal (chainConst_O14 (Module.finrank ℝ E) q h) *
            riemannianVolumeMeasure I M g (riemannianBallOf g y h)) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg hc0 _), pow_succ _ (k + 1)]
      _ ≤ ENNReal.ofReal (chainConst_O14 (Module.finrank ℝ E) q h ^ (k + 1)) *
          riemannianVolumeMeasure I M g (riemannianBallOf g z h) := mul_le_mul' le_rfl h2
      _ ≤ _ := h1

/-- **Volume transport through the centre** (`w → x → p`, all chain balls inside
`B(x, (N+4)h)`). -/
theorem ballVolume_through_centre_O38 (g : SmoothRiemannianMetric I M) (x : M) {q h : ℝ}
    (hq : 0 ≤ q) (hh : 0 < h) (N : ℕ)
    (hcpt : IsCompact (riemannianClosedBallOf g x ((N + 4) * h)))
    (hRic : ∀ z ∈ riemannianBallOf g x ((N + 4) * h), ∀ v : TangentSpace I z,
      -(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2) * g.inner z v v ≤
        ricciTensor (I := I) g z v v)
    {w p : M} (hw : riemannianEDistOf g x w < ENNReal.ofReal ((N + 1) * h))
    (hp : riemannianEDistOf g x p < ENNReal.ofReal ((N + 1) * h)) :
    ENNReal.ofReal (chainConst_O14 (Module.finrank ℝ E) q h ^ (2 * (N + 1))) *
        riemannianVolumeMeasure I M g (riemannianBallOf g w h) ≤
      riemannianVolumeMeasure I M g (riemannianBallOf g p h) := by
  have hc0 := (chainConst_pos_O14 (Module.finrank ℝ E) q h).le
  have h1 := ballVolume_chain_rev_O38 g x hq hh N hcpt hRic N le_rfl w hw
  have h2 := ballVolume_chain_O14 g x hq hh N hcpt hRic N le_rfl p hp
  calc ENNReal.ofReal (chainConst_O14 (Module.finrank ℝ E) q h ^ (2 * (N + 1))) *
        riemannianVolumeMeasure I M g (riemannianBallOf g w h)
      = ENNReal.ofReal (chainConst_O14 (Module.finrank ℝ E) q h ^ (N + 1)) *
        (ENNReal.ofReal (chainConst_O14 (Module.finrank ℝ E) q h ^ (N + 1)) *
          riemannianVolumeMeasure I M g (riemannianBallOf g w h)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg hc0 _), ← pow_add, two_mul]
    _ ≤ ENNReal.ofReal (chainConst_O14 (Module.finrank ℝ E) q h ^ (N + 1)) *
        riemannianVolumeMeasure I M g (riemannianBallOf g x h) := mul_le_mul' le_rfl h1
    _ ≤ _ := h2

end GC.LongTime.Ch12
