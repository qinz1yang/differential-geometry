import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.KcoreVolumeChainRev_O38

/-!
# CH12-O38, group 2b: small-ball volume at `p` from the volume at the centre `w`

`ballVolume_small_of_centre_O38`: the A1 inequality at one slice — `vol B(w,h) ≥ κ₀` and the
chain `w → x → p` inside `B(x,(N+4)h)` give, for every `ℓ ∈ (0, h]`,
`vol B(p, ℓ) ≥ e^{-q(n-1)h} (ℓ/2h)^n c^{2(N+1)} κ₀` (Bishop–Gromov at `p` from `h` down to `ℓ`,
ball `B(p,h) ⊆ B(x,(N+4)h)`).
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

/-- **Small-ball volume at `p` from the centre volume at `w`** (A1 at one slice). -/
theorem ballVolume_small_of_centre_O38 (g : SmoothRiemannianMetric I M) (x : M) {q h : ℝ}
    (hq : 0 ≤ q) (hh : 0 < h) (N : ℕ)
    (hcpt : IsCompact (riemannianClosedBallOf g x ((N + 4) * h)))
    (hRic : ∀ z ∈ riemannianBallOf g x ((N + 4) * h), ∀ v : TangentSpace I z,
      -(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2) * g.inner z v v ≤
        ricciTensor (I := I) g z v v)
    {w p : M} (hw : riemannianEDistOf g x w < ENNReal.ofReal ((N + 1) * h))
    (hp : riemannianEDistOf g x p < ENNReal.ofReal ((N + 1) * h))
    {κ₀ : ℝ} (hκ₀ : ENNReal.ofReal κ₀ ≤ riemannianVolumeMeasure I M g (riemannianBallOf g w h))
    {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓh : ℓ ≤ h) :
    ENNReal.ofReal (Real.exp (-(q * ((Module.finrank ℝ E - 1 : ℕ) : ℝ) * h)) *
        (ℓ / (2 * h)) ^ Module.finrank ℝ E *
        (chainConst_O14 (Module.finrank ℝ E) q h ^ (2 * (N + 1)) * κ₀)) ≤
      riemannianVolumeMeasure I M g (riemannianBallOf g p ℓ) := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hin : ∀ z, riemannianEDistOf g p z ≤ ENNReal.ofReal h →
      riemannianEDistOf g x z < ENNReal.ofReal ((N + 4) * h) := by
    intro z hz
    calc riemannianEDistOf g x z ≤ riemannianEDistOf g x p + riemannianEDistOf g p z :=
          riemannianEDistOf_triangle _ _ _ _
      _ < ENNReal.ofReal ((N + 1) * h) + ENNReal.ofReal h :=
          ENNReal.add_lt_add_of_lt_of_le (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hz) hp hz
      _ = ENNReal.ofReal ((N + 2) * h) := by
          rw [← ENNReal.ofReal_add (by positivity) hh.le]; ring_nf
      _ ≤ ENNReal.ofReal ((N + 4) * h) := ENNReal.ofReal_le_ofReal (by nlinarith)
  have hr := ballVolume_ratio_of_isCompact_O14 g p hq hℓ hℓh
    (hcpt.of_isClosed_subset (isClosed_riemannianClosedBallOf_O14 g p h)
      (fun z hz => (hin z hz).le))
    (fun z hz v => hRic z (hin z hz.le) v)
  have ht := ballVolume_through_centre_O38 g x hq hh N hcpt hRic hw hp
  have ha : 0 ≤ Real.exp (-(q * ((Module.finrank ℝ E - 1 : ℕ) : ℝ) * h)) *
      (ℓ / (2 * h)) ^ Module.finrank ℝ E := by positivity
  have hc : 0 ≤ chainConst_O14 (Module.finrank ℝ E) q h ^ (2 * (N + 1)) :=
    pow_nonneg (chainConst_pos_O14 _ q h).le _
  rw [ENNReal.ofReal_mul ha, ENNReal.ofReal_mul hc]
  calc _ ≤ ENNReal.ofReal (Real.exp (-(q * ((Module.finrank ℝ E - 1 : ℕ) : ℝ) * h)) *
          (ℓ / (2 * h)) ^ Module.finrank ℝ E) *
        (ENNReal.ofReal (chainConst_O14 (Module.finrank ℝ E) q h ^ (2 * (N + 1))) *
          riemannianVolumeMeasure I M g (riemannianBallOf g w h)) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl hκ₀)
    _ ≤ ENNReal.ofReal (Real.exp (-(q * ((Module.finrank ℝ E - 1 : ℕ) : ℝ) * h)) *
          (ℓ / (2 * h)) ^ Module.finrank ℝ E) *
        riemannianVolumeMeasure I M g (riemannianBallOf g p h) := mul_le_mul' le_rfl ht
    _ ≤ _ := hr

end GC.LongTime.Ch12
