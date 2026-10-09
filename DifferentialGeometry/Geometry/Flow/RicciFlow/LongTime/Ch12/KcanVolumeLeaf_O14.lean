import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.KcanVolumeChain_O14

/-!
# CH12-O14, group 1b: the K-can volume leaf of the KL70.2 chain

`normalized_ball_volume_of_centre_O14` produces EXACTLY the normalized-ball volume interface
`hvol` consumed by the local KL70.2 chain (`MicroGlueLocalCone.lean`, the `have hvol` after
`normalized_inner_ball_volume_local_O3`):
`∀ r < R < rho, ∀ J ≥ 0, ∃ a κ' > 0, r + a ≤ R, a⁴J² ≤ 1, eventually ∀ y ∈ B̄(x n, r),
vol B(y, a) ≥ κ' a³` (all in the normalized metrics `G n`),
from (i) a volume lower bound at the CENTRE only, at normalized scales `≤ a₀` (the canonical
witness at the blow-up centre: `exists_ball_volume_of_spatialCanonicalWitness`), and (ii) compact
closed balls and a Ricci lower bound on every normalized ball of radius `< rho` (the scalar buffer
bound + pinching inside the escape radius).  No volume test away from the centre, no κ(t), no test
ball: this is the volume leaf of the K-can route (`[FROZEN v2] CH12-O14`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped ContDiff ENNReal Manifold

namespace GC.LongTime.Ch12

open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- **K-can volume leaf.** Centre volume + local geometry inside the escape radius ⇒ the
normalized-ball volume interface of the KL70.2 chain. -/
theorem normalized_ball_volume_of_centre_O14
    {M : ℕ → Type*} [∀ n, TopologicalSpace (M n)] [∀ n, ChartedSpace H (M n)]
    [∀ n, IsManifold I ∞ (M n)] [∀ n, T2Space (M n)] [∀ n, T2Space (TangentBundle I (M n))]
    [∀ n, SigmaCompactSpace (M n)]
    (G : ∀ n, SmoothRiemannianMetric I (M n)) (x : ∀ n, M n) {rho κ a₀ : ℝ}
    (hκ : 0 < κ) (ha₀ : 0 < a₀)
    (hvx : ∀ᶠ n in atTop, ∀ b : ℝ, 0 < b → b ≤ a₀ →
      ENNReal.ofReal (κ * b ^ 3) ≤
        riemannianVolumeMeasure I (M n) (G n) (riemannianBallOf (G n) (x n) b))
    (hgeo : ∀ R : ℝ, R < rho → ∃ q : ℝ, 0 ≤ q ∧ ∀ᶠ n in atTop,
      IsCompact (riemannianClosedBallOf (G n) (x n) R) ∧
      ∀ z ∈ riemannianBallOf (G n) (x n) R, ∀ v : TangentSpace I z,
        -(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2) * (G n).inner z v v ≤
          ricciTensor (I := I) (G n) z v v) :
    ∀ r R : ℝ, 0 < r → r < R → R < rho → ∀ J : ℝ, 0 ≤ J →
      ∃ a κ' : ℝ, 0 < a ∧ 0 < κ' ∧ r + a ≤ R ∧ a ^ 4 * J ^ 2 ≤ 1 ∧
      ∀ᶠ n in atTop, ∀ y ∈ riemannianClosedBallOf (G n) (x n) r,
        ENNReal.ofReal (κ' * a ^ 3) ≤
          riemannianVolumeMeasure I (M n) (G n) (riemannianBallOf (G n) y a) := by
  intro r R hr hrR hRrho J hJ
  set a : ℝ := min (R - r) (min 1 (1 / (J + 1))) with hadef
  have ha : 0 < a := lt_min (sub_pos.mpr hrR) (lt_min one_pos (by positivity))
  have haR : a ≤ R - r := min_le_left _ _
  have ha1 : a ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have haJ' : a ≤ 1 / (J + 1) := (min_le_right _ _).trans (min_le_right _ _)
  have haJ : a * (J + 1) ≤ 1 := (le_div_iff₀ (by positivity)).mp haJ'
  have haJ2 : a * J ≤ 1 := by nlinarith
  have ha4 : a ^ 4 * J ^ 2 ≤ 1 := by
    have h0 : 0 ≤ a * J := mul_nonneg ha.le hJ
    have h1 : (a * J) ^ 2 ≤ 1 := by nlinarith
    have h2 : a ^ 2 ≤ 1 := by nlinarith
    calc a ^ 4 * J ^ 2 = a ^ 2 * (a * J) ^ 2 := by ring
      _ ≤ 1 * 1 := mul_le_mul h2 h1 (by positivity) zero_le_one
      _ = 1 := by ring
  set h : ℝ := min a (min a₀ ((R - r) / 5)) with hhdef
  have hh : 0 < h := lt_min ha (lt_min ha₀ (by linarith))
  have hha : h ≤ a := min_le_left _ _
  have hha₀ : h ≤ a₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hh5 : h ≤ (R - r) / 5 := (min_le_right _ _).trans (min_le_right _ _)
  set N : ℕ := ⌈r / h⌉₊ with hNdef
  have hN1 : r ≤ N * h := by
    have := Nat.le_ceil (r / h)
    rwa [div_le_iff₀ hh] at this
  have hN2 : (N : ℝ) * h < r + h := by
    have := Nat.ceil_lt_add_one (div_nonneg hr.le hh.le)
    rw [← hNdef] at this
    have := mul_lt_mul_of_pos_right this hh
    rwa [add_mul, div_mul_cancel₀ _ hh.ne', one_mul] at this
  have hNR : ((N : ℝ) + 4) * h ≤ R := by nlinarith
  obtain ⟨q, hq, hgeoR⟩ := hgeo R hRrho
  set c : ℝ := chainConst_O14 (Module.finrank ℝ E) q h with hcdef
  have hc : 0 < c := chainConst_pos_O14 _ _ _
  refine ⟨a, c ^ (N + 1) * κ * (h / a) ^ 3, ha, by positivity, by linarith, ha4, ?_⟩
  filter_upwards [hvx, hgeoR] with n hvxn hgeon
  obtain ⟨hcpt, hRic⟩ := hgeon
  intro y hy
  have hcpt' : IsCompact (riemannianClosedBallOf (G n) (x n) ((N + 4) * h)) :=
    hcpt.of_isClosed_subset (isClosed_riemannianClosedBallOf_O14 (G n) (x n) _)
      (riemannianClosedBallOf_mono (G n) (x n) hNR)
  have hRic' : ∀ z ∈ riemannianBallOf (G n) (x n) ((N + 4) * h), ∀ v : TangentSpace I z,
      -(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2) * (G n).inner z v v ≤
        ricciTensor (I := I) (G n) z v v :=
    fun z hz v => hRic z (riemannianBallOf_mono (G n) (x n) hNR hz) v
  have hyN : riemannianEDistOf (G n) (x n) y < ENNReal.ofReal ((N + 1) * h) :=
    lt_of_le_of_lt hy ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by nlinarith))
  have hch := ballVolume_chain_O14 (G n) (x n) hq hh N hcpt' hRic' N le_rfl y hyN
  have hxv := hvxn h hh hha₀
  calc ENNReal.ofReal (c ^ (N + 1) * κ * (h / a) ^ 3 * a ^ 3)
      = ENNReal.ofReal (c ^ (N + 1)) * ENNReal.ofReal (κ * h ^ 3) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
    _ ≤ ENNReal.ofReal (c ^ (N + 1)) *
          riemannianVolumeMeasure I (M n) (G n) (riemannianBallOf (G n) (x n) h) :=
        mul_le_mul' le_rfl hxv
    _ ≤ riemannianVolumeMeasure I (M n) (G n) (riemannianBallOf (G n) y h) := hch
    _ ≤ riemannianVolumeMeasure I (M n) (G n) (riemannianBallOf (G n) y a) :=
        measure_mono (riemannianBallOf_mono (G n) y hha)

end GC.LongTime.Ch12
