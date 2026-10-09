import DifferentialGeometry.Geometry.Comparison.CheegerGromovTaylor.InjectivityRadius.UniformLocalVolume
import DifferentialGeometry.Geometry.Comparison.Volume.BishopGromovLocal
import DifferentialGeometry.Geometry.Comparison.BonnetMyers.RicciLower
import DifferentialGeometry.Geometry.Metric.Distance.InducedMetricSpace
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Bounds.InjectivityRadius
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.MetricSeq

/-!
# A uniform injectivity radius from curvature, diameter and volume bounds

On a fixed closed connected manifold `M`, consider metrics `gSeq n` with a common curvature bound
`|Rm| ≤ B`, a common diameter bound `d` and a common lower bound `v > 0` for the total volume. Then
there is ONE radius `ι > 0`, depending only on `dim M`, `B`, `d`, `v`, below the injectivity radius
of every `gSeq n` at every point (`exists_uniform_hasInjRadiusAt_pointedMetricSeq`). The chain is

* Ricci lower bound `Ric ≥ -(dim M - 1) q² g` with the explicit `q = (dim M)² B + 1`
  (`ricciBoundedBelow_of_sqrt_normSq_rm04_le`, from `ricciLower_of_rm`);
* local Bishop–Gromov (`modelVolume_cross_of_ricciBoundedBelowOn`) between the small ball and the
  ball of radius `max d 0 + 1`, which is the whole manifold: a common lower bound for the volume of
  every small ball;
* the Cheeger–Gromov–Taylor estimate at the scale `R` chosen BEFORE the metrics
  (`exists_local_volume_inj_radius_scale`), with the explicit real `cgtVolumeInjRadius`.

The metric-space instances of each `gSeq n` are the induced ones of `InducedMetricSpace.lean`;
completeness comes from compactness, never from the curvature hypothesis.
-/

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Bundle Set Manifold MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff _root_.Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance uniformInjMeasurableE : MeasurableSpace E := borel E
private local instance uniformInjBorelE : BorelSpace E := ⟨rfl⟩

omit [SigmaCompactSpace M] in
/-- A global bound `|Rm| ≤ B` gives the Ricci lower bound `Ric ≥ -(n - 1) q² g` with the explicit
`q = n² B + 1`, `n = dim M`, in every dimension (for `n = 1` the Ricci tensor vanishes). -/
theorem ricciBoundedBelow_of_sqrt_normSq_rm04_le (g : SmoothRiemannianMetric I M) {B : ℝ}
    (hB : 0 ≤ B)
    (hRm : ∀ x : M, Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 4
      (metricRm04At (I := I) (M := M) g x)) ≤ B) :
    RicciBoundedBelow (I := I) g
      (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * ((Module.finrank ℝ E : ℝ) ^ 2 * B + 1) ^ 2)) := by
  by_cases hdim : Module.finrank ℝ E = 1
  · have h0 := ricciLower_dim1 (I := I) g hdim
    intro x v
    have hx := h0 x v
    simp only [hdim, Nat.sub_self, Nat.cast_zero, zero_mul, neg_zero] at hx ⊢
    exact hx
  · have hn2 : 2 ≤ Module.finrank ℝ E := by
      have := Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))
      omega
    have hric := ricciLower_of_rm (I := I) g hRm
    intro x v
    have hbase := hric x v
    have hcoef1 : (1 : ℝ) ≤ ((Module.finrank ℝ E - 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 1 ≤ Module.finrank ℝ E - 1)
    have hnB : 0 ≤ (Module.finrank ℝ E : ℝ) ^ 2 * B := by positivity
    have hsq : (Module.finrank ℝ E : ℝ) ^ 2 * B ≤
        ((Module.finrank ℝ E - 1 : ℕ) : ℝ) * ((Module.finrank ℝ E : ℝ) ^ 2 * B + 1) ^ 2 := by
      nlinarith
    have hinner : 0 ≤ g.inner x v v := by
      rcases eq_or_ne v 0 with hv | hv
      · subst v
        simp
      · exact (g.pos x v hv).le
    exact le_trans (mul_le_mul_of_nonneg_right (neg_le_neg hsq) hinner) hbase

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- **Uniform injectivity radius.** On a closed connected manifold, curvature `|Rm| ≤ B`, diameter
`≤ d` and total volume `≥ v > 0` give one injectivity-radius lower bound `ι > 0` for every metric
of a sequence with these bounds, at every basepoint. -/
theorem exists_uniform_hasInjRadiusAt_pointedMetricSeq [CompactSpace M] [ConnectedSpace M]
    {B d v : ℝ} (hB : 0 < B) (hv : 0 < v) :
    ∃ ι : ℝ, 0 < ι ∧ ∀ (p : M) (gSeq : ℕ → SmoothRiemannianMetric I M),
      (∀ n x, Real.sqrt (Tensor0SBundle.normSq0S (gSeq n) x 4
        (metricRm04 (gSeq n) x)) ≤ B) →
      (∀ n x y, riemannianEDistOf (gSeq n) x y ≤ ENNReal.ofReal d) →
      (∀ n, ENNReal.ofReal v ≤ riemannianVolumeMeasure I M (gSeq n) Set.univ) →
      ∀ n, HasInjRadiusAt (I := I) ((pointedMetricSeq p gSeq).obj n) p ι := by
  classical
  let q : ℝ := (Module.finrank ℝ E : ℝ) ^ 2 * B + 1
  have hq : 0 ≤ q := by positivity
  obtain ⟨R, hR, hR1, -, hCGT⟩ :=
    exists_local_volume_inj_radius_scale (I := I) (M := M) (ρ := 1) (K := B) one_pos hB
  let D : ℝ := max d 0 + 1
  have hD : 0 < D := by positivity
  have hsD : R / 8 ≤ D := by
    have := le_max_right d 0
    dsimp only [D]
    linarith
  let K : ℝ := -q ^ 2
  have hKnot : ¬ 0 < K := by
    dsimp only [K]
    nlinarith [sq_nonneg q]
  have hn1 : 1 ≤ Module.finrank ℝ E := Nat.one_le_iff_ne_zero.2 (NeZero.ne _)
  have hmD : 0 < modelVolume K (Module.finrank ℝ E) D :=
    modelVolume_pos hn1 hD ⟨hD.le, fun hK => absurd hK hKnot⟩
  have hms : 0 < modelVolume K (Module.finrank ℝ E) (R / 8) :=
    modelVolume_pos hn1 (by positivity) ⟨by positivity, fun hK => absurd hK hKnot⟩
  let vs : ℝ := v * modelVolume K (Module.finrank ℝ E) (R / 8) /
    modelVolume K (Module.finrank ℝ E) D
  have hvs : 0 < vs := by positivity
  refine ⟨cgtVolumeInjRadius E q R vs, cgtVolumeInjRadius_pos hq hR hvs, ?_⟩
  intro p gSeq hRm hdiam hvol n
  refine ⟨cgtVolumeInjRadius_pos hq hR hvs, fun hcomplete => ?_⟩
  let g : SmoothRiemannianMetric I M := gSeq n
  have : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : RiemannianBundle (fun y : M => TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  let : EMetricSpace M := inducedEMetricSpace g
  have : IsRiemannianManifold I M := inducedEMetricSpace_isRiemannianManifold g
  have : IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y) :=
    isContinuousRiemannianBundle_of_smoothRiemannianMetric g
  have : CompleteSpace M := complete_of_compact
  have hEnorm : IsMetricNorm (I := I) g := isMetricNorm_of_smoothRiemannianMetric g
  have hRmAt : ∀ y : M, Real.sqrt (Tensor0SBundle.normSq0S (I := I) g y 4
      (metricRm04At (I := I) g y)) ≤ B := by
    intro y
    rw [← metricRm04_apply]
    exact hRm n y
  have hRic := ricciBoundedBelow_of_sqrt_normSq_rm04_le (I := I) g hB.le hRmAt
  have hRicOn : ricciBoundedBelowOn (I := I) g
      {y : M | riemannianEDist I p y < ENNReal.ofReal (D + 1)}
      (((Module.finrank ℝ E - 1 : ℕ) : ℝ) * K) := by
    intro y _ w
    have h := hRic y w
    have hK : ((Module.finrank ℝ E - 1 : ℕ) : ℝ) * K =
        -(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2) := by
      dsimp only [K]
      ring
    rw [hK]
    exact h
  have hBG := modelVolume_cross_of_ricciBoundedBelowOn (I := I) g hEnorm p
    (K := K) (s := R / 8) (R := D) (R₀ := D + 1) (by positivity) hsD
    (fun hK => absurd hK hKnot) (by linarith) hRicOn
  have hball : {y : M | riemannianEDist I p y < ENNReal.ofReal D} = Set.univ := by
    ext y
    simp only [Set.mem_univ, iff_true]
    change riemannianEDist I p y < ENNReal.ofReal D
    rw [← riemannianEDistOf_eq_riemannianEDist (I := I) g hEnorm p y]
    refine (hdiam n p y).trans_lt ((ENNReal.ofReal_lt_ofReal_iff hD).2 ?_)
    have := le_max_left d 0
    dsimp only [D]
    linarith
  rw [hball] at hBG
  have hsmall : ENNReal.ofReal vs ≤ riemannianVolumeMeasure (I := I) (M := M) g
      {y : M | riemannianEDist I p y < ENNReal.ofReal (R / 8)} := by
    have hmul : ENNReal.ofReal (modelVolume K (Module.finrank ℝ E) D) * ENNReal.ofReal vs =
        ENNReal.ofReal v * ENNReal.ofReal (modelVolume K (Module.finrank ℝ E) (R / 8)) := by
      rw [← ENNReal.ofReal_mul hmD.le, ← ENNReal.ofReal_mul hv.le]
      congr 1
      dsimp only [vs]
      field_simp
    rw [← ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.2 hmD).ne' ENNReal.ofReal_ne_top, hmul]
    refine le_trans ?_ hBG
    gcongr
    exact hvol n
  have hcgt := hCGT g hEnorm q hq hRic p (ENNReal.ofReal vs)
    (fun y _ => hRmAt y) hsmall
  have hmain := (ofReal_cgtVolumeInjRadius_le (E := E) hq hR).trans hcgt
  exact hmain
end DifferentialGeometry.CheegerGromovCompactness
