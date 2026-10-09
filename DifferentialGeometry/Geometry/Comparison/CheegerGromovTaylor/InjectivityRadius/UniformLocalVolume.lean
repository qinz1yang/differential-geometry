import DifferentialGeometry.Geometry.Comparison.CheegerGromovTaylor.InjectivityRadius.LocalVolume

/-!
# A Cheeger–Gromov–Taylor scale chosen before the metric

`exists_uniform_local_volume_inj_radius` (`LocalVolume.lean`) quantifies the scale `R` after the
metric `g`. Its proof chooses `R = min r (π/√K)` with `r` from `exists_uniform_local_jacobi_scale`,
which depends only on the dimension, the radius `ρ` and the curvature bound `K`. Here that choice is
made first, and the estimate is stated for every complete metric (with its induced instance block)
on the fixed manifold `M` afterwards, so a whole sequence of metrics uses one `R`
(`exists_local_volume_inj_radius_scale`).

`cgtVolumeInjRadius E q R v` is an explicit positive real below the resulting extended-real
quotient for every volume `v > 0` (`ofReal_cgtVolumeInjRadius_le`), in the pattern of
`selectedCGTInjRadius` (`KappaSolutions/CGTInjectivityRadius.lean`), now with an arbitrary Ricci
parameter `q ≥ 0`.
-/

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open Bundle Set Manifold MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff _root_.Topology ENNReal

universe u uE uH

section Constant

variable (E : Type uE) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

private local instance uniformCGTMeasurableE : MeasurableSpace E := borel E
private local instance uniformCGTBorelE : BorelSpace E := ⟨rfl⟩

/-- The real lower bound for the Cheeger–Gromov–Taylor injectivity-radius quotient at scale `R`,
with Ricci parameter `q` and ball volume `v`. -/
def cgtVolumeInjRadius (q R v : ℝ) : ℝ :=
  (R / 16) * v /
    (1 + ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere
        Set.univ).toReal * hyperbolicRadialVolume q (Module.finrank ℝ E - 1) (R / 8) +
      ((volume : Measure E).toSphere Set.univ).toReal *
        hyperbolicRadialVolume q (Module.finrank ℝ E - 1) (R / 4))

variable {E}

theorem cgtVolumeInjRadius_pos {q R v : ℝ} (hq : 0 ≤ q) (hR : 0 < R) (hv : 0 < v) :
    0 < cgtVolumeInjRadius E q R v := by
  have hsmall : 0 ≤ hyperbolicRadialVolume q (Module.finrank ℝ E - 1) (R / 8) :=
    (hyperbolicRadialVolume_pos hq (by positivity)).le
  have hlarge : 0 ≤ hyperbolicRadialVolume q (Module.finrank ℝ E - 1) (R / 4) :=
    (hyperbolicRadialVolume_pos hq (by positivity)).le
  unfold cgtVolumeInjRadius
  positivity

variable [NeZero (Module.finrank ℝ E)]

theorem ofReal_cgtVolumeInjRadius_le {q R v : ℝ} (hq : 0 ≤ q) (hR : 0 < R) :
    ENNReal.ofReal (cgtVolumeInjRadius E q R v) ≤
      ENNReal.ofReal (R / 16) * ENNReal.ofReal v /
        ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere
            Set.univ * ENNReal.ofReal (hyperbolicRadialVolume q (Module.finrank ℝ E - 1) (R / 8)) +
          (volume : Measure E).toSphere Set.univ *
            ENNReal.ofReal (hyperbolicRadialVolume q (Module.finrank ℝ E - 1) (R / 4))) := by
  let _ : Nontrivial E := Module.nontrivial_of_finrank_pos
    (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E)))
  have hfin : 0 < Module.finrank ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) := by
    simpa only [finrank_euclideanSpace, Fintype.card_fin] using
      Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))
  let _ : Nontrivial (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    Module.nontrivial_of_finrank_pos hfin
  let b : ℝ := ((volume : Measure (EuclideanSpace ℝ
    (Fin (Module.finrank ℝ E)))).toSphere Set.univ).toReal
  let p : ℝ := ((volume : Measure E).toSphere Set.univ).toReal
  let m : ℝ := hyperbolicRadialVolume q (Module.finrank ℝ E - 1) (R / 8)
  let l : ℝ := hyperbolicRadialVolume q (Module.finrank ℝ E - 1) (R / 4)
  have hb : 0 ≤ b := ENNReal.toReal_nonneg
  have hp : 0 ≤ p := ENNReal.toReal_nonneg
  have hm : 0 ≤ m := (hyperbolicRadialVolume_pos hq (by positivity)).le
  have hl : 0 ≤ l := (hyperbolicRadialVolume_pos hq (by positivity)).le
  have hbeq : (volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere
      Set.univ = ENNReal.ofReal b :=
    (ENNReal.ofReal_toReal (measure_lt_top _ _).ne).symm
  have hpeq : (volume : Measure E).toSphere Set.univ = ENNReal.ofReal p :=
    (ENNReal.ofReal_toReal (measure_lt_top _ _).ne).symm
  have hden :
      (volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere Set.univ *
          ENNReal.ofReal m + (volume : Measure E).toSphere Set.univ * ENNReal.ofReal l ≤
        ENNReal.ofReal (1 + b * m + p * l) := by
    rw [hbeq, hpeq, ← ENNReal.ofReal_mul hb, ← ENNReal.ofReal_mul hp,
      ← ENNReal.ofReal_add (mul_nonneg hb hm) (mul_nonneg hp hl)]
    apply ENNReal.ofReal_le_ofReal
    linarith
  have hpos : 0 < 1 + b * m + p * l := by positivity
  rw [cgtVolumeInjRadius, ENNReal.ofReal_div_of_pos hpos,
    ENNReal.ofReal_mul (by positivity : 0 ≤ R / 16)]
  exact ENNReal.div_le_div le_rfl hden

end Constant

section Scale

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] [ConnectedSpace M]

private local instance uniformCGTScaleMeasurableE : MeasurableSpace E := borel E
private local instance uniformCGTScaleBorelE : BorelSpace E := ⟨rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- **Uniform CGT scale.** For a radius `ρ > 0` and a curvature bound `K > 0` there is one scale
`R ∈ (0, min ρ (π/√K)]`, depending only on `dim M`, `ρ`, `K`, such that for EVERY complete metric
`g` on `M` (with its own induced extended metric and bundle instances), every Ricci parameter `q`,
every point `p` with `|Rm| ≤ K` on the `ρ`-ball and every lower bound `v` for the volume of the
`R/8`-ball, the Cheeger–Gromov–Taylor quotient bounds the injectivity radius at `p`. -/
theorem exists_local_volume_inj_radius_scale {ρ K : ℝ} (hρ : 0 < ρ) (hK : 0 < K) :
    ∃ R : ℝ, 0 < R ∧ R ≤ ρ ∧ R ≤ Real.pi / Real.sqrt K ∧
      ∀ [PseudoEMetricSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
        [IsRiemannianManifold I M] [CompleteSpace M]
        [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
        (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g) (q : ℝ), 0 ≤ q →
        RicciBoundedBelow (I := I) g (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2)) →
        ∀ (p : M) (v : ENNReal),
        (∀ y : M, riemannianEDist I p y < ENNReal.ofReal ρ →
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g y 4
            (metricRm04At (I := I) g y)) ≤ K) →
        v ≤ riemannianVolumeMeasure (I := I) (M := M) g
          {y : M | riemannianEDist I p y < ENNReal.ofReal (R / 8)} →
        ENNReal.ofReal (R / 16) * v /
          ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere Set.univ *
              ENNReal.ofReal (hyperbolicRadialVolume q (Module.finrank ℝ E - 1) (R / 8)) +
            (volume : Measure E).toSphere Set.univ *
              ENNReal.ofReal (hyperbolicRadialVolume q (Module.finrank ℝ E - 1) (R / 4))) ≤
          intrinsicInjRadius (I := I) g hEnorm p := by
  obtain ⟨r, hr, hrρ, herror⟩ :=
    exists_uniform_local_jacobi_scale (Module.finrank ℝ E) hρ hK.le
  let R : ℝ := min r (Real.pi / Real.sqrt K)
  have hR : 0 < R := lt_min hr (div_pos Real.pi_pos (Real.sqrt_pos.mpr hK))
  have hRr : R ≤ r := min_le_left _ _
  have hRρ : R ≤ ρ := hRr.trans hrρ
  have hRpi : R ≤ Real.pi / Real.sqrt K := min_le_right _ _
  refine ⟨R, hR, hRρ, hRpi, ?_⟩
  intro _ _ _ _ _ g hEnorm q hq hRic p v hRm hvol
  have hCGT := intrInj_ge_vol_of_ball (I := I) g hEnorm p hK hR hRρ hRpi hRm
    (fun a ha haR => herror a ha (haR.trans hRr))
    (r₀ := R / 8) (s := R / 8) (by positivity) (by positivity)
    (by linarith) (by linarith) hq hRic hvol
  have hhalf : R / 8 / 2 = R / 16 := by ring
  have hadd : R / 8 + R / 8 = R / 4 := by ring
  simpa only [hhalf, hadd] using hCGT

end Scale

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
