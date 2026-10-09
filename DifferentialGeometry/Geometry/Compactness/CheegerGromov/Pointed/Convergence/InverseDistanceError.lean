import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.InverseDistance

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped Manifold ContDiff _root_.Topology ENNReal

universe u uE uH

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
  {subseq : ℕ → ℕ} {Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq}

private local instance distanceErrorLimitTopology : TopologicalSpace L.M := L.topology
private local instance distanceErrorLimitCharted : ChartedSpace H L.M := L.charted
private local instance distanceErrorLimitSmooth : IsManifold I ∞ L.M := L.smooth
private local instance distanceErrorSourceTopology (k : ℕ) :
    TopologicalSpace (X.obj (subseq k)).M := (X.obj (subseq k)).topology
private local instance distanceErrorSourceCharted (k : ℕ) :
    ChartedSpace H (X.obj (subseq k)).M := (X.obj (subseq k)).charted
private local instance distanceErrorSourceSmooth (k : ℕ) :
    IsManifold I ∞ (X.obj (subseq k)).M := (X.obj (subseq k)).smooth

theorem tendsto_pointed_inverse_distance_sub_source
    (C : MetricConvergenceData (I := I) Φ)
    (hreference : ∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric)
    (hcomplete : MetricComplete (I := I) L)
    (rho : ℝ) (hrho : 0 ≤ rho)
    (y z : ∀ k : ℕ, (X.obj (subseq k)).M)
    (hball : ∀ᶠ k in atTop,
      y k ∈ riemannianClosedBallOf (I := I) (X.obj (subseq k)).metric
        (X.obj (subseq k)).basepoint rho ∧
      z k ∈ riemannianClosedBallOf (I := I) (X.obj (subseq k)).metric
        (X.obj (subseq k)).basepoint rho) :
    Tendsto (fun k =>
      (riemannianEDistOf (I := I) L.metric
        ((Φ.partialDiffeomorph k).symm (y k)) ((Φ.partialDiffeomorph k).symm (z k))).toReal -
      (riemannianEDistOf (I := I) (X.obj (subseq k)).metric (y k) (z k)).toReal)
      atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro eta heta
  let epsilon := eta / (8 * rho + 1)
  have hden : 0 < 8 * rho + 1 := by linarith
  have hepsilon : 0 < epsilon := div_pos heta hden
  have hcancel : epsilon * (8 * rho + 1) = eta := div_mul_cancel₀ eta hden.ne'
  obtain ⟨_, k0, hk0⟩ := exists_pointed_inverse_distance_control
    C hreference hcomplete rho hrho 1 zero_lt_one
  obtain ⟨_, k1, hk1⟩ := exists_pointed_inverse_distance_control
    C hreference hcomplete rho hrho epsilon hepsilon
  filter_upwards [hball, eventually_ge_atTop k0, eventually_ge_atTop k1] with k hkb hk0' hk1'
  let g := (X.obj (subseq k)).metric
  let p := (X.obj (subseq k)).basepoint
  let _ : RiemannianBundle (fun q : (X.obj (subseq k)).M => TangentSpace I q) :=
    ⟨g.toRiemannianMetric⟩
  have htriangle : riemannianEDistOf g (y k) (z k) ≤
      riemannianEDistOf g (y k) p + riemannianEDistOf g p (z k) :=
    Manifold.riemannianEDist_triangle
  have hcomm : riemannianEDistOf g (y k) p = riemannianEDistOf g p (y k) :=
    Manifold.riemannianEDist_comm
  have habound : riemannianEDistOf g (y k) (z k) ≤ ENNReal.ofReal (2 * rho) := by
    calc
      _ ≤ riemannianEDistOf g p (y k) + riemannianEDistOf g p (z k) := by
        simpa only [hcomm] using htriangle
      _ ≤ ENNReal.ofReal rho + ENNReal.ofReal rho := add_le_add hkb.1 hkb.2
      _ = ENNReal.ofReal (2 * rho) := by rw [← ENNReal.ofReal_add hrho hrho, two_mul]
  have hafin : riemannianEDistOf g (y k) (z k) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top habound
  let a := (riemannianEDistOf g (y k) (z k)).toReal
  let b := (riemannianEDistOf L.metric
    ((Φ.partialDiffeomorph k).symm (y k)) ((Φ.partialDiffeomorph k).symm (z k))).toReal
  have ha : a ≤ 2 * rho := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top habound
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * rho)] using hh
  have hc0 := (hk0 k hk0').2 (y k) hkb.1 (z k) hkb.2
  have hbfin : riemannianEDistOf L.metric
      ((Φ.partialDiffeomorph k).symm (y k)) ((Φ.partialDiffeomorph k).symm (z k)) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hafin) hc0.1
  have hb : b ≤ 4 * rho := by
    have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hafin) hc0.1
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num : 0 ≤ (1 : ℝ) + 1)] at hh
    change b ≤ (1 + 1) * a at hh
    linarith
  have hc := (hk1 k hk1').2 (y k) hkb.1 (z k) hkb.2
  have hba : b ≤ (1 + epsilon) * a := by
    have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hafin) hc.1
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith : 0 ≤ 1 + epsilon)] using hh
  have hab : a ≤ (1 + epsilon) * b := by
    have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hbfin) hc.2
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith : 0 ≤ 1 + epsilon)] using hh
  change dist (b - a) 0 < eta
  rw [Real.dist_eq, sub_zero, abs_lt]
  have hea := mul_le_mul_of_nonneg_left ha hepsilon.le
  have heb := mul_le_mul_of_nonneg_left hb hepsilon.le
  constructor <;> nlinarith [mul_nonneg hepsilon.le hrho]

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
