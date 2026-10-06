import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroGlueVolumeTest

/-!
# CH12-O6, G1: KL Lemma 83.1 from one almost-model ball at a definite scale

Kleiner–Lott, *Notes on Perelman's papers* (G&T 12, 2008), Lemma 83.1 (p. 2791–2792): for
`b, w > 0` there is `θ₀(b, w)` such that a unit ball of volume `≥ w` with `sec ≥ -1` contains a
ball `B(y, θ₀)` all of whose subballs have volume `≥ (1 - b) ω₃ r³`.

The KL proof has two halves.
* (core) a contradiction/GH argument (pointed GH limit is an Alexandrov space, BGP Thm 10.8 volume
  convergence, a regular point of the limit) giving ONE ball `B(x', r)` at a definite scale
  with almost-Euclidean volume;
* (83.2–83.4) a Bishop–Gromov transfer from that ball to every subball of a much smaller
  concentric ball.

This file proves the second half in full and states the first half as the explicit hypothesis
`hcore` (inline, not a named Prop).  `hcore` is stated with the hyperbolic model
`V_{-r⁻²}(σ)` in place of `ω₃ σ³`: by relative Bishop–Gromov this is the scale-robust form (the
ratio `vol B(y, ·) / V_{-r⁻²}(·)` is nonincreasing), and it is implied by KL 83.1 itself
(take `σ = θ₀ r / 2` small), so `hcore` is no stronger than the theorem it feeds.

Main result: `almost_euclidean_subball_of_core_O6` (frozen shape of CH12-O4 G1
`almost_euclidean_subball_O4`, with `hcore` as the only extra input).
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

/-- Uniform continuity of the unit hyperbolic model volume on `[0, 1]`, in ratio form above a
fixed scale `σ₀`: `V₋₁(s + t) ≤ (1 + ε) V₋₁(s)` for `σ₀ ≤ s ≤ 1/2`, `0 ≤ t ≤ δ`. -/
theorem modelVolume_neg_one_ratio_O6 {σ₀ ε : ℝ} (hσ₀ : 0 < σ₀) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ ∀ s t : ℝ, σ₀ ≤ s → s ≤ 1 / 2 → 0 ≤ t → t ≤ δ →
      modelVolume (-((1 : ℝ) ^ 2)) 3 (s + t) ≤ (1 + ε) * modelVolume (-((1 : ℝ) ^ 2)) 3 s := by
  set f := fun x : ℝ => modelVolume (-((1 : ℝ) ^ 2)) 3 x with hf
  have hω := euclideanUnitBallVolume_pos 3
  have hm : 0 < ε * (euclideanUnitBallVolume 3 * σ₀ ^ 3) := by positivity
  have huc : UniformContinuousOn f (Icc (0 : ℝ) 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous (modelVolume_continuous _ _).continuousOn
  obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuousOn_iff.mp huc _ hm
  refine ⟨min (δ / 2) (1 / 2), by positivity, min_le_right _ _, ?_⟩
  intro s t hs hs2 ht htδ
  have hs0 : 0 ≤ s := hσ₀.le.trans hs
  have htδ' : t < δ := lt_of_le_of_lt (htδ.trans (min_le_left _ _)) (by linarith)
  have ht2 : t ≤ 1 / 2 := htδ.trans (min_le_right _ _)
  have hd := hδf (s + t) ⟨by linarith, by linarith⟩ s ⟨hs0, by linarith⟩
    (by rw [Real.dist_eq]; rw [abs_of_nonneg (by linarith)]; linarith)
  rw [Real.dist_eq] at hd
  have hlow : euclideanUnitBallVolume 3 * σ₀ ^ 3 ≤ f s := by
    have h1 := euclid_le_modelVolume_neg_sq_three_FXC1 (q := 1) zero_le_one hs0
    have h2 : σ₀ ^ 3 ≤ s ^ 3 := pow_le_pow_left₀ hσ₀.le hs 3
    calc euclideanUnitBallVolume 3 * σ₀ ^ 3 ≤ euclideanUnitBallVolume 3 * s ^ 3 := by gcongr
      _ ≤ f s := h1
  have := (abs_lt.mp hd).2
  change f (s + t) ≤ (1 + ε) * f s
  nlinarith [hlow]

/-- **G1 (KL 83.1), reduced to its GH core.**  Given the core (one ball `B(y, σ)` with
`σ ≥ σ₀ r`, `B(y, 2σ) ⊆ B(p, r)` and `vol B(y, σ) ≥ (1 - ε₁) V_{-r⁻²}(σ)`), every ball
`B(z, b)` with `z ∈ B(y, θ r)`, `b ≤ θ r` has `vol ≥ (1 - ε) ω₃ b³`, with `θ = θ(w, ε)`
chosen before the manifold.  Proof = KL (83.2)–(83.4): relative Bishop–Gromov at `z` between
`b` and `σ + θ r`, `B(y, σ) ⊆ B(z, σ + θ r)`, uniform continuity of `V₋₁` and `ω₃ b³ ≤ V(b)`. -/
theorem almost_euclidean_subball_of_core_O6
    (hcore : ∀ w : ℝ, 0 < w → ∀ ε₁ : ℝ, 0 < ε₁ → ∃ σ₀ : ℝ, 0 < σ₀ ∧
      ∀ (X : Type u) [TopologicalSpace X] [ChartedSpace ThreeSpace X]
        [IsManifold ThreeModel ∞ X] [T2Space X] [CompactSpace X]
        (g : SmoothRiemannianMetric ThreeModel X) (p : X) (r : ℝ), 0 < r →
        (∀ q ∈ riemannianBallOf g p r, SectionalBoundedBelowAt g q (-(r ^ 2)⁻¹)) →
        ENNReal.ofReal (w * r ^ 3) ≤ ballVolume g p r →
        ∃ (y : X) (σ : ℝ), σ₀ * r ≤ σ ∧
          riemannianEDistOf g p y + ENNReal.ofReal (2 * σ) ≤ ENNReal.ofReal r ∧
          ENNReal.ofReal ((1 - ε₁) * modelVolume (-(r ^ 2)⁻¹) 3 σ) ≤ ballVolume g y σ) :
    ∀ w : ℝ, 0 < w → ∀ ε : ℝ, 0 < ε → ∃ θ : ℝ, 0 < θ ∧
      ∀ (X : Type u) [TopologicalSpace X] [ChartedSpace ThreeSpace X]
        [IsManifold ThreeModel ∞ X] [T2Space X] [CompactSpace X]
        (g : SmoothRiemannianMetric ThreeModel X) (p : X) (r : ℝ), 0 < r →
        (∀ q ∈ riemannianBallOf g p r, SectionalBoundedBelowAt g q (-(r ^ 2)⁻¹)) →
        ENNReal.ofReal (w * r ^ 3) ≤ ballVolume g p r →
        ∃ y : X, riemannianBallOf g y (θ * r) ⊆ riemannianBallOf g p r ∧
          ∀ z ∈ riemannianBallOf g y (θ * r), ∀ b : ℝ, 0 < b → b ≤ θ * r →
            ENNReal.ofReal ((1 - ε) * euclideanUnitBallVolume 3 * b ^ 3) ≤ ballVolume g z b := by
  intro w hw ε hε
  obtain ⟨σ₀, hσ₀, hc⟩ := hcore w hw (ε / 2) (by positivity)
  obtain ⟨δ, hδ, hδ2, hratio⟩ := modelVolume_neg_one_ratio_O6 hσ₀ (by positivity : 0 < ε / 2)
  refine ⟨min (σ₀ / 2) δ, by positivity, ?_⟩
  intro X _ _ _ _ _ g p r hr hsec hvol
  set θ := min (σ₀ / 2) δ with hθ
  have hθpos : 0 < θ := by positivity
  obtain ⟨y, σ, hσ, hyp, hyvol⟩ := hc X g p r hr hsec hvol
  have hσpos : 0 < σ := lt_of_lt_of_le (by positivity) hσ
  set ρ := θ * r with hρ
  have hρpos : 0 < ρ := by positivity
  have hρσ : 2 * ρ ≤ σ := by
    have : θ ≤ σ₀ / 2 := min_le_left _ _
    have h2 : 2 * (θ * r) ≤ σ₀ * r := by nlinarith
    linarith
  -- `d(p, y)` is finite and `σ ≤ r/2`
  have hpy_le : riemannianEDistOf g p y ≤ ENNReal.ofReal r :=
    le_trans le_self_add hyp
  have hpy_ne : riemannianEDistOf g p y ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hpy_le
  have hσr : 2 * σ ≤ r := by
    have h1 : ENNReal.ofReal (2 * σ) ≤ ENNReal.ofReal r := le_trans le_add_self hyp
    exact (ENNReal.ofReal_le_ofReal_iff hr.le).mp h1
  -- `B(y, 2σ) ⊆ B(p, r)`
  have hsub2 : riemannianBallOf g y (2 * σ) ⊆ riemannianBallOf g p r := by
    intro q hq
    have hq' : riemannianEDistOf g y q < ENNReal.ofReal (2 * σ) := hq
    change riemannianEDistOf g p q < ENNReal.ofReal r
    calc riemannianEDistOf g p q ≤ riemannianEDistOf g p y + riemannianEDistOf g y q :=
          riemannianEDistOf_triangle g p y q
      _ < riemannianEDistOf g p y + ENNReal.ofReal (2 * σ) :=
          ENNReal.add_lt_add_left hpy_ne hq'
      _ ≤ ENNReal.ofReal r := hyp
  have hball_mono : ∀ {a c : ℝ}, a ≤ c → riemannianBallOf g y a ⊆ riemannianBallOf g y c := by
    intro a c hac q hq
    exact lt_of_lt_of_le hq (ENNReal.ofReal_le_ofReal hac)
  refine ⟨y, (hball_mono (by linarith)).trans hsub2, ?_⟩
  intro z hz b hb hbρ
  have hz' : riemannianEDistOf g y z < ENNReal.ofReal ρ := hz
  -- curvature on `B(z, σ + ρ) ⊆ B(y, σ + 2ρ) ⊆ B(y, 2σ)`
  have hsecz : ∀ q ∈ riemannianBallOf g z (σ + ρ),
      SectionalBoundedBelowAt g q (-(r ^ 2)⁻¹) := by
    intro q hq
    apply hsec q
    apply hsub2
    have hq' : riemannianEDistOf g z q < ENNReal.ofReal (σ + ρ) := hq
    change riemannianEDistOf g y q < ENNReal.ofReal (2 * σ)
    calc riemannianEDistOf g y q ≤ riemannianEDistOf g y z + riemannianEDistOf g z q :=
          riemannianEDistOf_triangle g y z q
      _ < ENNReal.ofReal ρ + ENNReal.ofReal (σ + ρ) := ENNReal.add_lt_add hz' hq'
      _ = ENNReal.ofReal (σ + 2 * ρ) := by
          rw [← ENNReal.ofReal_add hρpos.le (by positivity)]; ring_nf
      _ ≤ ENNReal.ofReal (2 * σ) := ENNReal.ofReal_le_ofReal (by linarith)
  -- `B(y, σ) ⊆ B(z, σ + ρ)`
  have hyz : riemannianBallOf g y σ ⊆ riemannianBallOf g z (σ + ρ) := by
    intro q hq
    have hq' : riemannianEDistOf g y q < ENNReal.ofReal σ := hq
    change riemannianEDistOf g z q < ENNReal.ofReal (σ + ρ)
    have hzy : riemannianEDistOf g z y < ENNReal.ofReal ρ := by
      rw [riemannianEDistOf_comm]; exact hz'
    calc riemannianEDistOf g z q ≤ riemannianEDistOf g z y + riemannianEDistOf g y q :=
          riemannianEDistOf_triangle g z y q
      _ < ENNReal.ofReal ρ + ENNReal.ofReal σ := ENNReal.add_lt_add hzy hq'
      _ = ENNReal.ofReal (σ + ρ) := by
          rw [← ENNReal.ofReal_add hρpos.le hσpos.le, add_comm]
  have hmono : ballVolume g y σ ≤ ballVolume g z (σ + ρ) :=
    MeasureTheory.measure_mono hyz
  have hκ : (0 : ℝ) ≤ (r ^ 2)⁻¹ := by positivity
  have hBG := FILL910.localBishopGromov_cross_of_compact_three g z hκ hb
    (by linarith : b ≤ σ + ρ) hsecz
  -- trivial case `ε ≥ 1`
  by_cases hε1 : 1 ≤ ε
  · have h0 : (1 - ε) * euclideanUnitBallVolume 3 * b ^ 3 ≤ 0 := by
      have := euclideanUnitBallVolume_pos 3
      have hb3 : 0 < b ^ 3 := by positivity
      have h1 : (1 - ε) * euclideanUnitBallVolume 3 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) this.le
      exact mul_nonpos_of_nonpos_of_nonneg h1 hb3.le
    rw [ENNReal.ofReal_eq_zero.mpr h0]; exact zero_le
  have hε1 : ε < 1 := lt_of_not_ge hε1
  -- model volumes in unit scale
  set V := fun c : ℝ => modelVolume (-(r ^ 2)⁻¹) 3 c with hV
  set V1 := fun c : ℝ => modelVolume (-((1 : ℝ) ^ 2)) 3 c with hV1
  have hVσ : V σ = r ^ 3 * V1 (σ / r) := by
    have h := modelVolume_scale_O3 hr (σ / r)
    rw [show r * (σ / r) = σ by field_simp] at h
    exact h
  have hVσρ : V (σ + ρ) = r ^ 3 * V1 (σ / r + θ) := by
    have h := modelVolume_scale_O3 hr (σ / r + θ)
    rw [show r * (σ / r + θ) = σ + ρ by rw [hρ]; field_simp] at h
    exact h
  have hs0 : σ₀ ≤ σ / r := (le_div_iff₀ hr).mpr hσ
  have hs2 : σ / r ≤ 1 / 2 := (div_le_iff₀ hr).mpr (by linarith)
  have hrat := hratio (σ / r) θ hs0 hs2 hθpos.le (min_le_right _ _)
  have hV1pos : 0 < V1 (σ / r) := modelVolume_neg_one_pos_O3 (by positivity)
  have hVσρ_le : V (σ + ρ) ≤ (1 + ε / 2) * V σ := by
    rw [hVσρ, hVσ]
    have hr3 : 0 < r ^ 3 := by positivity
    calc r ^ 3 * V1 (σ / r + θ) ≤ r ^ 3 * ((1 + ε / 2) * V1 (σ / r)) :=
          mul_le_mul_of_nonneg_left hrat hr3.le
      _ = (1 + ε / 2) * (r ^ 3 * V1 (σ / r)) := by ring
  have hVσpos : 0 < V σ := by rw [hVσ]; positivity
  have hVσρpos : 0 < V (σ + ρ) := by
    rw [hVσρ]; exact mul_pos (by positivity) (modelVolume_neg_one_pos_O3 (by positivity))
  have hVb : euclideanUnitBallVolume 3 * b ^ 3 ≤ V b := by
    have h := euclid_le_modelVolume_neg_sq_three_FXC1 (q := 1 / r) (by positivity) hb.le
    have hq : (1 / r) ^ 2 = (r ^ 2)⁻¹ := by field_simp
    rwa [hq] at h
  -- chain: `(1-ε/2) V(σ) V(b) ≤ V(σ+ρ) vol B(z,b)`
  have hchain : ENNReal.ofReal ((1 - ε / 2) * V σ) * ENNReal.ofReal (V b) ≤
      ENNReal.ofReal (V (σ + ρ)) * ballVolume g z b :=
    calc ENNReal.ofReal ((1 - ε / 2) * V σ) * ENNReal.ofReal (V b)
        ≤ ballVolume g z (σ + ρ) * ENNReal.ofReal (V b) := by
          gcongr; exact hyvol.trans hmono
      _ ≤ ENNReal.ofReal (V (σ + ρ)) * ballVolume g z b := hBG
  have hreal : V (σ + ρ) * ((1 - ε) * euclideanUnitBallVolume 3 * b ^ 3) ≤
      (1 - ε / 2) * V σ * V b := by
    have hω := euclideanUnitBallVolume_pos 3
    have hb3 : 0 < b ^ 3 := by positivity
    have h1 : 0 ≤ 1 - ε := by linarith
    have hA : 0 ≤ (1 - ε) * (euclideanUnitBallVolume 3 * b ^ 3) := by positivity
    calc V (σ + ρ) * ((1 - ε) * euclideanUnitBallVolume 3 * b ^ 3)
        = V (σ + ρ) * ((1 - ε) * (euclideanUnitBallVolume 3 * b ^ 3)) := by ring
      _ ≤ ((1 + ε / 2) * V σ) * ((1 - ε) * V b) := by
          apply mul_le_mul hVσρ_le _ hA (by positivity)
          exact mul_le_mul_of_nonneg_left hVb h1
      _ ≤ (1 - ε / 2) * V σ * V b := by
          have hVbpos : 0 ≤ V b := le_trans (by positivity) hVb
          have hkey : (1 + ε / 2) * (1 - ε) ≤ 1 - ε / 2 := by nlinarith
          have := mul_le_mul_of_nonneg_right hkey (mul_nonneg hVσpos.le hVbpos)
          nlinarith
  have hkey : ENNReal.ofReal (V (σ + ρ)) *
      ENNReal.ofReal ((1 - ε) * euclideanUnitBallVolume 3 * b ^ 3) ≤
      ENNReal.ofReal (V (σ + ρ)) * ballVolume g z b := by
    rw [← ENNReal.ofReal_mul hVσρpos.le]
    refine le_trans ?_ hchain
    rw [← ENNReal.ofReal_mul (by nlinarith)]
    exact ENNReal.ofReal_le_ofReal hreal
  exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr hVσρpos).ne'
    ENNReal.ofReal_ne_top).mp hkey

end GC.LongTime.Ch12
