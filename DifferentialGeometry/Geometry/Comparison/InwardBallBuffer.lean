import DifferentialGeometry.Geometry.Geodesic.Ray
import DifferentialGeometry.Geometry.Metric.CurveSpeed
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity
import DifferentialGeometry.Geometry.Metric.Distance.Ball
import DifferentialGeometry.Geometry.Metric.Distance.Finiteness

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Geometry.Riemannian

variable {E E' H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] [ConnectedSpace M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- A minimizing source segment produces an inward point with a closed source-ball buffer.
The original differential bound controls its image displacement; no target completeness,
source-ball convexity or map injectivity is required. -/
theorem exists_inward_point_with_ball_buffer
    (h : SmoothRiemannianMetric I M) (hh : RiemannianMetricComplete h)
    (g : SmoothRiemannianMetric J N) (F : M → N) (o x : M)
    {A η L : ℝ} (hη : 0 < η) (hL : 0 ≤ L)
    (hx : x ∈ riemannianBallOf h o A)
    (hηd : η ≤ (riemannianEDistOf h o x).toReal)
    (hF : ContMDiffOn I J 1 F (riemannianBallOf h o A))
    (hupper : ∀ z ∈ riemannianBallOf h o A, ∀ v : TangentSpace I z,
      g.inner (F z) (mfderiv I J F z v) (mfderiv I J F z v) ≤
        L ^ 2 * h.inner z v v) :
    ∃ y : M,
      (riemannianEDistOf h o y).toReal = (riemannianEDistOf h o x).toReal - η ∧
      riemannianEDistOf h y x = ENNReal.ofReal η ∧
      riemannianClosedBallOf h y η ⊆ riemannianBallOf h o A ∧
      riemannianEDistOf g (F y) (F x) ≤ ENNReal.ofReal (L * η) := by
  let d := (riemannianEDistOf h o x).toReal
  have hd0 : 0 ≤ d := ENNReal.toReal_nonneg
  have hdE (a b : M) : riemannianEDistOf h a b =
      ENNReal.ofReal (riemannianEDistOf h a b).toReal :=
    (ENNReal.ofReal_toReal (riemannianEDistOf_ne_top h a b)).symm
  have hox : o ≠ x := by
    intro heq
    have hd : d = 0 := by simp only [d, ← heq, riemannianEDistOf_self, ENNReal.toReal_zero]
    change η ≤ d at hηd
    linarith
  obtain ⟨γ, hγ0, hγd, hγ, _hgeodesic, hunit, hdist⟩ :=
    DifferentialGeometry.Geometry.exists_unitSpeed_minimizing_geodesic_of_complete
      h hh o x hox
  change γ d = x at hγd
  change ∀ s ∈ Icc 0 d, ∀ t ∈ Icc 0 d,
    (riemannianEDistOf h (γ s) (γ t)).toReal = |s - t| at hdist
  have ha : d - η ∈ Icc 0 d := ⟨sub_nonneg.mpr hηd, by linarith⟩
  have hradial (s : ℝ) (hs : s ∈ Icc 0 d) :
      (riemannianEDistOf h o (γ s)).toReal = s := by
    simpa only [hγ0, zero_sub, abs_neg, abs_of_nonneg hs.1] using
      hdist 0 ⟨le_rfl, hd0⟩ s hs
  have henddist : riemannianEDistOf h (γ (d - η)) x = ENNReal.ofReal η := by
    rw [hdE]
    congr 1
    have hd := hdist (d - η) ha d ⟨hd0, le_rfl⟩
    simpa only [hγd, show d - η - d = -η by ring, abs_neg, abs_of_pos hη] using hd
  have hx' : ENNReal.ofReal d < ENNReal.ofReal A := by
    change riemannianEDistOf h o x < ENNReal.ofReal A at hx
    exact (hdE o x).symm.trans_lt hx
  have hbuffer : riemannianClosedBallOf h (γ (d - η)) η ⊆
      riemannianBallOf h o A := by
    intro z hz
    calc
      riemannianEDistOf h o z ≤
          riemannianEDistOf h o (γ (d - η)) + riemannianEDistOf h (γ (d - η)) z :=
        riemannianEDistOf_triangle h o (γ (d - η)) z
      _ ≤ ENNReal.ofReal (d - η) + ENNReal.ofReal η := by
        rw [hdE o (γ (d - η)), hradial (d - η) ha]
        exact add_le_add le_rfl hz
      _ = ENNReal.ofReal d := by
        rw [← ENNReal.ofReal_add ha.1 hη.le, sub_add_cancel]
      _ < ENNReal.ofReal A := hx'
  have hstay : MapsTo γ (Icc (d - η) d) (riemannianBallOf h o A) := by
    intro s hs
    have hs' : s ∈ Icc 0 d := ⟨ha.1.trans hs.1, hs.2⟩
    change riemannianEDistOf h o (γ s) < ENNReal.ofReal A
    rw [hdE, hradial s hs']
    exact (ENNReal.ofReal_le_ofReal hs.2).trans_lt hx'
  have hopen : IsOpen (riemannianBallOf h o A) :=
    isOpen_lt (continuous_riemannianEDist h o) continuous_const
  have hγone : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc (d - η) d) :=
    (hγ.of_le (by decide : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω))).contMDiffOn
  have hcomp := hF.comp hγone hstay
  have hspeed : ∀ s ∈ Ioo (d - η) d, Real.sqrt
      (g.inner ((F ∘ γ) s) (mfderiv 𝓘(ℝ, ℝ) J (F ∘ γ) s 1)
        (mfderiv 𝓘(ℝ, ℝ) J (F ∘ γ) s 1)) ≤ L := by
    intro s hs
    have hγs := hstay ⟨hs.1.le, hs.2.le⟩
    have hFd := (hF.contMDiffAt (hopen.mem_nhds hγs)).mdifferentiableAt (by norm_num)
    have hγd' := hγ.mdifferentiable (by simp) s
    rw [mfderiv_comp_apply s hFd hγd']
    calc
      _ ≤ Real.sqrt (L ^ 2 * h.inner (γ s)
          (mfderiv 𝓘(ℝ, ℝ) I γ s 1) (mfderiv 𝓘(ℝ, ℝ) I γ s 1)) :=
        Real.sqrt_le_sqrt (hupper (γ s) hγs _)
      _ = L := by rw [hunit, mul_one, Real.sqrt_sq hL]
  have hlength := DifferentialGeometry.Geometry.riemannianEDistOf_le_of_curve_speed_bound
    g ha.2 hcomp hspeed
  have himage : riemannianEDistOf g (F (γ (d - η))) (F x) ≤
      ENNReal.ofReal (L * η) := by
    simpa only [Function.comp_apply, hγd, show d - (d - η) = η by ring,
      ← ENNReal.ofReal_mul hL] using hlength
  exact ⟨γ (d - η), hradial (d - η) ha, henddist, hbuffer, himage⟩

end DifferentialGeometry.Geometry.Riemannian
