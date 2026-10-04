import DifferentialGeometry.Geometry.Comparison.FiniteSoul.ClosedGeodesicTube
import DifferentialGeometry.Geometry.Exponential.FiniteMetric.UniformNormalCharts

/-!
# Forms and consumers of the tube around the soul (S-TUBE, D3)

Package CM-S (finite soul), lane CMS-T.

* `exists_closedGeodesic_tube`: the FROZEN interface statement of
  `build-logs/scratch/D-CMS/FiniteSoulInterfaces.lean` (injective, onto `{d_S < ε}` and calibrated
  on `[0, ℓ) × (−ε, ε)`), kept as a lemma (D3); derived from the quotient tube.
* `exists_closedGeodesic_normalTube_homeomorph`: the holonomy `σ` of `ν` is produced, and the
  open `ε`-tube of `NormalLineBundle σ` is homeomorphic to `{d_S < ε}` by the tube map (the form
  consumed by the S6 gluing).
* `exists_point_normalTube`: the tube of a point soul, CM1.d's normal chart repackaged as a `C^r`
  partial diffeomorphism from the `g_x`-ball onto `{d_{x} < ε}` with `d_{x}(Φ v) = |v|_{g_x}`.
* Consumer: `exists_closedGeodesic_normalTube_C2_of_C3`: for a `C³` metric (`r = 2`) the tube
  map is a `C²` partial diffeomorphism.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- **The frozen S-TUBE statement** (kept as a lemma, disposition D3): injective on
`[0, ℓ) × (−ε, ε)`, image `{d_S < ε}`, calibration `d_S = |h|`. -/
theorem exists_closedGeodesic_tube [CompleteSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hdim : Module.finrank ℝ E = 2) (p : TangentBundle I M) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hunit : g.inner p.proj p.snd p.snd = 1) (hper : g.geodesicFlow p ℓ = p)
    (hinj : InjOn (fun t => (g.geodesicFlow p t).proj) (Ico 0 ℓ)) (ν : ℝ → E)
    (hν : Continuous (fun t => (⟨(g.geodesicFlow p t).proj, ν t⟩ : TangentBundle I M)))
    (hνunit : ∀ t, g.inner (g.geodesicFlow p t).proj (ν t) (ν t) = 1)
    (hνperp : ∀ t, g.inner (g.geodesicFlow p t).proj (ν t) (g.geodesicFlow p t).snd = 0) :
    ∃ ε > 0,
      InjOn (fun z : ℝ × ℝ => g.expMap (⟨(g.geodesicFlow p z.1).proj, z.2 • ν z.1⟩ : TangentBundle I M))
        (Ico 0 ℓ ×ˢ Ioo (-ε) ε) ∧
      (fun z : ℝ × ℝ => g.expMap (⟨(g.geodesicFlow p z.1).proj, z.2 • ν z.1⟩ : TangentBundle I M)) ''
          (Ico 0 ℓ ×ˢ Ioo (-ε) ε) =
        {y | infDist y (range (fun t => (g.geodesicFlow p t).proj)) < ε} ∧
      ∀ z ∈ Ico 0 ℓ ×ˢ Ioo (-ε) ε,
        infDist (g.expMap (⟨(g.geodesicFlow p z.1).proj, z.2 • ν z.1⟩ : TangentBundle I M))
          (range (fun t => (g.geodesicFlow p t).proj)) = |z.2| := by
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  have hdom := g.geodesicFlowDomain_eq_univ hr hnorm
  obtain ⟨σ, hσ⟩ := exists_unitNormal_holonomy g hr1 hdom hdim p hunit hper hν hνunit hνperp
  obtain ⟨ε, hε, F, hFexp, -, hcal, himage, hFinj, -⟩ :=
    exists_closedGeodesic_normalLineBundle_tube g hr hnorm hdim p hℓ hunit hper hinj hν hνunit
      hνperp hσ
  -- the strip in `ℓ`-units is the tube in normalised units
  have hF : ∀ z : ℝ × ℝ, g.expMap (⟨(g.geodesicFlow p z.1).proj, z.2 • ν z.1⟩ : TangentBundle I M) =
      F (NormalLineBundle.mk σ (z.1 / ℓ) z.2) := by
    intro z
    rw [hFexp, mul_div_cancel₀ z.1 hℓ.ne']
  have hmemT : ∀ z ∈ Ico 0 ℓ ×ˢ Ioo (-ε) ε,
      NormalLineBundle.mk σ (z.1 / ℓ) z.2 ∈ {q | NormalLineBundle.fiberAbs σ q < ε} := by
    intro z hz
    change NormalLineBundle.fiberAbs σ (NormalLineBundle.mk σ (z.1 / ℓ) z.2) < ε
    rw [NormalLineBundle.fiberAbs_mk]
    exact abs_lt.mpr hz.2
  have hdivIco : ∀ z ∈ Ico 0 ℓ ×ˢ Ioo (-ε) ε, z.1 / ℓ ∈ Ico (0 : ℝ) 1 := by
    intro z hz
    exact ⟨div_nonneg hz.1.1 hℓ.le, (div_lt_one hℓ).mpr hz.1.2⟩
  refine ⟨ε, hε, ?_, ?_, ?_⟩
  · intro z hz z' hz' heq
    simp only at heq
    rw [hF, hF] at heq
    have hmk := hFinj (hmemT z hz) (hmemT z' hz') heq
    obtain ⟨h1, h2⟩ := NormalLineBundle.eq_of_mk_eq_of_mem_Ico σ (hdivIco z hz) (hdivIco z' hz') hmk
    have h1' : z.1 = z'.1 := by
      have := congrArg (fun a => a * ℓ) h1
      simpa only [div_mul_cancel₀ _ hℓ.ne'] using this
    exact Prod.ext h1' h2
  · rw [← himage]
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨_, hmemT z hz, (hF z).symm⟩
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨t, ht, h, rfl⟩ := NormalLineBundle.exists_mk_eq σ q
      have hh : |h| < ε := by
        change NormalLineBundle.fiberAbs σ _ < ε at hq
        rwa [NormalLineBundle.fiberAbs_mk] at hq
      refine ⟨(ℓ * t, h), ⟨⟨mul_nonneg hℓ.le ht.1, by nlinarith [ht.2]⟩, abs_lt.mp hh⟩, ?_⟩
      exact (hFexp t h).symm
  · intro z hz
    rw [hF, hcal _ (hmemT z hz), NormalLineBundle.fiberAbs_mk]

/-- **The tube as a homeomorphism** (holonomy produced): for a continuous unit normal `ν` along a
simple closed unit geodesic of a complete surface there are a sign `σ` with
`ν (t + ℓ) = σ • ν t`, a radius `ε > 0` and the tube map `F` on `NormalLineBundle σ`, which fixes
the zero section, is calibrated, and restricts to a homeomorphism from the open `ε`-tube onto
`{d_S < ε}`. -/
theorem exists_closedGeodesic_normalTube_homeomorph [CompleteSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hdim : Module.finrank ℝ E = 2) (p : TangentBundle I M) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hunit : g.inner p.proj p.snd p.snd = 1) (hper : g.geodesicFlow p ℓ = p)
    (hinj : InjOn (fun t => (g.geodesicFlow p t).proj) (Ico 0 ℓ)) {ν : ℝ → E}
    (hν : Continuous (fun t => (⟨(g.geodesicFlow p t).proj, ν t⟩ : TangentBundle I M)))
    (hνunit : ∀ t, g.inner (g.geodesicFlow p t).proj (ν t) (ν t) = 1)
    (hνperp : ∀ t, g.inner (g.geodesicFlow p t).proj (ν t) (g.geodesicFlow p t).snd = 0) :
    ∃ σ : ℤˣ, (∀ t, ν (t + ℓ) = ((σ : ℤ) : ℝ) • ν t) ∧ ∃ ε > 0, ∃ F : NormalLineBundle σ → M,
      (∀ t h, F (NormalLineBundle.mk σ t h) =
        g.expMap (⟨(g.geodesicFlow p (ℓ * t)).proj, h • ν (ℓ * t)⟩ : TangentBundle I M)) ∧
      (∀ t, F (NormalLineBundle.mk σ t 0) = (g.geodesicFlow p (ℓ * t)).proj) ∧
      (∀ q, NormalLineBundle.fiberAbs σ q < ε →
        infDist (F q) (range fun t => (g.geodesicFlow p t).proj) = NormalLineBundle.fiberAbs σ q) ∧
      ∃ e : ({q | NormalLineBundle.fiberAbs σ q < ε} : Set (NormalLineBundle σ)) ≃ₜ
          ({y | infDist y (range fun t => (g.geodesicFlow p t).proj) < ε} : Set M),
        ∀ q, (e q : M) = F q := by
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  have hdom := g.geodesicFlowDomain_eq_univ hr hnorm
  obtain ⟨σ, hσ⟩ := exists_unitNormal_holonomy g hr1 hdom hdim p hunit hper hν hνunit hνperp
  obtain ⟨ε, hε, F, hFexp, hF0, hcal, -, -, hdiff⟩ :=
    exists_closedGeodesic_normalLineBundle_tube g hr hnorm hdim p hℓ hunit hper hinj hν hνunit
      hνperp hσ
  obtain ⟨Φ, hs, ht, hΦ⟩ := hdiff 1 le_rfl (by exact_mod_cast hr1)
  refine ⟨σ, hσ, ε, hε, F, hFexp, hF0, hcal,
    ((Homeomorph.setCongr hs.symm).trans Φ.toOpenPartialHomeomorph.toHomeomorphSourceTarget).trans
      (Homeomorph.setCongr ht), fun q => ?_⟩
  change Φ q = F q
  rw [hΦ]

/-- **The tube of a point soul** (CM1.d bound directly): `exp_x` is a `C^r` partial
diffeomorphism from the `g_x`-ball of radius `ε` onto `{d_{x} < ε}`, fixing `0 ↦ x`, with
`d_{x}(exp_x v) = |v|_{g_x}`. -/
theorem exists_point_normalTube
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (x : M) :
    ∃ ε > 0, ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M r,
      Φ.source = {v : E | g.inner x v v < ε ^ 2} ∧ Φ.target = {y | infDist y {x} < ε} ∧
      (Φ : E → M) 0 = x ∧
      ∀ v ∈ Φ.source, (Φ : E → M) v = g.expMap (⟨x, v⟩ : TangentBundle I M) ∧
        infDist ((Φ : E → M) v) {x} = Real.sqrt (g.inner x v v) := by
  obtain ⟨ε, hε, hK⟩ := g.exists_uniform_normal_charts hr hnorm (isCompact_singleton (x := x))
  obtain ⟨e, hsrc, htgt, hexp, hsm, hsymm, hdist⟩ := hK x (mem_singleton x)
  refine ⟨ε, hε, { toPartialEquiv := e.toPartialEquiv
                   open_source := e.open_source
                   open_target := e.open_target
                   contMDiffOn_toFun := hsm
                   contMDiffOn_invFun := hsymm }, hsrc, ?_, ?_, fun v hv => ⟨(hexp v hv).2, ?_⟩⟩
  · change e.target = _
    rw [htgt]
    ext y
    change dist y x < ε ↔ infDist y {x} < ε
    rw [infDist_singleton]
  · set B : E →L[ℝ] E →L[ℝ] ℝ := g.inner x with hB
    have h0 : (0 : E) ∈ e.source := by
      rw [hsrc]
      change B 0 0 < ε ^ 2
      rw [map_zero]
      positivity
    have hd := hdist 0 h0
    change dist x (e 0) = Real.sqrt (B 0 0) at hd
    rw [map_zero, Real.sqrt_zero, dist_eq_zero] at hd
    exact hd.symm
  · change infDist (e v) {x} = _
    rw [infDist_singleton, dist_comm]
    exact hdist v hv

/-- **Consumer** (C³ metric): for `r = 2` the tube map of a closed geodesic is a `C²` partial
diffeomorphism from the open `ε`-tube of its normal line bundle onto `{d_S < ε}`. -/
theorem exists_closedGeodesic_normalTube_C2_of_C3 [CompleteSpace M]
    (g : ContMDiffRiemannianMetric I (((2 : ℕ∞) : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hdim : Module.finrank ℝ E = 2) (p : TangentBundle I M) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hunit : g.inner p.proj p.snd p.snd = 1) (hper : g.geodesicFlow p ℓ = p)
    (hinj : InjOn (fun t => (g.geodesicFlow p t).proj) (Ico 0 ℓ)) {ν : ℝ → E}
    (hν : Continuous (fun t => (⟨(g.geodesicFlow p t).proj, ν t⟩ : TangentBundle I M)))
    (hνunit : ∀ t, g.inner (g.geodesicFlow p t).proj (ν t) (ν t) = 1)
    (hνperp : ∀ t, g.inner (g.geodesicFlow p t).proj (ν t) (g.geodesicFlow p t).snd = 0) :
    ∃ σ : ℤˣ, ∃ ε > 0, ∃ Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) I (NormalLineBundle σ) M 2,
      Φ.source = {q | NormalLineBundle.fiberAbs σ q < ε} ∧
      Φ.target = {y | infDist y (range fun t => (g.geodesicFlow p t).proj) < ε} := by
  have hdom := g.geodesicFlowDomain_eq_univ le_rfl hnorm
  obtain ⟨σ, hσ⟩ := exists_unitNormal_holonomy g (by norm_num) hdom hdim p hunit hper hν hνunit
    hνperp
  obtain ⟨ε, hε, F, -, -, -, -, -, hdiff⟩ :=
    exists_closedGeodesic_normalLineBundle_tube g le_rfl hnorm hdim p hℓ hunit hper hinj hν
      hνunit hνperp hσ
  obtain ⟨Φ, hs, ht, -⟩ := hdiff 2 (by norm_num) le_rfl
  exact ⟨σ, ε, hε, Φ, hs, ht⟩

end DifferentialGeometry.Geometry.FiniteSoul
