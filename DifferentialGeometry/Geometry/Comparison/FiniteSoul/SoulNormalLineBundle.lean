import DifferentialGeometry.Geometry.Comparison.FiniteSoul.SoulPlaneCylinder

/-!
# The surface is the normal bundle of its soul (dimension-two LFR21 output, no orientation)

Package CM-S (finite soul), lane CMS-T, part C5. Same soul hypotheses as
`FiniteSoul/SoulPlaneCylinder.lean` (the output shape of S-SOUL2), but WITHOUT an orientation:

* `NormalLineBundle.fiberScale`: the fibrewise scaling `[t, h] ↦ [t, s h]` of the normal line
  bundle `(ℝ × ℝ) / ((t + 1, h) ∼ (t, σ h))`, jointly continuous, with `|s h| = |s| |h|`.
* `exists_homeomorph_normalLineBundle_of_closedGeodesic_soul`: a simple closed unit geodesic soul
  of a surface gives `F : NormalLineBundle σ ≃ₜ M` (`σ` the holonomy of a continuous unit normal
  `ν`), calibrated by `d_S(F q) = |q|`, equal to the normal exponential
  `[t, h] ↦ exp_{γ(ℓ t)}(h ν(ℓ t))` on a uniform tube and sending the zero section onto `S`
  (σ = −1 is the open Möbius band, σ = 1 the cylinder).
* `exists_homeomorph_tangentSpace_exp_of_point_soul`: a point soul gives `F : T_x M ≃ₜ M`,
  calibrated and equal to `exp_x` on a uniform ball.
* `nonempty_homeomorph_plane_or_normalLineBundle_of_soul`: S6 without orientation.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

namespace NormalLineBundle

variable (σ : ℤˣ)

/-- **Fibrewise scaling** `[t, h] ↦ [t, s h]` (well defined: it commutes with the deck action). -/
def fiberScale (s : ℝ) : NormalLineBundle σ → NormalLineBundle σ :=
  Quotient.lift (fun z : NormalCover σ => mk σ (NormalCover.time σ z) (s * NormalCover.fiber σ z))
    (by
      intro a b hab
      obtain ⟨n, rfl⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hab)
      change mk σ (NormalCover.time σ (n • b)) (s * NormalCover.fiber σ (n • b)) =
        mk σ (NormalCover.time σ b) (s * NormalCover.fiber σ b)
      rw [NormalCover.smul_def, NormalCover.time_mk, NormalCover.fiber_mk, mul_left_comm s]
      exact mk_add_int σ _ _ _)

theorem fiberScale_mk (s t h : ℝ) : fiberScale σ s (mk σ t h) = mk σ t (s * h) := rfl

theorem continuous_fiberScale :
    Continuous (fun q : ℝ × NormalLineBundle σ => fiberScale σ q.1 q.2) := by
  have hq : Topology.IsQuotientMap (Prod.map (id : ℝ → ℝ) (proj σ)) :=
    (IsOpenMap.id.prodMap (isOpenMap_proj σ)).isQuotientMap
      (continuous_id.prodMap (continuous_proj σ))
      (Function.surjective_id.prodMap (proj_surjective σ))
  rw [hq.continuous_iff]
  exact (continuous_mk σ).comp (((NormalCover.continuous_time σ).comp continuous_snd).prodMk
    (continuous_fst.mul ((NormalCover.continuous_fiber σ).comp continuous_snd)))

theorem fiberAbs_fiberScale (s : ℝ) (q : NormalLineBundle σ) :
    fiberAbs σ (fiberScale σ s q) = |s| * fiberAbs σ q := by
  obtain ⟨z, rfl⟩ := proj_surjective σ q
  change |s * NormalCover.fiber σ z| = |s| * |NormalCover.fiber σ z|
  exact abs_mul _ _

theorem fiberScale_one (q : NormalLineBundle σ) : fiberScale σ 1 q = q := by
  obtain ⟨z, rfl⟩ := proj_surjective σ q
  change mk σ (NormalCover.time σ z) (1 * NormalCover.fiber σ z) = proj σ z
  rw [one_mul]
  rfl

theorem fiberScale_fiberScale (s t : ℝ) (q : NormalLineBundle σ) :
    fiberScale σ s (fiberScale σ t q) = fiberScale σ (s * t) q := by
  obtain ⟨z, rfl⟩ := proj_surjective σ q
  change mk σ (NormalCover.time σ z) (s * (t * NormalCover.fiber σ z)) =
    mk σ (NormalCover.time σ z) (s * t * NormalCover.fiber σ z)
  rw [mul_assoc]

/-- **The model half-band product of the normal line bundle**:
`{|q| = a} × [a, ∞) ≃ₜ {|q| ≥ a}` by fibrewise scaling. -/
theorem exists_halfBand_product {a : ℝ} (ha : 0 < a) :
    ∃ e : ({q : NormalLineBundle σ // fiberAbs σ q = a} × Ici a) ≃ₜ
        {q : NormalLineBundle σ // fiberAbs σ q ∈ Ici a},
      (∀ z, (e z : NormalLineBundle σ) = fiberScale σ ((z.2 : ℝ) / a) z.1) ∧
      (∀ z, fiberAbs σ (e z) = z.2) ∧ ∀ z, (e (z, ⟨a, self_mem_Ici⟩) : NormalLineBundle σ) = z :=
  exists_scaling_halfBand_product (continuous_fiberAbs σ) (fiberScale σ) (continuous_fiberScale σ)
    (fiberScale_one σ) (fiberScale_fiberScale σ)
    (fun t q ht => by rw [fiberAbs_fiberScale, abs_of_nonneg ht]) ha

end NormalLineBundle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- **A closed-geodesic soul, no orientation** (dimension-two LFR21 output): the surface is
homeomorphic to the normal line bundle of its soul, by a calibrated homeomorphism that is the
normal exponential map on a uniform tube and sends the zero section onto the soul. -/
theorem exists_homeomorph_normalLineBundle_of_closedGeodesic_soul [SigmaCompactSpace M]
    [CompleteSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hdim : Module.finrank ℝ E = 2) (p : TangentBundle I M) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hunit : g.inner p.proj p.snd p.snd = 1) (hper : g.geodesicFlow p ℓ = p)
    (hinj : InjOn (fun t => (g.geodesicFlow p t).proj) (Ico 0 ℓ))
    (hout : ∀ q ∉ range (fun t => (g.geodesicFlow p t).proj), ∃ v : E, g.inner q v v = 1 ∧
      ∀ u ∈ g.finiteMinimizingDirectionsTo (range fun t => (g.geodesicFlow p t).proj) q,
        g.inner q v u < 0) :
    ∃ ν : ℝ → E,
      Continuous (fun t => (⟨(g.geodesicFlow p t).proj, ν t⟩ : TangentBundle I M)) ∧
      (∀ t, g.inner (g.geodesicFlow p t).proj (ν t) (ν t) = 1) ∧
      (∀ t, g.inner (g.geodesicFlow p t).proj (ν t) (g.geodesicFlow p t).snd = 0) ∧
      ∃ σ : ℤˣ, (∀ t, ν (t + ℓ) = ((σ : ℤ) : ℝ) • ν t) ∧
        ∃ F : NormalLineBundle σ ≃ₜ M,
          (∀ q, infDist (F q) (range fun t => (g.geodesicFlow p t).proj) =
            NormalLineBundle.fiberAbs σ q) ∧
          (∀ t, F (NormalLineBundle.mk σ t 0) = (g.geodesicFlow p (ℓ * t)).proj) ∧
          ∃ δ > 0, ∀ t h : ℝ, |h| ≤ δ → F (NormalLineBundle.mk σ t h) =
            g.expMap (⟨(g.geodesicFlow p (ℓ * t)).proj, h • ν (ℓ * t)⟩ : TangentBundle I M) := by
  have : NeZero (Module.finrank ℝ E) := ⟨by rw [hdim]; norm_num⟩
  set S := range fun t => (g.geodesicFlow p t).proj with hSdef
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hdom := g.geodesicFlowDomain_eq_univ hr hnorm
  have hS : IsCompact S := isCompact_range_geodesicFlow g hr1 hdom hℓ hper
  have hSne : S.Nonempty := range_nonempty _
  obtain ⟨ν, hν, hνunit, hνperp⟩ :=
    exists_unitNormal_closedGeodesic_dim_two g hr hnorm hdim p hℓ hunit hper
  obtain ⟨σ, hσ, ε, hε, F₀, hFexp, hF0, hcal, e, he⟩ :=
    exists_closedGeodesic_normalTube_homeomorph g hr hnorm hdim p hℓ hunit hper hinj hν hνunit
      hνperp
  set η : M → ℝ := fun y => infDist y S with hηdef
  have hρ : Continuous (NormalLineBundle.fiberAbs σ) := NormalLineBundle.continuous_fiberAbs σ
  have hη : Continuous η := continuous_infDist_pt _
  set T : {q : NormalLineBundle σ // NormalLineBundle.fiberAbs σ q < ε} ≃ₜ {y : M // η y < ε} := e with hTdef
  have hT : ∀ q, η (T q) = NormalLineBundle.fiberAbs σ q := fun q => by
    change infDist (e q : M) S = NormalLineBundle.fiberAbs σ (q : NormalLineBundle σ)
    rw [he]
    exact hcal q q.2
  have ha : 0 < ε / 2 := half_pos hε
  obtain ⟨eP, -, heP, heP0⟩ := NormalLineBundle.exists_halfBand_product σ ha
  obtain ⟨eM, heM, heM0⟩ := exists_halfBand_product_of_strict_outward g hr hnorm hS hSne hout ha
  obtain ⟨F, hF, hFT⟩ := exists_homeomorph_tube_halfBand_glue hρ hη (half_lt_self hε) T hT eP heP
    heP0 eM heM heM0
  have hFtube : ∀ t h : ℝ, |h| ≤ ε / 2 → F (NormalLineBundle.mk σ t h) = F₀ (NormalLineBundle.mk σ t h) :=
    fun t h hh => by
      have hlt : NormalLineBundle.fiberAbs σ (NormalLineBundle.mk σ t h) < ε := by
        change |h| < ε
        linarith
      rw [hFT _ hlt hh]
      exact he _
  refine ⟨ν, hν, hνunit, hνperp, σ, hσ, F, hF, fun t => ?_, ε / 2, ha, fun t h hh => ?_⟩
  · rw [hFtube t 0 (by rw [abs_zero]; exact ha.le)]
    exact hF0 t
  · rw [hFtube t h hh]
    exact hFexp t h

/-- **A point soul, with the exponential map** (any dimension): `F : T_x M ≃ₜ M`, calibrated by
`d_x(F v) = |v|_{g_x}` and equal to `exp_x` on a uniform `g_x`-ball. -/
theorem exists_homeomorph_tangentSpace_exp_of_point_soul [NeZero (Module.finrank ℝ E)]
    [SigmaCompactSpace M] [CompleteSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (x : M) (hout : ∀ q ∉ ({x} : Set M), ∃ v : E, g.inner q v v = 1 ∧
      ∀ u ∈ g.finiteMinimizingDirectionsTo {x} q, g.inner q v u < 0) :
    ∃ F : E ≃ₜ M, (∀ v, infDist (F v) {x} = Real.sqrt (g.inner x v v)) ∧
      ∃ δ > 0, ∀ v : E, Real.sqrt (g.inner x v v) ≤ δ → F v = g.expMap (⟨x, v⟩ : TangentBundle I M) := by
  obtain ⟨ε, hε, Φ, hsrc, htgt, -, hΦ⟩ := exists_point_normalTube g hr hnorm x
  set ρ : E → ℝ := fun v => Real.sqrt (g.inner x v v) with hρdef
  set η : M → ℝ := fun y => infDist y {x} with hηdef
  have hρ : Continuous ρ :=
    Real.continuous_sqrt.comp ((g.inner x).continuous₂.comp (continuous_id.prodMk continuous_id))
  have hη : Continuous η := continuous_infDist_pt _
  have hsrc' : {v : E | ρ v < ε} = Φ.toOpenPartialHomeomorph.source := by
    change {v : E | ρ v < ε} = Φ.source
    rw [hsrc]
    ext v
    exact Real.sqrt_lt' hε
  have htgt' : Φ.toOpenPartialHomeomorph.target = {y : M | η y < ε} := by
    change Φ.target = {y : M | η y < ε}
    rw [htgt]
  set T : {v : E // ρ v < ε} ≃ₜ {y : M // η y < ε} :=
    (Homeomorph.setCongr hsrc').trans
      (Φ.toOpenPartialHomeomorph.toHomeomorphSourceTarget.trans (Homeomorph.setCongr htgt'))
    with hTdef
  have hmem : ∀ v : E, ρ v < ε → v ∈ Φ.source := fun v hv => by
    rw [hsrc]
    exact (Real.sqrt_lt' hε).mp hv
  have hT : ∀ p, η (T p) = ρ p := fun p => (hΦ p (hmem p p.2)).2
  have ha : 0 < ε / 2 := half_pos hε
  obtain ⟨eP, -, heP, heP0⟩ := exists_smul_sqrt_halfBand_product (V := E) (g.inner x) ha
  obtain ⟨eM, heM, heM0⟩ := exists_halfBand_product_of_strict_outward g hr hnorm
    (isCompact_singleton (x := x)) (singleton_nonempty x) hout ha
  obtain ⟨F, hF, hFT⟩ := exists_homeomorph_tube_halfBand_glue hρ hη (half_lt_self hε) T hT eP heP
    heP0 eM heM heM0
  refine ⟨F, hF, ε / 2, ha, fun v hv => ?_⟩
  have hlt : ρ v < ε := lt_of_le_of_lt hv (half_lt_self hε)
  rw [hFT v hlt hv]
  exact (hΦ v (hmem v hlt)).1

/-- **S6 without orientation**: a point soul gives the plane; a simple closed geodesic soul gives
the normal line bundle of holonomy `σ` (cylinder for `σ = 1`, open Möbius band for `σ = −1`). -/
theorem nonempty_homeomorph_plane_or_normalLineBundle_of_soul [SigmaCompactSpace M]
    [CompleteSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hdim : Module.finrank ℝ E = 2) {S : Set M}
    (hshape : (∃ x, S = {x}) ∨
      ∃ (p : TangentBundle I M) (ℓ : ℝ), 0 < ℓ ∧ g.inner p.proj p.snd p.snd = 1 ∧
        g.geodesicFlow p ℓ = p ∧ InjOn (fun t => (g.geodesicFlow p t).proj) (Ico 0 ℓ) ∧
        S = range (fun t => (g.geodesicFlow p t).proj))
    (hout : ∀ q ∉ S, ∃ v : E, g.inner q v v = 1 ∧
      ∀ u ∈ g.finiteMinimizingDirectionsTo S q, g.inner q v u < 0) :
    Nonempty (M ≃ₜ EuclideanSpace ℝ (Fin 2)) ∨ ∃ σ : ℤˣ, Nonempty (M ≃ₜ NormalLineBundle σ) := by
  have : NeZero (Module.finrank ℝ E) := ⟨by rw [hdim]; norm_num⟩
  rcases hshape with ⟨x, rfl⟩ | ⟨p, ℓ, hℓ, hunit, hper, hinj, rfl⟩
  · obtain ⟨F, -⟩ := exists_homeomorph_tangentSpace_of_point_soul g hr hnorm x hout
    have hE : Module.finrank ℝ E = Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) := by
      rw [hdim, finrank_euclideanSpace_fin]
    exact Or.inl ⟨F.symm.trans (ContinuousLinearEquiv.ofFinrankEq hE).toHomeomorph⟩
  · obtain ⟨-, -, -, -, σ, -, F, -⟩ := exists_homeomorph_normalLineBundle_of_closedGeodesic_soul g
      hr hnorm hdim p hℓ hunit hper hinj hout
    exact Or.inr ⟨σ, ⟨F.symm⟩⟩

end DifferentialGeometry.Geometry.FiniteSoul
