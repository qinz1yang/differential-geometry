import DifferentialGeometry.Geometry.Comparison.FiniteSoul.TubeHalfBandGluing
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.ClosedGeodesicCylinder
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.ClosedGeodesicUnitNormal
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.BandProduct

/-!
# S6 from the soul: plane or cylinder, as a HOMEOMORPHISM (disposition D7)

Package CM-S (finite soul), lane CMS-T, part C. The soul enters only through explicit hypotheses
in the output shape of S-SOUL2 (`exists_finite_soul_strict_outward_dim_two`): `S` is a point or a
simple closed unit geodesic, and every `q ∉ S` carries a unit vector with strictly negative pairing
against all minimizing directions to `S`.

* `exists_halfBand_product_of_strict_outward` (S-PATCH + S-FLOW + S-HIT, CMS-H): for a compact
  nonempty `S` with that outward data, `{d_S = a} × [a, ∞) ≃ₜ {d_S ≥ a}`, identity on the level,
  second coordinate = `d_S`.
* `exists_homeomorph_tangentSpace_of_point_soul`: a point soul gives `F : T_x M ≃ₜ M` with
  `d_x(F v) = |v|_{g_x}` (any dimension; tube of `exp_x` glued to the exterior product).
* `exists_homeomorph_cylinder_of_closedGeodesic_soul`: a closed-geodesic soul on an oriented
  surface gives `F : AddCircle 1 × ℝ ≃ₜ M` with `d_S(F q) = |q.2|`.
* `nonempty_homeomorph_plane_or_cylinder_of_soul`: S6 for the S-SOUL2 output.
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

/-- **The exterior product from the soul's outward data** (S-PATCH + S-FLOW + S-HIT of lane
CMS-H): `{d_S = a} × [a, ∞) ≃ₜ {d_S ≥ a}` along one smooth outward flow, the identity on the level
`a` and carrying the second coordinate to `d_S`. -/
theorem exists_halfBand_product_of_strict_outward [NeZero (Module.finrank ℝ E)]
    [SigmaCompactSpace M] [CompleteSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {S : Set M} (hS : IsCompact S) (hSne : S.Nonempty)
    (hout : ∀ q ∉ S, ∃ v : E, g.inner q v v = 1 ∧
      ∀ u ∈ g.finiteMinimizingDirectionsTo S q, g.inner q v u < 0) {a : ℝ} (ha : 0 < a) :
    ∃ e : ({x : M // infDist x S = a} × Ici a) ≃ₜ {x : M // infDist x S ∈ Ici a},
      (∀ p, infDist (e p : M) S = p.2) ∧ ∀ x, (e (x, ⟨a, self_mem_Ici⟩) : M) = x := by
  have hnot : ∀ x : M, a ≤ infDist x S → x ∉ S := fun x hx hxS => by
    rw [infDist_zero_of_mem hxS] at hx
    linarith
  have hout' : ∀ x : M, ∃ w : TangentSpace I x, x ∉ S → g.inner x w w = 1 ∧
      ∀ u ∈ g.finiteMinimizingDirectionsTo S x, g.inner x w u < 0 := fun x => by
    by_cases hx : x ∈ S
    · exact ⟨0, fun h => absurd hx h⟩
    · obtain ⟨w, hw⟩ := hout x hx
      exact ⟨w, fun _ => hw⟩
  choose v hv using hout'
  have hvspec : ∀ x, a ≤ infDist x S → g.inner x (v x) (v x) = 1 ∧
      ∀ u ∈ g.finiteMinimizingDirectionsTo S x, g.inner x (v x) u < 0 := fun x hx =>
    hv x (hnot x hx)
  have hA : IsClosed {x : M | a ≤ infDist x S} :=
    isClosed_le continuous_const (continuous_infDist_pt S)
  obtain ⟨V, hV, hVR, O, -, hAO, hOout⟩ :=
    exists_contMDiff_outward_field_minimizingDirections g hr hnorm hS.isClosed hA two_pos v
      (c := 0) (fun x hx => by rw [(hvspec x hx).1]; norm_num)
      (fun x hx u hu => by rw [neg_zero]; exact (hvspec x hx).2 u hu)
  obtain ⟨-, -, -, -, -, -, -, e, -, -, -, he4, he5⟩ := exists_flow_infDist_halfBand_product g hr
    hnorm hS hSne (n := ⊤) le_top V hV (B := 2) (fun x => (hVR x).le) ha (c := a) self_mem_Ici
    (fun x hx u hu => by have := hOout x (hAO hx) u hu; rwa [neg_zero] at this)
  exact ⟨e, he4, he5⟩

/-- **A point soul** (S6, point case, any dimension): the tube of `exp_x` and the exterior product
glue to a homeomorphism `F : T_x M ≃ₜ M` with `d_x(F v) = |v|_{g_x}`. -/
theorem exists_homeomorph_tangentSpace_of_point_soul [NeZero (Module.finrank ℝ E)]
    [SigmaCompactSpace M] [CompleteSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (x : M) (hout : ∀ q ∉ ({x} : Set M), ∃ v : E, g.inner q v v = 1 ∧
      ∀ u ∈ g.finiteMinimizingDirectionsTo {x} q, g.inner q v u < 0) :
    ∃ F : E ≃ₜ M, ∀ v, infDist (F v) {x} = Real.sqrt (g.inner x v v) := by
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
  have hT : ∀ p, η (T p) = ρ p := fun p => by
    have hp : (p : E) ∈ Φ.source := by
      rw [hsrc]
      exact (Real.sqrt_lt' hε).mp p.2
    exact (hΦ p hp).2
  have ha : 0 < ε / 2 := half_pos hε
  obtain ⟨eP, -, heP, heP0⟩ := exists_smul_sqrt_halfBand_product (V := E) (g.inner x) ha
  obtain ⟨eM, heM, heM0⟩ := exists_halfBand_product_of_strict_outward g hr hnorm
    (isCompact_singleton (x := x)) (singleton_nonempty x) hout ha
  obtain ⟨F, hF, -⟩ := exists_homeomorph_tube_halfBand_glue hρ hη (half_lt_self hε) T hT eP heP
    heP0 eM heM heM0
  exact ⟨F, hF⟩

/-- **A closed-geodesic soul on an oriented surface** (S6, cylinder case): the orientable tube
`S¹ × (−ε, ε)` and the exterior product glue to `F : AddCircle 1 × ℝ ≃ₜ M` with
`d_S(F q) = |q.2|`, `S = range γ`. -/
theorem exists_homeomorph_cylinder_of_closedGeodesic_soul [SigmaCompactSpace M] [CompleteSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hdim : Module.finrank ℝ E = 2) (p : TangentBundle I M) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hunit : g.inner p.proj p.snd p.snd = 1) (hper : g.geodesicFlow p ℓ = p)
    (hinj : InjOn (fun t => (g.geodesicFlow p t).proj) (Ico 0 ℓ))
    (o : DifferentialGeometry.ManifoldOrientation I M 2)
    (hout : ∀ q ∉ range (fun t => (g.geodesicFlow p t).proj), ∃ v : E, g.inner q v v = 1 ∧
      ∀ u ∈ g.finiteMinimizingDirectionsTo (range fun t => (g.geodesicFlow p t).proj) q,
        g.inner q v u < 0) :
    ∃ F : AddCircle (1 : ℝ) × ℝ ≃ₜ M,
      ∀ q, infDist (F q) (range fun t => (g.geodesicFlow p t).proj) = |q.2| := by
  have : NeZero (Module.finrank ℝ E) := ⟨by rw [hdim]; norm_num⟩
  set S := range fun t => (g.geodesicFlow p t).proj with hSdef
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hdom := g.geodesicFlowDomain_eq_univ hr hnorm
  have hS : IsCompact S := isCompact_range_geodesicFlow g hr1 hdom hℓ hper
  have hSne : S.Nonempty := range_nonempty _
  obtain ⟨ν, hν, hνunit, hνperp⟩ :=
    exists_unitNormal_closedGeodesic_dim_two g hr hnorm hdim p hℓ hunit hper
  obtain ⟨-, ε, hε, F₀, -, hcal, e, he⟩ := exists_closedGeodesic_cylinderTube_of_orientation g hr
    hnorm hdim p hℓ hunit hper hinj hν hνunit hνperp o
  set ρ : AddCircle (1 : ℝ) × ℝ → ℝ := fun q => |q.2| with hρdef
  set η : M → ℝ := fun y => infDist y S with hηdef
  have hρ : Continuous ρ := continuous_abs.comp continuous_snd
  have hη : Continuous η := continuous_infDist_pt _
  set T : {q : AddCircle (1 : ℝ) × ℝ // ρ q < ε} ≃ₜ {y : M // η y < ε} := e with hTdef
  have hT : ∀ q, η (T q) = ρ q := fun q => by
    change infDist (e q : M) S = |(q : AddCircle (1 : ℝ) × ℝ).2|
    rw [he]
    exact hcal q q.2
  have ha : 0 < ε / 2 := half_pos hε
  obtain ⟨eP, -, heP, heP0⟩ := exists_cylinder_halfBand_product ha
  obtain ⟨eM, heM, heM0⟩ := exists_halfBand_product_of_strict_outward g hr hnorm hS hSne hout ha
  obtain ⟨F, hF, -⟩ := exists_homeomorph_tube_halfBand_glue hρ hη (half_lt_self hε) T hT eP heP
    heP0 eM heM heM0
  exact ⟨F, hF⟩

/-- **S6 for the S-SOUL2 output** (D7: a homeomorphism statement): a point soul gives the plane,
a simple closed geodesic soul of an oriented surface gives the cylinder. -/
theorem nonempty_homeomorph_plane_or_cylinder_of_soul [SigmaCompactSpace M] [CompleteSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hdim : Module.finrank ℝ E = 2) (o : DifferentialGeometry.ManifoldOrientation I M 2)
    {S : Set M}
    (hshape : (∃ x, S = {x}) ∨
      ∃ (p : TangentBundle I M) (ℓ : ℝ), 0 < ℓ ∧ g.inner p.proj p.snd p.snd = 1 ∧
        g.geodesicFlow p ℓ = p ∧ InjOn (fun t => (g.geodesicFlow p t).proj) (Ico 0 ℓ) ∧
        S = range (fun t => (g.geodesicFlow p t).proj))
    (hout : ∀ q ∉ S, ∃ v : E, g.inner q v v = 1 ∧
      ∀ u ∈ g.finiteMinimizingDirectionsTo S q, g.inner q v u < 0) :
    Nonempty (M ≃ₜ EuclideanSpace ℝ (Fin 2)) ∨ Nonempty (M ≃ₜ AddCircle (1 : ℝ) × ℝ) := by
  have : NeZero (Module.finrank ℝ E) := ⟨by rw [hdim]; norm_num⟩
  rcases hshape with ⟨x, rfl⟩ | ⟨p, ℓ, hℓ, hunit, hper, hinj, rfl⟩
  · obtain ⟨F, -⟩ := exists_homeomorph_tangentSpace_of_point_soul g hr hnorm x hout
    have hE : Module.finrank ℝ E = Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) := by
      rw [hdim, finrank_euclideanSpace_fin]
    exact Or.inl ⟨F.symm.trans (ContinuousLinearEquiv.ofFinrankEq hE).toHomeomorph⟩
  · obtain ⟨F, -⟩ := exists_homeomorph_cylinder_of_closedGeodesic_soul g hr hnorm hdim p hℓ hunit
      hper hinj o hout
    exact Or.inr ⟨F.symm⟩

end DifferentialGeometry.Geometry.FiniteSoul
