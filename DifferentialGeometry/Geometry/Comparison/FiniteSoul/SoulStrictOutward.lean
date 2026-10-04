import DifferentialGeometry.Geometry.Comparison.FiniteSoul.SoulArc
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.SeparationConsumers
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.ShaveConcavity

/-!
# Strict outward directions off the finite surface soul (LFR45.1 in dimension two)

Review of the finite soul design, §3 ("application has no boundary exception"): along a minimizing
segment from `q ∉ S` to the soul `S`, a function `φ` that is Lipschitz and convex along geodesic
arcs in a totally convex `C ⊇ S ∪ {q}` and is smaller on `S` than at `q` drops at once, so the
separation lemma S-SEP gives a unit vector with negative pairing against every minimizing
direction. One kernel (`exists_unit_strict_outward_of_lt`) serves both non-arc layers:
* `q ∉ C₀ = {f ≤ 0}`: `C = M`, `φ = f = rayExhaustion o` (`f q > 0 ≥ f` on `S`);
* `q ∈ C₀ \ C₁`, `C₁ = argmax_{C₀} d(·, ∂C₀)`: `C = C₀`, `φ = -d(·, ∂C₀)` (CMS-B's boundary
  concavity; `q` is not a maximum point, every point of `S ⊆ C₁` is), including `q ∈ ∂C₀`.
The arc layer uses the unique direction to the midpoint (`SoulArc.lean`).

Main statements:
* K1 `lt_left_of_convexOn_Icc`, K2 `exists_unit_strict_outward_of_lt`;
* `exists_soul_of_interior_eq_empty_dim_two`: the last flag set (compact, totally convex, empty
  interior) contains a soul (a point or a simple closed geodesic) with strict outward directions
  at its other points;
* `exists_soul_of_layer_dim_two`: the flag assembly: a layer `C' ⊆ C₀` of this kind whose
  complement in `C₀` is handled by the middle-layer kernel gives the S-SOUL2 conclusion;
* `exists_unit_strict_outward_middle_layer`: the middle layer `q ∈ C₀ \ C₁`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric Filter Topology
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry.FiniteSoul

open DifferentialGeometry.Geometry.Topology (rayExhaustion lipschitzWith_rayExhaustion
  rayExhaustion_nonneg rayExhaustion_self)

/-- **K1.** A function convex on `[0, d]` with `ψ d < ψ 0` is below `ψ 0` on `(0, d]`. -/
theorem lt_left_of_convexOn_Icc {ψ : ℝ → ℝ} {d : ℝ} (hψ : ConvexOn ℝ (Icc 0 d) ψ)
    (hd : ψ d < ψ 0) : ∀ t ∈ Ioc 0 d, ψ t < ψ 0 := by
  intro t ht
  have hd0 : 0 < d := ht.1.trans_le ht.2
  have h0 : (0 : ℝ) ∈ Icc 0 d := ⟨le_rfl, hd0.le⟩
  have hdm : d ∈ Icc 0 d := ⟨hd0.le, le_rfl⟩
  have hb : 0 < t / d := div_pos ht.1 hd0
  have ha : 0 ≤ 1 - t / d := by rw [sub_nonneg, div_le_one hd0]; exact ht.2
  have h := hψ.2 h0 hdm ha hb.le (by ring)
  have ht' : (1 - t / d) • (0 : ℝ) + (t / d) • d = t := by
    rw [smul_eq_mul, smul_eq_mul, mul_zero, zero_add, div_mul_cancel₀ t hd0.ne']
  rw [ht', smul_eq_mul, smul_eq_mul] at h
  have h2 : t / d * (ψ d - ψ 0) < 0 := mul_neg_of_pos_of_neg hb (by linarith)
  nlinarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- **K2.** Strict outward unit vectors from a drop on the soul: `S ⊆ C` closed and nonempty,
`C` totally convex, `φ` Lipschitz and convex along the geodesic arcs in `C`, `q ∈ C \ S` with
`φ < φ q` on `S`. -/
theorem exists_unit_strict_outward_of_lt
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {C S : Set M} (hconv : IsTotallyConvexFinite g C) (hSC : S ⊆ C) (hS : IsClosed S)
    (hSne : S.Nonempty) {φ : M → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ)
    (hφconv : ∀ (p : TangentBundle I M) (ℓ : ℝ), 0 ≤ ℓ →
      (∀ t ∈ Icc 0 ℓ, (g.geodesicFlow p t).proj ∈ C) →
        ConvexOn ℝ (Icc 0 ℓ) (fun t => φ (g.geodesicFlow p t).proj))
    {q : M} (hqC : q ∈ C) (hqS : q ∉ S) (hlt : ∀ s ∈ S, φ s < φ q) :
    ∃ v : E, g.inner q v v = 1 ∧ ∀ u ∈ g.finiteMinimizingDirectionsTo S q, g.inner q v u < 0 := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hD : g.geodesicFlowDomain = univ :=
    Bundle.ContMDiffRiemannianMetric.geodesicFlowDomain_eq_univ g hr hnorm
  have hflowE : ∀ (y : M) (v : E) (τ : ℝ), g.expMap (⟨y, τ • v⟩ : TangentBundle I M) =
      (g.geodesicFlow (⟨y, v⟩ : TangentBundle I M) τ).proj :=
    fun y v τ => g.expMap_smul_eq_proj_geodesicFlow hr1 y v τ (by rw [hD]; exact mem_univ _)
  obtain ⟨hKne, hKc⟩ := g.finiteMinimizingDirectionsTo_nonempty_isCompact hr hnorm hS hSne q
  have hd : 0 < infDist q S := (hS.notMem_iff_infDist_pos hSne).1 hqS
  refine exists_unit_strict_outward_of_descent g hr hnorm hconv hφ hφconv hKc hKne
    fun u hu => ⟨hu.1, infDist q S, hd, ?_⟩
  obtain ⟨-, hend⟩ := hu
  have hseg := hconv.expMap_mem (u := (u : E)) hr hnorm hd.le hqC (hSC hend)
  refine ⟨hseg, ?_⟩
  have hmaps : ∀ t ∈ Icc 0 (infDist q S),
      (g.geodesicFlow (⟨q, (u : E)⟩ : TangentBundle I M) t).proj ∈ C :=
    fun t ht => (congrArg (· ∈ C) (hflowE q u t)).mp (hseg t ht)
  have hψ := hφconv ⟨q, (u : E)⟩ (infDist q S) hd.le hmaps
  have hdrop : φ (g.geodesicFlow (⟨q, (u : E)⟩ : TangentBundle I M) (infDist q S)).proj <
      φ (g.geodesicFlow (⟨q, (u : E)⟩ : TangentBundle I M) 0).proj := by
    rw [g.geodesicFlow_zero hr1]
    exact (congrArg (fun y => φ y < φ q) (hflowE q u (infDist q S))).mp (hlt _ hend)
  intro t ht
  have h := lt_left_of_convexOn_Icc hψ hdrop t ht
  rw [g.geodesicFlow_zero hr1] at h
  exact (congrArg (fun y => φ y < φ q) (hflowE q u t)).mpr h

/-- **The last flag set.** A compact, nonempty, totally convex set with empty interior in a
complete surface contains a soul: a point or a simple closed unit geodesic, compact and totally
convex, with strict outward unit vectors at every other point of the set. (Point and closed
geodesic: the set itself; arc: its midpoint.) -/
theorem exists_soul_of_interior_eq_empty_dim_two
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hdim : Module.finrank ℝ E = 2) {C : Set M} (hCc : IsCompact C) (hCne : C.Nonempty)
    (hconv : IsTotallyConvexFinite g C) (hint : interior C = ∅) :
    ∃ S : Set M, S ⊆ C ∧ S.Nonempty ∧ IsCompact S ∧ IsTotallyConvexFinite g S ∧
      ((∃ x, S = {x}) ∨
        ∃ (p : TangentBundle I M) (ℓ : ℝ), 0 < ℓ ∧ g.inner p.proj p.snd p.snd = 1 ∧
          g.geodesicFlow p ℓ = p ∧ InjOn (fun t => (g.geodesicFlow p t).proj) (Ico 0 ℓ) ∧
          S = range (fun t => (g.geodesicFlow p t).proj)) ∧
      ∀ q ∈ C, q ∉ S → ∃ v : E, g.inner q v v = 1 ∧
        ∀ u ∈ g.finiteMinimizingDirectionsTo S q, g.inner q v u < 0 := by
  rcases totallyConvex_point_or_arc_or_closedGeodesic_dim_two g hr hnorm hdim hCc hCne hconv
      hint with ⟨x, hx⟩ | ⟨p, ℓ, hℓ, hunit, hinj, hC⟩ | ⟨p, ℓ, hℓ, hunit, hper, hinj, hC⟩
  · exact ⟨C, subset_rfl, hCne, hCc, hconv, Or.inl ⟨x, hx⟩, fun q hq hqS => absurd hq hqS⟩
  · have hm : ℓ / 2 ∈ Icc 0 ℓ := ⟨by linarith, by linarith⟩
    refine ⟨{(g.geodesicFlow p (ℓ / 2)).proj}, ?_, singleton_nonempty _, isCompact_singleton,
      isTotallyConvexFinite_singleton_arc g hr hnorm hdim hCc hconv hint hℓ hunit hinj hC hm,
      Or.inl ⟨_, rfl⟩, ?_⟩
    · rw [singleton_subset_iff, hC]
      exact ⟨ℓ / 2, hm, rfl⟩
    · intro q hq hqS
      rw [hC] at hq
      obtain ⟨t₀, ht₀, rfl⟩ := hq
      have hne : t₀ ≠ ℓ / 2 := fun h => hqS (by rw [h]; exact mem_singleton _)
      exact exists_unit_strict_outward_arc g hr hnorm hdim hCc hconv hint hℓ hunit hinj hC ht₀ hm
        hne
  · exact ⟨C, subset_rfl, hCne, hCc, hconv, Or.inr ⟨p, ℓ, hℓ, hunit, hper, hinj, hC⟩,
      fun q hq hqS => absurd hq hqS⟩

/-- **The flag assembly.** Let `C₀ = {f ≤ 0}`, `f = rayExhaustion o`, and let `C' ⊆ C₀` be a
compact, nonempty, totally convex set with empty interior such that every point of `C₀ \ C'` has
strict outward unit vectors towards every closed nonempty `S ⊆ C'`. Then the S-SOUL2 conclusion
holds. -/
theorem exists_soul_of_layer_dim_two
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    (hdim : Module.finrank ℝ E = 2) (o : M) {C' : Set M} (hCc : IsCompact C')
    (hCne : C'.Nonempty) (hconv : IsTotallyConvexFinite g C') (hint : interior C' = ∅)
    (hC'C₀ : C' ⊆ {x : M | rayExhaustion o x ≤ 0})
    (hmid : ∀ S ⊆ C', IsClosed S → S.Nonempty → ∀ q ∈ {x : M | rayExhaustion o x ≤ 0}, q ∉ C' →
      ∃ v : E, g.inner q v v = 1 ∧ ∀ u ∈ g.finiteMinimizingDirectionsTo S q, g.inner q v u < 0) :
    ∃ S : Set M, S.Nonempty ∧ IsCompact S ∧ IsTotallyConvexFinite g S ∧
      ((∃ x, S = {x}) ∨
        ∃ (p : TangentBundle I M) (ℓ : ℝ), 0 < ℓ ∧ g.inner p.proj p.snd p.snd = 1 ∧
          g.geodesicFlow p ℓ = p ∧ InjOn (fun t => (g.geodesicFlow p t).proj) (Ico 0 ℓ) ∧
          S = range (fun t => (g.geodesicFlow p t).proj)) ∧
      ∀ q ∉ S, ∃ v : E, g.inner q v v = 1 ∧
        ∀ u ∈ g.finiteMinimizingDirectionsTo S q, g.inner q v u < 0 := by
  obtain ⟨S, hSC', hSne, hSc, hSconv, hshape, hout⟩ :=
    exists_soul_of_interior_eq_empty_dim_two g hr hnorm hdim hCc hCne hconv hint
  refine ⟨S, hSne, hSc, hSconv, hshape, fun q hqS => ?_⟩
  by_cases hqC' : q ∈ C'
  · exact hout q hqC' hqS
  by_cases hqC₀ : q ∈ {x : M | rayExhaustion o x ≤ 0}
  · exact hmid S hSC' hSc.isClosed hSne q hqC₀ hqC'
  · have hfq : 0 < rayExhaustion o q := lt_of_not_ge hqC₀
    have : ProperSpace M := Manifold.properSpace_of_isRiemannianManifold I
    refine exists_unit_strict_outward_of_lt g hr hnorm (isTotallyConvexFinite_univ g)
      (subset_univ S) hSc.isClosed hSne (lipschitzWith_rayExhaustion o)
      (fun p ℓ _ _ => (convexOn_rayExhaustion_geodesicFlow g hr hnorm hsec o p).subset
        (subset_univ _) (convex_Icc 0 ℓ)) (mem_univ q) hqS fun s hs => ?_
    have : rayExhaustion o s ≤ 0 := hC'C₀ (hSC' hs)
    linarith

/-- **The middle layer** `q ∈ C₀ \ C₁`, `C₁ = argmax_{C₀} d(·, ∂C₀)`: strict outward unit vectors
towards every closed nonempty `S ⊆ C₁` (CMS-B's boundary concavity; no boundary exception). -/
theorem exists_unit_strict_outward_middle_layer
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    (hdim : Module.finrank ℝ E = 2) {C₀ : Set M} (hC₀ : IsClosed C₀)
    (hconv : IsTotallyConvexFinite g C₀) {S : Set M}
    (hS₁ : S ⊆ {x ∈ C₀ | ∀ y ∈ C₀, infDist y (frontier C₀) ≤ infDist x (frontier C₀)})
    (hS : IsClosed S) (hSne : S.Nonempty) {q : M} (hqC₀ : q ∈ C₀)
    (hq₁ : q ∉ {x ∈ C₀ | ∀ y ∈ C₀, infDist y (frontier C₀) ≤ infDist x (frontier C₀)}) :
    ∃ v : E, g.inner q v v = 1 ∧ ∀ u ∈ g.finiteMinimizingDirectionsTo S q, g.inner q v u < 0 := by
  have hr2 : 2 ≤ r := le_trans (by norm_num) hr
  have hqS : q ∉ S := fun h => hq₁ (hS₁ h)
  refine exists_unit_strict_outward_of_lt g hr2 hnorm hconv (fun s hs => (hS₁ hs).1) hS hSne
    (φ := fun x => -infDist x (frontier C₀)) (lipschitz_infDist_pt (frontier C₀)).neg
    (fun p ℓ _ hmaps => (concaveOn_infDist_frontier_geodesicFlow g hr hnorm hsec hdim hC₀ hconv
      p ℓ hmaps).neg) hqC₀ hqS fun s hs => ?_
  have hnot : ¬ ∀ y ∈ C₀, infDist y (frontier C₀) ≤ infDist q (frontier C₀) :=
    fun h => hq₁ ⟨hqC₀, h⟩
  simp only [not_forall, not_le] at hnot
  obtain ⟨y, hy, hlt⟩ := hnot
  have := (hS₁ hs).2 y hy
  change -infDist s (frontier C₀) < -infDist q (frontier C₀)
  linarith

end DifferentialGeometry.Geometry.FiniteSoul
