import DifferentialGeometry.Geometry.Comparison.FiniteSoul.NormalTube

/-!
# Consumers of S3-TUBE (lane CMS3-FLOW, G1)

* The frozen statement, verbatim, as an `example`.
* `exists_normalTube_finite_foot`: the SAME tube `(ε, ψ)` with its foot projection `x ↦ π (ψ x)`:
  `C^(r−1)` on the tube, values in `S`, realizing `d_S`, the identity on `S` (input of BASE-2 and of the
  LFR45 / LFR46 hand-off).
* `exists_normalTube_finite_singleton`: the point case (`d = 0`): `ψ x` is a tangent vector at `p` with
  `exp_p (ψ x) = x` and `|ψ x| = d(x, p)` (consistency with CMS-T's `exists_point_normalTube`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M] [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- The frozen S3-TUBE statement, verbatim. -/
example [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {S : Set M} (hSc : IsCompact S) (hSne : S.Nonempty) {d : ℕ}
    (hS : IsEmbeddedSliceOfOrder I (r : ℕ∞ω) d S) :
    ∃ ε > 0, ∃ ψ : M → TangentBundle I M,
      ContMDiffOn I I.tangent ((r - 1 : ℕ∞) : ℕ∞ω) ψ {x | infDist x S < ε} ∧
      (∀ x, infDist x S < ε → ψ x ∈ normalSetFinite g S ∧ g.expMap (ψ x) = x ∧
        Real.sqrt (g.inner (ψ x).proj (ψ x).snd (ψ x).snd) = infDist x S) ∧
      (∀ v ∈ normalSetFinite g S, Real.sqrt (g.inner v.proj v.snd v.snd) < ε →
        ψ (g.expMap v) = v ∧ infDist (g.expMap v) S = Real.sqrt (g.inner v.proj v.snd v.snd)) ∧
      (∀ s ∈ S, ψ s = (⟨s, 0⟩ : TangentBundle I M)) ∧
      ContMDiffOn I 𝓘(ℝ, ℝ) ((r - 1 : ℕ∞) : ℕ∞ω) (fun x => infDist x S)
        {x | 0 < infDist x S ∧ infDist x S < ε} :=
  exists_normalTube_finite g hr hnorm hSc hSne hS

/-- **The tube with its foot projection** (same `(ε, ψ)`): `x ↦ π (ψ x)` is `C^(r−1)` on the tube,
lands in `S`, realizes `d_S`, and fixes `S`. -/
theorem exists_normalTube_finite_foot [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {S : Set M} (hSc : IsCompact S) (hSne : S.Nonempty) {d : ℕ}
    (hS : IsEmbeddedSliceOfOrder I (r : ℕ∞ω) d S) :
    ∃ ε > 0, ∃ ψ : M → TangentBundle I M,
      ContMDiffOn I I.tangent ((r - 1 : ℕ∞) : ℕ∞ω) ψ {x | infDist x S < ε} ∧
      (∀ x, infDist x S < ε → ψ x ∈ normalSetFinite g S ∧ g.expMap (ψ x) = x ∧
        Real.sqrt (g.inner (ψ x).proj (ψ x).snd (ψ x).snd) = infDist x S) ∧
      (∀ v ∈ normalSetFinite g S, Real.sqrt (g.inner v.proj v.snd v.snd) < ε →
        ψ (g.expMap v) = v ∧ infDist (g.expMap v) S = Real.sqrt (g.inner v.proj v.snd v.snd)) ∧
      (∀ s ∈ S, ψ s = (⟨s, 0⟩ : TangentBundle I M)) ∧
      ContMDiffOn I 𝓘(ℝ, ℝ) ((r - 1 : ℕ∞) : ℕ∞ω) (fun x => infDist x S)
        {x | 0 < infDist x S ∧ infDist x S < ε} ∧
      ContMDiffOn I I ((r - 1 : ℕ∞) : ℕ∞ω) (fun x => (ψ x).proj) {x | infDist x S < ε} ∧
      (∀ x, infDist x S < ε → (ψ x).proj ∈ S ∧ dist x (ψ x).proj = infDist x S) := by
  obtain ⟨ε, hε, ψ, hψs, hψ, hψexp, hψS, hdS⟩ := exists_normalTube_finite g hr hnorm hSc hSne hS
  refine ⟨ε, hε, ψ, hψs, hψ, hψexp, hψS, hdS,
    (Bundle.contMDiff_proj (TangentSpace I)).comp_contMDiffOn hψs, fun x hx => ?_⟩
  obtain ⟨hn, hexp, hlen⟩ := hψ x hx
  refine ⟨hn.1, le_antisymm ?_ ?_⟩
  · have h := dist_proj_expMap_le_tube g (one_le_two.trans hr) hnorm (ψ x)
    rw [hexp, dist_comm, hlen] at h
    exact h
  · exact infDist_le_dist_of_mem hn.1

/-- **The point case** (`d = 0`): the tube of `{p}` inverts `exp_p` on the open ball of radius `ε`
with `|ψ x| = d(x, p)`. -/
theorem exists_normalTube_finite_singleton [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ ε > 0, ∃ ψ : M → TangentBundle I M,
      ContMDiffOn I I.tangent ((r - 1 : ℕ∞) : ℕ∞ω) ψ (ball p ε) ∧
      ∀ x ∈ ball p ε, (ψ x).proj = p ∧ g.expMap (ψ x) = x ∧
        Real.sqrt (g.inner p (ψ x).snd (ψ x).snd) = dist x p := by
  obtain ⟨ε, hε, ψ, hψs, hψ, -, -, -⟩ := exists_normalTube_finite g hr hnorm
    (isCompact_singleton (x := p)) (singleton_nonempty p)
    (IsEmbeddedSliceOfOrder.singleton (I := I) (k := r) p)
  have hball : ball p ε = {x | infDist x {p} < ε} := by
    ext x
    simp only [mem_ball, mem_ofPred_eq, infDist_singleton]
  refine ⟨ε, hε, ψ, hball ▸ hψs, fun x hx => ?_⟩
  rw [hball] at hx
  obtain ⟨hn, hexp, hlen⟩ := hψ x hx
  have hp : (ψ x).proj = p := hn.1
  refine ⟨hp, hexp, ?_⟩
  rw [← infDist_singleton, ← hlen, hp]

end DifferentialGeometry.Geometry.FiniteSoul
