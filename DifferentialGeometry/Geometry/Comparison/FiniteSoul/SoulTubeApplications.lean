import DifferentialGeometry.Geometry.Comparison.FiniteSoul.SoulTube

/-!
# Consumers of the LFR45 assembly (lane CMS3-FLOW2, G1)

* `exists_finite_soul_strict_outward_tube_dim_three`: LFR45 in dimension three, as the blueprint states
  it (soul of dimension at most two), with the tube of the SAME soul and the punctured-tube regularity
  of `d_S`.
* `infDist_eq_sqrt_tube`: on the tube of the same witness, `d_S = |ψ|` and `d_S (exp (t • ψ x / |ψ x|))`
  is calibrated along the normal ray (the hand-off used by LFR46).
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

/-- **LFR45 in dimension three** (`3 ≤ r`): a soul of relative dimension at most two with strict
outward directions, one normal tube of it, and `d_S` of class `C^(r−1)` on the punctured tube. -/
theorem exists_finite_soul_strict_outward_tube_dim_three [NoncompactSpace M] [ConnectedSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    (hdim : Module.finrank ℝ E = 3) :
    ∃ S : Set M, S.Nonempty ∧ IsCompact S ∧ IsConnected S ∧
      relBoundaryOfOrder I (r : ℕ∞ω) S = ∅ ∧ maxSliceDimOfOrder I (r : ℕ∞ω) S ≤ 2 ∧
      (∀ q ∉ S, ∃ v : E, g.inner q v v = 1 ∧
        ∀ u ∈ g.finiteMinimizingDirectionsTo S q, g.inner q v u < 0) ∧
      ∃ ε > 0, ∃ ψ : M → TangentBundle I M,
        (∀ x, infDist x S < ε → ψ x ∈ normalSetFinite g S ∧ g.expMap (ψ x) = x ∧
          Real.sqrt (g.inner (ψ x).proj (ψ x).snd (ψ x).snd) = infDist x S) ∧
        ContMDiffOn I 𝓘(ℝ, ℝ) ((r - 1 : ℕ∞) : ℕ∞ω) (fun x => infDist x S)
          {x | 0 < infDist x S ∧ infDist x S < ε} := by
  have : NeZero (Module.finrank ℝ E) := ⟨by rw [hdim]; norm_num⟩
  obtain ⟨S, hSne, hSc, hSconn, -, -, hrel, hd, -, hout, ε, hε, ψ, -, hψ, -, -, hdS, -⟩ :=
    exists_finite_soul_strict_outward_tube_data g hr hnorm hsec
  exact ⟨S, hSne, hSc, hSconn, hrel, by omega, hout, ε, hε, ψ, hψ, hdS⟩

/-- **The hand-off to LFR46**: for the SAME soul and tube, the foot of every point of the tube lies
in `S`, the tube vector at the foot is zero exactly on `S`, and `d_S = |ψ|`. -/
theorem infDist_eq_sqrt_tube [NeZero (Module.finrank ℝ E)] [NoncompactSpace M] [ConnectedSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂) :
    ∃ S : Set M, IsCompact S ∧ ∃ ε > 0, ∃ ψ : M → TangentBundle I M,
      ∀ x, infDist x S < ε → (ψ x).proj ∈ S ∧
        (ψ x = (⟨(ψ x).proj, 0⟩ : TangentBundle I M) ↔ x ∈ S) ∧
        g.inner (ψ x).proj (ψ x).snd (ψ x).snd = infDist x S ^ 2 := by
  obtain ⟨S, -, hSc, -, -, -, -, -, -, -, ε, hε, ψ, -, hψ, -, hψS, -, -, hfootS⟩ :=
    exists_finite_soul_strict_outward_tube_data g hr hnorm hsec
  refine ⟨S, hSc, ε, hε, ψ, fun x hx => ⟨(hfootS x hx).1, ⟨fun h => ?_, fun h => ?_⟩, ?_⟩⟩
  · obtain ⟨-, hexp, -⟩ := hψ x hx
    have hx' : g.expMap (⟨(ψ x).proj, 0⟩ : TangentBundle I M) = x := by rw [← h]; exact hexp
    rw [g.expMap_zero (le_trans (by norm_num) hr)] at hx'
    rw [← hx']
    exact (hfootS x hx).1
  · rw [hψS x h]
  · obtain ⟨-, -, hlen⟩ := hψ x hx
    have h0 : 0 ≤ g.inner (ψ x).proj (ψ x).snd (ψ x).snd := by
      by_cases hw : (ψ x).snd = 0
      · rw [hw]; simp
      · exact (g.pos _ _ hw).le
    rw [← hlen, Real.sq_sqrt h0]

end DifferentialGeometry.Geometry.FiniteSoul
