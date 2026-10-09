import DifferentialGeometry.Geometry.Collapse.LocalExport.ZeroModelBall

/-!
# Consumers of the LC80 zero-model balls (LC87 item 3 for the zero family)

* `ZeroModelBall.contMDiff_cutoff`: the LC31 cutoff `Φ ∘ radial` of a zero-model ball is globally
  smooth.
* `ZeroModelBall.tsupport_cutoff_subset_ball`: its closed support lies in the physical ball
  `B(center, (9/10 + e) radius)`, hence strictly inside the ball domain when `e < 1/10`.
* `ZeroModelFamily.disjoint_tsupport_cutoff`: in a zero-model family with `e < 1/10` the cutoff
  supports of distinct centres are pairwise disjoint (LC87's "cutoffs with supports strictly inside
  their smooth domains" and the disjointness of the zero cutoffs).
* `ZeroModelFamily.exists_mem_tenth_ball`: every point of the zero stratum lies in the tenth-radius
  ball of some selected zero-model ball.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Real Metric
open scoped Topology ContDiff Manifold
open GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Analysis.Calculus

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type} [mM : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {g : SmoothRiemannianMetric I M} {ι : Type} {N C : ι → Type}
  [∀ b, MetricSpace (N b)] [∀ b, ChartedSpace H (N b)] [∀ b, MetricSpace (C b)]
  {o : ∀ b, C b} {δ ε e : ℝ}

/-- The LC31 cutoff of a zero-model ball is globally smooth. -/
theorem ZeroModelBall.contMDiff_cutoff (z : ZeroModelBall I M g N C o δ ε e) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => annularCutoff cutoffProfile (z.radial x)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, L, -, -, hsm, -⟩ := z.radial_spec
  exact hsm

/-- The closed support of the LC31 cutoff of a zero-model ball lies in the physical ball
`B(center, (9/10 + e) radius)`. -/
theorem ZeroModelBall.tsupport_cutoff_subset_ball (z : ZeroModelBall I M g N C o δ ε e) :
    tsupport (fun x => annularCutoff cutoffProfile (z.radial x)) ⊆
      ball z.center ((9 / 10 + e) * z.radius) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, L, -, -, -, -, -, hts, -⟩ := z.radial_spec
  intro x hx
  have h : z.radius⁻¹ * dist x z.center < 9 / 10 + e := (hts hx).2
  rw [mem_ball]
  have := (inv_mul_lt_iff₀ z.radius_pos).mp h
  linarith

/-- In a zero-model family with value error `e < 1/10`, the cutoff supports of distinct selected
centres are pairwise disjoint. -/
theorem ZeroModelFamily.disjoint_tsupport_cutoff {ρ : M → ℝ} {hρ : ∀ p, 0 < ρ p} {β : ℕ → ℝ}
    {T V : ℝ} (F : ZeroModelFamily I M g ρ hρ β N C o δ ε e T V) (he : e < 1 / 10)
    {i j : M} (hi : i ∈ F.centres) (hj : j ∈ F.centres) (hij : i ≠ j) :
    Disjoint (tsupport (fun x => annularCutoff cutoffProfile ((F.zero i hi).radial x)))
      (tsupport (fun x => annularCutoff cutoffProfile ((F.zero j hj).radial x))) := by
  have hsub : ∀ k (hk : k ∈ F.centres),
      tsupport (fun x => annularCutoff cutoffProfile ((F.zero k hk).radial x)) ⊆
        ball k (F.zero k hk).radius := fun k hk => by
    refine (ZeroModelBall.tsupport_cutoff_subset_ball (F.zero k hk)).trans ?_
    rw [F.zero_center k hk]
    exact ball_subset_ball (by nlinarith [(F.zero k hk).radius_pos])
  exact (F.disjoint i hi j hj hij).mono (hsub i hi) (hsub j hj)

/-- Every point of the zero stratum lies in the tenth-radius ball of a selected zero-model ball. -/
theorem ZeroModelFamily.exists_mem_tenth_ball {ρ : M → ℝ} {hρ : ∀ p, 0 < ρ p} {β : ℕ → ℝ}
    {T V : ℝ} (F : ZeroModelFamily I M g ρ hρ β N C o δ ε e T V) {q : M}
    (hq : q ∈ scaledSplittingStratum.{0, 0} ρ hρ β 0) :
    ∃ i, ∃ hi : i ∈ F.centres, q ∈ ball i ((F.zero i hi).radius / 10) := by
  have h := F.covers_stratum hq
  simp only [mem_iUnion] at h
  exact h

end DifferentialGeometry.Geometry.Collapse
