import DifferentialGeometry.Geometry.Collapse.BoundaryRegisterExtConsumersBSTD2
import DifferentialGeometry.Geometry.Collapse.Inhabitants.DoubleCuspStandingSequenceInstApplications

/-!
# Joint satisfiability of the extended boundary register on the double cusps (lane BSTD2, G1)

The acceptance instance of the extension: with the derivative-control function `A` of the
double-cusp standing sequence (`exists_doubleCusp_standing_sequence_ratio_INST`, lane BDRY-INST;
members `T² × [0, 240]`, two boundary components) and the CHI record `χ` of the closed chain
producer (`exists_chainThresholds_chainE_BSTD2`, GAF01's CHOICE at `cadj`), there is ONE extended
early choice, the double-cusp sequence at `δ₀ = δStar`, ONE extended register and ONE tail such that
every tail member carries the extended output AND every numerical premise of the boundary rows
holds there at once (`BoundaryRegisterPremisesX_BSTD2 E R (n + 1)`: BCF02's eighteen, A2-mk's
block, the stage graph clauses, the closed CHI block, `θ < 1/100`, `θ ≤ ϑ₀`), and the closed chain
producer runs at exactly these numbers. No counterfactual hypothesis.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] BoundaryStandingSequence_BSTD1.conn

/-- **Joint satisfiability on the double cusps** (G1 acceptance instance): one `A`, GAF01's
moduli and CHOICE with `c 2 < cadj`, the closed CHI record `χ`, ONE extended early choice `E`, the
double-cusp standing sequence (two boundary components per member), ONE extended register `R`
over `(E, V)` and `n₀` such that every member `n ≥ n₀` carries the extended output, ALL numerical
premises of the boundary rows at the supply index `n + 1`, and the closed enhanced chain on every
packet at exactly the register's numbers. -/
theorem boundarySequenceAssignmentX_doubleCusp_BSTD2 (K : ℕ) (hK : 10 ≤ K) (Kj : ℕ) {cadj : ℝ}
    (hcadj : 0 < cadj) :
    ∃ A : ℝ → ℝ, ∃ hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w,
    ∃ (Ξ : Fin 3 → ℝ → ℝ) (c Γ Sg cw : Fin 3 → ℝ) (χ : BoundaryChainThresholds_BSTD2),
      c 2 < cadj ∧ ∃ E : BoundaryEarlyChoicesX_BSTD2 K hK A hA χ,
      ∃ S : BoundaryStandingSequence_BSTD1 K A (bdryThresholds_BSTD1 K hK A hA).δStar,
        (∀ n, (S.B n).count = 2) ∧
        ∃ V : ℝ, ∃ R : BoundaryRegisterOverX_BSTD2 E V, ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
          Nonempty (BoundaryMemberOutputX_BSTD2 S n R) ∧
          BoundaryRegisterPremisesX_BSTD2 E R (n + 1) ∧
          ∀ {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
            [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
            {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
            {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Kf : ℕ}
            (P : LocalChartPacketsC14 X g hmetric ρ hρ E.Λ E.β E.Δ E.σs Kf E.σc E.μ E.b E.s E.b'
              E.s' E.ε E.γc E.βc R.Lmax E.τ E.γ R.δlocal E.εr E.e E.T V E.vs E.ζ E.Λz) (x₀ : X),
            ∃ C : Gaf02ChainE P Kj (fun j => Ξ j (Γ j)) Γ Sg χ.eg c cw, C.x₀ = x₀ := by
  obtain ⟨A, hApos, hseq⟩ := exists_doubleCusp_standing_sequence_ratio_INST K
  have hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w := fun w _ _ => hApos w
  obtain ⟨Ξ, c, Γ, Sg, cw, χ, hc2, hchain⟩ := exists_chainThresholds_chainE_BSTD2 Kj hcadj
  obtain ⟨E⟩ := nonempty_boundaryEarlyChoicesX_BSTD2 K hK A hA χ
  have hδ := (bdryThresholds_BSTD1 K hK A hA).δStar_pos
  obtain ⟨W, hW, g, B, hc, hvol, hder⟩ := hseq _ hδ
  let S : BoundaryStandingSequence_BSTD1 K A (bdryThresholds_BSTD1 K hK A hA).δStar :=
    ⟨_, hδ, le_rfl, W, hW, g, B, hvol, hder⟩
  obtain ⟨V, R, n₀, hR⟩ := exists_boundarySequenceAssignmentX_BSTD2 E S
  refine ⟨A, hA, Ξ, c, Γ, Sg, cw, χ, hc2, E, S, hc, V, R, n₀, fun n hn => ⟨hR n hn, ?_,
    fun {X} _ _ _ _ {g hmetric ρ hρ Kf} P x₀ => hchain E R P x₀⟩⟩
  obtain ⟨h⟩ := hR n hn
  exact h.premises_BSTD2

end DifferentialGeometry.Geometry.Collapse
