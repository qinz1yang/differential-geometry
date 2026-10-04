import DifferentialGeometry.Geometry.Collapse.SelectedZeroPacketsOriginalBuffer

/-!
# Consumer of LCP04: each zero-stratum point sits in one selected packet

`exists_selected_zero_packets_of_original_buffer` applied once: every point `q` of the LC16 zero
stratum lies in the open tenth-radius ball of a selected center `i`; that center's whole closed
shell `[r_i/10, 10 r_i]` has nonzero rank and carries the ORIGINAL radial coordinate
`(ρ x)⁻¹ (d(i,·) - d(i,x))`; and the model attached to `i` has at most one end. The hypotheses
at the selected centers are the original buffer and the original model, cone, map and radial
function data — no comparison hypothesis.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric
open scoped Topology ContDiff Manifold ENNReal
open GC.MetricGeometry
open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

universe u v uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- **Every zero-stratum point lies in one selected zero packet (consumer of LCP04).** -/
theorem exists_selected_zero_packet_of_mem_zero_stratum (hE : Module.finrank ℝ E = 3)
    {β : ℕ → ℝ} (hβ : 0 < β 1) (hβone : β 1 < 1) {ζ : ℝ} (hβζ : β 1 < ζ) (hζone : ζ < 1) :
    ∃ ε δ' Λ' : ℝ, 0 < ε ∧ 0 < δ' ∧ 0 < Λ' ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T3Space M]
        [SigmaCompactSpace M] [ConnectedSpace M] [CompactSpace M]
        (g : SmoothRiemannianMetric I M),
      letI m := inducedMetricSpace g
      ∀ (N C : M → Type v) [mN : ∀ i, MetricSpace (N i)] [∀ i, ProperSpace (N i)]
        [mC : ∀ i, MetricSpace (C i)] [∀ i, ProperSpace (C i)]
        (n₀ : ∀ i, N i) (o : ∀ i, C i), (∀ i, RadialConeData (o i)) →
      ∀ (δ : M → ℝ) (η : M → M → ℝ) (r ρ : M → ℝ), Continuous ρ →
      ∀ (hρpos : ∀ p, 0 < ρ p) {T U : ℝ} (hT : 0 < T), 20 * Λ' ≤ T → T ≤ U →
      ∀ (hlower : ∀ p, T * ρ p ≤ r p), (∀ p, r p ≤ U * ρ p) →
      ∃ J : Set M, J.Finite ∧
        ((∀ i ∈ J,
            (∀ y ∈ riemannianBallOf g i (400 * r i),
              SectionalBoundedBelowAt g y (-((1 / 60) ^ 2 * (r i)⁻¹ ^ 2))) ∧
            fourPointComparison 0 (univ : Set (N i)) ∧
            (∀ x y : N i, ∃ f : Icc (0 : ℝ) 1 → N i,
              Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
              ∀ s t, dist (f s) (f t) = dist x y * dist s t) ∧
            (∀ δ₁ : ℝ, 0 < δ₁ → δ₁ < 1 → ∃ R₀ : ℝ, ∀ R : ℝ,
              R₀ ≤ R → ∀ hR : 0 < R, Nonempty (@KleinerLottApprox (N i) (C i)
                ((mN i).rescale R⁻¹ (inv_pos.mpr hR)) (mC i) (n₀ i) (o i) δ₁)) ∧
            δ i < δ' ∧
            Nonempty (@KleinerLottApprox M (C i)
              (m.rescale (r i)⁻¹ (inv_pos.mpr ((mul_pos hT (hρpos i)).trans_le (hlower i))))
              (mC i) i (o i) (δ i)) ∧
            ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (η i)
              {x | 3 / 40 ≤ (r i)⁻¹ * dist x i ∧ (r i)⁻¹ * dist x i ≤ 11} ∧
            ∀ x y, |(η i x - (r i)⁻¹ * dist i x) - (η i y - (r i)⁻¹ * dist i y)| ≤
              ε * ((r i)⁻¹ * dist x y)) →
          ∀ q, @splittingRank.{u, 0} M (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) q β 3 = 0 →
          ∃ i ∈ J, dist i q < r i / 10 ∧
            (∀ x, r i / 10 ≤ dist i x → dist i x ≤ 10 * r i →
              @splittingRank.{u, 0} M (m.rescale (ρ x)⁻¹ (inv_pos.mpr (hρpos x))) x β 3 ≠ 0 ∧
              ∃ (Z : Type) (mZ : MetricSpace Z), letI := mZ
                ∃ (z : Z) (F : @KleinerLottApprox M
                  (WithLp 2 (EuclideanSpace ℝ (Fin 1) × Z))
                  (m.rescale (ρ x)⁻¹ (inv_pos.mpr (hρpos x))) inferInstance
                  x (WithLp.toLp 2 (0, z)) (β 1)),
                  ∀ y : M, (@KleinerLottApprox.toFun M
                    (WithLp 2 (EuclideanSpace ℝ (Fin 1) × Z))
                    (m.rescale (ρ x)⁻¹ (inv_pos.mpr (hρpos x))) inferInstance
                    x (WithLp.toLp 2 (0, z)) (β 1) F y).fst = WithLp.toLp 2
                    (Function.const (Fin 1) ((ρ x)⁻¹ * (dist i y - dist i x)))) ∧
            ∀ K : Set (N i), IsCompact K → ∀ a b : N i,
              ¬ Bornology.IsBounded (connectedComponentIn Kᶜ a) →
              ¬ Bornology.IsBounded (connectedComponentIn Kᶜ b) →
              connectedComponentIn Kᶜ a = connectedComponentIn Kᶜ b) := by
  obtain ⟨ε, δ', Λ', hε, -, hδ', hΛ', hLCP04⟩ :=
    exists_selected_zero_packets_of_original_buffer.{u, v} (E := E) (H := H) (I := I) hE hβ
      hβone hβζ hζone
  refine ⟨ε, δ', Λ', hε, hδ', hΛ', ?_⟩
  intro M _ _ _ _ _ _ _ g N C mN _ mC _ n₀ o hcone δ η r ρ hρ hρpos T U hT hTΛ hTU hlower
    hupper
  let := inducedMetricSpace g
  obtain ⟨J, hfin, -, -, -, hexport⟩ :=
    hLCP04 M g N C n₀ o hcone δ η r ρ hρ hρpos hT hTΛ hTU hlower hupper
  refine ⟨J, hfin, fun hdata q hq => ?_⟩
  obtain ⟨hshell, hcover, hradial, -, hend⟩ := hexport hdata
  obtain ⟨i, hi, hqi⟩ := mem_iUnion₂.mp (hcover hq)
  refine ⟨i, hi, ?_, fun x hx1 hx2 => ⟨(hshell i hi x hx1 hx2).2, hradial i hi x hx1 hx2⟩,
    hend i hi⟩
  rw [mem_ball, dist_comm] at hqi
  exact hqi

end DifferentialGeometry.Geometry.Collapse
