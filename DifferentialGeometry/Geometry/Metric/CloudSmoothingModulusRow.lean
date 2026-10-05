import DifferentialGeometry.Analysis.ParameterSelection.ThresholdModulus
import DifferentialGeometry.Geometry.Metric.LargeCloudNearestBindings

/-!
# CFS15 in the (MCb) form: a smoothing modulus with CFS14's conclusions

Blueprint `master207B.tex`, CFS15 (`cor:fibration-cloud-marker-modulus`, lines 2711–2745).
`cfs15_modulus_row`: for fixed `k, K` and the ratio constant `B ≥ 1` of (MCb) there are `θ₁ > 0`
and a modulus `Ξ(Γ) → 0` (`Γ ↓ 0`), with values `(1/2)^(m+4) ≤ 1/16`, such that for
`0 < Γ < θ₁` every cloud of quality `Γ` satisfying the bounded-carrier hypotheses and (MCb) at
the buffer `b = Ξ(Γ)⁻¹` (radius comparison on `|x − y| ≤ 128 Ξ(Γ)⁻¹ max(r x, r y)`) has all of
CFS14's conclusions at accuracy `Ξ(Γ)` — the X80 Sol kernel
`exists_uniform_large_cloud_nearest_blueprint_budget` at `ε = Ξ(Γ)`, with the threshold `δ₀`
above `Γ`. The step "FC04 / FC26 markers with `Σ ≤ Ξ(Γ)/640` ⇒ (MCb)" (CFS07 on the actual
cloud) is NOT part of this theorem; it waits for the actual cloud binding (FC26, FC27).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter DifferentialGeometry.Analysis
open scoped BigOperators NNReal ContDiff Manifold Topology

namespace GC.MetricGeometry

universe u

/-- CFS15 in (MCb) form. -/
theorem cfs15_modulus_row (k K : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ θ₁ : ℝ, 0 < θ₁ ∧ ∃ Ξ : ℝ → ℝ, Tendsto Ξ (𝓝[>] 0) (𝓝 0) ∧
      ∀ Γ, 0 < Γ → Γ < θ₁ → (∃ m : ℕ, Ξ Γ = (1 / 2 : ℝ) ^ (m + 4)) ∧
      ((∃ F : ℕ → ℝ, (∀ m, 0 ≤ F m) ∧
          ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧
          δ₀ ≤ (Ξ Γ) / (3 * finiteCloudJetBudget F C K) ∧ Γ ≤ δ₀ ∧
          ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
            [FiniteDimensional ℝ H] (S T : Set H), S ⊆ T → TotallyBounded S →
            ∀ (r : H → ℝ) (P : H → Submodule ℝ H),
            (∀ x ∈ S, Module.finrank ℝ (P x) = k) →
            ∀ rmin R δ : ℝ, 0 < rmin →
            (∀ x ∈ S, rmin ≤ r x) → (∀ x ∈ S, r x ≤ R) →
            0 < δ → δ ≤ δ₀ →
            (∀ x ∈ T, ∀ y ∈ T, dist y x ≤ 128 * (Ξ Γ)⁻¹ * max (r y) (r x) →
              r x / B ≤ r y ∧ r y ≤ B * r x) →
            (∀ x ∈ S, hausdorffEDist (T ∩ ball x (r x / δ))
              ((AffineSubspace.mk' x (P x) : Set H) ∩ ball x (r x / δ)) ≤
                ENNReal.ofReal (δ * r x)) →
            ∃ (I : Set H) (hI : I.Finite), I ⊆ S ∧
              I.PairwiseDisjoint (fun i => ball i (r i)) ∧
              (∀ x ∈ S, ∃ i ∈ I, r x ≤ 2 * r i ∧ dist x i < 3 * r i) ∧
              ((⋃ x ∈ S, ball x (8 * (Ξ Γ)⁻¹ * r x)) ⊆
                ⋃ i ∈ I, ball i (20 * (Ξ Γ)⁻¹ * r i)) ∧
              let w : H → H → ℝ := fun i y =>
                  ballCutoff i (40 * (Ξ Γ)⁻¹ * r i) (2 * (40 * (Ξ Γ)⁻¹ * r i)) y /
                  (∑ a ∈ hI.toFinset,
                    ballCutoff a (40 * (Ξ Γ)⁻¹ * r a) (2 * (40 * (Ξ Γ)⁻¹ * r a)) y)
              let Q : H → Submodule ℝ H := fun y => ⨆ μ ∈ ball (1 : ℝ) (1 / 2),
                  Module.End.eigenspace
                  (∑ i ∈ hI.toFinset, w i y • (P i)ᗮ.starProjection).toLinearMap μ
              let η : H → H := fun y => (Q y).starProjection
                (y - ∑ i ∈ hI.toFinset, w i y • i)
              let U : Set H := ⋃ i ∈ I, ball i (20 * (Ξ Γ)⁻¹ * r i)
              let Z : Set H := {z | z ∈ U ∧ η z = 0}
              (IsProperMap (fun z : Z => (⟨z.1, z.2.1⟩ : U)) ∧
                ∃ cs : ChartedSpace (Fin k → ℝ) Z,
                  let _ := cs
                  IsManifold 𝓘(ℝ, Fin k → ℝ) ∞ Z ∧
                  _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) ∞
                    (Subtype.val : Z → H) ∧
                  let V : S → TopologicalSpace.Opens H := fun x => ⟨ball (x : H) (r x), isOpen_ball⟩
                  let Ω : TopologicalSpace.Opens H :=
                    ⟨⋃ x, (V x : Set H), isOpen_iUnion (fun x => (V x).isOpen)⟩
                  ∃ p : C^∞⟮𝓘(ℝ, H), Ω; 𝓘(ℝ, Fin k → ℝ), Z⟯,
                    _root_.Manifold.IsSubmersion 𝓘(ℝ, H) 𝓘(ℝ, Fin k → ℝ) ∞ p ∧
                    (∀ z : Ω, IsMinOn (fun y => dist (z : H) y) Z (p z : H) ∧
                      (∀ y ∈ Z, IsMinOn (fun w => dist (z : H) w) Z y → y = (p z : H))) ∧
                    (∀ x : S, ∀ z : V x,
                      ‖(p ⟨(z : H), mem_iUnion.mpr ⟨x, z.property⟩⟩ : H) -
                        ((x : H) + (P x).starProjection ((z : H) - x))‖ ≤ (Ξ Γ) * r x ∧
                      (let D : H →L[ℝ] H :=
                        mfderiv 𝓘(ℝ, H) 𝓘(ℝ, H) (fun y : Ω => (p y : H))
                          ⟨(z : H), mem_iUnion.mpr ⟨x, z.property⟩⟩
                      ‖D - (P x).starProjection‖ ≤ (Ξ Γ))) ∧
                    (let pAmbient : H → H := nearestAmbientExtension Ω Z p
                     ∀ x : S, ∀ z ∈ ball (x : H) (r x), ∀ j : ℕ,
                       ‖iteratedFDeriv ℝ j
                         (fun y => pAmbient y - ((x : H) + (P x).starProjection (y - x))) z‖ ≤
                           C j * δ * r x * ((r x)⁻¹) ^ j) ∧
                    (let pAmbient : H → H := nearestAmbientExtension Ω Z p
                     ∀ x : S, ∀ z ∈ ball (x : H) (r x), ∀ j ≤ K,
                       ‖iteratedFDeriv ℝ j
                         (fun y => pAmbient y - ((x : H) + (P x).starProjection (y - x))) z‖ ≤
                           ((Ξ Γ) / 3) * r x * ((r x)⁻¹) ^ j) ∧
                    (∀ z : Z, ∀ hz : (z : H) ∈ Ω, p ⟨(z : H), hz⟩ = z) ∧
                    (∀ x : S, ∀ z : Z, (z : H) ∈ ball (x : H) (r x) →
                      ‖actualZeroSetNormalProjector k Z z - (P x)ᗮ.starProjection‖ ≤ (Ξ Γ))) ∧
              (let N : Set H := ⋃ x ∈ S, ball x (r x);
                IsProperMap (Subtype.val : {z : N | (z : H) ∈ Z} → N)) ∧
              (Z ⊆ ⋃ q ∈ T, ball q ((Ξ Γ) * r q)) ∧
              (∀ x ∈ S,
                hausdorffEDist (((fun y => (r x)⁻¹ • (y - x)) '' T) ∩ closedBall 0 (Ξ Γ)⁻¹)
                    (((fun y => (r x)⁻¹ • (y - x)) '' Z) ∩ closedBall 0 (Ξ Γ)⁻¹) ≤
                    ENNReal.ofReal (7 * (Ξ Γ) / 16) ∧
                  hausdorffEDist (((fun y => (r x)⁻¹ • (y - x)) '' T) ∩ ball 0 (Ξ Γ)⁻¹)
                    (((fun y => (r x)⁻¹ • (y - x)) '' Z) ∩ ball 0 (Ξ Γ)⁻¹) ≤
                    ENNReal.ofReal (7 * (Ξ Γ) / 16)) ∧
              ∃ g : ∀ x : S, P x → (P x)ᗮ, ∀ x : S,
                ContDiffOn ℝ ∞ (g x) (ball 0 (4 * (Ξ Γ)⁻¹ * r x)) ∧
                (∀ t ∈ ball (0 : P x) (4 * (Ξ Γ)⁻¹ * r x), ‖g x t‖ ≤ r x / 4 ∧
                  (x : H) + orthogonalCoordinateSum (P x) (t, g x t) ∈ Z) ∧
                (∀ t ∈ ball (0 : P x) (4 * (Ξ Γ)⁻¹ * r x),
                  ∀ n ∈ closedBall (0 : (P x)ᗮ) (r x),
                  η ((x : H) + orthogonalCoordinateSum (P x) (t, n)) = 0 ↔ n = g x t) ∧
                (∀ m t, t ∈ ball (0 : P x) (4 * (Ξ Γ)⁻¹ * r x) → ∀ j, j ≤ m →
                  ‖iteratedFDeriv ℝ j (g x) t‖ ≤ F m * δ * r x * ((r x)⁻¹) ^ j) ∧
                Z ∩ ball (x : H) (3 * (Ξ Γ)⁻¹ * r x) =
                  {z : H | ∃ t ∈ ball (0 : P x) (4 * (Ξ Γ)⁻¹ * r x),
                    z = (x : H) + orthogonalCoordinateSum (P x) (t, g x t)} ∩
                      ball (x : H) (3 * (Ξ Γ)⁻¹ * r x) ∧
                (∀ t ∈ ball (0 : P x) (4 * (Ξ Γ)⁻¹ * r x), ∀ j ≤ K + 1,
                  ‖iteratedFDeriv ℝ j (g x) t‖ ≤ ((Ξ Γ) / 3) * r x * ((r x)⁻¹) ^ j))) := by
  refine ParameterSelection.exists_modulus_of_thresholds
    (P := fun ε Γ => ∃ F : ℕ → ℝ, (∀ m, 0 ≤ F m) ∧
        ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧
        δ₀ ≤ ε / (3 * finiteCloudJetBudget F C K) ∧ Γ ≤ δ₀ ∧
        ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
          [FiniteDimensional ℝ H] (S T : Set H), S ⊆ T → TotallyBounded S →
          ∀ (r : H → ℝ) (P : H → Submodule ℝ H),
          (∀ x ∈ S, Module.finrank ℝ (P x) = k) →
          ∀ rmin R δ : ℝ, 0 < rmin →
          (∀ x ∈ S, rmin ≤ r x) → (∀ x ∈ S, r x ≤ R) →
          0 < δ → δ ≤ δ₀ →
          (∀ x ∈ T, ∀ y ∈ T, dist y x ≤ 128 * ε⁻¹ * max (r y) (r x) →
            r x / B ≤ r y ∧ r y ≤ B * r x) →
          (∀ x ∈ S, hausdorffEDist (T ∩ ball x (r x / δ))
            ((AffineSubspace.mk' x (P x) : Set H) ∩ ball x (r x / δ)) ≤
              ENNReal.ofReal (δ * r x)) →
          ∃ (I : Set H) (hI : I.Finite), I ⊆ S ∧
            I.PairwiseDisjoint (fun i => ball i (r i)) ∧
            (∀ x ∈ S, ∃ i ∈ I, r x ≤ 2 * r i ∧ dist x i < 3 * r i) ∧
            ((⋃ x ∈ S, ball x (8 * ε⁻¹ * r x)) ⊆ ⋃ i ∈ I, ball i (20 * ε⁻¹ * r i)) ∧
            let w : H → H → ℝ := fun i y => ballCutoff i (40 * ε⁻¹ * r i) (2 * (40 * ε⁻¹ * r i)) y /
                (∑ a ∈ hI.toFinset, ballCutoff a (40 * ε⁻¹ * r a) (2 * (40 * ε⁻¹ * r a)) y)
            let Q : H → Submodule ℝ H := fun y => ⨆ μ ∈ ball (1 : ℝ) (1 / 2), Module.End.eigenspace
                (∑ i ∈ hI.toFinset, w i y • (P i)ᗮ.starProjection).toLinearMap μ
            let η : H → H := fun y => (Q y).starProjection
              (y - ∑ i ∈ hI.toFinset, w i y • i)
            let U : Set H := ⋃ i ∈ I, ball i (20 * ε⁻¹ * r i)
            let Z : Set H := {z | z ∈ U ∧ η z = 0}
            (IsProperMap (fun z : Z => (⟨z.1, z.2.1⟩ : U)) ∧
              ∃ cs : ChartedSpace (Fin k → ℝ) Z,
                let _ := cs
                IsManifold 𝓘(ℝ, Fin k → ℝ) ∞ Z ∧
                _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) ∞
                  (Subtype.val : Z → H) ∧
                let V : S → TopologicalSpace.Opens H := fun x => ⟨ball (x : H) (r x), isOpen_ball⟩
                let Ω : TopologicalSpace.Opens H :=
                  ⟨⋃ x, (V x : Set H), isOpen_iUnion (fun x => (V x).isOpen)⟩
                ∃ p : C^∞⟮𝓘(ℝ, H), Ω; 𝓘(ℝ, Fin k → ℝ), Z⟯,
                  _root_.Manifold.IsSubmersion 𝓘(ℝ, H) 𝓘(ℝ, Fin k → ℝ) ∞ p ∧
                  (∀ z : Ω, IsMinOn (fun y => dist (z : H) y) Z (p z : H) ∧
                    (∀ y ∈ Z, IsMinOn (fun w => dist (z : H) w) Z y → y = (p z : H))) ∧
                  (∀ x : S, ∀ z : V x,
                    ‖(p ⟨(z : H), mem_iUnion.mpr ⟨x, z.property⟩⟩ : H) -
                      ((x : H) + (P x).starProjection ((z : H) - x))‖ ≤ ε * r x ∧
                    (let D : H →L[ℝ] H :=
                      mfderiv 𝓘(ℝ, H) 𝓘(ℝ, H) (fun y : Ω => (p y : H))
                        ⟨(z : H), mem_iUnion.mpr ⟨x, z.property⟩⟩
                    ‖D - (P x).starProjection‖ ≤ ε)) ∧
                  (let pAmbient : H → H := nearestAmbientExtension Ω Z p
                   ∀ x : S, ∀ z ∈ ball (x : H) (r x), ∀ j : ℕ,
                     ‖iteratedFDeriv ℝ j
                       (fun y => pAmbient y - ((x : H) + (P x).starProjection (y - x))) z‖ ≤
                         C j * δ * r x * ((r x)⁻¹) ^ j) ∧
                  (let pAmbient : H → H := nearestAmbientExtension Ω Z p
                   ∀ x : S, ∀ z ∈ ball (x : H) (r x), ∀ j ≤ K,
                     ‖iteratedFDeriv ℝ j
                       (fun y => pAmbient y - ((x : H) + (P x).starProjection (y - x))) z‖ ≤
                         (ε / 3) * r x * ((r x)⁻¹) ^ j) ∧
                  (∀ z : Z, ∀ hz : (z : H) ∈ Ω, p ⟨(z : H), hz⟩ = z) ∧
                  (∀ x : S, ∀ z : Z, (z : H) ∈ ball (x : H) (r x) →
                    ‖actualZeroSetNormalProjector k Z z - (P x)ᗮ.starProjection‖ ≤ ε)) ∧
            (let N : Set H := ⋃ x ∈ S, ball x (r x);
              IsProperMap (Subtype.val : {z : N | (z : H) ∈ Z} → N)) ∧
            (Z ⊆ ⋃ q ∈ T, ball q (ε * r q)) ∧
            (∀ x ∈ S,
              hausdorffEDist (((fun y => (r x)⁻¹ • (y - x)) '' T) ∩ closedBall 0 ε⁻¹)
                  (((fun y => (r x)⁻¹ • (y - x)) '' Z) ∩ closedBall 0 ε⁻¹) ≤
                  ENNReal.ofReal (7 * ε / 16) ∧
                hausdorffEDist (((fun y => (r x)⁻¹ • (y - x)) '' T) ∩ ball 0 ε⁻¹)
                  (((fun y => (r x)⁻¹ • (y - x)) '' Z) ∩ ball 0 ε⁻¹) ≤
                  ENNReal.ofReal (7 * ε / 16)) ∧
            ∃ g : ∀ x : S, P x → (P x)ᗮ, ∀ x : S,
              ContDiffOn ℝ ∞ (g x) (ball 0 (4 * ε⁻¹ * r x)) ∧
              (∀ t ∈ ball (0 : P x) (4 * ε⁻¹ * r x), ‖g x t‖ ≤ r x / 4 ∧
                (x : H) + orthogonalCoordinateSum (P x) (t, g x t) ∈ Z) ∧
              (∀ t ∈ ball (0 : P x) (4 * ε⁻¹ * r x),
                ∀ n ∈ closedBall (0 : (P x)ᗮ) (r x),
                η ((x : H) + orthogonalCoordinateSum (P x) (t, n)) = 0 ↔ n = g x t) ∧
              (∀ m t, t ∈ ball (0 : P x) (4 * ε⁻¹ * r x) → ∀ j, j ≤ m →
                ‖iteratedFDeriv ℝ j (g x) t‖ ≤ F m * δ * r x * ((r x)⁻¹) ^ j) ∧
              Z ∩ ball (x : H) (3 * ε⁻¹ * r x) =
                {z : H | ∃ t ∈ ball (0 : P x) (4 * ε⁻¹ * r x),
                  z = (x : H) + orthogonalCoordinateSum (P x) (t, g x t)} ∩
                    ball (x : H) (3 * ε⁻¹ * r x) ∧
              (∀ t ∈ ball (0 : P x) (4 * ε⁻¹ * r x), ∀ j ≤ K + 1,
                ‖iteratedFDeriv ℝ j (g x) t‖ ≤ (ε / 3) * r x * ((r x)⁻¹) ^ j))
    (fun m => ?_)
  have hε : (0 : ℝ) < (1 / 2 : ℝ) ^ (m + 4) := by positivity
  have hεsmall : (1 / 2 : ℝ) ^ (m + 4) ≤ 1 / 10 := by
    calc (1 / 2 : ℝ) ^ (m + 4) ≤ (1 / 2 : ℝ) ^ 4 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ ≤ 1 / 10 := by norm_num
  obtain ⟨F, hF, C, hC, δ₀, hδ₀, hδ₀le, hrest⟩ :=
    exists_uniform_large_cloud_nearest_blueprint_budget.{u} k K B ((1 / 2 : ℝ) ^ (m + 4)) hB hε
      hεsmall
  exact ⟨δ₀, hδ₀, fun Γ _ hΓ => ⟨F, hF, C, hC, δ₀, hδ₀, hδ₀le, hΓ, hrest⟩⟩

end GC.MetricGeometry
