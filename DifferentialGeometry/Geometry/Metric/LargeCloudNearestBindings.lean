import DifferentialGeometry.Geometry.Metric.LargeCloudNearestFiniteBudget
import DifferentialGeometry.Geometry.Metric.RetainedMarkerBindings

set_option autoImplicit false
noncomputable section
open Set Metric Filter DifferentialGeometry.Analysis
open scoped BigOperators NNReal ContDiff Manifold
namespace GC.MetricGeometry
universe u

theorem exists_uniform_large_cloud_nearest_blueprint_budget
    (k K : ℕ) (B ε : ℝ) (hB : 1 ≤ B) (hε : 0 < ε) (hεsmall : ε ≤ 1 / 10) :
    ∃ F : ℕ → ℝ, (∀ m, 0 ≤ F m) ∧
      ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧
      δ₀ ≤ ε / (3 * finiteCloudJetBudget F C K) ∧
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
              ‖iteratedFDeriv ℝ j (g x) t‖ ≤ (ε / 3) * r x * ((r x)⁻¹) ^ j) := by
  obtain ⟨F, hF, C, hC, δ₁, hδ₁, hbudget, hproduce⟩ :=
    exists_uniform_large_cloud_nearest_finite_budget k K B ε hB hε hεsmall
  let A : ℝ := (80 * B + 31) * ε⁻¹ + 2
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨F, hF, C, hC, min δ₁ (1 / (2 * A)),
    lt_min hδ₁ (by positivity), (min_le_left _ _).trans hbudget, ?_⟩
  intro H instNorm instInner instFinite S T hST hS r P hdim rmin R δ hrmin hlower hupper
    hδ hδsmall hscale hcloud
  have hs : δ ≤ 1 / (2 * A) := hδsmall.trans (min_le_right _ _)
  have hm : δ * (2 * A) ≤ 1 := (le_div_iff₀ (by positivity)).mp hs
  have hi : δ * A < 1 := by nlinarith
  exact hproduce H S T hST hS r P hdim rmin R δ hrmin hlower hupper hδ
    (hδsmall.trans (min_le_left _ _)) hi hscale hcloud

theorem exists_uniform_retained_marker_cloud_nearest_finite_budget
    (k K : ℕ) (ε : ℝ) (hε : 0 < ε) (hεsmall : ε ≤ 1 / 10) :
    ∃ F : ℕ → ℝ, (∀ m, 0 ≤ F m) ∧
      ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧
      δ₀ ≤ ε / (3 * finiteCloudJetBudget F C K) ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
        [FiniteDimensional ℝ H] (S T : Set H), S ⊆ T → TotallyBounded S →
        ∀ (r : H → ℝ) (P : H → Submodule ℝ H),
        (∀ x ∈ S, Module.finrank ℝ (P x) = k) →
        ∀ rmin R δ : ℝ, 0 < rmin →
        (∀ x ∈ S, rmin ≤ r x) → (∀ x ∈ S, r x ≤ R) →
        0 < δ → δ ≤ δ₀ → δ * ((80 * (5 / 3 : ℝ) + 31) * ε⁻¹ + 2) < 1 →
        ∀ (MP MI : Type u) (f : MP → H) (ρ : MP → ℝ)
          (marker : MI → H → ℝ) (Rmarker : MI → ℝ) (select : H → MP) (σ : ℝ),
        (∀ i, 0 < Rmarker i) → (∀ i, LipschitzWith 1 (marker i)) →
        (∀ p, ∃ i, marker i (f p) = Rmarker i) →
        (∀ i p, 0 < marker i (f p) →
          3 * Rmarker i / 4 ≤ ρ p ∧ ρ p ≤ 5 * Rmarker i / 4) →
        (∀ x ∈ T, f (select x) = x) → (∀ x ∈ T, r x = σ * ρ (select x)) →
        0 < σ → σ ≤ ε / 640 →
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
              ‖iteratedFDeriv ℝ j (g x) t‖ ≤ (ε / 3) * r x * ((r x)⁻¹) ^ j) := by
  obtain ⟨F, hF, C, hC, δ₀, hδ₀, hbudget, hproduce⟩ :=
    exists_uniform_large_cloud_nearest_finite_budget k K (5 / 3) ε (by norm_num) hε hεsmall
  refine ⟨F, hF, C, hC, δ₀, hδ₀, hbudget, ?_⟩
  intro H instNorm instInner instFinite S T hST hS r P hdim rmin R δ hrmin hlower hupper
    hδ hδsmall hinterior MP MI f ρ marker Rmarker select σ hR hmarker hfull hsupport
    hselect hr hσ hσsmall hcloud
  have hsmall : (128 * ε⁻¹) * σ ≤ 1 / 5 := by
    have hs := mul_le_mul_of_nonneg_left hσsmall (by positivity : 0 ≤ 128 * ε⁻¹)
    have heq : (128 * ε⁻¹) * (ε / 640) = 1 / 5 := by field_simp; ring
    exact hs.trans_eq heq
  have hscale := retained_marker_selected_cloud_control f ρ marker Rmarker
    hR hmarker hfull hsupport T select hselect r hr hσ.le (by positivity) hsmall
  exact hproduce H S T hST hS r P hdim rmin R δ hrmin hlower hupper hδ hδsmall
    hinterior hscale hcloud

end GC.MetricGeometry
