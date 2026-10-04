import DifferentialGeometry.Geometry.Metric.LargeCloudNearestAllJets
import DifferentialGeometry.Topology.Manifold.NearestNormalGraphConverse
import DifferentialGeometry.Topology.Manifold.NearestNormalDiscCoordinates

/-! The original cloud nearest map gives a whole buffered normal-disc homeomorphism. -/

set_option autoImplicit false
noncomputable section
open Set Metric DifferentialGeometry.Analysis
open scoped BigOperators NNReal ContDiff Manifold
namespace GC.MetricGeometry
universe u

theorem exists_uniform_large_cloud_nearest_normal_disc_coordinates
    (k : ℕ) (B ε : ℝ) (hB : 1 ≤ B) (hε : 0 < ε) (hεsmall : ε ≤ 1 / 10) :
    ∃ F : ℕ → ℝ, (∀ m, 0 ≤ F m) ∧
      ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
        [FiniteDimensional ℝ H] (S T : Set H), S ⊆ T → TotallyBounded S →
        ∀ (r : H → ℝ) (P : H → Submodule ℝ H),
        (∀ x ∈ S, Module.finrank ℝ (P x) = k) →
        ∀ rmin R δ : ℝ, 0 < rmin →
        (∀ x ∈ S, rmin ≤ r x) → (∀ x ∈ S, r x ≤ R) →
        0 < δ → δ ≤ δ₀ → δ * ((80 * B + 31) * ε⁻¹ + 2) < 1 →
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
                (∀ y : Z, y ∈ nearestQuarterBase S r Z → ∀ n : H, ‖n‖ ≤ rmin / 4 →
                  n ∈ (actualZeroSetTangentSpace k Z y)ᗮ →
                  ∃ hz : (y : H) + n ∈ Ω, p ⟨(y : H) + n, hz⟩ = y) ∧
                (∃ e : nearestDiscDomain Ω Z p (nearestQuarterBase S r Z) (rmin / 4) ≃ₜ
                    actualNormalDisc k Z (nearestQuarterBase S r Z) (rmin / 4),
                  ∀ z, (e z : Z × H) = nearestResidualCoordinates Ω Z p z)) ∧
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
                  ball (x : H) (3 * ε⁻¹ * r x) := by
  classical
  obtain ⟨F, hF, C, hC, δc, hδc, hproduce⟩ :=
    exists_uniform_large_cloud_nearest_all_jets.{u} k B ε hB hε hεsmall
  obtain ⟨δn, hδn, hconverse⟩ := exists_uniform_actual_normal_graph_nearest_converse.{u} F hF
  refine ⟨F, hF, C, hC, min δc δn, lt_min hδc hδn, ?_⟩
  intro H _ _ _ S T hST hS r P hdim rmin R δ hrmin hlower hupper hδ hδsmall
    hinterior hscale hcloud
  obtain ⟨I, hI, hIS, hdisj, hcover, htube, hman, hproperCore, hprox, hcoverage, g, hg⟩ :=
    hproduce H S T hST hS r P hdim rmin R δ hrmin hlower hupper hδ
      (hδsmall.trans (min_le_left _ _)) hinterior hscale hcloud
  let w : H → H → ℝ := fun i y =>
    ballCutoff i (40 * ε⁻¹ * r i) (2 * (40 * ε⁻¹ * r i)) y /
      (∑ a ∈ hI.toFinset, ballCutoff a (40 * ε⁻¹ * r a) (2 * (40 * ε⁻¹ * r a)) y)
  let Q : H → Submodule ℝ H := fun y => ⨆ μ ∈ ball (1 : ℝ) (1 / 2),
    Module.End.eigenspace
      (∑ i ∈ hI.toFinset, w i y • (P i)ᗮ.starProjection).toLinearMap μ
  let η : H → H := fun y => (Q y).starProjection
    (y - ∑ i ∈ hI.toFinset, w i y • i)
  let U : Set H := ⋃ i ∈ I, ball i (20 * ε⁻¹ * r i)
  let Z : Set H := {z | z ∈ U ∧ η z = 0}
  rcases hman with ⟨hproper, cs, hcs, hemb, p, hp, hnearest, hbounds, hjets⟩
  let : ChartedSpace (Fin k → ℝ) Z := cs
  let : IsManifold 𝓘(ℝ, Fin k → ℝ) ∞ Z := hcs
  let V : S → TopologicalSpace.Opens H := fun x => ⟨ball (x : H) (r x), isOpen_ball⟩
  let Ω : TopologicalSpace.Opens H :=
    ⟨⋃ x, (V x : Set H), isOpen_iUnion (fun x => (V x).isOpen)⟩
  have hε1 : ε ≤ 1 := by linarith
  have hinv : 1 ≤ ε⁻¹ := (one_le_inv₀ hε).mpr hε1
  have hnormalInverse (y : Z) (hy : y ∈ nearestQuarterBase S r Z) (n : H)
      (hn : ‖n‖ ≤ rmin / 4) (hnormal : n ∈ (actualZeroSetTangentSpace k Z y)ᗮ) :
      ∃ hz : (y : H) + n ∈ Ω, p ⟨(y : H) + n, hz⟩ = y := by
    obtain ⟨x, hyx⟩ := mem_iUnion.mp hy
    have hrx : 0 < r x := hrmin.trans_le (hlower x x.property)
    have hsmallLarge : ball (0 : P x) (4 * r x) ⊆ ball 0 (4 * ε⁻¹ * r x) :=
      ball_subset_ball (by nlinarith)
    have hthreeLarge : ball (x : H) (3 * r x) ⊆ ball x (3 * ε⁻¹ * r x) :=
      ball_subset_ball (by nlinarith)
    have hsheet : ∀ w ∈ Z ∩ ball (x : H) (3 * r x),
        ∃ t ∈ ball (0 : P x) (4 * r x),
          w = (x : H) + orthogonalCoordinateSum (P x) (t, g x t) := by
      intro w hw
      have hwlarge : w ∈ Z ∩ ball (x : H) (3 * ε⁻¹ * r x) :=
        ⟨hw.1, hthreeLarge hw.2⟩
      rw [(hg x).2.2.2.2] at hwlarge
      obtain ⟨⟨t, ht, hrep⟩, hnear⟩ := hwlarge
      have hproj : (P x).orthogonalProjectionOnto (w - x) = t := by
        have hsub : w - x = (t : H) + (g x t : H) := by
          rw [hrep]
          change ((x : H) + ((t : H) + (g x t : H))) - x = _
          abel
        rw [hsub, map_add, (P x).orthogonalProjectionOnto_mem_subspace_eq_self,
          Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal (g x t).property, add_zero]
      have ht4 : t ∈ ball (0 : P x) (4 * r x) := by
        rw [mem_ball, dist_zero_right, ← hproj]
        have hbound := ((P x).norm_orthogonalProjectionOnto_apply_le (w - x)).trans_lt
          (by simpa only [mem_ball, dist_eq_norm] using hw.2)
        linarith
      exact ⟨t, ht4, hrep⟩
    let px : V x → Z := fun z => p ⟨(z : H), mem_iUnion.mpr ⟨x, z.property⟩⟩
    have hnx : ‖n‖ ≤ r x / 4 := hn.trans (by linarith [hlower x x.property])
    obtain ⟨hz, heq⟩ := hconverse H k Z hemb (P x) x (g x) (r x) δ hrx hδ.le
      (hδsmall.trans (min_le_right _ _)) ((hg x).1.mono hsmallLarge)
      (fun m i hi t ht => (hg x).2.2.2.1 m t (hsmallLarge ht) i hi)
      (fun t ht => ((hg x).2.1 t (hsmallLarge ht)).2) hsheet px
      (fun z => (hnearest ⟨(z : H), mem_iUnion.mpr ⟨x, z.property⟩⟩).1)
      y hyx n hnx hnormal
    exact ⟨mem_iUnion.mpr ⟨x, hz⟩, heq⟩
  have himage : nearestResidualCoordinates Ω Z p ''
      nearestDiscDomain Ω Z p (nearestQuarterBase S r Z) (rmin / 4) =
        actualNormalDisc k Z (nearestQuarterBase S r Z) (rmin / 4) := by
    apply Subset.antisymm
    · exact nearestDiscCoordinatesImage_subset_normalDisc Ω p hemb
        (fun z => (hnearest z).1) (nearestQuarterBase S r Z) (rmin / 4)
    · rintro yn ⟨hy, hnormal, hn⟩
      exact mem_nearestDiscCoordinatesImage_iff.mpr ⟨hy, hn,
        hnormalInverse yn.1 hy yn.2 hn hnormal⟩
  let e := (nearestDiscCoordinatesHomeomorph Ω Z p p.contMDiff.continuous
    (nearestQuarterBase S r Z) (rmin / 4)).trans (Homeomorph.setCongr himage)
  refine ⟨I, hI, hIS, hdisj, hcover, htube,
    ⟨hproper, cs, hcs, hemb, p, hp, hnearest, hbounds, hjets, hnormalInverse, e, ?_⟩,
    hproperCore, hprox, hcoverage, g, hg⟩
  intro z
  rfl

end GC.MetricGeometry
