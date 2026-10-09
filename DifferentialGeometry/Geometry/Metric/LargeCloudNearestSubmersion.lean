import DifferentialGeometry.Geometry.Metric.LargeCloudLocalNearestSubmersions
import DifferentialGeometry.Topology.Manifold.NearestSubmersionGluing

set_option autoImplicit false
noncomputable section
open Set Metric DifferentialGeometry.Analysis
open scoped BigOperators NNReal ContDiff Manifold
namespace GC.MetricGeometry
universe u

theorem exists_uniform_large_cloud_buffered_graph_manifold_with_nearest_submersion
    (k : ℕ) (B ε : ℝ) (hB : 1 ≤ B) (hε : 0 < ε) (hεsmall : ε ≤ 1 / 10) :
    ∃ F : ℕ → ℝ, (∀ m, 0 ≤ F m) ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧
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
                ∀ x : S, ∀ z : V x,
                  ‖(p ⟨(z : H), mem_iUnion.mpr ⟨x, z.property⟩⟩ : H) -
                    ((x : H) + (P x).starProjection ((z : H) - x))‖ ≤ ε * r x ∧
                  (let D : H →L[ℝ] H :=
                    mfderiv 𝓘(ℝ, H) 𝓘(ℝ, H) (fun y : Ω => (p y : H))
                      ⟨(z : H), mem_iUnion.mpr ⟨x, z.property⟩⟩
                  ‖D - (P x).starProjection‖ ≤ ε)) ∧
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
  obtain ⟨F, hF, δ₀, hδ₀, hproduce⟩ :=
    exists_uniform_large_cloud_buffered_graph_manifold_with_local_nearest_submersions.{u}
      k B ε hB hε hεsmall
  refine ⟨F, hF, δ₀, hδ₀, ?_⟩
  intro H _ _ _ S T hST hS r P hdim rmin R δ hrmin hlower hupper hδ hδsmall
    hinterior hscale hcloud
  obtain ⟨I, hI, hIS, hdisj, hcover, htube, hman, hproperCore, hprox, hcoverage, g, hg⟩ :=
    hproduce H S T hST hS r P hdim rmin R δ hrmin hlower hupper hδ hδsmall
      hinterior hscale hcloud
  let w : H → H → ℝ := fun i y =>
    ballCutoff i (40 * ε⁻¹ * r i) (2 * (40 * ε⁻¹ * r i)) y /
      (∑ j ∈ hI.toFinset,
        ballCutoff j (40 * ε⁻¹ * r j) (2 * (40 * ε⁻¹ * r j)) y)
  let Q : H → Submodule ℝ H := fun y => ⨆ μ ∈ ball (1 : ℝ) (1 / 2),
    Module.End.eigenspace
      (∑ i ∈ hI.toFinset, w i y • (P i)ᗮ.starProjection).toLinearMap μ
  let η : H → H := fun y => (Q y).starProjection
    (y - ∑ i ∈ hI.toFinset, w i y • i)
  let U : Set H := ⋃ i ∈ I, ball i (20 * ε⁻¹ * r i)
  let Z : Set H := {z | z ∈ U ∧ η z = 0}
  rcases hman with ⟨hproper, cs, hcs, hemb, hlocal⟩
  let : ChartedSpace (Fin k → ℝ) Z := cs
  let : IsManifold 𝓘(ℝ, Fin k → ℝ) ∞ Z := hcs
  let V : S → TopologicalSpace.Opens H := fun x => ⟨ball (x : H) (r x), isOpen_ball⟩
  let Ω : TopologicalSpace.Opens H :=
    ⟨⋃ x, (V x : Set H), isOpen_iUnion (fun x => (V x).isOpen)⟩
  choose p hp hnearest using hlocal
  obtain ⟨q, hq, hqnearest, hagree⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_smooth_unique_nearest_submersion_iUnion_of_local
      V Z p hp (fun x z => ⟨(hnearest x z).1, (hnearest x z).2.1⟩)
  refine ⟨I, hI, hIS, hdisj, hcover, htube,
    ⟨hproper, cs, hcs, hemb, q, hq, hqnearest, ?_⟩, hproperCore, hprox, hcoverage, g, hg⟩
  intro x z
  have hincl : V x ≤ Ω := fun _ hz => mem_iUnion.mpr ⟨x, hz⟩
  have heq : ((fun y : Ω => (q y : H)) ∘ TopologicalSpace.Opens.inclusion hincl) =
      (fun y : V x => (p x y : H)) := by
    funext y
    exact congrArg Subtype.val (hagree x y)
  have hqsmooth : ContMDiff 𝓘(ℝ, H) 𝓘(ℝ, H) ∞ (fun y : Ω => (q y : H)) :=
    hemb.contMDiff.comp q.contMDiff
  let Dlocal : H →L[ℝ] H :=
    mfderiv 𝓘(ℝ, H) 𝓘(ℝ, H) (fun y : V x => (p x y : H)) z
  let Dglobal : H →L[ℝ] H :=
    mfderiv 𝓘(ℝ, H) 𝓘(ℝ, H) (fun y : Ω => (q y : H))
      (TopologicalSpace.Opens.inclusion hincl z)
  have hd : Dlocal = Dglobal := by
    have hc := mfderiv_comp z (hqsmooth.mdifferentiableAt (by simp))
      ((contMDiff_inclusion (n := ∞) hincl).mdifferentiableAt (by simp))
    rw [heq, DifferentialGeometry.mfderiv_opens_incl] at hc
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg (fun A => A v) hc
  constructor
  · rw [hagree x z]
    exact (hnearest x z).2.2.1
  · have hbound : ‖Dlocal - (P x).starProjection‖ ≤ ε := (hnearest x z).2.2.2
    have hnorm : ‖Dlocal - (P x).starProjection‖ = ‖Dglobal - (P x).starProjection‖ :=
      congrArg (fun A : H →L[ℝ] H => ‖A - (P x).starProjection‖) hd
    change ‖Dglobal - (P x).starProjection‖ ≤ ε
    exact hnorm ▸ hbound

end GC.MetricGeometry
