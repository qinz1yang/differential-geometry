import DifferentialGeometry.Geometry.Metric.MarkerCloudApplications
import DifferentialGeometry.Geometry.Metric.LargeCloudNearestFiniteBudget

/-! Full SAME-witness cloud smoothing from actual retained markers and chosen preimages. -/

set_option autoImplicit false
noncomputable section

open Set Metric DifferentialGeometry.Analysis
open scoped BigOperators NNReal ContDiff Manifold

namespace GC.MetricGeometry

universe u

theorem exists_uniform_marker_cloud_nearest_finite_budget
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
  classical
  obtain ⟨F, hF, C, hC, δ₀, hδ₀, hthreshold, hproduce⟩ :=
    exists_uniform_large_cloud_nearest_finite_budget.{u}
      k K (5 / 3) ε (by norm_num) hε hεsmall
  refine ⟨F, hF, C, hC, δ₀, hδ₀, hthreshold, ?_⟩
  intro H instNorm instInner instFinite S T hST hS r P hdim rmin R δ
    hrmin hlower hupper hδ hδsmall hinterior MP MI f ρ marker Rmarker select σ
    hRmarker hmarker hfull hsupport hselect hr hσ hσsmall hcloud
  have hsmall : (128 * ε⁻¹) * σ ≤ 1 / 5 := by
    calc
      (128 * ε⁻¹) * σ ≤ (128 * ε⁻¹) * (ε / 640) :=
        mul_le_mul_of_nonneg_left hσsmall (by positivity)
      _ = 1 / 5 := by field_simp; ring
  have hscale := markerChosenRadius_local_scale_control f ρ marker Rmarker
    hRmarker hmarker hfull hsupport T select hselect r hr hσ.le
    (by positivity : 0 ≤ 128 * ε⁻¹) hsmall
  exact hproduce H S T hST hS r P hdim rmin R δ
    hrmin hlower hupper hδ hδsmall hinterior hscale hcloud

namespace NearestJetsExamples

theorem two_center_marker_cloud_has_three_jet_nearest_map :
    dist (center false) (center true) = 1 ∧
      offset ∈ (domain false : Set H) ∩ (domain true : Set H) ∧
    let S : Set H := range center
    let V : S → TopologicalSpace.Opens H := fun x => ⟨ball (x : H) 2, isOpen_ball⟩
    let Ω : TopologicalSpace.Opens H :=
      ⟨⋃ x, (V x : Set H), isOpen_iUnion (fun x => (V x).isOpen)⟩
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧ ∃ δ : ℝ, 0 < δ ∧
    ∃ (I : Set H) (hI : I.Finite), I ⊆ S ∧
      I.PairwiseDisjoint (fun i => ball i (2 : ℝ)) ∧
      let w : H → H → ℝ := fun i y =>
        ballCutoff i (40 * (1 / 20 : ℝ)⁻¹ * 2) (2 * (40 * (1 / 20 : ℝ)⁻¹ * 2)) y /
          (∑ a ∈ hI.toFinset,
            ballCutoff a (40 * (1 / 20 : ℝ)⁻¹ * 2) (2 * (40 * (1 / 20 : ℝ)⁻¹ * 2)) y)
      let Q₀ : H → Submodule ℝ H := fun y => ⨆ μ ∈ ball (1 : ℝ) (1 / 2),
        Module.End.eigenspace
          (∑ i ∈ hI.toFinset, w i y • tangentᗮ.starProjection).toLinearMap μ
      let η : H → H := fun y => (Q₀ y).starProjection
        (y - ∑ i ∈ hI.toFinset, w i y • i)
      let U : Set H := ⋃ i ∈ I, ball i (20 * (1 / 20 : ℝ)⁻¹ * 2)
      let W : Set H := {z | z ∈ U ∧ η z = 0}
      W.Nonempty ∧
        ∃ cs : ChartedSpace (Fin 1 → ℝ) W,
          let _ := cs
          IsManifold 𝓘(ℝ, Fin 1 → ℝ) ∞ W ∧
          _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin 1 → ℝ) 𝓘(ℝ, H) ∞
            (Subtype.val : W → H) ∧
          ∃ q : C^∞⟮𝓘(ℝ, H), Ω; 𝓘(ℝ, Fin 1 → ℝ), W⟯,
            _root_.Manifold.IsSubmersion 𝓘(ℝ, H) 𝓘(ℝ, Fin 1 → ℝ) ∞ q ∧
            (∀ z : Ω, IsMinOn (fun y => dist (z : H) y) W (q z : H) ∧
              (∀ y ∈ W, IsMinOn (fun v => dist (z : H) v) W y → y = (q z : H))) ∧
            (∀ x : S, ∀ z : V x,
              ‖(q ⟨(z : H), mem_iUnion.mpr ⟨x, z.property⟩⟩ : H) -
                ((x : H) + tangent.starProjection ((z : H) - x))‖ ≤ 1 / 10 ∧
              (let D : H →L[ℝ] H :=
                mfderiv 𝓘(ℝ, H) 𝓘(ℝ, H) (fun y : Ω => (q y : H))
                  ⟨(z : H), mem_iUnion.mpr ⟨x, z.property⟩⟩
              ‖D - tangent.starProjection‖ ≤ 1 / 20 ∧
                19 / 20 ≤ ‖D tangentVector‖)) ∧
            (let qAmbient : H → H := nearestAmbientExtension Ω W q
             ∀ x : S, ∀ z ∈ ball (x : H) 2, ∀ j : ℕ,
               ‖iteratedFDeriv ℝ j
                 (fun y => qAmbient y - ((x : H) + tangent.starProjection (y - x))) z‖ ≤
                   C j * δ * 2 * ((2 : ℝ)⁻¹) ^ j) ∧
            (let qAmbient : H → H := nearestAmbientExtension Ω W q
             ∀ x : S, ∀ z ∈ ball (x : H) 2, ∀ j ≤ 3,
               ‖iteratedFDeriv ℝ j
                 (fun y => qAmbient y - ((x : H) + tangent.starProjection (y - x))) z‖ ≤
                   (1 / 60 : ℝ) * 2 * ((2 : ℝ)⁻¹) ^ j) ∧
            (∀ z : W, ∀ hz : (z : H) ∈ Ω, q ⟨(z : H), hz⟩ = z) ∧
            (∀ x : S, ∀ z : W, (z : H) ∈ ball (x : H) 2 →
              ‖actualZeroSetNormalProjector 1 W z - tangentᗮ.starProjection‖ ≤ 1 / 20) := by
  classical
  refine ⟨distinct_centers_and_nonempty_overlap.1,
    distinct_centers_and_nonempty_overlap.2, ?_⟩
  let S : Set H := range center
  let V : S → TopologicalSpace.Opens H := fun x => ⟨ball (x : H) 2, isOpen_ball⟩
  let Ω : TopologicalSpace.Opens H :=
    ⟨⋃ x, (V x : Set H), isOpen_iUnion (fun x => (V x).isOpen)⟩
  let cloud : Set H := (AffineSubspace.mk' offset tangent : Set H)
  have hnorm : ‖tangentVector‖ = 1 := by
    simp [tangentVector, EuclideanSpace.single, PiLp.norm_single]
  have hdim : Module.finrank ℝ tangent = 1 := by
    have hne : tangentVector ≠ 0 := by
      intro hz
      rw [hz, norm_zero] at hnorm
      norm_num at hnorm
    exact finrank_span_singleton hne
  have hST : S ⊆ cloud := by
    rintro x ⟨b, rfl⟩
    cases b with
    | false => exact AffineSubspace.self_mem_mk' offset tangent
    | true =>
      change offset + tangentVector - offset ∈ tangent
      rw [add_sub_cancel_left]
      change tangentVector ∈ (Submodule.span ℝ {tangentVector} : Set H)
      exact Submodule.subset_span (mem_singleton tangentVector)
  obtain ⟨_F, _hF, C, hC, δ₀, hδ₀, _hthreshold, hproduce⟩ :=
    exists_uniform_marker_cloud_nearest_finite_budget
      1 3 (1 / 20) (by norm_num) (by norm_num)
  let δ : ℝ := min δ₀ (1 / 8000)
  have hδ : 0 < δ := lt_min hδ₀ (by norm_num)
  have hinterior : δ * ((80 * (5 / 3 : ℝ) + 31) * (1 / 20 : ℝ)⁻¹ + 2) < 1 := by
    have hsmall : δ ≤ 1 / 8000 := min_le_right _ _
    norm_num
    linarith
  have hcloud : ∀ x ∈ S,
      hausdorffEDist (cloud ∩ ball x (2 / δ))
        ((AffineSubspace.mk' x tangent : Set H) ∩ ball x (2 / δ)) ≤
          ENNReal.ofReal (δ * 2) := by
    intro x hx
    have ha : AffineSubspace.mk' x tangent = AffineSubspace.mk' offset tangent := by
      simpa only [AffineSubspace.direction_mk'] using
        (AffineSubspace.mk'_eq (s := AffineSubspace.mk' offset tangent) (hST hx))
    rw [ha, hausdorffEDist_self]
    exact zero_le
  obtain ⟨I, hI, hIS, hdisj, _hcover, _htube, hrest⟩ :=
    hproduce H S cloud hST (finite_range center).totallyBounded
      (fun x => 2) (fun x => tangent) (fun x hx => hdim)
      2 2 δ (by norm_num) (fun x hx => le_rfl) (fun x hx => le_rfl)
      hδ (min_le_left _ _) hinterior
      H Unit id (fun p => 25600) (fun i z => 25600) (fun i => 25600) id
      (1 / 12800) (by intro i; norm_num)
      (by intro i; exact (LipschitzWith.const 25600).weaken (by norm_num))
      (fun p => ⟨(), rfl⟩) (by intro i p h; constructor <;> norm_num)
      (by intro x hx; rfl) (by intro x hx; norm_num) (by norm_num) (by norm_num) hcloud
  let w : H → H → ℝ := fun i y =>
    ballCutoff i (40 * (1 / 20 : ℝ)⁻¹ * 2) (2 * (40 * (1 / 20 : ℝ)⁻¹ * 2)) y /
      (∑ a ∈ hI.toFinset,
        ballCutoff a (40 * (1 / 20 : ℝ)⁻¹ * 2) (2 * (40 * (1 / 20 : ℝ)⁻¹ * 2)) y)
  let Q₀ : H → Submodule ℝ H := fun y => ⨆ μ ∈ ball (1 : ℝ) (1 / 2),
    Module.End.eigenspace
      (∑ i ∈ hI.toFinset, w i y • tangentᗮ.starProjection).toLinearMap μ
  let η : H → H := fun y => (Q₀ y).starProjection
    (y - ∑ i ∈ hI.toFinset, w i y • i)
  let U : Set H := ⋃ i ∈ I, ball i (20 * (1 / 20 : ℝ)⁻¹ * 2)
  let W : Set H := {z | z ∈ U ∧ η z = 0}
  rcases hrest.1.2 with ⟨cs, hcs, hemb, q, hq, hnearest, hbounds, hjets, hfinite, hfixed, hnormal⟩
  let : ChartedSpace (Fin 1 → ℝ) W := cs
  let : IsManifold 𝓘(ℝ, Fin 1 → ℝ) ∞ W := hcs
  let x₀ : S := ⟨center false, ⟨false, rfl⟩⟩
  let z₀ : V x₀ := ⟨center false, by
    change dist (center false) (center false) < 2
    norm_num⟩
  let zΩ : Ω := ⟨(z₀ : H), mem_iUnion.mpr ⟨x₀, z₀.property⟩⟩
  refine ⟨C, hC, δ, hδ, I, hI, hIS, hdisj, ⟨(q zΩ : H), (q zΩ).property⟩,
    cs, hcs, hemb, q, hq, hnearest, ?_, hjets, ?_, hfixed, hnormal⟩
  · intro x z
    have hb := hbounds x z
    let D : H →L[ℝ] H :=
      mfderiv 𝓘(ℝ, H) 𝓘(ℝ, H) (fun y : Ω => (q y : H))
        ⟨(z : H), mem_iUnion.mpr ⟨x, z.property⟩⟩
    have hd : ‖D - tangent.starProjection‖ ≤ 1 / 20 := hb.2
    refine ⟨?_, hd, ?_⟩
    · have hacc : (1 / 20 : ℝ) * 2 = 1 / 10 := by norm_num
      simpa only [hacc] using hb.1
    · have ht : tangentVector ∈ tangent := Submodule.subset_span (mem_singleton tangentVector)
      have hproj : tangent.starProjection tangentVector = tangentVector :=
        tangent.starProjection_eq_self_iff.mpr ht
      have herror : ‖D tangentVector - tangentVector‖ ≤ 1 / 20 := by
        calc
          _ = ‖(D - tangent.starProjection) tangentVector‖ := by
            rw [sub_apply, hproj]
          _ ≤ ‖D - tangent.starProjection‖ * ‖tangentVector‖ :=
            (D - tangent.starProjection).le_opNorm tangentVector
          _ ≤ 1 / 20 := by rw [hnorm, mul_one]; exact hd
      have htri := norm_sub_le (D tangentVector - tangentVector) (D tangentVector)
      have heq : (D tangentVector - tangentVector) - D tangentVector = -tangentVector :=
        sub_sub_cancel_left (D tangentVector) tangentVector
      rw [heq, norm_neg, hnorm] at htri
      linarith
  · dsimp only
    intro x z hz j hj
    simpa only [show (1 / 20 : ℝ) / 3 = 1 / 60 by norm_num] using hfinite x z hz j hj

end NearestJetsExamples


end GC.MetricGeometry
