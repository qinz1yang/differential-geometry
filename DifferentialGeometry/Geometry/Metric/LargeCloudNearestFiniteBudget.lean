import DifferentialGeometry.Geometry.Metric.LargeCloudNearestAllJets
import DifferentialGeometry.Geometry.Metric.LargeCloudNearestJetsExamples
import DifferentialGeometry.Topology.Manifold.NearestNormalProjector

/-! Finite accuracy budgets and actual-zero normals of the unchanged nearest map. -/

set_option autoImplicit false
noncomputable section
open Set Metric Filter DifferentialGeometry.Analysis
open scoped BigOperators NNReal ContDiff Manifold
namespace GC.MetricGeometry
universe u

def finiteCloudJetBudget (F C : ℕ → ℝ) (K : ℕ) : ℝ :=
  1 + F (K + 1) + ∑ j ∈ Finset.range (K + 2), C j

theorem finiteCloudJetBudget_pos (F C : ℕ → ℝ) (K : ℕ)
    (hF : ∀ m, 0 ≤ F m) (hC : ∀ j, 0 ≤ C j) : 0 < finiteCloudJetBudget F C K := by
  have hsum : 0 ≤ ∑ j ∈ Finset.range (K + 2), C j :=
    Finset.sum_nonneg (fun j hj => hC j)
  have hFK := hF (K + 1)
  dsimp only [finiteCloudJetBudget]
  linarith

theorem finiteCloudJetBudget_coefficient_le (F C : ℕ → ℝ) (K : ℕ)
    (hF : ∀ m, 0 ≤ F m) (hC : ∀ j, 0 ≤ C j) {j : ℕ} (hj : j ≤ K + 1) :
    C j ≤ finiteCloudJetBudget F C K := by
  have hmem : j ∈ Finset.range (K + 2) := Finset.mem_range.mpr (by omega)
  have hsum := Finset.single_le_sum (fun i hi => hC i) hmem
  have hFK := hF (K + 1)
  dsimp only [finiteCloudJetBudget]
  linarith

theorem finiteCloudJetBudget_graph_le (F C : ℕ → ℝ) (K : ℕ)
    (hC : ∀ j, 0 ≤ C j) : F (K + 1) ≤ finiteCloudJetBudget F C K := by
  have hsum : 0 ≤ ∑ j ∈ Finset.range (K + 2), C j :=
    Finset.sum_nonneg (fun j hj => hC j)
  dsimp only [finiteCloudJetBudget]
  linarith

theorem nearestAmbientExtension_error_mfderiv_norm {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    {k : ℕ} {Z : Set H}
    [ChartedSpace (Fin k → ℝ) Z] (Ω : TopologicalSpace.Opens H)
    (p : C^∞⟮𝓘(ℝ, H), Ω; 𝓘(ℝ, Fin k → ℝ), Z⟯)
    (hemb : _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) ∞
      (Subtype.val : Z → H)) (L : Submodule ℝ H) (o : H) (z : Ω) :
    let D : H →L[ℝ] H := mfderiv 𝓘(ℝ, H) 𝓘(ℝ, H) (fun y : Ω => (p y : H)) z
    ‖D - L.starProjection‖ = ‖iteratedFDeriv ℝ 1
      (fun y => nearestAmbientExtension Ω Z p y - (o + L.starProjection (y - o))) (z : H)‖ := by
  classical
  let a : H → H := nearestAmbientExtension Ω Z p
  have heq : (fun y : Ω => a y) = (fun y : Ω => (p y : H)) := by
    funext y
    exact dite_eq_left y.property
  have hmd : MDifferentiableAt 𝓘(ℝ, H) 𝓘(ℝ, H) (fun y : Ω => a y) z := by
    rw [heq]
    exact (hemb.contMDiff.mdifferentiableAt (by simp)).comp z
      (p.contMDiff.mdifferentiableAt (by simp))
  have ha : DifferentiableAt ℝ a (z : H) :=
    (DifferentialGeometry.mdifferentiableAt_subtype_iff.mp hmd).differentiableAt
  have hd : (mfderiv 𝓘(ℝ, H) 𝓘(ℝ, H) (fun y : Ω => (p y : H)) z : H →L[ℝ] H) =
      fderiv ℝ a (z : H) := by
    rw [← heq, DifferentialGeometry.mfderiv_restrict_open, mfderiv_eq_fderiv]
    rfl
  have hlin : HasFDerivAt (fun y : H => o + L.starProjection (y - o))
      L.starProjection (z : H) := by
    simpa only [Function.comp_def, ContinuousLinearMap.comp_id, id_eq] using
      (L.starProjection.hasFDerivAt.comp (z : H)
        ((hasFDerivAt_id (z : H)).sub_const o)).const_add o
  dsimp only
  change ‖_ - L.starProjection‖ =
    ‖iteratedFDeriv ℝ 1 (fun y => a y - (o + L.starProjection (y - o))) (z : H)‖
  rw [hd, norm_iteratedFDeriv_one, fderiv_fun_sub ha hlin.differentiableAt, hlin.fderiv]

theorem nearestMap_dist_eq_zero_on_original_zeros {H : Type*} [PseudoMetricSpace H]
    (Ω : Set H) (Z : Set H) (p : Ω → Z)
    (hnearest : ∀ x : Ω, IsMinOn (fun y => dist (x : H) y) Z (p x : H))
    (z : Z) (hz : (z : H) ∈ Ω) : dist (p ⟨(z : H), hz⟩ : H) z = 0 := by
  have hle := hnearest ⟨(z : H), hz⟩ z.property
  change dist (z : H) (p ⟨(z : H), hz⟩ : H) ≤ dist (z : H) z at hle
  rw [dist_self] at hle
  exact le_antisymm (by simpa only [dist_comm] using hle) dist_nonneg

theorem exists_uniform_large_cloud_nearest_finite_budget
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
  obtain ⟨F, hF, C, hC, δc, hδc, hproduce⟩ :=
    exists_uniform_large_cloud_nearest_all_jets.{u} k B ε hB hε hεsmall
  let A : ℝ := finiteCloudJetBudget F C K
  have hA : 0 < A := finiteCloudJetBudget_pos F C K hF hC
  let δ₀ : ℝ := min δc (ε / (3 * A))
  have hδ₀ : 0 < δ₀ := lt_min hδc (div_pos hε (by positivity))
  refine ⟨F, hF, C, hC, δ₀, hδ₀, min_le_right _ _, ?_⟩
  intro H instNorm instInner instFinite S T hST hS r P hdim rmin R δ hrmin hlower hupper
    hδ hδsmall hinterior hscale hcloud
  have hbudget : δ * (3 * A) ≤ ε :=
    (le_div_iff₀ (by positivity : 0 < 3 * A)).mp
      (hδsmall.trans (min_le_right _ _))
  have hCbudget (j : ℕ) (hj : j ≤ K + 1) : C j * δ ≤ ε / 3 := by
    have hcoef : C j ≤ A := finiteCloudJetBudget_coefficient_le F C K hF hC hj
    have hmul := mul_le_mul_of_nonneg_right hcoef hδ.le
    nlinarith
  have hFbudget : F (K + 1) * δ ≤ ε / 3 := by
    have hcoef : F (K + 1) ≤ A := finiteCloudJetBudget_graph_le F C K hC
    have hmul := mul_le_mul_of_nonneg_right hcoef hδ.le
    nlinarith
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
  have hscaled (x : S) (z : H) (hz : z ∈ ball (x : H) (r x)) (j : ℕ)
      (hj : j ≤ K + 1) :
      ‖iteratedFDeriv ℝ j
        (fun y => nearestAmbientExtension Ω Z p y -
          ((x : H) + (P x).starProjection (y - x))) z‖ ≤
            (ε / 3) * r x * ((r x)⁻¹) ^ j := by
    have hr : 0 < r x := lt_of_lt_of_le hrmin (hlower x x.property)
    exact (hjets x z hz j).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hCbudget j hj) (by linarith [hlower x x.property]))
        (by positivity))
  have hfixed (z : Z) (hz : (z : H) ∈ Ω) : p ⟨(z : H), hz⟩ = z :=
    Subtype.ext (dist_eq_zero.mp
      (nearestMap_dist_eq_zero_on_original_zeros Ω Z p (fun y => (hnearest y).1) z hz))
  refine ⟨I, hI, hIS, hdisj, hcover, htube,
    ⟨hproper, cs, hcs, hemb, p, hp, hnearest, hbounds, hjets, ?_, hfixed, ?_⟩,
    hproperCore, hprox, hcoverage, g, ?_⟩
  · dsimp only
    intro x z hz j hj
    exact hscaled x z hz j (by omega)
  · intro x z hz
    let zΩ : Ω := ⟨(z : H), mem_iUnion.mpr ⟨x, hz⟩⟩
    have hclose :
        let D : H →L[ℝ] H := mfderiv 𝓘(ℝ, H) 𝓘(ℝ, H) (fun y : Ω => (p y : H)) zΩ
        ‖D - (P x).starProjection‖ ≤ ε / 3 := by
      have hh := hscaled x z hz 1 (by omega)
      have hr : 0 < r x := lt_of_lt_of_le hrmin (hlower x x.property)
      have hjet1 : ‖iteratedFDeriv ℝ 1
          (fun y => nearestAmbientExtension Ω Z p y -
            ((x : H) + (P x).starProjection (y - x))) (z : H)‖ ≤ ε / 3 := by
        simpa only [pow_one, mul_assoc, mul_inv_cancel₀ hr.ne', mul_one] using hh
      exact (nearestAmbientExtension_error_mfderiv_norm Ω p hemb (P x) x zΩ).trans_le hjet1
    have hnormal := norm_actualZeroSetNormalProjector_sub_le Ω p hemb hp (P x)
      (hdim x x.property) (ε / 3) (by positivity) (by linarith) zΩ hclose
    rw [hfixed z zΩ.property] at hnormal
    calc
      _ ≤ 3 * (ε / 3) := hnormal
      _ = ε := by ring
  · intro x
    refine ⟨(hg x).1, (hg x).2.1, (hg x).2.2.1, (hg x).2.2.2.1, (hg x).2.2.2.2, ?_⟩
    intro t ht j hj
    have hr : 0 < r x := lt_of_lt_of_le hrmin (hlower x x.property)
    exact ((hg x).2.2.2.1 (K + 1) t ht j hj).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hFbudget (by linarith [hlower x x.property]))
        (by positivity))

namespace NearestJetsExamples

theorem two_center_cloud_has_finite_budget_nearest_jets :
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
             ∀ x : S, ∀ z ∈ ball (x : H) 2, ∀ j ≤ 2,
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
    exists_uniform_large_cloud_nearest_finite_budget
      1 2 1 (1 / 20) (by norm_num) (by norm_num) (by norm_num)
  let δ : ℝ := min δ₀ (1 / 4444)
  have hδ : 0 < δ := lt_min hδ₀ (by norm_num)
  have hinterior : δ * ((80 * (1 : ℝ) + 31) * (1 / 20 : ℝ)⁻¹ + 2) < 1 := by
    have hsmall : δ ≤ 1 / 4444 := min_le_right _ _
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
      (by intro x hx y hy hxy; constructor <;> norm_num) hcloud
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
