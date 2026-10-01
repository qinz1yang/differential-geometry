import DifferentialGeometry.Geometry.Metric.CloudDisplacementJets
import DifferentialGeometry.Topology.Manifold.NormalSectionSubmersion
import Mathlib.Topology.Maps.Proper.Basic

set_option autoImplicit false
noncomputable section
open Set Metric DifferentialGeometry.Analysis
open scoped BigOperators NNReal ContDiff Manifold
namespace GC.MetricGeometry
universe u

theorem exists_uniform_cloud_local_submersion
    (k : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
        [FiniteDimensional ℝ H] (S T : Set H), S ⊆ T → TotallyBounded S →
        ∀ (r : H → ℝ) (P : H → Submodule ℝ H),
        (∀ x ∈ S, Module.finrank ℝ (P x) = k) →
        ∀ rmin R δ : ℝ, 0 < rmin →
        (∀ x ∈ S, rmin ≤ r x) → (∀ x ∈ S, r x ≤ R) →
        0 < δ → δ ≤ δ₀ →
        (∀ x ∈ S, ∀ y ∈ S, |r y - r x| ≤ C * (dist x y + r x)) →
        (∀ x ∈ S, hausdorffEDist (T ∩ ball x (r x / δ))
          ((AffineSubspace.mk' x (P x) : Set H) ∩ ball x (r x / δ)) ≤
            ENNReal.ofReal (δ * r x)) →
        let ℓ : ℝ := 1 / (100 * (C + 1))
        ∃ (I : Set H) (hI : I.Finite), I ⊆ S ∧
          I.PairwiseDisjoint (fun i => ball i (ℓ * r i)) ∧
          ((⋃ x ∈ S, ball x (ℓ * r x)) ⊆ ⋃ i ∈ I, ball i (5 * ℓ * r i)) ∧
          let w : H → H → ℝ := fun i y =>
            ballCutoff i (10 * ℓ * r i) (2 * (10 * ℓ * r i)) y /
              (∑ a ∈ hI.toFinset, ballCutoff a (10 * ℓ * r a) (2 * (10 * ℓ * r a)) y)
          let Q : H → Submodule ℝ H := fun y =>
            ⨆ μ ∈ ball (1 : ℝ) (1 / 2), Module.End.eigenspace
              (∑ i ∈ hI.toFinset, w i y • (P i)ᗮ.starProjection).toLinearMap μ
          let η : H → H := fun y => (Q y).starProjection
            (y - ∑ i ∈ hI.toFinset, w i y • i)
          let Ω : Set H := ⋃ i ∈ I, ball i (6 * ℓ * r i)
          ContDiffOn ℝ ∞ η Ω ∧
          (IsClosed {z : Ω | η z = 0} ∧
            IsProperMap (fun z : {z : Ω | η z = 0} => (z : Ω))) ∧
          (∀ z ∈ ⋃ i ∈ I, ball i (6 * ℓ * r i),
            Module.finrank ℝ (Q z) = Module.finrank ℝ H - k) ∧
          ∀ x₀ ∈ I, ∀ v ∈ ball x₀ (5 * ℓ * r x₀),
            (∀ z ∈ ball v (ℓ * r x₀), Manifold.IsSubmersionAt
              𝓘(ℝ, H) 𝓘(ℝ, (P x₀)ᗮ) ∞
                (fun y => (P x₀)ᗮ.orthogonalProjectionOnto (η y)) z) ∧
            {z : H | z ∈ ball v (ℓ * r x₀) ∧
              (P x₀)ᗮ.orthogonalProjectionOnto (η z) = 0} =
            {z : H | z ∈ ball v (ℓ * r x₀) ∧ η z = 0} := by
  classical
  obtain ⟨B, E, hproducer⟩ := exists_uniform_cloud_displacement_jets.{u} k C hC
  let ℓ : ℝ := 1 / (100 * (C + 1))
  let A : ℝ := 2 * (C + 1)
  let K : ℝ := 24 * (A + 1)
  have hℓ : 0 < ℓ := by dsimp [ℓ]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let δ₀ : ℝ := min (ℓ / (2 * A))
    (min (1 / (2 * ((E 1 : ℝ) + 1))) (1 / (2 * (K + 1))))
  have hδ₀ : 0 < δ₀ := by dsimp [δ₀]; positivity
  refine ⟨δ₀, hδ₀, ?_⟩
  intro H _ _ _ S T hST hS r P hdim rmin R δ hrmin hlower hupper hδ hδsmall hscale hcloud
  have hbudget : δ ≤ ℓ / (2 * A) := hδsmall.trans (min_le_left _ _)
  have hEδ : (E 1 : ℝ) * δ < 1 := by
    have hb : δ ≤ 1 / (2 * ((E 1 : ℝ) + 1)) :=
      hδsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hh := (le_div_iff₀ (by positivity : 0 < 2 * ((E 1 : ℝ) + 1))).mp hb
    nlinarith [(E 1).coe_nonneg]
  have hKδ : K * δ < 1 := by
    have hb : δ ≤ 1 / (2 * (K + 1)) :=
      hδsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hh := (le_div_iff₀ (by positivity : 0 < 2 * (K + 1))).mp hb
    nlinarith
  obtain ⟨I, hI, hIS, hdisj, hcover, _hw, _hQ, hrank, hη, hlocal⟩ :=
    hproducer H S T hST hS r P hdim rmin R δ hrmin hlower hupper hδ hbudget hscale hcloud
  let w : H → H → ℝ := fun i y =>
    ballCutoff i (10 * ℓ * r i) (2 * (10 * ℓ * r i)) y /
      (∑ a ∈ hI.toFinset, ballCutoff a (10 * ℓ * r a) (2 * (10 * ℓ * r a)) y)
  let Q : H → Submodule ℝ H := fun y =>
    ⨆ μ ∈ ball (1 : ℝ) (1 / 2), Module.End.eigenspace
      (∑ i ∈ hI.toFinset, w i y • (P i)ᗮ.starProjection).toLinearMap μ
  let η : H → H := fun y => (Q y).starProjection
    (y - ∑ i ∈ hI.toFinset, w i y • i)
  let Ω : Set H := ⋃ i ∈ I, ball i (6 * ℓ * r i)
  have hclosed : IsClosed {z : Ω | η z = 0} :=
    isClosed_eq hη.continuousOn.domRestrict continuous_const
  refine ⟨I, hI, hIS, hdisj, hcover, hη,
    ⟨hclosed, hclosed.isProperMap_subtypeVal⟩, hrank, ?_⟩
  dsimp only
  intro x₀ hx₀ v hv
  have hr₀ : 0 < r x₀ := hrmin.trans_le (hlower x₀ (hIS hx₀))
  have hUΩ : ball v (ℓ * r x₀) ⊆ ⋃ i ∈ I, ball i (6 * ℓ * r i) := by
    intro z hz
    apply mem_iUnion₂.mpr ⟨x₀, hx₀, ?_⟩
    have ht := dist_triangle z v x₀
    have hv' : dist v x₀ < 5 * ℓ * r x₀ := hv
    have hz' : dist z v < ℓ * r x₀ := hz
    change dist z x₀ < 6 * ℓ * r x₀
    linarith
  have hηU : ContDiffOn ℝ ∞ η (ball v (ℓ * r x₀)) := hη.mono hUΩ
  have herror (z : H) (hz : z ∈ ball v (ℓ * r x₀)) :
      ‖fderiv ℝ (fun y => η y - (P x₀)ᗮ.starProjection (y - x₀)) z‖ < 1 := by
    have hb := ((hlocal x₀ hx₀ v hv).2.2 1 1 le_rfl z hz).2
    have heq : (E 1 : ℝ) * δ * r x₀ * (r x₀)⁻¹ ^ (1 : ℕ) = (E 1 : ℝ) * δ := by
      rw [pow_one, mul_assoc, mul_inv_cancel₀ hr₀.ne', mul_one]
    rw [heq, norm_iteratedFDeriv_one] at hb
    exact hb.trans_lt hEδ
  refine ⟨Submodule.isSubmersionAt_orthogonalProjectionOnto_of_affine_error
    (P x₀)ᗮ η x₀ isOpen_ball hηU herror, ?_⟩
  apply Submodule.orthogonalProjectionOnto_projected_displacement_zeroSet
  intro z hz
  exact (((hlocal x₀ hx₀ v hv).2.1 z hz).2).trans_lt hKδ

end GC.MetricGeometry
