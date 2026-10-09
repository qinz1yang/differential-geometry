import DifferentialGeometry.Geometry.Metric.LargeCloudNearestAllJets
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! A concrete two-centre affine cloud consuming the unchanged full-union all-order map. -/

set_option autoImplicit false
noncomputable section
open Set Metric DifferentialGeometry.Analysis GC.MetricGeometry
open scoped BigOperators ContDiff Manifold

namespace GC.MetricGeometry.NearestJetsExamples

abbrev H := EuclideanSpace ℝ (Fin 2)

def tangentVector : H := EuclideanSpace.single 0 1

def offset : H := EuclideanSpace.single 1 1

def tangent : Submodule ℝ H := Submodule.span ℝ {tangentVector}

def center (b : Bool) : H := if b then offset + tangentVector else offset

def domain (b : Bool) : TopologicalSpace.Opens H := ⟨ball (center b) 2, isOpen_ball⟩

private theorem tangent_norm : ‖tangentVector‖ = 1 := by
  simp [tangentVector, EuclideanSpace.single, PiLp.norm_single]

theorem distinct_centers_and_nonempty_overlap :
    dist (center false) (center true) = 1 ∧
      offset ∈ (domain false : Set H) ∩ (domain true : Set H) := by
  have hd : dist (center false) (center true) = 1 := by
    change ‖offset - (offset + tangentVector)‖ = 1
    have heq : offset - (offset + tangentVector) = -tangentVector := by abel
    rw [heq, norm_neg, tangent_norm]
  refine ⟨hd, ?_, ?_⟩
  · change dist offset offset < 2
    norm_num
  · change dist (center false) (center true) < 2
    rw [hd]
    norm_num

theorem two_center_cloud_has_uniform_nearest_jets :
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
                   C j * δ * 2 * ((2 : ℝ)⁻¹) ^ j) := by
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
  obtain ⟨_F, _hF, C, hC, δ₀, hδ₀, hproduce⟩ :=
    exists_uniform_large_cloud_nearest_all_jets
      1 1 (1 / 20) (by norm_num) (by norm_num) (by norm_num)
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
  rcases hrest.1.2 with ⟨cs, hcs, hemb, q, hq, hnearest, hbounds, hjets⟩
  let : ChartedSpace (Fin 1 → ℝ) W := cs
  let : IsManifold 𝓘(ℝ, Fin 1 → ℝ) ∞ W := hcs
  let x₀ : S := ⟨center false, ⟨false, rfl⟩⟩
  let z₀ : V x₀ := ⟨center false, by
    change dist (center false) (center false) < 2
    norm_num⟩
  let zΩ : Ω := ⟨(z₀ : H), mem_iUnion.mpr ⟨x₀, z₀.property⟩⟩
  refine ⟨C, hC, δ, hδ, I, hI, hIS, hdisj, ⟨(q zΩ : H), (q zΩ).property⟩,
    cs, hcs, hemb, q, hq, hnearest, ?_, hjets⟩
  intro x z
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

end GC.MetricGeometry.NearestJetsExamples
