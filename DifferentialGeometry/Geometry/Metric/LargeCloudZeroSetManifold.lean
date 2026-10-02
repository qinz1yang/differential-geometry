import DifferentialGeometry.Geometry.Metric.LargeCloudDisplacementJets
import DifferentialGeometry.Topology.Manifold.SectionZeroSetManifold


set_option autoImplicit false
noncomputable section
open Set Metric DifferentialGeometry.Analysis
open scoped BigOperators NNReal ContDiff Manifold
namespace GC.MetricGeometry
universe u

theorem exists_uniform_large_cloud_zero_set_manifold
    (k : ℕ) (b B : ℝ) (hb : 1 ≤ b) (hB : 1 ≤ B) :
    ∃ C E : ℕ → ℝ≥0, ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
        [FiniteDimensional ℝ H] (S T : Set H), S ⊆ T → TotallyBounded S →
        ∀ (r : H → ℝ) (P : H → Submodule ℝ H),
        (∀ x ∈ S, Module.finrank ℝ (P x) = k) →
        ∀ rmin R δ : ℝ, 0 < rmin →
        (∀ x ∈ S, rmin ≤ r x) → (∀ x ∈ S, r x ≤ R) →
        0 < δ → δ ≤ δ₀ → δ * ((80 * B + 31) * b + 2) < 1 →
        (∀ x ∈ S, ∀ y ∈ S, dist y x ≤ 128 * b * max (r y) (r x) →
          r x / B ≤ r y ∧ r y ≤ B * r x) →
        (∀ x ∈ S, hausdorffEDist (T ∩ ball x (r x / δ))
          ((AffineSubspace.mk' x (P x) : Set H) ∩ ball x (r x / δ)) ≤
            ENNReal.ofReal (δ * r x)) →
        ∃ (I : Set H) (hI : I.Finite), I ⊆ S ∧
          I.PairwiseDisjoint (fun i => ball i (r i)) ∧
          (∀ x ∈ S, ∃ i ∈ I, r x ≤ 2 * r i ∧ dist x i < 3 * r i) ∧
          ((⋃ x ∈ S, ball x (8 * b * r x)) ⊆ ⋃ i ∈ I, ball i (20 * b * r i)) ∧
          let w : H → H → ℝ := fun i y => ballCutoff i (40 * b * r i) (2 * (40 * b * r i)) y /
              (∑ a ∈ hI.toFinset, ballCutoff a (40 * b * r a) (2 * (40 * b * r a)) y)
          let Q : H → Submodule ℝ H := fun y => ⨆ μ ∈ ball (1 : ℝ) (1 / 2), Module.End.eigenspace
              (∑ i ∈ hI.toFinset, w i y • (P i)ᗮ.starProjection).toLinearMap μ
          (∀ m, ∀ x ∈ S, ∀ j ≤ m, ∀ z ∈ ball x (8 * b * r x),
            (∑ i ∈ hI.toFinset, ‖iteratedFDeriv ℝ j (w i) z‖) ≤ (C m : ℝ) / (r x) ^ j) ∧
          (∀ m, ∀ i ∈ I, ∀ j ≤ m, ∀ z ∈ ball i (30 * b * r i),
            (∑ a ∈ hI.toFinset, ‖iteratedFDeriv ℝ j (w a) z‖) ≤ (C m : ℝ) / (r i) ^ j) ∧
          (∀ x ∈ S, ContDiffOn ℝ ∞ (fun y => (Q y).starProjection) (ball x (8 * b * r x)) ∧
              (∀ z ∈ ball x (8 * b * r x), Module.finrank ℝ (Q z) = Module.finrank ℝ H - k ∧
                ‖(Q z).starProjection - (P x)ᗮ.starProjection‖ ≤ 24 * (B + 1) * δ) ∧
              ∀ m : ℕ, ∀ j ≤ m, ∀ z ∈ ball x (8 * b * r x),
                ‖iteratedFDeriv ℝ j (fun y => (Q y).starProjection - (P x)ᗮ.starProjection) z‖ ≤
                  max 4 ((resolventDerivativeBound 4 (C m) j : ℝ) / 2) *
                    (6 * (B + 1)) * δ / (r x) ^ j) ∧
          (∀ i ∈ I, ContDiffOn ℝ ∞ (fun y => (Q y).starProjection) (ball i (30 * b * r i)) ∧
              (∀ z ∈ ball i (30 * b * r i), Module.finrank ℝ (Q z) = Module.finrank ℝ H - k ∧
                ‖(Q z).starProjection - (P i)ᗮ.starProjection‖ ≤ 24 * (B + 1) * δ) ∧
              ∀ m : ℕ, ∀ j ≤ m, ∀ z ∈ ball i (30 * b * r i),
                ‖iteratedFDeriv ℝ j (fun y => (Q y).starProjection - (P i)ᗮ.starProjection) z‖ ≤
                  max 4 ((resolventDerivativeBound 4 (C m) j : ℝ) / 2) *
                    (6 * (B + 1)) * δ / (r i) ^ j) ∧
          let η : H → H := fun y => (Q y).starProjection
            (y-∑ i ∈ hI.toFinset, w i y • i)
          let Ω : Set H := ⋃ i ∈ I, ball i (30*b*r i)
          ContDiffOn ℝ ∞ (fun y => (Q y).starProjection) Ω ∧
          (∀ z ∈ Ω, Module.finrank ℝ (Q z)=Module.finrank ℝ H-k) ∧
          ContDiffOn ℝ ∞ η Ω ∧
          (∀ m, ∀ x ∈ S, ∀ j ≤ m, ∀ z ∈ ball x (8*b*r x),
            ‖iteratedFDeriv ℝ j (fun y => η y-(P x)ᗮ.starProjection (y-x)) z‖ ≤
              (E m : ℝ)*δ*r x*((r x)⁻¹)^j) ∧
          (∀ m, ∀ i ∈ I, ∀ j ≤ m, ∀ z ∈ ball i (30*b*r i),
            ‖iteratedFDeriv ℝ j (fun y => η y-(P i)ᗮ.starProjection (y-i)) z‖ ≤
              (E m : ℝ)*δ*r i*((r i)⁻¹)^j) ∧
          let U : Set H := ⋃ i ∈ I, ball i (20*b*r i)
          let Z : Set H := {z | z ∈ U ∧ η z = 0}
          IsProperMap (fun z : Z => (⟨z.1, z.2.1⟩ : U)) ∧
            ∃ cs : ChartedSpace (Fin k → ℝ) Z,
              let _ := cs
              IsManifold 𝓘(ℝ, Fin k → ℝ) ∞ Z ∧
              _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) ∞
                (Subtype.val : Z → H) := by
  classical
  obtain ⟨C, E, hproduce⟩ := exists_uniform_large_cloud_displacement_jets.{u} k b B hb hB
  let δ₀ : ℝ := 1 / ((E 1 : ℝ) + 1)
  have hden : 0 < (E 1 : ℝ) + 1 := by positivity
  have hδ₀ : 0 < δ₀ := by dsimp only [δ₀]; positivity
  refine ⟨C, E, δ₀, hδ₀, ?_⟩
  intro H _ _ _ S T hST hS r P hdim rmin R δ hrmin hlower hupper hδ hδsmall
    hinterior hscale hcloud
  obtain ⟨I, hI, hIS, hdisj, hcover, htube, hrest⟩ :=
    hproduce H S T hST hS r P hdim rmin R δ hrmin hlower hupper hδ
      hinterior hscale hcloud
  rcases hrest with ⟨hwc, hws, hsc, hss, hQ, hQr, hη, hec, hes⟩
  refine ⟨I, hI, hIS, hdisj, hcover, htube, hwc, hws, hsc, hss,
    hQ, hQr, hη, hec, hes, ?_⟩
  let w : H → H → ℝ := fun i y => ballCutoff i (40*b*r i) (2*(40*b*r i)) y /
    (∑ a ∈ hI.toFinset, ballCutoff a (40*b*r a) (2*(40*b*r a)) y)
  let Q : H → Submodule ℝ H := fun y => ⨆ μ ∈ ball (1 : ℝ) (1/2), Module.End.eigenspace
    (∑ i ∈ hI.toFinset, w i y • (P i)ᗮ.starProjection).toLinearMap μ
  let η : H → H := fun y => (Q y).starProjection (y-∑ i ∈ hI.toFinset, w i y • i)
  let U : Set H := ⋃ i ∈ I, ball i (20*b*r i)
  let V : I → Set H := fun i => ball (i : H) (20*b*r i)
  have hr (i : I) : 0 < r i := hrmin.trans_le (hlower i (hIS i.property))
  have hbpos : 0 < b := zero_lt_one.trans_le hb
  have hV30 (i : I) : V i ⊆ ball (i : H) (30*b*r i) := by
    intro z hz
    have hh : dist z (i : H) < 20*b*r i := hz
    change dist z (i : H) < 30*b*r i
    nlinarith [mul_pos hbpos (hr i)]
  have hVU : (⋃ i : I, V i) = U := by
    ext z
    constructor
    · intro hz
      obtain ⟨i, hi⟩ := mem_iUnion.mp hz
      exact mem_iUnion₂.mpr ⟨i, i.property, hi⟩
    · intro hz
      obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp hz
      exact mem_iUnion.mpr ⟨⟨i, hi⟩, hzi⟩
  have hηV : ContDiffOn ℝ ∞ η (⋃ i : I, V i) := by
    apply hη.mono
    intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    exact mem_iUnion₂.mpr ⟨i, i.property, hV30 i hi⟩
  have hEδ : (E 1 : ℝ)*δ < 1 := by
    calc
      (E 1 : ℝ)*δ ≤ (E 1 : ℝ)*δ₀ :=
        mul_le_mul_of_nonneg_left hδsmall (E 1).coe_nonneg
      _ < 1 := by
        have hh : (E 1 : ℝ) / ((E 1 : ℝ)+1) < 1 :=
          (div_lt_one hden).mpr (by linarith)
        simpa only [δ₀, div_eq_mul_inv, one_mul] using hh
  have hcoef : 24*(B+1) ≤ (80*B+31)*b+2 := by
    have hB0 : 0 ≤ B := le_trans (by norm_num) hB
    have hh := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 80*B+31)
    nlinarith
  have hgapnum : 24*(B+1)*δ < 1 := by
    calc
      24*(B+1)*δ ≤ ((80*B+31)*b+2)*δ :=
        mul_le_mul_of_nonneg_right hcoef hδ.le
      _ < 1 := by simpa only [mul_comm] using hinterior
  have hgap (i : I) (z : H) (hz : z ∈ V i) :
      ‖(Q z).starProjection-(P i)ᗮ.starProjection‖ < 1 :=
    (((hss i i.property).2.1 z (hV30 i hz)).2).trans_lt hgapnum
  have herror (i : I) (z : H) (hz : z ∈ V i) :
      ‖fderiv ℝ (fun y => η y-(P i)ᗮ.starProjection (y-(i : H))) z‖ < 1 := by
    have hh := hes 1 i i.property 1 (le_refl 1) z (hV30 i hz)
    have hbound : ‖fderiv ℝ (fun y => η y-(P i)ᗮ.starProjection (y-(i : H))) z‖ ≤
        (E 1 : ℝ)*δ := by
      calc
        _ ≤ (E 1 : ℝ)*δ*r i*(r i)⁻¹ := by
          simpa only [norm_iteratedFDeriv_one, pow_one] using hh
        _ = _ := by rw [mul_assoc, mul_inv_cancel₀ (hr i).ne', mul_one]
    exact hbound.trans_lt hEδ
  have hman := DifferentialGeometry.Topology.Manifold.exists_section_zero_set_manifold_of_open_cover
    k V (fun _ => isOpen_ball) (fun i : I => P i)
    (fun i => hdim i (hIS i.property)) (fun i : I => (i : H)) η Q hηV
    (fun _ z _ => (Q z).starProjection_apply_mem _) hgap herror
  dsimp only at hman
  rw [hVU] at hman
  exact hman

end GC.MetricGeometry
