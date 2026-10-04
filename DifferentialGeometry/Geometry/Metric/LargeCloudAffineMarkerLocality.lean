import DifferentialGeometry.Analysis.InnerProductSpace.AffineMarkerSpectralSection
import DifferentialGeometry.Geometry.Metric.LargeCloudNearestSubmersion

/-! GAF03 (master207B, B:5871) bound to the literal large-cloud spectral construction of
`exists_uniform_large_cloud_buffered_graph_manifold_with_nearest_submersion` (CFS11–CFS14):
the same weights `w`, spectral projector `Q`, section `η` and nearest map. -/

set_option autoImplicit false
noncomputable section
open Set Metric DifferentialGeometry.Analysis
open scoped BigOperators NNReal ContDiff Manifold

namespace GC.MetricGeometry

theorem large_cloud_affine_marker_locality
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    (I : Set H) (hI : I.Finite) (r : H → ℝ) (P : H → Submodule ℝ H) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hr : ∀ i ∈ I, 0 < r i) (x : H)
    (htube : ball x (8 * ε⁻¹ * r x) ⊆ ⋃ i ∈ I, ball i (20 * ε⁻¹ * r i))
    (K : Submodule ℝ H) (c : H)
    (hcontrib : ∀ i ∈ I, (closedBall i (80 * ε⁻¹ * r i) ∩ ball x (8 * ε⁻¹ * r x)).Nonempty →
      K.starProjection i = c ∧ P i ≤ Kᗮ) :
    let w : H → H → ℝ := fun i y => ballCutoff i (40 * ε⁻¹ * r i) (2 * (40 * ε⁻¹ * r i)) y /
        (∑ a ∈ hI.toFinset, ballCutoff a (40 * ε⁻¹ * r a) (2 * (40 * ε⁻¹ * r a)) y)
    let Q : H → Submodule ℝ H := fun y => ⨆ μ ∈ ball (1 : ℝ) (1 / 2), Module.End.eigenspace
        (∑ i ∈ hI.toFinset, w i y • (P i)ᗮ.starProjection).toLinearMap μ
    let η : H → H := fun y => (Q y).starProjection (y - ∑ i ∈ hI.toFinset, w i y • i)
    (∀ z ∈ ball x (8 * ε⁻¹ * r x), K.starProjection (η z) = K.starProjection z - c) ∧
    (∀ z ∈ ball x (8 * ε⁻¹ * r x), η z = 0 → K.starProjection z = c) ∧
    (∀ z ∈ ball x (r x), ∀ q : H, η q = 0 →
      ‖q - (x + (P x).starProjection (z - x))‖ ≤ ε * r x → K.starProjection q = c) := by
  intro w Q η
  set U : Set H := ball x (8 * ε⁻¹ * r x) with hU
  have hden (z : H) (hz : z ∈ U) :
      1 ≤ ∑ a ∈ hI.toFinset, ballCutoff a (40 * ε⁻¹ * r a) (2 * (40 * ε⁻¹ * r a)) z := by
    obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp (htube hz)
    have hri := hr i hi
    apply one_le_sum_ballCutoffs_of_cover hI.toFinset (fun a => a) (fun a => 40 * ε⁻¹ * r a)
      (fun a ha => by have := hr a (hI.mem_toFinset.mp ha); positivity)
    refine ⟨i, hI.mem_toFinset.mpr hi, ?_⟩
    have : dist z i < 20 * ε⁻¹ * r i := hzi
    have h20 : 20 * ε⁻¹ * r i ≤ 40 * ε⁻¹ * r i := by
      have : 0 ≤ ε⁻¹ * r i := by positivity
      nlinarith
    linarith
  have hw : ∀ z ∈ U, ∑ i ∈ hI.toFinset, w i z = 1 := by
    intro z hz
    have h1 := hden z hz
    simp only [w]
    rw [← Finset.sum_div, div_self (by linarith)]
  have hactive (i : H) (hi : i ∈ hI.toFinset) (hne : ∃ z ∈ U, w i z ≠ 0) :
      K.starProjection i = c ∧ P i ≤ Kᗮ := by
    obtain ⟨z, hz, hwz⟩ := hne
    have hiI := hI.mem_toFinset.mp hi
    have hri := hr i hiI
    have hnum : ballCutoff i (40 * ε⁻¹ * r i) (2 * (40 * ε⁻¹ * r i)) z ≠ 0 := by
      intro h0
      apply hwz
      simp only [w, h0, zero_div]
    have hpos : 0 < 40 * ε⁻¹ * r i := by positivity
    have hzball : z ∈ ball i (2 * (40 * ε⁻¹ * r i)) :=
      ballCutoff_support_subset_ball hpos.le (by linarith) hnum
    apply hcontrib i hiI
    refine ⟨z, ?_, hz⟩
    rw [mem_closedBall]
    have h := mem_ball.mp hzball
    linarith
  have hsec := Submodule.affine_marker_weighted_normal_spectral_section hI.toFinset U w hw P
    (fun i => i) K c (fun i hi hne => (hactive i hi hne).1) (fun i hi hne => (hactive i hi hne).2)
  have hzero := Submodule.affine_marker_of_spectral_section_eq_zero hI.toFinset U w hw P
    (fun i => i) K c (fun i hi hne => (hactive i hi hne).1) (fun i hi hne => (hactive i hi hne).2)
  have hfirst : ∀ z ∈ U, K.starProjection (η z) = K.starProjection z - c := hsec
  have hsecond : ∀ z ∈ U, η z = 0 → K.starProjection z = c := hzero
  refine ⟨hfirst, hsecond, ?_⟩
  intro z hz q hq hqval
  apply hsecond q _ hq
  have hzx : ‖z - x‖ < r x := by rw [← dist_eq_norm]; exact hz
  have hrx : 0 < r x := lt_of_le_of_lt (norm_nonneg _) hzx
  have hproj : ‖(P x).starProjection (z - x)‖ ≤ ‖z - x‖ :=
    Submodule.norm_starProjection_apply_le (P x) (z - x)
  have htri : ‖q - x‖ ≤ ‖q - (x + (P x).starProjection (z - x))‖ +
      ‖(P x).starProjection (z - x)‖ := by
    have := norm_add_le (q - (x + (P x).starProjection (z - x))) ((P x).starProjection (z - x))
    rwa [show q - (x + (P x).starProjection (z - x)) + (P x).starProjection (z - x) = q - x by
      abel] at this
  have hinv : 1 ≤ ε⁻¹ := one_le_inv₀ hε |>.mpr hε1
  rw [mem_ball, dist_eq_norm]
  have h8 : 2 * r x ≤ 8 * ε⁻¹ * r x := by nlinarith
  nlinarith

universe u

/-- Consumer: the nearest-point submersion produced by
`exists_uniform_large_cloud_buffered_graph_manifold_with_nearest_submersion` keeps every affine
coordinate that all contributing centres and planes of a core ball share (GAF03, `JP = c`). -/
theorem exists_large_cloud_nearest_map_affine_marker_locality
    (k : ℕ) (B ε : ℝ) (hB : 1 ≤ B) (hε : 0 < ε) (hεsmall : ε ≤ 1 / 10) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧
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
          let w : H → H → ℝ := fun i y =>
              ballCutoff i (40 * ε⁻¹ * r i) (2 * (40 * ε⁻¹ * r i)) y /
              (∑ a ∈ hI.toFinset, ballCutoff a (40 * ε⁻¹ * r a) (2 * (40 * ε⁻¹ * r a)) y)
          let Q : H → Submodule ℝ H := fun y => ⨆ μ ∈ ball (1 : ℝ) (1 / 2),
              Module.End.eigenspace
                (∑ i ∈ hI.toFinset, w i y • (P i)ᗮ.starProjection).toLinearMap μ
          let η : H → H := fun y => (Q y).starProjection
            (y - ∑ i ∈ hI.toFinset, w i y • i)
          ∃ p : H → H, ∀ x ∈ S, ∀ z ∈ ball x (r x),
            η (p z) = 0 ∧
            ‖p z - (x + (P x).starProjection (z - x))‖ ≤ ε * r x ∧
            ∀ (K : Submodule ℝ H) (c : H),
              (∀ i ∈ I, (closedBall i (80 * ε⁻¹ * r i) ∩ ball x (8 * ε⁻¹ * r x)).Nonempty →
                K.starProjection i = c ∧ P i ≤ Kᗮ) →
              K.starProjection (p z) = c := by
  obtain ⟨F, -, δ₀, hδ₀, hproduce⟩ :=
    exists_uniform_large_cloud_buffered_graph_manifold_with_nearest_submersion.{u}
      k B ε hB hε hεsmall
  refine ⟨δ₀, hδ₀, ?_⟩
  intro H _ _ _ S T hST hS r P hdim rmin R δ hrmin hlower hupper hδ hδsmall
    hinterior hscale hcloud
  obtain ⟨I, hI, hIS, -, -, htube, hman, -⟩ :=
    hproduce H S T hST hS r P hdim rmin R δ hrmin hlower hupper hδ hδsmall
      hinterior hscale hcloud
  rcases hman with ⟨-, cs, -, -, q, -, -, hval⟩
  refine ⟨I, hI, hIS, ?_⟩
  intro w Q η
  classical
  let p : H → H := fun z =>
    if h : z ∈ ⋃ x : S, ball (x : H) (r x) then ((q ⟨z, h⟩ : _) : H) else z
  refine ⟨p, ?_⟩
  intro x hx z hz
  have hzΩ : z ∈ ⋃ x : S, ball (x : H) (r x) := mem_iUnion.mpr ⟨⟨x, hx⟩, hz⟩
  have hpz : p z = ((q ⟨z, hzΩ⟩ : _) : H) := dite_eq_left_of_eq_true (eq_true hzΩ)
  have hmem := (q ⟨z, hzΩ⟩).2
  have hηq : η (p z) = 0 := by rw [hpz]; exact hmem.2
  have hvalz : ‖p z - (x + (P x).starProjection (z - x))‖ ≤ ε * r x := by
    rw [hpz]
    exact (hval ⟨x, hx⟩ ⟨z, hz⟩).1
  refine ⟨hηq, hvalz, ?_⟩
  intro K c hcontrib
  have hr : ∀ i ∈ I, 0 < r i := fun i hi => lt_of_lt_of_le hrmin (hlower i (hIS hi))
  have htubex : ball x (8 * ε⁻¹ * r x) ⊆ ⋃ i ∈ I, ball i (20 * ε⁻¹ * r i) :=
    fun y hy => htube (mem_iUnion₂.mpr ⟨x, hx, hy⟩)
  exact (large_cloud_affine_marker_locality I hI r P hε (by linarith) hr x htubex K c
    hcontrib).2.2 z hz (p z) hηq hvalz

end GC.MetricGeometry
