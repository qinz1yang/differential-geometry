import DifferentialGeometry.Topology.MetricSpace.VariableRadiusCover
import DifferentialGeometry.Geometry.Metric.LargeSupportPacking
import DifferentialGeometry.Geometry.Metric.AffinePlaneCoherence

set_option autoImplicit false
noncomputable section
open Set Metric
namespace GC.MetricGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem large_cloud_selected_center_geometry
    (S T : Set H) (hST : S ⊆ T) (r : H → ℝ) (P : S → Submodule ℝ H)
    [∀ x : S, FiniteDimensional ℝ (P x)]
    (k : ℕ) (hdim : ∀ x : S, Module.finrank ℝ (P x) = k)
    (I : Set H) (hIS : I ⊆ S) (hI : I.Finite)
    (hdisj : I.PairwiseDisjoint (fun i => ball i (r i)))
    (hr : ∀ x ∈ S, 0 < r x)
    (b B δ : ℝ) (hb : 1 ≤ b) (hB : 1 ≤ B) (hδ : 0 < δ)
    (hδinterior : δ * ((80 * B + 31) * b + 2) < 1)
    (hscale : ∀ x ∈ S, ∀ y ∈ S, dist y x ≤ 128 * b * max (r y) (r x) →
      r x / B ≤ r y ∧ r y ≤ B * r x)
    (hcloud : ∀ x : S,
      hausdorffEDist (T ∩ ball x (r x / δ))
        ((AffineSubspace.mk' (x : H) (P x) : Set H) ∩ ball x (r x / δ)) ≤
          ENNReal.ofReal (δ * r x)) :
    ∀ x : S,
      let J : Set H := I ∩ {i | (closedBall i (80 * b * r i) ∩ ball x (30 * b * r x)).Nonempty}
      (J.ncard : ℝ) ≤ (1 + 2 * B * (80 * B + 31) * b) ^ k ∧
      ∀ (i : H) (hi : i ∈ J), r x / B ≤ r i ∧ r i ≤ B * r x ∧
        dist i x < (80 * B + 31) * b * r x ∧
        ‖(P x)ᗮ.starProjection (i - x)‖ ≤ δ * r x ∧
        ‖(P ⟨i, hIS hi.1⟩)ᗮ.starProjection - (P x)ᗮ.starProjection‖ ≤ 6 * (B + 1) * δ := by
  let D : ℝ := 80 * B + 31
  have hδcoherence : δ < 1 / (4 * (B + 1)) := by
    apply (lt_div_iff₀ (by linarith : 0 < 4 * (B + 1))).mpr
    have hDb : 4 * (B + 1) ≤ (80 * B + 31) * b + 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hb (by linarith : 0 ≤ 80 * B + 31)]
    exact (mul_le_mul_of_nonneg_left hDb hδ.le).trans_lt hδinterior
  have hδDb : δ * D * b < 1 := by
    change δ * (D * b + 2) < 1 at hδinterior
    nlinarith
  intro x
  have hflat (i : H) (hi : i ∈ I) (hdist : dist i x < r x / δ) :
      infDist i (AffineSubspace.mk' (x : H) (P x) : Set H) ≤ δ * r x := by
    have he : infEDist i (AffineSubspace.mk' (x : H) (P x) : Set H) ≤ ENNReal.ofReal (δ * r x) :=
      (infEDist_anti inter_subset_left).trans
        ((infEDist_le_hausdorffEDist_of_mem
          (show i ∈ T ∩ ball x (r x / δ) from ⟨hST (hIS hi),hdist⟩)).trans (hcloud x))
    simpa only [Metric.infDist, ENNReal.toReal_ofReal (mul_pos hδ (hr x x.property)).le] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top he
  obtain ⟨hlocal,hcard⟩ := large_support_packing_of_local_scale_control I hI r (P x)
    x (r x) b B δ (hr x x.property) hb hB (fun i hi => hr i (hIS hi)) hdisj
    (fun i hi hdist => hscale x x.property i (hIS hi) hdist) hflat hδ hδDb
  refine ⟨by simpa only [hdim x] using hcard, ?_⟩
  intro i hi
  obtain ⟨hlo,hup,hdist⟩ := hlocal i hi
  refine ⟨hlo,hup,hdist,?_⟩
  have hc : ‖i - x‖ ≤ (D * b) * r x := by
    simpa only [dist_eq_norm] using hdist.le
  obtain ⟨hoff,hproj⟩ := normal_offset_and_projection_gap_le_of_large_affine_hausdorffEDist
    (P x) (P ⟨i, hIS hi.1⟩) (by rw [hdim x, hdim ⟨i, hIS hi.1⟩]) T x i (hST (hIS hi.1))
    (hr x x.property) hB hlo hup hc hδ hδcoherence hδinterior
    (hcloud x) (hcloud ⟨i, hIS hi.1⟩)
  refine ⟨hoff,?_⟩
  rw [norm_sub_rev]
  exact hproj

theorem exists_large_cloud_cover_of_hausdorffEDist_le
    (S T : Set H) (hST : S ⊆ T) (hS : TotallyBounded S)
    (r : H → ℝ) (P : S → Submodule ℝ H)
    [∀ x : S, FiniteDimensional ℝ (P x)]
    (k : ℕ) (hdim : ∀ x : S, Module.finrank ℝ (P x) = k)
    (rmin R b B δ : ℝ) (hrmin : 0 < rmin)
    (hlower : ∀ x ∈ S, rmin ≤ r x) (hupper : ∀ x ∈ S, r x ≤ R)
    (hb : 1 ≤ b) (hB : 1 ≤ B) (hδ : 0 < δ)
    (hδinterior : δ * ((80 * B + 31) * b + 2) < 1)
    (hscale : ∀ x ∈ S, ∀ y ∈ S, dist y x ≤ 128 * b * max (r y) (r x) →
      r x / B ≤ r y ∧ r y ≤ B * r x)
    (hcloud : ∀ x : S,
      hausdorffEDist (T ∩ ball x (r x / δ))
        ((AffineSubspace.mk' (x : H) (P x) : Set H) ∩ ball x (r x / δ)) ≤
          ENNReal.ofReal (δ * r x)) :
    let D : ℝ := 80 * B + 31
    ∃ (I : Set H) (hIS : I ⊆ S), I.Finite ∧
      I.PairwiseDisjoint (fun i => ball i (r i)) ∧
      (∀ x ∈ S, ∃ i ∈ I, r x ≤ 2 * r i ∧ dist x i < 3 * r i) ∧
      ((⋃ x ∈ S, ball x (8 * b * r x)) ⊆ ⋃ i ∈ I, ball i (20 * b * r i)) ∧
      ∀ x : S,
        let J : Set H := I ∩ {i | (closedBall i (80 * b * r i) ∩ ball x (30 * b * r x)).Nonempty}
        (J.ncard : ℝ) ≤ (1 + 2 * B * D * b) ^ k ∧
        ∀ (i : H) (hi : i ∈ J), r x / B ≤ r i ∧ r i ≤ B * r x ∧ dist i x < D * b * r x ∧
          ‖(P x)ᗮ.starProjection (i - x)‖ ≤ δ * r x ∧
          ‖(P ⟨i, hIS hi.1⟩)ᗮ.starProjection - (P x)ᗮ.starProjection‖ ≤ 6 * (B + 1) * δ := by
  classical
  have hbpos : 0 < b := zero_lt_one.trans_le hb
  have hr (x : H) (hx : x ∈ S) : 0 < r x := hrmin.trans_le (hlower x hx)
  obtain ⟨I,hIS,hI,hdisj,hcover,hlarge⟩ :=
    Metric.exists_finite_disjoint_ball_selection_all_enlargements S hS r hrmin hlower hupper
  refine ⟨I,hIS,hI,hdisj,hcover,?_,?_⟩
  · intro z hz
    have hz' : z ∈ ⋃ i ∈ I, ball i ((2 * (8 * b) + 3) * r i) :=
      hlarge (8 * b) (by positivity) (by simpa only [mul_assoc] using hz)
    obtain ⟨i,hi,hzi⟩ := mem_iUnion₂.mp hz'
    refine mem_iUnion₂.mpr ⟨i,hi,?_⟩
    change dist z i < (2 * (8 * b) + 3) * r i at hzi
    change dist z i < 20 * b * r i
    apply hzi.trans_le
    have hri := hr i (hIS hi)
    nlinarith
  · exact large_cloud_selected_center_geometry S T hST r P k hdim I hIS hI hdisj hr
      b B δ hb hB hδ hδinterior hscale hcloud

end GC.MetricGeometry
