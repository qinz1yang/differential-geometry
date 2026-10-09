import DifferentialGeometry.Geometry.Metric.LargeCloudZeroSetManifold
import DifferentialGeometry.Analysis.InnerProductSpace.BufferedSectionGraphFamily
import DifferentialGeometry.Geometry.Metric.ZeroSetCloudProximity


set_option autoImplicit false
noncomputable section
open Set Metric DifferentialGeometry.Analysis
open scoped BigOperators NNReal ContDiff Manifold
namespace GC.MetricGeometry
universe u

theorem exists_uniform_large_cloud_buffered_graph_manifold_with_proximity
    (k : ℕ) (b B ε : ℝ) (hb : 1 ≤ b) (hB : 1 ≤ B) (hε : 0 < ε) :
    ∃ F : ℕ → ℝ, (∀ m, 0 ≤ F m) ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
        [FiniteDimensional ℝ H] (S T : Set H), S ⊆ T → TotallyBounded S →
        ∀ (r : H → ℝ) (P : H → Submodule ℝ H),
        (∀ x ∈ S, Module.finrank ℝ (P x) = k) →
        ∀ rmin R δ : ℝ, 0 < rmin →
        (∀ x ∈ S, rmin ≤ r x) → (∀ x ∈ S, r x ≤ R) →
        0 < δ → δ ≤ δ₀ → δ * ((80 * B + 31) * b + 2) < 1 →
        (∀ x ∈ T, ∀ y ∈ T, dist y x ≤ 128 * b * max (r y) (r x) →
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
          let η : H → H := fun y => (Q y).starProjection
            (y - ∑ i ∈ hI.toFinset, w i y • i)
          let U : Set H := ⋃ i ∈ I, ball i (20 * b * r i)
          let Z : Set H := {z | z ∈ U ∧ η z = 0}
          (IsProperMap (fun z : Z => (⟨z.1, z.2.1⟩ : U)) ∧
            ∃ cs : ChartedSpace (Fin k → ℝ) Z,
              let _ := cs
              IsManifold 𝓘(ℝ, Fin k → ℝ) ∞ Z ∧
              _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) ∞
                (Subtype.val : Z → H)) ∧
          (Z ⊆ ⋃ q ∈ T, ball q (ε * r q)) ∧
          ∃ g : ∀ x : S, P x → (P x)ᗮ, ∀ x : S,
            ContDiffOn ℝ ∞ (g x) (ball 0 (4 * b * r x)) ∧
            (∀ t ∈ ball (0 : P x) (4 * b * r x), ‖g x t‖ ≤ r x / 4 ∧
              (x : H) + orthogonalCoordinateSum (P x) (t, g x t) ∈ Z) ∧
            (∀ t ∈ ball (0 : P x) (4 * b * r x),
              ∀ n ∈ closedBall (0 : (P x)ᗮ) (r x),
              η ((x : H) + orthogonalCoordinateSum (P x) (t, n)) = 0 ↔ n = g x t) ∧
            (∀ m t, t ∈ ball (0 : P x) (4 * b * r x) → ∀ j, j ≤ m →
              ‖iteratedFDeriv ℝ j (g x) t‖ ≤ F m * δ * r x * ((r x)⁻¹) ^ j) ∧
            Z ∩ ball (x : H) (3 * b * r x) =
              {z : H | ∃ t ∈ ball (0 : P x) (4 * b * r x),
                z = (x : H) + orthogonalCoordinateSum (P x) (t, g x t)} ∩
                  ball (x : H) (3 * b * r x) := by
  classical
  obtain ⟨_C, E, δman, hδman, hproduce⟩ :=
    exists_uniform_large_cloud_zero_set_manifold.{u} k b B hb hB
  obtain ⟨δgraph, hδgraph, F, hF, hgraphs⟩ :=
    exists_uniform_buffered_section_graph_family.{u, u}
      (fun m => (E m : ℝ)) (fun m => (E m).coe_nonneg)
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  have hden : 0 < 2 * B * ((E 0 : ℝ) + 2) := by positivity
  let δprox : ℝ := ε / (2 * B * ((E 0 : ℝ) + 2))
  have hδprox : 0 < δprox := div_pos hε hden
  refine ⟨F, hF, min δman (min δgraph δprox),
    lt_min hδman (lt_min hδgraph hδprox), ?_⟩
  intro H _ _ _ S T hST hS r P hdim rmin R δ hrmin hlower hupper hδ hδsmall
    hinterior hscale hcloud
  obtain ⟨I, hI, hIS, hdisj, hcover, htube, hrest⟩ :=
    hproduce H S T hST hS r P hdim rmin R δ hrmin hlower hupper hδ
      (hδsmall.trans (min_le_left _ _)) hinterior
      (fun x hx y hy hxy => hscale x (hST hx) y (hST hy) hxy) hcloud
  rcases hrest with ⟨_hwc, _hws, hsc, _hss, _hQ, _hQr, hη, hec, hes, hman⟩
  refine ⟨I, hI, hIS, hdisj, hcover, htube, hman, ?_⟩
  let w : H → H → ℝ := fun i y => ballCutoff i (40*b*r i) (2*(40*b*r i)) y /
    (∑ a ∈ hI.toFinset, ballCutoff a (40*b*r a) (2*(40*b*r a)) y)
  let Q : H → Submodule ℝ H := fun y => ⨆ μ ∈ ball (1 : ℝ) (1/2), Module.End.eigenspace
    (∑ i ∈ hI.toFinset, w i y • (P i)ᗮ.starProjection).toLinearMap μ
  let η : H → H := fun y => (Q y).starProjection (y-∑ i ∈ hI.toFinset, w i y • i)
  let U : Set H := ⋃ i ∈ I, ball i (20*b*r i)
  have hr (x : S) : 0 < r x := hrmin.trans_le (hlower x x.property)
  have hbpos : 0 < b := zero_lt_one.trans_le hb
  have hU30 : U ⊆ ⋃ i ∈ I, ball i (30*b*r i) := by
    intro z hz
    obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp hz
    refine mem_iUnion₂.mpr ⟨i, hi, ?_⟩
    have hri : 0 < r i := hrmin.trans_le (hlower i (hIS hi))
    have hh : dist z i < 20*b*r i := hzi
    change dist z i < 30*b*r i
    nlinarith [mul_pos hbpos hri]
  have hcore (x : S) : ball (x : H) (8*b*r x) ⊆ U := by
    intro z hz
    exact htube (mem_iUnion₂.mpr ⟨x, x.property, hz⟩)
  have hηcore (x : S) : ContDiffOn ℝ ∞ η (ball (x : H) (8*b*r x)) :=
    hη.mono ((hcore x).trans hU30)
  have hcoef : 24*(B+1) ≤ (80*B+31)*b+2 := by
    have hB0 : 0 ≤ B := le_trans (by norm_num) hB
    have hh := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 80*B+31)
    nlinarith
  have hgapnum : 24*(B+1)*δ < 1 := by
    calc
      24*(B+1)*δ ≤ ((80*B+31)*b+2)*δ :=
        mul_le_mul_of_nonneg_right hcoef hδ.le
      _ < 1 := by simpa only [mul_comm] using hinterior
  have hgap (x : S) (z : H) (hz : z ∈ ball (x : H) (8*b*r x)) :
      ‖(Q z).starProjection - (P x)ᗮ.starProjection‖ < 1 :=
    (((hsc x x.property).2.1 z hz).2).trans_lt hgapnum
  constructor
  · have hδbound : δ ≤ δprox :=
      hδsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
    have haccuracy : B * ((E 0 : ℝ) + 2) * δ < ε := by
      have hh : δ * (2 * B * ((E 0 : ℝ) + 2)) ≤ ε :=
        (le_div_iff₀ hden).mp hδbound
      nlinarith
    have hcoef20 : 20 * b ≤ (80 * B + 31) * b + 2 := by
      have hh := mul_le_mul_of_nonneg_right hB hbpos.le
      nlinarith
    have hinside : (20 * b) * δ < 1 := by
      calc
        _ ≤ ((80 * B + 31) * b + 2) * δ :=
          mul_le_mul_of_nonneg_right hcoef20 hδ.le
        _ < 1 := by simpa only [mul_comm] using hinterior
    have hδlt : δ < 1 := by
      have hh := mul_le_mul_of_nonneg_right hb hδ.le
      nlinarith
    have hreach : 20 * b + 2 * δ ≤ 128 * b := by nlinarith
    have herror (i : I) (z : H) (hz : z ∈ ball (i : H) ((20 * b) * r i)) :
        ‖η z - (P i)ᗮ.starProjection (z - i)‖ ≤ (E 0 : ℝ) * δ * r i := by
      have hri : 0 < r i := hrmin.trans_le (hlower i (hIS i.property))
      have hz30 : z ∈ ball (i : H) (30 * b * r i) := by
        have hh : dist z i < 20 * b * r i := hz
        change dist z i < 30 * b * r i
        nlinarith [mul_pos hbpos hri]
      simpa only [norm_iteratedFDeriv_zero, pow_zero, mul_one] using
        hes 0 i i.property 0 (le_refl 0) z hz30
    have hprox := zero_set_subset_variable_ball_union_of_scale_control
      I T (hIS.trans hST) r (fun i : I => P i) η
      (20 * b) (128 * b) (E 0 : ℝ) δ B ε (by positivity) (E 0).coe_nonneg
      hδ hBpos (fun i => hrmin.trans_le (hlower i (hIS i.property)))
      hinside hreach haccuracy (fun i => hcloud i (hIS i.property)) herror
      (fun x hx y hy hxy => (hscale x hx y hy hxy).1)
    intro z hz
    apply hprox
    refine ⟨?_, hz.2⟩
    obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp hz.1
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hzi⟩
  · exact hgraphs H S (fun x : S => P x) b (fun x : S => r x)
      (fun x : S => (x : H)) U η Q δ hb hr hδ
      (hδsmall.trans ((min_le_right _ _).trans (min_le_left _ _))) hcore hηcore
      (fun _ z _ => (Q z).starProjection_apply_mem _) hgap
      (fun x m j hj z hz => hec m x x.property j hj z hz)

end GC.MetricGeometry
