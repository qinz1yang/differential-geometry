import DifferentialGeometry.Geometry.Metric.LargeCloudBufferedGraphProximity
import DifferentialGeometry.Analysis.InnerProductSpace.NormalGraphRescaledCoverage


set_option autoImplicit false
noncomputable section
open Set Metric DifferentialGeometry.Analysis
open scoped BigOperators NNReal ContDiff Manifold
namespace GC.MetricGeometry
universe u

private theorem isProperMap_relativeSubsetInclusion
    {X : Type*} [TopologicalSpace X] (U W V : Set X)
    (hWU : W ⊆ U) (hVU : V ⊆ U)
    (hproper : IsProperMap (fun w : W => (⟨w.1, hWU w.2⟩ : U))) :
    IsProperMap (Subtype.val : {v : V | (v : X) ∈ W} → V) := by
  let f : V → U := fun v => ⟨v.1, hVU v.2⟩
  have hf : Continuous f := continuous_subtype_val.subtype_mk (fun v => hVU v.2)
  have hset : f ⁻¹' Set.range (fun w : W => (⟨w.1, hWU w.2⟩ : U)) =
      {v : V | (v : X) ∈ W} := by
    ext v
    constructor
    · rintro ⟨w, hw⟩
      have hval : (w : X) = (v : X) := congrArg Subtype.val hw
      change (v : X) ∈ W
      rw [← hval]
      exact w.2
    · intro hv
      exact ⟨⟨(v : X), hv⟩, rfl⟩
  have hclosed := hproper.isClosed_range.preimage hf
  rw [hset] at hclosed
  exact hclosed.isProperMap_subtypeVal

theorem exists_uniform_large_cloud_buffered_graph_manifold_with_coverage
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
                (Subtype.val : Z → H)) ∧
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
  have hb : 1 ≤ ε⁻¹ := le_of_lt ((one_lt_inv₀ hε).mpr (by linarith))
  obtain ⟨F, hF, δbase, hδbase, hproduce⟩ :=
    exists_uniform_large_cloud_buffered_graph_manifold_with_proximity.{u}
      k ε⁻¹ B ε hb hB hε
  let δheight : ℝ := ε / (8 * (F 0 + 1))
  have hden : 0 < 8 * (F 0 + 1) := by have h0 := hF 0; positivity
  have hδheight : 0 < δheight := div_pos hε hden
  refine ⟨F, hF, min δbase (min (ε / 16) δheight),
    lt_min hδbase (lt_min (by positivity) hδheight), ?_⟩
  intro H _ _ _ S T hST hS r P hdim rmin R δ hrmin hlower hupper hδ hδsmall
    hinterior hscale hcloud
  obtain ⟨I, hI, hIS, hdisj, hcover, htube, hrest⟩ :=
    hproduce H S T hST hS r P hdim rmin R δ hrmin hlower hupper hδ
      (hδsmall.trans (min_le_left _ _)) hinterior hscale hcloud
  rcases hrest with ⟨hman, hprox, g, hg⟩
  let w : H → H → ℝ := fun i y =>
    ballCutoff i (40 * ε⁻¹ * r i) (2 * (40 * ε⁻¹ * r i)) y /
      (∑ a ∈ hI.toFinset,
        ballCutoff a (40 * ε⁻¹ * r a) (2 * (40 * ε⁻¹ * r a)) y)
  let Q : H → Submodule ℝ H := fun y => ⨆ μ ∈ ball (1 : ℝ) (1 / 2),
    Module.End.eigenspace
      (∑ i ∈ hI.toFinset, w i y • (P i)ᗮ.starProjection).toLinearMap μ
  let η : H → H := fun y => (Q y).starProjection
    (y - ∑ i ∈ hI.toFinset, w i y • i)
  let U : Set H := ⋃ i ∈ I, ball i (20 * ε⁻¹ * r i)
  let Z : Set H := {z | z ∈ U ∧ η z = 0}
  let N : Set H := ⋃ x ∈ S, ball x (r x)
  have hNU : N ⊆ U := by
    intro z hz
    obtain ⟨x, hx, hzx⟩ := mem_iUnion₂.mp hz
    apply htube
    refine mem_iUnion₂.mpr ⟨x, hx, ?_⟩
    have hr : 0 < r x := hrmin.trans_le (hlower x hx)
    have hle : r x ≤ ε⁻¹ * r x := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hb hr.le
    have hh : dist z x < r x := hzx
    change dist z x < 8 * ε⁻¹ * r x
    nlinarith
  have hproperCore : IsProperMap (Subtype.val : {z : N | (z : H) ∈ Z} → N) :=
    isProperMap_relativeSubsetInclusion U Z N (fun _ hz => hz.1) hNU hman.1
  refine ⟨I, hI, hIS, hdisj, hcover, htube, hman, hproperCore, hprox, ?_, g, hg⟩
  have hδε : δ ≤ ε / 16 :=
    hδsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδbound : δ ≤ δheight :=
    hδsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hheightbudget : F 0 * δ ≤ ε / 8 := by
    have hh : δ * (8 * (F 0 + 1)) ≤ ε := (le_div_iff₀ hden).mp hδbound
    nlinarith
  intro x hx
  let xS : S := ⟨x, hx⟩
  have hr : 0 < r x := hrmin.trans_le (hlower x hx)
  have hbr : 0 < ε⁻¹ * r x := mul_pos (inv_pos.mpr hε) hr
  have htbig (t : P x) (ht : ‖t‖ ≤ r x * ε⁻¹) :
      t ∈ ball (0 : P x) (4 * ε⁻¹ * r x) := by
    rw [mem_ball, dist_zero_right]
    nlinarith
  have hgraph (t : P x) (ht : ‖t‖ ≤ r x * ε⁻¹) :
      x + orthogonalCoordinateSum (P x) (t, g xS t) ∈ Z :=
    ((hg xS).2.1 t (htbig t ht)).2
  have hheight (t : P x) (ht : ‖t‖ ≤ r x * ε⁻¹) :
      ‖g xS t‖ ≤ (ε / 8) * r x := by
    have hh := (hg xS).2.2.2.1 0 t (htbig t ht) 0 (le_refl 0)
    simp only [norm_iteratedFDeriv_zero, pow_zero, mul_one] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hheightbudget hr.le)
  have hsheet (z : H) (hz : z ∈ Z ∩ closedBall x (r x * ε⁻¹)) :
      ∃ t : P x, z = x + orthogonalCoordinateSum (P x) (t, g xS t) := by
    have hz3 : z ∈ ball x (3 * ε⁻¹ * r x) := by
      have hh : dist z x ≤ r x * ε⁻¹ := hz.2
      change dist z x < 3 * ε⁻¹ * r x
      nlinarith
    obtain ⟨⟨t, _ht, heq⟩, _hz⟩ :=
      (Set.ext_iff.mp (hg xS).2.2.2.2 z).mp ⟨hz.1, hz3⟩
    exact ⟨t, heq⟩
  apply hausdorffEDist_rescaled_normal_graph_truncations_le_of_accuracy_bounds
    (P x) x (g xS) T Z (r x) ε (ε / 8) δ hr hε hεsmall
    (by positivity) (le_refl _) hδ hδε hgraph hheight hsheet
  simpa only [div_eq_mul_inv] using hcloud x hx

end GC.MetricGeometry
