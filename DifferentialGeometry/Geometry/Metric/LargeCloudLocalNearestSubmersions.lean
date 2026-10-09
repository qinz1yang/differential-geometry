import DifferentialGeometry.Geometry.Metric.LargeCloudBufferedGraphCoverage
import DifferentialGeometry.Topology.Manifold.BufferedNormalGraphSubmersion

set_option autoImplicit false
noncomputable section
open Set Metric DifferentialGeometry.Analysis
open scoped BigOperators NNReal ContDiff Manifold
namespace GC.MetricGeometry
universe u

theorem exists_uniform_large_cloud_buffered_graph_manifold_with_local_nearest_submersions
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
              ∀ x : S,
                let V : TopologicalSpace.Opens H := ⟨ball (x : H) (r x), isOpen_ball⟩
                ∃ p : C^∞⟮𝓘(ℝ, H), V; 𝓘(ℝ, Fin k → ℝ), Z⟯,
                  _root_.Manifold.IsSubmersion 𝓘(ℝ, H) 𝓘(ℝ, Fin k → ℝ) ∞ p ∧
                  ∀ z : V, IsMinOn (fun y => dist (z : H) y) Z (p z : H) ∧
                    (∀ y ∈ Z, IsMinOn (fun w => dist (z : H) w) Z y → y = (p z : H)) ∧
                    ‖(p z : H) - ((x : H) + (P x).starProjection ((z : H) - x))‖ ≤ ε * r x ∧
                    (let D : H →L[ℝ] H :=
                      mfderiv 𝓘(ℝ, H) 𝓘(ℝ, H) (fun y : V => (p y : H)) z
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
  have hb : 1 ≤ ε⁻¹ := le_of_lt ((one_lt_inv₀ hε).mpr (by linarith))
  let a : ℝ := min (1 / 100) (ε / 8)
  have ha : 0 < a := lt_min (by norm_num) (by positivity)
  have ha100 : a ≤ 1 / 100 := min_le_left _ _
  have haε : a ≤ ε / 8 := min_le_right _ _
  obtain ⟨F, hF, δbase, hδbase, hproduce⟩ :=
    exists_uniform_large_cloud_buffered_graph_manifold_with_coverage.{u} k B ε hB hε hεsmall
  have hden : 0 < F 2 + 1 := by have h2 := hF 2; positivity
  refine ⟨F, hF, min δbase (a / (F 2 + 1)),
    lt_min hδbase (div_pos ha hden), ?_⟩
  intro H _ _ _ S T hST hS r P hdim rmin R δ hrmin hlower hupper hδ hδsmall
    hinterior hscale hcloud
  have hδgraph : δ ≤ a / (F 2 + 1) := hδsmall.trans (min_le_right _ _)
  have hsmalljet : F 2 * δ ≤ a := by
    have hh : δ * (F 2 + 1) ≤ a := (le_div_iff₀ hden).mp hδgraph
    nlinarith
  obtain ⟨I, hI, hIS, hdisj, hcover, htube, hman, hproperCore, hprox, hcoverage, g, hg⟩ :=
    hproduce H S T hST hS r P hdim rmin R δ hrmin hlower hupper hδ
      (hδsmall.trans (min_le_left _ _)) hinterior hscale hcloud
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
  rcases hman with ⟨hproper, cs, hcs, hemb⟩
  let : ChartedSpace (Fin k → ℝ) Z := cs
  let : IsManifold 𝓘(ℝ, Fin k → ℝ) ∞ Z := hcs
  refine ⟨I, hI, hIS, hdisj, hcover, htube,
    ⟨hproper, cs, hcs, hemb, ?_⟩, hproperCore, hprox, hcoverage, g, hg⟩
  intro x
  have hr : 0 < r x := hrmin.trans_le (hlower x x.property)
  have hbr : r x ≤ ε⁻¹ * r x := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hb hr.le
  have htbig (t : P x) (ht : t ∈ ball (0 : P x) (4 * r x)) :
      t ∈ ball (0 : P x) (4 * ε⁻¹ * r x) := by
    rw [mem_ball, dist_zero_right] at ht ⊢
    nlinarith
  have hjet (j : ℕ) (hj : j ≤ 2) (t : P x)
      (ht : t ∈ ball (0 : P x) (4 * r x)) :
      ‖iteratedFDeriv ℝ j (g x) t‖ ≤ a * r x * ((r x)⁻¹) ^ j := by
    have hh := (hg x).2.2.2.1 2 t (htbig t ht) j hj
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hsmalljet hr.le) (pow_nonneg (inv_nonneg.mpr hr.le) j))
  have hsmooth : ContDiffOn ℝ ∞ (g x) (ball (0 : P x) (4 * r x)) :=
    (hg x).1.mono (fun t ht => htbig t ht)
  have hvalue (t : P x) (ht : t ∈ ball (0 : P x) (4 * r x)) : ‖g x t‖ ≤ a * r x := by
    simpa only [norm_iteratedFDeriv_zero, pow_zero, mul_one] using hjet 0 (by omega) t ht
  have hfirst (t : P x) (ht : t ∈ ball (0 : P x) (4 * r x)) : ‖fderiv ℝ (g x) t‖ ≤ a := by
    simpa only [norm_iteratedFDeriv_one, pow_one, mul_assoc,
      mul_inv_cancel₀ hr.ne', mul_one] using hjet 1 (by omega) t ht
  have hsecond (t : P x) (ht : t ∈ ball (0 : P x) (4 * r x)) :
      ‖fderiv ℝ (fderiv ℝ (g x)) t‖ ≤ a / r x := by
    have hn : ‖fderiv ℝ (fderiv ℝ (g x)) t‖ = ‖iteratedFDeriv ℝ 2 (g x) t‖ := by
      rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one]
    rw [hn]
    calc
      _ ≤ a * r x * ((r x)⁻¹) ^ 2 := hjet 2 (by omega) t ht
      _ = a / r x := by field_simp [hr.ne']
  have hgraph (t : P x) (ht : t ∈ ball (0 : P x) (4 * r x)) :
      (x : H) + orthogonalCoordinateSum (P x) (t, g x t) ∈ Z :=
    ((hg x).2.1 t (htbig t ht)).2
  have hsheet (y : H) (hy : y ∈ Z ∩ ball (x : H) (3 * r x)) :
      ∃ t ∈ ball (0 : P x) (4 * r x),
        y = (x : H) + orthogonalCoordinateSum (P x) (t, g x t) := by
    have hybig : y ∈ ball (x : H) (3 * ε⁻¹ * r x) := by
      have hh : dist y x < 3 * r x := hy.2
      change dist y x < 3 * ε⁻¹ * r x
      nlinarith
    obtain ⟨⟨t, _ht, heq⟩, _hy⟩ :=
      (Set.ext_iff.mp (hg x).2.2.2.2 y).mp ⟨hy.1, hybig⟩
    have htproj : (P x).orthogonalProjectionOnto (y - (x : H)) = t := by
      have hid : y - (x : H) = orthogonalCoordinateSum (P x) (t, g x t) := by
        rw [heq]
        abel
      rw [hid]
      change (P x).orthogonalProjectionOnto ((t : H) + (g x t : H)) = t
      rw [map_add, (P x).orthogonalProjectionOnto_mem_subspace_eq_self,
        Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal (g x t).property, add_zero]
    have htbound : ‖t‖ ≤ ‖y - (x : H)‖ := by
      rw [← htproj]
      exact (P x).norm_orthogonalProjectionOnto_apply_le (y - (x : H))
    have htcore : t ∈ ball (0 : P x) (4 * r x) := by
      rw [mem_ball, dist_zero_right]
      have hh : ‖y - (x : H)‖ < 3 * r x := by
        simpa only [mem_ball, dist_eq_norm] using hy.2
      nlinarith
    exact ⟨t, htcore, heq⟩
  have hdim' : Module.finrank ℝ (P x) = Module.finrank ℝ (Fin k → ℝ) := by
    simpa only [Module.finrank_fin_fun] using hdim x x.property
  obtain ⟨p, hp, hnearest⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_smooth_unique_nearest_submersion_buffered_normal_graph_with_bounds
      Z hemb (P x) hdim' x (g x) (r x) a hr ha100 hsmooth hvalue hfirst hsecond hgraph hsheet
  refine ⟨p, hp, ?_⟩
  intro z
  rcases hnearest z with ⟨hmin, huniq, hv, hd⟩
  refine ⟨hmin, huniq, hv.trans ?_, hd.trans ?_⟩
  · exact mul_le_mul_of_nonneg_right (by linarith : 3 * a ≤ ε) hr.le
  · linarith

end GC.MetricGeometry
