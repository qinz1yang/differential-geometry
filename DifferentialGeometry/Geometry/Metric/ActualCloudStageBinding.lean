import DifferentialGeometry.Geometry.Metric.ActualCloudContributorLocality
import DifferentialGeometry.Geometry.Metric.ActualCloudStagePreservation
import DifferentialGeometry.Geometry.Metric.MarkerCloudApplications

/-! CFS29 bound to the actual large-cloud smoothing (CFS11–CFS14 via
`exists_large_cloud_nearest_map_affine_marker_locality`, ratio constant `B = 5/3`).

* its large-scale control (MCb) at its OWN buffer `128 ε⁻¹` is discharged by CFS07/CFS26
  (`markerChosenRadius_local_scale_control`, `128 ε⁻¹ Σ ≤ 1/5` from `Σ ≤ ε/640`);
* its contributor hypothesis is discharged by CFS28 for the pruned (PP) planes, so the actual nearest map has zero
  small blocks on every core ball (`actualCloud_nearest_map_small_marker_locality`);
* with `P_j = π_{Q_j} ∘ p`, CFS29's stage kernel gives the preservation of the small originally zero markers by the
  actual blended adjustment (`actualCloud_stage_preserves_small_markers`).
The cloud approximation by the pruned planes, their dimension and the finite radius bounds remain explicit
hypotheses (the FC23/FC27 rough producers with CFS27's pruning). -/

set_option autoImplicit false
noncomputable section
open Set Metric DifferentialGeometry.Analysis
open scoped BigOperators

namespace GC.MetricGeometry

universe u v w x

/-- The actual CFS14 nearest map (literal weights, spectral projector and section) keeps every small block zero on
each core ball, for the pruned (PP) planes and radii `Σ ρ(select ·)`. -/
theorem actualCloud_nearest_map_small_marker_locality
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) (hεsmall : ε ≤ 1 / 10) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
        (M : Type v) (A : Type w) (E : Type x) [NormedAddCommGroup E] [NormedSpace ℝ E]
        (F' : M → H) (ρ : M → ℝ) (V : A → Submodule ℝ H) (marker : A → H → ℝ) (Rm : A → ℝ),
        (∀ i, 0 < Rm i) → (∀ i, LipschitzWith 1 (marker i)) →
        (∀ q, ∃ i, marker i (F' q) = Rm i) → (∀ i q, 0 ≤ marker i (F' q)) →
        (∀ i q, 0 < marker i (F' q) → 3 * Rm i / 4 ≤ ρ q ∧ ρ q ≤ 5 * Rm i / 4) →
        (∀ i q, marker i (F' q) = 0 → (V i).starProjection (F' q) = 0) →
        ∀ (S T : Set H), S ⊆ T → TotallyBounded S →
        ∀ (select model : H → M) (ref : H → A) (Tm : H → E →L[ℝ] H) (σ : ℝ),
        (∀ y ∈ T, F' (select y) = y) → (∀ y ∈ S, F' (model y) = y) →
        (∀ y ∈ S, marker (ref y) y = Rm (ref y)) → 0 < σ → σ ≤ ε / 640 →
        (∀ y ∈ S, Module.finrank ℝ (LinearMap.range
          (((actualCloudPrunedProjection V Rm (ref y)).comp (Tm y) : E →L[ℝ] H) : E →ₗ[ℝ] H)) = k) →
        ∀ rmin Rmax δ : ℝ, 0 < rmin →
        (∀ y ∈ S, rmin ≤ σ * ρ (select y)) → (∀ y ∈ S, σ * ρ (select y) ≤ Rmax) →
        0 < δ → δ ≤ δ₀ → δ * ((80 * (5 / 3 : ℝ) + 31) * ε⁻¹ + 2) < 1 →
        (∀ y ∈ S, hausdorffEDist (T ∩ ball y (σ * ρ (select y) / δ))
          ((AffineSubspace.mk' y (LinearMap.range
            (((actualCloudPrunedProjection V Rm (ref y)).comp (Tm y) : E →L[ℝ] H) :
              E →ₗ[ℝ] H)) : Set H) ∩ ball y (σ * ρ (select y) / δ)) ≤
            ENNReal.ofReal (δ * (σ * ρ (select y)))) →
        ∃ (I : Set H) (hI : I.Finite), I ⊆ S ∧
          let r : H → ℝ := fun y => σ * ρ (select y)
          let P : H → Submodule ℝ H := fun y => LinearMap.range
            (((actualCloudPrunedProjection V Rm (ref y)).comp (Tm y) : E →L[ℝ] H) : E →ₗ[ℝ] H)
          let w : H → H → ℝ := fun c y =>
              ballCutoff c (40 * ε⁻¹ * r c) (2 * (40 * ε⁻¹ * r c)) y /
              (∑ a ∈ hI.toFinset, ballCutoff a (40 * ε⁻¹ * r a) (2 * (40 * ε⁻¹ * r a)) y)
          let Q : H → Submodule ℝ H := fun y => ⨆ μ ∈ ball (1 : ℝ) (1 / 2),
              Module.End.eigenspace
                (∑ c ∈ hI.toFinset, w c y • (P c)ᗮ.starProjection).toLinearMap μ
          let η : H → H := fun y => (Q y).starProjection (y - ∑ c ∈ hI.toFinset, w c y • c)
          ∃ pn : H → H, ∀ x ∈ S, ∀ z ∈ ball x (r x),
            η (pn z) = 0 ∧ ‖pn z - (x + (P x).starProjection (z - x))‖ ≤ ε * r x ∧
            ∀ q, F' q = x → ∀ i, Rm i < ρ q / 16 → (V i).starProjection (pn z) = 0 := by
  obtain ⟨δ₀, hδ₀, hprod⟩ :=
    exists_large_cloud_nearest_map_affine_marker_locality.{u} k (5 / 3) ε (by norm_num) hε hεsmall
  refine ⟨δ₀, hδ₀, ?_⟩
  intro H _ _ _ M A E _ _ F' ρ V marker Rm hR hmarker hfull hnonneg hsupport hblock S T hST hS
    select model ref Tm σ hselT hmodel hfullref hσ hσε hdim rmin Rmax δ hrmin hlower hupper hδ
    hδle hinterior hcloud
  have hb : 1 ≤ ε⁻¹ := (one_le_inv₀ hε).mpr (by linarith)
  have hσb : 640 * ε⁻¹ * σ ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hσε (by positivity : (0 : ℝ) ≤ 640 * ε⁻¹)
    have heq : 640 * ε⁻¹ * (ε / 640) = 1 := by field_simp
    linarith
  have hscale := markerChosenRadius_local_scale_control F' ρ marker Rm hR hmarker hfull hsupport T
    select hselT (fun y => σ * ρ (select y)) (σ := σ) (L := 128 * ε⁻¹) (fun _ _ => rfl) hσ.le
    (by positivity) (by nlinarith)
  obtain ⟨I, hI, hIS, hrest⟩ := hprod H S T hST hS (fun y => σ * ρ (select y))
    (fun y => LinearMap.range
      (((actualCloudPrunedProjection V Rm (ref y)).comp (Tm y) : E →L[ℝ] H) : E →ₗ[ℝ] H))
    hdim rmin Rmax δ hrmin hlower hupper hδ hδle hinterior hscale hcloud
  refine ⟨I, hI, hIS, ?_⟩
  intro r P w Q η
  obtain ⟨pn, hpn⟩ := hrest
  refine ⟨pn, fun y hy z hz => ⟨(hpn y hy z hz).1, (hpn y hy z hz).2.1, ?_⟩⟩
  intro q hq i hi
  refine (hpn y hy z hz).2.2 (V i) 0 fun c hc hmeet => ?_
  exact actualCloud_contributor_marker_locality F' ρ V marker Rm hR hmarker hfull hnonneg
    hsupport hblock hb hσ.le hσb select model ref Tm q y hq (hselT y (hST hy)) c
    (hselT c (hST (hIS hc))) (hmodel c (hIS hc)) (hfullref c (hIS hc)) hmeet i hi

/-- CFS29 for the actual stage: with the stage projection `π_{Q_j} ∘ p` of the actual CFS14 nearest map `p`, every
blended adjustment whose cutoff localizes the original point to the stage core and whose preceding error is at
most `3Σ/10 · ρ` preserves the zero small markers. -/
theorem actualCloud_stage_preserves_small_markers
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) (hεsmall : ε ≤ 1 / 10) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
        (M : Type v) (A : Type w) (E : Type x) [NormedAddCommGroup E] [NormedSpace ℝ E]
        (Qj : Submodule ℝ H) (F : M → H) (ρ : M → ℝ) (V : A → Submodule ℝ H)
        (marker : A → H → ℝ) (Rm : A → ℝ),
        (∀ i, 0 < Rm i) → (∀ i, LipschitzWith 1 (marker i)) →
        (∀ q, ∃ i, marker i (Qj.starProjection (F q)) = Rm i) →
        (∀ i q, 0 ≤ marker i (Qj.starProjection (F q))) →
        (∀ i q, 0 < marker i (Qj.starProjection (F q)) →
          3 * Rm i / 4 ≤ ρ q ∧ ρ q ≤ 5 * Rm i / 4) →
        (∀ i q, marker i (Qj.starProjection (F q)) = 0 →
          (V i).starProjection (Qj.starProjection (F q)) = 0) →
        ∀ (S T : Set H), S ⊆ T → TotallyBounded S →
        ∀ (select model : H → M) (ref : H → A) (Tm : H → E →L[ℝ] H) (σ : ℝ),
        (∀ y ∈ T, Qj.starProjection (F (select y)) = y) →
        (∀ y ∈ S, Qj.starProjection (F (model y)) = y) →
        (∀ y ∈ S, marker (ref y) y = Rm (ref y)) → 0 < σ → σ ≤ ε / 640 →
        (∀ y ∈ S, Module.finrank ℝ (LinearMap.range
          (((actualCloudPrunedProjection V Rm (ref y)).comp (Tm y) : E →L[ℝ] H) : E →ₗ[ℝ] H)) = k) →
        ∀ rmin Rmax δ : ℝ, 0 < rmin →
        (∀ y ∈ S, rmin ≤ σ * ρ (select y)) → (∀ y ∈ S, σ * ρ (select y) ≤ Rmax) →
        0 < δ → δ ≤ δ₀ → δ * ((80 * (5 / 3 : ℝ) + 31) * ε⁻¹ + 2) < 1 →
        (∀ y ∈ S, hausdorffEDist (T ∩ ball y (σ * ρ (select y) / δ))
          ((AffineSubspace.mk' y (LinearMap.range
            (((actualCloudPrunedProjection V Rm (ref y)).comp (Tm y) : E →L[ℝ] H) :
              E →ₗ[ℝ] H)) : Set H) ∩ ball y (σ * ρ (select y) / δ)) ≤
            ENNReal.ofReal (δ * (σ * ρ (select y)))) →
        ∃ (I : Set H) (hI : I.Finite), I ⊆ S ∧
          let r : H → ℝ := fun y => σ * ρ (select y)
          let P : H → Submodule ℝ H := fun y => LinearMap.range
            (((actualCloudPrunedProjection V Rm (ref y)).comp (Tm y) : E →L[ℝ] H) : E →ₗ[ℝ] H)
          let w : H → H → ℝ := fun c y =>
              ballCutoff c (40 * ε⁻¹ * r c) (2 * (40 * ε⁻¹ * r c)) y /
              (∑ a ∈ hI.toFinset, ballCutoff a (40 * ε⁻¹ * r a) (2 * (40 * ε⁻¹ * r a)) y)
          let Q : H → Submodule ℝ H := fun y => ⨆ μ ∈ ball (1 : ℝ) (1 / 2),
              Module.End.eigenspace
                (∑ c ∈ hI.toFinset, w c y • (P c)ᗮ.starProjection).toLinearMap μ
          let η : H → H := fun y => (Q y).starProjection (y - ∑ c ∈ hI.toFinset, w c y • c)
          ∃ pn : H → H, (∀ x ∈ S, ∀ z ∈ ball x (r x),
            η (pn z) = 0 ∧ ‖pn z - (x + (P x).starProjection (z - x))‖ ≤ ε * r x) ∧
          ∀ (ψ : H → ℝ) (f : M → H) (e : ℝ), e ≤ 3 * σ / 10 →
            (∀ q, ψ (f q) ≠ 0 → Qj.starProjection (F q) ∈ S) →
            (∀ q, ψ (f q) ≠ 0 → ‖f q - F q‖ ≤ e * ρ q) →
            (∀ i, V i ≤ Qj ∨ V i ≤ Qjᗮ) →
            (∀ q i, Rm i < ρ q / 16 → (V i).starProjection (f q) = 0) →
            ∀ q i, Rm i < ρ q / 16 →
              (V i).starProjection
                (adjustmentMap Qj (fun z => Qj.starProjection (pn z)) ψ (f q)) = 0 := by
  obtain ⟨δ₀, hδ₀, hnear⟩ := actualCloud_nearest_map_small_marker_locality.{u, v, w, x} k ε hε hεsmall
  refine ⟨δ₀, hδ₀, ?_⟩
  intro H _ _ _ M A E _ _ Qj F ρ V marker Rm hR hmarker hfull hnonneg hsupport hblock S T hST hS
    select model ref Tm σ hselT hmodel hfullref hσ hσε hdim rmin Rmax δ hrmin hlower hupper hδ
    hδle hinterior hcloud
  obtain ⟨I, hI, hIS, hrest⟩ := hnear H M A E (fun q => Qj.starProjection (F q)) ρ V marker Rm hR
    hmarker hfull hnonneg hsupport hblock S T hST hS select model ref Tm σ hselT hmodel hfullref
    hσ hσε hdim rmin Rmax δ hrmin hlower hupper hδ hδle hinterior hcloud
  refine ⟨I, hI, hIS, ?_⟩
  intro r P w Q η
  obtain ⟨pn, hpn⟩ := hrest
  refine ⟨pn, fun y hy z hz => ⟨(hpn y hy z hz).1, (hpn y hy z hz).2.1⟩, ?_⟩
  intro ψ f e he hloc herror hretained hinput
  refine actualCloud_stage_small_marker_preservation Qj (fun z => Qj.starProjection (pn z))
    (fun z => Qj.starProjection_apply_mem (pn z)) ψ F f ρ V marker Rm hR hsupport
    (fun q _ => hfull q) S select (fun y hy => hselT y (hST hy)) hσ he hloc herror ?_ hretained
    hinput
  intro y hy z hz q hq i hi
  rcases hretained i with hVQ | hVQ
  · have hproj : (V i).starProjection (Qj.starProjection (pn z)) = (V i).starProjection (pn z) := by
      have := congrArg (fun L : H →L[ℝ] H => L (pn z))
        (Submodule.starProjection_comp_starProjection_of_le hVQ)
      simpa using this
    rw [hproj]
    exact (hpn y hy z hz).2.2 q hq i hi
  · have hQV : Qj ≤ (V i)ᗮ :=
      (Submodule.le_orthogonal_orthogonal Qj).trans (Submodule.orthogonal_le hVQ)
    exact ((V i).starProjection_apply_eq_zero_iff).mpr (hQV (Qj.starProjection_apply_mem _))

end GC.MetricGeometry
