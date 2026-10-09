import DifferentialGeometry.Geometry.Fibration.ActualCloudPacketsApplications
import DifferentialGeometry.Geometry.Metric.AffineCloudBindings

/-!
# CFS08 on the three actual clouds of FC07 / FC27

Blueprint `master207B.tex`, CFS08 (`lem:fibration-cloud-macroscopic-plane-coherence`, B:2225):
"Suppose the actual (CS) tests hold and `x, y ∈ S` satisfy `B⁻¹ ≤ r(y)/r(x) ≤ B`,
`|x − y| ≤ L max{r(x), r(y)}`, `B, L ≥ 1` … In particular CFS07 supplies `B = 5/3`."
The (CS) tests (B:1772) are the row's own hypothesis; the radius ratio is discharged on the ACTUAL
clouds by `ActualCloudPackets` (CFS07 for any preimages / FC04's exact radius), with `B = 5/3`.

* `cfs08_of_scale_ratio_KA3`: CFS08 for any cloud whose radius satisfies (MC) with `B = 5/3` at the
  scale `L'` (kernel `normal_coherence_of_max_radius_cloud_tests`).
* `cfs08_first_cloud`: FC07's first cloud `S₁ = 𝓔⁰(A₁) ⊆ S̃₁ = 𝓔⁰(Ã₁)`, FC04's radius `r₁ = Σ x_ρ`,
  planes of dimension two.
* `cfs08_edge_cloud`, `cfs08_slim_cloud`: FC27's projected clouds `S_j = π_j𝓔⁰(A_j) ⊆ S̃_j`, FC26's
  selected radius `Σρ ∘ select` for ANY selection of preimages over `S̃_j`, planes of dimension one.
Conclusion (LC): `|P_x(y − x)| ≤ δ r(x)` and `‖P_x − P_y‖ ≤ 6(5/3 + 1)δ` (normal projectors).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

section Generic

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- **CFS08** for a cloud `S ⊆ S̃` whose radius satisfies (MC) with `B = 5/3` at the scale `L' ≥ 1`:
under the (CS) tests at every point of `S`, every pair `x, y ∈ S` with `|y − x| ≤ L' max(r x, r y)`
has (LC). -/
theorem cfs08_of_scale_ratio_KA3 (S St : Set H) (hSSt : S ⊆ St) (r : H → ℝ)
    (hr : ∀ x ∈ S, 0 < r x) (k : ℕ) (plane : H → Submodule ℝ H)
    [∀ x, FiniteDimensional ℝ (plane x)] (hdim : ∀ x ∈ S, Module.finrank ℝ (plane x) = k)
    {L' δc : ℝ} (hL' : 1 ≤ L')
    (hscale : ∀ x ∈ S, ∀ y ∈ S, dist y x ≤ L' * max (r x) (r y) →
      r x / (5 / 3) ≤ r y ∧ r y ≤ (5 / 3) * r x)
    (hδ : 0 < δc) (hδsmall : δc < min (1 / (4 * (5 / 3)))
      (min (1 / (2 * (L' * (5 / 3) + 3))) (1 / (4 * (5 / 3 + 1)))))
    (hcloud : ∀ x ∈ S, hausdorffEDist (St ∩ ball x (r x / δc))
      ((AffineSubspace.mk' x (plane x) : Set H) ∩ ball x (r x / δc)) ≤
        ENNReal.ofReal (δc * r x)) :
    ∀ x ∈ S, ∀ y ∈ S, dist y x ≤ L' * max (r x) (r y) →
      ‖(plane x)ᗮ.starProjection (y - x)‖ ≤ δc * r x ∧
        ‖(plane x)ᗮ.starProjection - (plane y)ᗮ.starProjection‖ ≤ 6 * (5 / 3 + 1) * δc := by
  intro x hx y hy hd
  obtain ⟨hlo, hhi⟩ := hscale x hx y hy hd
  exact normal_coherence_of_max_radius_cloud_tests (plane x) (plane y)
    (by rw [hdim x hx, hdim y hy]) St x y (hSSt hy) (r x) (r y) (5 / 3) L' δc (hr x hx)
    (by norm_num) hL' hlo hhi hd hδ hδsmall (hcloud x hx) (hcloud y hy)

end Generic

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

section Clouds

variable (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
  (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V)

theorem fc04Set_mono {θ θ' : ℝ} (h : θ ≤ θ') : fc04Set L Z θ ⊆ fc04Set L Z θ' := by
  rintro p ⟨j, hj, hη⟩
  exact ⟨j, hj, hη.trans h⟩

theorem fc27EdgeSet_mono (hΔ : 0 ≤ Δ) {θ θ' : ℝ} (h : θ ≤ θ') :
    fc27EdgeSet L θ ⊆ fc27EdgeSet L θ' := by
  rintro p ⟨j, hj, hη, ht⟩
  exact ⟨j, hj, hη.trans (mul_le_mul_of_nonneg_right h hΔ),
    ht.trans (mul_le_mul_of_nonneg_right h hΔ)⟩

theorem fc27SlimSet_mono (hΔ : 0 ≤ Δ) {θ θ' : ℝ} (h : θ ≤ θ') :
    fc27SlimSet L θ ⊆ fc27SlimSet L θ' := by
  rintro p ⟨j, hj, hη⟩
  refine ⟨j, hj, hη.trans ?_⟩
  have h5 : (0 : ℝ) ≤ 10 ^ 5 * Δ := by positivity
  nlinarith

/-- **CFS08 on FC07's first cloud**: `S₁ = 𝓔⁰(A₁) ⊆ S̃₁ = 𝓔⁰(Ã₁)` with FC04's exact radius
`r₁ = Σ x_ρ` (`0 < Σ`, `L'Σ ≤ 1/5`) and two-dimensional planes: (CS) at every point of `S₁` gives
(LC) for every pair at distance `≤ L' max(r₁)`. -/
theorem cfs08_first_cloud {L' sg δc : ℝ} (hL' : 1 ≤ L') (hsg : 0 < sg) (hLsg : L' * sg ≤ 1 / 5)
    (plane : BlockSpace (fun _ : CGPTag L Z => ℝ²) →
      Submodule ℝ (BlockSpace (fun _ : CGPTag L Z => ℝ²)))
    (hdim : ∀ x ∈ cgpGlobalMap L Z '' fc04Set L Z 7, Module.finrank ℝ (plane x) = 2)
    (hδ : 0 < δc) (hδsmall : δc < min (1 / (4 * (5 / 3)))
      (min (1 / (2 * (L' * (5 / 3) + 3))) (1 / (4 * (5 / 3 + 1)))))
    (hcloud : ∀ x ∈ cgpGlobalMap L Z '' fc04Set L Z 7,
      hausdorffEDist (cgpGlobalMap L Z '' fc04Set L Z 8 ∩
          ball x (scaleRadius (cgpScaleTag L Z) sg x / δc))
        ((AffineSubspace.mk' x (plane x) : Set (BlockSpace (fun _ : CGPTag L Z => ℝ²))) ∩
          ball x (scaleRadius (cgpScaleTag L Z) sg x / δc)) ≤
        ENNReal.ofReal (δc * scaleRadius (cgpScaleTag L Z) sg x)) :
    ∀ x ∈ cgpGlobalMap L Z '' fc04Set L Z 7, ∀ y ∈ cgpGlobalMap L Z '' fc04Set L Z 7,
      dist y x ≤ L' * max (scaleRadius (cgpScaleTag L Z) sg x)
        (scaleRadius (cgpScaleTag L Z) sg y) →
      ‖(plane x)ᗮ.starProjection (y - x)‖ ≤ δc * scaleRadius (cgpScaleTag L Z) sg x ∧
        ‖(plane x)ᗮ.starProjection - (plane y)ᗮ.starProjection‖ ≤ 6 * (5 / 3 + 1) * δc := by
  obtain ⟨hr, -, hmc⟩ := fc04_first_cloud_scale L Z hsg.le hLsg
  refine cfs08_of_scale_ratio_KA3 _ _ (image_mono (fc04Set_mono L Z (by norm_num))) _ ?_ 2
    plane hdim hL' ?_ hδ hδsmall hcloud
  · rintro _ ⟨p, -, rfl⟩
    rw [hr]
    exact mul_pos hsg (hρ p)
  · rintro x ⟨p, -, rfl⟩ y ⟨q, -, rfl⟩ hd
    exact hmc _ ⟨p, rfl⟩ _ ⟨q, rfl⟩ (by rw [max_comm]; exact hd)

/-- **CFS08 on FC27's edge cloud**: `S₂ = π₂𝓔⁰(A₂) ⊆ S̃₂ = π₂𝓔⁰(Ã₂)` with FC26's selected radius
`Σρ ∘ select` (ANY selection of preimages over `S̃₂`; `0 < Σ`, `L'Σ ≤ 1/5`) and one-dimensional
planes: (CS) at every point of `S₂` gives (LC) for every pair at distance `≤ L' max r`. -/
theorem cfs08_edge_cloud (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4)
    (select : BlockSpace (fun _ : CGPTag L Z => ℝ²) → X)
    (hselect : ∀ x ∈ cgpProjMap L Z (cgpQ2Tags L Z) '' fc27EdgeSet L 8,
      cgpProjMap L Z (cgpQ2Tags L Z) (select x) = x)
    {L' sg δc : ℝ} (hL' : 1 ≤ L') (hsg : 0 < sg) (hLsg : L' * sg ≤ 1 / 5)
    (plane : BlockSpace (fun _ : CGPTag L Z => ℝ²) →
      Submodule ℝ (BlockSpace (fun _ : CGPTag L Z => ℝ²)))
    (hdim : ∀ x ∈ cgpProjMap L Z (cgpQ2Tags L Z) '' fc27EdgeSet L 7,
      Module.finrank ℝ (plane x) = 1)
    (hδ : 0 < δc) (hδsmall : δc < min (1 / (4 * (5 / 3)))
      (min (1 / (2 * (L' * (5 / 3) + 3))) (1 / (4 * (5 / 3 + 1)))))
    (hcloud : ∀ x ∈ cgpProjMap L Z (cgpQ2Tags L Z) '' fc27EdgeSet L 7,
      hausdorffEDist (cgpProjMap L Z (cgpQ2Tags L Z) '' fc27EdgeSet L 8 ∩
          ball x (sg * ρ (select x) / δc))
        ((AffineSubspace.mk' x (plane x) : Set (BlockSpace (fun _ : CGPTag L Z => ℝ²))) ∩
          ball x (sg * ρ (select x) / δc)) ≤ ENNReal.ofReal (δc * (sg * ρ (select x)))) :
    ∀ x ∈ cgpProjMap L Z (cgpQ2Tags L Z) '' fc27EdgeSet L 7,
      ∀ y ∈ cgpProjMap L Z (cgpQ2Tags L Z) '' fc27EdgeSet L 7,
      dist y x ≤ L' * max (sg * ρ (select x)) (sg * ρ (select y)) →
      ‖(plane x)ᗮ.starProjection (y - x)‖ ≤ δc * (sg * ρ (select x)) ∧
        ‖(plane x)ᗮ.starProjection - (plane y)ᗮ.starProjection‖ ≤ 6 * (5 / 3 + 1) * δc := by
  have hsub := image_mono (f := cgpProjMap L Z (cgpQ2Tags L Z))
    (fc27EdgeSet_mono L (by linarith) (by norm_num : (7 : ℝ) ≤ 8))
  have hmc := fc27_edge_cloud_mcb L Z hΔ hΛ hsmall select hselect hsg.le (by linarith) hLsg
  refine cfs08_of_scale_ratio_KA3 _ _ hsub (fun x => sg * ρ (select x))
    (fun x _ => mul_pos hsg (hρ _)) 1 plane hdim hL' ?_ hδ hδsmall hcloud
  intro x hx y hy hd
  exact hmc x (hsub hx) y (hsub hy) (by rw [max_comm]; exact hd)

/-- **CFS08 on FC27's slim cloud**: `S₃ = π₃𝓔⁰(A₃) ⊆ S̃₃ = π₃𝓔⁰(Ã₃)` with FC26's selected radius
`Σρ ∘ select` (ANY selection of preimages over `S̃₃`) and one-dimensional planes. -/
theorem cfs08_slim_cloud (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4)
    (select : BlockSpace (fun _ : CGPTag L Z => ℝ²) → X)
    (hselect : ∀ x ∈ cgpProjMap L Z (cgpQ3Tags L Z) '' fc27SlimSet L 8,
      cgpProjMap L Z (cgpQ3Tags L Z) (select x) = x)
    {L' sg δc : ℝ} (hL' : 1 ≤ L') (hsg : 0 < sg) (hLsg : L' * sg ≤ 1 / 5)
    (plane : BlockSpace (fun _ : CGPTag L Z => ℝ²) →
      Submodule ℝ (BlockSpace (fun _ : CGPTag L Z => ℝ²)))
    (hdim : ∀ x ∈ cgpProjMap L Z (cgpQ3Tags L Z) '' fc27SlimSet L 7,
      Module.finrank ℝ (plane x) = 1)
    (hδ : 0 < δc) (hδsmall : δc < min (1 / (4 * (5 / 3)))
      (min (1 / (2 * (L' * (5 / 3) + 3))) (1 / (4 * (5 / 3 + 1)))))
    (hcloud : ∀ x ∈ cgpProjMap L Z (cgpQ3Tags L Z) '' fc27SlimSet L 7,
      hausdorffEDist (cgpProjMap L Z (cgpQ3Tags L Z) '' fc27SlimSet L 8 ∩
          ball x (sg * ρ (select x) / δc))
        ((AffineSubspace.mk' x (plane x) : Set (BlockSpace (fun _ : CGPTag L Z => ℝ²))) ∩
          ball x (sg * ρ (select x) / δc)) ≤ ENNReal.ofReal (δc * (sg * ρ (select x)))) :
    ∀ x ∈ cgpProjMap L Z (cgpQ3Tags L Z) '' fc27SlimSet L 7,
      ∀ y ∈ cgpProjMap L Z (cgpQ3Tags L Z) '' fc27SlimSet L 7,
      dist y x ≤ L' * max (sg * ρ (select x)) (sg * ρ (select y)) →
      ‖(plane x)ᗮ.starProjection (y - x)‖ ≤ δc * (sg * ρ (select x)) ∧
        ‖(plane x)ᗮ.starProjection - (plane y)ᗮ.starProjection‖ ≤ 6 * (5 / 3 + 1) * δc := by
  have hsub := image_mono (f := cgpProjMap L Z (cgpQ3Tags L Z))
    (fc27SlimSet_mono L (by linarith) (by norm_num : (7 : ℝ) ≤ 8))
  have hmc := fc27_slim_cloud_mcb L Z hΔ hΛ hsmall select hselect hsg.le (by linarith) hLsg
  refine cfs08_of_scale_ratio_KA3 _ _ hsub (fun x => sg * ρ (select x))
    (fun x _ => mul_pos hsg (hρ _)) 1 plane hdim hL' ?_ hδ hδsmall hcloud
  intro x hx y hy hd
  exact hmc x (hsub hx) y (hsub hy) (by rw [max_comm]; exact hd)

end Clouds

end DifferentialGeometry.Geometry.Collapse
