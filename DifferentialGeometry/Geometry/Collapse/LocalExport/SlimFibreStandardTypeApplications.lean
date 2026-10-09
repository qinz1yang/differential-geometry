import DifferentialGeometry.Geometry.Collapse.LocalExport.SlimFibreStandardType
import DifferentialGeometry.Geometry.Collapse.LocalExport.SlimFibreSmoothTypeApplications
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SlimModelOrientation

/-!
# The original slim fibres of the final family are standard `S²` / `T²` (review 70, D70-4)

Lane C14-SLIM-STD, group 3 (external review 70 §3.4, disposition D70-4). The strong form of
C14-FIBRE-PRE's `LocalChartPacketsC14Z.slim_fibre_smooth_type_FPRE`: at every slim centre `j` of
the final closed family there is ONE compact connected smooth surface `F` (the zero fibre of the
original coordinate with its regular-fibre structure), smoothly diffeomorphic to the STANDARD
`ClosureSphere` or `Torus`, such that every whole level set `{x ∈ B(j, 10⁶Δρ(j)) | η_j x = a}`,
`|a| < 905·10³Δ`, is the exact image of a smooth embedding of `F`. The weak theorem stays.

Route, for an ARBITRARY `P : LocalChartPacketsC14Z … oM` (no new field, no second existence
theorem): the stored model `SlimCentre.model` of the SAME centre (with the SAME normalized
instances), oriented by route β from the family's orientation parameter `oM`
(`SlimProductModel.nonempty_orientation_of_oriented_source_SSTD`), has a surface factor
(`nonempty_slimSurfaceFactor`), and D70-2 (`SlimChart.zero_fibre_standard_type_SSTD`) identifies
FIBRE-PRE's zero fibre of the stored packet with the standard model.

* `SlimCentre.fibre_standard_type_SSTD` (one slim centre, `K ≥ 5`, `Δ ≥ 1`, any `oM`);
* `LocalChartPacketsC14Z.slim_fibre_standard_type_SSTD` (D70-4, review §3.4's statement);
* consumer `LocalChartPacketsC14Z.slim_level_standard_embedding_SSTD`: every whole slim level set is
  the exact image of an `IsSmoothEmbedding` of the standard `ClosureSphere`, or every one of the
  standard `Torus` (FC39's `SlimFibre` shape, at every slim centre of the final family).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open GC.GraphManifold GC.Endpoint

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- The model of the slim fibres (`dim X - 1`). -/
local notation "𝓘S" => 𝓘(ℝ, Fin (Module.finrank ℝ E3 - Module.finrank ℝ ℝ) → ℝ)

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p}

namespace SlimCentre

variable {β₁ Δ σs : ℝ} {K : ℕ} {j : X}

/-- **The standard smooth fibre type of an original slim piece, physical form** (D70-4 at one
centre). At a slim centre `j` (`K ≥ 5`, `Δ ≥ 1`) of a manifold with an orientation `oM` there is
ONE compact connected smooth surface `F`, diffeomorphic to the standard `ClosureSphere` or `Torus`,
such that for every `|a| < 905·10³Δ` the WHOLE level set `{x ∈ B(j, 10⁶Δρ(j)) | η_j x = a}` is the
image of a smooth embedding `ι : F → X` (smooth, topological embedding, injective differential). -/
theorem fibre_standard_type_SSTD (c : SlimCentre X g hmetric ρ hρ β₁ Δ σs K j) (hK : 5 ≤ K)
    (hΔ : 1 ≤ Δ) (oM : ManifoldOrientation 𝓘(ℝ, E3) X 3) :
    ∃ (F : Type) (_ : TopologicalSpace F) (_ : ChartedSpace (Fin (Module.finrank ℝ E3 -
        Module.finrank ℝ ℝ) → ℝ) F),
      IsManifold 𝓘S ∞ F ∧ CompactSpace F ∧ ConnectedSpace F ∧
      (Nonempty (F ≃ₘ⟮𝓘S, 𝓡 2⟯ ClosureSphere.{0}) ∨ Nonempty (F ≃ₘ⟮𝓘S, torusModel⟯ Torus)) ∧
      ∀ a : ℝ, |a| < 905 * 10 ^ 3 * Δ → ∃ ι : F → X, ContMDiff 𝓘S 𝓘(ℝ, E3) ∞ ι ∧
        Topology.IsEmbedding ι ∧ (∀ y, Injective (mfderiv 𝓘S 𝓘(ℝ, E3) ι y)) ∧
        range ι = {x | x ∈ ball j (10 ^ 6 * Δ * ρ j) ∧ c.coord x = a} := by
  have hΔ0 : 0 < Δ := lt_of_lt_of_le zero_lt_one hΔ
  let P := c.packet
  let PM := c.model
  let iZ := c.instZ
  let hMc : CompleteSpace X := complete_of_compact
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  let i₀ := P.fibreChartedSpace_FPRE le_rfl (SlimChart.zeroPoint_FPRE hΔ0)
  obtain ⟨hman, -, hcpt, hconn, -, -⟩ :=
    P.smooth_fibre_type_FPRE hΔ0 le_rfl (SlimChart.zeroPoint_FPRE hΔ0)
  obtain ⟨Q⟩ := SlimProductModel.nonempty_slimSurfaceFactor_of_oriented_source_SSTD hK hΔ PM oM
  have htype := P.toSlimChart.zero_fibre_standard_type_SSTD.{0} hK hΔ PM Q
  refine ⟨_, _, i₀, hman, hcpt, hconn, htype, fun a ha => ?_⟩
  let a' : lineBallOpens (905 * 10 ^ 3 * Δ) := ⟨a, mem_lineBallOpens_iff.mpr ha⟩
  obtain ⟨ι, hsm, hemb, hinj, hrange⟩ := P.exists_embedding_fibre_FPRE hΔ0 a'
  refine ⟨ι, hsm, hemb, hinj, ?_⟩
  rw [hrange]
  ext x
  have hr := hρ j
  constructor
  · rintro ⟨hx, hxa⟩
    refine ⟨?_, hxa⟩
    have h' : (ρ j)⁻¹ * @dist X mX.toDist x j < 10 ^ 6 * Δ := hx
    rw [inv_mul_lt_iff₀ hr] at h'
    change @dist X mX.toDist x j < 10 ^ 6 * Δ * ρ j
    linarith
  · rintro ⟨hx, hxa⟩
    refine ⟨?_, hxa⟩
    have h2 : (ρ j)⁻¹ * @dist X mX.toDist x j < 10 ^ 6 * Δ :=
      @inv_mul_dist_lt_of_mem_ball_LC87 X mX ρ j x _ hr hx
    exact h2

end SlimCentre

variable {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}

/-- **D70-4: the standard smooth fibre type of every original slim piece of the final family.**
For `K ≥ 5`, `Δ ≥ 1` and every slim centre `j` of `P : LocalChartPacketsC14Z … oM`: ONE compact
connected smooth surface `F`, diffeomorphic to the standard `ClosureSphere` or `Torus`, smoothly
embedded ONTO every whole level set `{x ∈ B(j, 10⁶Δρ(j)) | η_j x = a}`, `|a| < 905·10³Δ`. -/
theorem LocalChartPacketsC14Z.slim_fibre_standard_type_SSTD
    (P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM) (hK : 5 ≤ K) (hΔ : 1 ≤ Δ) {j : X} (hj : j ∈ P.slim.centres) :
    ∃ (F : Type) (_ : TopologicalSpace F) (_ : ChartedSpace (Fin (Module.finrank ℝ E3 -
        Module.finrank ℝ ℝ) → ℝ) F),
      IsManifold 𝓘S ∞ F ∧ CompactSpace F ∧ ConnectedSpace F ∧
      (Nonempty (F ≃ₘ⟮𝓘S, 𝓡 2⟯ ClosureSphere.{0}) ∨ Nonempty (F ≃ₘ⟮𝓘S, torusModel⟯ Torus)) ∧
      ∀ a : ℝ, |a| < 905 * 10 ^ 3 * Δ → ∃ ι : F → X, ContMDiff 𝓘S 𝓘(ℝ, E3) ∞ ι ∧
        Topology.IsEmbedding ι ∧ (∀ y, Injective (mfderiv 𝓘S 𝓘(ℝ, E3) ι y)) ∧
        range ι = {x | x ∈ ball j (10 ^ 6 * Δ * ρ j) ∧ (P.slim.centre j hj).coord x = a} :=
  (P.slim.centre j hj).fibre_standard_type_SSTD hK hΔ oM

/-- **Consumer: standard parametrizations of the slim levels of the final family.** At every slim
centre `j` (`K ≥ 5`, `Δ ≥ 1`): EITHER every whole level set `{x ∈ B(j, 10⁶Δρ(j)) | η_j x = a}`,
`|a| < 905·10³Δ`, is the exact image of a smooth embedding (`IsSmoothEmbedding`) of the standard
`ClosureSphere`, OR every one is the exact image of a smooth embedding of the standard `Torus`. -/
theorem LocalChartPacketsC14Z.slim_level_standard_embedding_SSTD
    (P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM) (hK : 5 ≤ K) (hΔ : 1 ≤ Δ) {j : X} (hj : j ∈ P.slim.centres) :
    (∀ a : ℝ, |a| < 905 * 10 ^ 3 * Δ → ∃ f : ClosureSphere.{0} → X,
      IsSmoothEmbedding (𝓡 2) 𝓘(ℝ, E3) ∞ f ∧
        range f = {x | x ∈ ball j (10 ^ 6 * Δ * ρ j) ∧ (P.slim.centre j hj).coord x = a}) ∨
    (∀ a : ℝ, |a| < 905 * 10 ^ 3 * Δ → ∃ f : Torus → X,
      IsSmoothEmbedding torusModel 𝓘(ℝ, E3) ∞ f ∧
        range f = {x | x ∈ ball j (10 ^ 6 * Δ * ρ j) ∧ (P.slim.centre j hj).coord x = a}) := by
  obtain ⟨F, tF, cF, hF, -, -, htype, hemb⟩ := P.slim_fibre_standard_type_SSTD hK hΔ hj
  rcases htype with ⟨⟨d⟩⟩ | ⟨⟨d⟩⟩
  · refine Or.inl fun a ha => ?_
    obtain ⟨ι, hι, he, hi, hr⟩ := hemb a ha
    obtain ⟨h1, h2⟩ := isSmoothEmbedding_comp_diffeomorph_symm_SSTD ι hι he hi d
    exact ⟨ι ∘ d.symm, h1, h2.trans hr⟩
  · refine Or.inr fun a ha => ?_
    obtain ⟨ι, hι, he, hi, hr⟩ := hemb a ha
    obtain ⟨h1, h2⟩ := isSmoothEmbedding_comp_diffeomorph_symm_SSTD ι hι he hi d
    exact ⟨ι ∘ d.symm, h1, h2.trans hr⟩

end DifferentialGeometry.Geometry.Collapse
