import DifferentialGeometry.Geometry.Collapse.LocalExport.SlimFibreSmoothType
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14ZeroTypesInhabitant

/-!
# The smooth fibre type of the original slim pieces of the final family (physical form)

Lane C14-FIBRE-PRE (class-(b) derived lemma, dispositions-task53; GAF07 B:6049). Binding of
`SlimFibreSmoothType.lean` (abstract `SlimChart` / `SlimPacket`) to the slim centres of the final
closed family `LocalChartPacketsC14Z` (through its projection `slim : SlimFamily`), in PHYSICAL
units (`B(j, 10⁶Δρ(j))`; the packet lives at the normalized scale `(ρ(j)⁻¹ d, ρ(j)⁻² g)`, whose
topology is the same).

* `SlimCentre.fibre_smooth_type_FPRE`: at a slim centre `j` there is ONE compact connected smooth
  surface `F` (the zero fibre of the original coordinate with its regular-fibre structure),
  homeomorphic to `S²` or `T²`, such that for EVERY `|a| < 905·10³Δ` the WHOLE level set
  `{x ∈ B(j, 10⁶Δρ(j)) | η_j x = a}` is the image of a smooth embedding `F → X` (smooth, topological
  embedding, injective differential). The homeomorphism field `zeroLevel_type` enters only the
  topological type of `F`; NO diffeomorphism `F ≃ₘ S²/T²` is claimed (obstruction in
  `SlimFibreSmoothType.lean`).
* `LocalChartPacketsC14Z.slim_fibre_smooth_type_FPRE`: the same at every slim centre of the final
  family.
* consumer `slim_fibre_smooth_type_pempty_FPRE`: on the structural inhabitant over `PEmpty`
  (`nonempty_localChartPacketsC14Z_pempty_FAMZ`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- The model of the slim fibres (`dim X - 1`). -/
local notation "𝓘S" => 𝓘(ℝ, Fin (Module.finrank ℝ E3 - Module.finrank ℝ ℝ) → ℝ)

section Family

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p}

namespace SlimCentre

variable {β₁ Δ σs : ℝ} {K : ℕ} {j : X}

/-- **The smooth fibre type of an original slim piece, physical form.** At a slim centre `j`
(`0 < Δ`) there is ONE compact connected smooth surface `F` (the zero fibre of the original
coordinate with its regular-fibre structure), homeomorphic to `S²` or to `T²`, such that for every
`|a| < 905·10³Δ` the WHOLE level set `{x ∈ B(j, 10⁶Δρ(j)) | η_j x = a}` is the image of a smooth
embedding `ι : F → X` (smooth, topological embedding, injective differential). -/
theorem fibre_smooth_type_FPRE (c : SlimCentre X g hmetric ρ hρ β₁ Δ σs K j) (hΔ : 0 < Δ) :
    ∃ (F : Type) (_ : TopologicalSpace F) (_ : ChartedSpace (Fin (Module.finrank ℝ E3 -
        Module.finrank ℝ ℝ) → ℝ) F),
      IsManifold 𝓘S ∞ F ∧ CompactSpace F ∧ ConnectedSpace F ∧
      (Nonempty (F ≃ₜ Metric.sphere (0 : E3) 1) ∨
        Nonempty (F ≃ₜ (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)))) ∧
      ∀ a : ℝ, |a| < 905 * 10 ^ 3 * Δ → ∃ ι : F → X, ContMDiff 𝓘S 𝓘(ℝ, E3) ∞ ι ∧
        Topology.IsEmbedding ι ∧ (∀ y, Injective (mfderiv 𝓘S 𝓘(ℝ, E3) ι y)) ∧
        range ι = {x | x ∈ ball j (10 ^ 6 * Δ * ρ j) ∧ c.coord x = a} := by
  let P := c.packet
  let iZ := c.instZ
  let hMc : CompleteSpace X := complete_of_compact
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  let i₀ := P.fibreChartedSpace_FPRE le_rfl (SlimChart.zeroPoint_FPRE hΔ)
  obtain ⟨hman, -, hcpt, hconn, htype, -⟩ :=
    P.smooth_fibre_type_FPRE hΔ le_rfl (SlimChart.zeroPoint_FPRE hΔ)
  refine ⟨_, _, i₀, hman, hcpt, hconn, htype, fun a ha => ?_⟩
  let a' : lineBallOpens (905 * 10 ^ 3 * Δ) := ⟨a, mem_lineBallOpens_iff.mpr ha⟩
  obtain ⟨ι, hsm, hemb, hinj, hrange⟩ := P.exists_embedding_fibre_FPRE hΔ a'
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

/-- **The smooth fibre type of every original slim piece of the final family** (physical form of
`SlimCentre.fibre_smooth_type_FPRE` at every slim centre of `LocalChartPacketsC14Z`). -/
theorem LocalChartPacketsC14Z.slim_fibre_smooth_type_FPRE
    (P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM) (hΔ : 0 < Δ) {j : X} (hj : j ∈ P.slim.centres) :
    ∃ (F : Type) (_ : TopologicalSpace F) (_ : ChartedSpace (Fin (Module.finrank ℝ E3 -
        Module.finrank ℝ ℝ) → ℝ) F),
      IsManifold 𝓘S ∞ F ∧ CompactSpace F ∧ ConnectedSpace F ∧
      (Nonempty (F ≃ₜ Metric.sphere (0 : E3) 1) ∨
        Nonempty (F ≃ₜ (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)))) ∧
      ∀ a : ℝ, |a| < 905 * 10 ^ 3 * Δ → ∃ ι : F → X, ContMDiff 𝓘S 𝓘(ℝ, E3) ∞ ι ∧
        Topology.IsEmbedding ι ∧ (∀ y, Injective (mfderiv 𝓘S 𝓘(ℝ, E3) ι y)) ∧
        range ι = {x | x ∈ ball j (10 ^ 6 * Δ * ρ j) ∧ (P.slim.centre j hj).coord x = a} :=
  (P.slim.centre j hj).fibre_smooth_type_FPRE hΔ

end Family

section Consumer

/-- The metric on `PEmpty` (the same term as the instance of `metricPEmpty_FAM`). -/
local instance metricSpacePEmpty_FPRE : MetricSpace PEmpty.{1} :=
  (MetricSpace.induced (PEmpty.elim : PEmpty.{1} → ℝ) (fun x => x.elim)
    inferInstance).replaceTopology (by ext s; simp only [Set.eq_empty_of_isEmpty s, isOpen_empty])

/-- The empty three-manifold (the same term as the instance of `metricPEmpty_FAM`). -/
local instance chartedSpacePEmpty_FPRE : ChartedSpace E3 PEmpty.{1} :=
  ChartedSpace.empty E3 PEmpty.{1}

/-- **Consumer on the structural inhabitant over `PEmpty`**: the final family over the empty
three-manifold carries the smooth fibre type at every slim centre (vacuously: no slim centre). -/
theorem slim_fibre_smooth_type_pempty_FPRE (Λ : ℝ) (β : ℕ → ℝ) (Δ σs : ℝ) (K : ℕ)
    (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ) (hΔ : 0 < Δ) :
    ∃ P : LocalChartPacketsC14Z PEmpty.{1} metricPEmpty_FAM (fun a => a.elim) (fun a => a.elim)
        (fun a => a.elim) Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
        manifoldOrientationPEmpty_FAMZ,
      ∀ j (hj : j ∈ P.slim.centres),
        ∃ (F : Type) (_ : TopologicalSpace F) (_ : ChartedSpace (Fin (Module.finrank ℝ E3 -
            Module.finrank ℝ ℝ) → ℝ) F),
          IsManifold 𝓘S ∞ F ∧ CompactSpace F ∧ ConnectedSpace F ∧
          (Nonempty (F ≃ₜ Metric.sphere (0 : E3) 1) ∨
            Nonempty (F ≃ₜ (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)))) ∧
          ∀ a : ℝ, |a| < 905 * 10 ^ 3 * Δ → ∃ ι : F → PEmpty.{1},
            ContMDiff 𝓘S 𝓘(ℝ, E3) ∞ ι ∧ Topology.IsEmbedding ι ∧
            (∀ y, Injective (mfderiv 𝓘S 𝓘(ℝ, E3) ι y)) ∧
            range ι = {x | x ∈ ball j (10 ^ 6 * Δ * (fun a : PEmpty.{1} => a.elim) j) ∧
              (P.slim.centre j hj).coord x = a} := by
  obtain ⟨P⟩ := nonempty_localChartPacketsC14Z_pempty_FAMZ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax
    τ γ δ εr e T V vs ζ Λz manifoldOrientationPEmpty_FAMZ
  exact ⟨P, fun j hj => P.slim_fibre_smooth_type_FPRE hΔ hj⟩

end Consumer

end DifferentialGeometry.Geometry.Collapse
