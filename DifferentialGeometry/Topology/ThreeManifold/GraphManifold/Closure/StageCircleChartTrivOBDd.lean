import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageOfBundlesTriv74
import DifferentialGeometry.Topology.Embedding.Diffeomorph
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingOpenTarget
import DifferentialGeometry.Topology.Manifold.ImmersionDifferential
import DifferentialGeometry.Topology.Manifold.OpenEmbedding

/-!
# A product chart of a circle stage is a local trivialization (lane S-BD2d, suffix `_OBDd`)

Lane O-BD1 (by S-BD2d), group G9, kernel. For a stage `Q : StageProj74 W 2` (smooth submersion
`q : parent → Base`) and a base point `b`, a smooth embedding `φ : ℝ² × S¹ → W` onto the WHOLE
`q`-preimage of the image of an injective `σ' : ℝ² → Base` with `q (φ (x, z)) = σ' x` is a local
trivialization of `q`: neither the manifold structure of the base nor the base inclusion enters.

* `exists_stageTrivialization_of_chart_OBDd`: `σ'` is `q ∘ φ ∘ (·, z₀)`, hence smooth; the
  composite `q ∘ φ = σ' ∘ fst` of two submersive maps and the bijective differential of the
  full-dimensional embedding `φ` make `dσ'` surjective, hence an isomorphism; `σ'` is a
  diffeomorphism onto the open set `N = range σ'`; the two smooth embeddings
  `φ ∘ (σ'⁻¹ × id) : N × S¹ → parent` and the inclusion `q⁻¹(N) → parent` have the same range, so
  `IsSmoothEmbedding.diffeomorphOfRangeEq` gives the diffeomorphism `q⁻¹(N) ≃ₘ N × S¹` over `N`
  (no interior atlas, whatever the carrier's boundary);
* `exists_circleCutTriv_of_charts_OBDd`: from such charts at every base point, the four
  trivialization fields of `CircleCutFacts74` over ANY open set `V` of the base (the restriction
  kit `CircleBundle.stageTrivialization_JN74` applied to the circle bundle with `cbase = ∅`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open scoped ContDiff Manifold Topology
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold

universe u

namespace GC.GraphManifold.Assembly.FC39P0

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- **A product chart of a circle stage is a local trivialization over the image of its base
parametrization.** -/
theorem exists_stageTrivialization_of_chart_OBDd {W : CompactCarrier.{u}} (Q : StageProj74 W 2)
    (σ' : ℝ² → Q.Base) (φ : ℝ² × Circle → W.Carrier) (hσinj : Injective σ')
    (hφ : IsSmoothEmbedding ((𝓡 2).prod (𝓡 1)) W.model ∞ φ)
    (hmem : ∀ x z, φ (x, z) ∈ Q.parent)
    (hproj : ∀ x z (h : φ (x, z) ∈ Q.parent), Q.proj ⟨φ (x, z), h⟩ = σ' x)
    (hrange : ∀ (p : W.Carrier) (hp : p ∈ Q.parent), Q.proj ⟨p, hp⟩ ∈ range σ' →
      p ∈ range φ) :
    ∃ N : TopologicalSpace.Opens Q.Base, (N : Set Q.Base) = range σ' ∧
      ∃ T : (TopologicalSpace.Opens.comap Q.proj N)
        ≃ₘ⟮W.model, (𝓡 2).prod (𝓡 1)⟯ (N × Circle), ∀ x, ((T x).1).val = Q.proj x.val := by
  classical
  let Φ₀ : ℝ² × Circle → Q.parent := fun p => ⟨φ p, hmem p.1 p.2⟩
  have hΦ₀ : IsSmoothEmbedding ((𝓡 2).prod (𝓡 1)) W.model ∞ Φ₀ :=
    DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_intoOpen _ _ Q.parent Φ₀ hφ
  have hΦ₀proj : ∀ p, Q.proj (Φ₀ p) = σ' p.1 := fun p => hproj p.1 p.2 (hmem p.1 p.2)
  have hcomp : (fun p : ℝ² × Circle => σ' p.1) = Q.proj ∘ Φ₀ :=
    funext fun p => (hΦ₀proj p).symm
  have hσs : ContMDiff (𝓡 2) (𝓡 2) ∞ σ' := by
    have h1 : ContMDiff (𝓡 2) (W.model) ∞ (fun x : ℝ² => Φ₀ (x, (1 : Circle))) :=
      hΦ₀.contMDiff.comp (contMDiff_id.prodMk contMDiff_const)
    have h2 := Q.proj_smooth.comp h1
    exact h2.congr fun x => (hΦ₀proj (x, 1)).symm
  have himm : ∀ x, Injective (mfderiv (𝓡 2) (𝓡 2) σ' x) := by
    intro x
    let p : ℝ² × Circle := (x, 1)
    have hB : Bijective (mfderiv ((𝓡 2).prod (𝓡 1)) W.model Φ₀ p) :=
      DifferentialGeometry.Topology.Manifold.bijective_mfderiv_of_isImmersionAt _ _ Φ₀ p
        (hΦ₀.isImmersion.isImmersionAt p) (by simp)
    have hS : Surjective (mfderiv ((𝓡 2).prod (𝓡 1)) (𝓡 2) (Q.proj ∘ Φ₀) p) := by
      rw [mfderiv_comp p (Q.proj_smooth.mdifferentiableAt (by simp))
        (hΦ₀.contMDiff.mdifferentiableAt (by simp))]
      exact (Q.proj_submersion (Φ₀ p)).comp hB.2
    have hS2 : Surjective (mfderiv ((𝓡 2).prod (𝓡 1)) (𝓡 2) (fun p : ℝ² × Circle => σ' p.1) p) := by
      rw [hcomp]
      exact hS
    have hfst : MDifferentiableAt ((𝓡 2).prod (𝓡 1)) (𝓡 2) (Prod.fst : ℝ² × Circle → ℝ²) p :=
      (contMDiff_fst (I := 𝓡 2) (J := 𝓡 1) (n := ∞)).mdifferentiableAt (by simp)
    have hS3 : Surjective (mfderiv (𝓡 2) (𝓡 2) σ' x) := by
      have h := mfderiv_comp p (g := σ') (f := (Prod.fst : ℝ² × Circle → ℝ²))
        (hσs.mdifferentiableAt (by simp)) hfst
      have h' : mfderiv ((𝓡 2).prod (𝓡 1)) (𝓡 2) (fun p : ℝ² × Circle => σ' p.1) p =
          (mfderiv (𝓡 2) (𝓡 2) σ' x).comp (mfderiv ((𝓡 2).prod (𝓡 1)) (𝓡 2) Prod.fst p) := h
      rw [h'] at hS2
      exact Surjective.of_comp hS2
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).2 hS3
  obtain ⟨N, Ψ, hNr, hΨ, hΨ'⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_diffeomorph_onto_range_of_injective_immersion
      (I := 𝓡 2) (J := 𝓡 2) σ' hσs hσinj himm rfl
  let Θ : (N × Circle) ≃ₘ⟮(𝓡 2).prod (𝓡 1), (𝓡 2).prod (𝓡 1)⟯ (ℝ² × Circle) :=
    Ψ.symm.prodCongr (Diffeomorph.refl (𝓡 1) Circle ∞)
  have hf' : IsSmoothEmbedding ((𝓡 2).prod (𝓡 1)) W.model ∞ (Φ₀ ∘ Θ) :=
    hΦ₀.comp_diffeomorph Θ
  have hg' : IsSmoothEmbedding W.model W.model ∞
      (Subtype.val : (TopologicalSpace.Opens.comap Q.proj N) → Q.parent) :=
    IsSmoothEmbedding.of_opens (I := W.model) (n := ∞) (TopologicalSpace.Opens.comap Q.proj N)
  have hR : range (Φ₀ ∘ Θ) = range
      (Subtype.val : (TopologicalSpace.Opens.comap Q.proj N) → Q.parent) := by
    ext p
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨⟨Φ₀ (Θ y), ?_⟩, rfl⟩
      change Q.proj (Φ₀ (Θ y)) ∈ N
      rw [hΦ₀proj]
      change σ' (Θ y).1 ∈ (N : Set Q.Base)
      rw [hNr]
      exact mem_range_self _
    · rintro ⟨q, rfl⟩
      have hq : Q.proj q.val ∈ range σ' := by
        have := q.2
        change Q.proj q.val ∈ (N : Set Q.Base) at this
        rwa [hNr] at this
      obtain ⟨⟨x, z⟩, hxz⟩ := hrange q.val.1 q.val.2 hq
      refine ⟨(Ψ x, z), ?_⟩
      have hs : Ψ.symm (Ψ x) = x := Ψ.symm_apply_apply x
      change Φ₀ (Ψ.symm (Ψ x), z) = q.val
      rw [hs]
      exact Subtype.ext hxz
  let E := hf'.diffeomorphOfRangeEq hg' hR
  refine ⟨N, hNr, E.symm, fun x => ?_⟩
  have h1 := hf'.comp_diffeomorphOfRangeEq hg' hR (E.symm x)
  rw [Diffeomorph.apply_symm_apply] at h1
  have h2 : Q.proj x.val = σ' (Ψ.symm (E.symm x).1) := by
    have h3 : x.val = Φ₀ (Θ (E.symm x)) := h1
    rw [h3, hΦ₀proj]
    rfl
  rw [h2]
  exact (hΨ' (E.symm x).1).symm

/-- **The four trivialization fields of `CircleCutFacts74` over ANY open set `V` of the base**, from
local trivializations of the stage's projection over a neighbourhood of every base point (the
restriction kit of `CircleBundle.stageTrivialization_JN74` applied to the circle bundle with
`cbase = ∅` that has the stage as its underlying stage). -/
theorem exists_circleCutTriv_of_charts_OBDd {W : CompactCarrier.{u}} (Q : StageProj74 W 2)
    (htriv : ∀ b : Q.Base, ∃ N : TopologicalSpace.Opens Q.Base, b ∈ N ∧
      ∃ T : (TopologicalSpace.Opens.comap Q.proj N)
        ≃ₘ⟮W.model, (𝓡 2).prod (𝓡 1)⟯ (N × Circle), ∀ x, ((T x).1).val = Q.proj x.val)
    (V : TopologicalSpace.Opens Q.Base) :
    ∃ nb : V → TopologicalSpace.Opens V, (∀ c, c ∈ nb c) ∧
      ∃ tr : ∀ c, (TopologicalSpace.Opens.comap (Q.restrictProj V) (nb c))
        ≃ₘ⟮W.model, (𝓡 2).prod (𝓡 1)⟯ (nb c × Circle),
        ∀ c x, ((tr c x).1).val = Q.restrictProj V x.val := by
  choose N hN T hT using htriv
  let R : CircleBundle W :=
    { Base := Q.Base
      domain := Q.parent
      domain_interior := Q.parent_interior
      proj := Q.proj
      proj_smooth := Q.proj_smooth
      proj_submersion := Q.proj_submersion
      neighborhood := N
      mem_neighborhood := hN
      trivialization := T
      projection_trivialization := hT
      cbase := ∅
      cbase_compact := isCompact_empty }
  exact ⟨R.stageNeighborhood_JN74 V, R.mem_stageNeighborhood_JN74 V,
    R.stageTrivialization_JN74 V, R.stageProjection_trivialization_JN74 V⟩

end GC.GraphManifold.Assembly.FC39P0
