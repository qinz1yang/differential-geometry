import DifferentialGeometry.Geometry.Fibration.ActualStageChainFc36Row

/-!
# Consumer of FC36's row: the slim piece is compact and contains every interval product

Lane S-FC-WRAP, group G1 (suffix `_FCW`). From `fc36_row_FCW` (GAF07 slim ∧ ZSP04 on one `K₃`):
`M^slim = f₃⁻¹(K₃ ∩ C₃)` is compact, maps onto `D₃ = K₃ ∩ C₃`, and for every arc `k` of `D₃` the
`S² × I` (or `T² × I`) over `arc k` is the range of a smooth injective map
`F × [0, 1] → M` lying INSIDE `M^slim` with `f₃ ∘ map = arc k ∘ pr₂`; together with the first
conjunct, properness of `π₃E : X₃ → B₃` over the open base `B₃`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis
open GC.GraphManifold GC.Endpoint
open DifferentialGeometry.Topology DifferentialGeometry.Topology.Ehresmann

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- **Consumer of FC36**: GAF07's proper onto slim bundle over `B₃` together with ONE compact
`M^slim = f₃⁻¹(D₃)` over `D₃ = K₃ ∩ C₃` that is mapped onto `D₃` and contains the whole preimage of
every arc of `D₃` as the range of a smooth injective map `F × [0, 1] → M`. -/
theorem fc36_slim_piece_fibres_FCW {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3} {cadj : ℝ}
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM}
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) (hK : 5 ≤ K) :
    IsProperMap (C.toChain.slimBase_BAS.restrictPreimage
      (fun p => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p))) ∧
    ∃ K₃ D₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35,
      IsCompact (C.slimPiece_ZSP35 K₃.carrier) ∧
      C.slimMap_ZSP35 '' C.slimPiece_ZSP35 K₃.carrier = D₃.carrier ∧
      ∀ k : Fin D₃.m,
        (∃ m : ClosureSphere.{0} × Icc (0 : ℝ) 1 → X,
          ContMDiff ((𝓡 2).prod (𝓡∂ 1)) 𝓘(ℝ, E3) ∞ m ∧ Injective m ∧
          (∀ z, C.slimMap_ZSP35 (m z) = D₃.arc k z.2) ∧
          range m ⊆ C.slimPiece_ZSP35 K₃.carrier) ∨
        (∃ m : Torus × Icc (0 : ℝ) 1 → X,
          ContMDiff (torusModel.prod (𝓡∂ 1)) 𝓘(ℝ, E3) ∞ m ∧ Injective m ∧
          (∀ z, C.slimMap_ZSP35 (m z) = D₃.arc k z.2) ∧
          range m ⊆ C.slimPiece_ZSP35 K₃.carrier) := by
  obtain ⟨hrow, K₃, D₃, hD, -, -, -, -, -, hSc, -, himg, -, -, -, -, harc, -⟩ :=
    C.fc36_row_FCW hεr hK
  have hmem : ∀ (k : Fin D₃.m) (z : Icc (0 : ℝ) 1), D₃.arc k z.1 ∈ C.slimC3_ZSP35 := fun k z => by
    have h : D₃.arc k z.1 ∈ D₃.carrier := by
      rw [D₃.carrier_eq]
      exact Or.inl (mem_iUnion.mpr ⟨k, z.1, z.2, rfl⟩)
    rw [hD] at h
    exact h.2
  have hmem' : ∀ (k : Fin D₃.m) (z : Icc (0 : ℝ) 1), D₃.arc k z.1 ∈ K₃.carrier := fun k z => by
    have h : D₃.arc k z.1 ∈ D₃.carrier := by
      rw [D₃.carrier_eq]
      exact Or.inl (mem_iUnion.mpr ⟨k, z.1, z.2, rfl⟩)
    rw [hD] at h
    exact h.1
  refine ⟨hrow.2.2.2.1, K₃, D₃, hSc, himg, fun k => ?_⟩
  rcases harc k with ⟨F₀, ⟨W⟩⟩ | ⟨F₀, ⟨W⟩⟩
  · have hp : ∀ z, C.slimMap_ZSP35 (W.map z) = D₃.arc k z.2 := W.proj_eq
    refine Or.inl ⟨W.map, W.smooth, W.injective, hp, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact ⟨by rw [hp]; exact hmem' k z.2, by rw [hp]; exact hmem k z.2⟩
  · have hp : ∀ z, C.slimMap_ZSP35 (W.map z) = D₃.arc k z.2 := W.proj_eq
    refine Or.inr ⟨W.map, W.smooth, W.injective, hp, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact ⟨by rw [hp]; exact hmem' k z.2, by rw [hp]; exact hmem k z.2⟩

end DifferentialGeometry.Geometry.Collapse
