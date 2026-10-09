import DifferentialGeometry.Geometry.Collapse.FixtureC2.SphereLoopStageSlim
import DifferentialGeometry.Geometry.Fibration.ActualStageChainPiecesFD4

/-!
# ZSP04's full row on a NON-EMPTY `K₃`: the slim piece through a slim centre (S-FIXTURE-C2d, G9)

`Gaf02ChainEJA.slim_pieces_nonempty_FXC2`: for a chain `C` over a closed family `P` (all packet
parameters free) with a slim centre `j` and an empty zero family, ZSP04's admissible pair
`K₃, D₃` (`zsp04_D3_ZSP35`, the five properties) carries ALL clauses of the full row
(`slim_pieces_FD4`, quoted by `type_of%`: `zsp04_full_row_ZSP35` clause by clause and the
decomposition of `M^slim = f₃⁻¹(D₃)` into the compact pieces over the arcs and loops of `D₃`), AND
is non-empty: the centre `j` lies in the slim piece (the plateau point of its slab), its image lies
in `K₃`, and `D₃` has at least one arc or loop (`0 < D₃.m + D₃.l`). On the dihedral fixture the
same row is an empty-truth test (`zsp04_full_row_dihedralTiny_ZSP35`); the C2 packet is the first
family on which the row, with the bundle clauses over the arcs and loops, is not vacuous.
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Riemannian
  GC.MetricGeometry DifferentialGeometry.Analysis GC.GraphManifold GC.Endpoint
  DifferentialGeometry.Topology DifferentialGeometry.Topology.Ehresmann
open DifferentialGeometry.Geometry.Collapse

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

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
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ} {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}

namespace Gaf02ChainEJA

variable {cadj : ℝ}
  {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V vs ζ Λz oM}

/-- **The slim piece through a slim centre** (see the module docstring). -/
theorem slim_pieces_nonempty_FXC2
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) (hK : 5 ≤ K) (hΔ : 0 < Δ) {j : X} (hj : j ∈ P.slim.centres)
    (h0 : P.zero.centres = ∅) :
    ∃ (K₃ D₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35)
      (hD : D₃.carrier = K₃.carrier ∩ C.slimC3_ZSP35)
      (hKs : C.toChain.slimSlabImage_ZSP35 ∪ C.slimFacePoints_ZSP35 ⊆
        Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
      (hKF : Disjoint (K₃.carrier \
          Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
        C.slimFacePoints_ZSP35)
      (hDreg : D₃.carrier ⊆ closure (Subtype.val '' interior
        (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35)))
      (hdD : D₃.carrier \ Subtype.val '' interior
          (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35) =
        ((K₃.carrier \ Subtype.val '' interior
              (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35)) ∩
            Subtype.val '' interior (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35)) ∪
          (Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35) ∩
            C.slimFacePoints_ZSP35)),
      type_of% (C.slim_pieces_FD4 hεr hK K₃ D₃ hD hKs hKF hDreg hdD) ∧
      j ∈ C.slimPiece_ZSP35 K₃.carrier ∧ C.slimMap_ZSP35 j ∈ K₃.carrier ∧
      0 < D₃.m + D₃.l := by
  obtain ⟨K₃, D₃, hD, hKs, hKF, hDreg, hdD⟩ := C.zsp04_D3_ZSP35 hεr
  refine ⟨K₃, D₃, hD, hKs, hKF, hDreg, hdD, ?_⟩
  have hpc := C.slim_pieces_FD4 hεr hK K₃ D₃ hD hKs hKF hDreg hdD
  have hjc : j ∈ P.toLocalChartFamily.slim.centres := hj
  have hjS : j ∈ zsp04SlimSlabs_ZSP35 P.toLocalChartPackets := by
    refine mem_iUnion.mpr ⟨⟨j, (Set.Finite.mem_toFinset _).mpr hjc⟩, ?_, ?_⟩
    · exact mem_ball_self (by have := hρ j; positivity)
    · rw [slimCentre_coord_center_FXC2, abs_zero]
      positivity
  have hE : C.zeroUnion_ZSP35 = ∅ := by
    refine eq_empty_iff_forall_notMem.mpr fun x hx => ?_
    obtain ⟨k, -⟩ := mem_iUnion.mp hx
    have hk : k.1 ∈ P.zero.centres := (Set.Finite.mem_toFinset _).mp k.2
    exact (Set.eq_empty_iff_forall_notMem.mp h0) _ hk
  have hjI : j ∈ (interior C.zeroUnion_ZSP35)ᶜ := by
    rw [hE, interior_empty, compl_empty]
    exact mem_univ j
  obtain ⟨-, hSeq, -, -, -, hslab, -, -, -, -, -, -, -, -, hdec, -⟩ := hpc
  have hjP : j ∈ C.slimPiece_ZSP35 K₃.carrier := hslab ⟨hjS, hjI⟩
  refine ⟨?_, hjP, (hSeq ▸ hjP).2, ?_⟩
  · exact C.slim_pieces_FD4 hεr hK K₃ D₃ hD hKs hKF hDreg hdD
  · by_contra hlt
    have hm : D₃.m = 0 := by omega
    have hl : D₃.l = 0 := by omega
    rw [hdec] at hjP
    rcases hjP with h | h
    · obtain ⟨k, -⟩ := mem_iUnion.mp h
      exact absurd k.2 (by omega)
    · obtain ⟨k, -⟩ := mem_iUnion.mp h
      exact absurd k.2 (by omega)

end Gaf02ChainEJA

end DifferentialGeometry.Geometry.Collapse
