import DifferentialGeometry.Geometry.Collapse.ZeroModel.ZeroModelRowLFR52

/-!
# Consumer of rows LFR51 + LFR52: LC77 excludes the trivial surface-line rows

Lane LFR54-ROW, group G3. Frozen blueprint master207A, LFR54 proof (A:29547–29549): "LFR51
classifies that bundle. LFR52 and LC77 exclude its two trivial surface-line bundles and identify the
remaining four disk types."

`lfr52_lc77_surface_soul_twisted`: for a surface soul (oriented total space, `K ≥ 0` base metric)
whose total space is carried by `e` onto a proper metric space `N` with LC77's at-most-one-end
property, LFR51's surface clause leaves only the two twisted rows: LFR52's two-ends clause rules out
`S² × ℝ` and `T² × ℝ`. The conclusion is exactly Q0's shape (an antipodal or a Klein unit map), the
input of the disc-core dichotomy `discCore_surface_soul_types_of_unit_map_dichotomy` (LPA02).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Function Module
open scoped ContDiff Topology Manifold

namespace DifferentialGeometry.Geometry.Collapse.ZeroModel

open DifferentialGeometry.Topology DifferentialGeometry.Topology.VectorBundle
open DifferentialGeometry.Topology.Manifold

universe uB uF uV uN

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "T2" => AddCircle (1 : ℝ) × AddCircle (1 : ℝ)

variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {B : Type uB} [TopologicalSpace B] [ChartedSpace E2 B] [IsManifold (𝓡 2) ∞ B]
  {V : B → Type uV} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V (𝓡 2)]
  [IsContMDiffRiemannianBundle (𝓡 2) ∞ F V]

/-- The round sphere `S² ⊆ ℝ³` is connected. -/
theorem connectedSpace_sphereTwo : ConnectedSpace S2 :=
  isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp)) 0 zero_le_one)

/-- **LC77 + LFR52 exclude the trivial surface-line rows.** For a surface soul with an oriented
total space and a `C^n` base metric of `K ≥ 0` (`n ≥ 2`), if `e` carries the total space onto a
proper metric space in which, for every compact `K`, all unbounded components of `Kᶜ` coincide
(LC77), then the unit sphere bundle carries an antipodal unit map or a Klein unit map. -/
theorem lfr52_lc77_surface_soul_twisted [CompactSpace B] [ConnectedSpace B] [T2Space B]
    (hd : finrank ℝ (E2 × F) = 2 + 1)
    (oN : SmoothOrientation ((𝓡 2).prod 𝓘(ℝ, F)) (TotalSpace F V))
    {n : ℕ∞ω} (hn : (2 : ℕ∞ω) ≤ n)
    (k : Bundle.ContMDiffRiemannianMetric (𝓡 2) n E2 (TangentSpace (𝓡 2) : B → Type _))
    (hK : ∀ x (v w : TangentSpace (𝓡 2) x), 0 ≤ k.sectionalCurvature x v w)
    {N : Type uN} [MetricSpace N] [ProperSpace N] (e : TotalSpace F V ≃ₜ N)
    (hLC77 : ∀ K : Set N, IsCompact K → ∀ a b : N,
      ¬ Bornology.IsBounded (connectedComponentIn Kᶜ a) →
      ¬ Bornology.IsBounded (connectedComponentIn Kᶜ b) →
      connectedComponentIn Kᶜ a = connectedComponentIn Kᶜ b) :
    (∃ ν : S2 → TotalSpace F V, ContMDiff (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, F)) ∞ ν ∧
      (∀ x, ‖(ν x).2‖ = 1) ∧ Injective ν ∧
      (∀ z : TotalSpace F V, ‖z.2‖ = 1 → ∃ x, ν x = z) ∧
      (∀ x, ν (-x) = ⟨(ν x).proj, -(ν x).2⟩) ∧
      IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ (fun x => (ν x).proj)) ∨
    (∃ ν : T2 → TotalSpace F V, ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, F)) ∞ ν ∧
      (∀ p, ‖(ν p).2‖ = 1) ∧ Injective ν ∧
      (∀ z : TotalSpace F V, ‖z.2‖ = 1 → ∃ p, ν p = z) ∧
      (∀ x y : AddCircle (1 : ℝ),
        ν (x + ((1 / 2 : ℝ) : AddCircle (1 : ℝ)), -y) = ⟨(ν (x, y)).proj, -(ν (x, y)).2⟩) ∧
      IsLocalDiffeomorph (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓡 2) ∞ (fun p => (ν p).proj)) := by
  let contMetric_LFR54ROW : IsContinuousRiemannianBundle F V :=
    RankOneQuotient.isContinuousRiemannianBundle_of_contMDiff (EB := E2)
  have sphereConnected_LFR54ROW : ConnectedSpace S2 := connectedSpace_sphereTwo
  obtain ⟨-, -, hS⟩ := lfr51_oriented_finite_soul_bundle_types.{0, 0, 0, uB, uF, uV}
  obtain ⟨-, -, -, -, h5⟩ := lfr52_twisted_core_identifications_and_ends.{0, uB, uF, uV, uN, 0}
  rcases hS hd oN hn k hK with ⟨-, Ψ, hΨ, -⟩ | ⟨-, -, Ψ, hΨ, -⟩ |
      ⟨ν, hν, hνS, hνinj, hνsurj, hνneg, hνloc, -⟩ | ⟨ν, hν, hνS, hνinj, hνsurj, hνneg, hνloc, -⟩
  · exfalso
    obtain ⟨⟨K, hKc, a, b, ha, hb, hne⟩, -⟩ := h5 Ψ.toHomeomorph hΨ e
    exact hne (hLC77 K hKc a b ha hb)
  · exfalso
    obtain ⟨⟨K, hKc, a, b, ha, hb, hne⟩, -⟩ := h5 Ψ.toHomeomorph hΨ e
    exact hne (hLC77 K hKc a b ha hb)
  · exact Or.inl ⟨ν, hν, hνS, hνinj, hνsurj, hνneg, hνloc⟩
  · exact Or.inr ⟨ν, hν, hνS, hνinj, hνsurj, hνneg, hνloc⟩

end DifferentialGeometry.Geometry.Collapse.ZeroModel
