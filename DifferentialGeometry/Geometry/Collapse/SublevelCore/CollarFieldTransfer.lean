import DifferentialGeometry.Geometry.Collapse.SublevelCore.CommonFieldCore
import DifferentialGeometry.Geometry.Collapse.SublevelCore.DirectionMargin
import DifferentialGeometry.Geometry.Operator.Gradient.Regularity

/-!
# Collar-field transfer (LC48, source side)

Frozen blueprint master207A, theorem `thm:collapse-collar-field-transfer` (LC48, lines
22349–22430). On the source manifold `M` (PC Riemannian setting) let `η` be the selected radial
function: continuous, smooth on an open `W` containing the compact band `K = η⁻¹[a, b]`, with
nonvanishing gradient on `K`, and with `η - d_p` globally `ε`-Lipschitz. Let `D` be a closed core
with `{η ≤ a} ⊆ int D`, `D ⊆ {η < b}`, and let `Z` be a smooth field on an OPEN collar `Wc` of the
frontier of `D`, `p ∉ Wc`, with `|Z| ≤ B` and `g(Z, w) ≤ -α` for EVERY inward unit minimizing
direction `w` to `p` at every point of `Wc`, `ε B < α`, and strictly outward on the frontier of `D`
(local defining functions `f` with `df(Z) > 0`). Then `D` is carried onto every `{η ≤ ρ}`,
`ρ ∈ (a, b)`, by one compactly supported smooth isotopy.

Proof: LC44 (`sub_mul_le_mvfderiv_of_lipschitz_sub_dist`, W3-F5a) gives `dη(Z) ≥ α - ε B > 0` on the
collar; the band field is `∇η`; the patch and LC47 are `exists_isotopy_of_collar_field`.

In the blueprint, `D = j₀(D_N)` is the image of a model core and `Z = (j₀)_* V`; its enclosure and
the collar position come from LC39/LC41 (`transverse_core_enclosure`, W3-F5a) and the outward
clause from pushing forward a model defining function. The packet repair `j₁ = H₁ ∘ j₀` is then the
time-one map composed with `j₀`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Bundle
open scoped Manifold ContDiff Topology NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Operator

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- **LC48 (source side).** A collar field with an LC44 direction margin against all inward
minimizing directions to `p`, strictly outward on the frontier of the core, carries the core onto
every radial sublevel `{η ≤ ρ}`, `ρ ∈ (a, b)`, by one compactly supported smooth isotopy. -/
theorem exists_isotopy_of_collar_direction_margin
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g) {p : M}
    {η : M → ℝ} (hη : Continuous η) {W : Set M} (hW : IsOpen W)
    (hηW : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ η W) {a b ρ : ℝ} (hρ : ρ ∈ Ioo a b)
    (hK : IsCompact (η ⁻¹' Icc a b)) (hKW : η ⁻¹' Icc a b ⊆ W)
    (hgrad : ∀ x ∈ η ⁻¹' Icc a b,
      0 < g.inner x (gradientFun (I := I) g η x) (gradientFun (I := I) g η x))
    {ε : ℝ≥0} (hlip : LipschitzWith ε (fun x => η x - dist p x))
    {D : Set M} (hD : IsClosed D) (hAD : {x | η x ≤ a} ⊆ interior D)
    (hDb : D ⊆ {x | η x < b}) {Wc : Set M} (hWc : IsOpen Wc) (hfrWc : frontier D ⊆ Wc)
    (hpWc : p ∉ Wc) (Z : (x : M) → TangentSpace I x)
    (hZ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (fun x => (⟨x, Z x⟩ : TangentBundle I M)) Wc)
    {α B : ℝ} (hZB : ∀ x ∈ Wc, √(g.inner x (Z x) (Z x)) ≤ B)
    (hdir : ∀ x ∈ Wc, ∀ u ∈ inwardMinimizingDirections (I := I) g hEnorm p x,
      g.inner x (Z x) u ≤ -α)
    (hmargin : ε * B < α)
    (hdef : ∀ q ∈ frontier D, ∃ U : Set M, IsOpen U ∧ q ∈ U ∧ ∃ f : M → ℝ,
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U ∧ D ∩ U = {x | f x ≤ 0} ∩ U ∧
        0 < mvfderiv (I := I) f q (Z q)) :
    ∃ Hs : ℝ → Diffeomorph I I M M ∞,
      Hs 0 = Diffeomorph.refl I M ∞ ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => Hs p.1 p.2) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => (Hs p.1).symm p.2) ∧
      (∃ S : Set M, IsCompact S ∧ S ⊆ η ⁻¹' Ioo a b ∧
        ∀ t x, x ∉ S → Hs t x = x ∧ (Hs t).symm x = x) ∧
      Hs 1 '' D = {x | η x ≤ ρ} := by
  have hY₀ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x => (⟨x, gradientFun (I := I) g η x⟩ : TangentBundle I M)) W := fun x hx =>
    (gradientFun_contMDiffAt (I := I) g (hηW.contMDiffAt (hW.mem_nhds hx))).contMDiffWithinAt
  have hpos₀ : ∀ x ∈ η ⁻¹' Icc a b, 0 < mvfderiv (I := I) η x (gradientFun (I := I) g η x) :=
    fun x hx => by
      rw [← inner_gradientFun]
      exact hgrad x hx
  have hZpos : ∀ x ∈ Wc ∩ η ⁻¹' Icc a b, 0 < mvfderiv (I := I) η x (Z x) := by
    intro x hx
    have hpx : p ≠ x := fun h => hpWc (h ▸ hx.1)
    have hd : MDifferentiableAt I 𝓘(ℝ, ℝ) η x :=
      (hηW.contMDiffAt (hW.mem_nhds (hKW hx.2))).mdifferentiableAt (by norm_num)
    have h := sub_mul_le_mvfderiv_of_lipschitz_sub_dist (I := I) g hEnorm hpx hd hlip
      (hZB x hx.1) (hdir x hx.1)
    linarith
  exact exists_isotopy_of_collar_field hη hW hηW hρ hK hKW (gradientFun (I := I) g η) hY₀ hpos₀
    hD hAD hDb hWc hfrWc Z hZ hZpos hdef

end DifferentialGeometry.Geometry.Collapse
