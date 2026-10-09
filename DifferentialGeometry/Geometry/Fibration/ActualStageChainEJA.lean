import DifferentialGeometry.Geometry.Fibration.ActualStageChainE

/-!
# GAF01's (JA) on the chain: `Gaf02RoughDataJA` and `Gaf02ChainEJA`

Blueprint `master207B.tex`, GAF01 (`prop:fibration-actual-adjustment-choices`, B:5705–5711):
one may additionally require
`(JA)  Σ_j ≤ ε_j/10000,  c₃ < min{c_adjust, 1/1000, 1/512}`.
Review 66, D66-3: the CHOICE evidence of the SAME numeric choice travels with the chain
(`Gaf02RoughData`, BASES' ChoiceValidity, a field of `Gaf02ChainE`). That record carries
`Σ_j < ε_j/10000` (`sigma_le`) but not the `c₃`-part of (JA); the chain itself only knows
`c₃ ≤ 1/512` (`Gaf02Chain.numbers`). GAF06, GAF07 and FDC02 read `c₃ = c 2 < 1/1000`. Since the
accepted record cannot be changed, (JA) is added by a strengthening:

* `Gaf02RoughDataJA C cadj` (record, extends `Gaf02RoughData C`): ChoiceValidity plus
  `c 2 < cadj` and `c 2 < 1/1000` (the `c₃`-part of (JA) for the early target `c_adjust = cadj`).
* `Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj` (object, extends `Gaf02ChainE`): the chain on the
  enhanced planes together with the two `c₃`-inequalities of (JA). Every definition and theorem of
  `Gaf02ChainE` and of `Gaf02Chain` applies to `C.toGaf02ChainE` and `C.toChain` unchanged.
* Accessors: `Gaf02ChainEJA.roughJA_GAFC` (the record), `Gaf02ChainEJA.ja_GAFC` ((JA) verbatim),
  `Gaf02ChainEJA.c_two_lt_512_GAFC`, `Gaf02RoughDataJA.ja_GAFC`,
  `Gaf02RoughDataJA.c_two_lt_512_GAFC`.
* `Gaf02ChainE.withJA_GAFC`: a chain `Ĉ : Gaf02ChainE` together with a (JA) record on `Ĉ.toChain`
  (for instance one filled from a register's own stage data) is a `Gaf02ChainEJA` with the same
  `toGaf02ChainE` (`Gaf02ChainE.withJA_toGaf02ChainE_GAFC`, rfl).

The producer (same packet, same numeric choice, D66-2 order) is `gaf02_chainEJA_row_GAFC`
(`ActualStageChainEJARow.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

/-- **ChoiceValidity with GAF01's (JA)** (B:5705–5711): BASES' record `Gaf02RoughData C` (three
rough-graph rows, (OS), one-sheet budget, rank margin, `Σ_j < ε_j/10000`, `0 ≤ c_w`) together with
the `c₃`-part of (JA) for the early target `cadj`: `c₃ = c 2 < cadj` and `c 2 < 1/1000`. -/
structure Gaf02RoughDataJA
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw) (cadj : ℝ) : Prop
    extends Gaf02RoughData C where
  /-- (JA): `c₃ < c_adjust`. -/
  c_lt_adj : c 2 < cadj
  /-- (JA): `c₃ < 1/1000`. -/
  c_two_lt : c 2 < 1 / 1000

namespace Gaf02RoughDataJA

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
  {C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw} {cadj : ℝ}

/-- `c₃ < 1/512`, the third part of (JA). -/
theorem c_two_lt_512_GAFC (R : Gaf02RoughDataJA C cadj) : c 2 < 1 / 512 :=
  R.c_two_lt.trans (by norm_num)

/-- **(JA) verbatim** (B:5709–5711): `Σ_j ≤ ε_j/10000` for every stage and
`c₃ < min{c_adjust, 1/1000, 1/512}`. -/
theorem ja_GAFC (R : Gaf02RoughDataJA C cadj) :
    (∀ j, S j ≤ Ξ j / 10000) ∧ c 2 < min cadj (min (1 / 1000) (1 / 512)) :=
  ⟨fun j => (R.sigma_le j).le, lt_min R.c_lt_adj (lt_min R.c_two_lt R.c_two_lt_512_GAFC)⟩

end Gaf02RoughDataJA

section Object

/-- **The chain on the enhanced planes with GAF01's (JA)**: a `Gaf02ChainE` (enhanced planes,
CFS15 slots, numbers, ChoiceValidity `rough`) whose numeric choice also satisfies the `c₃`-part of
(JA) for the early target `cadj`: `c 2 < cadj` and `c 2 < 1/1000`. Produced on the same packet and
the same numeric choice by `gaf02_chainEJA_row_GAFC`. -/
structure Gaf02ChainEJA
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (Kj : ℕ) (Ξ Γ S eg c cw : Fin 3 → ℝ) (cadj : ℝ) : Type
    extends Gaf02ChainE P Kj Ξ Γ S eg c cw where
  /-- (JA): `c₃ < c_adjust`. -/
  c_lt_adj : c 2 < cadj
  /-- (JA): `c₃ < 1/1000`. -/
  c_two_lt : c 2 < 1 / 1000

end Object

namespace Gaf02ChainEJA

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ} {cadj : ℝ}

/-- **The (JA) record of the chain** (ChoiceValidity with (JA)) on its forgetful projection. -/
theorem roughJA_GAFC (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj) :
    Gaf02RoughDataJA C.toChain cadj :=
  { C.rough with c_lt_adj := C.c_lt_adj, c_two_lt := C.c_two_lt }

/-- `c₃ < 1/512` for the chain. -/
theorem c_two_lt_512_GAFC (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj) : c 2 < 1 / 512 :=
  C.roughJA_GAFC.c_two_lt_512_GAFC

/-- **(JA) verbatim for the chain**: `Σ_j ≤ ε_j/10000` and `c₃ < min{c_adjust, 1/1000, 1/512}`. -/
theorem ja_GAFC (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj) :
    (∀ j, S j ≤ Ξ j / 10000) ∧ c 2 < min cadj (min (1 / 1000) (1 / 512)) :=
  C.roughJA_GAFC.ja_GAFC

/-- `E`, `scale` and the chain are those of the underlying `Gaf02ChainE` (rfl). -/
theorem toGaf02ChainE_E_scale_GAFC (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj) :
    C.toGaf02ChainE.E = C.toChain.E ∧ C.toGaf02ChainE.scale = C.toChain.scale :=
  ⟨rfl, rfl⟩

end Gaf02ChainEJA

namespace Gaf02ChainE

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ} {cadj : ℝ}

/-- **A chain on the enhanced planes with a (JA) record on its own projection** is a
`Gaf02ChainEJA` (same `Gaf02ChainE`). -/
def withJA_GAFC (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) (R : Gaf02RoughDataJA C.toChain cadj) :
    Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj :=
  { C with c_lt_adj := R.c_lt_adj, c_two_lt := R.c_two_lt }

/-- `withJA_GAFC` keeps the chain on the enhanced planes. -/
theorem withJA_toGaf02ChainE_GAFC (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughDataJA C.toChain cadj) : (C.withJA_GAFC R).toGaf02ChainE = C :=
  rfl

end Gaf02ChainE

end DifferentialGeometry.Geometry.Collapse
