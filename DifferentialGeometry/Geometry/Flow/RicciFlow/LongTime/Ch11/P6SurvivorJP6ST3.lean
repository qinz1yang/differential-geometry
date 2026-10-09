import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6TerminalComparisonP6ST3
import DifferentialGeometry.Topology.Manifold.OpenSubtypeDiffeomorph

/-!
# S-c P-J：survivor identification 复合到 `P.Carrier`（O-CH11-STAB3 G2，后缀 `_P6ST3`）

树内 `RegularCrossing.exists_survivor_partialDiffeomorph` 给的是 `F : Ω ⇢ Q`（`Ω := terminalRegularOpen`，
`F.source = {x | x.val ∈ interior (val '' old)}`、`F p = q`、`F*g⁺ = ḡ`）。STAB2 合同要
`J : PartialDiffeomorph P.Carrier Q.Carrier`。本文件取 `J := iΩ.symm ≫ F`（`iΩ` = open subtype 的
partial diffeomorph），证明（`exists_survivorJ_P6ST3`）：
* `J.source = interior (val '' E.old)`（surviving open domain，`P.Carrier` 中开集；`val '' old ⊆ Ω`）；
* `J p = q`；`J.source` 上每点 `RegularCrossing x (J x)`；
* **`g⁻ = J*g⁺`**：`x ∈ J.source` ⇒ `g⁺(J x)(dJ v, dJ w) = ḡ(x)(v, w)`（`J ∘ val = F` 于 `Ω`，
  `mfderiv_restrict_open`）。
合成（`nonempty_footprintData_of_crossing_P6ST3`）：`RegularCrossing p q` +
紧集 `U ⊆ K ⊆ interior (val '' old)` + 合同数值字段 + `Q_pos` + `footprint` ⇒
`Nonempty (BufferedFootprintData_P6ST2 …)`；`J`、`U_sub`、`comparison`、`scalar_tendsto`、
`gradient_tendsto` 全部生产（G1 + 本文件）。剩 `footprint` = G3（P-F）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace MetricCutCapEvent

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ}

/-- old core 的像落在 terminal regular region 内（`oldTerminal`）。 -/
theorem image_old_subset_terminalRegularOpen_P6ST3 (E : MetricCutCapEvent P Q a s) :
    Subtype.val '' E.old ⊆ (E.incoming.terminalRegularOpen : Set P.Carrier) := by
  rintro _ ⟨z, hz, rfl⟩
  exact E.oldTerminal_eq ⟨z, hz⟩ ▸ (E.oldTerminal ⟨z, hz⟩).property

/-- **P-J**：`RegularCrossing p q` ⇒ `P.Carrier` 层 surviving identification `J`：
`J.source = interior (val '' old)`、`J p = q`、source 上 crossing、`g⁻ = J*g⁺`（以 terminal limit `ḡ`）。 -/
theorem exists_survivorJ_P6ST3 (E : MetricCutCapEvent P Q a s) {p : P.Carrier} {q : Q.Carrier}
    (hcross : E.RegularCrossing p q) :
    ∃ J : PartialDiffeomorph ThreeModel ThreeModel P.Carrier Q.Carrier ∞,
      J.source = interior (Subtype.val '' E.old) ∧ J p = q ∧
      (∀ x ∈ J.source, E.RegularCrossing x (J x)) ∧
      ∀ (x : P.Carrier) (hx : x ∈ E.incoming.terminalRegularOpen), x ∈ J.source →
        ∀ v w : TangentSpace ThreeModel x,
          E.outputMetric.inner (J x) (mfderiv ThreeModel ThreeModel J x v)
            (mfderiv ThreeModel ThreeModel J x w) = E.terminal.metric.inner ⟨x, hx⟩ v w := by
  have hp : p ∈ E.incoming.terminalRegularOpen := hcross.mem_terminalRegularRegion E
  obtain ⟨F, hsrc, -, hFp, -, hcrossF, hmetric⟩ :=
    RegularCrossing.exists_survivor_partialDiffeomorph E (p := ⟨p, hp⟩) hcross
  let iΩ := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph ThreeModel
    E.incoming.terminalRegularOpen ⟨⟨p, hp⟩⟩
  let J := iΩ.symm.trans F
  have hsymm (x : P.Carrier) (hx : x ∈ E.incoming.terminalRegularOpen) :
      iΩ.symm x = ⟨x, hx⟩ :=
    DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_symm_apply _ _ _ hx
  have happ (x : P.Carrier) (hx : x ∈ E.incoming.terminalRegularOpen) :
      J x = F ⟨x, hx⟩ := by
    change F (iΩ.symm x) = F ⟨x, hx⟩
    rw [hsymm x hx]
  have hmem (x : P.Carrier) : x ∈ J.source ↔
      ∃ hx : x ∈ E.incoming.terminalRegularOpen,
        (⟨x, hx⟩ : E.incoming.terminalRegularOpen) ∈ F.source := by
    change (x ∈ iΩ.target ∧ iΩ.symm x ∈ F.source) ↔ _
    rw [DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target]
    constructor
    · rintro ⟨hx, hxF⟩
      exact ⟨hx, hsymm x hx ▸ hxF⟩
    · rintro ⟨hx, hxF⟩
      exact ⟨hx, (hsymm x hx).symm ▸ hxF⟩
  have hJsrc : J.source = interior (Subtype.val '' E.old) := by
    ext x
    rw [hmem]
    constructor
    · rintro ⟨hx, hxF⟩
      rw [hsrc] at hxF
      exact hxF
    · intro hx
      refine ⟨E.image_old_subset_terminalRegularOpen_P6ST3 (interior_subset hx), ?_⟩
      rw [hsrc]
      exact hx
  refine ⟨J, hJsrc, (happ p hp).trans hFp, ?_, ?_⟩
  · intro x hxJ
    obtain ⟨hx, hxF⟩ := (hmem x).mp hxJ
    rw [happ x hx]
    exact hcrossF _ hxF
  · intro x hx hxJ v w
    obtain ⟨hx', hxF⟩ := (hmem x).mp hxJ
    have hfun : (fun y : E.incoming.terminalRegularOpen => J y) =
        (F : E.incoming.terminalRegularOpen → Q.Carrier) :=
      funext fun y => happ y.val y.property
    have hres := DifferentialGeometry.mfderiv_restrict_open (I := ThreeModel) (J := ThreeModel)
      (J : P.Carrier → Q.Carrier) E.incoming.terminalRegularOpen ⟨x, hx⟩
    rw [hfun] at hres
    have hd : mfderiv ThreeModel ThreeModel (J : P.Carrier → Q.Carrier) x =
        mfderiv ThreeModel ThreeModel (F : E.incoming.terminalRegularOpen → Q.Carrier) ⟨x, hx⟩ :=
      hres.symm
    rw [hd, happ x hx]
    exact hmetric ⟨x, hx'⟩ hxF v w

/-- **P-J + P-C + P-S 合成**：`RegularCrossing p q` + 紧集 `U ⊆ K ⊆ interior (val '' old)` + 合同数值字段 +
`Q_pos` + `footprint` ⇒ STAB2 合同 `BufferedFootprintData_P6ST2`（`J` 取 `exists_survivorJ_P6ST3`）。 -/
theorem nonempty_footprintData_of_crossing_P6ST3 {E : MetricCutCapEvent P Q a s} {p : P.Carrier}
    {q : Q.Carrier} {ηout C1 C2 m : ℝ} {k : ℕ} (hη : ηout < 1 / 11) (hC1 : 1 ≤ C1)
    (hC2 : 1 ≤ C2) (hm0 : 0 < m) (hm1 : m ≤ 1 / 2) (hk : max 2 ⌈ηout⁻¹⌉₊ ≤ k)
    (hcross : E.RegularCrossing p q) (U : Opens P.Carrier) {K : Set P.Carrier}
    (hK : IsCompact K) (hUK : (U : Set P.Carrier) ⊆ K)
    (hKold : K ⊆ interior (Subtype.val '' E.old))
    (v : ℕ → ℝ) (hv : ∀ n, v n ∈ Ioo a s) (hvt : Tendsto v atTop (𝓝 s))
    (hQ : 0 < metricScalarAt E.outputMetric q)
    (hfoot : ∀ᶠ n in atTop,
      riemannianClosedBallOf (I := I3) (E.incoming.flow.base.metric (v n)) p
        ((8 * C1 + 3 * ((ηout / 2)⁻¹ + 7) * Real.sqrt C2) /
          Real.sqrt (metricScalarAt (E.incoming.flow.base.metric (v n)) p)) ⊆ U) :
    Nonempty (E.BufferedFootprintData_P6ST2 p q ηout C1 C2 m k) := by
  obtain ⟨J, hJsrc, hJ, -, hiso⟩ := E.exists_survivorJ_P6ST3 hcross
  have hKJ : K ⊆ J.source := hJsrc ▸ hKold
  have hKΩ : K ⊆ E.incoming.terminalRegularOpen :=
    hKold.trans (interior_subset.trans E.image_old_subset_terminalRegularOpen_P6ST3)
  exact ⟨BufferedFootprintData_P6ST2.ofTerminal_P6ST3 hη hC1 hC2 hm0 hm1 hk hcross J hJ U hK
    hUK hKJ hKΩ (fun x hx hxK => hiso x hx (hKJ hxK)) v hv hvt hQ hfoot⟩

end MetricCutCapEvent

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
