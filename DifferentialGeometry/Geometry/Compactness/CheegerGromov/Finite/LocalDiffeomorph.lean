import DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem.Basic
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph
import DifferentialGeometry.Analysis.Calculus.MapConvergence.Basic
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# LFR14, interface I-LOCDIFF: eventual local diffeomorphisms from `C¹` chart convergence

Blueprint LFR14 (master207A.tex:25869), steps 4–5: the patched comparison maps are `C¹` close, in
fixed charts, to the identity, hence (finite-order inverse function theorem) they are `C^K` local
diffeomorphisms on every fixed compact buffer.

* `isLocalDiffeomorphAt_of_chart_fderiv_near_id`: pointwise kernel. If `σ` and `d` are order-`K`
  partial diffeomorphisms, `F` is `C^K` near `σ x`, `F (σ x)` lies in the target of `d`, and the
  chart representation `c = d⁻¹ ∘ F ∘ σ` satisfies `‖D(c - id)(x)‖ < 1`, then `F` is a `C^K`
  local diffeomorphism at `σ x`.
* `eventually_isLocalDiffeomorphOn_of_chart_convergence`: the frozen interface I-LOCDIFF of
  `build-logs/scratch/D-LFR14/Interfaces.lean:244`, without the hypothesis `IsCompact L`, which
  the argument does not use (the uniformity in `i` is part of `MapCPConvergenceOn`), and without the
  instances `IsManifold 𝓘(ℝ, E) K X`, `IsManifold 𝓘(ℝ, E) K (Y i)`, which are not needed either
  (the inverse function theorem is applied on the model space `E`). The verbatim frozen statement
  is recorded as an `example` at the end of the file.

The finite-order inverse function theorem on manifolds is
`DifferentialGeometry.Coordinates.contMDiffAt_isLocalDiffeomorphAt_of_mfderiv`
(Topology/Manifold/InverseFunctionTheorem/Basic.lean); the infinite-order analogue of this
argument is `Topology/Manifold/InverseFunction/ContDiffOn.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A map `E → E` that is `C^K` at `x` (`1 ≤ K`) and whose derivative is within distance `< 1`
of the identity is a `C^K` local diffeomorphism at `x`. -/
theorem isLocalDiffeomorphAt_of_norm_fderiv_sub_id_lt {K : ℕ} (hK : 1 ≤ K) {c : E → E}
    {x : E} (hc : ContDiffAt ℝ K c x)
    (hnorm : ‖fderiv ℝ (fun y => c y - y) x‖ < 1) :
    IsLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) K c x := by
  have hK' : (1 : ℕ∞ω) ≤ (K : ℕ∞ω) := by exact_mod_cast hK
  have hdiff : DifferentiableAt ℝ c x :=
    hc.differentiableAt (by exact_mod_cast Nat.one_le_iff_ne_zero.mp hK)
  have hsub : fderiv ℝ (fun y => c y - y) x = fderiv ℝ c x - ContinuousLinearMap.id ℝ E :=
    (hdiff.hasFDerivAt.sub (hasFDerivAt_id x)).fderiv
  have hinv : (fderiv ℝ c x).IsInvertible := by
    apply DifferentialGeometry.Coordinates.isInvertible_of_norm_id_sub_lt
    rw [norm_sub_rev, ← hsub]
    exact hnorm
  have hm : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c x).IsInvertible := by
    rw [mfderiv_eq_fderiv]
    exact hinv
  exact DifferentialGeometry.Coordinates.contMDiffAt_isLocalDiffeomorphAt_of_mfderiv hK'
    (by exact_mod_cast ENat.natCast_ne_top K)
    (contMDiffAt_iff_contDiffAt.mpr hc) hm

section Pointwise

variable {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace E Y]

/-- **Pointwise kernel of I-LOCDIFF.** Let `σ : E ⇀ X` and `d : E ⇀ Y` be order-`K` partial
diffeomorphisms and let `F : X → Y` be `C^K` on an open `W`. If `x ∈ σ.source`, `σ x ∈ W`,
`F (σ x) ∈ d.target` and the chart representation `d⁻¹ ∘ F ∘ σ` has derivative within distance
`< 1` of the identity at `x`, then `F` is a `C^K` local diffeomorphism at `σ x`. -/
theorem isLocalDiffeomorphAt_of_chart_fderiv_near_id {K : ℕ} (hK : 1 ≤ K)
    (σ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E X K)
    (d : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E Y K)
    {F : X → Y} {W : Set X} (hW : IsOpen W) (hF : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) K F W)
    {x : E} (hxσ : x ∈ σ.source) (hxW : σ x ∈ W) (hxd : F (σ x) ∈ d.target)
    (hnorm : ‖fderiv ℝ (fun y => d.symm (F (σ y)) - y) x‖ < 1) :
    IsLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) K F (σ x) := by
  let c : E → E := fun y => d.symm (F (σ y))
  -- `c` is `C^K` at `x`
  have hFσ : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) K F (σ x) := hF.contMDiffAt (hW.mem_nhds hxW)
  have hσ : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) K σ x :=
    σ.contMDiffOn.contMDiffAt (σ.open_source.mem_nhds hxσ)
  have hds : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) K d.symm (F (σ x)) :=
    d.symm.contMDiffOn.contMDiffAt (d.open_target.mem_nhds hxd)
  have hcm : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) K c x := hds.comp x (hFσ.comp x hσ)
  have hcloc : IsLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) K c x :=
    isLocalDiffeomorphAt_of_norm_fderiv_sub_id_lt hK (contMDiffAt_iff_contDiffAt.mp hcm) hnorm
  -- compose with the charts
  have hσt : σ x ∈ σ.target := σ.map_source hxσ
  have hσinv : σ.symm (σ x) = x := σ.left_inv hxσ
  have hσs : IsLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) K σ.symm (σ x) :=
    σ.symm.isLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) K hσt
  have hc' : IsLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) K c (σ.symm (σ x)) := by
    rw [hσinv]
    exact hcloc
  have hdx : c (σ.symm (σ x)) ∈ d.source := by
    rw [hσinv]
    exact d.map_target hxd
  have hdloc : IsLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) K d (c (σ.symm (σ x))) :=
    d.isLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) K hdx
  have hcomp : IsLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) K (d ∘ (c ∘ σ.symm)) (σ x) :=
    (hσs.comp 𝓘(ℝ, E) E hc').comp 𝓘(ℝ, E) Y hdloc
  -- `F` agrees with the composite near `σ x`
  have hFc : ContinuousAt F (σ x) := hFσ.continuousAt
  have hev : F =ᶠ[𝓝 (σ x)] d ∘ (c ∘ σ.symm) := by
    filter_upwards [σ.open_target.mem_nhds hσt,
      hFc.preimage_mem_nhds (d.open_target.mem_nhds hxd)] with y hy hyd
    have hy' : σ (σ.symm y) = y := σ.right_inv hy
    change F y = d (d.symm (F (σ (σ.symm y))))
    rw [hy']
    exact (d.right_inv hyd).symm
  exact DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq hev hcomp

end Pointwise

/-- **I-LOCDIFF (LFR14 steps 4–5).** If the chart representation `(d i)⁻¹ ∘ Fᵢ ∘ σ` of `C^K`
maps converges to the identity in `C¹` on `L ⊆ σ.source ∩ σ⁻¹ W`, then eventually every `Fᵢ` is a
`C^K` local diffeomorphism at every point of `σ '' L`. (Frozen interface without the unused
compactness of `L` and the unused `IsManifold` instances.) -/
theorem eventually_isLocalDiffeomorphOn_of_chart_convergence
    {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
    {K : ℕ} (hK : 1 ≤ K)
    {Y : ℕ → Type*} [∀ i, TopologicalSpace (Y i)] [∀ i, ChartedSpace E (Y i)]
    (σ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E X K)
    (d : ∀ i, PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E (Y i) K)
    (F : ∀ i, X → Y i) {W : Set X} (hW : IsOpen W)
    (hF : ∀ i, ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) K (F i) W)
    {L : Set E} (hLW : L ⊆ σ.source ∩ σ ⁻¹' W)
    (hcap : ∀ᶠ i in atTop, MapsTo (F i ∘ σ) L (d i).target)
    (hcoord : MapCPConvergenceOn L 1 (fun i x => (d i).symm (F i (σ x))) id) :
    ∀ᶠ i in atTop, IsLocalDiffeomorphOn 𝓘(ℝ, E) 𝓘(ℝ, E) K (F i) (σ '' L) := by
  obtain ⟨k0, hk0⟩ := hcoord (1 / 2) (by norm_num)
  filter_upwards [hcap, eventually_ge_atTop k0] with i hcapi hi
  rintro ⟨_, x, hxL, rfl⟩
  have hb := hk0 i hi 1 le_rfl x hxL
  rw [mapDerivNorm, norm_iteratedFDeriv_one] at hb
  exact isLocalDiffeomorphAt_of_chart_fderiv_near_id hK σ (d i) hW (hF i) (hLW hxL).1
    (hLW hxL).2 (hcapi hxL) (lt_of_le_of_lt hb (by norm_num))

/-- Consumer: under the hypotheses of I-LOCDIFF, eventually every `Fᵢ` has invertible manifold
derivative at every point of `σ '' L` (the input of the orientation clause of LFR14). -/
theorem eventually_isInvertible_mfderiv_of_chart_convergence
    {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
    {K : ℕ} (hK : 1 ≤ K)
    {Y : ℕ → Type*} [∀ i, TopologicalSpace (Y i)] [∀ i, ChartedSpace E (Y i)]
    (σ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E X K)
    (d : ∀ i, PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E (Y i) K)
    (F : ∀ i, X → Y i) {W : Set X} (hW : IsOpen W)
    (hF : ∀ i, ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) K (F i) W)
    {L : Set E} (hLW : L ⊆ σ.source ∩ σ ⁻¹' W)
    (hcap : ∀ᶠ i in atTop, MapsTo (F i ∘ σ) L (d i).target)
    (hcoord : MapCPConvergenceOn L 1 (fun i x => (d i).symm (F i (σ x))) id) :
    ∀ᶠ i in atTop, ∀ y ∈ σ '' L, (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (F i) y).IsInvertible := by
  filter_upwards [eventually_isLocalDiffeomorphOn_of_chart_convergence hK σ d F hW hF hLW hcap
    hcoord] with i hi y hy
  exact (hi ⟨y, hy⟩).isInvertible_mfderiv (by exact_mod_cast Nat.one_le_iff_ne_zero.mp hK)

/-- The verbatim frozen statement I-LOCDIFF (`Interfaces.lean:244`), with `hL`. -/
example
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
    {K : ℕ} (hK : 1 ≤ K) [IsManifold 𝓘(ℝ, E) K X]
    {Y : ℕ → Type*} [∀ i, TopologicalSpace (Y i)] [∀ i, ChartedSpace E (Y i)]
    [∀ i, IsManifold 𝓘(ℝ, E) K (Y i)]
    (σ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E X K)
    (d : ∀ i, PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E (Y i) K)
    (F : ∀ i, X → Y i) {W : Set X} (hW : IsOpen W)
    (hF : ∀ i, ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) K (F i) W)
    {L : Set E} (_hL : IsCompact L) (hLW : L ⊆ σ.source ∩ σ ⁻¹' W)
    (hcap : ∀ᶠ i in atTop, MapsTo (F i ∘ σ) L (d i).target)
    (hcoord : MapCPConvergenceOn L 1 (fun i x => (d i).symm (F i (σ x))) id) :
    ∀ᶠ i in atTop, IsLocalDiffeomorphOn 𝓘(ℝ, E) 𝓘(ℝ, E) K (F i) (σ '' L) := by
  exact eventually_isLocalDiffeomorphOn_of_chart_convergence hK σ d F hW hF hLW hcap hcoord

end DifferentialGeometry.CheegerGromovCompactness
