import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.IsometryCompactness
import DifferentialGeometry.Analysis.Calculus.PiDeriv

set_option autoImplicit false

/-!
# Localized map / isometry compactness on nested Euclidean domains (MSM135 Ch4 Step B, B-loc)

MSM135 Chapter 4 Step B maps and metrics (`normalTransition`, `normalCoordMetric`,
the transition maps `J_k^{αβ}`) live only on nested Euclidean balls
`E^α ⊆ Ē^α ⊆ vec E^α`, not on all of `E`.  The F7/F8 engine
(`MapConvergence.exists_cInf_subseq`, `IsometryCompactness.isometry_seq_*`) is stated
for **total** maps: global `ContDiff ℝ ⊤` smoothness, `IsometryDerivBounds` over
**every** compact `K ⊆ E`, and a `Set.univ` conclusion.  This file is the localized
bridge requested by `STEPB_PLAN.md` PLANNER RULING Q2.

## What is delivered here

- `IsometryDerivBoundsOn U Φ` — the localized derivative-bounds predicate: uniform
  Euclidean derivative bounds on compact subsets **of an open domain `U`** only.
  `IsometryDerivBoundsOn.comp_subseq` and `IsometryDerivBounds.toOn` (a global bound
  restricts to any `U`).
- `comp_eq_id_of_cInf_on` — the localized **inverse-identity step** (`lbl374`'s
  "by symmetry").  A pure *consumer* of `C^∞`-on-compacts convergence: a compact
  neighbourhood of `Ψ_∞ x` is taken **inside** the open codomain `V`
  (`exists_compact_subset`, finite-dim `F` locally compact).
- `isometry_seq_cInf_on`, `isometry_seq_diffeo_on` — the two localized F8 producers,
  consuming the localized Arzelà–Ascoli engine.  The diffeo inverse identities are
  stated **conditionally on domain membership** (`Φ_∞ x ∈ V`, `Ψ_∞ y ∈ U`) — Step B's
  nested-ball data supplies those facts later, so no membership frontier is hidden.

The localized Arzelà–Ascoli **extraction** itself lives in `MapConvergence.lean` as
`exists_cInf_subseq_on` (planner-authorized engine addition): it bundles the order-`r`
*within* derivatives `∇ᵤʳΦₖ` as continuous maps on the metric subspace `↥U`, runs the
existing vector Arzelà–Ascoli, links the limits by differentiation on balls inside `U`,
and assembles a `HasFTaylorSeriesUpToOn ⊤` of the limit — no smooth cutoff, no
ball-to-space diffeomorphism.  See `MapConvergence.md`.
-/

namespace DifferentialGeometry
namespace HCGCompactness

open Filter Topology

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- **Localized isometry derivative bounds** (the open-domain analogue of
`IsometryDerivBounds`).  Uniform Euclidean derivative bounds for the sequence on every
compact subset of the open domain `U`, rather than on every compact subset of `E`.
This is the hypothesis the localized Arzelà–Ascoli extraction `exists_cInf_subseq_on`
(and `isometry_seq_cInf_on`) consumes. -/
def IsometryDerivBoundsOn (U : Set E) (Φ : ℕ → E → F) : Prop :=
  ∀ r : ℕ, ∀ K : Set E, IsCompact K → K ⊆ U →
    ∃ M : ℝ, ∀ k : ℕ, ∀ x ∈ K, ‖iteratedFDeriv ℝ r (Φ k) x‖ ≤ M

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- A sub-sequence still has the localized uniform derivative bounds. -/
theorem IsometryDerivBoundsOn.comp_subseq {U : Set E} {Φ : ℕ → E → F}
    (h : IsometryDerivBoundsOn U Φ) (φ : ℕ → ℕ) :
    IsometryDerivBoundsOn U (fun k => Φ (φ k)) := by
  intro r K hK hKU
  obtain ⟨M, hM⟩ := h r K hK hKU
  exact ⟨M, fun k x hx => hM (φ k) x hx⟩

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Finitely many componentwise localized derivative bounds assemble into a
localized derivative bound for the corresponding Pi-valued map. -/
theorem IsometryDerivBoundsOn.pi
    {ι : Type*} [Fintype ι] {U : Set E} {Φ : ℕ → E → (ι → F)}
    (hU : IsOpen U)
    (hsmooth : ∀ k i, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => Φ k x i) U)
    (hbdd : ∀ i, IsometryDerivBoundsOn U (fun k x => Φ k x i)) :
    IsometryDerivBoundsOn U Φ := by
  classical
  intro r K hK hKU
  choose M hM using fun i => hbdd i r K hK hKU
  refine ⟨∑ i, max (M i) 0, fun k x hx => ?_⟩
  have hr : ((r : ℕ∞) : WithTop ℕ∞) ≤
      ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast le_top
  have hcd : ∀ i, ContDiffAt ℝ ((r : ℕ∞) : WithTop ℕ∞)
      (fun y => Φ k y i) x := fun i =>
    ((hsmooth k i).contDiffAt (hU.mem_nhds (hKU hx))).of_le hr
  rw [iteratedFDeriv_pi hcd le_rfl, ContinuousMultilinearMap.opNorm_pi,
    pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => le_max_right (M i) 0)]
  intro i
  calc
    ‖iteratedFDeriv ℝ r (fun y => Φ k y i) x‖ ≤ M i := hM i k x hx
    _ ≤ max (M i) 0 := le_max_left _ _
    _ ≤ ∑ j, max (M j) 0 :=
      Finset.single_le_sum (fun j _ => le_max_right (M j) 0) (Finset.mem_univ i)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- A global all-compacts bound (`IsometryDerivBounds`) restricts to any open domain. -/
theorem IsometryDerivBounds.toOn {Φ : ℕ → E → F} (h : IsometryDerivBounds Φ)
    (U : Set E) : IsometryDerivBoundsOn U Φ :=
  fun r K hK _ => h r K hK

omit [FiniteDimensional ℝ E] in
/-- **Localized inverse-identity step** (`comp_eq_id_of_cInf` on nested open domains).
If `Φₖ → Φ_∞` in `C^∞` uniformly on compacts of an *open* `V ⊆ F`, `Ψₖ → Ψ_∞` in `C^∞`
on compacts of `U ⊆ E`, `Φ_∞` is continuous on `V`, and `Φₖ ∘ Ψₖ = id`, then
`Φ_∞ (Ψ_∞ x) = x` at every `x ∈ U` with `Ψ_∞ x ∈ V`.

The book uses this for the cocycle identity `J̄_∞^{βα} ∘ J_∞^{αβ} = id` on the inner
ball.  Unlike the global `comp_eq_id_of_cInf`, the compact neighbourhood of `Ψ_∞ x`
must be taken **inside** the open `V` (`exists_compact_subset`, finite-dimensional `F`
being locally compact); the convergence helpers already accept a general domain. -/
theorem comp_eq_id_of_cInf_on
    {U : Set E} {V : Set F}
    {Φ : ℕ → F → E} {Φinf : F → E} {Ψ : ℕ → E → F} {Ψinf : E → F}
    (hV : IsOpen V)
    (hΦ : MapCInfConvOnCompacts V Φ Φinf) (hΦc : ContinuousOn Φinf V)
    (hΨ : MapCInfConvOnCompacts U Ψ Ψinf)
    (hid : ∀ k, ∀ x' ∈ U, Φ k (Ψ k x') = x') {x : E} (hx : x ∈ U) (hΨinf : Ψinf x ∈ V) :
    Φinf (Ψinf x) = x := by
  have hΨx : Tendsto (fun k => Ψ k x) atTop (𝓝 (Ψinf x)) := tendsto_of_cInf hΨ hx
  obtain ⟨K, hKcomp, hKint, hKV⟩ := exists_compact_subset hV hΨinf
  have hKmem : K ∈ 𝓝 (Ψinf x) := mem_interior_iff_mem_nhds.mp hKint
  have hΦunif : TendstoUniformlyOn Φ Φinf atTop K :=
    tendstoUniformlyOn_of_cPConv (hΦ K hKcomp hKV 0)
  have hΨxK : Tendsto (fun k => Ψ k x) atTop (𝓝[K] (Ψinf x)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hΨx (hΨx.eventually_mem hKmem)
  have hcomp : Tendsto (fun k => Φ k (Ψ k x)) atTop (𝓝 (Φinf (Ψinf x))) :=
    hΦunif.tendsto_comp ((hΦc (Ψinf x) hΨinf).mono hKV) hΨxK
  have hidx : ∀ k, Φ k (Ψ k x) = x := fun k => hid k x hx
  simp only [hidx] at hcomp
  exact (tendsto_nhds_unique tendsto_const_nhds hcomp).symm

/-! ### Localized isometry compactness (the two F8 producers, `lbl374` on `U`) -/

/-- **Localized convergence core** of `lbl374`: from the localized derivative bounds, a
subsequence of maps that are `C^∞` on the open `U` converges in `C^∞` on compacts of
`U` to a limit `C^∞` on `U`.  Pure application of the localized Arzelà–Ascoli engine
`exists_cInf_subseq_on`. -/
theorem isometry_seq_cInf_on
    {U : Set E} (hU : IsOpen U) (Φ : ℕ → E → F)
    (hΦ : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (Φ k) U) (hbdd : IsometryDerivBoundsOn U Φ) :
    ∃ (φ : ℕ → ℕ) (Φinf : E → F),
      StrictMono φ ∧ ContDiffOn ℝ (⊤ : ℕ∞) Φinf U ∧
        MapCInfConvOnCompacts U (fun k => Φ (φ k)) Φinf :=
  exists_cInf_subseq_on hU Φ hΦ hbdd

/-- **Localized diffeomorphism compactness** (`lbl374` on nested open domains).  A
sequence of mutually inverse maps `Φₖ : U → V`, `Ψₖ : V → U` (each `C^∞` on its open
domain, both satisfying the localized isometry derivative bounds) has a subsequence
whose forward/backward limits converge in `C^∞` on compacts and are mutually inverse.

The inverse identities are stated **conditionally on domain membership** (`Φ_∞ x ∈ V`,
`Ψ_∞ y ∈ U`): the limits are only controlled on the open domains, and Step B's nested
ball data supplies those membership facts later.  Mirrors the global
`isometry_seq_diffeo`, with `comp_eq_id_of_cInf_on` for the two inverse identities. -/
theorem isometry_seq_diffeo_on
    {U : Set E} {V : Set F} (hU : IsOpen U) (hV : IsOpen V)
    (Φ : ℕ → E → F) (Ψ : ℕ → F → E)
    (hΦ : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (Φ k) U)
    (hΨ : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (Ψ k) V)
    (hbΦ : IsometryDerivBoundsOn U Φ) (hbΨ : IsometryDerivBoundsOn V Ψ)
    (hLeft : ∀ k, ∀ x ∈ U, Ψ k (Φ k x) = x) (hRight : ∀ k, ∀ y ∈ V, Φ k (Ψ k y) = y) :
    ∃ (φ : ℕ → ℕ) (Φinf : E → F) (Ψinf : F → E),
      StrictMono φ ∧ ContDiffOn ℝ (⊤ : ℕ∞) Φinf U ∧ ContDiffOn ℝ (⊤ : ℕ∞) Ψinf V ∧
        MapCInfConvOnCompacts U (fun k => Φ (φ k)) Φinf ∧
        MapCInfConvOnCompacts V (fun k => Ψ (φ k)) Ψinf ∧
        (∀ x ∈ U, Φinf x ∈ V → Ψinf (Φinf x) = x) ∧
        (∀ y ∈ V, Ψinf y ∈ U → Φinf (Ψinf y) = y) := by
  obtain ⟨φ1, Φinf, hφ1, hΦinf, hΦconv⟩ := exists_cInf_subseq_on hU Φ hΦ hbΦ
  obtain ⟨φ2, Ψinf, hφ2, hΨinf, hΨconv⟩ :=
    exists_cInf_subseq_on hV (fun k => Ψ (φ1 k)) (fun k => hΨ (φ1 k)) (hbΨ.comp_subseq φ1)
  have hΦconv' : MapCInfConvOnCompacts U (fun k => Φ (φ1 (φ2 k))) Φinf :=
    hΦconv.comp_subseq hφ2
  refine ⟨φ1 ∘ φ2, Φinf, Ψinf, hφ1.comp hφ2, hΦinf, hΨinf, hΦconv', hΨconv, ?_, ?_⟩
  · intro x hx hΦx
    exact comp_eq_id_of_cInf_on hV hΨconv hΨinf.continuousOn hΦconv'
      (fun k x' hx' => hLeft (φ1 (φ2 k)) x' hx') hx hΦx
  · intro y hy hΨy
    exact comp_eq_id_of_cInf_on hU hΦconv' hΦinf.continuousOn hΨconv
      (fun k y' hy' => hRight (φ1 (φ2 k)) y' hy') hy hΨy

end HCGCompactness
end DifferentialGeometry
