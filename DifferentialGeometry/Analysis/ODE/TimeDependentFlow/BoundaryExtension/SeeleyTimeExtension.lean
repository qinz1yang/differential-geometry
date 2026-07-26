import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.ChartOperator.ConventionBridge
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.BorelHalfLineParam

/-!
# Smooth time-extension of a field smooth on a closed time slab

A time-dependent field `X` that is jointly `C∞` (as a tangent-bundle section) on the *closed*
time slab `Icc 0 T ×ˢ univ` is extended to a field `Xext` that is jointly `C∞` on all of
`ℝ × M` and agrees with `X` on `Icc 0 T`.  This is the Seeley/Whitney smooth-extension-across-a-
boundary statement at the level of the joint tangent-bundle section: unlike the merely-continuous
time-clamp `field_time_clamp_extension`, the extension is smooth across the slab endpoints
`t = 0` and `t = T`, so the autonomised flow field `(1, Xext)` is `C∞` on all of `ℝ × M`.

The construction is the standard Seeley reflection/extension applied in the time variable, fibre
by fibre over `M`, assembled with a partition of unity; it is proven here in full (sorry-free),
so consumers do not depend on `sorryAx` through this file.
-/

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Set Function Bundle
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Integral.Connection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

set_option linter.unusedSectionVars false in
/-- **Per-chart Euclidean joint reading of a time-dependent section.** If the joint
tangent-bundle section of a family `X` is `ContMDiffOn` on the slab `s ×ˢ univ`, then for any
chart centre `α` its chart-Euclidean reading `(t, z) ↦ chartE_section_repr α (X t) z` (the
trivialised representation of `X t` through the canonical trivialization at `α`) is
`ContMDiffOn (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,E)` on `s ×ˢ (chartAt H α).source`.

This reads the joint section through the *fixed* trivialization at `α` via
`Bundle.Trivialization.contMDiffWithinAt_iff`, then identifies the fibre coordinate with
`chartE_section_repr` on the trivialization base set
(`chartE_section_repr_eq_trivialization_snd`). -/
theorem chartE_jointReading_contMDiffOn
    (X : ℝ → ∀ x : M, TangentSpace I x) (s : Set ℝ) (α : M)
    (hX : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M))
      (s ×ˢ (univ : Set M))) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E) ∞
      (fun q : ℝ × M => chartE_section_repr (I := I) α (X q.1) q.2)
      (s ×ˢ (chartAt H α).source) := by
  set e : Trivialization E (π E (TangentSpace I : M → Type _)) :=
    trivializationAt E (TangentSpace I) α with he
  have hbase : (chartAt H α).source ⊆ e.baseSet := by
    rw [he, TangentBundle.trivializationAt_baseSet]
  have hmaps : Set.MapsTo
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M))
      (s ×ˢ (chartAt H α).source) e.source := by
    intro q hq
    rw [Trivialization.mem_source]
    exact hbase hq.2
  have hiff := e.contMDiffOn_iff (n := ∞) (IM := 𝓘(ℝ, ℝ).prod I) (IB := I)
    (f := fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M)) hmaps
  have hfib : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E) ∞
      (fun q : ℝ × M => (e (TotalSpace.mk' E q.2 (X q.1 q.2))).2)
      (s ×ˢ (chartAt H α).source) := (hiff.mp (hX.mono ?_)).2
  · refine hfib.congr ?_
    intro q hq
    have hq2 : q.2 ∈ e.baseSet := hbase hq.2
    rw [he] at hq2 ⊢
    exact chartE_section_repr_eq_trivialization_snd (I := I) α (X q.1) hq2
  · exact Set.prod_mono (subset_refl _) (subset_univ _)

set_option linter.unusedSectionVars false in
/-- **Partition-of-unity assembly of joint tangent-bundle sections.** Let `ρ` be a smooth
partition of unity on `M` (indexed by `ι`) subordinate to a family of open sets `U`. For each
index `i` let `Y i : ℝ → ∀ x, TangentSpace I x` be a time-dependent section whose joint
tangent-bundle section is `ContMDiffOn` on `univ ×ˢ U i`. Then the patched global section

  `Xext q.1 q.2 := ∑ᶠ i, ρ i q.2 • Y i q.1 q.2`

has a globally `ContMDiff` joint tangent-bundle section on `ℝ × M`.

The proof is pointwise: at `q₀ = (t₀, x₀)`, `Bundle.contMDiffAt_section` reduces to the fibre
coordinate through the trivialization at `x₀`. That coordinate is a *fixed* continuous-linear
map of the fibre on the base set, so it distributes over the (locally finite) `finsum` and the
scalars (`map_finsum`, `map_smul`), giving `∑ᶠ i, ρ i q.2 • (fibre coord of Y i)`. Each summand
is `(ρ i ∘ snd)` (a smooth scalar) times the fibre coordinate of `Y i`'s joint section, which is
smooth at `q₀` whenever `x₀ ∈ tsupport (ρ i) ⊆ U i` (the subordinacy gives `q.2 ∈ U i`); off the
support the scalar vanishes. `contMDiffAt_finsum` over the locally-finite family closes it. -/
theorem partitionOfUnity_assembled_section_contMDiff
    {ι : Type*} {ρ : SmoothPartitionOfUnity ι I M (univ : Set M)} {U : ι → Set M}
    (hsub : ρ.IsSubordinate U) (hU : ∀ i, IsOpen (U i))
    (Y : ι → ℝ → ∀ x : M, TangentSpace I x)
    (hY : ∀ i, ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (Y i q.1 q.2) : TangentBundle I M))
      ((univ : Set ℝ) ×ˢ U i)) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M =>
        (TotalSpace.mk' E q.2 (∑ᶠ i, ρ i q.2 • Y i q.1 q.2) : TangentBundle I M)) := by
  classical
  intro q₀
  rw [Bundle.contMDiffAt_totalSpace]
  refine ⟨contMDiffAt_snd, ?_⟩
  set x₀ : M := q₀.2 with hx₀
  set e := trivializationAt E (TangentSpace I) x₀ with he
  -- The locally finite family of summand fibre-coordinates, read through `e`.
  set g : ι → ℝ × M → E :=
    fun i q => e.continuousLinearMapAt ℝ q.2 (Y i q.1 q.2) with hg
  -- Each summand `(ρ i ∘ snd) • g i` is `C∞` at `q₀`.
  have hsummand : ∀ i, q₀ ∈ tsupport (fun q : ℝ × M => ρ i q.2) →
      ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E) ∞ (g i) q₀ := by
    intro i hi
    -- `q₀.2 ∈ tsupport (ρ i) ⊆ U i`, so `Y i`'s joint section is smooth near `q₀`.
    have hx₀_supp : x₀ ∈ tsupport (ρ i) := by
      have hclosed : IsClosed ((fun q : ℝ × M => q.2) ⁻¹' tsupport (ρ i)) :=
        (isClosed_tsupport (ρ i)).preimage continuous_snd
      have hsubset : tsupport (fun q : ℝ × M => ρ i q.2) ⊆
          (fun q : ℝ × M => q.2) ⁻¹' tsupport (ρ i) := by
        refine closure_minimal (fun q hq => ?_) hclosed
        simp only [Function.mem_support, Set.mem_preimage] at hq ⊢
        exact subset_tsupport _ hq
      exact hsubset hi
    have hx₀_U : x₀ ∈ U i := hsub i hx₀_supp
    have hbase : x₀ ∈ e.baseSet := by
      rw [he, TangentBundle.trivializationAt_baseSet]
      exact mem_chart_source H x₀
    -- The joint section of `Y i` is `ContMDiffAt q₀` (open `univ ×ˢ U i`).
    have hopen : IsOpen ((univ : Set ℝ) ×ˢ U i) := isOpen_univ.prod (hU i)
    have hmem : q₀ ∈ (univ : Set ℝ) ×ˢ U i := ⟨mem_univ _, hx₀_U⟩
    have hYat : ContMDiffAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
        (fun q : ℝ × M => (TotalSpace.mk' E q.2 (Y i q.1 q.2) : TangentBundle I M)) q₀ :=
      (hY i q₀ hmem).contMDiffAt (hopen.mem_nhds hmem)
    -- Read its fibre coordinate through `e`.
    have hYat' : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E) ∞
        (fun q : ℝ × M => (e (TotalSpace.mk' E q.2 (Y i q.1 q.2))).2) q₀ := by
      have hsrc : (TotalSpace.mk' E q₀.2 (Y i q₀.1 q₀.2) : TangentBundle I M) ∈ e.source := by
        rw [Trivialization.mem_source]; exact hbase
      exact ((e.contMDiffAt_iff (n := ∞) (IM := 𝓘(ℝ, ℝ).prod I) (IB := I)
        (f := fun q : ℝ × M => (TotalSpace.mk' E q.2 (Y i q.1 q.2) : TangentBundle I M))
        hsrc).mp hYat).2
    -- `(e ⟨q.2, Y i q.1 q.2⟩).2 = e.continuousLinearMapAt ℝ q.2 (Y i q.1 q.2)` near `q₀`.
    refine hYat'.congr_of_eventuallyEq ?_
    have hpre : (fun q : ℝ × M => q.2) ⁻¹' e.baseSet ∈ 𝓝 q₀ :=
      (continuous_snd.continuousAt) (e.open_baseSet.mem_nhds hbase)
    filter_upwards [hpre] with q hq
    show g i q = (e (TotalSpace.mk' E q.2 (Y i q.1 q.2))).2
    rw [← chartE_section_repr_eq_trivialization_snd (I := I) x₀ (Y i q.1) hq]
    rfl
  -- The fibre coordinate of the assembled section equals `∑ᶠ i, ρ i q.2 • g i q` near `q₀`.
  have hfib_eq : (fun q : ℝ × M =>
      (e (TotalSpace.mk' E q.2 (∑ᶠ i, ρ i q.2 • Y i q.1 q.2))).2)
      =ᶠ[𝓝 q₀] (fun q : ℝ × M => ∑ᶠ i, ρ i q.2 • g i q) := by
    have hbase : x₀ ∈ e.baseSet := by
      rw [he, TangentBundle.trivializationAt_baseSet]; exact mem_chart_source H x₀
    have hpre : (fun q : ℝ × M => q.2) ⁻¹' e.baseSet ∈ 𝓝 q₀ :=
      (continuous_snd.continuousAt) (e.open_baseSet.mem_nhds hbase)
    filter_upwards [hpre] with q hq
    have hfin : (Function.support (fun i => ρ i q.2 • Y i q.1 q.2)).Finite :=
      (ρ.locallyFinite.point_finite q.2).subset (fun i hi => by
        simp only [Function.mem_support] at hi ⊢
        exact fun h => hi (by rw [h, zero_smul]))
    change (e (TotalSpace.mk' E q.2 (∑ᶠ i, ρ i q.2 • Y i q.1 q.2))).2 = ∑ᶠ i, ρ i q.2 • g i q
    have hcl : (e (TotalSpace.mk' E q.2 (∑ᶠ i, ρ i q.2 • Y i q.1 q.2))).2
        = e.continuousLinearMapAt ℝ q.2 (∑ᶠ i, ρ i q.2 • Y i q.1 q.2) :=
      (chartE_section_repr_eq_trivialization_snd (I := I) x₀
        (fun y => ∑ᶠ i, ρ i q.2 • Y i q.1 y) hq).symm
    rw [hcl, map_finsum (g := e.continuousLinearMapAt ℝ q.2) hfin]
    refine finsum_congr fun i => ?_
    rw [map_smul]
  change ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E) ∞
    (fun q : ℝ × M => (e (TotalSpace.mk' E q.2 (∑ᶠ i, ρ i q.2 • Y i q.1 q.2))).2) q₀
  refine ContMDiffAt.congr_of_eventuallyEq ?_ hfib_eq
  -- The family `fun i q => ρ i q.2 • g i q` is locally finite (pulled back from `ρ` by `snd`).
  have hlf : LocallyFinite (fun i => Function.support (fun q : ℝ × M => ρ i q.2 • g i q)) := by
    have hpre : LocallyFinite
        (fun i => (Prod.snd : ℝ × M → M) ⁻¹' Function.support (ρ i)) :=
      ρ.locallyFinite.preimage_continuous (g := (Prod.snd : ℝ × M → M)) continuous_snd
    refine hpre.subset (fun i q hq => ?_)
    simp only [Function.mem_support, Set.mem_preimage] at hq ⊢
    exact fun h => hq (by rw [h, zero_smul])
  refine contMDiffAt_finsum hlf ?_
  intro i
  by_cases hi : q₀ ∈ tsupport (fun q : ℝ × M => ρ i q.2)
  · refine ContMDiffAt.smul ?_ (hsummand i hi)
    exact ((ρ i).contMDiff.comp contMDiff_snd).contMDiffAt
  · exact contMDiffAt_of_notMem (compl_subset_compl.mpr
      (tsupport_smul_subset_left (fun q : ℝ × M => ρ i q.2) (g i)) hi) ∞

set_option linter.unusedSectionVars false in
/-- **Euclidean joint reading of a time-dependent section over a chart.** Pulling the
manifold-level chart reading `(t, x) ↦ chartE_section_repr α (X t) x` back through the chart
inverse `(extChartAt I α).symm` gives the `E`-valued map
`g_α (t, z) := chartE_section_repr α (X t) ((extChartAt I α).symm z)`, which is jointly
`ContDiffOn ℝ ∞` on `s ×ˢ (extChartAt I α).target`. This is the Fréchet-level reading consumed by
the Borel/Seeley parametrized interval extension `borel_interval_extend_param`. -/
private theorem chartE_euclideanReading_contDiffOn
    (X : ℝ → ∀ x : M, TangentSpace I x) (s : Set ℝ) (α : M)
    (hX : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M))
      (s ×ˢ (univ : Set M))) :
    ContDiffOn ℝ ∞
      (Function.uncurry fun t (z : E) =>
        chartE_section_repr (I := I) α (X t) ((extChartAt I α).symm z))
      (s ×ˢ (extChartAt I α).target) := by
  classical
  have hread := chartE_jointReading_contMDiffOn (I := I) X s α hX
  set R : ℝ × M → E := fun q => chartE_section_repr (I := I) α (X q.1) q.2 with hR
  have hΨsymm : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) (𝓘(ℝ, ℝ).prod I) ∞
      (fun q : ℝ × E => (q.1, (extChartAt I α).symm q.2))
      (s ×ˢ (extChartAt I α).target) := by
    refine ContMDiffOn.prodMk contMDiffOn_fst ?_
    refine (contMDiffOn_extChartAt_symm (I := I) (n := ∞) α).comp contMDiffOn_snd ?_
    intro q hq; exact hq.2
  have hcomp : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun q : ℝ × E => R (q.1, (extChartAt I α).symm q.2))
      (s ×ˢ (extChartAt I α).target) := by
    refine hread.comp hΨsymm ?_
    intro q hq
    refine ⟨hq.1, ?_⟩
    change (extChartAt I α).symm q.2 ∈ (chartAt H α).source
    rw [← extChartAt_source (I := I) α]
    exact (extChartAt I α).map_target hq.2
  rw [show (Function.uncurry fun t (z : E) =>
        chartE_section_repr (I := I) α (X t) ((extChartAt I α).symm z))
      = fun q : ℝ × E => R (q.1, (extChartAt I α).symm q.2) from rfl]
  rw [← contMDiffOn_iff_contDiffOn, ← chartedSpaceSelf_prod, modelWithCornersSelf_prod]
  exact hcomp

set_option linter.unusedSectionVars false in
/-- **Local chart lift of an extended Euclidean reading.** Given an `E`-valued family
`gext : ℝ → E → E` that is jointly `ContDiffOn ℝ ∞` on `univ ×ˢ V` (`V` open in the chart
target), the lifted local section `Y t x := trivFromE α x (gext t (extChartAt I α x))` has a
joint tangent-bundle section that is `ContMDiffOn` on `univ ×ˢ W`, where
`W := (chartAt H α).source ∩ extChartAt I α ⁻¹' V`. -/
private theorem lift_extended_reading_contMDiffOn
    (α : M) (gext : ℝ → E → E) (V : Set E)
    (hgext : ContDiffOn ℝ ∞ (Function.uncurry gext) ((univ : Set ℝ) ×ˢ V)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M =>
        (TotalSpace.mk' E q.2
            ((trivFromE (I := I) α q.2) (gext q.1 (extChartAt I α q.2))) : TangentBundle I M))
      ((univ : Set ℝ) ×ˢ
        ((chartAt H α).source ∩ (extChartAt I α) ⁻¹' V)) := by
  classical
  set W : Set M := (chartAt H α).source ∩ (extChartAt I α) ⁻¹' V with hW
  set e : Trivialization E (π E (TangentSpace I : M → Type _)) :=
    trivializationAt E (TangentSpace I) α with he
  set Yfib : ℝ → ∀ x : M, TangentSpace I x :=
    fun t x => (trivFromE (I := I) α x) (gext t (extChartAt I α x)) with hYfib
  have hbase : W ⊆ e.baseSet := by
    intro x hx
    rw [he, TangentBundle.trivializationAt_baseSet]
    exact hx.1
  have hmaps : Set.MapsTo
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (Yfib q.1 q.2) : TangentBundle I M))
      ((univ : Set ℝ) ×ˢ W) e.source := by
    intro q hq
    rw [Trivialization.mem_source]
    exact hbase hq.2
  have hiff := e.contMDiffOn_iff (n := ∞) (IM := 𝓘(ℝ, ℝ).prod I) (IB := I)
    (f := fun q : ℝ × M => (TotalSpace.mk' E q.2 (Yfib q.1 q.2) : TangentBundle I M)) hmaps
  -- The Euclidean composite `(t, x) ↦ gext t (extChartAt I α x)` is `ContMDiffOn` on `univ ×ˢ W`.
  have hgextM : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (Function.uncurry gext) ((univ : Set ℝ) ×ˢ V) := by
    rw [← contMDiffOn_iff_contDiffOn, ← chartedSpaceSelf_prod, modelWithCornersSelf_prod] at hgext
    exact hgext
  have hΦ : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (q.1, extChartAt I α q.2)) ((univ : Set ℝ) ×ˢ W) := by
    refine ContMDiffOn.prodMk contMDiffOn_fst ?_
    refine (contMDiffOn_extChartAt (I := I) (n := ∞) (x := α)).comp contMDiffOn_snd ?_
    intro q hq; exact hq.2.1
  have hread : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E) ∞
      (fun q : ℝ × M => gext q.1 (extChartAt I α q.2)) ((univ : Set ℝ) ×ˢ W) := by
    have := hgextM.comp hΦ ?_
    · exact this
    · intro q hq
      exact ⟨mem_univ _, hq.2.2⟩
  refine (hiff.mpr ⟨contMDiffOn_snd, ?_⟩)
  refine hread.congr ?_
  intro q hq
  have hq2 : q.2 ∈ e.baseSet := hbase hq.2
  rw [he] at hq2
  change (e (TotalSpace.mk' E q.2 (Yfib q.1 q.2))).2 = gext q.1 (extChartAt I α q.2)
  rw [← chartE_section_repr_eq_trivialization_snd (I := I) α (Yfib q.1) hq2]
  change trivToE (I := I) α q.2 ((trivFromE (I := I) α q.2) (gext q.1 (extChartAt I α q.2)))
    = gext q.1 (extChartAt I α q.2)
  rw [trivToE_trivFromE (I := I) α hq2]

/-- **Smooth time-extension across the slab endpoints.** A field `X` whose joint tangent-bundle
section is `C∞` on the closed time slab `Icc 0 T ×ˢ univ` admits a field `Xext` whose joint
section is `C∞` on all of `ℝ × M` and which agrees with `X` on `Icc 0 T`.

The construction is the Seeley/Whitney smooth extension in the time variable, performed chart by
chart in the Euclidean reading (`chartE_euclideanReading_contDiffOn` →
`borel_interval_extend_param`), lifted back to a local tangent-bundle section over each chart
(`lift_extended_reading_contMDiffOn`), and patched globally by a smooth partition of unity
subordinate to the chart-local extension neighbourhoods
(`partitionOfUnity_assembled_section_contMDiff`). Agreement on `Icc 0 T` follows from
`∑ ρ = 1` together with each local section reproducing `X` over `[0, T]`. -/
theorem seeley_time_extend
    (X : ℝ → ∀ x : M, TangentSpace I x) (T : ℝ) (hT : 0 < T)
    (hsmooth0 : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M))
      (Set.Icc 0 T ×ˢ univ)) :
    ∃ Xext : ℝ → ∀ x : M, TangentSpace I x,
      ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
        (fun q : ℝ × M => (TotalSpace.mk' E q.2 (Xext q.1 q.2) : TangentBundle I M)) ∧
      (∀ t ∈ Set.Icc 0 T, ∀ x : M, Xext t x = X t x) := by
  classical
  -- The Euclidean chart reading of `X` at every chart centre `α`.
  set g : M → ℝ → E → E :=
    fun α t z => chartE_section_repr (I := I) α (X t) ((extChartAt I α).symm z) with hg
  have hgC : ∀ α : M, ContDiffOn ℝ ∞ (Function.uncurry (g α))
      (Set.Icc 0 T ×ˢ (extChartAt I α).target) :=
    fun α => chartE_euclideanReading_contDiffOn (I := I) X (Set.Icc 0 T) α hsmooth0
  -- For each `α`, pick a compact `K_α ⊆ target` containing `z₀ := extChartAt I α α` in its interior.
  have hz₀tgt : ∀ α : M, extChartAt I α α ∈ (extChartAt I α).target :=
    fun α => mem_extChartAt_target (I := I) α
  have hKexists : ∀ α : M, ∃ K : Set E, IsCompact K ∧ extChartAt I α α ∈ interior K ∧
      K ⊆ (extChartAt I α).target :=
    fun α => exists_compact_subset (isOpen_extChartAt_target (I := I) α) (hz₀tgt α)
  choose K hKcompact hKint hKtgt using hKexists
  -- Apply the parametrized interval extension fibrewise in the chart coordinate.
  have hborel : ∀ α : M, ∃ gext : ℝ → E → E, ∃ Vα ∈ nhds (extChartAt I α α),
      ContDiffOn ℝ ∞ (Function.uncurry gext) ((univ : Set ℝ) ×ˢ Vα) ∧
        ∀ t ∈ Set.Icc (0:ℝ) T, ∀ z ∈ Vα, gext t z = g α t z := by
    intro α
    have hgK : ContDiffOn ℝ ∞ (Function.uncurry (g α)) (Set.Icc (0:ℝ) T ×ˢ K α) :=
      (hgC α).mono (Set.prod_mono_right (hKtgt α))
    exact DifferentialGeometry.Analysis.borel_interval_extend_param (g α) T hT (K α) (hKcompact α)
      (extChartAt I α α) (hKint α) hgK
  choose gext V hVnhds hgextC hgextEq using hborel
  -- Replace each neighbourhood `V α` by an open `Vo α ⊆ V α ∩ target` containing `z₀`.
  have hVoexists : ∀ α : M, ∃ Vo : Set E, IsOpen Vo ∧ extChartAt I α α ∈ Vo ∧
      Vo ⊆ V α ∧ Vo ⊆ (extChartAt I α).target := by
    intro α
    have hmem : V α ∩ (extChartAt I α).target ∈ nhds (extChartAt I α α) :=
      Filter.inter_mem (hVnhds α) ((isOpen_extChartAt_target (I := I) α).mem_nhds (hz₀tgt α))
    obtain ⟨Vo, hVosub, hVoopen, hz₀Vo⟩ := mem_nhds_iff.1 hmem
    exact ⟨Vo, hVoopen, hz₀Vo, fun z hz => (hVosub hz).1, fun z hz => (hVosub hz).2⟩
  choose Vo hVoopen hz₀Vo hVoV hVotgt using hVoexists
  -- The open chart-local extension neighbourhoods `W α` (cover `M`: each `α ∈ W α`).
  set W : M → Set M := fun α => (chartAt H α).source ∩ (extChartAt I α) ⁻¹' Vo α with hW
  have hWopen : ∀ α : M, IsOpen (W α) := by
    intro α
    have hcont : ContinuousOn (extChartAt I α) (chartAt H α).source := by
      rw [← extChartAt_source (I := I) α]; exact continuousOn_extChartAt (I := I) α
    exact hcont.isOpen_inter_preimage (chartAt H α).open_source (hVoopen α)
  have hWmem : ∀ α : M, α ∈ W α := fun α =>
    ⟨mem_chart_source H α, by
      simp only [Set.mem_preimage]
      exact hz₀Vo α⟩
  have hWcover : (univ : Set M) ⊆ ⋃ α, W α := fun x _ => mem_iUnion_of_mem x (hWmem x)
  -- A smooth partition of unity subordinate to `{W α}`.
  obtain ⟨ρ, hρsub⟩ :=
    SmoothPartitionOfUnity.exists_isSubordinate (I := I) (M := M) (ι := M)
      isClosed_univ W hWopen hWcover
  -- The local lifted sections.
  set Y : M → ℝ → ∀ x : M, TangentSpace I x :=
    fun α t x => (trivFromE (I := I) α x) (gext α t (extChartAt I α x)) with hY
  have hYsmooth : ∀ α : M, ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (Y α q.1 q.2) : TangentBundle I M))
      ((univ : Set ℝ) ×ˢ W α) := fun α =>
    lift_extended_reading_contMDiffOn (I := I) α (gext α) (Vo α)
      ((hgextC α).mono (Set.prod_mono_right (hVoV α)))
  -- The global patched extension.
  refine ⟨fun t x => ∑ᶠ α, ρ α x • Y α t x, ?_, ?_⟩
  · exact partitionOfUnity_assembled_section_contMDiff (I := I) hρsub hWopen Y hYsmooth
  · intro t ht x
    -- On `[0, T]`, each local section reproduces `X`, weighted by `ρ` summing to `1`.
    have hYeq : ∀ α : M, x ∈ tsupport (ρ α) → ρ α x • Y α t x = ρ α x • X t x := by
      intro α hα
      have hxW : x ∈ W α := hρsub α hα
      have hxsrc : x ∈ (chartAt H α).source := hxW.1
      have hxbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
        rw [TangentBundle.trivializationAt_baseSet]; exact hxsrc
      have hxVo : extChartAt I α x ∈ Vo α := hxW.2
      have hgextval : gext α t (extChartAt I α x) = g α t (extChartAt I α x) :=
        hgextEq α t ht (extChartAt I α x) (hVoV α hxVo)
      have hsymm : (extChartAt I α).symm (extChartAt I α x) = x :=
        (extChartAt I α).left_inv (by rw [extChartAt_source]; exact hxsrc)
      have hYval : Y α t x = X t x := by
        change (trivFromE (I := I) α x) (gext α t (extChartAt I α x)) = X t x
        rw [hgextval]
        change (trivFromE (I := I) α x)
            (chartE_section_repr (I := I) α (X t) ((extChartAt I α).symm (extChartAt I α x)))
          = X t x
        rw [hsymm]
        rw [chartE_section_repr_eq_trivToE (I := I) α (X t) x]
        exact trivFromE_trivToE (I := I) α hxbase (X t x)
      rw [hYval]
    have hsum1 : ∑ᶠ α, ρ α x = 1 := ρ.sum_eq_one (mem_univ x)
    have hfin : HasFiniteSupport fun α : M => ρ α x :=
      hasFiniteSupport_of_finsum_eq_one hsum1
    calc ∑ᶠ α, ρ α x • Y α t x
        = ∑ᶠ α, ρ α x • X t x := by
          refine finsum_congr fun α => ?_
          by_cases hα : x ∈ tsupport (ρ α)
          · exact hYeq α hα
          · have : ρ α x = 0 := image_eq_zero_of_notMem_tsupport hα
            rw [this, zero_smul, zero_smul]
      _ = (∑ᶠ α, ρ α x) • X t x := (finsum_smul' hfin (X t x)).symm
      _ = X t x := by rw [hsum1, one_smul]

end DifferentialGeometry.PDE.RicciFlow.ODE
