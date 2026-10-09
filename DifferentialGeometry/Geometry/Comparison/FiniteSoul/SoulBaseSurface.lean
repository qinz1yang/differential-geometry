import DifferentialGeometry.Geometry.Comparison.FiniteSoul.SoulBaseTube
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.NormalTubeApplications
import DifferentialGeometry.Topology.Manifold.SmoothApproximation.Hypersurface.OneSided
import DifferentialGeometry.Topology.Manifold.ContMDiff.OpenSubtype

/-!
# BASE-2: a smooth carrier for a compact two-dimensional `C^r` soul (lane CMS3-FLOW, G3)

Design `docs/geometrization/chapter13/design-finite-soul-three-20261004.md` §0.8, §3 "BASE", §9; frozen
statement `soulBase_surface` (`build-logs/scratch/D-CMS3/FiniteSoulThreeInterfaces.lean` §9) with the
hypothesis `(hSne : S.Nonempty)` added (external review §10, disposition D2).

**Counterexample to the frozen form without `hSne`.** Take `M = ℝ³` (flat) and `S = ∅`: `S` is compact and
vacuously an order-`r` `2`-slice, but `range b = S = ∅` forces `Shat = ∅`, while `R : M → Shat` cannot
exist since `M` is nonempty.

Route.
* Finite `r = k` (`k ≥ 2`): W-SUB's one-sided kernel `exists_smooth_hypersurface_one_sided` at order
  `n = k − 1`, fed by `exists_unitNormalCover_tube_data` (the unit-normal double cover, its tube map and
  its projection), `isCompact_unitNormalSet` and the deck lemmas; then `b = val ∘ β` and
  `R = β⁻¹ ∘ (foot projection of S3-TUBE)`. The one-sided kernel also covers two-sided `S`.
* `r = ∞`: the slice is already smooth (`IsEmbeddedSliceOfOrder I ∞ = IsEmbeddedSlice`), `Shat = S`,
  `b = val`, `R` = the corestricted foot projection (W-SUB is stated at natural orders only; review §13).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

open DifferentialGeometry.Geometry.Topology (embeddedSliceChartedSpace)

section Corestrict

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [I.Boundaryless] [IsManifold I ∞ M] in
/-- **Local smooth corestriction into a smooth embedded slice**: a map into `S` is smooth at `x` when
its composite with the inclusion is. -/
theorem contMDiffAt_embeddedSlice_of_val_tube {S : Set M} {d : ℕ}
    (hS : IsEmbeddedSlice I d S)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
    {X : Type*} [TopologicalSpace X] [ChartedSpace G X]
    (f : X → S) {x : X} (hf : ContMDiffAt J I ∞ (fun y => (f y : M)) x) :
    let _ := embeddedSliceChartedSpace hS
    ContMDiffAt J 𝓘(ℝ, Fin d → ℝ) ∞ f x := by
  intro _
  classical
  obtain ⟨W, hW, hpW, ρ, hρ, hρS, hρfix⟩ :=
    DifferentialGeometry.Topology.Manifold.SmoothHypersurface.exists_local_retraction hS (f x).2
  let Wo : TopologicalSpace.Opens M := ⟨W, hW⟩
  have hρ0 : ContMDiff I I ∞ (fun y : Wo => ρ y) :=
    hρ.comp_contMDiff contMDiff_subtype_val (fun y => y.2)
  have hρS' := DifferentialGeometry.Geometry.Topology.embeddedSlice_corestrict_contMDiff hS
    (fun y : Wo => ρ y) hρ0 (fun y => hρS y y.2)
  let κ : X → Wo := fun y => if h : (f y : M) ∈ W then ⟨f y, h⟩ else ⟨f x, hpW⟩
  have hnhds : (fun y => (f y : M)) ⁻¹' W ∈ 𝓝 x :=
    hf.continuousAt.preimage_mem_nhds (hW.mem_nhds hpW)
  have hκval : (Subtype.val ∘ κ) =ᶠ[𝓝 x] fun y => (f y : M) := by
    filter_upwards [hnhds] with y hy
    simp only [comp_apply, κ, dite_eq_left (show (f y : M) ∈ W from hy)]
  have hκ : ContMDiffAt J I ∞ κ x :=
    (DifferentialGeometry.Manifold.contMDiffAt_subtypeVal_comp_iff Wo κ x).mp
      (hf.congr_of_eventuallyEq hκval)
  have hcomp := (hρS' (κ x)).comp x hκ
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [hnhds] with y hy
  apply Subtype.ext
  simp only [comp_apply, κ, dite_eq_left (show (f y : M) ∈ W from hy)]
  exact (hρfix (f y) hy (f y).2).symm

end Corestrict

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M] [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- **BASE-2** (`2 ≤ r`, `dim = 3`; hypothesis `hSne` added by disposition D2). The base contract for a
compact nonempty two-dimensional `C^r` soul: a compact SMOOTH slice `Shat` and `b : Shat → M` of class
`C^{r−1}`, injective, onto `S`, with an ambient left inverse `R` of class `C^{r−1}` at the points of `S`. -/
theorem soulBase_surface [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hdim : Module.finrank ℝ E = 3) {S : Set M} (hSc : IsCompact S) (hSne : S.Nonempty)
    (hS : IsEmbeddedSliceOfOrder I (r : ℕ∞ω) 2 S) :
    ∃ (Shat : Set M) (hShat : IsEmbeddedSlice I 2 Shat), IsCompact Shat ∧
      let _ := embeddedSliceChartedSpace hShat
      ∃ b : Shat → M, ContMDiff 𝓘(ℝ, Fin 2 → ℝ) I ((r - 1 : ℕ∞) : ℕ∞ω) b ∧ Injective b ∧ range b = S ∧
        ∃ R : M → Shat, (∀ s, R (b s) = s) ∧
          ∀ x ∈ S, ContMDiffAt I 𝓘(ℝ, Fin 2 → ℝ) ((r - 1 : ℕ∞) : ℕ∞ω) R x := by
  classical
  obtain ⟨ε, hε, ψ, hψs, hψ, -, hψS, -, hfootc, hfoot⟩ :=
    exists_normalTube_finite_foot g hr hnorm hSc hSne hS
  have htube : IsOpen {x : M | infDist x S < ε} :=
    isOpen_lt (continuous_infDist_pt S) continuous_const
  -- the foot projection with values in `S`
  set footS : M → S := fun x =>
    if h : infDist x S < ε then ⟨(ψ x).proj, (hfoot x h).1⟩ else ⟨_, hSne.some_mem⟩ with hfootSdef
  have hfootS_eq : ∀ x (h : infDist x S < ε), footS x = ⟨(ψ x).proj, (hfoot x h).1⟩ :=
    fun x h => by
      rw [hfootSdef]
      simp only [h, ↓reduceDIte]
  have hfootS_self : ∀ s : S, footS s = s := by
    intro s
    have h0 : infDist (s : M) S < ε := by rw [infDist_zero_of_mem s.2]; exact hε
    rw [hfootS_eq _ h0]
    apply Subtype.ext
    change (ψ (s : M)).proj = s
    rw [hψS s s.2]
  have hfootS_val : ∀ x ∈ S, (fun y => ((footS y : S) : M)) =ᶠ[𝓝 x] fun y => (ψ y).proj := by
    intro x hx
    have h0 : infDist x S < ε := by rw [infDist_zero_of_mem hx]; exact hε
    filter_upwards [htube.mem_nhds h0] with y hy
    rw [hfootS_eq y hy]
  have hfootproj : ∀ x ∈ S, ContMDiffAt I I ((r - 1 : ℕ∞) : ℕ∞ω) (fun y => (ψ y).proj) x := by
    intro x hx
    have h0 : infDist x S < ε := by rw [infDist_zero_of_mem hx]; exact hε
    exact hfootc.contMDiffAt (htube.mem_nhds h0)
  induction r using ENat.recTopCoe with
  | top =>
    -- the slice is already smooth
    have hS' : IsEmbeddedSlice I 2 S := hS
    have htop : ((⊤ - 1 : ℕ∞) : ℕ∞ω) = ∞ := by simp
    refine ⟨S, hS', hSc, ?_⟩
    intro _
    refine ⟨Subtype.val, ?_, Subtype.val_injective, Subtype.range_coe, footS, hfootS_self, ?_⟩
    · rw [htop]
      exact DifferentialGeometry.Geometry.Topology.embeddedSlice_inclusion_contMDiff hS'
    · intro x hx
      rw [htop]
      refine contMDiffAt_embeddedSlice_of_val_tube hS' footS ?_
      have h := hfootproj x hx
      rw [htop] at h
      exact h.congr_of_eventuallyEq (hfootS_val x hx)
  | coe k =>
    have hk2 : 2 ≤ k := by exact_mod_cast hr
    set n : ℕ := k - 1 with hn
    have hn1 : 1 ≤ n := by omega
    have hnk : ((k : ℕ∞) - 1 : ℕ∞) = (n : ℕ∞) := by
      rw [hn]
      simp
    have hord : (((k : ℕ∞) - 1 : ℕ∞) : ℕ∞ω) = (n : ℕ∞ω) := by
      rw [hnk]
      rfl
    have hnr : (n : ℕ∞ω) ≤ ((k : ℕ∞) : ℕ∞ω) := by
      have : n ≤ k := by omega
      exact_mod_cast this
    obtain ⟨cs, ε', hε', hinj, hdata⟩ :=
      exists_unitNormalCover_tube_data g hr hnorm hSc hSne (d := 2) (by rw [hdim]) hS
    let _ := cs
    let _ := embeddedSliceChartedSpaceOfOrder hS
    obtain ⟨hloc, hπ⟩ := hdata n (le_of_eq hnk.symm)
    obtain ⟨hπs, hπf⟩ :=
      unitNormalCoverProj_surjective_and_fibres g hr (d := 2) (by rw [hdim]) hS
    have : CompactSpace (unitNormalCover g S) :=
      isCompact_iff_compactSpace.mp (isCompact_unitNormalSet g hr hnorm hSc hSne hS)
    obtain ⟨Shat, hShat, hShatc, -, hβ⟩ :=
      DifferentialGeometry.Topology.Manifold.SmoothHypersurface.exists_smooth_hypersurface_one_sided
        (I := I) (IS := 𝓘(ℝ, Fin 2 → ℝ)) (IS' := 𝓘(ℝ, Fin 2 → ℝ)) (d := 2) (by rw [hdim]) hn1
        (Φ := unitNormalTube g S) (σ := unitNormalCoverNeg g S)
        (δ := ε') hε' le_rfl hloc (continuous_unitNormalCoverNeg g S)
        (unitNormalCoverNeg_neg g S) (unitNormalTube_neg g S) hinj hπ hπs hπf
    refine ⟨Shat, hShat, hShatc, ?_⟩
    intro _
    obtain ⟨β, -⟩ := hβ
    have hval : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) I (n : ℕ∞ω) (Subtype.val : S → M) :=
      (contMDiff_val_ofOrder hS).of_le hnr
    refine ⟨fun x => (β x : M), ?_, ?_, ?_, fun x => β.symm (footS x), ?_, ?_⟩
    · rw [hord]
      exact hval.comp β.contMDiff
    · exact Subtype.val_injective.comp β.injective
    · ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact (β y).2
      · intro hx
        refine ⟨β.symm ⟨x, hx⟩, ?_⟩
        change ((β (β.symm ⟨x, hx⟩) : S) : M) = x
        rw [β.apply_symm_apply]
    · intro s
      change β.symm (footS ((β s : S) : M)) = s
      rw [hfootS_self, β.symm_apply_apply]
    · intro x hx
      rw [hord]
      have hf : ContMDiffAt I 𝓘(ℝ, Fin 2 → ℝ) (n : ℕ∞ω) footS x := by
        refine contMDiffAt_of_contMDiffAt_val_ofOrder hS hnr footS ?_
        have h := hfootproj x hx
        rw [hord] at h
        exact h.congr_of_eventuallyEq (hfootS_val x hx)
      exact β.symm.contMDiff.contMDiffAt.comp x hf

end DifferentialGeometry.Geometry.FiniteSoul
