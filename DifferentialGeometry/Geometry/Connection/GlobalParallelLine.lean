import DifferentialGeometry.Geometry.Connection.ParallelLine
import Mathlib.Topology.Homotopy.Lifting

set_option autoImplicit false

noncomputable section

open Bundle Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Connection

universe uE uH uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [T2Space M]

attribute [local instance] DifferentialGeometry.seminormedAddCommGroupTangentSpace
attribute [local instance] DifferentialGeometry.normedAddCommGroupTangentSpace
attribute [local instance] DifferentialGeometry.normedSpaceTangentSpace

local instance unitLineTangentT2Space (x : M) : T2Space (TangentSpace I x) :=
  FiberBundle.t2Space E (TangentSpace I) x

local instance unitLineTangentFiberBundle :
    FiberBundle E (TangentSpace I : M → Type _) :=
  TangentSpace.fiberBundle (I := I) (M := M)

local instance unitLineTangentVectorBundle :
    VectorBundle ℝ E (TangentSpace I : M → Type _) :=
  TangentSpace.vectorBundle (I := I) (M := M)

local instance unitLineTangentSmoothVectorBundle :
    ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I := by
  have h : IsManifold I ∞ M := inferInstance
  have : IsManifold I (∞ + 1) M := h
  exact TangentBundle.contMDiffVectorBundle (I := I) (M := M)

private abbrev unitLine
    (g : SmoothRiemannianMetric I M)
    (S : ContMDiffVectorSubbundle
      (I := I) (F := E) (V := (TangentSpace I : M → Type _))
      (n := (∞ : WithTop ℕ∞))) :=
  {p : TangentBundle I M // (p.2 ∈ S.fiber p.1) ∧ g.inner p.1 p.2 p.2 = 1}

private def unitLineProj
    (g : SmoothRiemannianMetric I M)
    (S : ContMDiffVectorSubbundle
      (I := I) (F := E) (V := (TangentSpace I : M → Type _))
      (n := (∞ : WithTop ℕ∞))) :
    unitLine g S → M := fun p => p.1.1

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
private theorem unitLine_eq_or_eq_neg
    (g : SmoothRiemannianMetric I M)
    (S : ContMDiffVectorSubbundle
      (I := I) (F := E) (V := (TangentSpace I : M → Type _))
      (n := (∞ : WithTop ℕ∞)))
    (hSrank : S.rank = 1) {U : Set M}
    (s : Cₛ^∞⟮I; E, TangentSpace I⟯)
    (hsmem : ∀ y ∈ U, s y ∈ S.fiber y)
    (hsunit : ∀ y ∈ U, g.inner y (s y) (s y) = 1)
    (p : unitLine g S) (hpU : unitLineProj g S p ∈ U) :
    p.1.2 = s p.1.1 ∨ p.1.2 = -s p.1.1 := by
  have hsne : s p.1.1 ≠ 0 := by
    intro hs
    have h := hsunit p.1.1 hpU
    rw [hs] at h
    simp at h
  have hfin : Module.finrank ℝ (S.fiber p.1.1) = 1 := by
    rw [S.finrank_fiber, hSrank]
  have hspan : S.fiber p.1.1 = ℝ ∙ s p.1.1 :=
    eq_span_singleton_of_mem_of_finrank_eq_one hfin (hsmem p.1.1 hpU) hsne
  have hp_mem := p.2.1
  rw [hspan, Submodule.mem_span_singleton] at hp_mem
  obtain ⟨c, hc⟩ := hp_mem
  have hc_sq : c ^ 2 = 1 := by
    have hpunit := p.2.2
    rw [← hc] at hpunit
    simp only [map_smul, smul_apply, smul_eq_mul, hsunit p.1.1 hpU] at hpunit
    nlinarith
  rcases sq_eq_one_iff.mp hc_sq with hc1 | hc1
  · exact Or.inl (by simpa [hc1] using hc.symm)
  · exact Or.inr (by simpa [hc1] using hc.symm)

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
private theorem continuous_unitLineProj
    (g : SmoothRiemannianMetric I M)
    (S : ContMDiffVectorSubbundle
      (I := I) (F := E) (V := (TangentSpace I : M → Type _))
      (n := (∞ : WithTop ℕ∞))) :
    Continuous (unitLineProj g S) :=
  (FiberBundle.continuous_proj E (TangentSpace I : M → Type _)).comp continuous_subtype_val

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
private theorem continuous_unitLinePairing
    (g : SmoothRiemannianMetric I M)
    (S : ContMDiffVectorSubbundle
      (I := I) (F := E) (V := (TangentSpace I : M → Type _))
      (n := (∞ : WithTop ℕ∞)))
    (s : Cₛ^∞⟮I; E, TangentSpace I⟯) :
    Continuous (fun p : unitLine g S => g.inner p.1.1 p.1.2 (s p.1.1)) := by
  have hg : Continuous (fun p : unitLine g S =>
      TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
        p.1.1 (g.inner p.1.1)) :=
    g.contMDiff.continuous.comp (continuous_unitLineProj g S)
  have hv : Continuous (fun p : unitLine g S =>
      TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) p.1.1 p.1.2) := by
    exact (continuous_subtype_val : Continuous (fun p : unitLine g S => p.1))
  have hs : Continuous (fun p : unitLine g S =>
      TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) p.1.1 (s p.1.1)) :=
    s.contMDiff.continuous.comp (continuous_unitLineProj g S)
  have htotal := Continuous.clm_bundle_apply₂
    (𝕜 := ℝ) (B := M) (F₁ := E) (F₂ := E) (F₃ := ℝ)
    (E₃ := fun _ : M => ℝ) (b := unitLineProj g S) hg hv hs
  have hproj : Continuous (fun p : TotalSpace ℝ (fun _ : M => ℝ) => p.2) :=
    continuous_snd.comp ((Bundle.Trivial.homeomorphProd M ℝ).continuous)
  exact hproj.comp htotal

private theorem unitLine_isEvenlyCovered
    (g : SmoothRiemannianMetric I M)
    (S : ContMDiffVectorSubbundle
      (I := I) (F := E) (V := (TangentSpace I : M → Type _))
      (n := (∞ : WithTop ℕ∞)))
    (hSrank : S.rank = 1)
    (hS : IsCovariantlyInvariantSubmoduleFamily (LeviCivita (I := I) g) S.fiber)
    (x : M) :
    IsEvenlyCovered (unitLineProj g S) x Bool := by
  obtain ⟨U, s, hUopen, hxU, hsmem, hsunit, hsparallel⟩ :=
    ContMDiffVectorSubbundle.exists_local_parallel_unit_section_of_rank_eq_one_of_covariantly_invariant
      g S hSrank hS x
  let a : unitLine g S → ℝ := fun p => g.inner p.1.1 p.1.2 (s p.1.1)
  let sign : unitLine g S → Bool := fun p => if 0 < a p then true else false
  have ha : Continuous a := continuous_unitLinePairing g S s
  have hsign : Continuous (fun p : (unitLineProj g S) ⁻¹' U => sign p.1) := by
    rw [continuous_bool_rng true]
    have hpre : (fun p : (unitLineProj g S) ⁻¹' U => sign p.1) ⁻¹' {true} =
        (fun p : (unitLineProj g S) ⁻¹' U => a p.1) ⁻¹' {1} := by
      ext p
      obtain hp | hp := unitLine_eq_or_eq_neg g S hSrank s hsmem hsunit p.1 p.2
      · have haeq : a p.1 = 1 := by
          simp [a, hp, hsunit p.1.1.1 p.2]
        change ((if 0 < a p.1 then true else false) = true ↔ a p.1 = 1)
        rw [haeq]
        norm_num
      · have haeq : a p.1 = -1 := by
          simp [a, hp, hsunit p.1.1.1 p.2]
        change ((if 0 < a p.1 then true else false) = true ↔ a p.1 = 1)
        rw [haeq]
        norm_num
    rw [hpre]
    have haU : Continuous (fun p : (unitLineProj g S) ⁻¹' U => a p.1) :=
      ha.comp continuous_subtype_val
    have hsame :
        (fun p : (unitLineProj g S) ⁻¹' U => a p.1) ⁻¹' {1} =
          (fun p : (unitLineProj g S) ⁻¹' U => a p.1) ⁻¹' Set.Ioi 0 := by
      ext p
      obtain hp | hp := unitLine_eq_or_eq_neg g S hSrank s hsmem hsunit p.1 p.2
      · have haeq : a p.1 = 1 := by
          simp [a, hp, hsunit p.1.1.1 p.2]
        change (a p.1 = 1 ↔ 0 < a p.1)
        rw [haeq]
        norm_num
      · have haeq : a p.1 = -1 := by
          simp [a, hp, hsunit p.1.1.1 p.2]
        change (a p.1 = 1 ↔ 0 < a p.1)
        rw [haeq]
        norm_num
    refine ⟨isClosed_singleton.preimage haU, ?_⟩
    rw [hsame]
    exact isOpen_Ioi.preimage haU
  let inv : U × Bool → (unitLineProj g S) ⁻¹' U := fun p =>
      ⟨⟨⟨p.1.1, match p.2 with
          | false => -s p.1.1
          | true => s p.1.1⟩, by
          constructor
          · cases p.2
            · exact (S.fiber p.1.1).neg_mem (hsmem p.1.1 p.1.2)
            · exact hsmem p.1.1 p.1.2
          · cases p.2
            · simpa using hsunit p.1.1 p.1.2
            · exact hsunit p.1.1 p.1.2⟩,
        p.1.2⟩
  have hinv : Continuous inv := by
    rw [continuous_prod_of_discrete_right]
    intro b
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    cases b with
    | false =>
        change Continuous (fun y : U =>
          (⟨y.1, -s y.1⟩ : TangentBundle I M))
        exact (-s).contMDiff.continuous.comp
          (continuous_subtype_val : Continuous (fun p : U => p.1))
    | true =>
        change Continuous (fun y : U =>
          (⟨y.1, s y.1⟩ : TangentBundle I M))
        exact s.contMDiff.continuous.comp
          (continuous_subtype_val : Continuous (fun p : U => p.1))
  let e : (unitLineProj g S) ⁻¹' U ≃ₜ U × Bool :=
    { toFun := fun p => (⟨unitLineProj g S p.1, p.2⟩, sign p.1)
      invFun := inv
      left_inv := by
        intro p
        apply Subtype.ext
        apply Subtype.ext
        apply TotalSpace.ext
        · rfl
        · obtain hp | hp := unitLine_eq_or_eq_neg g S hSrank s hsmem hsunit p.1 p.2
          · have hpos : 0 < a p.1 := by simp [a, hp, hsunit p.1.1.1 p.2]
            have hsignp : sign p.1 = true := by
              dsimp only [sign]
              rw [if_pos hpos]
            change (match sign p.1 with
              | false => -s (unitLineProj g S p.1)
              | true => s (unitLineProj g S p.1)) ≍ p.1.1.2
            rw [hsignp]
            exact heq_of_eq hp.symm
          · have hneg : ¬ 0 < a p.1 := by simp [a, hp, hsunit p.1.1.1 p.2]
            have hsignp : sign p.1 = false := by
              dsimp only [sign]
              rw [if_neg hneg]
            change (match sign p.1 with
              | false => -s (unitLineProj g S p.1)
              | true => s (unitLineProj g S p.1)) ≍ p.1.1.2
            rw [hsignp]
            exact heq_of_eq hp.symm
      right_inv := by
        rintro ⟨y, b⟩
        apply Prod.ext
        · rfl
        · cases b <;> simp [inv, sign, a, hsunit y.1 y.2]
      continuous_toFun :=
        ((continuous_unitLineProj g S).comp continuous_subtype_val).subtype_mk
          (fun p => p.2) |>.prodMk hsign
      continuous_invFun := hinv }
  refine ⟨inferInstance, U, hxU, hUopen, ?_, e, ?_⟩
  · exact hUopen.preimage (continuous_unitLineProj g S)
  · intro p
    rfl

private theorem unitLine_isCoveringMap
    (g : SmoothRiemannianMetric I M)
    (S : ContMDiffVectorSubbundle
      (I := I) (F := E) (V := (TangentSpace I : M → Type _))
      (n := (∞ : WithTop ℕ∞)))
    (hSrank : S.rank = 1)
    (hS : IsCovariantlyInvariantSubmoduleFamily (LeviCivita (I := I) g) S.fiber) :
    IsCoveringMap (unitLineProj g S) := by
  intro x
  exact (unitLine_isEvenlyCovered g S hSrank hS x).to_isEvenlyCovered_preimage

theorem ContMDiffVectorSubbundle.exists_global_parallel_unit_section_of_rank_eq_one
    [SimplyConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    (S : ContMDiffVectorSubbundle
      (I := I) (F := E) (V := (TangentSpace I : M → Type _))
      (n := (∞ : WithTop ℕ∞)))
    (hSrank : S.rank = 1)
    (hS : IsCovariantlyInvariantSubmoduleFamily (LeviCivita (I := I) g) S.fiber) :
    ∃ X : Cₛ^∞⟮I; E, TangentSpace I⟯,
      (∀ x, X x ∈ S.fiber x) ∧
      (∀ x, g.inner x (X x) (X x) = 1) ∧
      ∀ x, ∀ v : TangentSpace I x,
        (LeviCivita (I := I) g) X x v = 0 := by
  let _ : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M :=
    ChartedSpace.locallyPathConnectedSpace H M
  let x0 : M := Classical.arbitrary M
  obtain ⟨U0, s0, hU0open, hx0U0, hs0mem, hs0unit, hs0parallel⟩ :=
    ContMDiffVectorSubbundle.exists_local_parallel_unit_section_of_rank_eq_one_of_covariantly_invariant
      g S hSrank hS x0
  let e0 : unitLine g S :=
    ⟨⟨x0, s0 x0⟩, hs0mem x0 hx0U0, hs0unit x0 hx0U0⟩
  have hcov : IsCoveringMap (unitLineProj g S) :=
    unitLine_isCoveringMap g S hSrank hS
  obtain ⟨L, hL0, hLproj⟩ :=
    (hcov.existsUnique_continuousMap_lifts (ContinuousMap.id M) x0 e0 rfl).exists
  have hbase (x : M) : unitLineProj g S (L x) = x := by
    have h := congrFun hLproj x
    simpa [Function.comp_def] using h
  let X : ∀ x : M, TangentSpace I x := fun x => hbase x ▸ (L x).1.2
  have hXL (x : M) : (⟨x, X x⟩ : TangentBundle I M) = (L x).1 := by
    apply TotalSpace.ext
    · exact (hbase x).symm
    · exact eqRec_heq _ _
  have hXcontinuous : Continuous (fun x : M =>
      (⟨x, X x⟩ : TangentBundle I M)) := by
    rw [show (fun x : M => (⟨x, X x⟩ : TangentBundle I M)) =
        fun x : M => (L x).1 by funext x; exact hXL x]
    exact continuous_subtype_val.comp L.continuous
  have hXmem (x : M) : X x ∈ S.fiber x := by
    have hx := (L x).2.1
    rw [← hXL x] at hx
    exact hx
  have hXunit (x : M) : g.inner x (X x) (X x) = 1 := by
    have hx := (L x).2.2
    rw [← hXL x] at hx
    exact hx
  have hlocal (x : M) :
      ∃ (U : Set M) (s : Cₛ^∞⟮I; E, TangentSpace I⟯),
        And (IsOpen U) <| And (x ∈ U) <|
        And (∀ y ∈ U, X y = s y) <|
        ∀ y ∈ U, ∀ v : TangentSpace I y,
          (LeviCivita (I := I) g) s y v = 0 := by
    obtain ⟨U, s, hUopen, hxU, hsmem, hsunit, hsparallel⟩ :=
      ContMDiffVectorSubbundle.exists_local_parallel_unit_section_of_rank_eq_one_of_covariantly_invariant
        g S hSrank hS x
    have hcases : ∀ y ∈ U, X y = s y ∨ X y = -s y := by
      intro y hy
      have hpU : unitLineProj g S (L y) ∈ U := by
        rw [hbase y]
        exact hy
      have hc := unitLine_eq_or_eq_neg g S hSrank s hsmem hsunit (L y) hpU
      rw [← hXL y] at hc
      exact hc
    let a : M → ℝ := fun y => g.inner y (X y) (s y)
    have ha : Continuous a := by
      have hg : Continuous (fun y : M =>
          TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
            (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] ℝ)
            y (g.inner y)) := g.contMDiff.continuous
      have hs : Continuous (fun y : M =>
          TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) y (s y)) :=
        s.contMDiff.continuous
      have htotal := Continuous.clm_bundle_apply₂
        (𝕜 := ℝ) (B := M) (F₁ := E) (F₂ := E) (F₃ := ℝ)
        (E₃ := fun _ : M => ℝ) (b := id) hg hXcontinuous hs
      have hproj : Continuous (fun p : TotalSpace ℝ (fun _ : M => ℝ) => p.2) :=
        continuous_snd.comp ((Bundle.Trivial.homeomorphProd M ℝ).continuous)
      exact hproj.comp htotal
    rcases hcases x hxU with hx | hx
    · have hax : a x = 1 := by simp [a, hx, hsunit x hxU]
      have hpos : {y : M | 0 < a y} ∈ 𝓝 x :=
        (isOpen_Ioi.preimage ha).mem_nhds (by simp [hax])
      obtain ⟨V, hVsub, hVopen, hxV⟩ := mem_nhds_iff.mp hpos
      let W := V ∩ U
      refine ⟨W, s, hVopen.inter hUopen, ⟨hxV, hxU⟩, ?_, ?_⟩
      · intro y hy
        rcases hcases y hy.2 with hys | hys
        · exact hys
        · have hay : a y = -1 := by simp [a, hys, hsunit y hy.2]
          have := hVsub hy.1
          simp [hay] at this
          norm_num at this
      · intro y hy v
        exact hsparallel y hy.2 v
    · let t : Cₛ^∞⟮I; E, TangentSpace I⟯ := -s
      have hax : a x = -1 := by simp [a, hx, hsunit x hxU]
      have hneg : {y : M | a y < 0} ∈ 𝓝 x :=
        (isOpen_Iio.preimage ha).mem_nhds (by simp [hax])
      obtain ⟨V, hVsub, hVopen, hxV⟩ := mem_nhds_iff.mp hneg
      let W := V ∩ U
      refine ⟨W, t, hVopen.inter hUopen, ⟨hxV, hxU⟩, ?_, ?_⟩
      · intro y hy
        rcases hcases y hy.2 with hys | hys
        · have hay : a y = 1 := by simp [a, hys, hsunit y hy.2]
          have := hVsub hy.1
          simp [hay] at this
          norm_num at this
        · exact hys
      · intro y hy v
        simp only [t]
        rw [show (⇑(-s) : (z : M) → TangentSpace I z) =
            ((-1 : ℝ) • fun z => s z) by
          funext z
          simp]
        rw [(LeviCivita (I := I) g).isCovariantDerivativeOnUniv.smul_const
          (-1) (s.contMDiff.mdifferentiableAt (by simp))]
        simp [hsparallel y hy.2 v]
  have hXsmooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => (⟨x, X x⟩ : TangentBundle I M)) := by
    apply contMDiff_of_locally_contMDiffOn
    intro x
    obtain ⟨U, s, hUopen, hxU, hXs, hsparallel⟩ := hlocal x
    refine ⟨U, hUopen, hxU, ?_⟩
    exact s.contMDiff.contMDiffOn.congr
      (fun y hy => by simp only [hXs y hy])
  let Xs : Cₛ^∞⟮I; E, TangentSpace I⟯ := ⟨X, hXsmooth⟩
  refine ⟨Xs, hXmem, hXunit, ?_⟩
  intro x v
  obtain ⟨U, s, hUopen, hxU, hXs, hsparallel⟩ := hlocal x
  have hevent : (fun y => Xs y) =ᶠ[𝓝 x] fun y => s y := by
    filter_upwards [hUopen.mem_nhds hxU] with y hy
    exact hXs y hy
  have hc := (LeviCivita (I := I) g).isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    Xs.mdifferentiableAt s.mdifferentiableAt
    (Filter.univ_mem : (Set.univ : Set M) ∈ 𝓝 x) hevent
  have hc' : (LeviCivita (I := I) g) Xs x =
      (LeviCivita (I := I) g) s x := by
    simpa using hc
  rw [hc']
  exact hsparallel x hxU v

end DifferentialGeometry.Geometry.Connection
