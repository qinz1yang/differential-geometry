import DifferentialGeometry.Geometry.Comparison.FiniteSoul.SoulBaseCover

/-!
# BASE-2 adapter: the one-sided tube data of W-SUB from S3-TUBE (lane CMS3-FLOW, G3)

`exists_unitNormalCover_tube_data` (**main**): for a compact nonempty `C^r` slice `S` of codimension one
(`r ≥ 2`), the unit-normal double cover `S̃ = unitNormalCover g S` carries a charted space over the model
`Fin d → ℝ` of the order-`r` structure of `S` (`embeddedSliceChartedSpaceOfOrder`) such that, for some
`ε > 0` and every `1 ≤ n ≤ r − 1`:
* the tube map `(v, t) ↦ exp (t v)` is a `C^n` local diffeomorphism on `S̃ × (−ε, ε)`;
* it is injective modulo `(v, t) ↦ (−v, −t)`;
* the projection `S̃ → S` is a `C^n` local diffeomorphism.
These are, with `isCompact_unitNormalSet`, `unitNormalTube_neg`, `continuous_unitNormalCoverNeg`,
`unitNormalCoverNeg_neg` and `unitNormalCoverProj_surjective_and_fibres`, exactly the hypotheses of W-SUB's
`exists_smooth_hypersurface_one_sided`.

Route. Charts of `S̃` are the sheets of local unit normal fields `ν` (`SoulBaseSheet.lean`); the tube map
on a sheet has the explicit `C^(r−1)` inverse `x ↦ (ν (π ψ x), g(ψ x, ν (π ψ x)))` built from S3-TUBE's
inverse `ψ`, and injectivity modulo the deck map comes from the uniqueness clause of S3-TUBE.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M] [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- **One-sided tube data for W-SUB** over the unit-normal double cover. -/
theorem exists_unitNormalCover_tube_data [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {S : Set M} (hSc : IsCompact S) (hSne : S.Nonempty) {d : ℕ}
    (hcodim : Module.finrank ℝ E = d + 1) (hS : IsEmbeddedSliceOfOrder I (r : ℕ∞ω) d S) :
    ∃ cs : ChartedSpace (Fin d → ℝ) (unitNormalCover g S), ∃ ε > 0,
      (∀ p ∈ (univ : Set (unitNormalCover g S)) ×ˢ Ioo (-ε) ε,
        ∀ q ∈ (univ : Set (unitNormalCover g S)) ×ˢ Ioo (-ε) ε,
          unitNormalTube g S p = unitNormalTube g S q →
            q = p ∨ q = (unitNormalCoverNeg g S p.1, -p.2)) ∧
      let _ := cs
      let _ := embeddedSliceChartedSpaceOfOrder hS
      ∀ n : ℕ, (n : ℕ∞) ≤ r - 1 →
        IsLocalDiffeomorphOn (𝓘(ℝ, Fin d → ℝ).prod 𝓘(ℝ, ℝ)) I n (unitNormalTube g S)
          ((univ : Set (unitNormalCover g S)) ×ˢ Ioo (-ε) ε) ∧
        IsLocalDiffeomorph 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ) n (unitNormalCoverProj g S) := by
  classical
  have hr1 : 1 ≤ r := one_le_two.trans hr
  set m : ℕ∞ω := ((r - 1 : ℕ∞) : ℕ∞ω) with hm
  have hmn : m ≤ (r : ℕ∞ω) + 1 := coe_sub_one_le_add_one_tube
  have hmr : m ≤ (r : ℕ∞ω) :=
    (le_add_of_nonneg_right zero_le_one).trans (coe_sub_one_add_one_le_tube hr1)
  have hdom := g.geodesicFlowDomain_eq_univ hr hnorm
  have hexpdom : g.expDomain = univ := by
    rw [Bundle.ContMDiffRiemannianMetric.expDomain, hdom, preimage_univ]
  have hexp : ContMDiff I.tangent I (r : ℕ∞ω) g.expMap := by
    have h := g.contMDiffOn_expMap hr1
    rwa [hexpdom, contMDiffOn_univ] at h
  obtain ⟨ε, hε, ψ, hψs, hψ, hψexp, -, -⟩ := exists_normalTube_finite g hr hnorm hSc hSne hS
  have htube : IsOpen {x : M | infDist x S < ε} :=
    isOpen_lt (continuous_infDist_pt S) continuous_const
  -- calibration of the tube map
  have hcal : ∀ (v : unitNormalCover g S) (t : ℝ), |t| < ε →
      ψ (unitNormalTube g S (v, t)) = (⟨v.1.proj, t • v.1.snd⟩ : TangentBundle I M) ∧
        infDist (unitNormalTube g S (v, t)) S = |t| := by
    intro v t ht
    have han := smul_mem_normalSetFinite g v.2.1 t
    have hlen : Real.sqrt (g.inner v.1.proj (t • v.1.snd) (t • v.1.snd)) = |t| := by
      rw [DifferentialGeometry.Geometry.Collapse.finite_inner_smul_self, v.2.2, mul_one,
        Real.sqrt_sq_eq_abs]
    have h := hψexp _ han (by
      change Real.sqrt (g.inner v.1.proj (t • v.1.snd) (t • v.1.snd)) < ε
      rw [hlen]
      exact ht)
    refine ⟨h.1, ?_⟩
    change infDist (g.expMap (⟨v.1.proj, t • v.1.snd⟩ : TangentBundle I M)) S = |t|
    rw [h.2]
    exact hlen
  -- local unit normal fields through every point of the cover
  have hfield := fun w : unitNormalCover g S =>
    exists_local_unitNormal_field_through g hr hcodim hS w.2.1 w.2.2
  choose O hO hwO ν hνs hunit hnormal hline hthrough using hfield
  set p : unitNormalCover g S → S := unitNormalCoverProj g S with hpdef
  have hp : Continuous p := continuous_unitNormalCoverProj g S
  set V : unitNormalCover g S → Set S := fun w => {s : S | (s : M) ∈ O w} with hVdef
  have hV : ∀ w, IsOpen (V w) := fun w => (hO w).preimage continuous_subtype_val
  have hpV : ∀ w, p w ∈ V w := fun w => hwO w
  set sec : unitNormalCover g S → S → unitNormalCover g S := fun w s =>
    if h : (s : M) ∈ O w then ⟨⟨s, ν w s⟩, hnormal w s ⟨h, s.2⟩, hunit w s h⟩ else w with hsecdef
  have hsec_eq : ∀ w (s : S) (h : (s : M) ∈ O w),
      sec w s = ⟨⟨s, ν w s⟩, hnormal w s ⟨h, s.2⟩, hunit w s h⟩ := fun w s h => by
    rw [hsecdef]
    simp only [h, ↓reduceDIte]
  have hpsec : ∀ w, ∀ s ∈ V w, p (sec w s) = s := by
    intro w s hs
    rw [hsec_eq w s hs]
    rfl
  have hself : ∀ w, sec w (p w) = w := by
    intro w
    rw [hsec_eq w (p w) (hwO w)]
    exact Subtype.ext (tangentBundle_mk_eq rfl (hthrough w))
  have hsec : ∀ w, ContinuousOn (sec w) (V w) := by
    intro w
    have h2 : ContinuousOn (fun s : S => ((sec w s : unitNormalCover g S) : TangentBundle I M))
        (V w) := by
      refine (((hνs w).continuousOn).comp continuous_subtype_val.continuousOn
        (fun s hs => hs)).congr ?_
      intro s hs
      change ((sec w s : unitNormalCover g S) : TangentBundle I M) =
        (⟨(s : M), ν w s⟩ : TangentBundle I M)
      rw [hsec_eq w s hs]
    exact (Topology.IsInducing.subtypeVal.continuousOn_iff).mpr h2
  -- the sheets are open
  have hsheet_iff : ∀ w (z : unitNormalCover g S), (z.1.proj ∈ O w ∧
      0 < g.inner z.1.proj z.1.snd (ν w z.1.proj)) → sec w (p z) = z := by
    rintro w z ⟨hz1, hz2⟩
    rw [hsec_eq w (p z) hz1]
    apply Subtype.ext
    refine tangentBundle_mk_eq rfl ?_
    have hn1 := hnormal w z.1.proj ⟨hz1, z.2.1.1⟩
    rcases unit_normal_eq_or_neg g hr hcodim hS z.2.1 hn1 rfl z.2.2 (hunit w _ hz1) with h1 | h1
    · exact h1
    · exfalso
      have h1'' : (ν w z.1.proj : E) = -z.1.snd := h1
      have h1' : (ν w z.1.proj : E) = (-1 : ℝ) • z.1.snd := by rw [h1'', neg_one_smul]
      have : g.inner z.1.proj z.1.snd (ν w z.1.proj) = -1 := by
        rw [h1', map_smul, z.2.2]
        norm_num
      linarith
  have hsheet_val : ∀ w (z : unitNormalCover g S), z.1.proj ∈ O w → sec w (p z) = z →
      (z.1.snd : E) = ν w z.1.proj := by
    intro w z hz1 hz2
    have h := congrArg (fun y : unitNormalCover g S => (y.1.snd : E)) hz2
    rw [hsec_eq w (p z) hz1] at h
    exact h.symm
  have hopen : ∀ w, IsOpen {z | p z ∈ V w ∧ sec w (p z) = z} := by
    intro w
    set A : Set (TangentBundle I M) := (fun v : TangentBundle I M => v.proj) ⁻¹' O w with hA
    have hAo : IsOpen A := (hO w).preimage (FiberBundle.continuous_proj E (TangentSpace I))
    have hq : ContinuousOn (fun v : TangentBundle I M => g.inner v.proj v.snd (ν w v.proj)) A := by
      intro v hv
      have hfield : ContMDiffAt I.tangent I.tangent m
          (fun v : TangentBundle I M => (⟨v.proj, ν w v.proj⟩ : TangentBundle I M)) v :=
        ((hνs w).contMDiffAt ((hO w).mem_nhds hv)).comp v
          (Bundle.contMDiff_proj (TangentSpace I)).contMDiffAt
      exact (contMDiffAt_inner_field_tube g hmn (b := fun v : TangentBundle I M => v.proj)
        (v := fun v => v.snd) (w := fun v => ν w v.proj) contMDiffAt_id
        hfield).continuousAt.continuousWithinAt
    have hset : {z : unitNormalCover g S | p z ∈ V w ∧ sec w (p z) = z} =
        Subtype.val ⁻¹' (A ∩ (fun v : TangentBundle I M => g.inner v.proj v.snd (ν w v.proj)) ⁻¹'
          Ioi 0) := by
      ext z
      constructor
      · rintro ⟨hz1, hz2⟩
        refine ⟨hz1, ?_⟩
        change 0 < g.inner z.1.proj z.1.snd (ν w z.1.proj)
        have hzs := hsheet_val w z hz1 hz2
        have key : ∀ X : E, X = ν w z.1.proj → g.inner z.1.proj X (ν w z.1.proj) = 1 := by
          rintro X rfl
          exact hunit w _ hz1
        rw [key _ hzs]
        exact one_pos
      · rintro ⟨hz1, hz2⟩
        exact ⟨hz1, hsheet_iff w z ⟨hz1, hz2⟩⟩
    rw [hset]
    exact (hq.isOpen_inter_preimage hAo isOpen_Ioi).preimage continuous_subtype_val
  let _ := embeddedSliceChartedSpaceOfOrder hS
  let cs : ChartedSpace (Fin d → ℝ) (unitNormalCover g S) :=
    sheetChartedSpace (Fin d → ℝ) p hp V hV hpV sec hsec hpsec hself hopen
  refine ⟨cs, ε, hε, ?_, ?_⟩
  · -- injectivity modulo the deck map
    rintro ⟨v, t⟩ ⟨-, ht⟩ ⟨v', t'⟩ ⟨-, ht'⟩ heq
    have hta : |t| < ε := abs_lt.mpr ⟨ht.1, ht.2⟩
    have hta' : |t'| < ε := abs_lt.mpr ⟨ht'.1, ht'.2⟩
    have h1 := (hcal v t hta).1
    have h2 := (hcal v' t' hta').1
    rw [heq, h2] at h1
    have hproj : v'.1.proj = v.1.proj := by
      have := congrArg (fun z : TangentBundle I M => z.proj) h1
      exact this
    have hsnd : t' • (v'.1.snd : E) = t • (v.1.snd : E) := by
      have := congrArg (fun z : TangentBundle I M => (z.snd : E)) h1
      exact this
    have hv0 : (v.1.snd : E) ≠ 0 := by
      intro h0
      have h := v.2.2
      have h00 : g.inner v.1.proj (0 : TangentSpace I v.1.proj) (0 : TangentSpace I v.1.proj) = 0 := by
        rw [map_zero]
      have key : ∀ X : E, X = 0 → g.inner v.1.proj X X = 0 := by
        rintro X rfl
        exact h00
      rw [key _ h0] at h
      exact zero_ne_one h
    rcases unit_normal_eq_or_neg g hr hcodim hS v.2.1 v'.2.1 hproj.symm v.2.2 v'.2.2 with hs | hs
    · left
      have hsnd' : t' • (v.1.snd : E) = t • (v.1.snd : E) :=
        (congrArg (fun u : E => t' • u) hs.symm).trans hsnd
      have htt : t' = t := smul_left_injective ℝ hv0 hsnd'
      have hvv : v' = v := Subtype.ext (tangentBundle_mk_eq hproj hs)
      rw [hvv, htt]
    · right
      have hsnd' : t' • (-(v.1.snd : E)) = t • (v.1.snd : E) :=
        (congrArg (fun u : E => t' • u) hs.symm).trans hsnd
      have h3 : (-t') • (v.1.snd : E) = t • (v.1.snd : E) :=
        ((neg_smul t' (v.1.snd : E)).trans (smul_neg t' (v.1.snd : E)).symm).trans hsnd'
      have htt : t' = -t := by
        have := smul_left_injective ℝ hv0 h3
        linarith
      have hvv : v' = unitNormalCoverNeg g S v := by
        apply Subtype.ext
        change v'.1 = (⟨v.1.proj, (-1 : ℝ) • v.1.snd⟩ : TangentBundle I M)
        exact tangentBundle_mk_eq hproj (by rw [hs, neg_one_smul])
      rw [hvv, htt]
  · intro _ _ n hn
    have hnm : (n : WithTop ℕ∞) ≤ m := by rw [hm]; exact_mod_cast hn
    -- the inclusion of the cover into `TM` and the tube map are `C^m`
    have hι : ∀ v : unitNormalCover g S, ContMDiffAt 𝓘(ℝ, Fin d → ℝ) I.tangent m
        (fun v : unitNormalCover g S => (v : TangentBundle I M)) v := by
      intro v
      refine contMDiffAt_sheet_of_comp_sec p hp V hV hpV sec hsec hpsec hself hopen ?_
      have hval : ContMDiffAt 𝓘(ℝ, Fin d → ℝ) I (r : ℕ∞ω) (Subtype.val : S → M) (p v) :=
        contMDiff_val_ofOrder hS (p v)
      have hf : ContMDiffAt I I.tangent m (fun x : M => (⟨x, ν v x⟩ : TangentBundle I M))
          ((p v : S) : M) :=
        (hνs v).contMDiffAt ((hO v).mem_nhds (hwO v))
      refine (hf.comp (p v) (hval.of_le hmr)).congr_of_eventuallyEq ?_
      filter_upwards [(hV v).mem_nhds (hpV v)] with s hs
      rw [hsec_eq v s hs]
      rfl
    have hΦ : ∀ q : unitNormalCover g S × ℝ,
        ContMDiffAt (𝓘(ℝ, Fin d → ℝ).prod 𝓘(ℝ, ℝ)) I m (unitNormalTube g S) q := by
      intro q
      have h1 : ContMDiffAt (𝓘(ℝ, Fin d → ℝ).prod 𝓘(ℝ, ℝ)) I.tangent m
          (fun q : unitNormalCover g S × ℝ => (q.1 : TangentBundle I M)) q :=
        (hι q.1).comp q contMDiffAt_fst
      have h3 := contMDiffAt_smul_tube h1
        (contMDiffAt_snd (I := 𝓘(ℝ, Fin d → ℝ)) (J := 𝓘(ℝ, ℝ)))
      exact (hexp.of_le hmr).contMDiffAt.comp q h3
    -- the foot point, as a point of `S`
    set foot : M → S := fun x =>
      if h : infDist x S < ε then ⟨(ψ x).proj, (hψ x h).1.1⟩ else ⟨_, hSne.some_mem⟩ with hfootdef
    have hfoot_eq : ∀ x (h : infDist x S < ε), foot x = ⟨(ψ x).proj, (hψ x h).1.1⟩ :=
      fun x h => by
        rw [hfootdef]
        simp only [h, ↓reduceDIte]
    have hfootval : ∀ x, infDist x S < ε → ((foot x : S) : M) = (ψ x).proj := by
      intro x h
      rw [hfoot_eq x h]
    have hψproj : ∀ x, infDist x S < ε →
        ContMDiffAt I I m (fun y => (ψ y).proj) x := fun x hx =>
      (Bundle.contMDiff_proj (TangentSpace I)).contMDiffAt.comp x
        (hψs.contMDiffAt (htube.mem_nhds hx))
    have hfoot : ∀ x, infDist x S < ε → ContMDiffAt I 𝓘(ℝ, Fin d → ℝ) n foot x := by
      intro x hx
      refine contMDiffAt_of_contMDiffAt_val_ofOrder hS (hnm.trans hmr) foot ?_
      refine ((hψproj x hx).of_le hnm).congr_of_eventuallyEq ?_
      filter_upwards [htube.mem_nhds hx] with y hy
      exact hfootval y hy
    refine ⟨?_, isLocalDiffeomorph_sheet_proj p hp V hV hpV sec hsec hpsec hself hopen n⟩
    rintro ⟨⟨w, t₀⟩, -, ht₀⟩
    set sh : Set (unitNormalCover g S) := {z | p z ∈ V w ∧ sec w (p z) = z} with hsh
    set tgt : Set M := {x | infDist x S < ε} ∩ (fun x => (ψ x).proj) ⁻¹' O w with htgt
    set inv : M → unitNormalCover g S × ℝ := fun x =>
      (sec w (foot x), g.inner (ψ x).proj (ψ x).snd (ν w (ψ x).proj)) with hinv
    have htgto : IsOpen tgt := by
      have hc : ContinuousOn (fun x => (ψ x).proj) {x : M | infDist x S < ε} :=
        (FiberBundle.continuous_proj E (TangentSpace I : M → Type _)).comp_continuousOn
          hψs.continuousOn
      exact hc.isOpen_inter_preimage htube (hO w)
    have hfootV : ∀ x ∈ tgt, foot x ∈ V w := by
      intro x hx
      change ((foot x : S) : M) ∈ O w
      rw [hfootval x hx.1]
      exact hx.2
    have hsecfoot : ∀ x ∈ tgt, ((sec w (foot x) : unitNormalCover g S) : TangentBundle I M) =
        ⟨(ψ x).proj, ν w (ψ x).proj⟩ := by
      intro x hx
      rw [hsec_eq w (foot x) (hfootV x hx)]
      exact tangentBundle_mk_eq (hfootval x hx.1) (by rw [hfootval x hx.1])
    let e : PartialEquiv (unitNormalCover g S × ℝ) M :=
      { toFun := unitNormalTube g S
        invFun := inv
        source := sh ×ˢ Ioo (-ε) ε
        target := tgt
        map_source' := by
          rintro ⟨v, t⟩ ⟨hv, ht⟩
          have hta : |t| < ε := abs_lt.mpr ⟨ht.1, ht.2⟩
          obtain ⟨h1, h2⟩ := hcal v t hta
          refine ⟨?_, ?_⟩
          · change infDist (unitNormalTube g S (v, t)) S < ε
            rw [h2]
            exact hta
          · change (ψ (unitNormalTube g S (v, t))).proj ∈ O w
            rw [h1]
            exact hv.1
        map_target' := by
          intro x hx
          refine ⟨⟨?_, ?_⟩, ?_⟩
          · rw [hpsec w _ (hfootV x hx)]
            exact hfootV x hx
          · rw [hpsec w _ (hfootV x hx)]
          · have hcs := DifferentialGeometry.Geometry.Collapse.abs_finite_inner_le g (ψ x).proj
              (ψ x).snd (ν w (ψ x).proj)
            rw [hunit w _ hx.2, Real.sqrt_one, mul_one, (hψ x hx.1).2.2] at hcs
            exact abs_lt.mp (hcs.trans_lt hx.1)
        left_inv' := by
          rintro ⟨v, t⟩ ⟨hv, ht⟩
          have hta : |t| < ε := abs_lt.mpr ⟨ht.1, ht.2⟩
          obtain ⟨h1, h2⟩ := hcal v t hta
          have hxt : infDist (unitNormalTube g S (v, t)) S < ε := by rw [h2]; exact hta
          have hfv : foot (unitNormalTube g S (v, t)) = p v := by
            rw [hfoot_eq _ hxt]
            apply Subtype.ext
            change (ψ (unitNormalTube g S (v, t))).proj = v.1.proj
            rw [h1]
          have hvs := hsheet_val w v hv.1 hv.2
          change (sec w (foot (unitNormalTube g S (v, t))),
            g.inner (ψ (unitNormalTube g S (v, t))).proj (ψ (unitNormalTube g S (v, t))).snd
              (ν w (ψ (unitNormalTube g S (v, t))).proj)) = (v, t)
          rw [hfv, hv.2, h1]
          refine Prod.ext rfl ?_
          change g.inner v.1.proj (t • v.1.snd) (ν w v.1.proj) = t
          have key : ∀ X : TangentSpace I v.1.proj, X = ν w v.1.proj →
              g.inner v.1.proj (t • X) (ν w v.1.proj) = t := by
            rintro X rfl
            rw [map_smul, smul_apply, hunit w v.1.proj hv.1, smul_eq_mul, mul_one]
          exact key _ hvs
        right_inv' := by
          intro x hx
          change g.expMap (⟨((sec w (foot x) : unitNormalCover g S) : TangentBundle I M).proj,
            g.inner (ψ x).proj (ψ x).snd (ν w (ψ x).proj) •
              ((sec w (foot x) : unitNormalCover g S) : TangentBundle I M).snd⟩ :
                TangentBundle I M) = x
          rw [hsecfoot x hx]
          have hl := hline w (ψ x) (hψ x hx.1).1 hx.2
          exact (congrArg g.expMap (tangentBundle_mk_eq rfl hl.symm)).trans (hψ x hx.1).2.1 }
    refine ⟨{ toPartialEquiv := e
              open_source := (hopen w).prod isOpen_Ioo
              open_target := htgto
              contMDiffOn_toFun := fun q _ => ((hΦ q).of_le hnm).contMDiffWithinAt
              contMDiffOn_invFun := ?_ }, ⟨⟨hpV w, hself w⟩, ht₀⟩, fun _ _ => rfl⟩
    intro x hx
    have hxt : infDist x S < ε := hx.1
    have hC1 : ContMDiffAt I 𝓘(ℝ, Fin d → ℝ) n (fun x => sec w (foot x)) x := by
      refine contMDiffAt_sheet_of_comp_proj p hp V hV hpV sec hsec hpsec hself hopen ?_ ?_
      · exact ContinuousAt.comp (g := sec w) (f := foot)
          ((hsec w).continuousAt ((hV w).mem_nhds (hfootV x hx))) (hfoot x hxt).continuousAt
      · refine (hfoot x hxt).congr_of_eventuallyEq ?_
        filter_upwards [htgto.mem_nhds hx] with y hy
        exact hpsec w _ (hfootV y hy)
    have hC2 : ContMDiffAt I 𝓘(ℝ, ℝ) n
        (fun x => g.inner (ψ x).proj (ψ x).snd (ν w (ψ x).proj)) x := by
      have hψx : ContMDiffAt I I.tangent n ψ x := (hψs.contMDiffAt (htube.mem_nhds hxt)).of_le hnm
      have hfw : ContMDiffAt I I.tangent n
          (fun y => (⟨(ψ y).proj, ν w (ψ y).proj⟩ : TangentBundle I M)) x :=
        (((hνs w).contMDiffAt ((hO w).mem_nhds hx.2)).of_le hnm).comp x
          ((hψproj x hxt).of_le hnm)
      exact contMDiffAt_inner_field_tube g (hnm.trans hmn) (b := fun y => (ψ y).proj)
        (v := fun y => (ψ y).snd) (w := fun y => ν w (ψ y).proj) hψx hfw
    exact (hC1.prodMk hC2).contMDiffWithinAt

end DifferentialGeometry.Geometry.FiniteSoul
