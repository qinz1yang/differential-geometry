import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspCoreMove

/-!
# BCG06, G3 (part 1): the all-level flow of the moving level on `W°` (lane BCG6-Kb, review 65 M3)

Review 65 (D65-4) asked for the parametrized comparison `G_t ∘ Φ_t = F` at ALL levels (the
G2 delivery transported only the `40`-level and recovered the two sides by connectedness). Here
the moving level `G_τ = level_b + τ Q` (`coreLevelT_BCG6K`, `Q` the strip correction) is followed
by the flow of a time-dependent field `V` with `∂_t G_{s(t)} + dG_{s(t)}(V_t) = 0` everywhere
(`s = Real.smoothTransition`), so `G_{s(t)} ∘ Φ_t = level_b` at every point of `W°`.

* `exists_allLevels_timeLift_BCG6K` (generic): `dΨ (1, V) = 0` everywhere from regularity of the
  slices on a compact `S` and time-independence off `S`;
* `flow_preserves_of_timeLift_BCG6K` (generic): the flow keeps `Ψ`;
* `mfderiv_coreLevelT_ne_zero_of_mem_closedStrip_BCG6K`: every `G_τ`, `τ ∈ [0, 1]`, is regular
  on the closed strip `K = e{37.5 ≤ z ≤ 42.5} ∩ {38.5 ≤ η_b ≤ 41.5}` ⊇ `tsupport Q` at every
  level (condition (R) `80 ε∂ + 1.02 c₃ < 1`);
* `exists_coreLevel_flow_interior_BCG6K`: on `W° = W.pieceInterior ⊤` (interior atlas) a jointly
  smooth family `Φ t` of diffeomorphisms, `Φ 0 = id`, identity off a compact set in
  `band ∩ {38 < η_b < 42}`, with `G_{s(t)} ∘ Φ t = level_b`.

No new structure, no named hypothesis.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Bundle
open scoped Manifold ContDiff Topology
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
  DifferentialGeometry.Analysis DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.Geometry.Collapse

section AllLevels

open DifferentialGeometry.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **All-level time lift** (generic). Let `Ψ : ℝ × M → ℝ` be smooth, with every slice
`Ψ (t, ·)` regular on a compact `S ⊆ N` (`N` open) and `Ψ` independent of time to first order
off `S` (`dΨ (1, 0) = 0`). Then there is a jointly smooth time-dependent field `V`, vanishing off a
compact `K ⊆ N`, with `dΨ (1, V) = 0` at EVERY point of `ℝ × M` (not only near one level): a
partition of unity on `ℝ × M` of local time lifts (on `S`) and of `(1, 0)` (off `S`) under the
affine constraint `{w | w.1 = 1, dΨ w = 0}`, then a spatial cutoff `χ` equal to `1` near `S`
(`(1, χ Y₂) = (1 - χ) (1, 0) + χ Y`). The pattern is the tree's `exists_timeLift_field_Cn`. -/
theorem exists_allLevels_timeLift_BCG6K [T2Space M] [SigmaCompactSpace M]
    {Ψ : ℝ × M → ℝ} (hΨ : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ Ψ)
    {S : Set M} (hS : IsCompact S) {N : Set M} (hN : IsOpen N) (hSN : S ⊆ N)
    (htrans : ∀ q : ℝ × M, q.2 ∈ S →
      Surjective (mfderiv I 𝓘(ℝ, ℝ) (fun y => Ψ (q.1, y)) q.2))
    (hfree : ∀ q : ℝ × M, q.2 ∉ S →
      mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) Ψ q ((1 : ℝ), (0 : E)) = 0) :
    ∃ (V : ℝ → (x : M) → TangentSpace I x) (K : Set M),
      ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞
        (fun q : ℝ × M => (⟨q.2, V q.1 q.2⟩ : TangentBundle I M)) ∧
      IsCompact K ∧ K ⊆ N ∧ (∀ t x, x ∉ K → V t x = 0) ∧
      ∀ q : ℝ × M, mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) Ψ q ((1 : ℝ), V q.1 q.2) = 0 := by
  classical
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  set T : (q : ℝ × M) → Set (TangentSpace (𝓘(ℝ, ℝ).prod I) q) := fun q =>
    {w | w.1 = 1 ∧ mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) Ψ q w = 0} with hT
  have hTconv : ∀ q, Convex ℝ (T q) := by
    intro q w₁ hw₁ w₂ hw₂ a b ha hb hab
    refine ⟨?_, ?_⟩
    · change a * w₁.1 + b * w₂.1 = 1
      rw [hw₁.1, hw₂.1, mul_one, mul_one, hab]
    · rw [map_add, map_smul, map_smul, hw₁.2, hw₂.2, smul_zero, smul_zero, add_zero]
  have hzero : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent (⊤ : ℕ∞)
      (fun q : ℝ × M => (⟨q.2, (0 : TangentSpace I q.2)⟩ : TangentBundle I M)) :=
    (contMDiff_zeroSection ℝ (TangentSpace I : M → Type _)).comp contMDiff_snd
  have hloc : ∀ q₀ : ℝ × M, ∃ U ∈ 𝓝 q₀,
      ∃ Y : (p : ℝ × M) → TangentSpace (𝓘(ℝ, ℝ).prod I) p,
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I).tangent (⊤ : ℕ∞)
          (fun p ↦ (⟨p, Y p⟩ : TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))) U ∧
        ∀ p ∈ U, Y p ∈ T p := by
    intro q₀
    by_cases h : q₀.2 ∈ S
    · obtain ⟨U, hU, Y, hY, hYU⟩ := exists_local_timeLift_Cn (n := ⊤) (by simp) hΨ
        (htrans q₀ h)
      exact ⟨U, hU, Y, hY, fun p hp => hYU p hp⟩
    · refine ⟨Prod.snd ⁻¹' Sᶜ, (hS.isClosed.isOpen_compl.preimage continuous_snd).mem_nhds h,
        autonomizedFlowVF (fun (_ : ℝ) (x : M) => (0 : TangentSpace I x)),
        (contMDiff_autonomizedFlowVF_section _ hzero).contMDiffOn, fun p hp => ⟨rfl, ?_⟩⟩
      exact hfree p hp
  obtain ⟨Y, hYT⟩ := exists_contMDiffSection_forall_mem_convex_of_local
    (I := 𝓘(ℝ, ℝ).prod I) (n := ⊤) (TangentSpace (𝓘(ℝ, ℝ).prod I)) T hTconv hloc
  obtain ⟨K, hK, hSK, hKN⟩ := exists_compact_between hS hN hSN
  obtain ⟨χ, hχ1, hχ0, -⟩ := exists_contMDiffMap_one_nhds_of_subset_interior I (n := ⊤)
    hS.isClosed hSK
  obtain ⟨U₁, hU₁o, hSU₁, hU₁χ⟩ := mem_nhdsSet_iff_exists.1 hχ1
  set V : ℝ → (x : M) → TangentSpace I x := fun t x => χ x • (Y (t, x)).2 with hVdef
  have hYs : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I).tangent (⊤ : ℕ∞)
      (fun q ↦ (⟨q, Y q⟩ : TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))) := Y.contMDiff
  have hχP : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) (⊤ : ℕ∞) (fun q : ℝ × M => χ q.2) :=
    χ.contMDiff.comp contMDiff_snd
  have hZs : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I).tangent (⊤ : ℕ∞)
      (fun q ↦ (⟨q, χ q.2 • Y q⟩ : TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))) :=
    hχP.smul_section hYs
  have hV : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent (⊤ : ℕ∞)
      (fun q : ℝ × M => (⟨q.2, V q.1 q.2⟩ : TangentBundle I M)) :=
    contMDiff_snd.comp ((contMDiff_equivTangentBundleProd (I := 𝓘(ℝ, ℝ)) (M := ℝ) (I' := I)
      (M' := M)).comp hZs)
  refine ⟨V, K, hV, hK, hKN, ?_, ?_⟩
  · intro t x hx
    change χ x • (Y (t, x)).2 = 0
    rw [hχ0 x hx, zero_smul]
  · intro q
    by_cases hq : q.2 ∈ U₁
    · have h1 : χ q.2 = 1 := hU₁χ hq
      have hVY : ((((1 : ℝ), V q.1 q.2) : ℝ × E) : TangentSpace (𝓘(ℝ, ℝ).prod I) q) = Y q := by
        refine Prod.ext (hYT q).1.symm ?_
        change χ q.2 • (Y q).2 = (Y q).2
        rw [h1, one_smul]
      rw [hVY]
      exact (hYT q).2
    · have hqS : q.2 ∉ S := fun h => hq (hSU₁ h)
      have key : mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) Ψ q
          ((1 - χ q.2) • (show TangentSpace (𝓘(ℝ, ℝ).prod I) q from ((1 : ℝ), (0 : E))) +
            χ q.2 • Y q) = 0 := by
        rw [map_add, map_smul, map_smul, hfree q hqS, (hYT q).2, smul_zero, smul_zero,
          add_zero]
      convert key using 1
      congr 1
      refine Prod.ext ?_ ?_
      · change (1 : ℝ) = (1 - χ q.2) * 1 + χ q.2 * (Y q).1
        rw [(hYT q).1]
        ring
      · change χ q.2 • (Y q).2 = (1 - χ q.2) • (0 : E) + χ q.2 • (Y q).2
        rw [smul_zero, zero_add]

omit [FiniteDimensional ℝ E] in
/-- **The flow of an all-level time lift keeps `Ψ`**: if `dΨ (1, V) = 0` everywhere, then
`Ψ (t, Φ_{s,t} x) = Ψ (s, x)` for the compactly supported flow `Φ_{s,t} = finiteOrderFlow V s t`
(clopen argument in `ℝ` with the tree's `isOpen_graph_preimage_inter_of_transport`). -/
theorem flow_preserves_of_timeLift_BCG6K [CompleteSpace E] [T2Space M]
    [BoundarylessManifold I M]
    (V : ℝ → (x : M) → TangentSpace I x)
    (hV : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞
      (fun q : ℝ × M => (⟨q.2, V q.1 q.2⟩ : TangentBundle I M)))
    {K : Set M} (hK : IsCompact K) (hsupp : ∀ t x, x ∉ K → V t x = 0)
    {Ψ : ℝ × M → ℝ} (hΨ : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ Ψ)
    (htr : ∀ q : ℝ × M, mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) Ψ q ((1 : ℝ), V q.1 q.2) = 0)
    (s t : ℝ) (x : M) : Ψ (t, finiteOrderFlow V s t x) = Ψ (s, x) := by
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  have hW := (contMDiff_autonomizedFlowVF_section V hV).of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
  set γ : ℝ → M := fun σ => finiteOrderFlow V s σ x with hγdef
  have hγ : ∀ σ, HasMFDerivAt 𝓘(ℝ, ℝ) I γ σ ((1 : ℝ →L[ℝ] ℝ).smulRight (V σ (γ σ))) :=
    fun σ => hasMFDerivAt_finiteOrderFlow V hW hK hsupp s σ x
  have hopen := isOpen_graph_preimage_inter_of_transport V hγ isOpen_univ
    (fun p _ => hΨ.mdifferentiableAt (by simp)) (fun p _ => htr p) {Ψ (s, x)}
  have hγc : Continuous γ := continuous_iff_continuousAt.2 fun σ => (hγ σ).continuousAt
  have hclosed : IsClosed ({σ : ℝ | ((σ, γ σ) : ℝ × M) ∈ univ} ∩
      (fun σ : ℝ => Ψ (σ, γ σ)) ⁻¹' {Ψ (s, x)}) :=
    (isClosed_univ.preimage (continuous_id.prodMk hγc)).inter
      (isClosed_singleton.preimage (hΨ.continuous.comp (continuous_id.prodMk hγc)))
  have hs : s ∈ ({σ : ℝ | ((σ, γ σ) : ℝ × M) ∈ univ} ∩
      (fun σ : ℝ => Ψ (σ, γ σ)) ⁻¹' {Ψ (s, x)}) := by
    refine ⟨mem_univ _, ?_⟩
    change Ψ (s, finiteOrderFlow V s s x) = Ψ (s, x)
    rw [finiteOrderFlow_self V hW hK hsupp]
  have huniv := (isClopen_iff.1 ⟨hclosed, hopen⟩).resolve_left
    (Set.nonempty_iff_ne_empty.1 ⟨s, hs⟩)
  have ht : t ∈ ({σ : ℝ | ((σ, γ σ) : ℝ × M) ∈ univ} ∩
      (fun σ : ℝ => Ψ (σ, γ σ)) ⁻¹' {Ψ (s, x)}) := huniv ▸ mem_univ t
  exact ht.2

end AllLevels

universe u

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ}
  {A : ℝ → ℝ} {w₀ ε : ℝ}

namespace BoundaryCollarPacket

variable (P : BoundaryCollarPacket W g K A w₀ ε) {b : Fin P.cusp.count}

/-- **Regularity of every moving level on the closed strip `K`** (`τ ∈ [0, 1]`, condition (R)):
the support of the correction carries no critical point of any `G_τ`, at any level. -/
theorem mfderiv_coreLevelT_ne_zero_of_mem_closedStrip_BCG6K (hε : ε ≤ 1 / 1000)
    {u : W.Carrier → ℝ} (hu : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ u) {εd c₃ : ℝ} (hc₃ : 0 ≤ c₃)
    (hR : 80 * εd + 102 / 100 * c₃ < 1)
    (hBIu : ∀ x ∈ P.safeBand_BAUGA b, |u x - (P.block b x).1| < εd)
    (hBD : ∀ x ∈ P.collarBand_BAUGA b, 38 ≤ P.height b x → P.height b x ≤ 42 →
      ∀ w : TangentSpace W.model x, |mvfderiv W.model (fun y => u y - P.height b y) x w| ≤
        c₃ * Real.sqrt (g.inner x w w))
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) {x : W.Carrier}
    (hx : x ∈ (P.cusp.collar b).toFun '' {p : CuspHalfSpace | 75 / 2 ≤ p.2.val 0 ∧
        p.2.val 0 ≤ 85 / 2} ∩ {y | 77 / 2 ≤ P.height b y ∧ P.height b y ≤ 83 / 2}) :
    mfderiv W.model 𝓘(ℝ, ℝ) (P.coreLevelT_BCG6K b u τ) x ≠ 0 := by
  obtain ⟨hxK, h1, h2⟩ := hx
  have hxS : x ∈ P.coreStrip_BCG6K b := P.closedStrip_subset_coreStrip_BCG6K b hxK
  have hband := P.coreStrip_subset_band_BCG6K b hxS
  have hsafe : x ∈ P.safeBand_BAUGA b := ⟨hband, by linarith, by linarith⟩
  have hux := hBIu x hsafe
  rw [P.block_eq_of_mem_safeBand_BAUGA b hsafe] at hux
  have hux' : |u x - P.height b x| < εd := hux
  have heq : P.coreLevelT_BCG6K b u τ =ᶠ[𝓝 x] fun y =>
      P.height b y + τ * (coreCutoff_BCG6K (P.height b y) * (u y - P.height b y)) := by
    filter_upwards [(P.isOpen_coreStrip_BCG6K b).mem_nhds hxS] with y hy
    exact P.coreLevelT_eq_on_strip_BCG6K b u τ hy
  obtain ⟨w, hw1, hw2⟩ := P.exists_heightUnit_BCG6K b hε hband
  apply mfderiv_ne_zero_of_mvfderiv_BCG6K (w := w)
  rw [mvfderiv_congr_BCG6K heq]
  have hηd : MDifferentiableAt W.model 𝓘(ℝ, ℝ) (P.height b) x :=
    ((P.contMDiff_height b) x).mdifferentiableAt (by simp)
  have hud : MDifferentiableAt W.model 𝓘(ℝ, ℝ) u x := (hu x).mdifferentiableAt (by simp)
  have hhd : MDifferentiableAt W.model 𝓘(ℝ, ℝ) (fun y => u y - P.height b y) x := hud.sub hηd
  have hκd : MDifferentiableAt W.model 𝓘(ℝ, ℝ) (fun y => coreCutoff_BCG6K (P.height b y)) x :=
    ((contDiff_coreCutoff_BCG6K.contMDiff.comp (P.contMDiff_height b)) x).mdifferentiableAt
      (by simp)
  have hτd : MDifferentiableAt W.model 𝓘(ℝ, ℝ) (fun _ : W.Carrier => τ) x :=
    mdifferentiableAt_const
  have hκdiff : DifferentiableAt ℝ coreCutoff_BCG6K (P.height b x) :=
    (contDiff_coreCutoff_BCG6K.differentiable (by simp)) _
  change mvfderiv W.model (P.height b + (fun _ => τ) * ((fun y => coreCutoff_BCG6K (P.height b y)) *
    (fun y => u y - P.height b y))) x w ≠ 0
  rw [mvfderiv_add hηd (hτd.mul (hκd.mul hhd)), add_apply, mvfderiv_mul hτd (hκd.mul hhd),
    mvfderiv_const, add_apply, smul_apply, smul_apply, zero_apply, smul_zero, add_zero,
    smul_eq_mul, mvfderiv_mul hκd hhd, add_apply, smul_apply, smul_apply, smul_eq_mul,
    smul_eq_mul, DifferentialGeometry.Topology.Ehresmann.mvfderiv_comp_real hηd hκdiff w, hw1]
  have hd := abs_le.mp (abs_deriv_coreCutoff_le_BCG6K (P.height b x))
  have hκ0 := coreCutoff_nonneg_BCG6K (P.height b x)
  have hκ1 := coreCutoff_le_one_BCG6K (P.height b x)
  have hA : |mvfderiv W.model (fun y => u y - P.height b y) x w| ≤ c₃ * (101 / 100) :=
    (hBD x hband (by linarith) (by linarith) w).trans (mul_le_mul_of_nonneg_left hw2 hc₃)
  have hA' := abs_le.mp hA
  have hu2 := abs_lt.mp hux'
  have hεd0 : 0 < εd := (abs_nonneg _).trans_lt hux'
  have e1 : -(101 / 100 * c₃) ≤ coreCutoff_BCG6K (P.height b x) *
      mvfderiv W.model (fun y => u y - P.height b y) x w := by nlinarith
  have e2 : -(80 * εd) ≤ (u x - P.height b x) * (deriv coreCutoff_BCG6K (P.height b x) * 1) := by
    nlinarith
  have e3 : -(101 / 100 * c₃ + 80 * εd) ≤ τ * (coreCutoff_BCG6K (P.height b x) *
      mvfderiv W.model (fun y => u y - P.height b y) x w +
        (u x - P.height b x) * (deriv coreCutoff_BCG6K (P.height b x) * 1)) := by
    have h3 : -(101 / 100 * c₃ + 80 * εd) ≤ coreCutoff_BCG6K (P.height b x) *
        mvfderiv W.model (fun y => u y - P.height b y) x w +
          (u x - P.height b x) * (deriv coreCutoff_BCG6K (P.height b x) * 1) := by linarith
    have h4 : 0 ≤ 101 / 100 * c₃ + 80 * εd := by positivity
    nlinarith
  apply ne_of_gt
  linarith

end BoundaryCollarPacket

section Interior

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1

namespace BoundaryCollarPacket

variable {P : BoundaryCollarPacket W g K A w₀ ε} {b : Fin P.cusp.count}

/-- **The all-level flow of the moving level on `W°`** (review 65 M3, the form
`G_t ∘ Φ_t = F`): a jointly smooth family of diffeomorphisms `Φ t` of `W°`, `Φ 0 = id`, the
identity off a compact set inside `band ∩ {38 < η_b < 42}`, with
`G_{s(t)} ∘ Φ t = level_b` at EVERY point (all levels), `s = Real.smoothTransition`. -/
theorem exists_coreLevel_flow_interior_BCG6K (hε : ε ≤ 1 / 1000) {u : W.Carrier → ℝ}
    (hu : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ u) {εd c₃ : ℝ} (hc₃ : 0 ≤ c₃)
    (hR : 80 * εd + 102 / 100 * c₃ < 1)
    (hBIu : ∀ x ∈ P.safeBand_BAUGA b, |u x - (P.block b x).1| < εd)
    (hBD : ∀ x ∈ P.collarBand_BAUGA b, 38 ≤ P.height b x → P.height b x ≤ 42 →
      ∀ w : TangentSpace W.model x, |mvfderiv W.model (fun y => u y - P.height b y) x w| ≤
        c₃ * Real.sqrt (g.inner x w w)) :
    ∃ (K' : Set (W.pieceInterior ⊤))
      (Φ : ℝ → Diffeomorph (𝓡 3) (𝓡 3) (W.pieceInterior ⊤) (W.pieceInterior ⊤) ∞),
      IsCompact K' ∧
      (∀ x ∈ K', (x : W.Carrier) ∈ P.collarBand_BAUGA b ∧ 38 < P.height b x ∧
        P.height b x < 42) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞
        (fun q : ℝ × W.pieceInterior ⊤ => Φ q.1 q.2) ∧
      (∀ x, Φ 0 x = x) ∧ (∀ t x, x ∉ K' → Φ t x = x) ∧
      ∀ t x, P.coreLevelT_BCG6K b u (Real.smoothTransition t) (Φ t x : W.Carrier) =
        P.level b x := by
  set Ψ : ℝ × W.pieceInterior ⊤ → ℝ :=
    fun q => P.coreLevelT_BCG6K b u (Real.smoothTransition q.1) q.2 with hΨdef
  have hval := contMDiff_val_interior_BCG6K W
  have hQ := P.contMDiff_coreCorrection_BCG6K b hu
  have hΨ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞ Ψ := by
    have h1 : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × W.pieceInterior ⊤ => P.level b q.2) :=
      ((P.contMDiff_level b).comp hval).comp contMDiff_snd
    have h2 : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × W.pieceInterior ⊤ => Real.smoothTransition q.1) :=
      Real.smoothTransition.contDiff.contMDiff.comp contMDiff_fst
    have h3 : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × W.pieceInterior ⊤ => P.coreCorrection_BCG6K b u q.2) :=
      (hQ.comp hval).comp contMDiff_snd
    exact h1.add (h2.mul h3)
  set S0 : Set W.Carrier :=
    (P.cusp.collar b).toFun '' {p : CuspHalfSpace | 75 / 2 ≤ p.2.val 0 ∧ p.2.val 0 ≤ 85 / 2} ∩
      {y | 77 / 2 ≤ P.height b y ∧ P.height b y ≤ 83 / 2} with hS0
  have hS0c : IsCompact S0 :=
    ((P.cusp.collar b).isCompact_image_band (by norm_num [cuspDepth])).inter_right
      ((isClosed_le continuous_const (P.contMDiff_height b).continuous).inter
        (isClosed_le (P.contMDiff_height b).continuous continuous_const))
  have hS0r : S0 ⊆ range (Subtype.val : W.pieceInterior ⊤ → W.Carrier) := by
    rintro _ ⟨⟨p, hp, rfl⟩, -⟩
    have hpd : p ∈ cuspDomain :=
      cusp_mem_cuspDomain_of_le (b := 85 / 2) (by norm_num [cuspDepth]) hp.2
    exact ⟨⟨_, mem_pieceInterior_of_isInteriorPoint_BCG6K
      (isInteriorPoint_of_height_pos_BCG6K (P.cusp.collar b) hpd (by linarith [hp.1]))⟩, rfl⟩
  have hS : IsCompact ((Subtype.val : W.pieceInterior ⊤ → W.Carrier) ⁻¹' S0) :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' hS0c hS0r
  set N0 : Set W.Carrier :=
    P.collarBand_BAUGA b ∩ {y | 38 < P.height b y ∧ P.height b y < 42} with hN0
  have hN : IsOpen ((Subtype.val : W.pieceInterior ⊤ → W.Carrier) ⁻¹' N0) :=
    continuous_subtype_val.isOpen_preimage _ ((P.isOpen_collarBand_BAUGA b).inter
      ((isOpen_lt continuous_const (P.contMDiff_height b).continuous).inter
        (isOpen_lt (P.contMDiff_height b).continuous continuous_const)))
  have hSN : (Subtype.val : W.pieceInterior ⊤ → W.Carrier) ⁻¹' S0 ⊆
      (Subtype.val : W.pieceInterior ⊤ → W.Carrier) ⁻¹' N0 := by
    rintro x ⟨hxK, h1, h2⟩
    exact ⟨P.coreStrip_subset_band_BCG6K b (P.closedStrip_subset_coreStrip_BCG6K b hxK),
      by linarith, by linarith⟩
  have htrans : ∀ q : ℝ × W.pieceInterior ⊤,
      q.2 ∈ (Subtype.val : W.pieceInterior ⊤ → W.Carrier) ⁻¹' S0 →
      Surjective (mfderiv (𝓡 3) 𝓘(ℝ, ℝ) (fun y => Ψ (q.1, y)) q.2) := by
    intro q hq
    have hGs : ContMDiff W.model 𝓘(ℝ, ℝ) ∞
        (P.coreLevelT_BCG6K b u (Real.smoothTransition q.1)) :=
      (P.contMDiff_level b).add (contMDiff_const.mul hQ)
    exact surjective_of_ne_zero_BCG6K (mfderiv_comp_val_ne_zero_BCG6K hGs q.2
      (P.mfderiv_coreLevelT_ne_zero_of_mem_closedStrip_BCG6K hε hu hc₃ hR hBIu hBD
        (Real.smoothTransition.nonneg q.1) (Real.smoothTransition.le_one q.1) hq))
  have hfree : ∀ q : ℝ × W.pieceInterior ⊤,
      q.2 ∉ (Subtype.val : W.pieceInterior ⊤ → W.Carrier) ⁻¹' S0 →
      mfderiv (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) Ψ q ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin 3))) =
        0 := by
    intro q hq
    have hnt : (q.2 : W.Carrier) ∉ tsupport (P.coreCorrection_BCG6K b u) :=
      fun h => hq (P.tsupport_coreCorrection_subset_BCG6K b u h)
    have hQ0 : P.coreCorrection_BCG6K b u =ᶠ[𝓝 (q.2 : W.Carrier)] 0 :=
      notMem_tsupport_iff_eventuallyEq.mp hnt
    have hT : Tendsto (fun q' : ℝ × W.pieceInterior ⊤ => (q'.2 : W.Carrier)) (𝓝 q)
        (𝓝 (q.2 : W.Carrier)) := (continuous_subtype_val.comp continuous_snd).continuousAt
    have heq : Ψ =ᶠ[𝓝 q] fun q' : ℝ × W.pieceInterior ⊤ => P.level b q'.2 := by
      filter_upwards [hT.eventually hQ0] with q' hq'
      simp only [hΨdef, coreLevelT_BCG6K, hq', Pi.zero_apply, mul_zero, add_zero]
    have hf : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun y : W.pieceInterior ⊤ => P.level b y) :=
      (P.contMDiff_level b).comp hval
    rw [heq.mfderiv_eq]
    have hcomp : (fun q' : ℝ × W.pieceInterior ⊤ => P.level b q'.2) =
        (fun y : W.pieceInterior ⊤ => P.level b y) ∘ Prod.snd := rfl
    rw [hcomp, mfderiv_comp q ((hf q.2).mdifferentiableAt (by simp)) mdifferentiableAt_snd,
      mfderiv_snd]
    change (mfderiv (𝓡 3) 𝓘(ℝ, ℝ) (fun y : W.pieceInterior ⊤ => P.level b y) q.2)
      (0 : EuclideanSpace ℝ (Fin 3)) = 0
    exact map_zero _
  obtain ⟨V, K', hV, hK', hK'N, hsupp, htr⟩ :=
    exists_allLevels_timeLift_BCG6K hΨ hS hN hSN htrans hfree
  refine ⟨K', fun t => DifferentialGeometry.Analysis.ODE.finiteOrderFlowDiffeomorphENat le_top V hV
    hK' hsupp 0 t, hK', fun x hx => ?_, ?_, fun x => ?_, fun t x hx => ?_, fun t x => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hK'N hx
    exact ⟨h1, h2, h3⟩
  · exact (DifferentialGeometry.Analysis.ODE.contMDiff_finiteOrderFlowDiffeomorphENat le_top V hV
      hK' hsupp).comp ((contMDiff_const.prodMk contMDiff_fst).prodMk contMDiff_snd)
  · change DifferentialGeometry.Analysis.ODE.finiteOrderFlowDiffeomorphENat le_top V hV hK' hsupp
      0 0 x = x
    rw [DifferentialGeometry.Analysis.ODE.finiteOrderFlowDiffeomorphENat_self]
    rfl
  · exact DifferentialGeometry.Analysis.ODE.finiteOrderFlowDiffeomorphENat_eq_self_of_not_mem
      le_top V hV hK' hsupp 0 t hx
  · have h := flow_preserves_of_timeLift_BCG6K V hV hK' hsupp hΨ htr 0 t x
    simp only [hΨdef, Real.smoothTransition.zero, coreLevelT_zero_BCG6K] at h
    exact h

end BoundaryCollarPacket

end Interior

end DifferentialGeometry.Geometry.Collapse
