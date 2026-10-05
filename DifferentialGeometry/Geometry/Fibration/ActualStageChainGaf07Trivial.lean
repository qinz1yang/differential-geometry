import DifferentialGeometry.Geometry.Fibration.ActualStageChainGaf07Row
import DifferentialGeometry.Topology.Ehresmann.LocalTriviality
import DifferentialGeometry.Topology.Manifold.ContMDiff.OpenSubtype

/-!
# GAF07: smooth bundle (local trivializations in the base charts) and the whole-fibre isotopy

Blueprint `master207B.tex`, GAF07 (`thm:fibration-whole-closed-fiber-bundles`, B:6049–6165):
"The map `π_jE : X_j → B_j` is a proper onto smooth bundle … The inherited smooth
proper-submersion theorem supplies its local trivializations" and "Each WHOLE fiber is smoothly
isotopic, inside its original buffered chart, to a fiber of the SAME original coordinate `η_i`"
(FC34, the smooth compact isotopy result). The accepted GAF07 row (`Gaf02ChainEJA.gaf07_row_GAFD`,
C14-GAF-D G3) states the bundle in the base chart (proper, onto, submersion) and the fibre
comparison as a homeomorphism (deviations D1, D2 of its delivery). This file supplies both strong
forms.

D1 (bundle). In BASES' base chart `κ_i = R_i⁻¹u_i` the piece `B_j^i = W_j ∩ {v_i > .9R_i,
|u_i| < 4ℓ_iv_i}` of `B_j` is the ball `B(0, 4ℓ_i)` (`κ_i` is a bijection, BASES' smooth chart
inverse), its whole preimage is `(π_jE)⁻¹(B_j^i) = {p ∈ Y_i | |g_i(p)| < 4ℓ_i}`, and
`g_i = κ_i ∘ π_jE : {p ∈ Y_i | |g_i| < 4ℓ_i} → B(0, 4ℓ_i)` is a smooth PROPER SURJECTIVE SUBMERSION
of manifolds (open subsets of `M` and of `ℝ^d`); the tree's Ehresmann theorem
`ehresmann_local_triviality` then gives, over every point of the ball, an open neighbourhood `Q` and
a diffeomorphism `fibre × Q ≃ₘ g_i⁻¹(Q)` over `Q`.

D2 (isotopy as FC34's diffeomorphism). FC34a in the tree
(`nonempty_diffeomorph_levelSet_of_compact_transport`) transports the level along the whole trace
of `h_τ = (1 − τ)η_i + τg_i` inside the compact `{|η_i| ≤ 4.01ℓ_i} ⊂ Y_i` and gives a
DIFFEOMORPHISM of the two levels; stated here as ONE compact manifold `S` with two smooth embeddings
into `M`, onto the original fibre `{p ∈ Y_i | η_i(p) = a}` and onto the whole fibre
`{p ∈ Y_i | g_i(p) = a}` (both inside the buffered chart `Y_i`).

* generic: `exists_embedding_pair_level_on_open_GAFD` (D2 kernel), `chart_bundle_of_open_GAFD`
  (D1 kernel: smooth, proper, onto, submersion of a codomain-restricted map).
* chain: `Gaf02Chain.gaf07_circle_submersion_of_mem_GAFD`, `gaf07_circle_level_pair_GAFD`,
  `gaf07_slim_level_pair_GAFD`, `gaf07_circle_chart_map_GAFD`, `gaf07_slim_chart_map_GAFD`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open GC.GraphManifold GC.Endpoint

namespace DifferentialGeometry.Geometry.Collapse

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

section Generic

variable {E F H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- The inclusion of a regular level of a map on an open subset into `M`: smooth, a topological
embedding, with injective differential (the data of a smooth embedding). -/
theorem regularLevel_open_inclusion_GAFD {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] (V : TopologicalSpace.Opens M) (f : V → F) (a : F)
    (hf : ContMDiff I 𝓘(ℝ, F) ∞ f) (hreg : ∀ x, f x = a → Surjective (mfderiv I 𝓘(ℝ, F) f x)) :
    let _ := regularFiberChartedSpace f a hf hreg
    ContMDiff 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ) I ∞
        ((Subtype.val : V → M) ∘ (Subtype.val : {x // f x = a} → V)) ∧
      Topology.IsEmbedding ((Subtype.val : V → M) ∘ (Subtype.val : {x // f x = a} → V)) ∧
      ∀ y, Injective (mfderiv 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ) I
        ((Subtype.val : V → M) ∘ (Subtype.val : {x // f x = a} → V)) y) := by
  let _ := regularFiberChartedSpace f a hf hreg
  have hinc := contMDiff_regularFiberInclusion f a hf hreg
  refine ⟨(contMDiff_subtype_val (I := I)).comp hinc,
    Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal, fun y => ?_⟩
  have hFd := (hinc y).mdifferentiableAt (by simp)
  have h2 := (DifferentialGeometry.hasMFDerivAt_subtype_val (I := I) _ y.1).comp y
    hFd.hasMFDerivAt
  rw [h2.mfderiv]
  have hi := mfderiv_regularFiberInclusion_injective f a hf hreg y
  intro u v huv
  exact hi huv

variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [LocallyCompactSpace M] [SecondCountableTopology M]

/-- **FC34a as a pair of smooth embeddings** (generic; D2 kernel): with the hypotheses of
`nonempty_homeomorph_level_on_open_GAFC` and `dim F < dim E`, there is ONE manifold `S` with smooth
embeddings `ι₀, ι₁ : S → M` onto the original level `{y ∈ U | η y = a}` and onto the whole adjusted
level `{y ∈ U | g y = a}` (FC34a's diffeomorphism of the two regular levels). -/
theorem exists_embedding_pair_level_on_open_GAFD (hdim : Module.finrank ℝ F < Module.finrank ℝ E)
    {U : Set M} (hU : IsOpen U) {η g : M → F}
    (hη : ContMDiffOn I 𝓘(ℝ, F) ∞ η U) (hg : ContMDiffOn I 𝓘(ℝ, F) ∞ g U) {a : F} {ℓ : ℝ}
    (hℓ : 1 ≤ ℓ) (ha : ‖a‖ < 4 * ℓ) (hgη : ∀ y ∈ U, ‖g y - η y‖ < 1 / 800) (ν : M → E → ℝ)
    {c K : ℝ} (hc : 0 ≤ c) (hcK : c * K < 1)
    (hright : ∀ y ∈ U, ∃ R : F →L[ℝ] E,
      (show E →L[ℝ] F from mfderiv I 𝓘(ℝ, F) η y).comp R = ContinuousLinearMap.id ℝ F ∧
        ∀ w, ν y (R w) ≤ K * ‖w‖)
    (hDg : ∀ y ∈ U, ∀ v : E, ‖(show E →L[ℝ] F from mfderiv I 𝓘(ℝ, F) g y) v -
      (show E →L[ℝ] F from mfderiv I 𝓘(ℝ, F) η y) v‖ ≤ c * ν y v)
    (hQ : IsCompact {y | y ∈ U ∧ ‖η y‖ ≤ 401 / 100 * ℓ}) :
    ∃ (S : Type u) (_ : TopologicalSpace S)
      (_ : ChartedSpace (Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ) S)
      (_ : IsManifold 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ) ∞ S)
      (ι₀ ι₁ : S → M),
      IsSmoothEmbedding 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ) I ∞ ι₀ ∧
      IsSmoothEmbedding 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ) I ∞ ι₁ ∧
      range ι₀ = {y | y ∈ U ∧ η y = a} ∧ range ι₁ = {y | y ∈ U ∧ g y = a} := by
  have : Nonempty (Fin (Module.finrank ℝ E - Module.finrank ℝ F)) := ⟨⟨0, by omega⟩⟩
  let V : TopologicalSpace.Opens M := ⟨U, hU⟩
  have : LocallyCompactSpace V := hU.locallyCompactSpace
  have hηV : ContMDiff I 𝓘(ℝ, F) ∞ (fun y : V => η y) :=
    hη.comp_contMDiff (contMDiff_subtype_val (I := I)) (fun y => y.2)
  have hgV : ContMDiff I 𝓘(ℝ, F) ∞ (fun y : V => g y) :=
    hg.comp_contMDiff (contMDiff_subtype_val (I := I)) (fun y => y.2)
  have hder : ∀ (f : M → F) (y : V),
      mfderiv I 𝓘(ℝ, F) (fun z : V => f z) y = mfderiv I 𝓘(ℝ, F) f y :=
    fun f y => DifferentialGeometry.mfderiv_restrict_open f V y
  have hQV : IsCompact {y : V | ‖η y‖ ≤ 401 / 100 * ℓ} := by
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
    convert hQ using 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hx, hxη⟩
      exact ⟨⟨x, hx⟩, hxη, rfl⟩
  have hright' : ∀ y : V, ∃ R : F →L[ℝ] E,
      (mfderiv I 𝓘(ℝ, F) (fun z : V => η z) y : E →L[ℝ] F).comp R = ContinuousLinearMap.id ℝ F ∧
        ∀ w, ν y (R w) ≤ K * ‖w‖ := fun y => by
    obtain ⟨R, hR, hRw⟩ := hright y y.2
    refine ⟨R, ?_, hRw⟩
    rw [hder]
    exact hR
  have hDg' : ∀ (y : V) (v : E), ‖(show E →L[ℝ] F from mfderiv I 𝓘(ℝ, F) (fun z : V => g z) y) v -
      (show E →L[ℝ] F from mfderiv I 𝓘(ℝ, F) (fun z : V => η z) y) v‖ ≤ c * ν y v :=
    fun y v => by
      rw [hder, hder]
      exact hDg y y.2 v
  let h : V × ℝ → F := fun x => (1 - x.2) • η x.1 + x.2 • g x.1
  have hh : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ, F) ∞ h := contMDiff_straightLine hηV hgV
  have hreg : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y, h (y, τ) = a →
      Surjective (mfderiv I 𝓘(ℝ, F) (fun z => h (z, τ)) y) :=
    fun τ hτ y _ => straightLine_slice_regular_nu_GAFC hηV hgV (fun y => ν y) hc hcK hright' hDg'
      τ hτ y
  have hloc : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y, h (y, τ) = a → y ∈ {y : V | ‖η y‖ ≤ 401 / 100 * ℓ} :=
    fun τ hτ y hy => (norm_lt_of_level_of_straight_line hτ hℓ ha (hgη y y.2) hy).le
  have hh0 := contMDiff_familySlice hh 0
  have hreg0 := hreg 0 (left_mem_Icc.mpr zero_le_one)
  have hh1 := contMDiff_familySlice hh 1
  have hreg1 := hreg 1 (right_mem_Icc.mpr zero_le_one)
  let _ := regularFiberChartedSpace (fun y => h (y, 0)) a hh0 hreg0
  let _ := regularFiberChartedSpace (fun y => h (y, 1)) a hh1 hreg1
  have hm0 := regularFiberIsManifold (fun y => h (y, 0)) a hh0 hreg0
  have _ := regularFiberIsManifold (fun y => h (y, 1)) a hh1 hreg1
  obtain ⟨φ⟩ := nonempty_diffeomorph_levelSet_of_compact_transport h hh a hreg hQV hloc
  obtain ⟨c0, e0, i0⟩ := regularLevel_open_inclusion_GAFD V (fun y => h (y, 0)) a hh0 hreg0
  obtain ⟨c1, e1, i1⟩ := regularLevel_open_inclusion_GAFD V (fun y => h (y, 1)) a hh1 hreg1
  have he0 := isSmoothEmbedding_of_injective_mfderiv_of_interior_GSF (by simp) c0 e0 i0
    (fun _ => BoundarylessManifold.isInteriorPoint)
  obtain ⟨he1', hr1⟩ := isSmoothEmbedding_comp_diffeomorph_symm_SSTD _ c1 e1 i1 φ.symm
  have h0 : ∀ y : V, h (y, 0) = η y := fun y => by
    change (1 - 0 : ℝ) • η y + (0 : ℝ) • g y = η y
    rw [sub_zero, one_smul, zero_smul, add_zero]
  have h1 : ∀ y : V, h (y, 1) = g y := fun y => by
    change (1 - 1 : ℝ) • η y + (1 : ℝ) • g y = g y
    rw [sub_self, zero_smul, one_smul, zero_add]
  refine ⟨{y : V // h (y, 0) = a}, inferInstance, regularFiberChartedSpace _ a hh0 hreg0, hm0, _,
    _, he0, he1', ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y.1.2, (h0 y.1).symm.trans y.2⟩
    · rintro ⟨hx, hxa⟩
      exact ⟨⟨⟨x, hx⟩, (h0 ⟨x, hx⟩).trans hxa⟩, rfl⟩
  · rw [hr1]
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y.1.2, (h1 y.1).symm.trans y.2⟩
    · rintro ⟨hx, hxa⟩
      exact ⟨⟨⟨x, hx⟩, (h1 ⟨x, hx⟩).trans hxa⟩, rfl⟩

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
  [LocallyCompactSpace M] [SecondCountableTopology M] in
/-- **A proper surjective submersion onto an open set, restricted** (generic; D1 kernel): for `f`
smooth on an open `U ⊆ M` with values in an open `O ⊆ F`, submersive on `U`, with compact
`{x ∈ U | f x ∈ K}` for every compact `K ⊆ O`, and onto `O`, the codomain-restricted map between
the open submanifolds `U → O` is smooth, proper, surjective, and a submersion at every point. -/
theorem chart_bundle_of_open_GAFD {U : Set M} (hU : IsOpen U) {O : Set F} (hO : IsOpen O)
    {f : M → F} (hf : ContMDiffOn I 𝓘(ℝ, F) ∞ f U) (hmaps : ∀ x ∈ U, f x ∈ O)
    (hreg : ∀ x ∈ U, Surjective (mfderiv I 𝓘(ℝ, F) f x))
    (hprop : ∀ Kc ⊆ O, IsCompact Kc → IsCompact {x | x ∈ U ∧ f x ∈ Kc})
    (hsurj : ∀ y ∈ O, ∃ x ∈ U, f x = y) :
    ContMDiff I 𝓘(ℝ, F) ∞ (fun x : (⟨U, hU⟩ : TopologicalSpace.Opens M) =>
        (⟨f x, hmaps x x.2⟩ : (⟨O, hO⟩ : TopologicalSpace.Opens F))) ∧
      IsProperMap (fun x : (⟨U, hU⟩ : TopologicalSpace.Opens M) =>
        (⟨f x, hmaps x x.2⟩ : (⟨O, hO⟩ : TopologicalSpace.Opens F))) ∧
      Surjective (fun x : (⟨U, hU⟩ : TopologicalSpace.Opens M) =>
        (⟨f x, hmaps x x.2⟩ : (⟨O, hO⟩ : TopologicalSpace.Opens F))) ∧
      ∀ x, Surjective (mfderiv I 𝓘(ℝ, F) (fun x : (⟨U, hU⟩ : TopologicalSpace.Opens M) =>
        (⟨f x, hmaps x x.2⟩ : (⟨O, hO⟩ : TopologicalSpace.Opens F))) x) := by
  let V : TopologicalSpace.Opens M := ⟨U, hU⟩
  let W : TopologicalSpace.Opens F := ⟨O, hO⟩
  let fW : V → W := fun x => ⟨f x, hmaps x x.2⟩
  have hfV : ContMDiff I 𝓘(ℝ, F) ∞ (fun x : V => f x) :=
    hf.comp_contMDiff (contMDiff_subtype_val (I := I)) (fun y => y.2)
  have hsm : ContMDiff I 𝓘(ℝ, F) ∞ fW :=
    (DifferentialGeometry.Manifold.contMDiff_subtypeVal_comp_iff W fW).mp hfV
  refine ⟨hsm, ?_, fun y => ?_, fun x => ?_⟩
  · rw [isProperMap_iff_isCompact_preimage]
    refine ⟨hsm.continuous, fun Kc hK => ?_⟩
    have hK' : IsCompact ((Subtype.val : W → F) '' Kc) := hK.image continuous_subtype_val
    have hsub : (Subtype.val : W → F) '' Kc ⊆ O := by
      rintro _ ⟨z, -, rfl⟩
      exact z.2
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
    convert hprop _ hsub hK' using 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, fW y, hy, rfl⟩
    · rintro ⟨hx, z, hz, hzx⟩
      refine ⟨⟨x, hx⟩, ?_, rfl⟩
      have : fW ⟨x, hx⟩ = z := Subtype.ext hzx.symm
      change fW ⟨x, hx⟩ ∈ Kc
      rw [this]
      exact hz
  · obtain ⟨x, hx, hfx⟩ := hsurj y.1 y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hfx⟩
  · have h1 := DifferentialGeometry.mfderiv_subtypeVal_comp (I := I) (J := 𝓘(ℝ, F)) fW x
    have h2 := DifferentialGeometry.mfderiv_restrict_open (I := I) (J := 𝓘(ℝ, F)) f V x
    change Surjective (mfderiv I 𝓘(ℝ, F) fW x)
    rw [← h1]
    change Surjective (mfderiv I 𝓘(ℝ, F) (fun z : V => f z) x)
    rw [h2]
    exact hreg x.1 x.2

/-- **Ehresmann local triviality, existential form** (the tree's `ehresmann_local_triviality`, with
the fibre's regular-level smooth structure as an existential instance): a smooth proper submersion
`f : M → N` is trivial over a neighbourhood `Q` of every `y`: `fibre × Q ≃ₘ f⁻¹(Q)` over `Q`,
identity on the fibre over `y`. -/
theorem local_trivial_of_proper_submersion_GAFD {E' F' H' H'' M' N' : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F']
    [TopologicalSpace H'] [TopologicalSpace H''] [TopologicalSpace M'] [ChartedSpace H' M']
    [TopologicalSpace N'] [ChartedSpace H'' N'] {I' : ModelWithCorners ℝ E' H'}
    {J' : ModelWithCorners ℝ F' H''} [I'.Boundaryless] [J'.Boundaryless] [IsManifold I' ∞ M']
    [IsManifold J' ∞ N'] [T2Space M'] [SigmaCompactSpace M'] [T2Space N']
    (f : M' → N') (hf : ContMDiff I' J' ∞ f) (hproper : IsProperMap f)
    (hreg : ∀ x, Surjective (mfderiv I' J' f x)) (y : N') :
    ∃ (Q : TopologicalSpace.Opens N') (hy : y ∈ Q) (hQ : IsOpen (f ⁻¹' Q))
      (_ : ChartedSpace (Fin (Module.finrank ℝ E' - Module.finrank ℝ F') → ℝ) {x // f x = y})
      (Θ : Diffeomorph (𝓘(ℝ, Fin (Module.finrank ℝ E' - Module.finrank ℝ F') → ℝ).prod J') I'
        ({x : M' // f x = y} × Q) (⟨f ⁻¹' Q, hQ⟩ : TopologicalSpace.Opens M') ∞),
      (∀ p, f (Θ p).1 = p.2.1) ∧ ∀ x, (Θ (x, ⟨y, hy⟩)).1 = x.1 := by
  obtain ⟨Q, hy, Θ, h1, h2⟩ := ehresmann_local_triviality f hf hproper hreg y
  exact ⟨Q, hy, Q.isOpen.preimage hf.continuous,
    regularFiberChartedSpace f y hf (fun x _ => hreg x), Θ, h1, h2⟩

end Generic

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

namespace Gaf02Chain

variable {P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- **The adjusted circle coordinate is a submersion on the WHOLE original domain `Y_i`**
(B:6118–6121; TCP01's right inverse of norm `< 2`, `‖Dg_i − Dη_i‖ < c₃`). -/
theorem gaf07_circle_submersion_of_mem_GAFD (C : Gaf02Chain P Kj Ξ Γ S eg c cw)
    (hc : c 2 < 1 / 1000) (hβ : β 2 ≤ 1 / 10000000) (hd : γ + β 2 < 1 / 10)
    (i : P.toLocalChartFamily.circle.finite_centres.toFinset) {p : X}
    (hp : p ∈ gaf07CircleY_GAFC P i) :
    Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) (C.gaf07CircleCoord_GAFC i) p) := by
  have hj := (Set.Finite.mem_toFinset _).mp i.2
  have hri := hρ i.1
  obtain ⟨H, hH, hder⟩ := C.gaf07_circle_derivative_GAFC
  have key := tcp01_gram_right_inverse_FAM2 P hβ hd hj hp.1
  let _ := radialScaledBundle g (ρ i.1)⁻¹ (inv_pos.mpr hri)
  obtain ⟨-, R, hR, -, hR2⟩ := key
  refine surjective_of_right_inverse_perturbation_nu_GAFC
    (show E3 →L[ℝ] ℝ² from mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²)
      (cgpCoord P.toLocalChartFamily P.zero (.inl i)) p)
    (show E3 →L[ℝ] ℝ² from mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) (C.gaf07CircleCoord_GAFC i) p)
    R hR (fun v => Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner p v v)) (c := max H 0) (K := 2)
    (fun w => ?_) (fun v => ?_) (le_max_right _ _) ?_
  · have hn := norm_tangent_radialScaled_KA4 g hri p (R w)
    calc Real.sqrt _ = ‖R w‖ := hn.symm
      _ ≤ ‖R‖ * ‖w‖ := R.le_opNorm w
      _ ≤ 2 * ‖w‖ := mul_le_mul_of_nonneg_right hR2.le (norm_nonneg w)
  · refine (hder i p hp.1 (by linarith [hp.2]) v).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
  · have : max H 0 < 1 / 1000 := max_lt (hH.trans hc) (by norm_num)
    linarith

/-- **GAF07, `j = 1`: the whole adjusted level and the original level are ONE embedded manifold**
(FC34a; D2): for `‖a‖ < 4` there are a manifold `S` and smooth embeddings `ι₀, ι₁ : S → M` onto the
original circle fibre `{p ∈ Y_i | η_i(p) = a}` and onto the whole adjusted level
`{p ∈ Y_i | g_i(p) = a}` (both inside the buffered chart `Y_i`). -/
theorem gaf07_circle_level_pair_GAFD (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (hc : c 2 < 1 / 1000)
    (hβ : β 2 ≤ 1 / 10000000) (hd : γ + β 2 < 1 / 10)
    (i : P.toLocalChartFamily.circle.finite_centres.toFinset) {a : ℝ²} (ha : ‖a‖ < 4) :
    ∃ (S : Type) (_ : TopologicalSpace S)
      (_ : ChartedSpace (Fin (Module.finrank ℝ E3 - Module.finrank ℝ ℝ²) → ℝ) S)
      (_ : IsManifold 𝓘(ℝ, Fin (Module.finrank ℝ E3 - Module.finrank ℝ ℝ²) → ℝ) ∞ S)
      (ι₀ ι₁ : S → X),
      IsSmoothEmbedding 𝓘(ℝ, Fin (Module.finrank ℝ E3 - Module.finrank ℝ ℝ²) → ℝ) 𝓘(ℝ, E3) ∞ ι₀ ∧
      IsSmoothEmbedding 𝓘(ℝ, Fin (Module.finrank ℝ E3 - Module.finrank ℝ ℝ²) → ℝ) 𝓘(ℝ, E3) ∞ ι₁ ∧
      range ι₀ = {p | p ∈ gaf07CircleY_GAFC P i ∧
        cgpCoord P.toLocalChartFamily P.zero (.inl i) p = a} ∧
      range ι₁ = {p | p ∈ gaf07CircleY_GAFC P i ∧ C.gaf07CircleCoord_GAFC i p = a} := by
  have hj := (Set.Finite.mem_toFinset _).mp i.2
  have hri := hρ i.1
  obtain ⟨H, hH, hder⟩ := C.gaf07_circle_derivative_GAFC
  have hU := isOpen_gaf07CircleY_GAFC P i
  have hη : ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) ∞ (cgpCoord P.toLocalChartFamily P.zero (.inl i))
      (gaf07CircleY_GAFC P i) :=
    (cgpCircleCoord_contMDiffOn P.toLocalChartFamily hj).mono fun x hx => hx.1
  have hg : ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) ∞ (C.gaf07CircleCoord_GAFC i)
      (gaf07CircleY_GAFC P i) :=
    (C.gaf07_circle_smooth_GAFC i).2.contMDiffOn
  have hgη : ∀ y ∈ gaf07CircleY_GAFC P i,
      ‖C.gaf07CircleCoord_GAFC i y - cgpCoord P.toLocalChartFamily P.zero (.inl i) y‖ < 1 / 800 :=
    fun y hy => (C.gaf07_circle_coordinate_G47 hc i hy.1 hy.2).1
  have hcK : max H 0 * 2 < 1 := by
    have : max H 0 < 1 / 1000 := max_lt (hH.trans hc) (by norm_num)
    linarith
  have hright : ∀ y ∈ gaf07CircleY_GAFC P i, ∃ R : ℝ² →L[ℝ] E3,
      (show E3 →L[ℝ] ℝ² from mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²)
        (cgpCoord P.toLocalChartFamily P.zero (.inl i)) y).comp R =
          ContinuousLinearMap.id ℝ ℝ² ∧
        ∀ w, Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner y (R w) (R w)) ≤ 2 * ‖w‖ := by
    intro y hy
    have key := tcp01_gram_right_inverse_FAM2 P hβ hd hj hy.1
    let _ := radialScaledBundle g (ρ i.1)⁻¹ (inv_pos.mpr hri)
    obtain ⟨-, R, hR, -, hR2⟩ := key
    refine ⟨R, hR, fun w => ?_⟩
    have hn := norm_tangent_radialScaled_KA4 g hri y (R w)
    calc Real.sqrt _ = ‖R w‖ := hn.symm
      _ ≤ ‖R‖ * ‖w‖ := R.le_opNorm w
      _ ≤ 2 * ‖w‖ := mul_le_mul_of_nonneg_right hR2.le (norm_nonneg w)
  have hDg : ∀ y ∈ gaf07CircleY_GAFC P i, ∀ v : E3,
      ‖(show E3 →L[ℝ] ℝ² from mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) (C.gaf07CircleCoord_GAFC i) y) v -
        (show E3 →L[ℝ] ℝ² from mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²)
          (cgpCoord P.toLocalChartFamily P.zero (.inl i)) y) v‖ ≤
        max H 0 * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner y v v) := by
    intro y hy v
    refine (hder i y hy.1 (by linarith [hy.2]) v).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
  have hQ : IsCompact {y | y ∈ gaf07CircleY_GAFC P i ∧
      ‖cgpCoord P.toLocalChartFamily P.zero (.inl i) y‖ ≤ 401 / 100 * 1} := by
    convert isCompact_circleSlab_GAFC P i (a := 401 / 100) (by norm_num) using 1
    ext x
    constructor
    · rintro ⟨⟨hx, -⟩, hxa⟩
      exact ⟨hx, by linarith⟩
    · rintro ⟨hx, hxa⟩
      exact ⟨⟨hx, by linarith⟩, by linarith⟩
  have hdim : Module.finrank ℝ ℝ² < Module.finrank ℝ E3 := by
    simp only [finrank_euclideanSpace_fin]
    norm_num
  exact exists_embedding_pair_level_on_open_GAFD hdim hU hη hg le_rfl (by linarith) hgη
    (fun y v => Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner y v v)) (le_max_right _ _) hcK hright hDg hQ

/-- **GAF07, `j = 3`: the whole adjusted slim level and the original slim level are ONE embedded
surface** (FC34a; D2): for `|a| < 4·10⁵Δ` there are a manifold `S` and smooth embeddings
`ι₀, ι₁ : S → M` onto `{p ∈ Y_i | η_i(p) = a}` and onto `{p ∈ Y_i | g_i(p) = a}`. -/
theorem gaf07_slim_level_pair_GAFD (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (hc : c 2 < 1 / 1000)
    (i : P.toLocalChartFamily.slim.finite_centres.toFinset) {a : ℝ}
    (ha : |a| < 4 * (10 ^ 5 * Δ)) :
    ∃ (S : Type) (_ : TopologicalSpace S)
      (_ : ChartedSpace (Fin (Module.finrank ℝ E3 - Module.finrank ℝ ℝ) → ℝ) S)
      (_ : IsManifold 𝓘(ℝ, Fin (Module.finrank ℝ E3 - Module.finrank ℝ ℝ) → ℝ) ∞ S)
      (ι₀ ι₁ : S → X),
      IsSmoothEmbedding 𝓘(ℝ, Fin (Module.finrank ℝ E3 - Module.finrank ℝ ℝ) → ℝ) 𝓘(ℝ, E3) ∞ ι₀ ∧
      IsSmoothEmbedding 𝓘(ℝ, Fin (Module.finrank ℝ E3 - Module.finrank ℝ ℝ) → ℝ) 𝓘(ℝ, E3) ∞ ι₁ ∧
      range ι₀ = {p | p ∈ gaf07SlimY_GAFC P i ∧
        (P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p = a} ∧
      range ι₁ = {p | p ∈ gaf07SlimY_GAFC P i ∧ C.gaf07SlimCoord_GAFC i p = a} := by
  have hj := (Set.Finite.mem_toFinset _).mp i.2
  set cc := P.slim.centre i.1 hj with hcc
  have hri := hρ i.1
  obtain ⟨-, hΔ1, -⟩ := C.std
  have hΔ0 : (0 : ℝ) < Δ := by linarith
  have hℓ : (1 : ℝ) ≤ 10 ^ 5 * Δ := by nlinarith
  have hball : ball i.1 (1000000 * Δ * ρ i.1) = ball i.1 (10 ^ 6 * Δ * ρ i.1) := by norm_num
  obtain ⟨H, hH, hder⟩ := C.gaf07_slim_derivative_GAFC
  have hU := isOpen_gaf07SlimY_GAFC P i
  have hη : ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ cc.coord (gaf07SlimY_GAFC P i) :=
    cc.contMDiffOn_coord.mono fun x hx => hball ▸ hx.1
  have hg : ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (C.gaf07SlimCoord_GAFC i) (gaf07SlimY_GAFC P i) :=
    (C.gaf07_slim_smooth_GAFC i).2.contMDiffOn
  have hgη : ∀ y ∈ gaf07SlimY_GAFC P i, ‖C.gaf07SlimCoord_GAFC i y - cc.coord y‖ < 1 / 800 := by
    intro y hy
    rw [Real.norm_eq_abs]
    exact C.gaf07_slim_axis_value_GAFC hc i hy.1 hy.2
  have hcK : max H 0 * (4 / 3) < 1 := by
    have : max H 0 < 1 / 1000 := max_lt (hH.trans hc) (by norm_num)
    linarith
  have hright : ∀ y ∈ gaf07SlimY_GAFC P i, ∃ R : ℝ →L[ℝ] E3,
      (show E3 →L[ℝ] ℝ from mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) cc.coord y).comp R =
          ContinuousLinearMap.id ℝ ℝ ∧
        ∀ w, Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner y (R w) (R w)) ≤ 4 / 3 * ‖w‖ := by
    intro y hy
    have hyd : dist y i.1 < 91 / 100 * (10 ^ 6 * Δ) * ρ i.1 :=
      cc.dist_lt_of_abs_coord_le_ZERO (hball ▸ hy.1) (by nlinarith [hy.2, abs_nonneg (cc.coord y)])
    obtain ⟨w, hw1, hw⟩ := cc.derivative_GAFC hyd
    set d : ℝ := mvfderiv 𝓘(ℝ, E3) cc.coord y w with hd
    have hd0 : 0 < d := by linarith
    refine ⟨ContinuousLinearMap.toSpanSingleton ℝ (d⁻¹ • w), ?_, fun t => ?_⟩
    · refine ContinuousLinearMap.ext fun t => ?_
      change (mvfderiv 𝓘(ℝ, E3) cc.coord y) (t • d⁻¹ • w) = t
      rw [map_smul, map_smul, ← hd, smul_eq_mul, smul_eq_mul, inv_mul_cancel₀ hd0.ne', mul_one]
    · change Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner y (t • d⁻¹ • w) (t • d⁻¹ • w)) ≤ 4 / 3 * ‖t‖
      have hsc : g.inner y (t • d⁻¹ • w) (t • d⁻¹ • w) = (t * d⁻¹) ^ 2 * g.inner y w w := by
        rw [smul_smul, map_smul, map_smul]
        simp only [smul_apply, smul_eq_mul]
        ring
      rw [hsc, show (ρ i.1)⁻¹ ^ 2 * ((t * d⁻¹) ^ 2 * g.inner y w w) =
        (t * d⁻¹) ^ 2 * ((ρ i.1)⁻¹ ^ 2 * g.inner y w w) by ring, hw1, mul_one,
        Real.sqrt_sq_eq_abs, abs_mul, abs_of_pos (inv_pos.mpr hd0), Real.norm_eq_abs]
      have h43 : d⁻¹ ≤ 4 / 3 := by
        rw [inv_le_comm₀ hd0 (by norm_num)]
        linarith
      calc |t| * d⁻¹ ≤ |t| * (4 / 3) := mul_le_mul_of_nonneg_left h43 (abs_nonneg t)
        _ = 4 / 3 * |t| := by ring
  have hDg : ∀ y ∈ gaf07SlimY_GAFC P i, ∀ v : E3,
      ‖(show E3 →L[ℝ] ℝ from mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (C.gaf07SlimCoord_GAFC i) y) v -
        (show E3 →L[ℝ] ℝ from mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) cc.coord y) v‖ ≤
        max H 0 * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner y v v) := by
    intro y hy v
    rw [Real.norm_eq_abs]
    refine (hder i y hy.1 (by nlinarith [hy.2]) v).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
  have hQ : IsCompact {y | y ∈ gaf07SlimY_GAFC P i ∧ ‖cc.coord y‖ ≤ 401 / 100 * (10 ^ 5 * Δ)} := by
    convert isCompact_slimSlab_GAFS P.toLocalChartFamily hΔ0 i
      (a := 401 / 100 * (10 ^ 5 * Δ)) (by nlinarith) using 1
    ext x
    simp only [Set.mem_ofPred_eq, Real.norm_eq_abs]
    constructor
    · rintro ⟨⟨hx, -⟩, hxa⟩
      exact ⟨hball ▸ hx, hxa⟩
    · rintro ⟨hx, hxa⟩
      exact ⟨⟨hball ▸ hx, by nlinarith⟩, hxa⟩
  have hdim : Module.finrank ℝ ℝ < Module.finrank ℝ E3 := by
    simp only [finrank_euclideanSpace_fin, Module.finrank_self]
    norm_num
  exact exists_embedding_pair_level_on_open_GAFD hdim hU hη hg hℓ
    (by rw [Real.norm_eq_abs]; exact ha) hgη
    (fun y v => Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner y v v)) (le_max_right _ _) hcK hright hDg hQ

/-- The open source of the circle base chart map: `{p ∈ Y_i | ‖g_i(p)‖ < 4}` is open. -/
theorem isOpen_gaf07CircleChartSource_GAFD (C : Gaf02Chain P Kj Ξ Γ S eg c cw)
    (i : P.toLocalChartFamily.circle.finite_centres.toFinset) :
    IsOpen {p | p ∈ gaf07CircleY_GAFC P i ∧ ‖C.gaf07CircleCoord_GAFC i p‖ < 4} :=
  (isOpen_gaf07CircleY_GAFC P i).inter
    (isOpen_lt (C.gaf07_circle_smooth_GAFC i).2.continuous.norm continuous_const)

/-- **GAF07, `j = 1`, the bundle in the base chart** (B:6092–6103; D1): with `κ_i = R_i⁻¹u_i`,
`g_i = κ_i ∘ π₁E` maps the open set `{p ∈ Y_i | ‖g_i(p)‖ < 4}` (the whole preimage of the base piece
`B₁^i`, `gaf07_circle_piece_GAFD`) to the ball `B(0, 4)`, and this map between open submanifolds of
`M` and `ℝ²` is smooth, PROPER, SURJECTIVE and a SUBMERSION at every point. -/
theorem gaf07_circle_chart_map_GAFD (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (hc : c 2 < 1 / 1000)
    (hβ : β 2 ≤ 1 / 10000000) (hd : γ + β 2 < 1 / 10)
    (i : P.toLocalChartFamily.circle.finite_centres.toFinset) :
    ∃ hmaps : ∀ p ∈ {p | p ∈ gaf07CircleY_GAFC P i ∧ ‖C.gaf07CircleCoord_GAFC i p‖ < 4},
        C.gaf07CircleCoord_GAFC i p ∈ ball (0 : ℝ²) 4,
      ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) ∞
          (fun x : (⟨_, C.isOpen_gaf07CircleChartSource_GAFD i⟩ : TopologicalSpace.Opens X) =>
            (⟨C.gaf07CircleCoord_GAFC i x, hmaps x x.2⟩ :
              (⟨ball (0 : ℝ²) 4, isOpen_ball⟩ : TopologicalSpace.Opens ℝ²))) ∧
        IsProperMap
          (fun x : (⟨_, C.isOpen_gaf07CircleChartSource_GAFD i⟩ : TopologicalSpace.Opens X) =>
            (⟨C.gaf07CircleCoord_GAFC i x, hmaps x x.2⟩ :
              (⟨ball (0 : ℝ²) 4, isOpen_ball⟩ : TopologicalSpace.Opens ℝ²))) ∧
        Surjective
          (fun x : (⟨_, C.isOpen_gaf07CircleChartSource_GAFD i⟩ : TopologicalSpace.Opens X) =>
            (⟨C.gaf07CircleCoord_GAFC i x, hmaps x x.2⟩ :
              (⟨ball (0 : ℝ²) 4, isOpen_ball⟩ : TopologicalSpace.Opens ℝ²))) ∧
        ∀ x, Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²)
          (fun x : (⟨_, C.isOpen_gaf07CircleChartSource_GAFD i⟩ : TopologicalSpace.Opens X) =>
            (⟨C.gaf07CircleCoord_GAFC i x, hmaps x x.2⟩ :
              (⟨ball (0 : ℝ²) 4, isOpen_ball⟩ : TopologicalSpace.Opens ℝ²))) x) := by
  have hmaps : ∀ p ∈ {p | p ∈ gaf07CircleY_GAFC P i ∧ ‖C.gaf07CircleCoord_GAFC i p‖ < 4},
      C.gaf07CircleCoord_GAFC i p ∈ ball (0 : ℝ²) 4 := fun p hp => mem_ball_zero_iff.mpr hp.2
  have hgc : Continuous (C.gaf07CircleCoord_GAFC i) := (C.gaf07_circle_smooth_GAFC i).2.continuous
  have hprop : ∀ Kc ⊆ ball (0 : ℝ²) 4, IsCompact Kc →
      IsCompact {x | x ∈ {p | p ∈ gaf07CircleY_GAFC P i ∧ ‖C.gaf07CircleCoord_GAFC i p‖ < 4} ∧
        C.gaf07CircleCoord_GAFC i x ∈ Kc} := by
    intro Kc hKc hK
    have hQ := isCompact_circleSlab_GAFC P i (a := 401 / 100) (by norm_num)
    convert hQ.inter_right (hK.isClosed.preimage hgc) using 1
    ext x
    constructor
    · rintro ⟨⟨hxY, -⟩, hxK⟩
      have h1 := (C.gaf07_circle_coordinate_G47 hc i hxY.1 hxY.2).1
      have h2 : ‖C.gaf07CircleCoord_GAFC i x‖ < 4 := mem_ball_zero_iff.mp (hKc hxK)
      have h3 := norm_sub_norm_le (cgpCoord P.toLocalChartFamily P.zero (.inl i) x)
        (C.gaf07CircleCoord_GAFC i x)
      rw [norm_sub_rev] at h3
      refine ⟨⟨hxY.1, ?_⟩, hxK⟩
      have h1' : ‖C.gaf07CircleCoord_GAFC i x -
          cgpCoord P.toLocalChartFamily P.zero (.inl i) x‖ < 1 / 800 := h1
      linarith
    · rintro ⟨⟨hx, hxη⟩, hxK⟩
      exact ⟨⟨⟨hx, by linarith⟩, mem_ball_zero_iff.mp (hKc hxK)⟩, hxK⟩
  have hsurj : ∀ y ∈ ball (0 : ℝ²) 4, ∃ x ∈ {p | p ∈ gaf07CircleY_GAFC P i ∧
      ‖C.gaf07CircleCoord_GAFC i p‖ < 4}, C.gaf07CircleCoord_GAFC i x = y := by
    intro y hy
    have hy' : ‖y‖ < 4 := mem_ball_zero_iff.mp hy
    obtain ⟨x, hxY, hxy⟩ := (C.gaf07_circle_level_GAFC hc hβ hd i hy').2.1.nonempty
    exact ⟨x, ⟨hxY, by rw [hxy]; exact hy'⟩, hxy⟩
  exact ⟨hmaps, chart_bundle_of_open_GAFD (C.isOpen_gaf07CircleChartSource_GAFD i) isOpen_ball
    (C.gaf07_circle_smooth_GAFC i).2.contMDiffOn hmaps
    (fun x hx => C.gaf07_circle_submersion_of_mem_GAFD hc hβ hd i hx.1) hprop hsurj⟩

/-- The open source of the slim base chart map: `{p ∈ Y_i | |g_i(p)| < 4·10⁵Δ}` is open. -/
theorem isOpen_gaf07SlimChartSource_GAFD (C : Gaf02Chain P Kj Ξ Γ S eg c cw)
    (i : P.toLocalChartFamily.slim.finite_centres.toFinset) :
    IsOpen {p | p ∈ gaf07SlimY_GAFC P i ∧ |C.gaf07SlimCoord_GAFC i p| < 4 * (10 ^ 5 * Δ)} :=
  (isOpen_gaf07SlimY_GAFC P i).inter
    (isOpen_lt (C.gaf07_slim_smooth_GAFC i).2.continuous.abs continuous_const)

/-- **GAF07, `j = 3`, the bundle in the base chart** (B:6092–6103; D1): with BASES' axis chart
`κ_i = R_i⁻¹ axis u_i`, `g_i = κ_i ∘ π₃E` maps the open set `{p ∈ Y_i | |g_i(p)| < 4·10⁵Δ}` (the
whole preimage of the base piece `B₃^i`, `gaf07_slim_piece_GAFD`) to `B(0, 4·10⁵Δ) ⊂ ℝ`, and this
map between open submanifolds is smooth, PROPER, SURJECTIVE and a SUBMERSION at every point. -/
theorem gaf07_slim_chart_map_GAFD (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (hc : c 2 < 1 / 1000)
    (i : P.toLocalChartFamily.slim.finite_centres.toFinset) :
    ∃ hmaps : ∀ p ∈ {p | p ∈ gaf07SlimY_GAFC P i ∧ |C.gaf07SlimCoord_GAFC i p| < 4 * (10 ^ 5 * Δ)},
        C.gaf07SlimCoord_GAFC i p ∈ ball (0 : ℝ) (4 * (10 ^ 5 * Δ)),
      ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞
          (fun x : (⟨_, C.isOpen_gaf07SlimChartSource_GAFD i⟩ : TopologicalSpace.Opens X) =>
            (⟨C.gaf07SlimCoord_GAFC i x, hmaps x x.2⟩ :
              (⟨ball (0 : ℝ) (4 * (10 ^ 5 * Δ)), isOpen_ball⟩ : TopologicalSpace.Opens ℝ))) ∧
        IsProperMap
          (fun x : (⟨_, C.isOpen_gaf07SlimChartSource_GAFD i⟩ : TopologicalSpace.Opens X) =>
            (⟨C.gaf07SlimCoord_GAFC i x, hmaps x x.2⟩ :
              (⟨ball (0 : ℝ) (4 * (10 ^ 5 * Δ)), isOpen_ball⟩ : TopologicalSpace.Opens ℝ))) ∧
        Surjective
          (fun x : (⟨_, C.isOpen_gaf07SlimChartSource_GAFD i⟩ : TopologicalSpace.Opens X) =>
            (⟨C.gaf07SlimCoord_GAFC i x, hmaps x x.2⟩ :
              (⟨ball (0 : ℝ) (4 * (10 ^ 5 * Δ)), isOpen_ball⟩ : TopologicalSpace.Opens ℝ))) ∧
        ∀ x, Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ)
          (fun x : (⟨_, C.isOpen_gaf07SlimChartSource_GAFD i⟩ : TopologicalSpace.Opens X) =>
            (⟨C.gaf07SlimCoord_GAFC i x, hmaps x x.2⟩ :
              (⟨ball (0 : ℝ) (4 * (10 ^ 5 * Δ)), isOpen_ball⟩ : TopologicalSpace.Opens ℝ))) x) := by
  obtain ⟨-, hΔ1, -⟩ := C.std
  have hΔ0 : (0 : ℝ) < Δ := by linarith
  have hball : ball i.1 (1000000 * Δ * ρ i.1) = ball i.1 (10 ^ 6 * Δ * ρ i.1) := by norm_num
  have hmaps : ∀ p ∈ {p | p ∈ gaf07SlimY_GAFC P i ∧
      |C.gaf07SlimCoord_GAFC i p| < 4 * (10 ^ 5 * Δ)},
      C.gaf07SlimCoord_GAFC i p ∈ ball (0 : ℝ) (4 * (10 ^ 5 * Δ)) := fun p hp => by
    rw [mem_ball_zero_iff, Real.norm_eq_abs]
    exact hp.2
  have hgc : Continuous (C.gaf07SlimCoord_GAFC i) := (C.gaf07_slim_smooth_GAFC i).2.continuous
  have hprop : ∀ Kc ⊆ ball (0 : ℝ) (4 * (10 ^ 5 * Δ)), IsCompact Kc →
      IsCompact {x | x ∈ {p | p ∈ gaf07SlimY_GAFC P i ∧
        |C.gaf07SlimCoord_GAFC i p| < 4 * (10 ^ 5 * Δ)} ∧ C.gaf07SlimCoord_GAFC i x ∈ Kc} := by
    intro Kc hKc hK
    have hQ := isCompact_slimSlab_GAFS P.toLocalChartFamily hΔ0 i
      (a := 401 / 100 * (10 ^ 5 * Δ)) (by nlinarith)
    convert hQ.inter_right (hK.isClosed.preimage hgc) using 1
    ext x
    constructor
    · rintro ⟨⟨hxY, -⟩, hxK⟩
      have h1 := C.gaf07_slim_axis_value_GAFC hc i hxY.1 hxY.2
      have h2 : |C.gaf07SlimCoord_GAFC i x| < 4 * (10 ^ 5 * Δ) := by
        have := hKc hxK
        rwa [mem_ball_zero_iff, Real.norm_eq_abs] at this
      have h1' : |C.gaf07SlimCoord_GAFC i x -
          (P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x| < 1 / 800 := h1
      refine ⟨⟨hball ▸ hxY.1, ?_⟩, hxK⟩
      have h3 := abs_sub_abs_le_abs_sub
        ((P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x)
        (C.gaf07SlimCoord_GAFC i x)
      rw [abs_sub_comm] at h3
      nlinarith
    · rintro ⟨⟨hx, hxη⟩, hxK⟩
      have h2 := hKc hxK
      rw [mem_ball_zero_iff, Real.norm_eq_abs] at h2
      exact ⟨⟨⟨hball ▸ hx, by nlinarith⟩, h2⟩, hxK⟩
  have hsurj : ∀ y ∈ ball (0 : ℝ) (4 * (10 ^ 5 * Δ)), ∃ x ∈ {p | p ∈ gaf07SlimY_GAFC P i ∧
      |C.gaf07SlimCoord_GAFC i p| < 4 * (10 ^ 5 * Δ)}, C.gaf07SlimCoord_GAFC i x = y := by
    intro y hy
    have hy' : |y| < 4 * (10 ^ 5 * Δ) := by rwa [mem_ball_zero_iff, Real.norm_eq_abs] at hy
    obtain ⟨x, hxY, hxy⟩ := (C.gaf07_slim_level_GAFC hc i hy').2.1.nonempty
    exact ⟨x, ⟨hxY, by rw [hxy]; exact hy'⟩, hxy⟩
  exact ⟨hmaps, chart_bundle_of_open_GAFD (C.isOpen_gaf07SlimChartSource_GAFD i) isOpen_ball
    (C.gaf07_slim_smooth_GAFC i).2.contMDiffOn hmaps
    (fun x hx => C.gaf07_slim_submersion_of_mem_GAFD hc i hx.1) hprop hsurj⟩

/-- **GAF07, `j = 1`, local trivializations** (B:6102–6103, "the inherited smooth
proper-submersion result supplies its local trivializations"; D1): over every point `y` of the
base chart ball `B(0, 4)` (= `κ_i(B₁^i)`) there are an open `Q ∋ y` and a diffeomorphism
`Θ : g_i⁻¹(y) × Q ≃ₘ g_i⁻¹(Q)` with `g_i ∘ Θ = pr₂`, the identity on the fibre over `y`
(`g_i = κ_i ∘ π₁E` on `{p ∈ Y_i | ‖g_i(p)‖ < 4}`, whose fibres are the whole fibres of `π₁E`). -/
theorem gaf07_circle_local_trivial_GAFD (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (hc : c 2 < 1 / 1000)
    (hβ : β 2 ≤ 1 / 10000000) (hd : γ + β 2 < 1 / 10)
    (i : P.toLocalChartFamily.circle.finite_centres.toFinset) :
    ∃ hmaps : ∀ p ∈ {p | p ∈ gaf07CircleY_GAFC P i ∧ ‖C.gaf07CircleCoord_GAFC i p‖ < 4},
        C.gaf07CircleCoord_GAFC i p ∈ ball (0 : ℝ²) 4,
      let fW : (⟨_, C.isOpen_gaf07CircleChartSource_GAFD i⟩ : TopologicalSpace.Opens X) →
          (⟨ball (0 : ℝ²) 4, isOpen_ball⟩ : TopologicalSpace.Opens ℝ²) :=
        fun x => ⟨C.gaf07CircleCoord_GAFC i x, hmaps x x.2⟩
      ∀ y, ∃ (Q : TopologicalSpace.Opens (⟨ball (0 : ℝ²) 4, isOpen_ball⟩ :
          TopologicalSpace.Opens ℝ²)) (hy : y ∈ Q) (hQ : IsOpen (fW ⁻¹' Q))
        (_ : ChartedSpace (Fin (Module.finrank ℝ E3 - Module.finrank ℝ ℝ²) → ℝ) {x // fW x = y})
        (Θ : Diffeomorph (𝓘(ℝ, Fin (Module.finrank ℝ E3 - Module.finrank ℝ ℝ²) → ℝ).prod
            𝓘(ℝ, ℝ²)) 𝓘(ℝ, E3) ({x // fW x = y} × Q) (⟨fW ⁻¹' Q, hQ⟩ :
              TopologicalSpace.Opens (⟨_, C.isOpen_gaf07CircleChartSource_GAFD i⟩ :
                TopologicalSpace.Opens X)) ∞),
        (∀ p, fW (Θ p).1 = p.2.1) ∧ ∀ x, (Θ (x, ⟨y, hy⟩)).1 = x.1 := by
  obtain ⟨hmaps, hsm, hpr, -, hreg⟩ := C.gaf07_circle_chart_map_GAFD hc hβ hd i
  have : LocallyCompactSpace
      (⟨_, C.isOpen_gaf07CircleChartSource_GAFD i⟩ : TopologicalSpace.Opens X) :=
    (C.isOpen_gaf07CircleChartSource_GAFD i).locallyCompactSpace
  exact ⟨hmaps, fun y => local_trivial_of_proper_submersion_GAFD _ hsm hpr hreg y⟩

/-- **GAF07, `j = 3`, local trivializations** (B:6102–6103; D1): over every point `y` of the base
chart interval `B(0, 4·10⁵Δ)` there are an open `Q ∋ y` and a diffeomorphism
`Θ : g_i⁻¹(y) × Q ≃ₘ g_i⁻¹(Q)` with `g_i ∘ Θ = pr₂`, the identity on the fibre over `y`. -/
theorem gaf07_slim_local_trivial_GAFD (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (hc : c 2 < 1 / 1000)
    (i : P.toLocalChartFamily.slim.finite_centres.toFinset) :
    ∃ hmaps : ∀ p ∈ {p | p ∈ gaf07SlimY_GAFC P i ∧ |C.gaf07SlimCoord_GAFC i p| < 4 * (10 ^ 5 * Δ)},
        C.gaf07SlimCoord_GAFC i p ∈ ball (0 : ℝ) (4 * (10 ^ 5 * Δ)),
      let fW : (⟨_, C.isOpen_gaf07SlimChartSource_GAFD i⟩ : TopologicalSpace.Opens X) →
          (⟨ball (0 : ℝ) (4 * (10 ^ 5 * Δ)), isOpen_ball⟩ : TopologicalSpace.Opens ℝ) :=
        fun x => ⟨C.gaf07SlimCoord_GAFC i x, hmaps x x.2⟩
      ∀ y, ∃ (Q : TopologicalSpace.Opens (⟨ball (0 : ℝ) (4 * (10 ^ 5 * Δ)), isOpen_ball⟩ :
          TopologicalSpace.Opens ℝ)) (hy : y ∈ Q) (hQ : IsOpen (fW ⁻¹' Q))
        (_ : ChartedSpace (Fin (Module.finrank ℝ E3 - Module.finrank ℝ ℝ) → ℝ) {x // fW x = y})
        (Θ : Diffeomorph (𝓘(ℝ, Fin (Module.finrank ℝ E3 - Module.finrank ℝ ℝ) → ℝ).prod
            𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) ({x // fW x = y} × Q) (⟨fW ⁻¹' Q, hQ⟩ :
              TopologicalSpace.Opens (⟨_, C.isOpen_gaf07SlimChartSource_GAFD i⟩ :
                TopologicalSpace.Opens X)) ∞),
        (∀ p, fW (Θ p).1 = p.2.1) ∧ ∀ x, (Θ (x, ⟨y, hy⟩)).1 = x.1 := by
  obtain ⟨hmaps, hsm, hpr, -, hreg⟩ := C.gaf07_slim_chart_map_GAFD hc i
  have : LocallyCompactSpace
      (⟨_, C.isOpen_gaf07SlimChartSource_GAFD i⟩ : TopologicalSpace.Opens X) :=
    (C.isOpen_gaf07SlimChartSource_GAFD i).locallyCompactSpace
  exact ⟨hmaps, fun y => local_trivial_of_proper_submersion_GAFD _ hsm hpr hreg y⟩

/-- Every adjusted circle level `‖a‖ < 4` meets `Y_i` (it is connected, hence nonempty). -/
theorem gaf07_circle_level_nonempty_GAFD (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (hc : c 2 < 1 / 1000)
    (hβ : β 2 ≤ 1 / 10000000) (hd : γ + β 2 < 1 / 10)
    (i : P.toLocalChartFamily.circle.finite_centres.toFinset) {a : ℝ²} (ha : ‖a‖ < 4) :
    ∃ p, p ∈ gaf07CircleY_GAFC P i ∧ C.gaf07CircleCoord_GAFC i p = a :=
  (C.gaf07_circle_level_GAFC hc hβ hd i ha).2.1.nonempty

/-- Every adjusted slim level `|a| < 4·10⁵Δ` meets `Y_i`. -/
theorem gaf07_slim_level_nonempty_GAFD (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (hc : c 2 < 1 / 1000)
    (i : P.toLocalChartFamily.slim.finite_centres.toFinset) {a : ℝ}
    (ha : |a| < 4 * (10 ^ 5 * Δ)) :
    ∃ p, p ∈ gaf07SlimY_GAFC P i ∧ C.gaf07SlimCoord_GAFC i p = a :=
  (C.gaf07_slim_level_GAFC hc i ha).2.1.nonempty

end Gaf02Chain

namespace Gaf02ChainE

variable {vs ζ Λz : ℝ}
  {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
    V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- **GAF07, `j = 1`: the whole preimage of the base piece** `B₁^i = W₁ ∩ {v_i > .9R_i,
‖u_i‖ < 4v_i}`: `(π₁E)⁻¹(B₁^i) = {p ∈ Y_i | ‖g_i(p)‖ < 4}` (GAF06 one way, CGP08 + GAF05's marker
`R_i` the other way). -/
theorem gaf07_circle_piece_preimage_GAFD (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (hc : c 2 < 1 / 1000) (i : P.toLocalChartFamily.circle.finite_centres.toFinset) :
    (fun p => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p)) ⁻¹'
        (C.toChain.finalBase_BAS 0 ∩
          {w | 9 / 10 * ρ i.1 < gafCircleMarker P.toLocalChartPackets i w ∧
          ‖gafCircleVector P.toLocalChartPackets i w‖ <
            4 * gafCircleMarker P.toLocalChartPackets i w}) =
      {p | p ∈ gaf07CircleY_GAFC P.toLocalChartPackets i ∧
        ‖C.toChain.gaf07CircleCoord_GAFC i p‖ < 4} := by
  have hri := hρ i.1
  have hπ : ∀ y, (gafStageQ P.toLocalChartFamily P.zero 0).starProjection y = y :=
    gafStageQ_zero_starProjection_BAS P.toLocalChartPackets
  -- the final image of a point of `Y_i` is in `W₁ ∩ {marked i}` with marker `R_i`
  have hmark : ∀ p ∈ gaf07CircleY_GAFC P.toLocalChartPackets i,
      (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p) ∈
          C.toChain.finalBase_BAS 0 ∩ markedCondition_BPRE (gafCircleVector P.toLocalChartPackets i)
            (gafCircleMarker P.toLocalChartPackets i) (ρ i.1) 1 ∧
        gafCircleMarker P.toLocalChartPackets i
          ((gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p)) = ρ i.1 :=
    fun p hp => ⟨C.final_mem_circleBase_GAFC i hp,
      C.gaf05_circleBase_marker_GAFC i _ (C.final_mem_circleBase_GAFC i hp)⟩
  have hg : ∀ p, C.toChain.gaf07CircleCoord_GAFC i p = ((ρ i.1)⁻¹ •
      gafCircleVector P.toLocalChartPackets i)
        ((gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p)) := fun p => rfl
  have hnorm : ∀ p, ‖C.toChain.gaf07CircleCoord_GAFC i p‖ = (ρ i.1)⁻¹ *
      ‖gafCircleVector P.toLocalChartPackets i
        ((gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p))‖ := fun p => by
    rw [hg, smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hri)]
  ext p
  constructor
  · rintro ⟨-, hm, hr⟩
    have hm1 : 9 / 10 * ρ i.1 < gafCircleMarker P.toLocalChartPackets i
        ((gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p)) := hm
    have hr1 : ‖gafCircleVector P.toLocalChartPackets i
        ((gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p))‖ <
        4 * gafCircleMarker P.toLocalChartPackets i
          ((gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p)) := hr
    have hm2 : 9 / 10 * ρ i.1 < blockMarkerCLM
        (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl i) (C.toChain.E p) := by
      have h := hm1
      rw [hπ] at h
      exact h
    have hr2 : ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl i)
        (C.toChain.E p)‖ ≤ 4 * blockMarkerCLM
          (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl i) (C.toChain.E p) := by
      have h := hr1
      rw [hπ] at h
      exact h.le
    obtain ⟨hpi, hη, -⟩ := C.toChain.gaf06_circle_G47 hc i p 1 ⟨zero_le_one, le_rfl⟩
      (by rw [C.toChain.segment_one_GAFD]; exact hm2)
      (by rw [C.toChain.segment_one_GAFD]; exact hr2)
    have hpY : p ∈ gaf07CircleY_GAFC P.toLocalChartPackets i := ⟨hpi, by linarith⟩
    refine ⟨hpY, ?_⟩
    rw [hnorm, inv_mul_lt_iff₀ hri]
    rw [(hmark p hpY).2] at hr1
    linarith
  · rintro ⟨hpY, hp4⟩
    obtain ⟨⟨hW, -⟩, hv⟩ := hmark p hpY
    refine ⟨hW, ?_, ?_⟩
    · change 9 / 10 * ρ i.1 < gafCircleMarker P.toLocalChartPackets i
        ((gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p))
      rw [hv]
      linarith
    · change ‖gafCircleVector P.toLocalChartPackets i
        ((gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p))‖ <
        4 * gafCircleMarker P.toLocalChartPackets i
          ((gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p))
      rw [hv]
      rw [hnorm, inv_mul_lt_iff₀ hri] at hp4
      linarith

/-- **GAF07, `j = 1`: the base piece `B₁^i` in BASES' chart and its whole preimage** (D1): for the
piece `B₁^i = W₁ ∩ {v_i > .9R_i, ‖u_i‖ < 4v_i}` of `B₁`, `(π₁E)⁻¹(B₁^i) = {p ∈ Y_i | ‖g_i(p)‖ < 4}`
and the base chart `κ_i = R_i⁻¹u_i` maps `B₁^i` bijectively onto `B(0, 4)`. -/
theorem gaf07_circle_piece_GAFD (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) (hc : c 2 < 1 / 1000)
    (hβ : β 2 ≤ 1 / 10000000) (hd : γ + β 2 < 1 / 10)
    (i : P.toLocalChartFamily.circle.finite_centres.toFinset) :
    (fun p => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p)) ⁻¹'
        (C.toChain.finalBase_BAS 0 ∩
          {w | 9 / 10 * ρ i.1 < gafCircleMarker P.toLocalChartPackets i w ∧
          ‖gafCircleVector P.toLocalChartPackets i w‖ <
            4 * gafCircleMarker P.toLocalChartPackets i w}) =
      {p | p ∈ gaf07CircleY_GAFC P.toLocalChartPackets i ∧
        ‖C.toChain.gaf07CircleCoord_GAFC i p‖ < 4} ∧
    BijOn ((ρ i.1)⁻¹ • gafCircleVector P.toLocalChartPackets i)
      (C.toChain.finalBase_BAS 0 ∩ {w | 9 / 10 * ρ i.1 < gafCircleMarker P.toLocalChartPackets i w ∧
        ‖gafCircleVector P.toLocalChartPackets i w‖ <
          4 * gafCircleMarker P.toLocalChartPackets i w}) (ball 0 4) := by
  have heq := C.gaf07_circle_piece_preimage_GAFD hc i
  have hg : ∀ p, C.toChain.gaf07CircleCoord_GAFC i p = ((ρ i.1)⁻¹ •
      gafCircleVector P.toLocalChartPackets i)
        ((gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p)) := fun p => rfl
  have hW : ∀ p ∈ gaf07CircleY_GAFC P.toLocalChartPackets i,
      (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p) ∈
          C.toChain.finalBase_BAS 0 ∩ markedCondition_BPRE (gafCircleVector P.toLocalChartPackets i)
            (gafCircleMarker P.toLocalChartPackets i) (ρ i.1) 1 :=
    fun p hp => C.final_mem_circleBase_GAFC i hp
  refine ⟨heq, ⟨?_, ?_, ?_⟩⟩
  · intro w hw
    obtain ⟨p, rfl⟩ := C.gaf07_circle_onto_GAFC w hw.1
    have hp : p ∈ {p | p ∈ gaf07CircleY_GAFC P.toLocalChartPackets i ∧
        ‖C.toChain.gaf07CircleCoord_GAFC i p‖ < 4} := by
      rw [← heq]
      exact hw
    rw [mem_ball_zero_iff, ← hg]
    exact hp.2
  · intro w₁ hw₁ w₂ hw₂ h12
    obtain ⟨p₁, rfl⟩ := C.gaf07_circle_onto_GAFC w₁ hw₁.1
    obtain ⟨p₂, rfl⟩ := C.gaf07_circle_onto_GAFC w₂ hw₂.1
    have hp₁ : p₁ ∈ {p | p ∈ gaf07CircleY_GAFC P.toLocalChartPackets i ∧
        ‖C.toChain.gaf07CircleCoord_GAFC i p‖ < 4} := by
      rw [← heq]
      exact hw₁
    have hp₂ : p₂ ∈ {p | p ∈ gaf07CircleY_GAFC P.toLocalChartPackets i ∧
        ‖C.toChain.gaf07CircleCoord_GAFC i p‖ < 4} := by
      rw [← heq]
      exact hw₂
    exact (C.gaf05_circleBase_chart_GAFC i).2.1.injOn (hW p₁ hp₁.1) (hW p₂ hp₂.1) h12
  · intro y hy
    have hy' : ‖y‖ < 4 := mem_ball_zero_iff.mp hy
    obtain ⟨p, hpY, hpy⟩ := C.toChain.gaf07_circle_level_nonempty_GAFD hc hβ hd i hy'
    have hp : p ∈ {p | p ∈ gaf07CircleY_GAFC P.toLocalChartPackets i ∧
        ‖C.toChain.gaf07CircleCoord_GAFC i p‖ < 4} := ⟨hpY, by rw [hpy]; exact hy'⟩
    rw [← heq] at hp
    exact ⟨_, hp, by rw [← hg]; exact hpy⟩

/-- **GAF07, `j = 3`: the whole preimage of the axis base piece** `B₃^i = W₃ ∩ {v_i > .9R_i,
|axis u_i| < 4·10⁵Δ v_i}`: `(π₃E)⁻¹(B₃^i) = {p ∈ Y_i | |g_i(p)| < 4·10⁵Δ}`. -/
theorem gaf07_slim_piece_preimage_GAFD (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (hc : c 2 < 1 / 1000) (i : P.toLocalChartFamily.slim.finite_centres.toFinset) :
    (fun p => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p)) ⁻¹'
        (C.toChain.finalBase_BAS 2 ∩
          {w | 9 / 10 * ρ i.1 < gafSlimMarker P.toLocalChartFamily P.zero i w ∧
          ‖(axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero i)) w‖ <
            4 * (10 ^ 5 * Δ) * gafSlimMarker P.toLocalChartFamily P.zero i w}) =
      {p | p ∈ gaf07SlimY_GAFC P.toLocalChartPackets i ∧
        |C.toChain.gaf07SlimCoord_GAFC i p| < 4 * (10 ^ 5 * Δ)} := by
  have hri := hρ i.1
  have hcoord := slim_retained_coord_eq_GAFC (P := P) i
  have hV : ∀ p ∈ gaf07SlimY_GAFC P.toLocalChartPackets i,
      (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p) ∈
        C.toChain.slimPatch_BAS i := fun p hp => by
    have h := C.toChain.slim_mem_patch_of_domain5_BAS i hp.1 hp.2
    rw [C.stageMap_two_eq_GAFC] at h
    exact h
  have hgabs : ∀ p, |C.toChain.gaf07SlimCoord_GAFC i p| = (ρ i.1)⁻¹ *
      ‖(axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero i))
        ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p))‖ := fun p => by
    have h := hcoord ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p))
    change |EuclideanSpace.proj (0 : Fin 2) ((ρ i.1)⁻¹ •
      blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inl i))
        ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p)))| = _
    rw [← h, smul_apply, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr hri), Real.norm_eq_abs]
  ext p
  constructor
  · rintro ⟨-, hm, hr⟩
    have hm1 : 9 / 10 * ρ i.1 < gafSlimMarker P.toLocalChartFamily P.zero i
        ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p)) := hm
    have hr1 : ‖(axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero i))
        ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p))‖ <
        4 * (10 ^ 5 * Δ) * gafSlimMarker P.toLocalChartFamily P.zero i
          ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p)) := hr
    have hpY := C.gaf07_slim_fibre_mem_Y_axis_GAFD hc _ i hm1 hr1 p rfl
    refine ⟨hpY, ?_⟩
    rw [hgabs, inv_mul_lt_iff₀ hri]
    rw [C.gaf05_slimPatch_marker_GAFC i _ (hV p hpY)] at hr1
    linarith
  · rintro ⟨hpY, hp4⟩
    have hv := C.gaf05_slimPatch_marker_GAFC i _ (hV p hpY)
    refine ⟨⟨_, mem_iUnion.mpr ⟨i, hV p hpY⟩, rfl⟩, ?_, ?_⟩
    · change 9 / 10 * ρ i.1 < gafSlimMarker P.toLocalChartFamily P.zero i
        ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p))
      rw [hv]
      linarith
    · change ‖(axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero i))
        ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p))‖ <
        4 * (10 ^ 5 * Δ) * gafSlimMarker P.toLocalChartFamily P.zero i
          ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p))
      rw [hv]
      rw [hgabs, inv_mul_lt_iff₀ hri] at hp4
      linarith

/-- **GAF07, `j = 3`: the axis base piece `B₃^i` in BASES' chart and its whole preimage** (D1):
`(π₃E)⁻¹(B₃^i) = {p ∈ Y_i | |g_i(p)| < 4·10⁵Δ}` and BASES' axis chart `κ_i = R_i⁻¹ axis u_i` maps
`B₃^i` bijectively onto `B(0, 4·10⁵Δ)`. -/
theorem gaf07_slim_piece_GAFD (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) (hc : c 2 < 1 / 1000)
    (i : P.toLocalChartFamily.slim.finite_centres.toFinset) :
    (fun p => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p)) ⁻¹'
        (C.toChain.finalBase_BAS 2 ∩
          {w | 9 / 10 * ρ i.1 < gafSlimMarker P.toLocalChartFamily P.zero i w ∧
          ‖(axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero i)) w‖ <
            4 * (10 ^ 5 * Δ) * gafSlimMarker P.toLocalChartFamily P.zero i w}) =
      {p | p ∈ gaf07SlimY_GAFC P.toLocalChartPackets i ∧
        |C.toChain.gaf07SlimCoord_GAFC i p| < 4 * (10 ^ 5 * Δ)} ∧
    BijOn ((ρ i.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero i))
      (C.toChain.finalBase_BAS 2 ∩
        {w | 9 / 10 * ρ i.1 < gafSlimMarker P.toLocalChartFamily P.zero i w ∧
        ‖(axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero i)) w‖ <
          4 * (10 ^ 5 * Δ) * gafSlimMarker P.toLocalChartFamily P.zero i w})
      (ball 0 (4 * (10 ^ 5 * Δ))) := by
  have heq := C.gaf07_slim_piece_preimage_GAFD hc i
  have hcoord := slim_retained_coord_eq_GAFC (P := P) i
  have hg : ∀ p, C.toChain.gaf07SlimCoord_GAFC i p = ((ρ i.1)⁻¹ •
      axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero i))
        ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p)) :=
    fun p => (hcoord _).symm
  have hV : ∀ p ∈ gaf07SlimY_GAFC P.toLocalChartPackets i,
      (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p) ∈
        C.toChain.slimPatch_BAS i := fun p hp => by
    have h := C.toChain.slim_mem_patch_of_domain5_BAS i hp.1 hp.2
    rw [C.stageMap_two_eq_GAFC] at h
    exact h
  refine ⟨heq, ⟨?_, ?_, ?_⟩⟩
  · intro w hw
    obtain ⟨p, rfl⟩ := C.gaf07_slim_onto_GAFC w hw.1
    have hp : p ∈ {p | p ∈ gaf07SlimY_GAFC P.toLocalChartPackets i ∧
        |C.toChain.gaf07SlimCoord_GAFC i p| < 4 * (10 ^ 5 * Δ)} := by
      rw [← heq]
      exact hw
    rw [mem_ball_zero_iff, ← hg, Real.norm_eq_abs]
    exact hp.2
  · intro w₁ hw₁ w₂ hw₂ h12
    obtain ⟨p₁, rfl⟩ := C.gaf07_slim_onto_GAFC w₁ hw₁.1
    obtain ⟨p₂, rfl⟩ := C.gaf07_slim_onto_GAFC w₂ hw₂.1
    have hp₁ : p₁ ∈ {p | p ∈ gaf07SlimY_GAFC P.toLocalChartPackets i ∧
        |C.toChain.gaf07SlimCoord_GAFC i p| < 4 * (10 ^ 5 * Δ)} := by
      rw [← heq]
      exact hw₁
    have hp₂ : p₂ ∈ {p | p ∈ gaf07SlimY_GAFC P.toLocalChartPackets i ∧
        |C.toChain.gaf07SlimCoord_GAFC i p| < 4 * (10 ^ 5 * Δ)} := by
      rw [← heq]
      exact hw₂
    exact (C.toChain.cgp07_slim_BAS C.rough i).1.injOn (hV p₁ hp₁.1) (hV p₂ hp₂.1) h12
  · intro y hy
    have hy' : |y| < 4 * (10 ^ 5 * Δ) := by rwa [mem_ball_zero_iff, Real.norm_eq_abs] at hy
    obtain ⟨p, hpY, hpy⟩ := C.toChain.gaf07_slim_level_nonempty_GAFD hc i hy'
    have hp : p ∈ {p | p ∈ gaf07SlimY_GAFC P.toLocalChartPackets i ∧
        |C.toChain.gaf07SlimCoord_GAFC i p| < 4 * (10 ^ 5 * Δ)} := ⟨hpY, by rw [hpy]; exact hy'⟩
    rw [← heq] at hp
    exact ⟨_, hp, by rw [← hg]; exact hpy⟩

end Gaf02ChainE

end DifferentialGeometry.Geometry.Collapse
