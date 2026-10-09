import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspCoreFlow

/-!
# BCG06, G3 (part 2): the relative supported flow on `W` (lane BCG6-Kb, review 65 M3(a)/(b))

The interior flow of `BoundaryCuspCoreFlow` is extended by the identity to the whole carrier `W`
(with its boundary): a compactly supported diffeomorphism of `W°` (interior atlas) is the identity
near `∂W`, so its extension is a diffeomorphism of `W` (model `W.model`), and the same holds
jointly in time.

* `extendInterior_BCG6K`, `contMDiff_extendInterior_BCG6K`, `extendDiffeomorph_BCG6K` (the
  extension of a compactly supported diffeomorphism of `W°` to a `Diffeomorph` of `W`),
  `contMDiff_extendInterior_family_BCG6K` (joint smoothness on `ℝ × W`);
* **`cuspCore_relative_flow_BCG6K`**: `Φ : ℝ → W ≃ₘ W`, jointly smooth, `Φ 0 = id`, identity off a
  compact `K' ⊆ band ∩ {38 < η_b < 42}` and on a neighbourhood of `∂W`, with
  `G_{s(t)} ∘ Φ t = level_b` on ALL of `W` (all levels; every `G_τ`, `τ ∈ [0, 1]`, is reached), so
  `Φ 1 {level_b ≤ c} = {G ≤ c}` for every `c`, `Φ 1 {level_b ≤ 40} = C_b`,
  `Φ 1 {level_b = 40} = H_b` (review 65 M3: `G_t ∘ Φ_t = F`, `Φ₀ = id`, `Φ₁{F ≤ 40} = C_b`,
  identity near the original boundary, support in the prescribed band).

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

universe u

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ}
  {A : ℝ → ℝ} {w₀ ε : ℝ}

section Extension

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1

variable (W) in
open Classical in
/-- The extension by the identity of a self-map of the interior `W°` to `W`. -/
def extendInterior_BCG6K (f : W.pieceInterior ⊤ → W.pieceInterior ⊤) (y : W.Carrier) :
    W.Carrier :=
  if h : y ∈ ((W.pieceInterior ⊤ : TopologicalSpace.Opens W.Carrier) : Set W.Carrier) then
    (f ⟨y, h⟩ : W.Carrier) else y

theorem extendInterior_apply_val_BCG6K (f : W.pieceInterior ⊤ → W.pieceInterior ⊤)
    (x : W.pieceInterior ⊤) : extendInterior_BCG6K W f x = f x := by
  unfold extendInterior_BCG6K
  split_ifs with h
  · rfl
  · exact absurd x.2 h

theorem extendInterior_of_notMem_BCG6K (f : W.pieceInterior ⊤ → W.pieceInterior ⊤)
    {y : W.Carrier}
    (hy : y ∉ ((W.pieceInterior ⊤ : TopologicalSpace.Opens W.Carrier) : Set W.Carrier)) :
    extendInterior_BCG6K W f y = y := by
  simp [extendInterior_BCG6K, hy]

theorem extendInterior_eq_self_BCG6K {f : W.pieceInterior ⊤ → W.pieceInterior ⊤}
    {K' : Set (W.pieceInterior ⊤)} (hid : ∀ x, x ∉ K' → f x = x) {y : W.Carrier}
    (hy : y ∉ (Subtype.val : W.pieceInterior ⊤ → W.Carrier) '' K') :
    extendInterior_BCG6K W f y = y := by
  by_cases hW : y ∈ ((W.pieceInterior ⊤ : TopologicalSpace.Opens W.Carrier) : Set W.Carrier)
  · rw [show y = ((⟨y, hW⟩ : W.pieceInterior ⊤) : W.Carrier) from rfl,
      extendInterior_apply_val_BCG6K, hid ⟨y, hW⟩ fun h => hy ⟨_, h, rfl⟩]
  · exact extendInterior_of_notMem_BCG6K f hW

variable (W) in
/-- The identity of `W°` from the open-subset atlas to the interior atlas is smooth. -/
theorem contMDiff_id_toInterior_BCG6K :
    ContMDiff W.model (𝓡 3) ∞ (id : W.pieceInterior ⊤ → W.pieceInterior ⊤) :=
  DifferentialGeometry.Manifold.contMDiff_id_interiorAtlas W.model ∞
    (M := W.pieceInterior ⊤)

/-- **The extension by the identity of a compactly supported smooth self-map of `W°` is smooth
on `W`.** -/
theorem contMDiff_extendInterior_BCG6K {f : W.pieceInterior ⊤ → W.pieceInterior ⊤}
    (hf : ContMDiff (𝓡 3) (𝓡 3) ∞ f) {K' : Set (W.pieceInterior ⊤)} (hK' : IsCompact K')
    (hid : ∀ x, x ∉ K' → f x = x) :
    ContMDiff W.model W.model ∞ (extendInterior_BCG6K W f) := by
  intro y
  by_cases hy : y ∈ (Subtype.val : W.pieceInterior ⊤ → W.Carrier) '' K'
  · obtain ⟨x, -, rfl⟩ := hy
    apply contMDiffAt_subtype_iff.mp
    have hfun : (fun z : W.pieceInterior ⊤ => extendInterior_BCG6K W f z) =
        (Subtype.val : W.pieceInterior ⊤ → W.Carrier) ∘ f ∘ id := by
      funext z
      exact extendInterior_apply_val_BCG6K f z
    rw [hfun]
    exact (((contMDiff_val_interior_BCG6K W).comp hf).comp (contMDiff_id_toInterior_BCG6K W)) x
  · have hcl : IsClosed ((Subtype.val : W.pieceInterior ⊤ → W.Carrier) '' K') :=
      (hK'.image continuous_subtype_val).isClosed
    apply contMDiffAt_id.congr_of_eventuallyEq
    filter_upwards [hcl.isOpen_compl.mem_nhds hy] with z hz
    exact extendInterior_eq_self_BCG6K hid hz

/-- **A compactly supported diffeomorphism of `W°` extends by the identity to a diffeomorphism of
`W`** (identity on `∂W` and off the support). -/
def extendDiffeomorph_BCG6K (Φ : Diffeomorph (𝓡 3) (𝓡 3) (W.pieceInterior ⊤) (W.pieceInterior ⊤) ∞)
    {K' : Set (W.pieceInterior ⊤)} (hK' : IsCompact K') (hid : ∀ x, x ∉ K' → Φ x = x) :
    Diffeomorph W.model W.model W.Carrier W.Carrier ∞ where
  toFun := extendInterior_BCG6K W Φ
  invFun := extendInterior_BCG6K W Φ.symm
  left_inv y := by
    by_cases hy : y ∈ ((W.pieceInterior ⊤ : TopologicalSpace.Opens W.Carrier) : Set W.Carrier)
    · have h1 : extendInterior_BCG6K W Φ y = Φ ⟨y, hy⟩ := extendInterior_apply_val_BCG6K Φ ⟨y, hy⟩
      rw [h1, extendInterior_apply_val_BCG6K, Diffeomorph.symm_apply_apply]
    · rw [extendInterior_of_notMem_BCG6K _ hy, extendInterior_of_notMem_BCG6K _ hy]
  right_inv y := by
    by_cases hy : y ∈ ((W.pieceInterior ⊤ : TopologicalSpace.Opens W.Carrier) : Set W.Carrier)
    · have h1 : extendInterior_BCG6K W Φ.symm y = Φ.symm ⟨y, hy⟩ :=
        extendInterior_apply_val_BCG6K Φ.symm ⟨y, hy⟩
      rw [h1, extendInterior_apply_val_BCG6K, Diffeomorph.apply_symm_apply]
    · rw [extendInterior_of_notMem_BCG6K _ hy, extendInterior_of_notMem_BCG6K _ hy]
  contMDiff_toFun := contMDiff_extendInterior_BCG6K Φ.contMDiff hK' hid
  contMDiff_invFun := contMDiff_extendInterior_BCG6K Φ.symm.contMDiff hK' fun x hx => by
    calc Φ.symm x = Φ.symm (Φ x) := by rw [hid x hx]
      _ = x := Φ.symm_apply_apply x

theorem extendDiffeomorph_apply_BCG6K
    (Φ : Diffeomorph (𝓡 3) (𝓡 3) (W.pieceInterior ⊤) (W.pieceInterior ⊤) ∞)
    {K' : Set (W.pieceInterior ⊤)} (hK' : IsCompact K') (hid : ∀ x, x ∉ K' → Φ x = x)
    (y : W.Carrier) : extendDiffeomorph_BCG6K Φ hK' hid y = extendInterior_BCG6K W Φ y :=
  rfl

/-- **Joint smoothness of the extension of a jointly smooth compactly supported family.** -/
theorem contMDiff_extendInterior_family_BCG6K {f : ℝ → W.pieceInterior ⊤ → W.pieceInterior ⊤}
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞ (fun q : ℝ × W.pieceInterior ⊤ => f q.1 q.2))
    {K' : Set (W.pieceInterior ⊤)} (hK' : IsCompact K') (hid : ∀ t x, x ∉ K' → f t x = x) :
    ContMDiff (𝓘(ℝ, ℝ).prod W.model) W.model ∞
      (fun q : ℝ × W.Carrier => extendInterior_BCG6K W (f q.1) q.2) := by
  intro q
  by_cases hy : q.2 ∈ (Subtype.val : W.pieceInterior ⊤ → W.Carrier) '' K'
  · have hWo : IsOpen (univ ×ˢ ((W.pieceInterior ⊤ : TopologicalSpace.Opens W.Carrier) :
        Set W.Carrier)) := (isOpen_univ (X := ℝ)).prod (W.pieceInterior ⊤).isOpen
    set U : TopologicalSpace.Opens (ℝ × W.Carrier) := ⟨_, hWo⟩ with hU
    obtain ⟨x, -, hx⟩ := hy
    have hqU : q ∈ U := ⟨mem_univ _, by rw [← hx]; exact x.2⟩
    apply (contMDiffAt_subtype_iff (U := U) (x := ⟨q, hqU⟩)).mp
    set k : U → W.pieceInterior ⊤ := fun z => ⟨z.1.2, z.2.2⟩ with hk
    have hk' : ContMDiff (𝓘(ℝ, ℝ).prod W.model) W.model ∞ k := by
      rw [← ContMDiff.subtypeVal_comp_iff]
      exact contMDiff_snd.comp contMDiff_subtype_val
    have hh : ContMDiff (𝓘(ℝ, ℝ).prod W.model) (𝓘(ℝ, ℝ).prod (𝓡 3)) ∞
        (fun z : U => ((z.1.1, k z) : ℝ × W.pieceInterior ⊤)) :=
      (contMDiff_fst.comp contMDiff_subtype_val).prodMk
        ((contMDiff_id_toInterior_BCG6K W).comp hk')
    have hfun : (fun z : U => extendInterior_BCG6K W (f z.1.1) z.1.2) =
        (Subtype.val : W.pieceInterior ⊤ → W.Carrier) ∘
          (fun p : ℝ × W.pieceInterior ⊤ => f p.1 p.2) ∘
            (fun z : U => ((z.1.1, k z) : ℝ × W.pieceInterior ⊤)) := by
      funext z
      exact extendInterior_apply_val_BCG6K (f z.1.1) (k z)
    rw [hfun]
    exact (((contMDiff_val_interior_BCG6K W).comp hf).comp hh) _
  · have hcl : IsClosed ((Subtype.val : W.pieceInterior ⊤ → W.Carrier) '' K') :=
      (hK'.image continuous_subtype_val).isClosed
    apply contMDiffAt_snd.congr_of_eventuallyEq
    have hT : (Prod.snd : ℝ × W.Carrier → W.Carrier) ⁻¹'
        ((Subtype.val : W.pieceInterior ⊤ → W.Carrier) '' K')ᶜ ∈ 𝓝 q :=
      continuous_snd.continuousAt.preimage_mem_nhds (hcl.isOpen_compl.mem_nhds hy)
    filter_upwards [hT] with z hz
    exact extendInterior_eq_self_BCG6K (hid z.1) hz

end Extension

section WholeFlow

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1

namespace BoundaryCollarPacket

variable {P : BoundaryCollarPacket W g K A w₀ ε} {b : Fin P.cusp.count}

variable (P b) in
/-- The collar band consists of interior points of `W`. -/
theorem mem_interior_of_mem_collarBand_BCG6K {x : W.Carrier} (hx : x ∈ P.collarBand_BAUGA b) :
    x ∈ ((W.pieceInterior ⊤ : TopologicalSpace.Opens W.Carrier) : Set W.Carrier) := by
  obtain ⟨p, hp, rfl⟩ := hx
  have hpd : p ∈ cuspDomain :=
    cusp_mem_cuspDomain_of_le (b := 98) (by norm_num [cuspDepth]) hp.2.le
  exact mem_pieceInterior_of_isInteriorPoint_BCG6K
    (isInteriorPoint_of_height_pos_BCG6K (P.cusp.collar b) hpd (by linarith [hp.1]))

/-- Every value `τ ∈ [0, 1]` is taken by `Real.smoothTransition` on `[0, 1]`. -/
theorem exists_smoothTransition_eq_BCG6K {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) :
    ∃ t ∈ Icc (0 : ℝ) 1, Real.smoothTransition t = τ := by
  have h := intermediate_value_Icc (zero_le_one' ℝ) Real.smoothTransition.continuous.continuousOn
  rw [Real.smoothTransition.zero, Real.smoothTransition.one] at h
  exact h hτ

/-- **The relative supported flow on `W` (review 65 M3, both forms)**: a jointly smooth family of
diffeomorphisms `Φ t` of `W` (with its boundary), `Φ 0 = id`, the identity off a compact set
`K'` inside `band ∩ {38 < η_b < 42}` (hence on a neighbourhood of `∂W`), with
`G_{s(t)} ∘ Φ t = level_b` on ALL of `W` (all levels; `s = Real.smoothTransition`, and every
`G_τ`, `τ ∈ [0, 1]`, is reached), so `Φ 1` carries every sublevel `{level_b ≤ c}` onto
`{G ≤ c}`, the original level-`40` inner collar onto `C_b` and its level torus onto `H_b`. -/
theorem cuspCore_relative_flow_BCG6K (hε : ε ≤ 1 / 1000)
    {u v : Fin P.cusp.count → W.Carrier → ℝ} (hu : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (u b))
    {εd c₃ : ℝ} (hεd : εd < 1 / 1000000) (hc₃ : 0 ≤ c₃) (hR : 80 * εd + 102 / 100 * c₃ < 1)
    (hBI : ∀ x, |u b x - (P.block b x).1| < εd ∧ |v b x - (P.block b x).2| < εd)
    (hBFM : ∀ x ∈ P.safeBand_BAUGA b, v b x = 1)
    (hBD : ∀ x ∈ P.collarBand_BAUGA b, 38 ≤ P.height b x → P.height b x ≤ 42 →
      ∀ w : TangentSpace W.model x, |mvfderiv W.model (fun y => u b y - P.height b y) x w| ≤
        c₃ * Real.sqrt (g.inner x w w)) :
    ∃ (K' : Set W.Carrier) (Φ : ℝ → Diffeomorph W.model W.model W.Carrier W.Carrier ∞),
      IsCompact K' ∧
      (∀ x ∈ K', x ∈ P.collarBand_BAUGA b ∧ 38 < P.height b x ∧ P.height b x < 42) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod W.model) W.model ∞ (fun q : ℝ × W.Carrier => Φ q.1 q.2) ∧
      (∀ x, Φ 0 x = x) ∧ (∀ t x, x ∉ K' → Φ t x = x) ∧
      (∀ y, ¬ W.model.IsInteriorPoint y → ∀ᶠ z in 𝓝 y, ∀ t, Φ t z = z) ∧
      (∀ t x, P.coreLevelT_BCG6K b (u b) (Real.smoothTransition t) (Φ t x) = P.level b x) ∧
      (∀ τ ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1,
        ∀ x, P.coreLevelT_BCG6K b (u b) τ (Φ t x) = P.level b x) ∧
      (∀ c : ℝ, Φ 1 '' {x | P.level b x ≤ c} = {x | P.coreLevel_BCG6K b (u b) x ≤ c}) ∧
      Φ 1 '' {x | P.level b x ≤ 40} = P.cuspCore_BCG6K b u v ∧
      Φ 1 '' {x | P.level b x = 40} = P.cuspFront_BCG6K b u v := by
  obtain ⟨K₀, Φ₀, hK₀, hK₀N, hjoint, h0, hid, hlev⟩ :=
    exists_coreLevel_flow_interior_BCG6K hε hu hc₃ hR (fun x _ => (hBI x).1) hBD
  set Φ : ℝ → Diffeomorph W.model W.model W.Carrier W.Carrier ∞ :=
    fun t => extendDiffeomorph_BCG6K (Φ₀ t) hK₀ (hid t) with hΦ
  have hΦapp : ∀ t y, Φ t y = extendInterior_BCG6K W (Φ₀ t) y := fun t y => rfl
  set K' : Set W.Carrier := (Subtype.val : W.pieceInterior ⊤ → W.Carrier) '' K₀ with hK'
  have hK'c : IsCompact K' := hK₀.image continuous_subtype_val
  have hoff : ∀ t x, x ∉ K' → Φ t x = x := fun t x hx => by
    rw [hΦapp]
    exact extendInterior_eq_self_BCG6K (hid t) hx
  -- the level identity on all of `W`
  have hlevW : ∀ t x, P.coreLevelT_BCG6K b (u b) (Real.smoothTransition t) (Φ t x) =
      P.level b x := by
    intro t x
    by_cases hx : x ∈ ((W.pieceInterior ⊤ : TopologicalSpace.Opens W.Carrier) : Set W.Carrier)
    · rw [hΦapp, show x = ((⟨x, hx⟩ : W.pieceInterior ⊤) : W.Carrier) from rfl,
        extendInterior_apply_val_BCG6K]
      exact hlev t ⟨x, hx⟩
    · rw [hΦapp, extendInterior_of_notMem_BCG6K _ hx, coreLevelT_BCG6K, coreCorrection_BCG6K,
        indicator_of_notMem (fun h => hx (P.mem_interior_of_mem_collarBand_BCG6K b h)), mul_zero,
        add_zero]
  have hset : ∀ r : ℝ → Prop, Φ 1 '' {x | r (P.level b x)} =
      {x | r (P.coreLevel_BCG6K b (u b) x)} := by
    intro r
    have h1 : ∀ x, P.coreLevel_BCG6K b (u b) (Φ 1 x) = P.level b x := by
      intro x
      have h := hlevW 1 x
      rw [Real.smoothTransition.one, coreLevelT_one_BCG6K] at h
      exact h
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change r (P.coreLevel_BCG6K b (u b) (Φ 1 x))
      rw [h1]
      exact hx
    · intro hy
      refine ⟨(Φ 1).symm y, ?_, (Φ 1).apply_symm_apply y⟩
      change r (P.level b ((Φ 1).symm y))
      rw [← h1, (Φ 1).apply_symm_apply]
      exact hy
  refine ⟨K', Φ, hK'c, ?_, contMDiff_extendInterior_family_BCG6K hjoint hK₀ hid, fun x => ?_,
    hoff, fun y hy => ?_, hlevW, fun τ hτ => ?_, fun c => hset (· ≤ c), ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hK₀N x hx
  · rw [hΦapp]
    by_cases hx : x ∈ ((W.pieceInterior ⊤ : TopologicalSpace.Opens W.Carrier) : Set W.Carrier)
    · rw [show x = ((⟨x, hx⟩ : W.pieceInterior ⊤) : W.Carrier) from rfl,
        extendInterior_apply_val_BCG6K, h0]
    · exact extendInterior_of_notMem_BCG6K _ hx
  · have hyK : y ∉ K' := by
      rintro ⟨x, -, rfl⟩
      exact hy (isInteriorPoint_of_mem_interior_BCG6K x)
    filter_upwards [hK'c.isClosed.isOpen_compl.mem_nhds hyK] with z hz t
    exact hoff t z hz
  · obtain ⟨t, ht, hst⟩ := exists_smoothTransition_eq_BCG6K hτ
    refine ⟨t, ht, fun x => ?_⟩
    rw [← hst]
    exact hlevW t x
  · rw [P.cuspCore_eq_BCG6K hεd hBI hBFM]
    exact hset (· ≤ 40)
  · rw [P.cuspFront_eq_BCG6K hεd hBI hBFM]
    exact hset (· = 40)

end BoundaryCollarPacket

end WholeFlow

end DifferentialGeometry.Geometry.Collapse
