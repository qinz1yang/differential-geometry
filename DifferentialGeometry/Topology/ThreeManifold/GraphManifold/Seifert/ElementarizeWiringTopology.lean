import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.OldPortCollar
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FibreCoordinateFlow
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.EmbeddedPieces
import DifferentialGeometry.Topology.Manifold.BoundaryExtrema

/-!
# The height function on an old piece and its collar regions

Lane P1W (P1 wiring), topological part of tier T2.

For a circle fibration `F` of an open piece `U` and Morse data `D` on its base, `u = f ∘ π` is the
height (`portHeight`) and `lowSet F D` the part of `U` where `u ≤ ℓ`, `ℓ = level 0`. Through every
point of height `ℓ` runs a continuous path along which `u` grows at rate `κ`
(`exists_levelPath`, a lifted level bicollar). Consequently:

* if `K : T² × [0, ℓ] → U` is smooth with bijective differential, has range in `lowSet F D` and
  height `≠ ℓ` on `T² × 0`, then every point of height `ℓ` in its range lies on `T² × ℓ`
  (`eq_top_of_portHeight`), since otherwise `K` would cover a neighbourhood of a point from which
  the path climbs above `ℓ`;
* `K` maps `T² × (0, ℓ)` to interior points (`isInteriorPoint_of_mem_Ioo`);
* if moreover `range K` is a component of `lowSet F D` and `K` follows a flow near `T² × ℓ`, then
  `T² × ℓ` has height `ℓ` (`portHeight_top`), since a component point of height `< ℓ` has a
  connected neighbourhood inside `range K` along which the flow would move `T² × ℓ` beyond itself;
* every component of `lowSet F D` meets the boundary of `C`, hence contains a boundary torus
  (`exists_mem_component_of_boundary`): at a point of minimal height in a component the height
  is either `0` (boundary), or `< ℓ` and regular (not a local minimum, `BoundaryExtrema`), or `ℓ`
  and the path descends;
* a component of `lowSet F D` through a boundary point contains a point of height `ℓ`
  (`exists_level_mem_component`), otherwise it would be clopen in the connected `U`.
-/

set_option autoImplicit false

noncomputable section
open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.Wiring

theorem locallyConnectedSpace_model (k : CarrierModel) : LocallyConnectedSpace k.Space := by
  cases k
  · exact inferInstanceAs (LocallyConnectedSpace (EuclideanSpace ℝ (Fin 3)))
  · exact inferInstanceAs (LocallyConnectedSpace (EuclideanHalfSpace 3))

theorem locallyConnectedSpace_opens {C : CompactCarrier.{u}}
    (U : TopologicalSpace.Opens C.Carrier) :
    LocallyConnectedSpace U := by
  have := locallyConnectedSpace_model C.kind
  exact ChartedSpace.locallyConnectedSpace C.kind.Space U

variable {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier}

def lowSet (F : CircleFibration C U) (D : BaseMorseData F.base) : Set C.Carrier :=
  {y | ∃ h : y ∈ U, D.f (F.projection ⟨y, h⟩) ≤ D.level 0}

theorem collarRegion_eq (F : CircleFibration C U) (D : BaseMorseData F.base)
    (c₀ : PartialDiffeomorph halfCollarModel C.model (Torus × EuclideanHalfSpace 1) C.Carrier ∞) :
    collarRegion F D c₀ = connectedComponentIn (lowSet F D) (c₀ (1, halfZero)) := rfl

theorem val_mem_lowSet {F : CircleFibration C U} {D : BaseMorseData F.base} {x : U} :
    x.val ∈ lowSet F D ↔ portHeight F D x ≤ D.level 0 :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨x.2, h⟩⟩

theorem exists_levelPath (F : CircleFibration C U) (D : BaseMorseData F.base) (y : U)
    (hy : portHeight F D y = D.level 0) :
    ∃ γ : ℝ → U, Continuous γ ∧ γ 0 = y ∧ ∃ w > 0, ∀ r, |r| < w →
      portHeight F D (γ r) = D.level 0 + D.κ * r := by
  obtain ⟨c, hcs, hcr, hcf, -⟩ := D.exists_levelBicollar 0 hy
  have hmem : F.projection y ∈ range (fun t => c (t, 0)) := by
    rw [hcr]
    exact mem_connectedComponentIn hy
  obtain ⟨θ, hθ⟩ := hmem
  obtain ⟨L, -, -⟩ := CircleFibration.exists_liftFlow F c (R := 1 / 2) (by norm_num)
    fun θ s hs => by
      rw [hcs]
      constructor <;> linarith [abs_le.mp hs]
  refine ⟨fun r => L.flow r y, L.smooth.continuous.comp (continuous_id.prodMk continuous_const),
    L.flow_zero y, L.width, L.width_pos, fun r hr => ?_⟩
  have h := LiftedBicollar.f_projection_flow D hcs hcf L (x := y) (θ := θ) (s := 0) (r := r)
    hθ.symm (by simpa using L.width_pos) (by simpa using hr)
  change D.f (F.projection (L.flow r y)) = _
  rw [h]
  change portHeight F D y + D.κ * r = _
  rw [hy]

section Piece

variable (F : CircleFibration C U) (D : BaseMorseData F.base)

theorem isInteriorPoint_torus_Icc {ℓ : ℝ} [Fact (0 < ℓ)] (p : Torus) {r : Icc (0 : ℝ) ℓ}
    (h0 : 0 < r.1)
    (h1 : r.1 < ℓ) : (torusModel.prod (𝓡∂ 1)).IsInteriorPoint (p, r) := by
  change (p, r) ∈ (torusModel.prod (𝓡∂ 1)).interior (Torus × Icc (0 : ℝ) ℓ)
  rw [ModelWithCorners.interior_prod]
  exact ⟨BoundarylessManifold.isInteriorPoint, Icc_isInteriorPoint_interior ⟨h0, h1⟩⟩

variable {F D} {ℓ : ℝ} [Fact (0 < ℓ)] {K : Torus × Icc (0 : ℝ) ℓ → U}

theorem isInteriorPoint_of_mem_Ioo
    (hK : ContMDiff (torusModel.prod (𝓡∂ 1)) C.model ∞ (fun q => (K q).val))
    (hKb : ∀ q, Bijective (mfderiv (torusModel.prod (𝓡∂ 1)) C.model (fun q => (K q).val) q))
    (p : Torus) {r : Icc (0 : ℝ) ℓ} (h0 : 0 < r.1) (h1 : r.1 < ℓ) :
    C.model.IsInteriorPoint (K (p, r)).val := by
  have h := isLocalDiffeomorphAt_of_isInteriorPoint_of_bijective hK
    (isInteriorPoint_torus_Icc p h0 h1) (hKb _)
  exact (h.isInteriorPoint_iff (by simp)).mp (isInteriorPoint_torus_Icc p h0 h1)

theorem eq_top_of_portHeight
    (hK : ContMDiff (torusModel.prod (𝓡∂ 1)) C.model ∞ (fun q => (K q).val))
    (hKb : ∀ q, Bijective (mfderiv (torusModel.prod (𝓡∂ 1)) C.model (fun q => (K q).val) q))
    (hR : range (fun q => (K q).val) ⊆ lowSet F D)
    (h0 : ∀ p (r : Icc (0 : ℝ) ℓ), r.1 = 0 → portHeight F D (K (p, r)) ≠ D.level 0)
    {p : Torus} {r : Icc (0 : ℝ) ℓ} (hu : portHeight F D (K (p, r)) = D.level 0) : r.1 = ℓ := by
  by_contra hne
  have hr1 : r.1 < ℓ := lt_of_le_of_ne r.2.2 hne
  have hr0 : 0 < r.1 := lt_of_le_of_ne r.2.1 fun h => h0 p r h.symm hu
  have hKU : ContMDiff (torusModel.prod (𝓡∂ 1)) C.model ∞ K :=
    (ContMDiff.subtypeVal_comp_iff U _).mp hK
  have hinj : Injective (mfderiv (torusModel.prod (𝓡∂ 1)) C.model K (p, r)) := by
    have h := (hKb (p, r)).1
    rwa [DifferentialGeometry.mfderiv_subtypeVal_comp] at h
  have hpos : 0 < portHeight F D (K (p, r)) := by
    rw [hu]
    exact D.level_zero_pos
  have hnhds : K '' univ ∈ 𝓝 (K (p, r)) :=
    image_mem_nhds_of_mfderiv_injective hKU (isInteriorPoint_torus_Icc p hr0 hr1)
      (isInteriorPoint_of_portHeight_pos F D hpos) hinj (by simp [EuclideanSpace]) univ_mem
  obtain ⟨γ, hγ, hγ0, w, hw, hγu⟩ := exists_levelPath F D _ hu
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), γ t ∈ K '' univ := by
    have hc : Tendsto γ (𝓝[>] 0) (𝓝 (K (p, r))) := by
      rw [← hγ0]
      exact (hγ.tendsto 0).mono_left nhdsWithin_le_nhds
    exact hc hnhds
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ t < w :=
    (eventually_nhdsWithin_of_forall fun t ht => ht).and
      (nhdsWithin_le_nhds (eventually_lt_nhds hw))
  obtain ⟨t, ⟨q, -, hq⟩, ht0, htw⟩ := (hev.and hsmall).exists
  have hlow : portHeight F D (γ t) ≤ D.level 0 := by
    rw [← hq]
    exact val_mem_lowSet.mp (hR ⟨q, rfl⟩)
  rw [hγu t (by rw [abs_of_pos ht0]; exact htw)] at hlow
  nlinarith [D.κ_pos]

end Piece

section Top

variable {F : CircleFibration C U} {D : BaseMorseData F.base}
  {K : Torus × Icc (0 : ℝ) (D.level 0) → U}

theorem eq_zero_of_isBoundaryPoint [Fact (0 < D.level 0)]
    (hK : ContMDiff (torusModel.prod (𝓡∂ 1)) C.model ∞ (fun q => (K q).val))
    (hKb : ∀ q, Bijective (mfderiv (torusModel.prod (𝓡∂ 1)) C.model (fun q => (K q).val) q))
    (htop : ∀ p, portHeight F D (K (p, topPoint D)) = D.level 0) {p : Torus}
    {r : Icc (0 : ℝ) (D.level 0)} (hb : C.model.IsBoundaryPoint (K (p, r)).val) : r.1 = 0 := by
  by_contra h0
  have hr0 : 0 < r.1 := lt_of_le_of_ne r.2.1 (Ne.symm h0)
  rcases lt_or_eq_of_le r.2.2 with hr1 | hr1
  · exact (C.model.isInteriorPoint_iff_not_isBoundaryPoint _).mp
      (isInteriorPoint_of_mem_Ioo hK hKb p hr0 hr1) hb
  · have hr : r = topPoint D := Subtype.ext hr1
    have hu := htop p
    rw [← hr] at hu
    have hpos : 0 < portHeight F D (K (p, r)) := by
      rw [hu]
      exact D.level_zero_pos
    have hi := isInteriorPoint_of_portHeight_pos F D hpos
    rw [ModelWithCorners.isInteriorPoint_iff_isInteriorPoint_val] at hi
    exact (C.model.isInteriorPoint_iff_not_isBoundaryPoint _).mp hi hb

theorem image_val_subset_component {x₀ : C.Carrier} {V : Set U} (hV : IsPreconnected V)
    (hVlow : ∀ z ∈ V, portHeight F D z ≤ D.level 0) {y : U} (hyV : y ∈ V)
    (hy : y.val ∈ connectedComponentIn (lowSet F D) x₀) :
    Subtype.val '' V ⊆ connectedComponentIn (lowSet F D) x₀ := by
  rw [connectedComponentIn_eq hy]
  exact (hV.image _ continuous_subtype_val.continuousOn).subset_connectedComponentIn
    ⟨y, hyV, rfl⟩ (by rintro _ ⟨z, hz, rfl⟩; exact val_mem_lowSet.mpr (hVlow z hz))

theorem exists_open_component_nhds {x₀ : C.Carrier} {y : U}
    (hy : y.val ∈ connectedComponentIn (lowSet F D) x₀) (hlt : portHeight F D y < D.level 0) :
    ∃ V : Set U, IsOpen V ∧ y ∈ V ∧ Subtype.val '' V ⊆ connectedComponentIn (lowSet F D) x₀ ∧
      ∀ z ∈ V, portHeight F D z < D.level 0 := by
  have := locallyConnectedSpace_opens U
  have hO : IsOpen {z : U | portHeight F D z < D.level 0} :=
    isOpen_lt (contMDiff_portHeight F D).continuous continuous_const
  have hsub : ∀ z ∈ connectedComponentIn {z : U | portHeight F D z < D.level 0} y,
      portHeight F D z < D.level 0 := fun z hz =>
    connectedComponentIn_subset {z : U | portHeight F D z < D.level 0} y hz
  refine ⟨connectedComponentIn {z : U | portHeight F D z < D.level 0} y,
    hO.connectedComponentIn, mem_connectedComponentIn hlt, ?_, hsub⟩
  exact image_val_subset_component isPreconnected_connectedComponentIn
    (fun z hz => (hsub z hz).le) (mem_connectedComponentIn hlt) hy

theorem portHeight_top [Fact (0 < D.level 0)] (hKc : Continuous K) (hKi : Injective K)
    {x₀ : C.Carrier} (hR : range (fun q => (K q).val) = connectedComponentIn (lowSet F D) x₀)
    {φ : ℝ → U → U} (hφc : ∀ x, Continuous fun r => φ r x) (hφ0 : ∀ x, φ 0 x = x)
    (hφadd : ∀ s t x, φ (s + t) x = φ s (φ t x)) {δ : ℝ} (hδ : 0 < δ)
    (htop : ∀ p (s : Icc (0 : ℝ) (D.level 0)), D.level 0 - δ < s.1 →
      K (p, s) = φ (s.1 - D.level 0) (K (p, topPoint D)))
    (p : Torus) : portHeight F D (K (p, topPoint D)) = D.level 0 := by
  have hl0 : 0 < D.level 0 := Fact.out
  set y := K (p, topPoint D) with hy
  have hyR : y.val ∈ connectedComponentIn (lowSet F D) x₀ := by
    rw [← hR]
    exact ⟨(p, topPoint D), rfl⟩
  have hyle : portHeight F D y ≤ D.level 0 :=
    val_mem_lowSet.mp (connectedComponentIn_subset _ _ hyR)
  by_contra hne
  have hlt : portHeight F D y < D.level 0 := lt_of_le_of_ne hyle hne
  obtain ⟨V, hVo, hyV, hVR, -⟩ := exists_open_component_nhds hyR hlt
  set δ' := min δ (D.level 0) / 2 with hδ'
  have hδ'0 : 0 < δ' := by positivity
  have hδ'δ : δ' ≤ δ / 2 := by
    rw [hδ']
    exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hδ'l : δ' ≤ D.level 0 / 2 := by
    rw [hδ']
    exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hemb := hKc.isClosedEmbedding hKi
  have hA : IsOpen {q : Torus × Icc (0 : ℝ) (D.level 0) | D.level 0 - δ' < q.2.1} :=
    isOpen_lt continuous_const (continuous_subtype_val.comp continuous_snd)
  obtain ⟨W, hWo, hWA⟩ := hemb.isInducing.isOpen_iff.mp hA
  have hyW : y ∈ W := by
    have h : (p, topPoint D) ∈ K ⁻¹' W := by
      rw [hWA]
      change D.level 0 - δ' < D.level 0
      linarith
    exact h
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), φ t y ∈ V ∩ W := by
    have hc := (hφc y).tendsto 0
    rw [hφ0] at hc
    exact hc ((hVo.inter hWo).mem_nhds ⟨hyV, hyW⟩)
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ t < δ' :=
    (eventually_nhdsWithin_of_forall fun t ht => ht).and
      (nhdsWithin_le_nhds (eventually_lt_nhds hδ'0))
  have hev' : ∀ᶠ t in 𝓝[>] (0 : ℝ), φ t y ∈ V ∩ W := nhdsWithin_le_nhds hev
  obtain ⟨t, ⟨htV, htW⟩, ht0, htδ⟩ := (hev'.and hpos).exists
  obtain ⟨q, hq⟩ : φ t y ∈ range K := by
    obtain ⟨q, hq⟩ : (φ t y).val ∈ range (fun q => (K q).val) := by
      rw [hR]
      exact hVR ⟨_, htV, rfl⟩
    exact ⟨q, Subtype.ext hq⟩
  have hqA : D.level 0 - δ' < q.2.1 := by
    have h : q ∈ K ⁻¹' W := by
      change K q ∈ W
      rw [hq]
      exact htW
    rw [hWA] at h
    exact h
  have hmem : q.2.1 - t ∈ Icc (0 : ℝ) (D.level 0) := ⟨by linarith, by linarith [q.2.2.2]⟩
  have hK1 : K (q.1, ⟨q.2.1 - t, hmem⟩) = y := by
    rw [htop q.1 ⟨q.2.1 - t, hmem⟩ (by change D.level 0 - δ < q.2.1 - t; linarith)]
    change φ (q.2.1 - t - D.level 0) (K (q.1, topPoint D)) = y
    have h2 : φ (q.2.1 - t - D.level 0) (K (q.1, topPoint D)) =
        φ (-t) (φ (q.2.1 - D.level 0) (K (q.1, topPoint D))) := by
      rw [← hφadd]
      congr 1
      ring
    rw [h2, ← htop q.1 q.2 (by linarith)]
    change φ (-t) (K q) = y
    rw [hq, ← hφadd, neg_add_cancel, hφ0]
  have h3 := congrArg (fun z : Torus × Icc (0 : ℝ) (D.level 0) => z.2.1) (hKi hK1)
  change q.2.1 - t = D.level 0 at h3
  linarith [q.2.2.2]

theorem exists_level_mem_component (hUc : IsClosed (U : Set C.Carrier)) [ConnectedSpace U]
    {x₀ : C.Carrier} (hx₀ : x₀ ∈ lowSet F D) :
    ∃ x : U, x.val ∈ connectedComponentIn (lowSet F D) x₀ ∧ portHeight F D x = D.level 0 := by
  by_contra hne
  push Not at hne
  set R := connectedComponentIn (lowSet F D) x₀ with hRdef
  have hlowc : IsClosed (lowSet F D) := by
    have h : lowSet F D = Subtype.val '' {x : U | portHeight F D x ≤ D.level 0} := by
      ext y
      exact ⟨fun ⟨hy, h⟩ => ⟨⟨y, hy⟩, h, rfl⟩, fun ⟨x, hx, hxy⟩ => hxy ▸ val_mem_lowSet.mpr hx⟩
    rw [h]
    exact hUc.isClosedMap_subtype_val _
      (isClosed_le (contMDiff_portHeight F D).continuous continuous_const)
  have hRc : IsClosed R := by
    rw [hRdef, connectedComponentIn_eq_image hx₀]
    exact hlowc.isClosedMap_subtype_val _ isClosed_connectedComponent
  have hclopen : IsClopen (Subtype.val ⁻¹' R : Set U) := by
    refine ⟨hRc.preimage continuous_subtype_val, isOpen_iff_mem_nhds.mpr fun y hy => ?_⟩
    have hyle := val_mem_lowSet.mp (connectedComponentIn_subset _ _ hy)
    obtain ⟨V, hVo, hyV, hVR, -⟩ :=
      exists_open_component_nhds hy (lt_of_le_of_ne hyle (hne y hy))
    exact Filter.mem_of_superset (hVo.mem_nhds hyV) fun z hz => hVR ⟨z, hz, rfl⟩
  rcases isClopen_iff.mp hclopen with h | h
  · have hm : (⟨x₀, hx₀.1⟩ : U) ∈ (Subtype.val ⁻¹' R : Set U) := mem_connectedComponentIn hx₀
    rw [h] at hm
    exact hm
  · obtain ⟨b, hb⟩ := D.exists_level_zero_lt
    obtain ⟨x, hx⟩ := F.surjective b
    have hm : x ∈ (Subtype.val ⁻¹' R : Set U) := by
      rw [h]
      exact mem_univ x
    have hle := val_mem_lowSet.mp (connectedComponentIn_subset _ _ hm)
    change D.f (F.projection x) ≤ D.level 0 at hle
    rw [hx] at hle
    linarith

theorem exists_isBoundaryPoint_mem_component (hUc : IsClosed (U : Set C.Carrier)) (x : U)
    (hx : portHeight F D x ≤ D.level 0) :
    ∃ y : U, C.model.IsBoundaryPoint y.val ∧
      y.val ∈ connectedComponentIn (lowSet F D) x.val := by
  set R := connectedComponentIn (lowSet F D) x.val with hRdef
  have hxR : x.val ∈ R := mem_connectedComponentIn (val_mem_lowSet.mpr hx)
  have hlowc : IsClosed (lowSet F D) := by
    have h : lowSet F D = Subtype.val '' {x : U | portHeight F D x ≤ D.level 0} := by
      ext y
      exact ⟨fun ⟨hy, h⟩ => ⟨⟨y, hy⟩, h, rfl⟩, fun ⟨x, hx, hxy⟩ => hxy ▸ val_mem_lowSet.mpr hx⟩
    rw [h]
    exact hUc.isClosedMap_subtype_val _
      (isClosed_le (contMDiff_portHeight F D).continuous continuous_const)
  have hRc : IsClosed R := by
    rw [hRdef, connectedComponentIn_eq_image (val_mem_lowSet.mpr hx)]
    exact hlowc.isClosedMap_subtype_val _ isClosed_connectedComponent
  have hUcpt : CompactSpace U := isCompact_iff_compactSpace.mp hUc.isCompact
  have hR'c : IsCompact (Subtype.val ⁻¹' R : Set U) :=
    (hRc.preimage continuous_subtype_val).isCompact
  obtain ⟨y, hyR, hymin⟩ := hR'c.exists_isMinOn ⟨x, hxR⟩
    (contMDiff_portHeight F D).continuous.continuousOn
  have hyle := val_mem_lowSet.mp (connectedComponentIn_subset _ _ hyR)
  rcases eq_or_lt_of_le (portHeight_nonneg F D y) with h0 | h0
  · exact ⟨y, (BaseMorseData.f_projection_eq_zero_iff F D y).mp h0.symm, hyR⟩
  exfalso
  rcases lt_or_eq_of_le hyle with hlt | heq
  · obtain ⟨V, hVo, hyV, hVR, -⟩ := exists_open_component_nhds hyR hlt
    have hmin : IsLocalMin (portHeight F D) y :=
      Filter.mem_of_superset (hVo.mem_nhds hyV) fun z hz => hymin (hVR ⟨z, hz, rfl⟩)
    have hb :=
      DifferentialGeometry.Topology.Manifold.isBoundaryPoint_of_isLocalMin_of_mfderiv_ne_zero hmin
        (mfderiv_portHeight_ne_zero F D (by linarith [D.κ_pos]))
    exact (C.model.isInteriorPoint_iff_not_isBoundaryPoint _).mp
      (isInteriorPoint_of_portHeight_pos F D h0) hb
  · obtain ⟨γ, hγ, hγ0, w, hw, hγu⟩ := exists_levelPath F D y heq
    have hsub : Subtype.val '' (γ '' Icc (-(w / 2)) 0) ⊆ R := by
      refine image_val_subset_component (isPreconnected_Icc.image _ hγ.continuousOn) ?_
        ⟨0, ⟨by linarith, le_rfl⟩, hγ0⟩ hyR
      rintro _ ⟨r, hr, rfl⟩
      rw [hγu r (by rw [abs_lt]; constructor <;> linarith [hr.1, hr.2])]
      nlinarith [D.κ_pos, hr.2]
    have hm : γ (-(w / 2)) ∈ (Subtype.val ⁻¹' R : Set U) :=
      hsub ⟨_, ⟨_, ⟨le_rfl, by linarith⟩, rfl⟩, rfl⟩
    have h1 := hymin hm
    change portHeight F D y ≤ portHeight F D (γ (-(w / 2))) at h1
    rw [hγu _ (by rw [abs_neg, abs_of_pos (by linarith)]; linarith), heq] at h1
    nlinarith [D.κ_pos]

end Top

end GC.Seifert.Wiring
