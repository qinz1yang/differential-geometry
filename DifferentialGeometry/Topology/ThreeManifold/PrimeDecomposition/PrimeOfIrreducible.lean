import DifferentialGeometry.Topology.ThreeManifold.PrimeDecomposition.IrreducibleOfPrime
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.StandardPrimes
import DifferentialGeometry.Topology.VanKampen.EmbeddedCell
import DifferentialGeometry.Topology.ClosedBallComplement
import DifferentialGeometry.Topology.Manifold.PartialChartEmbedding
import DifferentialGeometry.Topology.Embedding.Sphere
import DifferentialGeometry.Topology.VanKampen.FiniteConnectedSumFreeProduct
import DifferentialGeometry.Topology.Covering.TrivialFundamentalGroup
import DifferentialGeometry.Compat.Ch567.Topology.ClosedBallComplement

/-!
# Irreducible closed oriented 3-manifolds are prime

If `M ≅ A # B` and every smoothly embedded sphere in `M` bounds a ball, then the seam sphere of
the connected sum (the unit sphere of its seam chart) bounds a ball in `A # B`. Its interior is
connected and misses the seam, so it is the outer region of one summand, and the corresponding
punctured summand is homeomorphic to a closed ball. Removing an embedded closed cell does not
change the fundamental group (`fundamentalGroupEmbeddedCellComplementEquiv`), so that summand is
simply connected, hence a `3`-sphere by the smooth Poincaré theorem. Together with
`isIrreducible_or_sphereTwoTimesCircle_of_isPrime` this characterises prime manifolds as the
irreducible ones and `S² × S¹` (Hatcher, *Notes on basic 3-manifold topology*, Prop. 1.4).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Manifold
open DifferentialGeometry DifferentialGeometry.Topology
open scoped Manifold ContDiff

namespace GC.Endpoint

universe u

local notation "E³" => EuclideanSpace ℝ (Fin 3)
local notation "S²" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

private theorem seamChartX_mem_atlas (A B : ConnectedClosedOrientedManifold.{u} 3) :
    ConnectedSumQuotient.seamChartX (orientedBallChart A).toBallChart
      (orientedBallChart B).toBallChart boundaryAttachment.1.toHomeomorph ∈
      atlas E³ (connectedSum A B).Carrier :=
  ⟨.inr (.inr ()), rfl⟩

private def seamPartialDiffeomorph (A B : ConnectedClosedOrientedManifold.{u} 3) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) (connectedSum A B).Carrier E³ ∞ where
  toPartialEquiv := (ConnectedSumQuotient.seamChartX (orientedBallChart A).toBallChart
    (orientedBallChart B).toBallChart boundaryAttachment.1.toHomeomorph).toPartialEquiv
  open_source := (ConnectedSumQuotient.seamChartX _ _ _).open_source
  open_target := (ConnectedSumQuotient.seamChartX _ _ _).open_target
  contMDiffOn_toFun := by
    have h := IsManifold.subset_maximalAtlas (I := 𝓡 3) (n := ∞) (seamChartX_mem_atlas A B)
    exact contMDiffOn_of_mem_maximalAtlas h
  contMDiffOn_invFun := by
    have h := IsManifold.subset_maximalAtlas (I := 𝓡 3) (n := ∞) (seamChartX_mem_atlas A B)
    exact contMDiffOn_symm_of_mem_maximalAtlas (M := (connectedSum A B).Carrier) (H := E³) h

private theorem sphere_mem_seamShell (z : S²) : (z : E³) ∈ ConnectedSumQuotient.SeamShell := by
  have hz : ‖(z : E³)‖ = 1 := norm_eq_of_mem_sphere z
  change (1 / 2 : ℝ) < ‖(z : E³)‖ ∧ ‖(z : E³)‖ < 3 / 2
  rw [hz]
  norm_num

private def seamSphere (A B : ConnectedClosedOrientedManifold.{u} 3) :
    S² → (connectedSum A B).Carrier :=
  fun z => (seamPartialDiffeomorph A B).symm (z : E³)

private theorem isSmoothEmbedding_seamSphere (A B : ConnectedClosedOrientedManifold.{u} 3) :
    IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (seamSphere A B) := by
  refine isSmoothEmbedding_comp_partialDiffeomorph (seamPartialDiffeomorph A B).symm
    (isSmoothEmbedding_coe_sphere (E := E³) (n := 2)) ?_
  rintro _ ⟨z, rfl⟩
  change (z : E³) ∈ (ConnectedSumQuotient.seamChartX _ _ _).target
  rw [ConnectedSumQuotient.seamChartX_target]
  exact sphere_mem_seamShell z

private theorem seamSphere_eq (A B : ConnectedClosedOrientedManifold.{u} 3) (z : S²) :
    seamSphere A B z = ConnectedSumQuotient.inl (orientedBallChart A).toBallChart
      (orientedBallChart B).toBallChart boundaryAttachment.1.toHomeomorph
      ((orientedBallChart A).toBallChart.boundaryMap z) := by
  have hz : ‖(z : E³)‖ = 1 := norm_eq_of_mem_sphere z
  let x : ConnectedSumQuotient.Seam := ⟨z, sphere_mem_seamShell z⟩
  change (ConnectedSumQuotient.seamChartX _ _ _).symm (x : E³) = _
  rw [ConnectedSumQuotient.seamChartX_symm_apply, ConnectedSumQuotient.seamMap_of_one_le _ _ _ x
    hz.ge, ConnectedSumQuotient.seamLeft_eq_boundary _ _ _ x hz]
  congr 2
  apply Subtype.ext
  rw [ConnectedSumQuotient.coe_seamDir_eq]
  change ‖(z : E³)‖⁻¹ • (z : E³) = z
  rw [hz, inv_one, one_smul]

section Punctured

variable {X : Type u} [TopologicalSpace X] [ChartedSpace E³ X] (c : BallChart 3 (𝓡 3) X)

private def outerSet : Set c.Punctured := {p | p.1 ∉ c.chart '' closedBall (0 : E³) 1}

private theorem isCompact_chart_closedBall :
    IsCompact (c.chart '' closedBall (0 : E³) 1) :=
  (isCompact_closedBall (0 : E³) 1).image_of_continuousOn
    (c.chart.contMDiffOn_toFun.continuousOn.mono
      ((closedBall_subset_closedBall (by norm_num)).trans c.closedBall_subset_source))

private theorem isOpen_outerSet [T2Space X] : IsOpen (outerSet c) :=
  (isCompact_chart_closedBall c).isClosed.isOpen_compl.preimage continuous_subtype_val

private theorem chart_injOn :
    InjOn c.chart (closedBall (0 : E³) 2) :=
  c.chart.toPartialEquiv.injOn.mono c.closedBall_subset_source

private theorem outerSet_nonempty : (outerSet c).Nonempty := by
  let v : E³ := EuclideanSpace.single 0 (3 / 2)
  have hv : ‖v‖ = 3 / 2 := by simp [v]
  have hv2 : v ∈ closedBall (0 : E³) 2 := by
    rw [mem_closedBall_zero_iff, hv]; norm_num
  have hout : c.chart v ∉ c.chart '' closedBall (0 : E³) 1 := by
    rintro ⟨y, hy, hyv⟩
    have hy2 : y ∈ closedBall (0 : E³) 2 :=
      closedBall_subset_closedBall (by norm_num) hy
    have := chart_injOn c hy2 hv2 hyv
    rw [mem_closedBall_zero_iff, this, hv] at hy
    norm_num at hy
  exact ⟨⟨c.chart v, fun h => hout ⟨_, ball_subset_closedBall h.choose_spec.1,
    h.choose_spec.2⟩⟩, hout⟩

private theorem isPreconnected_outerSet [T2Space X] [PreconnectedSpace X] :
    IsPreconnected (outerSet c) := by
  have hdim : 1 < Module.rank ℝ E³ := Module.one_lt_rank_of_one_lt_finrank (by simp)
  have h := isPreconnected_compl_iUnion_image_closedBall (M := X) (ι := Unit)
    (fun _ => c.chart.toOpenPartialHomeomorph) (fun _ => 1) hdim (fun _ => zero_le_one)
    (fun _ => (closedBall_subset_closedBall (by norm_num)).trans c.closedBall_subset_source)
    (fun i j hij => absurd (Subsingleton.elim i j) hij)
  rw [iUnion_const] at h
  have hsub : (c.chart '' closedBall (0 : E³) 1)ᶜ ⊆ range (Subtype.val : c.Punctured → X) :=
    fun x hx => ⟨⟨x, fun h' => hx ⟨_, ball_subset_closedBall h'.choose_spec.1,
      h'.choose_spec.2⟩⟩, rfl⟩
  have himg : Subtype.val '' outerSet c = (c.chart '' closedBall (0 : E³) 1)ᶜ :=
    image_preimage_eq_of_subset hsub
  exact (Topology.IsInducing.subtypeVal.isPreconnected_image).mp (himg ▸ h)

private theorem exists_boundaryMap_of_not_mem_outerSet (p : c.Punctured)
    (hp : p ∉ outerSet c) : ∃ z, c.boundaryMap z = p := by
  obtain ⟨y, hy, hyp⟩ := not_not.mp hp
  have hy1 : ‖y‖ = 1 := by
    rcases (mem_closedBall_zero_iff.mp hy).lt_or_eq with hlt | heq
    · exact absurd ⟨y, mem_ball_zero_iff.mpr hlt, hyp⟩ p.2
    · exact heq
  exact ⟨⟨y, mem_sphere_zero_iff_norm.mpr hy1⟩, Subtype.ext hyp⟩

private theorem boundaryMap_not_mem_outerSet (z : S²) : c.boundaryMap z ∉ outerSet c :=
  fun h => h ⟨z, sphere_subset_closedBall z.2, rfl⟩

private def chartCell : ClosedCell 3 → X := fun y => c.chart y.1

private theorem mem_closedBall_two (y : ClosedCell 3) : (y : E³) ∈ closedBall (0 : E³) 2 :=
  closedBall_subset_closedBall (by norm_num) (mem_closedBall_zero_iff.mpr y.2)

private theorem chartCell_injective : Injective (chartCell c) := fun y y' h =>
  Subtype.ext (chart_injOn c (mem_closedBall_two y) (mem_closedBall_two y') h)

private theorem continuous_chartCell : Continuous (chartCell c) :=
  c.chart.contMDiffOn_toFun.continuousOn.comp_continuous continuous_subtype_val
    fun y => c.closedBall_subset_source (mem_closedBall_two y)

private theorem embeddedCellInteriorImage_chartCell :
    ThreeManifold.embeddedCellInteriorImage (chartCell c) = c.chart '' ball (0 : E³) 1 := by
  ext x
  constructor
  · rintro ⟨y, ⟨w, rfl⟩, rfl⟩
    exact ⟨w.1, mem_ball_zero_iff.mpr w.2, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, (mem_ball_zero_iff.mp hy).le⟩, ⟨⟨y, mem_ball_zero_iff.mp hy⟩, rfl⟩,
      rfl⟩

end Punctured

private theorem simplyConnectedSpace_of_punctured (A : ConnectedClosedOrientedManifold.{u} 3)
    (c : BallChart 3 (𝓡 3) A.Carrier) [SimplyConnectedSpace c.Punctured] :
    SimplyConnectedSpace A.Carrier := by
  have hset : ThreeManifold.embeddedCellComplement (chartCell c) =
      {x | x ∉ c.chart '' ball (0 : E³) 1} := by
    rw [ThreeManifold.embeddedCellComplement, embeddedCellInteriorImage_chartCell]
    rfl
  let h₀ : ThreeManifold.embeddedCellComplement (chartCell c) ≃ₜ c.Punctured :=
    Homeomorph.setCongr hset
  have : SimplyConnectedSpace (ThreeManifold.embeddedCellComplement (chartCell c)) :=
    h₀.toHomotopyEquiv.simplyConnectedSpace_iff.mpr inferInstance
  let x : ThreeManifold.embeddedCellComplement (chartCell c) := Classical.choice inferInstance
  have hopen : IsOpen (ThreeManifold.embeddedCellInteriorImage (chartCell c)) := by
    rw [embeddedCellInteriorImage_chartCell]
    exact c.isOpen_chart_image_ball
  let e := ThreeManifold.fundamentalGroupEmbeddedCellComplementEquiv (chartCell c)
    (chartCell_injective c) (continuous_chartCell c) hopen x
  have : Subsingleton (FundamentalGroup A.Carrier (x : A.Carrier)) :=
    e.symm.injective.subsingleton
  exact simplyConnectedSpace_of_subsingleton_fundamentalGroup (x : A.Carrier)

private theorem simplyConnectedSpace_of_range_eq_image_closedBall {P Y : Type*}
    [TopologicalSpace P] [CompactSpace P] [TopologicalSpace Y] [T2Space Y] [ChartedSpace E³ Y]
    (ι : P → Y) (hι : Continuous ι) (hinj : Injective ι)
    (G : PartialDiffeomorph (𝓡 3) (𝓡 3) E³ Y ∞) (hG : closedBall (0 : E³) 1 ⊆ G.source)
    (heq : range ι = G '' closedBall (0 : E³) 1) : SimplyConnectedSpace P := by
  let g : closedBall (0 : E³) 1 → Y := fun x => G x
  have hg : Continuous g :=
    G.contMDiffOn_toFun.continuousOn.comp_continuous continuous_subtype_val fun x => hG x.2
  have hginj : Injective g := fun x y hxy => Subtype.ext (G.injOn (hG x.2) (hG y.2) hxy)
  have hrange : range g = G '' closedBall (0 : E³) 1 := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have : ContractibleSpace (closedBall (0 : E³) 1) :=
    (convex_closedBall (0 : E³) 1).contractibleSpace ⟨0, mem_closedBall_self zero_le_one⟩
  let e₁ : P ≃ₜ range ι := (hι.isClosedEmbedding hinj).isEmbedding.toHomeomorph
  let e₂ : closedBall (0 : E³) 1 ≃ₜ range g :=
    (hg.isClosedEmbedding hginj).isEmbedding.toHomeomorph
  let e : P ≃ₜ closedBall (0 : E³) 1 :=
    (e₁.trans (Homeomorph.setCongr (heq.trans hrange.symm))).trans e₂.symm
  exact e.toHomotopyEquiv.simplyConnectedSpace_iff.mpr inferInstance

private theorem image_ball_eq_of_subset {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [ChartedSpace E³ Y] (G : PartialDiffeomorph (𝓡 3) (𝓡 3) E³ Y ∞)
    (hG : closedBall (0 : E³) 1 ⊆ G.source) {O : Set Y} (hO : IsPreconnected O)
    (hOs : ∀ y ∈ O, y ∉ G '' sphere (0 : E³) 1) (hsub : G '' ball (0 : E³) 1 ⊆ O) :
    O = G '' ball (0 : E³) 1 := by
  refine Subset.antisymm ?_ hsub
  have hU₁ : IsOpen (G '' ball (0 : E³) 1) :=
    G.toOpenPartialHomeomorph.isOpen_image_of_subset_source isOpen_ball
      (ball_subset_closedBall.trans hG)
  have hK : IsCompact (G '' closedBall (0 : E³) 1) :=
    (isCompact_closedBall (0 : E³) 1).image_of_continuousOn
      (G.contMDiffOn_toFun.continuousOn.mono hG)
  have hcover : O ⊆ G '' ball (0 : E³) 1 ∪ (G '' closedBall (0 : E³) 1)ᶜ := by
    intro y hy
    by_cases h : y ∈ G '' closedBall (0 : E³) 1
    · left
      obtain ⟨x, hx, rfl⟩ := h
      rcases (mem_closedBall_zero_iff.mp hx).lt_or_eq with hlt | heq
      · exact ⟨x, mem_ball_zero_iff.mpr hlt, rfl⟩
      · exact absurd ⟨x, mem_sphere_zero_iff_norm.mpr heq, rfl⟩ (hOs _ hy)
    · exact Or.inr h
  rcases hO.subset_or_subset hU₁ hK.isClosed.isOpen_compl
    (Set.disjoint_compl_right_iff_subset.mpr (image_mono ball_subset_closedBall)) hcover with
    h | h
  · exact h
  · have h0 : G 0 ∈ O := hsub ⟨0, mem_ball_self one_pos, rfl⟩
    exact absurd ⟨0, mem_closedBall_self zero_le_one, rfl⟩ (h h0)

private theorem image_closedBall_eq {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace E³ Y] (G : PartialDiffeomorph (𝓡 3) (𝓡 3) E³ Y ∞) :
    G '' closedBall (0 : E³) 1 = G '' ball (0 : E³) 1 ∪ G '' sphere (0 : E³) 1 := by
  rw [← image_union, ball_union_sphere]

private theorem nonempty_diffeomorph_sphere_of_simplyConnected
    (A : ConnectedClosedOrientedManifold.{u} 3) [SimplyConnectedSpace A.Carrier] :
    Nonempty (A.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ standardThreeSphereLift.{u}.Carrier) := by
  obtain ⟨f⟩ := smooth_poincare_conjecture A.Carrier
  exact ⟨f.trans standardThreeSphereLiftDiffeomorph⟩

theorem isPrime_of_isIrreducible (M : ConnectedClosedOrientedManifold.{u} 3)
    (h : IsIrreducible M) : IsPrime M := by
  intro A B ⟨D⟩
  let c := (orientedBallChart A).toBallChart
  let d := (orientedBallChart B).toBallChart
  let a := boundaryAttachment.1.toHomeomorph
  let ι₁ : c.Punctured → (connectedSum A B).Carrier := ConnectedSumQuotient.inl c d a
  let ι₂ : d.Punctured → (connectedSum A B).Carrier := ConnectedSumQuotient.inr c d a
  obtain ⟨G₀, hG₀, hG₀s⟩ := h _ (Topology.Manifold.isSmoothEmbedding_diffeomorph_comp
    (𝓡 2) (𝓡 3) _ (isSmoothEmbedding_seamSphere A B) D.symm)
  let G := G₀.trans D.toPartialDiffeomorph
  have hι₁ : Continuous ι₁ := ConnectedSumQuotient.continuous_inl c d a
  have hι₂ : Continuous ι₂ := ConnectedSumQuotient.continuous_inr c d a
  have hG : closedBall (0 : E³) 1 ⊆ G.source := fun x hx => ⟨hG₀ hx, trivial⟩
  have hGs : G '' sphere (0 : E³) 1 = range (seamSphere A B) := by
    change (D ∘ G₀) '' sphere (0 : E³) 1 = _
    rw [image_comp, hG₀s, ← range_comp]
    congr 1
    funext z
    exact D.apply_symm_apply _
  have hSA : ∀ p, ι₁ p ∈ range (seamSphere A B) ↔ p ∉ outerSet c := by
    intro p
    constructor
    · rintro ⟨z, hz⟩
      rw [seamSphere_eq] at hz
      rw [← ConnectedSumQuotient.inl_injective c d a hz]
      exact boundaryMap_not_mem_outerSet c z
    · intro hp
      obtain ⟨z, rfl⟩ := exists_boundaryMap_of_not_mem_outerSet c p hp
      exact ⟨z, seamSphere_eq A B z⟩
  have hSB : ∀ q, ι₂ q ∈ range (seamSphere A B) ↔ q ∉ outerSet d := by
    intro q
    constructor
    · rintro ⟨z, hz⟩
      rw [seamSphere_eq] at hz
      obtain ⟨w, -, rfl⟩ := (ConnectedSumQuotient.inl_eq_inr_iff c d a _ q).mp hz
      exact boundaryMap_not_mem_outerSet d _
    · intro hq
      obtain ⟨w, rfl⟩ := exists_boundaryMap_of_not_mem_outerSet d q hq
      refine ⟨a.symm w, ?_⟩
      rw [seamSphere_eq, ConnectedSumQuotient.boundary_eq, Homeomorph.apply_symm_apply]
  have hOA : IsOpen (ι₁ '' outerSet c) :=
    ConnectedSumQuotient.isOpen_image_inl c d a (isOpen_outerSet c)
      (boundaryMap_not_mem_outerSet c)
  have hOB : IsOpen (ι₂ '' outerSet d) :=
    ConnectedSumQuotient.isOpen_image_inr c d a (isOpen_outerSet d)
      (boundaryMap_not_mem_outerSet d)
  have hAB : Disjoint (ι₁ '' outerSet c) (ι₂ '' outerSet d) := by
    rw [Set.disjoint_left]
    rintro _ ⟨p, hp, rfl⟩ ⟨q, -, hq⟩
    obtain ⟨z, rfl, -⟩ := (ConnectedSumQuotient.inl_eq_inr_iff c d a p q).mp hq.symm
    exact boundaryMap_not_mem_outerSet c z hp
  have hAs : ∀ y ∈ ι₁ '' outerSet c, y ∉ G '' sphere (0 : E³) 1 := by
    rintro _ ⟨p, hp, rfl⟩ hy
    rw [hGs] at hy
    exact (hSA p).mp hy hp
  have hBs : ∀ y ∈ ι₂ '' outerSet d, y ∉ G '' sphere (0 : E³) 1 := by
    rintro _ ⟨q, hq, rfl⟩ hy
    rw [hGs] at hy
    exact (hSB q).mp hy hq
  have hball : G '' ball (0 : E³) 1 ⊆ ι₁ '' outerSet c ∪ ι₂ '' outerSet d := by
    rintro _ ⟨x, hx, rfl⟩
    have hxs : G x ∉ range (seamSphere A B) := by
      rw [← hGs]
      rintro ⟨y, hy, hyx⟩
      have := G.injOn (hG (sphere_subset_closedBall hy)) (hG (ball_subset_closedBall hx)) hyx
      rw [this, mem_sphere_zero_iff_norm] at hy
      exact (mem_ball_zero_iff.mp hx).ne hy
    rcases ConnectedSumQuotient.jointly_surjective c d a (G x) with ⟨p, hp⟩ | ⟨q, hq⟩
    · refine Or.inl ⟨p, ?_, hp⟩
      by_contra hp'
      exact hxs (hp ▸ (hSA p).mpr hp')
    · refine Or.inr ⟨q, ?_, hq⟩
      by_contra hq'
      exact hxs (hq ▸ (hSB q).mpr hq')
  have hpre : IsPreconnected (G '' ball (0 : E³) 1) :=
    (convex_ball (0 : E³) 1).isPreconnected.image _
      (G.contMDiffOn_toFun.continuousOn.mono (ball_subset_closedBall.trans hG))
  rcases hpre.subset_or_subset hOA hOB hAB hball with hsub | hsub
  · left
    have hO := image_ball_eq_of_subset G hG
      ((isPreconnected_outerSet c).image _ hι₁.continuousOn)
      hAs hsub
    have heq : range ι₁ = G '' closedBall (0 : E³) 1 := by
      rw [image_closedBall_eq, ← hO, hGs]
      ext y
      constructor
      · rintro ⟨p, rfl⟩
        by_cases hp : p ∈ outerSet c
        · exact Or.inl ⟨p, hp, rfl⟩
        · exact Or.inr ((hSA p).mpr hp)
      · rintro (⟨p, -, rfl⟩ | ⟨z, rfl⟩)
        · exact ⟨p, rfl⟩
        · exact ⟨_, (seamSphere_eq A B z).symm⟩
    have := simplyConnectedSpace_of_range_eq_image_closedBall ι₁ hι₁
      (ConnectedSumQuotient.inl_injective c d a)
      G hG heq
    have := simplyConnectedSpace_of_punctured A c
    exact nonempty_diffeomorph_sphere_of_simplyConnected A
  · right
    have hO := image_ball_eq_of_subset G hG
      ((isPreconnected_outerSet d).image _ hι₂.continuousOn)
      hBs hsub
    have heq : range ι₂ = G '' closedBall (0 : E³) 1 := by
      rw [image_closedBall_eq, ← hO, hGs]
      ext y
      constructor
      · rintro ⟨q, rfl⟩
        by_cases hq : q ∈ outerSet d
        · exact Or.inl ⟨q, hq, rfl⟩
        · exact Or.inr ((hSB q).mpr hq)
      · rintro (⟨q, -, rfl⟩ | ⟨z, rfl⟩)
        · exact ⟨q, rfl⟩
        · rw [seamSphere_eq, ConnectedSumQuotient.boundary_eq]
          exact ⟨_, rfl⟩
    have := simplyConnectedSpace_of_range_eq_image_closedBall ι₂ hι₂
      (ConnectedSumQuotient.inr_injective c d a)
      G hG heq
    have := simplyConnectedSpace_of_punctured B d
    exact nonempty_diffeomorph_sphere_of_simplyConnected B

private theorem isPrime_sphereTwoTimesCircleLift_ulift :
    IsPrime sphereTwoTimesCircleLift.ulift.{0, u} := by
  let K : SphereTwoTimesCircle ≃ₜ (sphereTwoTimesCircleLift.ulift.{0, u}).Carrier :=
    sphereTwoTimesCircleModelCopy.equiv.toHomeomorph.trans
      (ClosedOrientedManifold.uliftDiffeomorph.{0, u}
        sphereTwoTimesCircleLift.toClosedOrientedManifold).toHomeomorph
  let p : (sphereTwoTimesCircleLift.ulift.{0, u}).Carrier := Classical.choice inferInstance
  obtain ⟨e⟩ := exists_fundamentalGroupMulEquivInt_sphereTwoTimesCircle (K.symm p)
  let f := (fundamentalGroupMulEquivOfHomotopyEquiv K.symm.toHomotopyEquiv p (K.symm p) rfl).trans e
  refine isPrime_of_commutative_fundamentalGroup _ p fun x y => f.injective ?_
  rw [map_mul, map_mul]
  exact mul_comm _ _

theorem isPrime_iff_isIrreducible_or_sphereTwoTimesCircle
    (M : ConnectedClosedOrientedManifold.{u} 3) :
    IsPrime M ↔ IsIrreducible M ∨
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph M.toClosedOrientedManifold
        sphereTwoTimesCircleLift.ulift.{0, u}.toClosedOrientedManifold) ∨
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph M.toClosedOrientedManifold
        sphereTwoTimesCircleLift.ulift.{0, u}.opposite.toClosedOrientedManifold) := by
  refine ⟨isIrreducible_or_sphereTwoTimesCircle_of_isPrime, ?_⟩
  rintro (h | ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩)
  · exact isPrime_of_isIrreducible M h
  · exact isPrime_of_diffeomorph f.1.symm isPrime_sphereTwoTimesCircleLift_ulift
  · exact isPrime_of_diffeomorph f.1.symm
      ((isPrime_opposite_iff _).mpr isPrime_sphereTwoTimesCircleLift_ulift)

end GC.Endpoint
