import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.BlockCharts
/-!
# Whole-manifold gluing of compatible smooth chart maps
Actual local diffeomorphisms covering both manifolds determine a global diffeomorphism.
The compatibility conditions concern the supplied local maps and their actual inverses.
-/
set_option autoImplicit false
noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff

namespace GC.Seifert

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
    {N : Type*} [TopologicalSpace N] [ChartedSpace G N] {ι : Type*}

def selectedChartMap (e : ι → PartialDiffeomorph I J M N ∞)
    (hsource : ∀ x, ∃ i, x ∈ (e i).source) (x : M) : N :=
  e (Classical.choose (hsource x)) x

theorem selectedChartMap_eq (e : ι → PartialDiffeomorph I J M N ∞)
    (hsource : ∀ x, ∃ i, x ∈ (e i).source)
    (hforward : ∀ i j x, x ∈ (e i).source → x ∈ (e j).source → e i x = e j x)
    (i : ι) (x : M) (hx : x ∈ (e i).source) : selectedChartMap e hsource x = e i x :=
  hforward _ i x (Classical.choose_spec (hsource x)) hx

theorem contMDiff_selectedChartMap (e : ι → PartialDiffeomorph I J M N ∞)
    (hsource : ∀ x, ∃ i, x ∈ (e i).source)
    (hforward : ∀ i j x, x ∈ (e i).source → x ∈ (e j).source → e i x = e j x) :
    ContMDiff I J ∞ (selectedChartMap e hsource) := by
  intro x
  obtain ⟨i, hi⟩ := hsource x
  have heq : selectedChartMap e hsource =ᶠ[𝓝 x] e i := by
    filter_upwards [(e i).open_source.mem_nhds hi] with y hy
    exact selectedChartMap_eq e hsource hforward i y hy
  exact heq.contMDiffAt_iff.mpr
    (((e i).contMDiffOn_toFun x hi).contMDiffAt ((e i).open_source.mem_nhds hi))

def gluePartialDiffeomorphs (e : ι → PartialDiffeomorph I J M N ∞)
    (hsource : ∀ x, ∃ i, x ∈ (e i).source)
    (htarget : ∀ y, ∃ i, y ∈ (e i).target)
    (hforward : ∀ i j x, x ∈ (e i).source → x ∈ (e j).source → e i x = e j x)
    (hbackward : ∀ i j y, y ∈ (e i).target → y ∈ (e j).target →
      (e i).symm y = (e j).symm y) : M ≃ₘ⟮I, J⟯ N where
  toFun := selectedChartMap e hsource
  invFun := selectedChartMap (fun i => (e i).symm) htarget
  left_inv x := by
    obtain ⟨i, hi⟩ := hsource x
    rw [selectedChartMap_eq e hsource hforward i x hi]
    rw [selectedChartMap_eq (fun i => (e i).symm) htarget hbackward i (e i x)
      ((e i).map_source hi)]
    exact (e i).left_inv hi
  right_inv y := by
    obtain ⟨i, hi⟩ := htarget y
    rw [selectedChartMap_eq (fun i => (e i).symm) htarget hbackward i y hi]
    rw [selectedChartMap_eq e hsource hforward i ((e i).symm y)
      ((e i).map_target hi)]
    exact (e i).right_inv hi
  contMDiff_toFun := contMDiff_selectedChartMap e hsource hforward
  contMDiff_invFun := contMDiff_selectedChartMap (fun i => (e i).symm) htarget hbackward

theorem gluePartialDiffeomorphs_apply (e : ι → PartialDiffeomorph I J M N ∞)
    (hsource : ∀ x, ∃ i, x ∈ (e i).source)
    (htarget : ∀ y, ∃ i, y ∈ (e i).target)
    (hforward : ∀ i j x, x ∈ (e i).source → x ∈ (e j).source → e i x = e j x)
    (hbackward : ∀ i j y, y ∈ (e i).target → y ∈ (e j).target →
      (e i).symm y = (e j).symm y)
    (i : ι) (x : M) (hx : x ∈ (e i).source) :
    gluePartialDiffeomorphs e hsource htarget hforward hbackward x = e i x :=
  selectedChartMap_eq e hsource hforward i x hx

def partialDiffeomorphSourceOpen (e : PartialDiffeomorph I J M N ∞)
    (U : TopologicalSpace.Opens M) (hU : Nonempty U) :
    PartialDiffeomorph I J U N ∞ :=
  (DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal U hU).trans e

theorem partialDiffeomorphSourceOpen_source (e : PartialDiffeomorph I J M N ∞)
    (U : TopologicalSpace.Opens M) (hU : Nonempty U) :
    (partialDiffeomorphSourceOpen e U hU).source = Subtype.val ⁻¹' e.source := by
  change (e.toOpenPartialHomeomorph.subtypeRestr hU).source = _
  exact e.toOpenPartialHomeomorph.subtypeRestr_source hU

theorem partialDiffeomorphSourceOpen_target (e : PartialDiffeomorph I J M N ∞)
    (U : TopologicalSpace.Opens M) (hU : Nonempty U) (hs : e.source ⊆ U) :
    (partialDiffeomorphSourceOpen e U hU).target = e.target := by
  change (e.toOpenPartialHomeomorph.subtypeRestr hU).target = e.target
  rw [OpenPartialHomeomorph.subtypeRestr_def, OpenPartialHomeomorph.trans_target,
    TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target]
  exact inter_eq_left.mpr (fun y hy => hs (e.map_target hy))

theorem partialDiffeomorphSourceOpen_apply (e : PartialDiffeomorph I J M N ∞)
    (U : TopologicalSpace.Opens M) (hU : Nonempty U) (x : U) :
    partialDiffeomorphSourceOpen e U hU x = e x := rfl

theorem partialDiffeomorphSourceOpen_symm_apply (e : PartialDiffeomorph I J M N ∞)
    (U : TopologicalSpace.Opens M) (hU : Nonempty U) (hs : e.source ⊆ U)
    (y : N) (hy : y ∈ e.target) :
    ((partialDiffeomorphSourceOpen e U hU).symm y : M) = e.symm y := by
  change U.openPartialHomeomorphSubtypeCoe hU
    ((U.openPartialHomeomorphSubtypeCoe hU).symm (e.symm y)) = e.symm y
  apply (U.openPartialHomeomorphSubtypeCoe hU).right_inv
  rw [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target]
  exact hs (e.map_target hy)

def partialDiffeomorphOnOpens (e : PartialDiffeomorph I J M N ∞)
    (U : TopologicalSpace.Opens M) (V : TopologicalSpace.Opens N)
    (hU : Nonempty U) (hV : Nonempty V) : PartialDiffeomorph I J U V ∞ :=
  (partialDiffeomorphSourceOpen (partialDiffeomorphSourceOpen e U hU).symm V hV).symm

theorem partialDiffeomorphOnOpens_source (e : PartialDiffeomorph I J M N ∞)
    (U : TopologicalSpace.Opens M) (V : TopologicalSpace.Opens N)
    (hU : Nonempty U) (hV : Nonempty V) (hs : e.source ⊆ U) (ht : e.target ⊆ V) :
    (partialDiffeomorphOnOpens e U V hU hV).source = Subtype.val ⁻¹' e.source := by
  have hinner : (partialDiffeomorphSourceOpen e U hU).symm.source ⊆ V := by
    change (partialDiffeomorphSourceOpen e U hU).target ⊆ V
    rwa [partialDiffeomorphSourceOpen_target e U hU hs]
  change (partialDiffeomorphSourceOpen
    (partialDiffeomorphSourceOpen e U hU).symm V hV).target = _
  rw [partialDiffeomorphSourceOpen_target _ V hV hinner]
  exact partialDiffeomorphSourceOpen_source e U hU

theorem partialDiffeomorphOnOpens_target (e : PartialDiffeomorph I J M N ∞)
    (U : TopologicalSpace.Opens M) (V : TopologicalSpace.Opens N)
    (hU : Nonempty U) (hV : Nonempty V) (hs : e.source ⊆ U) :
    (partialDiffeomorphOnOpens e U V hU hV).target = Subtype.val ⁻¹' e.target := by
  change (partialDiffeomorphSourceOpen
    (partialDiffeomorphSourceOpen e U hU).symm V hV).source = _
  rw [partialDiffeomorphSourceOpen_source]
  change Subtype.val ⁻¹' (partialDiffeomorphSourceOpen e U hU).target = _
  rw [partialDiffeomorphSourceOpen_target e U hU hs]

theorem partialDiffeomorphOnOpens_apply (e : PartialDiffeomorph I J M N ∞)
    (U : TopologicalSpace.Opens M) (V : TopologicalSpace.Opens N)
    (hU : Nonempty U) (hV : Nonempty V) (ht : e.target ⊆ V)
    (x : U) (hx : (x : M) ∈ e.source) :
    (partialDiffeomorphOnOpens e U V hU hV x : N) = e x := by
  apply partialDiffeomorphSourceOpen_symm_apply
  · change (partialDiffeomorphSourceOpen e U hU).target ⊆ V
    intro y hy
    exact ht (e.toOpenPartialHomeomorph.subtypeRestr_target_subset hU hy)
  · change x ∈ (partialDiffeomorphSourceOpen e U hU).source
    rwa [partialDiffeomorphSourceOpen_source]

theorem partialDiffeomorphOnOpens_symm_apply (e : PartialDiffeomorph I J M N ∞)
    (U : TopologicalSpace.Opens M) (V : TopologicalSpace.Opens N)
    (hU : Nonempty U) (hV : Nonempty V) (hs : e.source ⊆ U)
    (y : V) (hy : (y : N) ∈ e.target) :
    ((partialDiffeomorphOnOpens e U V hU hV).symm y : M) = e.symm y :=
  partialDiffeomorphSourceOpen_symm_apply e U hU hs y hy

def gluePartialDiffeomorphsOnOpens (e : ι → PartialDiffeomorph I J M N ∞)
    (U : TopologicalSpace.Opens M) (V : TopologicalSpace.Opens N)
    (hU : Nonempty U) (hV : Nonempty V)
    (hs : ∀ i, (e i).source ⊆ U) (ht : ∀ i, (e i).target ⊆ V)
    (hsource : ∀ x ∈ U, ∃ i, x ∈ (e i).source)
    (htarget : ∀ y ∈ V, ∃ i, y ∈ (e i).target)
    (hforward : ∀ i j x, x ∈ (e i).source → x ∈ (e j).source → e i x = e j x)
    (hbackward : ∀ i j y, y ∈ (e i).target → y ∈ (e j).target →
      (e i).symm y = (e j).symm y) : U ≃ₘ⟮I, J⟯ V := by
  let patches := fun i => partialDiffeomorphOnOpens (e i) U V hU hV
  have hsrc (i : ι) (x : U) : x ∈ (patches i).source ↔ (x : M) ∈ (e i).source := by
    rw [partialDiffeomorphOnOpens_source (e i) U V hU hV (hs i) (ht i)]
    rfl
  have htgt (i : ι) (y : V) : y ∈ (patches i).target ↔ (y : N) ∈ (e i).target := by
    rw [partialDiffeomorphOnOpens_target (e i) U V hU hV (hs i)]
    rfl
  refine gluePartialDiffeomorphs patches ?_ ?_ ?_ ?_
  · intro x
    obtain ⟨i, hi⟩ := hsource x x.property
    exact ⟨i, (hsrc i x).mpr hi⟩
  · intro y
    obtain ⟨i, hi⟩ := htarget y y.property
    exact ⟨i, (htgt i y).mpr hi⟩
  · intro i j x hi hj
    apply Subtype.ext
    rw [partialDiffeomorphOnOpens_apply (e i) U V hU hV (ht i) x ((hsrc i x).mp hi),
      partialDiffeomorphOnOpens_apply (e j) U V hU hV (ht j) x ((hsrc j x).mp hj)]
    exact hforward i j x ((hsrc i x).mp hi) ((hsrc j x).mp hj)
  · intro i j y hi hj
    apply Subtype.ext
    rw [partialDiffeomorphOnOpens_symm_apply (e i) U V hU hV (hs i) y
      ((htgt i y).mp hi), partialDiffeomorphOnOpens_symm_apply (e j) U V hU hV (hs j) y
      ((htgt j y).mp hj)]
    exact hbackward i j y ((htgt i y).mp hi) ((htgt j y).mp hj)

end GC.Seifert
