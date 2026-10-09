import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Edges
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyInteriorSublevel
import DifferentialGeometry.Topology.Manifold.OpenSubtype

/-!
# E4 binder, part 1: the sublevel manifold over an open compact part of the edge base

Draft 74, package E4 (`EdgeComponentModels.circleTriv`). For `P : EdgeBundle W` and an open compact
set `B` of the base, the part of the edge piece over `B`,
`N = {x ∈ source | proj x ∈ B ∧ height x ≤ level}`, is a compact `𝓡∂ 3` manifold:

* `exists_regular_extension_agree_ECM`: the cutoff extension of the tree's
  `exists_regular_extension_of_interior_sublevel`, with the extra clause that the global function
  agrees with the defining function near the sublevel (needed to compare differentials);
* `EdgeBundle.heightExt_ECM`, `overOpen_ECM`, the regularity of the level `{height = level}`
  (from `rank_two`) and the compactness of `N` (from `proper`);
* `EdgeBundle.sublevelFn_ECM` (the chosen extension), `EdgeBundle.Total_ECM` (its sublevel with the
  tree's slice structure `carrierSublevelChartedSpace`) with the named instances, the smooth
  inclusion `val`, its bijective differential, the universal property for maps into `Total_ECM`,
  and the description of the boundary.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- **The cutoff extension with local agreement.** As
`exists_regular_extension_of_interior_sublevel` (`AssemblyInteriorSublevel.lean`), with the
additional conclusion that the global function agrees with `f` on a neighbourhood of every point
of the sublevel. -/
theorem exists_regular_extension_agree_ECM (W : CompactCarrier.{u})
    (U : TopologicalSpace.Opens W.Carrier) (hU : (U : Set W.Carrier) ⊆ W.interior)
    (f : W.Carrier → ℝ) (c : ℝ) (hf : ContMDiffOn W.model 𝓘(ℝ, ℝ) ∞ f U)
    (hreg : ∀ x ∈ U, f x = c → mfderiv W.model 𝓘(ℝ, ℝ) f x ≠ 0)
    (hK : IsCompact {x | x ∈ U ∧ f x ≤ c}) :
    ∃ F : W.Carrier → ℝ, ContMDiff W.model 𝓘(ℝ, ℝ) ∞ F ∧
      (∀ x, F x = c → mfderiv W.model 𝓘(ℝ, ℝ) F x ≠ 0) ∧
      (∀ x, F x = c → x ∈ W.interior) ∧
      (∀ x, F x ≤ c ↔ (x ∈ U ∧ f x ≤ c)) ∧
      (∀ x, F x = c ↔ (x ∈ U ∧ f x = c)) ∧
      ∀ x, x ∈ U → f x ≤ c → F =ᶠ[𝓝 x] f := by
  have hd : Disjoint (U : Set W.Carrier)ᶜ {x | x ∈ U ∧ f x ≤ c} :=
    disjoint_left.mpr fun x hx hx' => hx hx'.1
  obtain ⟨χ, hχ0, hχ1, hχI⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed W.model (n := ⊤)
    U.isOpen.isClosed_compl hK.isClosed hd
  let F : W.Carrier → ℝ := fun x => χ x * f x + (1 - χ x) * (c + 1)
  have hχK : ∀ x, x ∈ U → f x ≤ c → ∀ᶠ y in 𝓝 x, χ y = 1 := fun x hxU hfx =>
    hχ1.filter_mono (nhds_le_nhdsSet (show x ∈ {x | x ∈ U ∧ f x ≤ c} from ⟨hxU, hfx⟩))
  have hFK : ∀ x, x ∈ U → f x ≤ c → F =ᶠ[𝓝 x] f := fun x hxU hfx =>
    (hχK x hxU hfx).mono fun y hy => by simp only [F, hy, one_mul, sub_self, zero_mul, add_zero]
  have hFeqK : ∀ x, x ∈ U → f x ≤ c → F x = f x := fun x hxU hfx => (hFK x hxU hfx).self_of_nhds
  have hmemK : ∀ x, F x ≤ c → x ∈ U ∧ f x ≤ c := by
    intro x hx
    by_contra h
    apply (not_lt.mpr hx)
    by_cases hxU : x ∈ U
    · have hfx : c < f x := lt_of_not_ge fun h' => h ⟨hxU, h'⟩
      obtain ⟨h0, h1⟩ := hχI x
      rcases h1.lt_or_eq with hlt | heq
      · nlinarith [mul_nonneg h0 (sub_nonneg.mpr hfx.le)]
      · simp only [F, heq, one_mul, sub_self, zero_mul, add_zero]
        exact hfx
    · have h0 : χ x = 0 := hχ0.self_of_nhdsSet x hxU
      simp only [F, h0, zero_mul, sub_zero, one_mul, zero_add]
      linarith
  have hle : ∀ x, F x ≤ c ↔ (x ∈ U ∧ f x ≤ c) := fun x =>
    ⟨hmemK x, fun h => (hFeqK x h.1 h.2).symm ▸ h.2⟩
  have hsm : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (fun x => χ x * f x) := by
    intro x
    by_cases hxU : x ∈ U
    · exact (χ.contMDiff x).mul (hf.contMDiffAt (U.isOpen.mem_nhds hxU))
    · have hloc : (fun _ : W.Carrier => (0 : ℝ)) =ᶠ[𝓝 x] fun y => χ y * f y :=
        (hχ0.filter_mono (nhds_le_nhdsSet hxU)).mono fun y hy => by
          simp only [hy, zero_mul]
      exact contMDiffAt_const.congr_of_eventuallyEq hloc.symm
  have hFs : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ F :=
    hsm.add ((contMDiff_const.sub χ.contMDiff).mul contMDiff_const)
  refine ⟨F, hFs, ?_, ?_, hle, ?_, hFK⟩
  · intro x hx
    obtain ⟨hxU, hfx⟩ := hmemK x hx.le
    rw [(hFK x hxU hfx).mfderiv_eq]
    exact hreg x hxU ((hFeqK x hxU hfx).symm.trans hx)
  · intro x hx
    exact hU (hmemK x hx.le).1
  · intro x
    constructor
    · intro hx
      obtain ⟨hxU, hfx⟩ := hmemK x hx.le
      exact ⟨hxU, (hFeqK x hxU hfx) ▸ hx⟩
    · rintro ⟨hxU, hfx⟩
      rw [hFeqK x hxU hfx.le]
      exact hfx

namespace FC39P0

namespace EdgeBundle

variable {W : CompactCarrier.{u}} (P : EdgeBundle W)

open Classical in
/-- The height on `W` (zero off the source). -/
def heightExt_ECM : W.Carrier → ℝ := fun x =>
  if hx : x ∈ P.source then P.height ⟨x, hx⟩ else 0

theorem heightExt_apply_ECM (y : P.source) : P.heightExt_ECM y = P.height y := by
  simp [heightExt_ECM, y.2]

theorem heightExt_comp_val_ECM :
    P.heightExt_ECM ∘ (Subtype.val : P.source → W.Carrier) = P.height :=
  funext P.heightExt_apply_ECM

/-- The open set of `W` over an open set `B` of the base. -/
def overOpen_ECM (B : Set P.Base) (hB : IsOpen B) : TopologicalSpace.Opens W.Carrier :=
  ⟨Subtype.val '' (P.proj ⁻¹' B),
    P.source.isOpenEmbedding'.isOpenMap _ (hB.preimage P.proj.continuous)⟩

variable {P}

theorem mem_overOpen_ECM {B : Set P.Base} {hB : IsOpen B} {x : W.Carrier} :
    x ∈ P.overOpen_ECM B hB ↔ ∃ h : x ∈ P.source, P.proj ⟨x, h⟩ ∈ B := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨x, h⟩, hx, rfl⟩

theorem overOpen_subset_interior_ECM (B : Set P.Base) (hB : IsOpen B) :
    (P.overOpen_ECM B hB : Set W.Carrier) ⊆ W.interior := fun _ hx =>
  P.source_interior (mem_overOpen_ECM.mp hx).1

theorem contMDiffOn_heightExt_ECM :
    ContMDiffOn W.model 𝓘(ℝ, ℝ) ∞ P.heightExt_ECM P.source := by
  intro x hx
  have h : ContMDiffAt W.model 𝓘(ℝ, ℝ) ∞ (fun y : P.source => P.heightExt_ECM y) ⟨x, hx⟩ := by
    have := P.height_smooth (⟨x, hx⟩ : P.source)
    rwa [← P.heightExt_comp_val_ECM] at this
  exact (contMDiffAt_subtype_iff.mp h).contMDiffWithinAt

theorem mfderiv_heightExt_ECM (y : P.source) :
    mfderiv W.model 𝓘(ℝ, ℝ) P.heightExt_ECM y = mfderiv W.model 𝓘(ℝ, ℝ) P.height y := by
  have h := DifferentialGeometry.mfderiv_restrict_open (I := W.model) (J := 𝓘(ℝ, ℝ)) P.heightExt_ECM
    P.source y
  rw [show (fun z : P.source => P.heightExt_ECM z) = P.height from P.heightExt_comp_val_ECM] at h
  exact h.symm

/-- The level `{height = level}` is regular (from `rank_two`). -/
theorem heightExt_regular_ECM {x : W.Carrier} (hx : x ∈ P.source)
    (h0 : P.heightExt_ECM x = P.level) :
    mfderiv W.model 𝓘(ℝ, ℝ) P.heightExt_ECM x ≠ 0 := by
  intro hzero
  let y : P.source := ⟨x, hx⟩
  have hy : P.height y = P.level := (P.heightExt_apply_ECM y).symm.trans h0
  obtain ⟨v, hv⟩ := P.rank_two y hy
    (show TangentSpace (𝓡 1) (P.proj y) × TangentSpace 𝓘(ℝ, ℝ) (P.height y) from (0, 1))
  have h1 : mfderiv W.model 𝓘(ℝ, ℝ) P.height y v = 1 := congrArg Prod.snd hv
  have h2 := mfderiv_heightExt_ECM (P := P) y
  rw [show ((y : P.source) : W.Carrier) = x from rfl, hzero] at h2
  have h3 : mfderiv W.model 𝓘(ℝ, ℝ) P.height y v = 0 := by
    rw [← h2]
    rfl
  have h4 : (1 : ℝ) = 0 := h1.symm.trans h3
  exact one_ne_zero h4

/-- The part of the edge piece over a compact open set of the base is compact. -/
theorem isCompact_sublevel_ECM {B : Set P.Base} (hB : IsOpen B) (hBk : IsCompact B) :
    IsCompact {x | x ∈ P.overOpen_ECM B hB ∧ P.heightExt_ECM x ≤ P.level} := by
  have h := P.proper B hBk
  convert h using 1
  ext x
  constructor
  · rintro ⟨hx, hle⟩
    obtain ⟨hs, hb⟩ := mem_overOpen_ECM.mp hx
    exact ⟨⟨x, hs⟩, ⟨hb, (P.heightExt_apply_ECM ⟨x, hs⟩).symm.trans_le hle⟩, rfl⟩
  · rintro ⟨y, ⟨hb, hle⟩, rfl⟩
    exact ⟨mem_overOpen_ECM.mpr ⟨y.2, hb⟩, by rwa [heightExt_apply_ECM]⟩

variable (P) in
theorem exists_sublevelExt_ECM {B : Set P.Base} (hB : IsOpen B) (hBk : IsCompact B) :
    ∃ F : W.Carrier → ℝ, ContMDiff W.model 𝓘(ℝ, ℝ) ∞ F ∧
      (∀ x, F x = P.level → mfderiv W.model 𝓘(ℝ, ℝ) F x ≠ 0) ∧
      (∀ x, F x = P.level → x ∈ W.interior) ∧
      (∀ x, F x ≤ P.level ↔ (x ∈ P.overOpen_ECM B hB ∧ P.heightExt_ECM x ≤ P.level)) ∧
      (∀ x, F x = P.level ↔ (x ∈ P.overOpen_ECM B hB ∧ P.heightExt_ECM x = P.level)) ∧
      ∀ x, x ∈ P.overOpen_ECM B hB → P.heightExt_ECM x ≤ P.level →
        F =ᶠ[𝓝 x] P.heightExt_ECM :=
  exists_regular_extension_agree_ECM W (P.overOpen_ECM B hB) (overOpen_subset_interior_ECM B hB)
    P.heightExt_ECM P.level
    (P.contMDiffOn_heightExt_ECM.mono fun _ hx => (mem_overOpen_ECM.mp hx).1)
    (fun _ hx h0 => heightExt_regular_ECM (mem_overOpen_ECM.mp hx).1 h0)
    (isCompact_sublevel_ECM hB hBk)

variable (P) in
/-- A global smooth function on `W`, regular on its level `level`, whose sublevel is the part of the
edge piece over `B` (the cutoff extension of the height). -/
def sublevelFn_ECM {B : Set P.Base} (hB : IsOpen B) (hBk : IsCompact B) : W.Carrier → ℝ :=
  Classical.choose (P.exists_sublevelExt_ECM hB hBk)

section Spec

variable {B : Set P.Base} {hB : IsOpen B} {hBk : IsCompact B}

theorem contMDiff_sublevelFn_ECM :
    ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (P.sublevelFn_ECM hB hBk) :=
  (Classical.choose_spec (P.exists_sublevelExt_ECM hB hBk)).1

theorem sublevelFn_regular_ECM (x : W.Carrier) (h : P.sublevelFn_ECM hB hBk x = P.level) :
    mfderiv W.model 𝓘(ℝ, ℝ) (P.sublevelFn_ECM hB hBk) x ≠ 0 :=
  (Classical.choose_spec (P.exists_sublevelExt_ECM hB hBk)).2.1 x h

theorem sublevelFn_interior_ECM (x : W.Carrier) (h : P.sublevelFn_ECM hB hBk x = P.level) :
    x ∈ W.interior :=
  (Classical.choose_spec (P.exists_sublevelExt_ECM hB hBk)).2.2.1 x h

theorem sublevelFn_le_iff_ECM {x : W.Carrier} :
    P.sublevelFn_ECM hB hBk x ≤ P.level ↔
      (x ∈ P.overOpen_ECM B hB ∧ P.heightExt_ECM x ≤ P.level) :=
  (Classical.choose_spec (P.exists_sublevelExt_ECM hB hBk)).2.2.2.1 x

theorem sublevelFn_eq_iff_ECM {x : W.Carrier} :
    P.sublevelFn_ECM hB hBk x = P.level ↔
      (x ∈ P.overOpen_ECM B hB ∧ P.heightExt_ECM x = P.level) :=
  (Classical.choose_spec (P.exists_sublevelExt_ECM hB hBk)).2.2.2.2.1 x

theorem sublevelFn_eventuallyEq_ECM {x : W.Carrier} (hx : x ∈ P.overOpen_ECM B hB)
    (hle : P.heightExt_ECM x ≤ P.level) :
    P.sublevelFn_ECM hB hBk =ᶠ[𝓝 x] P.heightExt_ECM :=
  (Classical.choose_spec (P.exists_sublevelExt_ECM hB hBk)).2.2.2.2.2 x hx hle

end Spec

variable (P) in
/-- **The total space over `B`**: the sublevel of the extended height with the tree's slice
structure (`carrierSublevelChartedSpace`). -/
abbrev Total_ECM {B : Set P.Base} (hB : IsOpen B) (hBk : IsCompact B) : Type u :=
  {x : W.Carrier // P.sublevelFn_ECM hB hBk x ≤ P.level}

section Total

variable {B : Set P.Base} {hB : IsOpen B} {hBk : IsCompact B}

instance totalCharts_ECM : ChartedSpace (EuclideanHalfSpace 3) (P.Total_ECM hB hBk) :=
  carrierSublevelChartedSpace W (P.sublevelFn_ECM hB hBk) P.level
    P.contMDiff_sublevelFn_ECM P.sublevelFn_regular_ECM P.sublevelFn_interior_ECM

instance totalManifold_ECM : IsManifold (𝓡∂ 3) ∞ (P.Total_ECM hB hBk) :=
  carrierSublevel_isManifold W (P.sublevelFn_ECM hB hBk) P.level
    P.contMDiff_sublevelFn_ECM P.sublevelFn_regular_ECM P.sublevelFn_interior_ECM

instance totalCompact_ECM : CompactSpace (P.Total_ECM hB hBk) :=
  compactSpace_carrierSublevel W (P.sublevelFn_ECM hB hBk) P.level
    P.contMDiff_sublevelFn_ECM.continuous

theorem contMDiff_total_val_ECM :
    ContMDiff (𝓡∂ 3) W.model ∞ (Subtype.val : P.Total_ECM hB hBk → W.Carrier) :=
  carrierSublevel_contMDiff_val W (P.sublevelFn_ECM hB hBk) P.level
    P.contMDiff_sublevelFn_ECM P.sublevelFn_regular_ECM P.sublevelFn_interior_ECM

theorem mfderiv_total_val_bijective_ECM (x : P.Total_ECM hB hBk) :
    Bijective (mfderiv (𝓡∂ 3) W.model (Subtype.val : P.Total_ECM hB hBk → W.Carrier) x) :=
  carrierSublevel_mfderiv_val_bijective W (P.sublevelFn_ECM hB hBk) P.level
    P.contMDiff_sublevelFn_ECM P.sublevelFn_regular_ECM P.sublevelFn_interior_ECM x

/-- The universal property of the total space: a map into it is smooth iff its composite with the
inclusion is. -/
theorem contMDiff_total_iff_ECM {F' G' X : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    [TopologicalSpace G'] {J : ModelWithCorners ℝ F' G'} [TopologicalSpace X] [ChartedSpace G' X]
    {g : X → P.Total_ECM hB hBk} :
    ContMDiff J (𝓡∂ 3) ∞ g ↔ ContMDiff J W.model ∞ (Subtype.val ∘ g) :=
  DifferentialGeometry.Manifold.RegularLevel.slice_contMDiff_iff
    (carrierSublevel_sliceCharts W (P.sublevelFn_ECM hB hBk) P.level P.contMDiff_sublevelFn_ECM
      P.sublevelFn_regular_ECM P.sublevelFn_interior_ECM) le_rfl

theorem total_mem_overOpen_ECM (x : P.Total_ECM hB hBk) : x.1 ∈ P.overOpen_ECM B hB :=
  (sublevelFn_le_iff_ECM.mp x.2).1

theorem total_heightExt_le_ECM (x : P.Total_ECM hB hBk) : P.heightExt_ECM x.1 ≤ P.level :=
  (sublevelFn_le_iff_ECM.mp x.2).2

theorem total_mem_source_ECM (x : P.Total_ECM hB hBk) : x.1 ∈ P.source :=
  (mem_overOpen_ECM.mp (P.total_mem_overOpen_ECM x)).1

/-- The model boundary of the total space is the rim `{height = level}`. -/
theorem total_isBoundaryPoint_iff_ECM {x : P.Total_ECM hB hBk} :
    (𝓡∂ 3).IsBoundaryPoint x ↔ P.heightExt_ECM x.1 = P.level := by
  rw [carrierSublevel_isBoundaryPoint_iff (hf := P.contMDiff_sublevelFn_ECM)
    (hreg := P.sublevelFn_regular_ECM) (hint := P.sublevelFn_interior_ECM)]
  constructor
  · rintro (hb | h0)
    · exact absurd hb ((W.model.isInteriorPoint_iff_not_isBoundaryPoint _).mp
        (overOpen_subset_interior_ECM B hB (P.total_mem_overOpen_ECM x)))
    · exact (sublevelFn_eq_iff_ECM.mp h0).2
  · intro h0
    exact Or.inr (sublevelFn_eq_iff_ECM.mpr ⟨P.total_mem_overOpen_ECM x, h0⟩)

end Total

end EdgeBundle

end FC39P0

end GC.GraphManifold.Assembly
