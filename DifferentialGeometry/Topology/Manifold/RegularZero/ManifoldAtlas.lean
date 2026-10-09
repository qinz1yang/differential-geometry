import DifferentialGeometry.Topology.Manifold.RegularZero.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Finite regular-zero atlases on manifolds

A regular zero fibre of a finite differentiable map receives charts from actual ambient
extended charts and finite regular-zero coordinates. The topology is the original subtype topology.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Function Manifold
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Manifold.RegularZero

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {m : ℕ∞ω}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I m M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

def ambientChart (x : M) : PartialDiffeomorph I 𝓘(ℝ, E) M E m where
  toPartialEquiv := extChartAt I x
  open_source := isOpen_extChartAt_source x
  open_target := isOpen_extChartAt_target x
  contMDiffOn_toFun := by
    simpa only [extChartAt_source] using (contMDiffOn_extChartAt (I := I) (n := m) (x := x))
  contMDiffOn_invFun := contMDiffOn_extChartAt_symm x

theorem exists_manifold_coordinates (hm : m ≠ 0) (t : M → F)
    (ht : ContMDiff I 𝓘(ℝ, F) m t) {a : M}
    (hreg : Surjective (mvfderiv I t a)) :
    ∃ Φ : PartialDiffeomorph I
        𝓘(ℝ, F × (Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ))
        M (F × (Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ)) m,
      a ∈ Φ.source ∧ (∀ x ∈ Φ.source, (Φ x).1 = t x) ∧ (Φ a).2 = 0 := by
  let : IsManifold I 1 M := IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.mpr hm)
  let c := ambientChart (I := I) (m := m) a
  let g : E → F := t ∘ c.symm
  have ha : a ∈ c.source := mem_extChartAt_source a
  have hca : c a ∈ c.target := c.map_source ha
  have hg : ContDiffOn ℝ m g c.target :=
    contMDiffOn_iff_contDiffOn.mp (ht.comp_contMDiffOn c.symm.contMDiffOn)
  have hcD := (c.symm.contMDiffOn.contMDiffAt (c.open_target.mem_nhds hca)).mdifferentiableAt hm
  have htD := (ht a).mdifferentiableAt hm
  have hcomp := mvfderiv_comp_of_eq htD hcD (c.left_inv ha)
  have hccomp := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'
    (I := I) (x := a) ha
  rw [I.range_eq_univ, mfderivWithin_univ] at hccomp
  have hgreg : Surjective (fderiv ℝ g (c a)) := by
    intro u
    obtain ⟨v, hv⟩ := hreg u
    let w := mfderiv I 𝓘(ℝ, E) c a v
    refine ⟨NormedSpace.fromTangentSpace (c a) w, ?_⟩
    have hh := DFunLike.congr_fun hcomp w
    have hc_inv : c.symm.toPartialEquiv (c a) = a := c.left_inv ha
    have he : mfderiv 𝓘(ℝ, E) I c.symm (c a) w = v := by
      exact DFunLike.congr_fun hccomp v
    change mvfderiv 𝓘(ℝ, E) g (c a) w =
      mvfderiv I t (c.symm (c a)) (mfderiv 𝓘(ℝ, E) I c.symm (c a) w) at hh
    erw [he, hc_inv] at hh
    rw [← hv]
    simpa only [mvfderiv_eq_fderiv, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe] using hh
  obtain ⟨Φ, hΦa, hΦS, hΦ, hΦ0⟩ := exists_coordinates_finrank hm c.open_target hg hca hgreg
  refine ⟨c.trans Φ, ⟨ha, hΦa⟩, ?_, hΦ0⟩
  intro x hx
  change (Φ (c x)).1 = t x
  rw [hΦ, show g (c x) = t x from congrArg t (c.left_inv hx.1)]

section NativeSlice
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

def manifoldFiberChart (t : M → F) (Φ : PartialDiffeomorph I 𝓘(ℝ, F × P) M (F × P) m)
    (hΦ : ∀ x ∈ Φ.source, (Φ x).1 = t x) (a : {x : M // t x = 0}) :
    OpenPartialHomeomorph {x : M // t x = 0} P := by
  classical
  have hzero {z : P} (hz : (0, z) ∈ Φ.target) : t (Φ.symm (0, z)) = 0 := by
    exact (hΦ _ (Φ.map_target hz)).symm.trans (congrArg Prod.fst (Φ.right_inv hz))
  let inv : P → {x : M // t x = 0} :=
    fun z => if hz : (0, z) ∈ Φ.target then ⟨Φ.symm (0, z), hzero hz⟩ else a
  have hp (x : {x : M // t x = 0}) (hx : x.val ∈ Φ.source) :
      (0, (Φ x.val).2) = Φ x.val := Prod.ext ((hΦ _ hx).trans x.property).symm rfl
  refine { toFun := fun x => (Φ x.val).2
           invFun := inv
           source := Subtype.val ⁻¹' Φ.source
           target := (fun z => (0, z)) ⁻¹' Φ.target
           map_source' := ?_
           map_target' := ?_
           left_inv' := ?_
           right_inv' := ?_
           open_source := Φ.open_source.preimage continuous_subtype_val
           open_target := Φ.open_target.preimage (continuous_const.prodMk continuous_id)
           continuousOn_toFun := ?_
           continuousOn_invFun := ?_ }
  · intro x hx
    change (0, (Φ x.val).2) ∈ Φ.target
    rw [hp x hx]
    exact Φ.map_source hx
  · intro z hz
    change (0, z) ∈ Φ.target at hz
    change (inv z).val ∈ Φ.source
    simp only [inv, dite_eq_left hz]
    exact Φ.map_target hz
  · intro x hx
    have hz : (0, (Φ x.val).2) ∈ Φ.target := by rw [hp x hx]; exact Φ.map_source hx
    apply Subtype.ext
    simp only [inv, dite_eq_left hz]
    rw [hp x hx]
    exact Φ.left_inv hx
  · intro z hz
    change (0, z) ∈ Φ.target at hz
    simp only [inv, dite_eq_left hz]
    exact congrArg Prod.snd (Φ.right_inv hz)
  · exact (Φ.toOpenPartialHomeomorph.continuousOn.comp continuous_subtype_val.continuousOn
      (fun x hx => hx)).snd
  · apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
    apply (Φ.symm.toOpenPartialHomeomorph.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn (fun z hz => hz)).congr
    intro z hz
    change (0, z) ∈ Φ.target at hz
    simp only [comp_apply, inv, dite_eq_left hz]
    rfl

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I m M]
  [FiniteDimensional ℝ F] in
theorem manifoldFiberChart_symm_apply (t : M → F)
    (Φ : PartialDiffeomorph I 𝓘(ℝ, F × P) M (F × P) m)
    (hΦ : ∀ x ∈ Φ.source, (Φ x).1 = t x) (a : {x : M // t x = 0})
    {z : P} (hz : z ∈ (manifoldFiberChart t Φ hΦ a).target) :
    ((manifoldFiberChart t Φ hΦ a).symm z).val = Φ.symm (0, z) := by
  classical
  change ((if hz' : (0, z) ∈ Φ.target then ⟨Φ.symm (0, z), _⟩ else a) :
    {x : M // t x = 0}).val = _
  rw [dite_eq_left (show (0, z) ∈ Φ.target from hz)]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I m M]
  [FiniteDimensional ℝ F] in
theorem contMDiffOn_manifoldFiberChart_symm (t : M → F)
    (Φ : PartialDiffeomorph I 𝓘(ℝ, F × P) M (F × P) m)
    (hΦ : ∀ x ∈ Φ.source, (Φ x).1 = t x) (a : {x : M // t x = 0}) :
    ContMDiffOn 𝓘(ℝ, P) I m (fun z => ((manifoldFiberChart t Φ hΦ a).symm z).val)
      (manifoldFiberChart t Φ hΦ a).target := by
  apply (Φ.symm.contMDiffOn.comp
    (contDiff_const.prodMk contDiff_id).contMDiff.contMDiffOn (fun z hz => hz)).congr
  intro z hz
  exact manifoldFiberChart_symm_apply t Φ hΦ a hz

end NativeSlice

def manifoldCoordinates (hm : m ≠ 0) (t : M → F)
    (ht : ContMDiff I 𝓘(ℝ, F) m t)
    (hreg : ∀ x, t x = 0 → Surjective (mvfderiv I t x)) (z : {x : M // t x = 0}) :=
  (exists_manifold_coordinates hm t ht (hreg z.val z.property)).choose

theorem manifoldCoordinates_spec (hm : m ≠ 0) (t : M → F)
    (ht : ContMDiff I 𝓘(ℝ, F) m t)
    (hreg : ∀ x, t x = 0 → Surjective (mvfderiv I t x)) (z : {x : M // t x = 0}) :
    z.val ∈ (manifoldCoordinates hm t ht hreg z).source ∧
      (∀ x ∈ (manifoldCoordinates hm t ht hreg z).source,
        (manifoldCoordinates hm t ht hreg z x).1 = t x) ∧
      (manifoldCoordinates hm t ht hreg z z.val).2 = 0 :=
  (exists_manifold_coordinates hm t ht (hreg z.val z.property)).choose_spec

def manifoldChart (hm : m ≠ 0) (t : M → F) (ht : ContMDiff I 𝓘(ℝ, F) m t)
    (hreg : ∀ x, t x = 0 → Surjective (mvfderiv I t x)) (z : {x : M // t x = 0}) :
    OpenPartialHomeomorph {x : M // t x = 0}
      (Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ) :=
  manifoldFiberChart t (manifoldCoordinates hm t ht hreg z)
    (manifoldCoordinates_spec hm t ht hreg z).2.1 z

theorem mem_manifoldChart_source (hm : m ≠ 0) (t : M → F)
    (ht : ContMDiff I 𝓘(ℝ, F) m t)
    (hreg : ∀ x, t x = 0 → Surjective (mvfderiv I t x)) (z : {x : M // t x = 0}) :
    z ∈ (manifoldChart hm t ht hreg z).source :=
  (manifoldCoordinates_spec hm t ht hreg z).1

theorem contMDiffOn_manifoldChart_symm (hm : m ≠ 0) (t : M → F)
    (ht : ContMDiff I 𝓘(ℝ, F) m t)
    (hreg : ∀ x, t x = 0 → Surjective (mvfderiv I t x)) (z : {x : M // t x = 0}) :
    ContMDiffOn 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ) I m
      (fun v => ((manifoldChart hm t ht hreg z).symm v).val)
      (manifoldChart hm t ht hreg z).target :=
  contMDiffOn_manifoldFiberChart_symm t _ _ z

@[reducible]
def manifoldChartedSpace (hm : m ≠ 0) (t : M → F) (ht : ContMDiff I 𝓘(ℝ, F) m t)
    (hreg : ∀ x, t x = 0 → Surjective (mvfderiv I t x)) :
    ChartedSpace (Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ) {x : M // t x = 0} where
  atlas := range (manifoldChart hm t ht hreg)
  chartAt := manifoldChart hm t ht hreg
  mem_chart_source := mem_manifoldChart_source hm t ht hreg
  chart_mem_atlas z := ⟨z, rfl⟩

theorem manifold_isManifold (hm : m ≠ 0) (t : M → F) (ht : ContMDiff I 𝓘(ℝ, F) m t)
    (hreg : ∀ x, t x = 0 → Surjective (mvfderiv I t x)) :
    let _ := manifoldChartedSpace hm t ht hreg
    IsManifold 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ) m
      {x : M // t x = 0} := by
  let _ := manifoldChartedSpace hm t ht hreg
  apply isManifold_of_contDiffOn
  rintro c c' ⟨x, rfl⟩ ⟨y, rfl⟩
  let Φ := manifoldCoordinates hm t ht hreg y
  have h := Φ.contMDiffOn.comp
    ((contMDiffOn_manifoldChart_symm hm t ht hreg x).mono inter_subset_left)
    (fun z hz => hz.2)
  simp only [mfld_simps]
  change ContDiffOn ℝ m
    (fun v => (Φ ((manifoldChart hm t ht hreg x).symm v).val).2)
    ((manifoldChart hm t ht hreg x).target ∩
      (fun v => ((manifoldChart hm t ht hreg x).symm v).val) ⁻¹' Φ.source)
  exact (contMDiffOn_iff_contDiffOn.mp h).snd

theorem contMDiff_manifold_val (hm : m ≠ 0) (t : M → F)
    (ht : ContMDiff I 𝓘(ℝ, F) m t)
    (hreg : ∀ x, t x = 0 → Surjective (mvfderiv I t x)) :
    let _ := manifoldChartedSpace hm t ht hreg
    ContMDiff 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ) I m
      (Subtype.val : {x : M // t x = 0} → M) := by
  dsimp only
  let _ := manifoldChartedSpace hm t ht hreg
  let _ := manifold_isManifold hm t ht hreg
  intro z
  let P := Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ
  let c := manifoldChart hm t ht hreg z
  have hz : z ∈ c.source := mem_manifoldChart_source hm t ht hreg z
  have h := (contMDiffOn_manifoldChart_symm hm t ht hreg z).contMDiffAt
    (c.open_target.mem_nhds (c.map_source hz))
  have hh := h.comp z (contMDiffAt_extChartAt (I := 𝓘(ℝ, P)) (n := m) (x := z))
  apply hh.congr_of_eventuallyEq
  filter_upwards [chart_source_mem_nhds P z] with w hw
  exact (congrArg Subtype.val (c.left_inv hw)).symm

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

theorem contMDiff_manifold_lift (hm : m ≠ 0) (t : M → F)
    (ht : ContMDiff I 𝓘(ℝ, F) m t)
    (hreg : ∀ x, t x = 0 → Surjective (mvfderiv I t x))
    (f : N → M) (hf : ContMDiff J I m f) (hzero : ∀ x, t (f x) = 0) :
    letI := manifoldChartedSpace hm t ht hreg
    ContMDiff J 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ) m
      (fun x => (⟨f x, hzero x⟩ : {x : M // t x = 0})) := by
  let _ := manifoldChartedSpace hm t ht hreg
  intro x
  let z : {x : M // t x = 0} := ⟨f x, hzero x⟩
  let Φ := manifoldCoordinates hm t ht hreg z
  have hz : f x ∈ Φ.source := (manifoldCoordinates_spec hm t ht hreg z).1
  rw [contMDiffAt_iff_target]
  refine ⟨(hf.continuous.subtype_mk hzero).continuousAt, ?_⟩
  change ContMDiffAt J
    𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ) m
    (fun y => (Φ (f y)).2) x
  exact contDiff_snd.contMDiff.contMDiffAt.comp x
    ((Φ.contMDiffOn.contMDiffAt (Φ.open_source.mem_nhds hz)).comp x (hf x))

theorem contMDiffWithinAt_manifold_lift_of_le {n : ℕ∞ω} (hn : n ≤ m)
    (hm : m ≠ 0) (t : M → F) (ht : ContMDiff I 𝓘(ℝ, F) m t)
    (hreg : ∀ x, t x = 0 → Surjective (mvfderiv I t x))
    (f : N → M) {s : Set N} {x : N} (hf : ContMDiffWithinAt J I n f s x)
    (hzero : ∀ y, t (f y) = 0) :
    letI := manifoldChartedSpace hm t ht hreg
    ContMDiffWithinAt J 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ) n
      (fun y => (⟨f y, hzero y⟩ : {x : M // t x = 0})) s x := by
  let _ := manifoldChartedSpace hm t ht hreg
  let z : {x : M // t x = 0} := ⟨f x, hzero x⟩
  let Φ := manifoldCoordinates hm t ht hreg z
  have hz : f x ∈ Φ.source := (manifoldCoordinates_spec hm t ht hreg z).1
  rw [contMDiffWithinAt_iff_target]
  refine ⟨(Topology.IsInducing.subtypeVal.continuousWithinAt_iff).mpr hf.continuousWithinAt, ?_⟩
  change ContMDiffWithinAt J
    𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ) n
    (fun y => (Φ (f y)).2) s x
  have hΦ := (Φ.contMDiffOn.of_le hn).contMDiffAt (Φ.open_source.mem_nhds hz)
  exact contDiff_snd.contMDiff.contMDiffAt.comp_contMDiffWithinAt x
    (hΦ.comp_contMDiffWithinAt x hf)

theorem contMDiff_manifold_lift_of_le {n : ℕ∞ω} (hn : n ≤ m) (hm : m ≠ 0) (t : M → F)
    (ht : ContMDiff I 𝓘(ℝ, F) m t)
    (hreg : ∀ x, t x = 0 → Surjective (mvfderiv I t x))
    (f : N → M) (hf : ContMDiff J I n f) (hzero : ∀ y, t (f y) = 0) :
    letI := manifoldChartedSpace hm t ht hreg
    ContMDiff J 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ) n
      (fun y => (⟨f y, hzero y⟩ : {x : M // t x = 0})) := by
  let _ := manifoldChartedSpace hm t ht hreg
  intro x
  exact contMDiffWithinAt_manifold_lift_of_le hn hm t ht hreg f (hf x) hzero

end DifferentialGeometry.Manifold.RegularZero
