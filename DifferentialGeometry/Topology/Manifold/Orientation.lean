import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.LinearAlgebra.Orientation
import DifferentialGeometry.Bundle.Orientation.Map
import DifferentialGeometry.Topology.Manifold.OpenSubtype
import DifferentialGeometry.Topology.Manifold.Paths
import DifferentialGeometry.Bundle.Orientation.Section

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]

def tangentChartEquiv (p x : M)
    (hx : x ∈ (trivializationAt E (TangentSpace I) p).baseSet) :
    TangentSpace I x ≃ₗ[ℝ] E :=
  (trivializationAt E (TangentSpace I) p).linearEquivAt ℝ x hx

structure ManifoldOrientation (n : ℕ) [FiniteDimensional ℝ E] where
  dimension_eq : Module.finrank ℝ E = n
  orientation : (x : M) → Orientation ℝ (TangentSpace I x) (Fin n)
  locally_constant : ∀ p x : M,
    ∀ hx : x ∈ (trivializationAt E (TangentSpace I) p).baseSet,
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∃ hU : U ⊆ (trivializationAt E (TangentSpace I) p).baseSet,
      ∀ y : M, ∀ hy : y ∈ U,
        Orientation.map (Fin n) (tangentChartEquiv I M p y (hU hy)) (orientation y) =
          Orientation.map (Fin n) (tangentChartEquiv I M p x hx) (orientation x)

namespace ManifoldOrientation

variable {I M} {n : ℕ} [FiniteDimensional ℝ E]

@[ext]
theorem ext {o₁ o₂ : ManifoldOrientation I M n}
    (h : ∀ x, o₁.orientation x = o₂.orientation x) : o₁ = o₂ := by
  cases o₁
  cases o₂
  congr
  exact funext h

def inChart (o : ManifoldOrientation I M n) (p x : M)
    (hx : x ∈ (trivializationAt E (TangentSpace I) p).baseSet) :
    Orientation ℝ E (Fin n) :=
  Orientation.map (Fin n) (tangentChartEquiv I M p x hx) (o.orientation x)

def opposite (o : ManifoldOrientation I M n) : ManifoldOrientation I M n where
  dimension_eq := o.dimension_eq
  orientation x := -o.orientation x
  locally_constant p x hx := by
    obtain ⟨U, hUopen, hxU, hU, h⟩ := o.locally_constant p x hx
    refine ⟨U, hUopen, hxU, hU, fun y hy ↦ ?_⟩
    simpa only [Orientation.map_neg] using congrArg Neg.neg (h y hy)

@[simp]
theorem opposite_orientation (o : ManifoldOrientation I M n) (x : M) :
    o.opposite.orientation x = -o.orientation x := rfl

@[simp]
theorem opposite_opposite (o : ManifoldOrientation I M n) :
    o.opposite.opposite = o := by
  apply ManifoldOrientation.ext
  intro x
  exact neg_neg (o.orientation x)

end ManifoldOrientation

section RestrictOpen

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ} [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem tangentChartEquiv_restrictOpen (U : TopologicalSpace.Opens M) (p x : U)
    (hx : x ∈ (trivializationAt E (TangentSpace I) p).baseSet)
    (hxM : x.1 ∈ (trivializationAt E (TangentSpace I) p.1).baseSet) :
    tangentChartEquiv I U p x hx = tangentChartEquiv I M p.1 x.1 hxM := by
  have hu : x ∈ (chartAt H p).source := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hx
  have hm : x.1 ∈ (chartAt H p.1).source := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hxM
  have hd : mfderiv I 𝓘(ℝ, E) (extChartAt I p : U → E) x =
      mfderiv I 𝓘(ℝ, E) (extChartAt I p.1 : M → E) x.1 :=
    DifferentialGeometry.mfderiv_restrict_open (extChartAt I p.1 : M → E) U x
  have hc : (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ x =
      (trivializationAt E (TangentSpace I) p.1).continuousLinearMapAt ℝ x.1 := by
    rw [TangentBundle.continuousLinearMapAt_trivializationAt hu,
      TangentBundle.continuousLinearMapAt_trivializationAt hm]
    exact hd
  apply LinearEquiv.ext
  intro v
  calc
    tangentChartEquiv I U p x hx v =
        (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ x v :=
      (Trivialization.continuousLinearMapAt_apply_of_mem ℝ
        (trivializationAt E (TangentSpace I) p) hx v).symm
    _ = (trivializationAt E (TangentSpace I) p.1).continuousLinearMapAt ℝ x.1 v :=
      congrArg (fun A : E →L[ℝ] E => A v) hc
    _ = tangentChartEquiv I M p.1 x.1 hxM v :=
      Trivialization.continuousLinearMapAt_apply_of_mem ℝ
        (trivializationAt E (TangentSpace I) p.1) hxM v

namespace ManifoldOrientation

def restrictOpen (o : ManifoldOrientation I M n) (U : TopologicalSpace.Opens M) :
    ManifoldOrientation I U n where
  dimension_eq := o.dimension_eq
  orientation x := o.orientation x.1
  locally_constant := by
    intro p x hx
    have hxM : x.1 ∈ (trivializationAt E (TangentSpace I) p.1).baseSet := by
      simpa only [TangentBundle.trivializationAt_baseSet, TopologicalSpace.Opens.chartAt_eq,
        OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hx
    obtain ⟨V, hVo, hxV, hVm, hV⟩ := o.locally_constant p.1 x.1 hxM
    let W : Set U := Subtype.val ⁻¹' V
    have hWm : W ⊆ (trivializationAt E (TangentSpace I) p).baseSet := by
      intro y hy
      simpa only [TangentBundle.trivializationAt_baseSet, TopologicalSpace.Opens.chartAt_eq,
        OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hVm hy
    refine ⟨W, hVo.preimage continuous_subtype_val, hxV, hWm, fun y hy => ?_⟩
    rw [tangentChartEquiv_restrictOpen U p y (hWm hy) (hVm hy),
      tangentChartEquiv_restrictOpen U p x hx hxM]
    exact hV y.1 hy

@[simp]
theorem restrictOpen_orientation (o : ManifoldOrientation I M n) (U : TopologicalSpace.Opens M)
    (x : U) : (o.restrictOpen U).orientation x = o.orientation x.1 := rfl

end ManifoldOrientation

end RestrictOpen

private theorem orientation_map_trans
    {A F G : Type*} [AddCommGroup A] [Module ℝ A]
    [AddCommGroup F] [Module ℝ F] [AddCommGroup G] [Module ℝ G]
    {n : ℕ} (e : A ≃ₗ[ℝ] F) (f : F ≃ₗ[ℝ] G) (o : Orientation ℝ A (Fin n)) :
    Orientation.map (Fin n) (e.trans f) o =
      Orientation.map (Fin n) f (Orientation.map (Fin n) e o) := by
  induction o using Module.Ray.ind with
  | h v hv => rfl

end DifferentialGeometry

namespace Diffeomorph

open DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {H' : Type*} [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} {N : Type*} [TopologicalSpace N]
  [ChartedSpace H' N] [IsManifold J ∞ N]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [FiniteDimensional ℝ G] {H'' : Type*} [TopologicalSpace H'']
  {K : ModelWithCorners ℝ G H''} {P : Type*} [TopologicalSpace P]
  [ChartedSpace H'' P] [IsManifold K ∞ P]
  {n : ℕ}

def preservesOrientation (f : M ≃ₘ⟮I, J⟯ N)
    (oM : ManifoldOrientation I M n) (oN : ManifoldOrientation J N n) : Prop :=
  ∀ x, Orientation.map (Fin n)
    (f.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
    (oM.orientation x) = oN.orientation (f x)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private theorem mfderivLinearEquiv_refl (x : M) :
    ((Diffeomorph.refl I M ∞).mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv =
      LinearEquiv.refl ℝ (TangentSpace I x) := by
  ext v
  change mfderiv I I id x v = v
  simp only [mfderiv_id, ContinuousLinearMap.id_apply]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [FiniteDimensional ℝ F] [IsManifold J ∞ N]
  [FiniteDimensional ℝ G] [IsManifold K ∞ P] in
private theorem mfderivLinearEquiv_trans (f : M ≃ₘ⟮I, J⟯ N)
    (g : N ≃ₘ⟮J, K⟯ P) (x : M) :
    ((f.trans g).mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv =
      (f.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv.trans
        (g.mfderivToContinuousLinearEquiv (by simp) (f x)).toLinearEquiv := by
  ext v
  exact mfderiv_comp_apply x (g.mdifferentiable (by simp) (f x))
    (f.mdifferentiable (by simp) x) v

theorem preservesOrientation_refl (o : ManifoldOrientation I M n) :
    (Diffeomorph.refl I M ∞).preservesOrientation o o := by
  intro x
  erw [mfderivLinearEquiv_refl, Orientation.map_refl]
  rfl

theorem preservesOrientation_trans {f : M ≃ₘ⟮I, J⟯ N} {g : N ≃ₘ⟮J, K⟯ P}
    {oM : ManifoldOrientation I M n} {oN : ManifoldOrientation J N n}
    {oP : ManifoldOrientation K P n}
    (hf : f.preservesOrientation oM oN) (hg : g.preservesOrientation oN oP) :
    (f.trans g).preservesOrientation oM oP := by
  intro x
  erw [mfderivLinearEquiv_trans, orientation_map_trans, hf x, hg (f x)]
  rfl

theorem preservesOrientation_symm {f : M ≃ₘ⟮I, J⟯ N}
    {oM : ManifoldOrientation I M n} {oN : ManifoldOrientation J N n}
    (hf : f.preservesOrientation oM oN) : f.symm.preservesOrientation oN oM := by
  intro y
  apply (Orientation.map (Fin n)
    (f.mfderivToContinuousLinearEquiv (by simp) (f.symm y)).toLinearEquiv).injective
  rw [hf (f.symm y)]
  have h := congrArg (fun e ↦ Orientation.map (Fin n) e (oN.orientation y))
    (mfderivLinearEquiv_trans f.symm f y)
  erw [f.symm_trans_self, mfderivLinearEquiv_refl, Orientation.map_refl,
    orientation_map_trans] at h
  convert! h.symm using 1
  congr 1
  exact f.apply_symm_apply y

theorem preservesOrientation_opposite {f : M ≃ₘ⟮I, J⟯ N}
    {oM : ManifoldOrientation I M n} {oN : ManifoldOrientation J N n}
    (hf : f.preservesOrientation oM oN) :
    f.preservesOrientation oM.opposite oN.opposite := by
  intro x
  simpa only [ManifoldOrientation.opposite_orientation, Orientation.map_neg] using
    congrArg Neg.neg (hf x)

end Diffeomorph

namespace DifferentialGeometry.Topology.Manifold

open Bundle Manifold
open scoped Manifold ContDiff

theorem exists_tangent_orientation_of_simply_connected
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [SimplyConnectedSpace M] (hdim : Module.finrank ℝ E = 3) :
    ∃ o : ∀ x : M, Orientation ℝ (TangentSpace 𝓘(ℝ, E) x) (Fin 3),
      DifferentialGeometry.VectorBundle.IsCompatibleOrientation
        (F := E) (TangentSpace 𝓘(ℝ, E)) o := by
  let : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace E M
  exact DifferentialGeometry.VectorBundle.exists_compatible_orientation_of_simply_connected
    (tangentBundleCore 𝓘(ℝ, E) M) hdim

theorem exists_manifoldOrientation_of_compatibleOrientation
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {n : ℕ}
    (hdim : Module.finrank ℝ E = n)
    (o : ∀ x : M, Orientation ℝ (TangentSpace 𝓘(ℝ, E) x) (Fin n))
    (ho : DifferentialGeometry.VectorBundle.IsCompatibleOrientation
      (F := E) (TangentSpace 𝓘(ℝ, E)) o) :
    Nonempty (ManifoldOrientation (𝓘(ℝ, E)) M n) := by
  classical
  refine ⟨{ dimension_eq := hdim, orientation := o, locally_constant := ?_ }⟩
  intro p x hx
  obtain ⟨t, ht, U, hUx, hU, q, hq⟩ := ho x
  have ht_mem : MemTrivializationAtlas t := ht
  let S : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace 𝓘(ℝ, E)) → M) :=
    trivializationAt E (TangentSpace 𝓘(ℝ, E)) p
  have hSinst : MemTrivializationAtlas S := by
    change MemTrivializationAtlas (trivializationAt E (TangentSpace 𝓘(ℝ, E)) p)
    infer_instance
  let C : M → E ≃L[ℝ] E := fun y => Trivialization.coordChangeL ℝ t S y
  have hcard : Fintype.card (Fin n) = Module.finrank ℝ E := by simpa using hdim.symm
  have hxS : x ∈ S.baseSet := hx
  have hxT : x ∈ t.baseSet := hU (mem_of_mem_nhds hUx)
  have hcont : ContinuousOn (fun y : M =>
      (Trivialization.coordChangeL ℝ t S y : E →L[ℝ] E)) (t.baseSet ∩ S.baseSet) :=
    continuousOn_coordChange (R := ℝ) (B := M) (F := E)
      (E := TangentSpace 𝓘(ℝ, E)) t S
  have hC : ContinuousAt (fun y => (C y : E →L[ℝ] E)) x :=
    hcont.continuousAt ((t.open_baseSet.inter S.open_baseSet).mem_nhds ⟨hxT, hxS⟩)
  have hqL : ∀ y (hy : y ∈ U),
      Orientation.map (Fin n) (t.linearEquivAt ℝ y (hU hy)) (o y) = q := by
    intro y hy
    have h := hq y hy
    rwa [show (t.continuousLinearEquivAt ℝ y (hU hy)).toLinearEquiv =
      t.linearEquivAt ℝ y (hU hy) from LinearEquiv.ext fun v => rfl] at h
  have hdet : ContinuousAt
      (fun y => LinearMap.det (((C y).toLinearEquiv) : E →ₗ[ℝ] E)) x :=
    ContinuousLinearMap.continuous_det.continuousAt.comp hC
  have hxC : LinearMap.det (((C x).toLinearEquiv) : E →ₗ[ℝ] E) ≠ 0 :=
    (C x).toLinearEquiv.isUnit_det'.ne_zero
  have htrans (y : M) (hyT : y ∈ t.baseSet) (hyS : y ∈ S.baseSet) :
      (S.linearEquivAt ℝ y hyS) =
        (t.linearEquivAt ℝ y hyT).trans ((C y).toLinearEquiv) := by
    have hC' : (C y).toLinearEquiv =
        (t.linearEquivAt ℝ y hyT).symm.trans (S.linearEquivAt ℝ y hyS) :=
      LinearEquiv.coe_injective (Trivialization.coe_coordChangeL (R := ℝ) t S ⟨hyT, hyS⟩)
    calc (S.linearEquivAt ℝ y hyS)
        = (t.linearEquivAt ℝ y hyT).trans
            ((t.linearEquivAt ℝ y hyT).symm.trans (S.linearEquivAt ℝ y hyS)) := by
          rw [← LinearEquiv.trans_assoc, LinearEquiv.self_trans_symm, LinearEquiv.refl_trans]
      _ = (t.linearEquivAt ℝ y hyT).trans ((C y).toLinearEquiv) := by rw [← hC']
  rcases lt_or_gt_of_ne hxC with hneg | hpos
  · have hmem : {y : M | y ∈ U ∧ y ∈ S.baseSet ∧
        LinearMap.det (((C y).toLinearEquiv) : E →ₗ[ℝ] E) < 0} ∈ 𝓝 x :=
      Filter.inter_mem hUx
        (Filter.inter_mem (S.open_baseSet.mem_nhds hxS)
          (hdet.eventually (isOpen_Iio.mem_nhds hneg)))
    obtain ⟨U', hU'sub, hU'open, hxU'⟩ := mem_nhds_iff.mp hmem
    refine ⟨U', hU'open, hxU', fun y hy => (hU'sub hy).2.1, fun y hy => ?_⟩
    obtain ⟨hyU, hyS, hyneg⟩ := hU'sub hy
    have hyT : y ∈ t.baseSet := hU hyU
    have hmapy : Orientation.map (Fin n) (S.linearEquivAt ℝ y hyS) (o y) = -q := by
      rw [htrans y hyT hyS, ← DifferentialGeometry.VectorBundle.map_orientation_trans_between,
        hqL y hyU, (Orientation.map_eq_neg_iff_det_neg q (C y).toLinearEquiv hcard).2 hyneg]
    have hmapx : Orientation.map (Fin n) (S.linearEquivAt ℝ x hxS) (o x) = -q := by
      rw [htrans x hxT hxS, ← DifferentialGeometry.VectorBundle.map_orientation_trans_between,
        hqL x (mem_of_mem_nhds hUx),
        (Orientation.map_eq_neg_iff_det_neg q (C x).toLinearEquiv hcard).2 hneg]
    simp only [tangentChartEquiv]
    rw [hmapy, hmapx]
  · have hmem : {y : M | y ∈ U ∧ y ∈ S.baseSet ∧
        0 < LinearMap.det (((C y).toLinearEquiv) : E →ₗ[ℝ] E)} ∈ 𝓝 x :=
      Filter.inter_mem hUx
        (Filter.inter_mem (S.open_baseSet.mem_nhds hxS)
          (hdet.eventually (isOpen_Ioi.mem_nhds hpos)))
    obtain ⟨U', hU'sub, hU'open, hxU'⟩ := mem_nhds_iff.mp hmem
    refine ⟨U', hU'open, hxU', fun y hy => (hU'sub hy).2.1, fun y hy => ?_⟩
    obtain ⟨hyU, hyS, hypos⟩ := hU'sub hy
    have hyT : y ∈ t.baseSet := hU hyU
    have hmapy : Orientation.map (Fin n) (S.linearEquivAt ℝ y hyS) (o y) = q := by
      rw [htrans y hyT hyS, ← DifferentialGeometry.VectorBundle.map_orientation_trans_between,
        hqL y hyU, (Orientation.map_eq_iff_det_pos q (C y).toLinearEquiv hcard).2 hypos]
    have hmapx : Orientation.map (Fin n) (S.linearEquivAt ℝ x hxS) (o x) = q := by
      rw [htrans x hxT hxS, ← DifferentialGeometry.VectorBundle.map_orientation_trans_between,
        hqL x (mem_of_mem_nhds hUx),
        (Orientation.map_eq_iff_det_pos q (C x).toLinearEquiv hcard).2 hpos]
    simp only [tangentChartEquiv]
    rw [hmapy, hmapx]

theorem isCompatibleOrientation_of_manifoldOrientation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {n : ℕ}
    (o : ManifoldOrientation I M n) :
    DifferentialGeometry.VectorBundle.IsCompatibleOrientation (F := E) (TangentSpace I)
      o.orientation := by
  intro x
  have hx : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt ..
  obtain ⟨U, hUopen, hxU, hUsub, hconst⟩ := o.locally_constant x x hx
  refine ⟨trivializationAt E (TangentSpace I) x, inferInstance, U, hUopen.mem_nhds hxU, hUsub,
    Orientation.map (Fin n) (tangentChartEquiv I M x x hx) (o.orientation x), ?_⟩
  intro y hy
  have hL : ((trivializationAt E (TangentSpace I) x).continuousLinearEquivAt ℝ y (hUsub hy)).toLinearEquiv =
      tangentChartEquiv I M x y (hUsub hy) :=
    LinearEquiv.ext fun _ => rfl
  rw [hL]
  exact hconst y hy

theorem nonempty_manifoldOrientation_iff_exists_compatibleOrientation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {n : ℕ}
    (hdim : Module.finrank ℝ E = n) :
    Nonempty (ManifoldOrientation 𝓘(ℝ, E) M n) ↔
      ∃ o : ∀ x : M, Orientation ℝ (TangentSpace 𝓘(ℝ, E) x) (Fin n),
        DifferentialGeometry.VectorBundle.IsCompatibleOrientation (F := E)
          (TangentSpace 𝓘(ℝ, E)) o := by
  constructor
  · rintro ⟨o⟩
    exact ⟨o.orientation,
      isCompatibleOrientation_of_manifoldOrientation (I := 𝓘(ℝ, E)) (M := M) (o := o)⟩
  · rintro ⟨o, ho⟩
    exact exists_manifoldOrientation_of_compatibleOrientation hdim o ho

theorem exists_manifoldOrientation_of_simply_connected
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [SimplyConnectedSpace M] {n : ℕ} (hdim : Module.finrank ℝ E = n) :
    Nonempty (ManifoldOrientation (𝓘(ℝ, E)) M n) := by
  let : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace E M
  obtain ⟨o, ho⟩ :=
    DifferentialGeometry.VectorBundle.exists_compatible_orientation_of_simply_connected
      (tangentBundleCore 𝓘(ℝ, E) M) hdim
  exact exists_manifoldOrientation_of_compatibleOrientation hdim o ho

end DifferentialGeometry.Topology.Manifold
