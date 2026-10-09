import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Orientation
import DifferentialGeometry.Topology.Manifold.SmoothOrientationCompatible
import DifferentialGeometry.Topology.Manifold.DiffeomorphPullbackOrientation
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.SeamOrientationGlue

/-!+# Gluing orientations along actual smooth quotient patches

Actual partial diffeomorphisms transport the given patch orientations to their open targets.
Compatibility of the actual transition differentials makes these local orientations agree.
Their smooth gluing orients the covered manifold, preserving every original patch orientation.
-/

set_option autoImplicit false
noncomputable section
open Set Function Manifold TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology

namespace GC.Seifert

section Differential

variable {E F G H K L M N Q : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] [TopologicalSpace K] [TopologicalSpace L]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
  {Z : ModelWithCorners ℝ G L}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace K N]
  [TopologicalSpace Q] [ChartedSpace L Q]

def carrierSurgeryPatchTangentEquiv (e : PartialDiffeomorph I J M N ∞)
    {x : M} (hx : x ∈ e.source) : E ≃ₗ[ℝ] F :=
  ((e.isLocalDiffeomorphAt I J ∞ hx).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv

theorem carrierSurgeryPatchTangentEquiv_apply (e : PartialDiffeomorph I J M N ∞)
    {x : M} (hx : x ∈ e.source) (v : E) :
    carrierSurgeryPatchTangentEquiv e hx v = mfderiv I J e x v := rfl

theorem carrierSurgeryPatchTangentEquiv_congr (e : PartialDiffeomorph I J M N ∞)
    {x y : M} (hx : x ∈ e.source) (hy : y ∈ e.source) (hxy : x = y) :
    carrierSurgeryPatchTangentEquiv e hx = carrierSurgeryPatchTangentEquiv e hy := by
  subst y
  rfl

theorem carrierSurgeryPatchTangentEquiv_trans (e : PartialDiffeomorph I J M N ∞)
    (f : PartialDiffeomorph J Z N Q ∞) {x : M} (hx : x ∈ (e.trans f).source) :
    carrierSurgeryPatchTangentEquiv (e.trans f) hx =
      (carrierSurgeryPatchTangentEquiv e hx.1).trans
        (carrierSurgeryPatchTangentEquiv f hx.2) := by
  ext v
  exact mfderiv_comp_apply x (f.mdifferentiableAt (by simp) hx.2)
    (e.mdifferentiableAt (by simp) hx.1) v

theorem carrierSurgeryPatchTangentEquiv_symm (e : PartialDiffeomorph I J M N ∞)
    {x : M} (hx : x ∈ e.source) :
    carrierSurgeryPatchTangentEquiv e.symm (e.toOpenPartialHomeomorph.map_source hx) =
      (carrierSurgeryPatchTangentEquiv e hx).symm := by
  let A := carrierSurgeryPatchTangentEquiv e hx
  let B := carrierSurgeryPatchTangentEquiv e.symm
    (e.toOpenPartialHomeomorph.map_source hx)
  have he : (fun y => e.symm (e y)) =ᶠ[𝓝 x] id := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact e.toOpenPartialHomeomorph.left_inv hy
  have hd := he.mfderiv_eq (I := I) (I' := I)
  change mfderiv I I (fun y => e.symm (e y)) x = mfderiv I I id x at hd
  have hc := mfderiv_comp x
    (e.symm.mdifferentiableAt (by simp) (e.toOpenPartialHomeomorph.map_source hx))
    (e.mdifferentiableAt (by simp) hx)
  change mfderiv I I (fun y => e.symm (e y)) x =
    (mfderiv J I e.symm (e x)).comp (mfderiv I J e x) at hc
  rw [hd, mfderiv_id] at hc
  have hab : A.trans B = LinearEquiv.refl ℝ E := by
    ext v
    exact (congrArg (fun D : E →L[ℝ] E => D v) hc).symm
  change B = A.symm
  ext v
  obtain ⟨w, rfl⟩ := A.surjective v
  rw [A.symm_apply_apply]
  exact congrArg (fun D : E ≃ₗ[ℝ] E => D w) hab

end Differential

section Gluing

variable {ι E H Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H]
  {J : ModelWithCorners ℝ E H}
  [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold J ∞ Q]
  {F : ι → Type*} [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
  [∀ i, FiniteDimensional ℝ (F i)]
  {K : ι → Type*} [∀ i, TopologicalSpace (K i)]
  {M : ι → Type*} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace (K i) (M i)]
  {I : ∀ i, ModelWithCorners ℝ (F i) (K i)} [∀ i, IsManifold (I i) ∞ (M i)]
  {n : ℕ}

theorem exists_carrierSurgeryOrientation_of_openCover
    (e : ∀ i, PartialDiffeomorph (I i) J (M i) Q ∞)
    (hcover : ∀ q : Q, ∃ i, q ∈ (e i).target)
    (o : ∀ i, ManifoldOrientation (I i) (M i) n) (hdim : Module.finrank ℝ E = n)
    (hcompat : ∀ i j x (hx : x ∈ ((e i).trans (e j).symm).source),
      Orientation.map (Fin n)
        (carrierSurgeryPatchTangentEquiv ((e i).trans (e j).symm) hx) ((o i).orientation x) =
          (o j).orientation ((e j).symm ((e i) x))) :
    ∃ O : ManifoldOrientation J Q n, ∀ i x (hx : x ∈ (e i).source),
      Orientation.map (Fin n) (carrierSurgeryPatchTangentEquiv (e i) hx)
        ((o i).orientation x) = O.orientation ((e i) x) := by
  classical
  let s (i : ι) := smoothOrientationOfManifoldOrientation (I i)
    (OrientationAssembly.reindexManifoldOrientation (I i) (finCongr (o i).dimension_eq.symm)
      (o i))
  let U (i : ι) : Opens Q := ⟨(e i).target, (e i).open_target⟩
  let a (i : ι) : SmoothOrientation J (U i) :=
    DifferentialGeometry.PartialDiffeomorph.pullbackSmoothOrientation (e i).symm
      (fun y hy => hy) (s i)
  have ha (i : ι) (y : Q) (hy : y ∈ (e i).target) :
      (a i).val ⟨y, hy⟩ =
        tangentOrientationEquiv (carrierSurgeryPatchTangentEquiv (e i).symm hy).symm
          ((s i).val ((e i).symm y)) :=
    DifferentialGeometry.PartialDiffeomorph.pullbackSmoothOrientation_apply
      (e i).symm (fun z hz => hz) (s i) ⟨y, hy⟩
  have heq (i j : ι) (y : Q) (hi : y ∈ U i) (hj : y ∈ U j) :
      (a i).val ⟨y, hi⟩ = (a j).val ⟨y, hj⟩ := by
    let x := (e i).symm y
    have hx : x ∈ (e i).source := (e i).toOpenPartialHomeomorph.map_target hi
    have hxy : (e i) x = y := (e i).toOpenPartialHomeomorph.right_inv hi
    have hxj : x ∈ ((e i).trans (e j).symm).source := by
      refine ⟨hx, ?_⟩
      change (e i) x ∈ (e j).target
      rwa [hxy]
    have hs := (tangentOrientationEquiv_reindex_eq_iff
      (carrierSurgeryPatchTangentEquiv ((e i).trans (e j).symm) hxj)
      (o i).dimension_eq (o j).dimension_eq ((o i).orientation x)
      ((o j).orientation ((e j).symm ((e i) x)))).mpr (hcompat i j x hxj)
    change tangentOrientationEquiv
      (carrierSurgeryPatchTangentEquiv ((e i).trans (e j).symm) hxj)
      ((s i).val x) = (s j).val ((e j).symm ((e i) x)) at hs
    rw [carrierSurgeryPatchTangentEquiv_trans, tangentOrientationEquiv_trans] at hs
    have hB := carrierSurgeryPatchTangentEquiv_congr (e j).symm hxj.2 hj hxy
    rw [hB, hxy] at hs
    rw [ha i y hi, ha j y hj]
    have hA := carrierSurgeryPatchTangentEquiv_symm (e i).symm hi
    change carrierSurgeryPatchTangentEquiv (e i) hx =
      (carrierSurgeryPatchTangentEquiv (e i).symm hi).symm at hA
    rw [← hA]
    apply (tangentOrientationEquiv (carrierSurgeryPatchTangentEquiv (e j).symm hj)).injective
    have hcancel := tangentOrientationEquiv_symm
      (carrierSurgeryPatchTangentEquiv (e j).symm hj).symm ((s j).val ((e j).symm y))
    rw [LinearEquiv.symm_symm] at hcancel
    rw [hcancel]
    exact hs
  let S := glueSmoothOrientations J U a hcover heq
  obtain ⟨O, hO⟩ := exists_manifoldOrientation_eq_of_smoothOrientation J S
  refine ⟨OrientationAssembly.reindexManifoldOrientation J (finCongr hdim) O, ?_⟩
  intro i x hx
  have htarget := (e i).toOpenPartialHomeomorph.map_source hx
  have hs : tangentOrientationEquiv (carrierSurgeryPatchTangentEquiv (e i) hx)
      ((s i).val x) = S.val ((e i) x) := by
    rw [glueSmoothOrientations_apply J U a hcover heq i ⟨(e i) x, htarget⟩,
      ha i ((e i) x) htarget]
    have hinv := carrierSurgeryPatchTangentEquiv_symm (e i) hx
    change carrierSurgeryPatchTangentEquiv (e i).symm htarget =
      (carrierSurgeryPatchTangentEquiv (e i) hx).symm at hinv
    have hleft : (e i).symm ((e i) x) = x := (e i).toOpenPartialHomeomorph.left_inv hx
    have hlin := congrArg LinearEquiv.symm hinv
    rw [LinearEquiv.symm_symm] at hlin
    have hv := congrArg (fun L : F i ≃ₗ[ℝ] E =>
      tangentOrientationEquiv L ((s i).val ((e i).symm ((e i) x)))) hlin
    exact (congrArg (tangentOrientationEquiv (carrierSurgeryPatchTangentEquiv (e i) hx))
      (congrArg (s i).val hleft).symm).trans hv.symm
  have hm := orientation_map_reindex_of_tangentOrientationEquiv
    (carrierSurgeryPatchTangentEquiv (e i) hx) (o i).dimension_eq hdim
    ((s i).val x) (S.val ((e i) x)) hs
  have hindex : Orientation.reindex ℝ (F i) (finCongr (o i).dimension_eq)
      ((s i).val x) = (o i).orientation x := by
    change Orientation.reindex ℝ (F i) (finCongr (o i).dimension_eq)
      (Orientation.reindex ℝ (F i) (finCongr (o i).dimension_eq.symm)
        ((o i).orientation x)) = (o i).orientation x
    have hh : (finCongr (o i).dimension_eq.symm).symm = finCongr (o i).dimension_eq := by
      ext k
      rfl
    rw [← hh, ← Orientation.reindex_symm]
    exact Equiv.symm_apply_apply _ _
  rw [hindex] at hm
  change Orientation.map (Fin n) (carrierSurgeryPatchTangentEquiv (e i) hx)
    ((o i).orientation x) = Orientation.reindex ℝ E (finCongr hdim) (O.orientation ((e i) x))
  rw [hO]
  exact hm

end Gluing

end GC.Seifert
