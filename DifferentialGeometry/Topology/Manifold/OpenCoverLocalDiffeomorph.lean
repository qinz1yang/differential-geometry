import DifferentialGeometry.Topology.Manifold.OpenCoverAtlas
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry

variable {E F G H H' H'' M N P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
  [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P]
  [ChartedSpace H M] [ChartedSpace H' N] [ChartedSpace H'' P]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  {K : ModelWithCorners ℝ G H''} {n : WithTop ℕ∞}

theorem isLocalDiffeomorphAt_of_comp_right
    {f : M → N} {g : N → P} {x : M}
    (hf : ContinuousAt f x) (hg : IsLocalDiffeomorphAt J K n g (f x))
    (hgf : IsLocalDiffeomorphAt I K n (g ∘ f) x) :
    IsLocalDiffeomorphAt I J n f x := by
  have h := hgf.comp (K := J) (P := N) hg.localInverse_isLocalDiffeomorphAt
  apply DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq _ h
  filter_upwards [hf (hg.localInverse.open_target.mem_nhds hg.localInverse_mem_target)] with y hy
  exact (hg.localInverse_left_inv hy).symm

end DifferentialGeometry

namespace OpenPartialHomeomorph

variable {E F G H H' H'' M N P X : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
  [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P] [TopologicalSpace X]
  [ChartedSpace H M] [ChartedSpace H' N] [ChartedSpace H'' P]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  {K : ModelWithCorners ℝ G H''} {n : WithTop ℕ∞}

theorem contMDiffOn_transition_of_localDiffeomorph
    (a : OpenPartialHomeomorph M X) (b : OpenPartialHomeomorph N X) (f : X → P)
    (ha : IsLocalDiffeomorphOn I K n (f ∘ a) a.source)
    (hb : IsLocalDiffeomorphOn J K n (f ∘ b) b.source) :
    ContMDiffOn I J n (a.trans b.symm) (a.trans b.symm).source := by
  intro x hx
  have hbx : b.symm (a x) ∈ b.source := b.map_target hx.2
  have heq : (f ∘ b) ∘ (a.trans b.symm) =ᶠ[𝓝 x] f ∘ a := by
    filter_upwards [(a.trans b.symm).open_source.mem_nhds hx] with y hy
    change f (b (b.symm (a y))) = f (a y)
    exact congrArg f (b.right_inv (show a y ∈ b.target from hy.2))
  have hcomp : IsLocalDiffeomorphAt I K n ((f ∘ b) ∘ (a.trans b.symm)) x :=
    DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq heq (ha ⟨x, hx.1⟩)
  have h := DifferentialGeometry.isLocalDiffeomorphAt_of_comp_right
    ((a.trans b.symm).continuousOn.continuousAt ((a.trans b.symm).open_source.mem_nhds hx))
    (hb ⟨b.symm (a x), hbx⟩) hcomp
  exact h.contMDiffAt.contMDiffWithinAt

end OpenPartialHomeomorph

namespace DifferentialGeometry.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {X : Type*} [TopologicalSpace X] {ι : Type*}
  (F H N : ι → Type*) [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
  [∀ i, TopologicalSpace (H i)] [∀ i, TopologicalSpace (N i)] [∀ i, ChartedSpace (H i) (N i)]
  (J : ∀ i, ModelWithCorners ℝ (F i) (H i))
  [∀ i, IsManifold (J i) ∞ (N i)]
  (L : ∀ i, F i ≃L[ℝ] E)
  (e : ∀ i, OpenPartialHomeomorph (N i) X)
  (hcover : ∀ x : X, ∃ i, x ∈ (e i).target)
  (hinterior : ∀ i p, p ∈ (e i).source → (J i).IsInteriorPoint p)
  {E' H' P : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] [TopologicalSpace P] [ChartedSpace H' P]
  (I : ModelWithCorners ℝ E' H') (f : X → P)

theorem isLocalDiffeomorph_openCoverChartedSpace
    (hlocal : ∀ i, IsLocalDiffeomorphOn (J i) I ∞ (f ∘ e i) (e i).source) :
    let _ := openCoverChartedSpace F H N J L e hcover hinterior
    IsManifold 𝓘(ℝ, E) ∞ X ∧ IsLocalDiffeomorph 𝓘(ℝ, E) I ∞ f := by
  have htrans (i j : ι) : ContMDiffOn (J i) (J j) ∞
      ((e i).trans (e j).symm) ((e i).trans (e j).symm).source :=
    (e i).contMDiffOn_transition_of_localDiffeomorph (e j) f (hlocal i) (hlocal j)
  let _ := openCoverChartedSpace F H N J L e hcover hinterior
  refine ⟨isManifold_openCoverChartedSpace F H N J L e hcover hinterior htrans, ?_⟩
  intro x
  obtain ⟨i, hi⟩ := hcover x
  let φ : PartialDiffeomorph (J i) 𝓘(ℝ, E) (N i) X ∞ :=
    { (e i).toPartialEquiv with
      open_source := (e i).open_source
      open_target := (e i).open_target
      contMDiffOn_toFun :=
        contMDiffOn_openCover_parametrization F H N J L e hcover hinterior htrans i
      contMDiffOn_invFun :=
        contMDiffOn_openCover_inverse F H N J L e hcover hinterior htrans i }
  have hy : (e i).symm x ∈ (e i).source := (e i).map_target hi
  have hφ : IsLocalDiffeomorphAt (J i) 𝓘(ℝ, E) ∞ (e i) ((e i).symm x) :=
    φ.isLocalDiffeomorphAt (J i) 𝓘(ℝ, E) ∞ hy
  have h := DifferentialGeometry.isLocalDiffeomorphAt_of_comp
    (hlocal i ⟨(e i).symm x, hy⟩) hφ
  rwa [(e i).right_inv hi] at h

end DifferentialGeometry.Manifold
