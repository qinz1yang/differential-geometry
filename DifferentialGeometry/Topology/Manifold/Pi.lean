import Mathlib.Geometry.Manifold.ContMDiff.Constructions

open scoped ContDiff Manifold

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {ι : Type*} [Fintype ι] {F : ι → Type*}
  [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]
  {G : ι → Type*} [∀ i, TopologicalSpace (G i)]
  {J : ∀ i, ModelWithCorners 𝕜 (F i) (G i)}
  {N : ι → Type*} [∀ i, TopologicalSpace (N i)] [∀ i, ChartedSpace (G i) (N i)]
  {n : WithTop ℕ∞} {f : M → ∀ i, N i} {s : Set M} {x : M}

theorem contMDiffWithinAt_pi :
    ContMDiffWithinAt I (ModelWithCorners.pi J) n f s x ↔
      ∀ i, ContMDiffWithinAt I (J i) n (fun y => f y i) s x := by
  constructor
  · intro hf i
    obtain ⟨hc, hd⟩ := contMDiffWithinAt_iff.mp hf
    exact contMDiffWithinAt_iff.mpr
      ⟨continuousWithinAt_pi.mp hc i, contDiffWithinAt_pi.mp hd i⟩
  · intro hf
    apply contMDiffWithinAt_iff.mpr
    exact ⟨continuousWithinAt_pi.mpr fun i => (contMDiffWithinAt_iff.mp (hf i)).1,
      contDiffWithinAt_pi.mpr fun i => (contMDiffWithinAt_iff.mp (hf i)).2⟩

theorem contMDiff_pi :
    ContMDiff I (ModelWithCorners.pi J) n f ↔
      ∀ i, ContMDiff I (J i) n (fun y => f y i) := by
  exact ⟨fun hf i x => contMDiffWithinAt_pi.mp (hf x) i,
    fun hf x => contMDiffWithinAt_pi.mpr (fun i => hf i x)⟩

theorem contMDiff_pi_apply (i : ι) :
    ContMDiff (ModelWithCorners.pi J) (J i) n (fun x : ∀ j, N j => x i) := by
  intro x
  apply contMDiffAt_iff.mpr
  refine ⟨(continuous_apply i).continuousAt, ?_⟩
  have hd := (contMDiffAt_iff.mp
    (contMDiffAt_id (I := J i) (n := n) (x := x i))).2
  have he : ContDiffWithinAt 𝕜 n (fun y : ∀ j, F j => y i)
      (Set.range (ModelWithCorners.pi J)) (extChartAt (ModelWithCorners.pi J) x x) :=
    (ContinuousLinearMap.proj i : (∀ j, F j) →L[𝕜] F i).contDiff.contDiffAt.contDiffWithinAt
  have hm : Set.MapsTo (fun y : ∀ j, F j => y i)
      (Set.range (ModelWithCorners.pi J)) (Set.range (J i)) := by
    rintro y ⟨z, rfl⟩
    exact ⟨z i, rfl⟩
  have hc := hd.comp (extChartAt (ModelWithCorners.pi J) x x) he hm
  exact hc

end
